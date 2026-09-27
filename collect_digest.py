#!/usr/bin/env python3
"""
Collecte les flux RSS des revues de presse de Mayeul (quotidienne, hebdomadaire,
mensuelle) et produit trois digests markdown, groupés par rubrique :
- digest/latest.md   : dernières 24h (revue quotidienne)
- digest/week.md     : semaine ISO complète la plus récente, lundi à dimanche
                        (revue hebdomadaire)
- digest/month.md    : mois civil écoulé le plus récent (revue mensuelle)

Ce script ne fait AUCUN travail éditorial (pas de hiérarchisation, pas de
vérification de fond) : il se contente de rassembler et nettoyer la matière
première, pour que Claude n'ait plus qu'une page propre à lire au lieu de
devoir chercher lui-même sur le web. Le travail éditorial (choix de la Une,
vérification, rédaction, mise en page) reste fait par Claude à partir de ces
digests.

Deux types de sources sont utilisées :
- Flux RSS propres au média (le plus précis, marqué tel quel).
- Recherche Google Actualités limitée à un site précis ("site:domaine"),
  utilisée quand le média n'a pas de flux RSS public fiable ou documenté :
  ça reste un flux RSS (Google Actualités en fournit un par requête), donc
  ça marche exactement pareil, juste un cran moins direct. Ces entrées sont
  marquées "(via Google Actualités)" dans les digests pour rester transparent
  sur l'origine.

Fonctionnement de l'archive (digest/history.jsonl) :
Chaque exécution collecte sur une fenêtre large (HISTORIQUE_HEURES, plus
large qu'un jour pour survivre à une exécution manquée), garde ce qui a
été retenu par rubrique (mêmes plafonds que le digest quotidien) et
l'ajoute à une archive persistante dédoublonnée par URL. Cette archive est
purgée au-delà de HISTORIQUE_JOURS_CONSERVES jours. Les digests hebdomadaire
et mensuel sont reconstruits chaque jour à partir de cette archive, avec
leurs propres plafonds par rubrique (plus larges, puisqu'ils couvrent une
période plus longue). Les entrées sans date fiable ne sont pas archivées
(elles ne peuvent pas être placées dans une semaine ou un mois précis) mais
restent présentes dans le digest quotidien.

Archive longue (digest/archive/) : history.jsonl est aussi reversé chaque
jour dans un fichier par mois, conservé un an, qui alimente la page de
recherche recherche.html (publiée avec GitHub Pages).

Usage: python3 collect_digest.py
Écrit digest/latest.md, digest/week.md, digest/month.md, digest/history.jsonl
et digest/archive/ dans le répertoire courant.
"""

import json
import os
import re
import sys
import time
import urllib.parse
from datetime import datetime, timedelta, timezone

import feedparser
import requests

FRAICHEUR_HEURES = 24            # fenêtre du digest quotidien
HISTORIQUE_HEURES = 48           # fenêtre de collecte pour l'archive (résiste à un run manqué)
HISTORIQUE_JOURS_CONSERVES = 33  # purge de l'archive au-delà de cette ancienneté
MAX_ITEMS_PAR_FLUX = 20

MAX_ITEMS_PAR_RUBRIQUE = 25      # plafond quotidien, par rubrique
MAX_ITEMS_UNE = 40               # plafond quotidien, rubrique 0 (recoupement de la Une)

MAX_ITEMS_PAR_RUBRIQUE_SEMAINE = 40
MAX_ITEMS_UNE_SEMAINE = 60

MAX_ITEMS_PAR_RUBRIQUE_MOIS = 55
MAX_ITEMS_UNE_MOIS = 80

TIMEOUT = 15
HISTORY_PATH = "digest/history.jsonl"

# Archive longue durée, utilisée par la page de recherche (recherche.html).
# Un fichier par mois (digest/archive/AAAA-MM.jsonl) plutôt qu'un seul gros
# fichier : les mois passés ne changent plus, seul le mois en cours est
# réécrit chaque jour, et la page ne charge que les mois dont elle a besoin.
ARCHIVE_DIR = "digest/archive"
ARCHIVE_MOIS_CONSERVES = 12   # mois complets gardés en plus du mois en cours


def google_news(query):
    q = urllib.parse.quote(query)
    return f"https://news.google.com/rss/search?q={q}&hl=fr&gl=FR&ceid=FR:fr"


def gsite(nom, domaine, extra=""):
    """Source sans flux RSS propre fiable : on prend ses articles récents
    via Google Actualités, filtré sur son domaine. Le paramètre extra
    permet d'ajouter des mots-clés (utile pour restreindre à une section)."""
    query = f"site:{domaine} {extra}".strip()
    return (f"{nom} (via Google Actualités)", google_news(query))


def site_or(domaines):
    """Groupe une liste de domaines en clause OR entre parenthèses, ex.
    "(site:lemonde.fr OR site:lefigaro.fr)". À combiner ensuite avec un
    groupe de mots-clés, lui aussi entre parenthèses, pour éviter tout
    problème de priorité des opérateurs dans la requête Google."""
    return "(" + " OR ".join(f"site:{d}" for d in domaines) + ")"


# Domaines de presse retenus pour restreindre les recherches thématiques
# Google Actualités (par opposition à gsite(), qui cible UN média précis,
# ces listes couvrent plusieurs médias de référence, sensibilités
# différentes incluses, pour une même zone ou un même sujet). Sans cette
# restriction, une recherche par mots-clés seule peut remonter n'importe
# quel site indexé par Google : qualité éditoriale incertaine, ou même
# mauvais pays (c'est ce qui a produit l'erreur Portugal/Sécurité sociale).
DOMAINES_FRANCE = [
    "lemonde.fr", "lefigaro.fr", "liberation.fr", "francetvinfo.fr",
    "leparisien.fr", "lopinion.fr", "la-croix.com", "ouest-france.fr",
    "sudouest.fr", "lepoint.fr", "nouvelobs.com", "marianne.net",
    "rtl.fr", "bfmtv.com", "publicsenat.fr", "lcp.fr",
]
DOMAINES_UE = ["euractiv.fr", "touteleurope.eu", "politico.eu", "lemonde.fr", "lefigaro.fr"]
DOMAINES_EUROPE_PAYS = [
    "lemonde.fr", "courrierinternational.com", "euronews.com",
    "bbc.com", "reuters.com", "apnews.com", "politico.eu",
]
DOMAINES_CONFLITS = [
    "lemonde.fr", "france24.com", "rfi.fr", "reuters.com",
    "apnews.com", "bbc.com", "lefigaro.fr", "courrierinternational.com",
]
DOMAINES_AMERIQUES = ["reuters.com", "apnews.com", "nytimes.com", "bbc.com", "lemonde.fr"]
DOMAINES_ASIE = [
    "reuters.com", "apnews.com", "bbc.com", "scmp.com",
    "lemonde.fr", "courrierinternational.com",
]
DOMAINES_AFRIQUE = ["rfi.fr", "lemonde.fr", "reuters.com", "apnews.com", "jeuneafrique.com"]
DOMAINES_ECO_MONDIALE = [
    "ft.com", "reuters.com", "lemonde.fr", "lesechos.fr",
    "latribune.fr", "bloomberg.com",
]
DOMAINES_TECH = ["lemonde.fr", "reuters.com", "courrierinternational.com", "usine-digitale.fr"]


# Chaque rubrique : (numéro, nom, liste de flux [(nom_source, url), ...])
# Pluralisme visé par rubrique : presse généraliste de sensibilités
# différentes, audiovisuel public, presse régionale, presse spécialisée,
# agences et presse internationale, sources indépendantes/en exil quand
# le sujet le justifie.
RUBRIQUES = [
    (0, "Flux généraux (recoupement de la Une, presse nationale et régionale)", [
        ("Le Monde", "https://www.lemonde.fr/rss/une.xml"),
        ("Le Figaro", "https://www.lefigaro.fr/rss/figaro_actualites.xml"),
        ("Libération", "https://www.liberation.fr/arc/outboundfeeds/rss-all/?outputType=xml"),
        ("franceinfo", "https://www.francetvinfo.fr/titres.rss"),
        ("France 24", "https://www.france24.com/fr/rss"),
        ("RFI", "https://www.rfi.fr/fr/rss"),
        ("Le Parisien", "https://feeds.leparisien.fr/leparisien/rss"),
        ("Mediapart", "https://www.mediapart.fr/articles/feed"),
        ("L'Humanité", "https://www.humanite.fr/feed"),
        ("Euronews", "https://fr.euronews.com/rss"),
        ("BBC News", "https://feeds.bbci.co.uk/news/world/rss.xml"),
        ("The Guardian", "https://www.theguardian.com/world/rss"),
        ("Courrier International", "https://www.courrierinternational.com/feed/all/rss.xml"),
        gsite("La Croix", "la-croix.com"),
        gsite("L'Opinion", "lopinion.fr"),
        gsite("Ouest-France", "ouest-france.fr"),
        gsite("Sud Ouest", "sudouest.fr"),
        gsite("La Voix du Nord", "lavoixdunord.fr"),
        gsite("AFP", "afp.com"),
    ]),
    (1, "Politique française", [
        ("Le Monde", "https://www.lemonde.fr/politique/rss_full.xml"),
        ("Le Figaro", "https://www.lefigaro.fr/rss/figaro_politique.xml"),
        ("franceinfo", "https://www.francetvinfo.fr/politique.rss"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (Assemblée nationale OR gouvernement OR Sénat OR Élysée OR ministre OR projet de loi OR motion de censure)")),
        gsite("La Croix", "la-croix.com", "politique"),
        gsite("L'Humanité", "humanite.fr", "politique"),
        gsite("L'Opinion", "lopinion.fr", "politique"),
    ]),
    (2, "Justice, police et sécurité intérieure", [
        ("franceinfo", "https://www.francetvinfo.fr/faits-divers.rss"),
        ("Le Parisien", "https://feeds.leparisien.fr/leparisien/rss"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (procès OR tribunal OR garde à vue OR Cour de cassation OR enquête judiciaire OR condamnation OR parquet OR perquisition)")),
        gsite("OCCRP", "occrp.org"),
    ]),
    (3, "Défense et armées", [
        ("Opex360 / Zone Militaire", "https://www.opex360.com/feed/"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (armée française OR défense OR OTAN OR militaire OR ministère des Armées OR forces armées OR dissuasion nucléaire)")),
    ]),
    (4, "Économie française et social", [
        ("Le Monde", "https://www.lemonde.fr/economie/rss_full.xml"),
        ("Les Échos", "https://services.lesechos.fr/rss/les-echos-economie.xml"),
        ("franceinfo", "https://www.francetvinfo.fr/economie.rss"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (budget OR chômage OR salaires OR grève OR Bercy OR dette publique OR pouvoir d'achat OR inflation)")),
        gsite("La Tribune", "latribune.fr"),
        gsite("Alternatives Économiques", "alternatives-economiques.fr"),
    ]),
    (5, "Union européenne", [
        ("Euractiv France", "https://euractiv.fr/feed/"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_UE)} (Commission européenne OR Parlement européen OR Bruxelles OR eurodéputés OR sommet européen OR Conseil européen)")),
        gsite("Contexte", "contexte.com"),
    ]),
    (6, "Europe (pays)", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_EUROPE_PAYS)} (Allemagne OR Italie OR Espagne OR Royaume-Uni OR Pologne OR Pays-Bas) (politique OR élections OR gouvernement)")),
        gsite("Der Spiegel International", "spiegel.de/international"),
        gsite("El País", "elpais.com"),
    ]),
    (7, "Guerres et conflits", [
        ("Le Monde", "https://www.lemonde.fr/international/rss_full.xml"),
        ("France 24", "https://www.france24.com/fr/moyen-orient/rss"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_CONFLITS)} (Ukraine OR Gaza OR Sahel OR Soudan OR Syrie) (guerre OR conflit)")),
        ("The Moscow Times", "https://www.themoscowtimes.com/rss/news"),
        ("Meduza (English)", "https://meduza.io/rss/en/all"),
        gsite("Reuters", "reuters.com"),
        gsite("Kyiv Independent", "kyivindependent.com"),
    ]),
    (8, "Amériques", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_AMERIQUES)} (États-Unis OR Washington OR Amérique latine OR Maison Blanche OR Congrès américain OR Brésil OR Mexique OR Argentine)")),
        ("MercoPress", "https://en.mercopress.com/rss/"),
        gsite("Associated Press", "apnews.com"),
        gsite("New York Times", "nytimes.com"),
        gsite("BBC Mundo", "bbc.com/mundo"),
    ]),
    (9, "Asie et Océanie", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_ASIE)} (Chine OR Inde OR Japon OR Taïwan OR Corée du Sud OR Pékin OR Tokyo)")),
        gsite("South China Morning Post", "scmp.com"),
        gsite("CNA / Focus Taiwan", "focustaiwan.tw"),
        gsite("The Hindu", "thehindu.com"),
        gsite("The Wire (Inde)", "thewire.in"),
        gsite("Scroll.in", "scroll.in"),
        gsite("Channel NewsAsia", "channelnewsasia.com"),
        gsite("NHK World", "nhk.or.jp/nhkworld"),
    ]),
    (10, "Afrique et Maghreb", [
        ("RFI", "https://www.rfi.fr/fr/afrique/rss"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_AFRIQUE)} (Afrique OR Algérie OR Maroc OR Sahel OR Tunisie OR Sénégal OR Nigeria OR RDC)")),
        ("Jeune Afrique", "https://www.jeuneafrique.com/feed/"),
        ("AllAfrica", "https://allafrica.com/tools/headlines/rdf/latest/headlines.rdf"),
        ("Daily Maverick", "https://www.dailymaverick.co.za/dmrss/"),
        gsite("The Continent", "continent.substack.com"),
    ]),
    (11, "Économie mondiale, marchés et énergie", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_ECO_MONDIALE)} (BCE OR Fed OR pétrole OR marchés OR inflation OR taux d'intérêt OR Wall Street OR récession)")),
        gsite("Financial Times", "ft.com"),
        gsite("Reuters Business", "reuters.com", "business"),
    ]),
    (12, "Sciences, technologies et numérique", [
        ("Le Monde", "https://www.lemonde.fr/sciences/rss_full.xml"),
        ("Next", "https://next.ink/feed/"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_TECH)} (intelligence artificielle OR cybersécurité OR espace OR recherche OR OpenAI OR semi-conducteurs OR données personnelles OR CNIL)")),
        ("Rest of World", "https://restofworld.org/feed/latest/"),
    ]),
    (13, "Environnement et climat", [
        ("Le Monde", "https://www.lemonde.fr/planete/rss_full.xml"),
        ("Reporterre", "https://reporterre.net/spip.php?page=backend"),
        ("Carbon Brief", "https://www.carbonbrief.org/feed/"),
    ]),
    (14, "Agriculture et alimentation", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (agriculteurs OR PAC OR élevage OR récolte OR FNSEA OR prix agricoles OR sécheresse agricole)")),
        gsite("La France Agricole", "lafranceagricole.fr"),
    ]),
    (15, "Santé et protection sociale", [
        ("franceinfo", "https://www.francetvinfo.fr/sante.rss"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (hôpital OR Sécurité sociale OR médicament OR retraites OR assurance maladie OR PLFSS OR Cnam OR soignants OR déficit de la Sécu)")),
    ]),
    (16, "Éducation et enseignement supérieur", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (école OR université OR Parcoursup OR enseignants OR collège OR lycée OR ministère de l'Éducation OR rentrée scolaire)")),
        gsite("Café pédagogique", "cafepedagogique.net"),
    ]),
    (17, "Société et migrations", [
        ("Le Monde", "https://www.lemonde.fr/societe/rss_full.xml"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (immigration OR logement OR laïcité OR démographie OR asile OR sans-abrisme OR natalité)")),
        ("The New Humanitarian", "https://www.thenewhumanitarian.org/rss/all.xml"),
    ]),
    (18, "Transports et villes", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (SNCF OR RATP OR transports OR urbanisme OR grève des transports OR autoroutes OR aéroports)")),
    ]),
    (19, "Île-de-France et Paris", [
        ("Le Parisien", "https://feeds.leparisien.fr/leparisien/rss"),
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (Paris OR Île-de-France OR mairie OR conseil régional OR Hidalgo OR banlieue parisienne)")),
    ]),
    (20, "Médias et journalisme", [
        ("Google Actualités", google_news(f"{site_or(DOMAINES_FRANCE)} (Arcom OR rédaction OR audiences OR liberté de la presse OR RSF OR pluralisme des médias OR concentration des médias)")),
        ("Bellingcat", "https://www.bellingcat.com/feed/"),
        gsite("La Revue des médias (INA)", "larevuedesmedias.ina.fr"),
    ]),
    (21, "Culture", [
        ("Le Monde", "https://www.lemonde.fr/culture/rss_full.xml"),
        ("franceinfo", "https://www.francetvinfo.fr/culture.rss"),
        gsite("Télérama", "telerama.fr"),
    ]),
    (22, "Sport (attention au cyclisme)", [
        ("L'Équipe", "https://www.lequipe.fr/rss/actu_rss.xml"),
        ("L'Équipe Cyclisme", "https://www.lequipe.fr/rss/actu_rss_Cyclisme.xml"),
        gsite("Cyclism'Actu", "cyclismactu.net"),
    ]),
    (23, "Analyse de fond et investigation (toutes rubriques)", [
        ("The Conversation France", "https://theconversation.com/fr/articles.atom"),
        gsite("OCCRP", "occrp.org"),
        ("Bellingcat", "https://www.bellingcat.com/feed/"),
    ]),
]

RUBRIQUE_NOMS = {num: nom for num, nom, _ in RUBRIQUES}


def parse_entry_datetime(entry):
    for field in ("published_parsed", "updated_parsed"):
        t = entry.get(field)
        if t:
            try:
                return datetime.fromtimestamp(time.mktime(t), tz=timezone.utc)
            except (OverflowError, ValueError):
                pass
    return None


def clean_title(title):
    title = re.sub(r"\s+", " ", title or "").strip()
    return title


def fetch_feed(name, url, cutoff_hours):
    items = []
    try:
        resp = requests.get(
            url,
            timeout=TIMEOUT,
            headers={"User-Agent": "Mozilla/5.0 (compatible; RevueDigestBot/1.0)"},
        )
        resp.raise_for_status()
        parsed = feedparser.parse(resp.content)
    except Exception as exc:
        print(f"  [!] {name} ({url}) : échec ({exc})", file=sys.stderr)
        return items

    cutoff = datetime.now(timezone.utc) - timedelta(hours=cutoff_hours)
    for entry in parsed.entries[:MAX_ITEMS_PAR_FLUX * 2]:
        dt = parse_entry_datetime(entry)
        if dt is not None and dt < cutoff:
            continue
        title = clean_title(entry.get("title"))
        link = entry.get("link")
        if not title or not link:
            continue
        date_str = dt.strftime("%Y-%m-%d %H:%M UTC") if dt else "date inconnue"
        source = name
        if name == "Google Actualités":
            # Recherche thématique : on remonte le vrai média éditeur, fourni
            # par Google dans le champ <source>, et on retire le suffixe
            # " - Média" que Google ajoute au titre.
            editeur = (entry.get("source") or {}).get("title", "").strip()
            if editeur:
                source = f"{editeur} (via Google Actualités)"
                suffixe = f" - {editeur}"
                if title.endswith(suffixe):
                    title = title[: -len(suffixe)].strip()
            else:
                source = "Média non identifié (via Google Actualités)"
        elif name.endswith("(via Google Actualités)"):
            # Source gsite() : le média est déjà connu, on nettoie juste le titre.
            editeur = (entry.get("source") or {}).get("title", "").strip()
            if editeur and title.endswith(f" - {editeur}"):
                title = title[: -len(f" - {editeur}")].strip()
        items.append({"title": title, "link": link, "source": source, "date": date_str, "dt": dt})
        if len(items) >= MAX_ITEMS_PAR_FLUX:
            break
    return items


def normalize_for_dedupe(title):
    t = title.lower()
    t = re.sub(r"[^a-z0-9àâäéèêëïîôöùûüç ]", "", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t


def load_history():
    if not os.path.exists(HISTORY_PATH):
        return []
    history = []
    with open(HISTORY_PATH, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                history.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return history


def update_archive(history, now):
    """Reverse l'archive courte (history.jsonl, 33 jours) dans l'archive
    longue par mois. Idempotent : une URL déjà archivée n'est pas réécrite,
    donc relancer le script ne crée pas de doublons. Purge les mois au-delà
    de ARCHIVE_MOIS_CONSERVES et écrit un index des mois disponibles."""
    os.makedirs(ARCHIVE_DIR, exist_ok=True)

    par_mois = {}
    for item in history:
        par_mois.setdefault(item["dt"][:7], []).append(item)

    for mois, items in par_mois.items():
        path = os.path.join(ARCHIVE_DIR, f"{mois}.jsonl")
        existants = set()
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as f:
                for line in f:
                    try:
                        existants.add(json.loads(line)["url"])
                    except (json.JSONDecodeError, KeyError):
                        continue
        nouveaux = [it for it in items if it["url"] not in existants]
        if nouveaux:
            with open(path, "a", encoding="utf-8") as f:
                for it in nouveaux:
                    ligne = dict(it)
                    ligne["rubrique"] = RUBRIQUE_NOMS.get(it["rubrique_num"], "")
                    # Entrées collectées avant le nettoyage des titres Google
                    # Actualités (fin septembre 2026) : Google y avait ajouté
                    # " - Média" en fin de titre. On le retire, et pour les
                    # recherches thématiques on s'en sert comme nom de source.
                    ancien = ligne["dt"] < "2026-09-27"
                    if ancien and ligne["source"] == "Google Actualités" and " - " in ligne["title"]:
                        titre, editeur = ligne["title"].rsplit(" - ", 1)
                        ligne["title"] = titre.strip()
                        ligne["source"] = f"{editeur.strip()} (via Google Actualités)"
                    elif ancien and ligne["source"].endswith("(via Google Actualités)") and " - " in ligne["title"]:
                        ligne["title"] = ligne["title"].rsplit(" - ", 1)[0].strip()
                    f.write(json.dumps(ligne, ensure_ascii=False) + "\n")

    # Purge : on garde le mois en cours + ARCHIVE_MOIS_CONSERVES mois pleins.
    annee, mois = now.year, now.month
    for _ in range(ARCHIVE_MOIS_CONSERVES):
        mois -= 1
        if mois == 0:
            annee, mois = annee - 1, 12
    limite = f"{annee:04d}-{mois:02d}"

    index = []
    for nom in sorted(os.listdir(ARCHIVE_DIR)):
        if not re.fullmatch(r"\d{4}-\d{2}\.jsonl", nom):
            continue
        cle = nom[:7]
        chemin = os.path.join(ARCHIVE_DIR, nom)
        if cle < limite:
            os.remove(chemin)
            continue
        with open(chemin, "r", encoding="utf-8") as f:
            n = sum(1 for line in f if line.strip())
        index.append({"mois": cle, "fichier": nom, "articles": n})

    with open(os.path.join(ARCHIVE_DIR, "index.json"), "w", encoding="utf-8") as f:
        json.dump({"genere_le": now.isoformat(), "mois": index}, f, ensure_ascii=False, indent=1)

    total = sum(m["articles"] for m in index)
    print(f"OK : archive longue à jour ({len(index)} mois, {total} articles)", file=sys.stderr)


def save_history(history):
    with open(HISTORY_PATH, "w", encoding="utf-8") as f:
        for item in history:
            f.write(json.dumps(item, ensure_ascii=False) + "\n")


def week_bounds(now):
    """Semaine calendaire la plus récemment terminée, lundi 00:00 à dimanche 23:59 UTC."""
    today = now.date()
    days_since_sunday = (today.weekday() - 6) % 7  # 0 si aujourd'hui est dimanche
    last_sunday = today - timedelta(days=days_since_sunday)
    monday = last_sunday - timedelta(days=6)
    start = datetime.combine(monday, datetime.min.time(), tzinfo=timezone.utc)
    end = datetime.combine(last_sunday, datetime.max.time(), tzinfo=timezone.utc)
    return start, end


def month_bounds(now):
    """Mois civil le plus récemment terminé."""
    today = now.date()
    first_of_this_month = today.replace(day=1)
    last_of_prev_month = first_of_this_month - timedelta(days=1)
    first_of_prev_month = last_of_prev_month.replace(day=1)
    start = datetime.combine(first_of_prev_month, datetime.min.time(), tzinfo=timezone.utc)
    end = datetime.combine(last_of_prev_month, datetime.max.time(), tzinfo=timezone.utc)
    return start, end


def render_digest(path, titre, description, history, start, end, cap_normal, cap_une, now):
    lines = [f"# {titre} — généré le {now.strftime('%Y-%m-%d %H:%M UTC')}", ""]
    lines.append(description)
    lines.append("")

    by_rubrique = {}
    for item in history:
        dt = item.get("dt")
        if dt is None:
            continue
        dt = datetime.fromisoformat(dt)
        if not (start <= dt <= end):
            continue
        by_rubrique.setdefault(item["rubrique_num"], []).append(item)

    total_items = 0
    for num, nom, _ in RUBRIQUES:
        lines.append(f"## {num}. {nom}" if num > 0 else f"## {nom}")
        items = by_rubrique.get(num, [])
        if not items:
            lines.append("_Rien de retenu par les flux pour cette rubrique sur la période._")
        else:
            items.sort(key=lambda it: it["dt"], reverse=True)
            plafond = cap_une if num == 0 else cap_normal
            items = items[:plafond]
            for item in items:
                lines.append(f"- **{item['title']}** — {item['source']} ({item['date']}) — {item['url']}")
            total_items += len(items)
        lines.append("")

    lines.append(f"---\n\nTotal d'entrées sur la période : {total_items}.")

    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(f"OK : {total_items} entrées écrites dans {path}", file=sys.stderr)


def main():
    seen_urls = set()
    seen_titles = set()
    now = datetime.now(timezone.utc)

    daily_lines = [f"# Digest RSS quotidien — généré le {now.strftime('%Y-%m-%d %H:%M UTC')}", ""]
    daily_lines.append(
        "Ce fichier est une collecte brute de flux RSS (directs ou via Google "
        f"Actualités par site), filtrée sur les dernières {FRAICHEUR_HEURES}h et "
        "dédoublonnée. Aucun tri éditorial n'a été fait : la sélection, la "
        "hiérarchisation et la vérification restent à faire."
    )
    daily_lines.append("")

    daily_total = 0
    new_history_items = []

    for num, nom, flux in RUBRIQUES:
        daily_lines.append(f"## {num}. {nom}" if num > 0 else f"## {nom}")
        pool = []
        for source_name, url in flux:
            print(f"Rubrique {num} — {nom} : {source_name}", file=sys.stderr)
            for item in fetch_feed(source_name, url, HISTORIQUE_HEURES):
                key_url = item["link"].strip().rstrip("/")
                key_title = normalize_for_dedupe(item["title"])
                if key_url in seen_urls or key_title in seen_titles:
                    continue
                seen_urls.add(key_url)
                seen_titles.add(key_title)
                pool.append(item)

        if not pool:
            daily_lines.append("_Rien de neuf remonté par les flux pour cette rubrique._")
            daily_lines.append("")
            continue

        # Plus récent d'abord ; une entrée sans date connue est traitée comme
        # la plus récente (comportement historique, pour ne pas la perdre).
        pool.sort(key=lambda it: it["dt"] or now, reverse=True)
        plafond_archive = MAX_ITEMS_UNE if num == 0 else MAX_ITEMS_PAR_RUBRIQUE
        pool = pool[:plafond_archive]

        # Sous-ensemble des dernières 24h (+ dates inconnues) pour le digest
        # quotidien : comme le tri ci-dessus place déjà les entrées connues
        # les plus récentes en tête, ce sous-ensemble reproduit exactement
        # ce qu'aurait donné une collecte directe à 24h.
        cutoff_24h = now - timedelta(hours=FRAICHEUR_HEURES)
        daily_items = [it for it in pool if it["dt"] is None or it["dt"] >= cutoff_24h]
        for item in daily_items:
            daily_lines.append(f"- **{item['title']}** — {item['source']} ({item['date']}) — {item['link']}")
        daily_total += len(daily_items)
        daily_lines.append("")

        # Archive (pour les digests hebdomadaire et mensuel) : uniquement les
        # entrées dont on connaît la date, sinon impossible de les situer
        # dans une semaine ou un mois.
        for item in pool:
            if item["dt"] is None:
                continue
            new_history_items.append({
                "url": item["link"].strip().rstrip("/"),
                "title": item["title"],
                "source": item["source"],
                "date": item["date"],
                "dt": item["dt"].isoformat(),
                "rubrique_num": num,
            })

    daily_lines.append(f"---\n\nTotal d'entrées collectées après dédoublonnage : {daily_total}.")
    with open("digest/latest.md", "w", encoding="utf-8") as f:
        f.write("\n".join(daily_lines) + "\n")
    print(f"OK : {daily_total} entrées écrites dans digest/latest.md", file=sys.stderr)

    # --- Archive persistante ---
    history = load_history()
    existing_urls = {h["url"] for h in history}
    added = 0
    for item in new_history_items:
        if item["url"] in existing_urls:
            continue
        history.append(item)
        existing_urls.add(item["url"])
        added += 1

    prune_cutoff = now - timedelta(days=HISTORIQUE_JOURS_CONSERVES)
    before_prune = len(history)
    history = [h for h in history if datetime.fromisoformat(h["dt"]) >= prune_cutoff]
    pruned = before_prune - len(history)
    save_history(history)
    update_archive(history, now)
    print(f"OK : archive mise à jour ({added} ajoutées, {pruned} purgées, {len(history)} au total)", file=sys.stderr)

    # --- Digest hebdomadaire ---
    week_start, week_end = week_bounds(now)
    render_digest(
        "digest/week.md",
        "Digest RSS hebdomadaire",
        "Ce fichier regroupe, par rubrique, les entrées RSS archivées dont la "
        f"date se situe entre le {week_start.strftime('%Y-%m-%d')} et le "
        f"{week_end.strftime('%Y-%m-%d')} (semaine calendaire complète la plus "
        "récente, lundi à dimanche). Aucun tri éditorial n'a été fait.",
        history, week_start, week_end,
        MAX_ITEMS_PAR_RUBRIQUE_SEMAINE, MAX_ITEMS_UNE_SEMAINE, now,
    )

    # --- Digest mensuel ---
    month_start, month_end = month_bounds(now)
    render_digest(
        "digest/month.md",
        "Digest RSS mensuel",
        "Ce fichier regroupe, par rubrique, les entrées RSS archivées dont la "
        f"date se situe entre le {month_start.strftime('%Y-%m-%d')} et le "
        f"{month_end.strftime('%Y-%m-%d')} (mois civil écoulé le plus récent). "
        "Aucun tri éditorial n'a été fait.",
        history, month_start, month_end,
        MAX_ITEMS_PAR_RUBRIQUE_MOIS, MAX_ITEMS_UNE_MOIS, now,
    )


if __name__ == "__main__":
    main()
