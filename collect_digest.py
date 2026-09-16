#!/usr/bin/env python3
"""
Collecte les flux RSS de la revue de presse quotidienne de Mayeul et produit
un digest markdown unique, groupé par rubrique, filtré sur les dernières 48h.

Ce script ne fait AUCUN travail éditorial (pas de hiérarchisation, pas de
vérification de fond) : il se contente de rassembler et nettoyer la matière
première, pour que Claude n'ait plus qu'une seule page propre à lire au lieu
de devoir chercher lui-même sur le web. Le travail éditorial (choix de la
Une, vérification, rédaction, mise en page) reste fait par Claude à partir
de ce digest.

Deux types de sources sont utilisées :
- Flux RSS propres au média (le plus précis, marqué tel quel).
- Recherche Google Actualités limitée à un site précis ("site:domaine"),
  utilisée quand le média n'a pas de flux RSS public fiable ou documenté :
  ça reste un flux RSS (Google Actualités en fournit un par requête), donc
  ça marche exactement pareil, juste un cran moins direct. Ces entrées sont
  marquées "(via Google Actualités)" dans le digest pour rester transparent
  sur l'origine.

Usage: python3 collect_digest.py
Écrit digest/latest.md dans le répertoire courant.
"""

import re
import sys
import time
import urllib.parse
from datetime import datetime, timedelta, timezone

import feedparser
import requests

FRAICHEUR_HEURES = 60
MAX_ITEMS_PAR_FLUX = 20
TIMEOUT = 15


def google_news(query):
    q = urllib.parse.quote(query)
    return f"https://news.google.com/rss/search?q={q}&hl=fr&gl=FR&ceid=FR:fr"


def gsite(nom, domaine, extra=""):
    """Source sans flux RSS propre fiable : on prend ses articles récents
    via Google Actualités, filtré sur son domaine. Le paramètre extra
    permet d'ajouter des mots-clés (utile pour restreindre à une section)."""
    query = f"site:{domaine} {extra}".strip()
    return (f"{nom} (via Google Actualités)", google_news(query))


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
        ("Google Actualités", google_news("Assemblée nationale OR gouvernement OR Sénat")),
        gsite("La Croix", "la-croix.com", "politique"),
        gsite("L'Humanité", "humanite.fr", "politique"),
        gsite("L'Opinion", "lopinion.fr", "politique"),
    ]),
    (2, "Justice, police et sécurité intérieure", [
        ("franceinfo", "https://www.francetvinfo.fr/faits-divers.rss"),
        ("Le Parisien", "https://feeds.leparisien.fr/leparisien/rss"),
        ("Google Actualités", google_news("procès OR tribunal OR garde à vue OR Cour de cassation")),
        gsite("OCCRP", "occrp.org"),
    ]),
    (3, "Défense et armées", [
        ("Opex360 / Zone Militaire", "https://www.opex360.com/feed/"),
        ("Google Actualités", google_news("armée française OR défense OR OTAN OR militaire")),
    ]),
    (4, "Économie française et social", [
        ("Le Monde", "https://www.lemonde.fr/economie/rss_full.xml"),
        ("Les Échos", "https://services.lesechos.fr/rss/les-echos-economie.xml"),
        ("franceinfo", "https://www.francetvinfo.fr/economie.rss"),
        ("Google Actualités", google_news("budget OR chômage OR salaires OR grève France")),
        gsite("La Tribune", "latribune.fr"),
        gsite("Alternatives Économiques", "alternatives-economiques.fr"),
    ]),
    (5, "Union européenne", [
        ("Euractiv France", "https://euractiv.fr/feed/"),
        ("Google Actualités", google_news("Commission européenne OR Parlement européen OR Bruxelles UE")),
        gsite("Contexte", "contexte.com"),
    ]),
    (6, "Europe (pays)", [
        ("Google Actualités", google_news("Allemagne OR Italie OR Espagne OR Royaume-Uni politique")),
        gsite("Der Spiegel International", "spiegel.de/international"),
        gsite("El País", "elpais.com"),
    ]),
    (7, "Guerres et conflits", [
        ("Le Monde", "https://www.lemonde.fr/international/rss_full.xml"),
        ("France 24", "https://www.france24.com/fr/moyen-orient/rss"),
        ("Google Actualités", google_news("Ukraine OR Gaza OR Sahel guerre")),
        ("The Moscow Times", "https://www.themoscowtimes.com/rss/news"),
        ("Meduza (English)", "https://meduza.io/rss/en/all"),
        gsite("Reuters", "reuters.com"),
        gsite("Kyiv Independent", "kyivindependent.com"),
    ]),
    (8, "Amériques", [
        ("Google Actualités", google_news("États-Unis OR Washington OR Amérique latine")),
        ("MercoPress", "https://en.mercopress.com/rss/"),
        gsite("Associated Press", "apnews.com"),
        gsite("New York Times", "nytimes.com"),
        gsite("BBC Mundo", "bbc.com/mundo"),
    ]),
    (9, "Asie et Océanie", [
        ("Google Actualités", google_news("Chine OR Inde OR Japon OR Taïwan")),
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
        ("Google Actualités", google_news("Afrique OR Algérie OR Maroc OR Sahel")),
        ("Jeune Afrique", "https://www.jeuneafrique.com/feed/"),
        ("AllAfrica", "https://allafrica.com/tools/headlines/rdf/latest/headlines.rdf"),
        ("Daily Maverick", "https://www.dailymaverick.co.za/dmrss/"),
        gsite("The Continent", "continent.substack.com"),
    ]),
    (11, "Économie mondiale, marchés et énergie", [
        ("Google Actualités", google_news("BCE OR Fed OR pétrole OR marchés OR inflation")),
        gsite("Financial Times", "ft.com"),
        gsite("Reuters Business", "reuters.com", "business"),
    ]),
    (12, "Sciences, technologies et numérique", [
        ("Le Monde", "https://www.lemonde.fr/sciences/rss_full.xml"),
        ("Next", "https://next.ink/feed/"),
        ("Google Actualités", google_news("intelligence artificielle OR cybersécurité OR espace recherche")),
        ("Rest of World", "https://restofworld.org/feed/latest/"),
    ]),
    (13, "Environnement et climat", [
        ("Le Monde", "https://www.lemonde.fr/planete/rss_full.xml"),
        ("Reporterre", "https://reporterre.net/spip.php?page=backend"),
        ("Carbon Brief", "https://www.carbonbrief.org/feed/"),
    ]),
    (14, "Agriculture et alimentation", [
        ("Google Actualités", google_news("agriculteurs OR PAC OR élevage OR récolte")),
        gsite("La France Agricole", "lafranceagricole.fr"),
    ]),
    (15, "Santé et protection sociale", [
        ("franceinfo", "https://www.francetvinfo.fr/sante.rss"),
        ("Google Actualités", google_news("hôpital OR Sécurité sociale OR médicament OR retraites")),
    ]),
    (16, "Éducation et enseignement supérieur", [
        ("Google Actualités", google_news("école OR université OR Parcoursup OR enseignants")),
        gsite("Café pédagogique", "cafepedagogique.net"),
    ]),
    (17, "Société et migrations", [
        ("Le Monde", "https://www.lemonde.fr/societe/rss_full.xml"),
        ("Google Actualités", google_news("immigration OR logement OR laïcité OR démographie France")),
        ("The New Humanitarian", "https://www.thenewhumanitarian.org/rss/all.xml"),
    ]),
    (18, "Transports et villes", [
        ("Google Actualités", google_news("SNCF OR RATP OR transports OR urbanisme")),
    ]),
    (19, "Île-de-France et Paris", [
        ("Le Parisien", "https://feeds.leparisien.fr/leparisien/rss"),
        ("Google Actualités", google_news("Paris OR Île-de-France mairie OR conseil régional")),
    ]),
    (20, "Médias et journalisme", [
        ("Google Actualités", google_news("Arcom OR rédaction OR audiences OR liberté de la presse")),
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


def fetch_feed(name, url):
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

    cutoff = datetime.now(timezone.utc) - timedelta(hours=FRAICHEUR_HEURES)
    for entry in parsed.entries[:MAX_ITEMS_PAR_FLUX * 2]:
        dt = parse_entry_datetime(entry)
        if dt is not None and dt < cutoff:
            continue
        title = clean_title(entry.get("title"))
        link = entry.get("link")
        if not title or not link:
            continue
        date_str = dt.strftime("%Y-%m-%d %H:%M UTC") if dt else "date inconnue"
        items.append({"title": title, "link": link, "source": name, "date": date_str, "dt": dt})
        if len(items) >= MAX_ITEMS_PAR_FLUX:
            break
    return items


def normalize_for_dedupe(title):
    t = title.lower()
    t = re.sub(r"[^a-z0-9àâäéèêëïîôöùûüç ]", "", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t


def main():
    seen_urls = set()
    seen_titles = set()
    lines = []
    now = datetime.now(timezone.utc)
    lines.append(f"# Digest RSS quotidien — généré le {now.strftime('%Y-%m-%d %H:%M UTC')}")
    lines.append("")
    lines.append(
        "Ce fichier est une collecte brute de flux RSS (directs ou via Google "
        f"Actualités par site), filtrée sur les dernières {FRAICHEUR_HEURES}h et "
        "dédoublonnée. Aucun tri éditorial n'a été fait : la sélection, la "
        "hiérarchisation et la vérification restent à faire."
    )
    lines.append("")

    total_items = 0
    for num, nom, flux in RUBRIQUES:
        lines.append(f"## {num}. {nom}" if num > 0 else f"## {nom}")
        rubrique_items = []
        for source_name, url in flux:
            print(f"Rubrique {num} — {nom} : {source_name}", file=sys.stderr)
            for item in fetch_feed(source_name, url):
                key_url = item["link"].strip().rstrip("/")
                key_title = normalize_for_dedupe(item["title"])
                if key_url in seen_urls or key_title in seen_titles:
                    continue
                seen_urls.add(key_url)
                seen_titles.add(key_title)
                rubrique_items.append(item)

        if not rubrique_items:
            lines.append("_Rien de neuf remonté par les flux pour cette rubrique._")
        else:
            rubrique_items.sort(key=lambda it: it["dt"] or now, reverse=True)
            for item in rubrique_items:
                lines.append(f"- **{item['title']}** — {item['source']} ({item['date']}) — {item['link']}")
            total_items += len(rubrique_items)
        lines.append("")

    lines.append(f"---\n\nTotal d'entrées collectées après dédoublonnage : {total_items}.")

    with open("digest/latest.md", "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(f"OK : {total_items} entrées écrites dans digest/latest.md", file=sys.stderr)


if __name__ == "__main__":
    main()
