#!/usr/bin/env python3
"""
Outils de révision pour les concours des écoles de journalisme, construits à
partir de l'archive de la revue de presse (digest/archive/AAAA-MM.jsonl).

Deux productions, regénérées chaque nuit par la GitHub Action, juste après la
collecte des flux :

1. QCM d'actualité (digest/revisions/qcm/AAAA-MM.json)
   Chaque jour, une douzaine de questions sur l'actualité de la veille.
   - Avec une clé API Claude (secret ANTHROPIC_API_KEY) : vraies questions de
     QCM rédigées à partir des titres de la journée, avec explication.
   - Sans clé : questions « texte à trous » générées automatiquement (on
     masque un pays, une personnalité ou un chiffre dans un titre et on
     propose des leurres tirés de l'archive). Moins riches, mais gratuites.

2. Fiches de synthèse thématiques (digest/revisions/fiches/AAAA-MM.json + .md)
   Pour chaque mois, les grands sujets sont repérés automatiquement (entités
   et mots qui reviennent le plus dans les titres, regroupés par sujet), avec
   une chronologie jour par jour et les liens vers les articles.
   - Avec une clé API Claude : chaque fiche reçoit en plus une synthèse
     (résumé, contexte, enjeux, acteurs, chiffres clés, ce qu'il faut retenir
     pour le concours, questions possibles à l'oral).

Comme pour collect_digest.py, la matière première, ce sont uniquement les
TITRES (pas le texte des articles). Les questions et synthèses s'appuient
donc sur ce que disent les titres : chaque question et chaque fiche renvoie
vers ses sources pour pouvoir vérifier.

La page revisions.html (à publier avec GitHub Pages) lit ces fichiers et
sert d'outil d'entraînement : QCM du jour, concours blanc, répétition
espacée des questions ratées, statistiques par rubrique et fiches.

Usage :
    python3 revisions.py                 # run quotidien
    python3 revisions.py --rattrapage 30 # (re)génère les QCM manquants des 30 derniers jours
    python3 revisions.py --sans-ia       # force le mode sans API, même si une clé existe
"""

import argparse
import glob
import json
import math
import os
import random
import re
import sys
import unicodedata
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta, timezone

ARCHIVE_DIR = "digest/archive"
OUT_DIR = "digest/revisions"
QCM_DIR = os.path.join(OUT_DIR, "qcm")
FICHES_DIR = os.path.join(OUT_DIR, "fiches")

MODELE = "claude-opus-5-5"

QUESTIONS_PAR_JOUR = 12
MAX_TITRES_PROMPT_QCM = 220       # titres envoyés à Claude pour un QCM quotidien
JOURS_RATTRAPAGE_AUTO = 3         # jours manqués rattrapés automatiquement à chaque run
MAX_APPELS_IA_QCM = 4             # plafond d'appels IA pour les QCM par run
MAX_APPELS_IA_FICHES = 8          # plafond d'appels IA pour les fiches par run
SEUIL_REGEN_FICHE = 1.25          # resynthétiser une fiche si elle a grossi de 25 %

FICHES_PAR_MOIS = 15
MIN_ARTICLES_FICHE = 8
MAX_TITRES_CHRONO_PAR_JOUR = 4
MAX_TITRES_PROMPT_FICHE = 120

RUBRIQUE_NOMS = {
    0: "Une (recoupement presse nationale et régionale)",
    1: "Politique française",
    2: "Justice, police et sécurité intérieure",
    3: "Défense et armées",
    4: "Économie française et social",
    5: "Union européenne",
    6: "Europe (pays)",
    7: "Guerres et conflits",
    8: "Amériques",
    9: "Asie et Océanie",
    10: "Afrique et Maghreb",
    11: "Économie mondiale, marchés et énergie",
    12: "Sciences, technologies et numérique",
    13: "Environnement et climat",
    14: "Agriculture et alimentation",
    15: "Santé et protection sociale",
    16: "Éducation et enseignement supérieur",
    17: "Société et migrations",
    18: "Transports et villes",
    19: "Île-de-France et Paris",
    20: "Médias et journalisme",
    21: "Culture",
    22: "Sport",
    23: "Analyse de fond et investigation",
}

# ---------------------------------------------------------------------------
# Lexique
# ---------------------------------------------------------------------------

STOPWORDS = set("""
a à au aux avec ce ces cet cette c ça d dans de des du elle elles en entre et eux il ils
je j l la le les leur leurs lui m ma mais me même mes moi mon n ne ni nos notre nous on ou
où par pas pour qu que quel quelle quels quelles qui s sa sans se ses si son sont sur ta te
tes toi ton tu un une vos votre vous y été être est sont ont a ai avait avoir fait faire
plus moins très tout tous toute toutes après avant depuis pendant contre vers chez sous
selon comme quand alors aussi encore déjà bien peu non oui ici là cela celui celle ceux
dont lors face fin début jour jours semaine an ans année années mois heure heures hier
aujourd demain soir matin nouveau nouvelle nouveaux nouvelles premier première deux trois
quatre cinq six sept huit neuf dix cent mille millions milliards million milliard
faut peut doit veut va vont dit dire selon être sera serait seront pourrait entre
ce qu quoi comment pourquoi est-ce vidéo direct live info infos exclusif témoignage
the of and to in on for at by with from as is are was were be been it its this that
these those an or not but has have had will would can could after over into about than
new more says said say amid us up out who what why how his her their they he she we you
""".split())

MOIS_FR = {1: "janvier", 2: "février", 3: "mars", 4: "avril", 5: "mai", 6: "juin",
           7: "juillet", 8: "août", 9: "septembre", 10: "octobre", 11: "novembre",
           12: "décembre"}

JOURS_FR = ["lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche"]

# Pays et grandes entités géographiques (forme française usuelle dans les titres).
PAYS = """
France Allemagne Italie Espagne Portugal Belgique Suisse Royaume-Uni Irlande Pays-Bas
Luxembourg Autriche Pologne Hongrie Roumanie Bulgarie Grèce Chypre Malte Suède Norvège
Finlande Danemark Islande Estonie Lettonie Lituanie Tchéquie Slovaquie Slovénie Croatie
Serbie Bosnie Monténégro Albanie Macédoine Kosovo Moldavie Ukraine Russie Biélorussie
Géorgie Arménie Azerbaïdjan Turquie Israël Liban Syrie Jordanie Irak Iran Arabie Yémen
Oman Qatar Koweït Bahreïn Émirats Egypte Égypte Libye Tunisie Algérie Maroc Mauritanie
Mali Niger Tchad Soudan Éthiopie Erythrée Somalie Kenya Ouganda Rwanda Burundi Tanzanie
Congo Gabon Cameroun Nigeria Nigéria Ghana Togo Bénin Sénégal Guinée Côte-d'Ivoire
Burkina Liberia Angola Zambie Zimbabwe Mozambique Madagascar Namibie Botswana Afrique
Chine Japon Corée Taïwan Inde Pakistan Afghanistan Bangladesh Népal Birmanie Thaïlande
Vietnam Cambodge Laos Malaisie Singapour Indonésie Philippines Australie Nouvelle-Zélande
Kazakhstan Ouzbékistan Mongolie Etats-Unis États-Unis Canada Mexique Cuba Haïti Venezuela
Colombie Pérou Brésil Argentine Chili Bolivie Equateur Équateur Paraguay Uruguay Groenland
Gaza Cisjordanie Nouvelle-Calédonie Guadeloupe Martinique Guyane Mayotte Corse
""".split()

CHIFFRE_RE = re.compile(
    r"(?<![\w,.])(\d{1,3}(?:[  .]\d{3})+|\d+(?:[,.]\d+)?)(\s?%|\s?(?:millions?|milliards?|"
    r"euros?|€|ans|km|morts|personnes|jours|degrés|°C))?(?![\w])"
)

MOIS_RE = (r"(?:janvier|février|fevrier|mars|avril|mai|juin|juillet|août|aout|septembre|octobre|"
           r"novembre|décembre|decembre|january|february|march|april|may|june|july|august|"
           r"september|october|november|december|jan|feb|sept?|oct|nov|dec)\.?")
DATE_AVANT_RE = re.compile(r"(?:" + MOIS_RE + r"|lundi|mardi|mercredi|jeudi|vendredi|samedi|dimanche|"
                           r"[A-Z]{2,}|n°|no\.?|numéro|saison|épisode|tome|article|acte|cop|g)\s*$", re.I)
DATE_APRES_RE = re.compile(r"^\s*(?:er\b|e\b|ème\b)?\s*" + MOIS_RE + r"\b", re.I)

# Titres sans intérêt pour un QCM (grilles TV, émissions récurrentes, communiqués).
TITRES_EXCLUS_RE = re.compile(
    r"résumé et diffusions|programme tv|les informés|news briefs|droits de vote|"
    r"horoscope|replay|en direct|live|podcast|quiz|mots croisés|météo du", re.I)

TOKEN_RE = re.compile(r"[A-Za-zÀ-ÖØ-öø-ÿŒœ0-9][A-Za-zÀ-ÖØ-öø-ÿŒœ0-9\-]*")


def sans_accents(s):
    return "".join(c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn")


def tokens_titre(titre):
    """Liste de (mot, position, est_majuscule). Les élisions (l’, d’, qu’...)
    sont retirées. Position = index du mot dans le titre ou dans le segment
    qui suit une ponctuation forte (début de phrase : la majuscule n'y est
    pas significative)."""
    titre = titre.replace("’", "'")
    out = []
    pos = 0
    for brut in re.split(r"(\s+|[:«»\"“”?!.;,()\[\]|—–])", titre):
        if not brut or brut.isspace():
            continue
        if re.fullmatch(r"[:«»\"“”?!.;()\[\]|—–]", brut):
            pos = 0
            continue
        if brut == ",":
            continue
        mot = brut.split("'")[-1] if "'" in brut[:3] else brut
        mot = mot.strip("'-")
        if not mot or not TOKEN_RE.fullmatch(mot):
            pos += 1
            continue
        out.append((mot, pos, mot[0].isupper()))
        pos += 1
    return out


# ---------------------------------------------------------------------------
# Archive
# ---------------------------------------------------------------------------

def charger_archive():
    items = []
    for chemin in sorted(glob.glob(os.path.join(ARCHIVE_DIR, "*.jsonl"))):
        with open(chemin, "r", encoding="utf-8") as f:
            for ligne in f:
                ligne = ligne.strip()
                if not ligne:
                    continue
                try:
                    it = json.loads(ligne)
                except json.JSONDecodeError:
                    continue
                if not it.get("dt") or not it.get("title"):
                    continue
                it["_dt"] = datetime.fromisoformat(it["dt"])
                items.append(it)
    # Dédoublonnage par titre normalisé (même dépêche reprise par plusieurs flux).
    vus, uniques = set(), []
    for it in sorted(items, key=lambda x: x["_dt"]):
        cle = sans_accents(it["title"].lower())
        cle = re.sub(r"\W+", " ", cle).strip()
        if cle in vus:
            continue
        vus.add(cle)
        uniques.append(it)
    return uniques


def construire_lexique(items):
    """Repère les noms propres : mots qui apparaissent avec une majuscule en
    milieu de titre (donc pas juste parce qu'ils ouvrent la phrase) et
    presque jamais en minuscule."""
    maj_milieu, minus = Counter(), Counter()
    for it in items:
        for mot, pos, maj in tokens_titre(it["title"]):
            if mot.isdigit():
                continue
            if maj and pos > 0:
                maj_milieu[mot] += 1
            elif not maj:
                minus[mot.lower()] += 1
    propres = set()
    for mot, n in maj_milieu.items():
        if n >= 2 and minus.get(mot.lower(), 0) <= n * 0.25 and mot.lower() not in STOPWORDS:
            if len(mot) > 1 and not mot.isupper() or 2 <= len(mot) <= 6:
                propres.add(mot)
    return propres


def entites_titre(titre, propres):
    """Suites de noms propres consécutifs (« Jean-Noël Barrot », « Union
    européenne » ne marche pas, mais « Marine Le Pen » oui grâce aux
    particules)."""
    toks = tokens_titre(titre)
    particules = {"de", "du", "des", "la", "le", "von", "van", "al", "el", "ben", "bin"}
    runs, courant = [], []
    for i, (mot, pos, maj) in enumerate(toks):
        est_propre = mot in propres or mot in PAYS
        if est_propre:
            courant.append(mot)
        elif courant and mot.lower() in particules and i + 1 < len(toks) and toks[i + 1][0] in propres:
            courant.append(mot)
        else:
            if courant:
                runs.append(" ".join(courant))
            courant = []
    if courant:
        runs.append(" ".join(courant))
    return [r for r in runs if r.split()[-1].lower() not in particules]


# ---------------------------------------------------------------------------
# Appels à Claude (optionnels)
# ---------------------------------------------------------------------------

def client_claude(sans_ia):
    if sans_ia or not os.environ.get("ANTHROPIC_API_KEY"):
        return None
    try:
        import anthropic
    except ImportError:
        print("SDK anthropic absent : mode sans IA.", file=sys.stderr)
        return None
    return anthropic.Anthropic()


def appel_structure(client, systeme, contenu, schema, effort="medium"):
    """Appel Claude avec sortie structurée validée par Pydantic. Renvoie
    l'objet validé, ou None si l'appel échoue (le script retombe alors sur le
    mode sans IA, la collecte ne doit jamais casser à cause de ça)."""
    import anthropic
    try:
        reponse = client.beta.messages.parse(
            model=MODELE,
            max_tokens=16000,
            system=systeme,
            messages=[{"role": "user", "content": contenu}],
            output_format=schema,
            output_config={"effort": effort},
            betas=["server-side-fallback-2026-07-01"],
            fallbacks="default",
        )
    except anthropic.APIConnectionError as e:
        print(f"Claude injoignable : {e}", file=sys.stderr)
        return None
    except anthropic.RateLimitError:
        print("Claude : limite de débit atteinte.", file=sys.stderr)
        return None
    except anthropic.APIStatusError as e:
        print(f"Claude : erreur {e.status_code} : {e.message}", file=sys.stderr)
        return None
    except Exception as e:  # validation Pydantic, réponse inattendue...
        print(f"Claude : réponse inexploitable ({type(e).__name__}: {e})", file=sys.stderr)
        return None
    if reponse.stop_reason in ("refusal", "max_tokens"):
        print(f"Claude : arrêt « {reponse.stop_reason} », réponse ignorée.", file=sys.stderr)
        return None
    return reponse.parsed_output


# ---------------------------------------------------------------------------
# QCM
# ---------------------------------------------------------------------------

SYSTEME_QCM = """Tu prépares des étudiants aux concours d'entrée des écoles de journalisme \
françaises (CFJ, ESJ Lille, CELSA, IPJ, IJBA, CUEJ, EJT...). L'épreuve de \
connaissance de l'actualité est un QCM exigeant : noms de personnalités et de \
fonctions, pays, institutions, chiffres marquants, événements.

On te donne la liste numérotée des titres de presse d'une journée, classés \
par rubrique. Rédige des questions de QCM en français à partir de ces titres.

Règles impératives :
- Chaque question repose sur UN titre précis (source_index = son numéro). Le \
fait demandé doit être explicitement contenu dans ce titre : n'invente rien, \
ne complète pas avec des faits récents que le titre ne donne pas.
- Tu peux t'appuyer sur la culture générale stable (capitale, institution, \
fonction connue de longue date) pour formuler la question ou les leurres, \
jamais pour la bonne réponse d'un fait d'actualité.
- 4 propositions, une seule juste, leurres plausibles et du même type que la \
réponse (quatre pays, quatre ministres, quatre ordres de grandeur...).
- Privilégie ce qui tombe aux concours : politique française et \
internationale, conflits, économie, Europe, société, sciences, culture, \
médias. Varie les rubriques. Évite les faits divers anecdotiques, les \
résultats sportifs mineurs, la promo et les titres trop vagues.
- La question doit se comprendre seule, sans voir le titre (donne le contexte \
utile : « Début novembre 2026, ... »).
- L'explication (1 à 2 phrases) rappelle le fait et son contexte, utile pour \
réviser.
- Titres en anglais : la question reste en français."""


def schema_qcm():
    from typing import List, Literal
    from pydantic import BaseModel, Field

    class QuestionIA(BaseModel):
        question: str
        choix: List[str] = Field(description="Exactement 4 propositions")
        bonne_reponse: int = Field(description="Index (0 à 3) de la bonne proposition dans choix")
        explication: str
        source_index: int = Field(description="Numéro du titre sur lequel repose la question")
        difficulte: Literal["facile", "moyen", "difficile"]

    class QCMIA(BaseModel):
        questions: List[QuestionIA]

    return QCMIA


def selectionner_titres_jour(items_jour, n):
    """Répartit le quota de titres entre rubriques (la rubrique 0, très
    généraliste, ne doit pas tout écraser)."""
    par_rub = defaultdict(list)
    for it in items_jour:
        par_rub[it["rubrique_num"]].append(it)
    for lst in par_rub.values():
        lst.sort(key=lambda x: x["_dt"], reverse=True)
    choisis = []
    while len(choisis) < n and any(par_rub.values()):
        for rub in sorted(par_rub):
            if par_rub[rub] and len(choisis) < n:
                choisis.append(par_rub[rub].pop(0))
    return choisis


def qcm_ia(client, jour, items_jour):
    titres = selectionner_titres_jour(items_jour, MAX_TITRES_PROMPT_QCM)
    if len(titres) < 20:
        return None
    lignes = [f"Journée du {jour_fr(jour)}. {len(titres)} titres.\n"]
    for i, it in enumerate(titres):
        lignes.append(f"[{i}] ({RUBRIQUE_NOMS.get(it['rubrique_num'], '')}) {it['title']} — {it['source']}")
    lignes.append(f"\nRédige {QUESTIONS_PAR_JOUR} questions.")
    res = appel_structure(client, SYSTEME_QCM, "\n".join(lignes), schema_qcm())
    if res is None:
        return None
    questions = []
    for q in res.questions:
        if len(q.choix) != 4 or not (0 <= q.bonne_reponse < 4) or not (0 <= q.source_index < len(titres)):
            continue
        if len({c.strip().lower() for c in q.choix}) != 4:
            continue
        src = titres[q.source_index]
        bonne = q.choix[q.bonne_reponse]
        choix = list(q.choix)
        random.shuffle(choix)  # Claude a tendance à mettre la bonne réponse en premier
        questions.append({
            "type": "qcm",
            "question": q.question.strip(),
            "choix": choix,
            "reponse": choix.index(bonne),
            "explication": q.explication.strip(),
            "difficulte": q.difficulte,
            **source_question(src),
        })
    return questions or None


def source_question(it):
    return {
        "rubrique_num": it["rubrique_num"],
        "rubrique": RUBRIQUE_NOMS.get(it["rubrique_num"], ""),
        "titre_source": it["title"],
        "media": it["source"],
        "url": it["url"],
        "date": it["_dt"].date().isoformat(),
    }


def leurres_chiffre(valeur, suffixe):
    """Trois leurres numériques plausibles autour de la vraie valeur."""
    brut = valeur.replace(" ", "").replace(" ", "").replace(".", "") if re.search(r"\d[  .]\d{3}", valeur) else valeur
    try:
        v = float(brut.replace(",", "."))
    except ValueError:
        return None
    if v < 2:
        return None
    entier = "," not in valeur and "." not in brut
    if suffixe.strip() == "%" and v <= 100:
        candidats = [v / 2, v * 1.5, v * 2, v - 10, v + 10, v / 3]
        candidats = [c for c in candidats if 0 < c <= 100]
    elif 1900 <= v <= 2100 and entier:
        return None  # une année : trop facile ou ambigu
    else:
        candidats = [v / 10, v / 2, v * 2, v * 3, v * 10, v * 1.5]
    vus, out = {v}, []
    random.shuffle(candidats)
    for c in candidats:
        c = round(c) if entier or c >= 10 else round(c, 1)
        if c > 0 and c not in vus:
            vus.add(c)
            txt = f"{c:,}".replace(",", " ") if entier else str(c).replace(".", ",")
            out.append(txt + suffixe)
        if len(out) == 3:
            return out
    return None


def qcm_texte_a_trous(jour, items_jour, propres, freq_entites, freq_par_rub, rng):
    """Questions générées sans IA : un pays, une personnalité ou un chiffre est
    masqué dans le titre, avec trois leurres du même type tirés de l'archive."""
    pays_freq = [e for e, _ in freq_entites.most_common() if e in PAYS][:60]

    def nom_valide(e):
        mots = e.split()
        return (len(mots) >= 2 and len(set(mots)) == len(mots) and not any(m in PAYS for m in mots)
                and freq_entites[e] >= 3)

    personnes_freq = [e for e, _ in freq_entites.most_common() if nom_valide(e)][:300]
    candidats = []
    for it in items_jour:
        titre = it["title"]
        if len(titre) < 40 or len(titre) > 220 or TITRES_EXCLUS_RE.search(titre):
            continue
        ents = entites_titre(titre, propres)
        options = []
        for e in ents:
            # « Nigeria: ... » (préfixe de dépêche) : la réponse est donnée par le reste du titre.
            if re.match(re.escape(e) + r"\s*:", titre):
                continue
            if e in PAYS and len(pays_freq) >= 10:
                pool = [p for p in pays_freq if p != e and sans_accents(p) != sans_accents(e)]
                options.append(("pays", e, rng.sample(pool[:30], 3)))
            elif nom_valide(e) and len(personnes_freq) >= 20:
                # Leurres pris dans la même rubrique : on oppose un politique à
                # des politiques, un artiste à des artistes.
                pool = [p for p, _ in freq_par_rub[it["rubrique_num"]].most_common(60)
                        if nom_valide(p) and p != e and not set(p.split()) & set(e.split())]
                if len(pool) < 8:
                    pool = [p for p in personnes_freq if p != e and not set(p.split()) & set(e.split())]
                # Pas deux variantes d'un même nom (« Flávio » / « Flavio »).
                vus, uniques = {sans_accents(e).lower()}, []
                for p in pool[:40]:
                    k = sans_accents(p).lower()
                    if k not in vus:
                        vus.add(k)
                        uniques.append(p)
                if len(uniques) >= 3:
                    options.append(("nom", e, rng.sample(uniques, 3)))
        for m in CHIFFRE_RE.finditer(titre):
            # Dates (« lundi 9 novembre », « November 9 »), numéros (COP 31,
            # saison 3) : à masquer, ça ne teste rien.
            if DATE_AVANT_RE.search(titre[:m.start()]) or DATE_APRES_RE.match(titre[m.end():]):
                continue
            if titre[max(0, m.start() - 1):m.start()] in "/-." and m.start() > 0 or titre[m.end():m.end() + 1] in ("/", "-"):
                continue
            leurres = leurres_chiffre(m.group(1), m.group(2) or "")
            if leurres:
                options.append(("chiffre", m.group(0).strip(), leurres))
        if not options:
            continue
        # Priorité aux chiffres et aux personnalités, plus formateurs que les pays.
        poids = {"chiffre": 3, "nom": 2, "pays": 1}
        options.sort(key=lambda o: poids[o[0]], reverse=True)
        genre, reponse, leurres = options[0]
        trou = titre.replace(reponse, "_____", 1)
        if "_____" not in trou:
            continue
        candidats.append((poids[genre] + (0 if it["rubrique_num"] in (0, 22) else 1), it, genre, reponse, leurres, trou))

    rng.shuffle(candidats)
    candidats.sort(key=lambda c: c[0], reverse=True)
    questions, rubs, genres = [], Counter(), Counter()
    max_genre = {"chiffre": 5, "nom": 5, "pays": 3}
    for _, it, genre, reponse, leurres, trou in candidats:
        if rubs[it["rubrique_num"]] >= 2 or genres[genre] >= max_genre[genre]:
            continue
        rubs[it["rubrique_num"]] += 1
        genres[genre] += 1
        choix = leurres + [reponse]
        rng.shuffle(choix)
        intitule = {"pays": "Quel pays complète ce titre", "nom": "Qui ou quoi complète ce titre",
                    "chiffre": "Quel chiffre complète ce titre"}[genre]
        questions.append({
            "type": "texte_a_trous",
            "question": f"{intitule} ({it['source']}, {jour_fr(it['_dt'].date())}) ? « {trou} »",
            "choix": choix,
            "reponse": choix.index(reponse),
            "explication": f"Titre complet : « {it['title']} »",
            "difficulte": "moyen",
            **source_question(it),
        })
        if len(questions) >= QUESTIONS_PAR_JOUR:
            break
    return questions


def jour_fr(d):
    return f"{JOURS_FR[d.weekday()]} {d.day} {MOIS_FR[d.month]} {d.year}"


def charger_json(chemin, defaut):
    if os.path.exists(chemin):
        try:
            with open(chemin, "r", encoding="utf-8") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            pass
    return defaut


def ecrire_json(chemin, data):
    os.makedirs(os.path.dirname(chemin), exist_ok=True)
    tmp = chemin + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)
    os.replace(tmp, chemin)


def generer_qcm(items, propres, client, now, rattrapage):
    par_jour = defaultdict(list)
    for it in items:
        par_jour[it["_dt"].date()].append(it)

    freq_entites, freq_par_rub = Counter(), defaultdict(Counter)
    for it in items:
        for e in set(entites_titre(it["title"], propres)):
            freq_entites[e] += 1
            freq_par_rub[it["rubrique_num"]][e] += 1

    hier = now.date() - timedelta(days=1)
    premier_jour = min(par_jour) if par_jour else hier
    # Sans rattrapage explicite : tous les jours manquants en mode sans IA
    # (gratuit), et seulement les derniers jours en mode IA.
    fenetre_ia = rattrapage if rattrapage else JOURS_RATTRAPAGE_AUTO

    mois_cache = {}
    appels_ia = 0
    jours_ecrits = 0
    d = hier
    while d >= premier_jour:
        cle_mois = d.strftime("%Y-%m")
        chemin = os.path.join(QCM_DIR, f"{cle_mois}.json")
        if cle_mois not in mois_cache:
            mois_cache[cle_mois] = charger_json(chemin, {"mois": cle_mois, "jours": {}})
        data = mois_cache[cle_mois]
        existant = data["jours"].get(d.isoformat())
        dans_fenetre_ia = (hier - d).days < fenetre_ia
        plafond_ia = max(MAX_APPELS_IA_QCM, rattrapage)  # un rattrapage explicite lève le plafond
        veut_ia = client is not None and dans_fenetre_ia and appels_ia < plafond_ia
        a_faire = existant is None or (veut_ia and existant.get("mode") != "ia") or (rattrapage and dans_fenetre_ia)
        if a_faire and len(par_jour.get(d, [])) >= 20:
            questions, mode = None, "auto"
            if veut_ia:
                appels_ia += 1
                print(f"QCM {d} : génération par Claude…", file=sys.stderr)
                questions = qcm_ia(client, d, par_jour[d])
                mode = "ia" if questions else "auto"
            if not questions:
                if existant is not None and not (rattrapage and dans_fenetre_ia):
                    d -= timedelta(days=1)
                    continue  # on garde l'existant plutôt que de le dégrader
                rng = random.Random(d.toordinal())
                questions = qcm_texte_a_trous(d, par_jour[d], propres, freq_entites, freq_par_rub, rng)
            for i, q in enumerate(questions):
                q["id"] = f"{d.isoformat()}-{i:02d}"
            data["jours"][d.isoformat()] = {"mode": mode, "genere_le": now.isoformat(timespec="seconds"),
                                            "questions": questions}
            jours_ecrits += 1
        d -= timedelta(days=1)

    for cle_mois, data in mois_cache.items():
        data["jours"] = dict(sorted(data["jours"].items(), reverse=True))
        ecrire_json(os.path.join(QCM_DIR, f"{cle_mois}.json"), data)

    # Purge au-delà de 13 mois, comme l'archive longue.
    limite = (now.date().replace(day=1) - timedelta(days=380)).strftime("%Y-%m")
    index = []
    for chemin in sorted(glob.glob(os.path.join(QCM_DIR, "????-??.json"))):
        cle = os.path.basename(chemin)[:7]
        if cle < limite:
            os.remove(chemin)
            continue
        data = charger_json(chemin, {"jours": {}})
        n = sum(len(j["questions"]) for j in data["jours"].values())
        index.append({"mois": cle, "fichier": os.path.basename(chemin), "jours": len(data["jours"]), "questions": n})
    ecrire_json(os.path.join(QCM_DIR, "index.json"), {"genere_le": now.isoformat(timespec="seconds"), "mois": index})
    print(f"OK : QCM ({jours_ecrits} jours écrits, {appels_ia} appels IA)", file=sys.stderr)


# ---------------------------------------------------------------------------
# Fiches thématiques
# ---------------------------------------------------------------------------

# Termes trop génériques pour définir un sujet à eux seuls.
GENERIQUES = set("""
france français française françaises europe européen européenne européens paris monde
pays gouvernement président présidente ministre état etats ia intelligence janvier février
mars avril mai juin juillet août septembre octobre novembre décembre lundi mardi mercredi
jeudi vendredi samedi dimanche russian ukrainian company announcement news report world
government state president people week year video photos analysis opinion interview
entretien tribune édito éditorial chronique enquête reportage portrait décryptage
mort morts ue briefs south african africa nouvelles
""".split())


def racine(mot):
    """Racinisation minimale pour rapprocher lycéen/lycéens/lycéenne,
    manifestation/manifestations, démocrate/démocrates."""
    w = sans_accents(mot.lower())
    if w.endswith("s") and len(w) > 4:
        w = w[:-1]
    if w.endswith("enne"):
        w = w[:-2]
    elif w.endswith("e") and len(w) > 5:
        w = w[:-1]
    return w


def termes_titre(titre, propres):
    """Termes utiles au repérage des sujets, sous forme {clé: forme affichée}.
    Entités : clé = dernier mot (« Donald Trump » et « Trump » se
    rejoignent). Mots courants : clé = racine."""
    termes = {}
    for e in entites_titre(titre, propres):
        if e.lower() in GENERIQUES:
            continue
        termes[("E", sans_accents(e.split()[-1].lower()))] = e
    for mot, pos, maj in tokens_titre(titre):
        m = mot.lower()
        if m in STOPWORDS or m in GENERIQUES or len(m) < 4 or m.isdigit():
            continue
        if mot in propres or mot in PAYS:
            continue  # déjà couverts par les entités
        termes.setdefault(("M", racine(m)), m)
    return termes


def detecter_sujets(items_mois, items_tous, propres):
    """Repère les sujets du mois : entités et mots fréquents ce mois-ci et
    plus fréquents que d'habitude, puis regroupe les titres qui les
    contiennent et fusionne les groupes qui se recouvrent."""
    n_mois = max(1, len({it["dt"][:7] for it in items_tous}))
    df_mois, df_tous = Counter(), Counter()
    formes = defaultdict(Counter)
    termes_par_item = []
    for it in items_mois:
        termes = termes_titre(it["title"], propres)
        for k, forme in termes.items():
            formes[k][forme] += 1
        termes_par_item.append(set(termes))
        df_mois.update(termes.keys())
    for it in items_tous:
        df_tous.update(termes_titre(it["title"], propres).keys())

    def affiche(k):
        if k[0] == "E":
            # Forme la plus complète parmi les plus fréquentes (« Donald Trump » plutôt que « Trump »).
            top = formes[k].most_common(3)
            seuil = top[0][1] * 0.3
            return max((f for f, n in top if n >= seuil), key=len)
        return formes[k].most_common(1)[0][0]

    total = len(items_mois)
    scores = {}
    for t, n in df_mois.items():
        if n < MIN_ARTICLES_FICHE:
            continue
        moyenne = df_tous[t] / n_mois
        specificite = min(3.0, n / (moyenne + 1))
        if specificite < 1.15 and n > total * 0.03:
            continue  # sujet de fond trop large (ex. un pays omniprésent) sans pic ce mois-ci
        bonus = 1.6 if t[0] == "E" else 1.0
        scores[t] = n * specificite * bonus

    graines = sorted(scores, key=scores.get, reverse=True)[:80]
    groupes = []
    for g in graines:
        membres = {i for i, ts in enumerate(termes_par_item) if g in ts}
        fusionne = False
        for grp in groupes:
            inter = len(membres & grp["membres"])
            if inter / max(1, min(len(membres), len(grp["membres"]))) >= 0.35:
                grp["membres"] |= membres
                grp["graines"].append(g)
                fusionne = True
                break
        if not fusionne:
            groupes.append({"graines": [g], "membres": membres})

    fiches = []
    for grp in groupes:
        if len(grp["membres"]) < MIN_ARTICLES_FICHE:
            continue
        membres = [items_mois[i] for i in grp["membres"]]
        co = Counter()
        for i in grp["membres"]:
            co.update(termes_par_item[i])
        mots_cles = [t for t, n in co.most_common(40) if n >= max(3, len(membres) * 0.12)]
        entites = [affiche(t) for t in mots_cles if t[0] == "E"][:10]
        mots = [affiche(t) for t in mots_cles if t[0] == "M"][:8]
        principaux = [affiche(t) for t in grp["graines"][:3]]
        fiches.append({
            "intitule_auto": " · ".join(principaux),
            "entites": entites,
            "mots_cles": mots,
            "items": membres,
            "score": sum(scores.get(t, 0) for t in grp["graines"]),
        })
    fiches.sort(key=lambda f: f["score"], reverse=True)
    return fiches[:FICHES_PAR_MOIS]


SYSTEME_FICHE = """Tu prépares des étudiants aux concours des écoles de journalisme \
françaises. On te donne les titres de presse (datés, avec rubrique et média) \
d'un même sujet d'actualité sur un mois. Rédige une fiche de révision en \
français, claire et dense, comme un bon étudiant la ferait.

Règles :
- Les faits d'actualité (qui a fait quoi, quand, chiffres) viennent \
UNIQUEMENT des titres fournis. N'invente aucun fait, chiffre ou déclaration.
- Pour le contexte et les enjeux, tu peux mobiliser la culture générale \
stable (histoire, institutions, géographie, débats de fond). Si un élément \
de contexte n'est pas certain ou peut avoir évolué, écris « (à vérifier) ».
- Si les titres mélangent plusieurs sujets, concentre-toi sur le sujet \
dominant et ignore les titres hors sujet.
- « titre » : intitulé court et parlant (ex. « Budget 2027 : le PLF au \
Parlement »), pas une liste de mots-clés.
- « a_retenir » : 3 à 6 points mémorisables pour un QCM ou une copie.
- « questions_oral » : 2 ou 3 questions qu'un jury pourrait poser à l'oral, \
qui demandent d'avoir un avis argumenté."""


def schema_fiche():
    from typing import List
    from pydantic import BaseModel

    class Acteur(BaseModel):
        nom: str
        role: str

    class FicheIA(BaseModel):
        titre: str
        resume: str
        contexte: str
        enjeux: List[str]
        acteurs: List[Acteur]
        chiffres_cles: List[str]
        a_retenir: List[str]
        questions_oral: List[str]

    return FicheIA


def synthese_ia(client, mois_txt, fiche):
    items = sorted(fiche["items"], key=lambda x: x["_dt"])
    if len(items) > MAX_TITRES_PROMPT_FICHE:
        pas = len(items) / MAX_TITRES_PROMPT_FICHE
        items = [items[int(i * pas)] for i in range(MAX_TITRES_PROMPT_FICHE)]
    lignes = [f"Sujet repéré automatiquement : {fiche['intitule_auto']} — {mois_txt}.",
              f"{len(fiche['items'])} articles au total, en voici {len(items)} :\n"]
    for it in items:
        lignes.append(f"- {it['_dt'].date().isoformat()} ({RUBRIQUE_NOMS.get(it['rubrique_num'], '')}, "
                      f"{it['source']}) {it['title']}")
    res = appel_structure(client, SYSTEME_FICHE, "\n".join(lignes), schema_fiche())
    return res.model_dump() if res else None


def empreinte(url):
    """Empreinte courte d'une URL : sert à reconnaître d'un jour à l'autre une
    fiche déjà synthétisée, même si ses mots-clés ont un peu bougé."""
    import hashlib
    return hashlib.sha1(url.encode("utf-8")).hexdigest()[:10]


def fiche_correspondante(anciennes, empreintes):
    """Ancienne fiche qui partage le plus d'articles avec la nouvelle (au
    moins la moitié de la plus petite des deux), ou None."""
    nouv = set(empreintes)
    meilleure, meilleur_score = None, 0.0
    for f in anciennes:
        anc = set(f.get("empreintes", []))
        if not anc:
            continue
        score = len(nouv & anc) / min(len(nouv), len(anc))
        if score > meilleur_score:
            meilleure, meilleur_score = f, score
    return meilleure if meilleur_score >= 0.5 else None


def chronologie(items):
    par_jour = defaultdict(list)
    for it in sorted(items, key=lambda x: x["_dt"]):
        par_jour[it["_dt"].date().isoformat()].append(it)
    out = []
    for jour, lst in sorted(par_jour.items()):
        # Les titres de la rubrique Une et ceux de l'analyse de fond d'abord.
        lst.sort(key=lambda x: (x["rubrique_num"] not in (0, 23), x["_dt"]))
        out.append({
            "date": jour,
            "nombre": len(lst),
            "articles": [{"titre": it["title"], "media": it["source"], "url": it["url"]}
                         for it in lst[:MAX_TITRES_CHRONO_PAR_JOUR]],
        })
    return out


def generer_fiches(items, propres, client, now):
    par_mois = defaultdict(list)
    for it in items:
        par_mois[it["dt"][:7]].append(it)

    mois_courant = now.strftime("%Y-%m")
    appels = 0
    # Mois en cours d'abord (c'est lui qu'on révise), puis les précédents.
    for cle_mois in sorted(par_mois, reverse=True):
        chemin = os.path.join(FICHES_DIR, f"{cle_mois}.json")
        ancien = charger_json(chemin, None)
        if ancien and cle_mois < mois_courant and ancien.get("complet"):
            # Mois terminé et déjà finalisé : on complète seulement les synthèses manquantes.
            if client is None or all(f.get("synthese") for f in ancien["fiches"]):
                continue
        a, m = map(int, cle_mois.split("-"))
        mois_txt = f"{MOIS_FR[m]} {a}"
        anciennes = (ancien or {}).get("fiches", [])

        sujets = detecter_sujets(par_mois[cle_mois], items, propres)
        fiches = []
        for s in sujets:
            empreintes = sorted({empreinte(it["url"]) for it in s["items"]})
            prec = fiche_correspondante(anciennes, empreintes)
            synthese = prec.get("synthese") if prec else None
            n_synth = prec.get("synthese_sur", 0) if prec else 0
            if client and appels < MAX_APPELS_IA_FICHES and (
                    synthese is None or len(s["items"]) >= n_synth * SEUIL_REGEN_FICHE):
                appels += 1
                print(f"Fiche {cle_mois} « {s['intitule_auto']} » : synthèse par Claude…", file=sys.stderr)
                nouvelle = synthese_ia(client, mois_txt, s)
                if nouvelle:
                    synthese, n_synth = nouvelle, len(s["items"])
            rubs = Counter(it["rubrique_num"] for it in s["items"] if it["rubrique_num"] != 0)
            medias = Counter(it["source"] for it in s["items"])
            dates = sorted(it["_dt"] for it in s["items"])
            fiches.append({
                "id": f"{cle_mois}-{len(fiches) + 1:02d}",
                "titre": synthese["titre"] if synthese else s["intitule_auto"],
                "intitule_auto": s["intitule_auto"],
                "nombre_articles": len(s["items"]),
                "debut": dates[0].date().isoformat(),
                "fin": dates[-1].date().isoformat(),
                "rubriques": [RUBRIQUE_NOMS[r] for r, _ in rubs.most_common(3)],
                "medias": [m for m, _ in medias.most_common(6)],
                "entites": s["entites"],
                "mots_cles": s["mots_cles"],
                "synthese": synthese,
                "synthese_sur": n_synth,
                "chronologie": chronologie(s["items"]),
                "empreintes": empreintes,
            })
        data = {
            "mois": cle_mois,
            "libelle": mois_txt,
            "complet": cle_mois < mois_courant,
            "genere_le": now.isoformat(timespec="seconds"),
            "articles_du_mois": len(par_mois[cle_mois]),
            "fiches": fiches,
        }
        ecrire_json(chemin, data)
        ecrire_fiches_md(os.path.join(FICHES_DIR, f"{cle_mois}.md"), data)

    index = []
    for chemin in sorted(glob.glob(os.path.join(FICHES_DIR, "????-??.json"))):
        cle = os.path.basename(chemin)[:7]
        if cle not in par_mois:
            os.remove(chemin)
            md = chemin[:-5] + ".md"
            if os.path.exists(md):
                os.remove(md)
            continue
        data = charger_json(chemin, {"fiches": []})
        index.append({"mois": cle, "libelle": data.get("libelle", cle), "fichier": os.path.basename(chemin),
                      "fiches": len(data["fiches"])})
    ecrire_json(os.path.join(FICHES_DIR, "index.json"), {"genere_le": now.isoformat(timespec="seconds"), "mois": index})
    print(f"OK : fiches ({len(index)} mois, {appels} synthèses IA)", file=sys.stderr)


def ecrire_fiches_md(chemin, data):
    """Version Markdown des fiches, lisible directement sur GitHub."""
    L = [f"# Fiches d'actualité — {data['libelle']}", ""]
    L.append(f"_Générées le {data['genere_le'][:10]} à partir de {data['articles_du_mois']} titres archivés. "
             "Les faits viennent des titres de presse : vérifier dans les articles liés avant de les citer._")
    L.append("")
    for i, f in enumerate(data["fiches"], 1):
        L.append(f"- [{f['titre']}](#fiche-{i}) — {f['nombre_articles']} articles")
    L.append("")
    for i, f in enumerate(data["fiches"], 1):
        L.append(f'<a id="fiche-{i}"></a>')
        L.append(f"## {i}. {f['titre']}")
        L.append("")
        L.append(f"**{f['nombre_articles']} articles** du {f['debut']} au {f['fin']} · "
                 f"{', '.join(f['rubriques']) or 'Une'}")
        if f["entites"]:
            L.append(f"\n**Noms qui reviennent :** {', '.join(f['entites'])}")
        s = f.get("synthese")
        if s:
            L += ["", f"**En bref.** {s['resume']}", "", f"**Contexte.** {s['contexte']}", ""]
            if s["enjeux"]:
                L.append("**Enjeux**")
                L += [f"- {x}" for x in s["enjeux"]]
                L.append("")
            if s["acteurs"]:
                L.append("**Acteurs**")
                L += [f"- **{a['nom']}** : {a['role']}" for a in s["acteurs"]]
                L.append("")
            if s["chiffres_cles"]:
                L.append("**Chiffres clés**")
                L += [f"- {x}" for x in s["chiffres_cles"]]
                L.append("")
            if s["a_retenir"]:
                L.append("**À retenir pour le concours**")
                L += [f"- {x}" for x in s["a_retenir"]]
                L.append("")
            if s["questions_oral"]:
                L.append("**Questions possibles à l'oral**")
                L += [f"- {x}" for x in s["questions_oral"]]
                L.append("")
        L += ["", "**Chronologie**", ""]
        for j in f["chronologie"]:
            d = date.fromisoformat(j["date"])
            L.append(f"- **{d.day} {MOIS_FR[d.month]}** ({j['nombre']} art.)")
            for a in j["articles"]:
                L.append(f"  - [{a['titre']}]({a['url']}) — {a['media']}")
        L.append("")
    with open(chemin, "w", encoding="utf-8") as fh:
        fh.write("\n".join(L) + "\n")


# ---------------------------------------------------------------------------

def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--rattrapage", type=int, default=0,
                   help="(re)génère les QCM des N derniers jours (avec Claude si une clé est configurée)")
    p.add_argument("--sans-ia", action="store_true", help="n'appelle jamais l'API Claude")
    args = p.parse_args()

    now = datetime.now(timezone.utc)
    items = charger_archive()
    if not items:
        print("Archive vide : rien à faire.", file=sys.stderr)
        return
    propres = construire_lexique(items)
    client = client_claude(args.sans_ia)
    print(f"Archive : {len(items)} titres uniques, {len(propres)} noms propres repérés, "
          f"mode {'IA (Claude)' if client else 'automatique sans IA'}.", file=sys.stderr)

    generer_qcm(items, propres, client, now, args.rattrapage)
    generer_fiches(items, propres, client, now)


if __name__ == "__main__":
    main()
