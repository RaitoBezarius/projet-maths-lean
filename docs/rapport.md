---
title: Rapport
author: \textsc{Maryem Hajji, Léa Riant, Ryan Lahfa, Ivan Hasenohr} 
advanced-maths: true
advanced-cs: true
toc: true
minted: true
lean-minted: true
twocolumn-minted: true
lang: fr
classoption: 
- twocolumn
papersize: a4
numbersections: true
---

\newcommand{\mynat}{\N_{\text{mynat}}}
\newcommand{\Type}{\mathrm{Type}}

# Introduction

Ce travail ainsi que les codes sources sont disponibles à l'URL suivante: <https://github.com/RaitoBezarius/projet-maths-lean>.

Avant d'expliquer en quoi consiste un assistant de preuve, donnons quelques éléments d'histoire autour de ces derniers.

## Courte histoire des assistants de preuve et du rêve d'Hilbert

En août 1900, David Hilbert présente ses 23 problèmes, dont le second est la cohérence de l'arithmétique, fracassé par le résultat d'incomplétude de Gödel (qui ne résoud pas tout à fait la question et dont on pourra retrouver une démonstration en profondeur dans \cite{girard2006le}) en 1931, et dont une réponse positive est obtenue par Gantzen à l'aide de la récurrence transfinie. C'est l'élan qui va lancer la théorie de la démonstration.

En 1966, de Bruijn lance le projet Automath \cite{Automath} qui a pour visée de pouvoir exprimer des théories mathématiques complètes, c'est-à-dire des théories qui sont des ensembles maximaux cohérents de propositions, i.e. le théorème d'incomplétude de Gödel ne s'y applique pas notamment.

Peu après, les projets Mizar \cite{Mizar}, HOL-Isabelle \cite{IsabelleHOL} et Coq \cite{Coq} naissent pour devenir les assistants de preuve mathématiques que l'on connaît.

## Principe d'un assistant de preuves

Ces projets mettent à disposition un ensemble d'outil afin d'aider le mathématicien à formaliser sa preuve dans une théorie mathématiques de son choix: ZFC\footnote{Théorie de Zermelo-Fraenkel avec l'axiome du choix.}, la théorie des types dépendants \cite{bertot2013interactive}, la théorie des types homotopiques \cite{hottbook} par exemple.

Certains assistants de preuve ne se contentent pas de vérifier la formalisation d'une preuve mais peuvent aussi effectuer de la décision (dans l'arithmétique de Presburger par exemple. ^[L'arithmétique de Presburger est connu pour être intégralement décidable.]) \cite{akbarpour2010metitarski}

À noter, que Lean implémente **partiellement** la procédure de décision `omega` tiré de l'arithmétique de Presburger. \cite{baek2019reflected}, \cite{pugh1991omega}

## Enjeu d'un assistant de preuves et exemples d'usages

L'enjeu des assistants de preuve et des concepts utilisés derrière dépasse le simple outil de mathématicien.

D'une part, ils permettent d'attaquer des problèmes qui ont résisté pendant longtemps, le théorème des quatre couleurs par exemple.

D'autre part, leurs usages se généralisent afin de pouvoir faire de la certification informatique, démontrer qu'un programme vérifie un certain nombre d'invariants, par exemple, dans l'aviation, des outils similaires sont employés pour certifier le comportement de certaines pièces embarquées.

## Éléments de théorie des assistants de preuves

Nous ne nous attacherons pas à faire un état du fonctionnement des assistants de preuves, ceux là dépassent largement le cadre d'une licence, mais on peut donner quelques éléments d'explications.

Distinguons deux opérations, celle de la vérification de preuve et celle de la déduction automatique.

Notons que dans un premier temps, la plupart des opérations idéales d'un assistant de preuve sont indécidables, c'est-à-dire, qu'il n'existe pas d'algorithme permettant de calculer le résultat en temps fini.

Dans ce cas, afin de pouvoir vérifier une preuve, il faut l'écrire dans un langage où toutes les étapes sont des fonctions récursives primitives (ou des programmes), ce qui les rend décidables par un algorithme. L'enjeu ensuite est de le faire efficacement, bien sûr.

Ainsi, rentre en jeu les notions de mots, de langages, de confluences et de systèmes de réécritures et d'avoir des algorithmes de bonne complexité temporelle et mémoire afin de pouvoir manipuler les représentations internes d'une preuve et décider s'ils sont des preuves du résultat désiré.

Au dessus de cela, on a besoin de se donner des théories axiomatiques dans lequel on travaille, par exemple ZFC, Peano, la théorie des catégories, la théorie des types dépendants, la théorie des types homotopiques. Dans notre cas, Lean utilise la théorie des types dépendants par défaut.

On mentionne aussi un intérêt pour la version homotopique aussi, qui est plus délicate à manipuler, mais un groupe de travail interne à Lean est intéressé en raison de la puissance du principe d'univalence qu'on peut vulgariser en $(x \equiv y) \equiv (x = y)$, autrement dit, « l'équivalence est l'égalité », cela permet de simplifier énormément beaucoup de preuves qui travaillent « à isomorphisme (unique) près » où il convient de manipuler certains objets formellement et de les remplacer par un de leurs isomorphismes, citons par exemple: $R[1/fg] \equiv R[1/f][1/g]$, en théorie des anneaux. Lean avait autrefois dans sa version 2, le support pour la théorie des types homotopiques, mais depuis Lean 3, celui-ci a été retiré. Ajoutons que Coq possède aussi une librairie de théorie des types homotopiques \cite{bauer2017hott}.

De cela, on peut construire des notions d'ensembles, d'entiers naturels, de catégories aussi.

Ceci est pour la partie vérification et fondations théoriques du modèle.

Pour la partie automatique, selon la logique, le problème passe d'indécidable à décidable, par exemple, pour le calcul des propositions, le problème est décidable mais de classe de complexité co-NP-complete (le complémentaire de la classe NP-complete), indiquant que les algorithmes de décisions prennent un temps exponentiel certainement.

En somme, c'est un problème très difficile, mais sur lequel il a été possible d'avoir des résultats positifs, notamment un qui a résolu un problème de longue date sur lequel aucune bille n'était disponible: la conjecture de Robbins, 1933, résolue en 1996 avec un assistant de preuve à déduction automatique EQP. \cite{wampler2010complete}

Dans une certaine mesure, Lean \cite{avigad2014lean} est capable d'assister à trouver des morceaux de preuve par lui-même à l'aide de tactiques qui peuvent être aussi écrite par les utilisateurs afin d'améliorer l'intelligence de Lean dans certains contextes (chasse aux diagrammes en catégories par exemple).

## Objectifs de ce projet

Nous allons d'abord nous familiariser au langage de Lean \cite{avigad2014lean}, l'assistant de preuve de Microsoft Research qui sera utilisé pour ce projet, ses concepts à travers le « Number Games » de Kevin Buzzard \cite{natgames2019} qui consiste à redémontrer quelques théorèmes autour des entiers naturels en partant des axiomes de Peano.

Nous fournissons en \ref{number_games_solution}, des solutions détaillées et expliquées des théorèmes qu'on a jugé un peu subtil tout en introduisant le système de tactique, pièce fondamentale des assistants de preuve et de l'automatisation des démonstrations.

Ensuite, nous nous dirigerons vers les espaces métriques et construirons leur formalisme dans un cadre usuel, alors que la bibliothèque mathlib \cite{mathlib} construit les espaces topologiques, uniformes, métriques avec des notions de suites généralisées et de filtres.

Enfin, un projet plus ambitieux mais si le temps le permet est de donner une démonstration formalisée du théorème d'Ostrowski\footnote{Dont le livre d'Artin fournit une démonstration} en posant la théorie des valuations d'Artin \cite{artin2005algebraic}.

# Détail des exercices du « Number Games » de Kevin Buzzard {#number_games_solution}

On se donnera pendant cette section un alphabet $\Sigma$ qui pourra contenir selon le contexte, les opérateurs usuels en mathématiques $\{ +, -, \times, / \}$, les chiffres, l'alphabet grec et latin.

Puis, on munit $(\Sigma^{*}, \cdot)$ d'une structure de monoïde usuelle où $\cdot$ est la concaténation des mots et $\Sigma^{*}$ est la fermeture par l'étoile de Kleene de $\Sigma$. \footnote{i.e. tous les mots sur $\Sigma$}

<!-- Tactiques de bases -->
\input{chapitres/basic_tactics.tex}
<!-- Chapitre de Maryem (Premiers Mondes) -->
\input{chapitres/fundamentalsworld.tex}
<!-- Chapitre de Ivan (Mondes Intermédiaires) -->
\input{chapitres/fpropworld.tex}
<!-- Chapitre de Léa (Mondes Finaux) -->
\input{chapitres/finalworlds.tex}

# Excursion dans le formalisme des espaces métriques

\input{chapitres/metric_tactics.tex}
\input{chapitres/Cauchy_est_bornee.tex}
\input{chapitres/Cauchy_admet_une_va.tex}

## $\R$ est un espace complet

Nous allons détailler sans rentrer dans les preuves, comment démontrer que $\R$ est un espace complet, qui repose axiomatiquement seulement sur l'axiome de la borne supérieure et le fait que $\R$ soit archimédien :

- Un lemme type Bolzano-Weierstrass qu'on retrouvera dans `custom/bolzano_weierstrass.lean` 
- Un lemme qui nous donne la convergence d'une suite de Cauchy sous réserve d'existence d'une valeur d'adhérence: `converge_of_va_for_cauchy` dans `custom/cauchy.lean`

Le second lemme repose sur des plus petits lemmes: une suite de Cauchy admet au plus une valeur d'adhérence, décrit sous le nom de `cauchy_admet_une_va`.

Le premier lemme requiert aussi un lemme de bornitude des suites de Cauchy, sous le nom de `cauchy_est_bornee`, décrit précédemment.

### Structure du code

#### `custom/sequences.lean`

On a des lemmes autour des suites, on a les définitions élémentaires de convergence, être de Cauchy, adhérence, bornitude, sous-suites et stricte croissance.

On y démontre une forme d'équivalence entre l'adhérence et sa version séquentielle, des lemmes autour de l'affaiblissement dénombrable du quantificateur réel devant les $\forall \varepsilon > 0$.

#### `custom/si_sequences.lean`

On définit des lemmes autour de la construction des suites strictement croissantes dans un ensemble infini complètement linéairement ordonné^[Cette hypothèse est probablement trop forte, on peut sûrement exploiter des notions fines comme la topologie de l'ordre, mais nous n'avons pas eu le temps d'explorer cela.] (qu'on appliquera donc principalement à $\R$).

Petit point sur ce qui se passe, car il s'agit de preuves non classiques, on exploite une autre forme d'infinitude, celle qui indique qu'un ensemble fini c'est exactement un ensemble pour lesquelles toutes ses parties non vides ont un plus grand et plus petit élément.

Cela nous fournit une preuve efficace pour tirer une suite strictement croissante, qu'on utilisera dans un raisonnement par l'absurde pour Bolzano-Weierstrass.

Un élément intéressant de ce fichier c'est la première utilisation de `well_founded.fix` avec l'ordre bien fondé de $\N$: `nat.lt_wf`, Lean permet de construire des objets donc par « récurrence » ^[On est plutôt dans l'induction bien-fondée, en réalité.].

Cela fonctionne comme ceci: `well_founded.fix` effectue un calcul de point fixe, cela prend en premier argument un ordre bien fondé, et en second un argument une fonction qui prend un élément, disons $n$, de l'ensemble bien fondé et la fonction partiellement construite pour tout $\l n$ au sens de l'ordre bien fondé, on doit retourner le nouveau terme induit.

Cependant, cela ne fait que construire la suite ou l'objet désiré, cela ne donne pas les propriétés sur lui qu'on veut.

Pour cela, c'est quelque chose qu'on retrouve classiquement dans Lean, on utilise un théorème type « spec » ^[`classical_spec`, etc.], en l'occurrence: `well_founded.fix_eq` qui prouve que le calcul de point fixe vérifie l'équation du point fixe.

De là, on construit notre suite par opérations ensemblistes, on pourrait explorer s'il était faisable de faire ça avec des types et des sous-types plutôt que des vrais ensembles.

#### `custom/sups.lean`

On y démontre des lemmes autour des bornes supérieures et inférieures, et des lemmes de type topologiques.

Notamment, le fait que les sups et infs sont des points limites dès lorsqu'ils ne sont pas des max/min.

On exploite `linarith` principalement et des morceaux de la `mathlib` sur les ordres qui ne reposent pas sur $\R$.

#### `custom/topology.lean`

Des définitions topologiques:

- Complétude
- Adhérence à un ensemble
- Point limite

#### `custom/negative_sets.lean`

On y démontre de lemmes autour des ensembles opposés, i.e. pour $S$ un ensemble, on regarde $-S := \{ x \mid -x \in S \}$.

On y démontre principalement des lemmes autour des sups/infs et de leurs adhérences.


#### `custom/cauchy.lean`

On y démontre des lemmes autour des suites de Cauchy, on détaillera plus ce fichier dans la partie sur les complétés.

#### `custom/bolzano_weierstrass.lean`

La preuve de Bolzano-Weierstrass en deux versions:

- Version 1: Toute suite bornée a une valeur d'adhérence.
- Version 2: Un ensemble infini borné a des points limites.

La version 2 entraîne la version 1, nous allons montrer en quoi.

### Bolzano-Weierstrass

Démontrer Bolzano-Weierstrass proprement et efficacement en partant de l'axiome de la borne supérieure est difficile en raison de la quantité de lemmes requis, nous retrouverons donc la plupart des constructions nécessaires dans les fichiers précédents.

Donnons la feuille de route pour le théorème final (Bolzano-Weierstrass version 2):

- On a besoin du lemme fondateur: `lemme_fondateur_de_bw`: qui prouve la version d'infinitude dont on a parlé dans le fichier des suites strictement croissantes, par contraposée.
- Ensuite, on prouve `bolzano_weierstrass_v2` en utilisant la nouvelle définition de l'infinitude, par l'absurde, en supposant que l'ensemble n'a pas de point limite, puis en montrant que l'ensemble est fini, puisqu'il n'a pas de point limite, son sup/inf qui en seraient sont nécessairement des max/min, d'où, ceci étant vrai pour toutes les parties, on en tire la finitude, donc l'absurdité.
- Ensuite, on prouve la version 1: `bolzano_weierstrass`, en commençant par une distinction sur la cardinalité des valeurs prises par la suite, si c'est fini, on se contente d'utiliser le principe des tiroirs, sinon, on recourt à la version 2, on s'en tire en démontrant qu'on a une adhérence séquentielle en utilisant la tactique `choose`.

## Interlude: Continuité séquentielle

## Complété d'un espace métrique

Soit $(X, d)$ un espace métrique.

À présent, nous allons essayer de construire un complété de l'espace métrique $X$ en tant que quotient par la relation d'équivalence $x \sim y \iff \lim d(x_n, y_n) = 0$ où $x, y$ sont des suites de Cauchy sur l'espace métrique $X$.

Tout d'abord, on se donne quelques lemmes:

- l'unicité de la limite ;
- une inégalité triangulaire pour le pré-écart ;
- la preuve qu'un pré-écart est une suite de Cauchy ;

À ce stade-là, puisque le pré-écart est de Cauchy, par complétude $\R$, il a toujours une limite.

Donc, on définit `cauchy.limit` la fonction qui associe l'unique limite d'une suite de Cauchy à valeurs réelles. ^[On pourrait généraliser à des espaces complets arbitraires. Cela coûte trois fois rien.]

On remarquera qu'on utilise `classical.some` qui est l'incarnation de l'axiome du choix, afin de choisir une limite.

Puis, après, on peut la rendre unique par les lemmes précédents.

On définit des lemmes utiles:

- Une suite constante est de Cauchy ;
- Limite d'une suite constante ;
- Passage à la limite dans les inégalités ;

Enfin, on définit la distance « de Cauchy » qui est $d_C(x, y) = \lim_n d(x_n, y_n)$, bien définie.

On montre que cette distance induit un espace pré-métrique sur les suites de Cauchy à valeurs dans $X$.

Dernière étape pour la complétion: montrer que $x \sim y \iff d_C(x, y) = 0$ est bien une relation d'équivalence.

Pour cela, on définit `cauchy.cong` comme étant le prédicat désiré, puis on démontre les trois lemmes classiques: réflexivité, symétrie, transitivité, ce qui nous donne le lemme d'équivalence: `equivalence (cauchy.cong X)`.

Enfin, on instancie `setoid (cauchy_seqs X)`, avec tout ce qui précède.

Pour terminer, on définit la complétion comme `quotient (pre_ecart.setoid)`, i.e. la complétion est exactement le quotient par la relation d'équivalence sur la « distance de Cauchy » ou la limite du pré-écart.

Il reste à prouver que la complétion induit bien un espace métrique, pour cela, il faut procéder en plusieurs étapes:

- Il faut transporter la distance de Cauchy, valable sur les suites de Cauchy aux classes d'équivalences (suites de Cauchy quotientés par la distance)
- Il faut transporter la structure pré-métrique acquise: cela se fait en utilisant `quotient.lift_2`, en montrant qu'elles sont compatibles pour la relation d'équivalence (appelé `soundness` en général).
- Il faut démontrer la séparabilité, en invoquant le fait que si une distance s'annule, c'est exactement le fait que $x \sim y$, i.e. $\overline{x} = \overline{y}$.

Pour aller plus loin, il faudrait continuer à transporter toutes les lois compatibles dans le complété, rajouter un lemme de cœrcion afin de pouvoir injecter tout élément de $X$ dans $\overline{X}$, le complété.

Une fois ceci fait, on aura un structure d'espace métrique complété élémentaire mais utilisable.

\bibliographystyle{plain}
\bibliography{references}
