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

Certains assistants de preuve ne se contentent pas de vérifier la formalisation d'une preuve mais peuvent aussi effectuer de la décision (dans l'arithmétique de Presburger par exemple).

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

Au dessus de cela, on a besoin de se donner des théories axiomatiques dans lequel on travaille, par exemple ZFC, Peano, la théorie des catégories, la théorie des types dépendants, la théorie des types homotopiques. Dans notre cas, Lean utilise la théorie des types dépendants par défaut mais propose la version homotopique aussi, qui est plus délicate à manipuler. De cela, on peut construire des notions d'ensembles, d'entiers naturels, de catégories aussi.

Ceci est pour la partie vérification et fondations théoriques du modèle.

Pour la partie automatique, selon la logique, le problème passe d'indécidable à décidable, par exemple, pour le calcul des propositions, le problème est décidable mais de classe de complexité co-NP-complete (le complémentaire de la classe NP-complete), indiquant que les algorithmes de décisions prennent un temps exponentiel certainement.

En somme, c'est un problème très difficile, mais sur lequel il a été possible d'avoir des résultats positifs, notamment un qui a résolu un problème de longue date sur lequel aucune bille n'était disponible: la conjecture de Robbins, 1933, résolue en 1996 avec un assistant de preuve à déduction automatique EQP. \cite{wampler2010complete}

Dans une certaine mesure, Lean \cite{avigad2014lean} est capable d'assister à trouver des morceaux de preuve par lui-même à l'aide de tactiques qui peuvent être aussi écrite par les utilisateurs afin d'améliorer l'intelligence de Lean dans certains contextes (chasse aux diagrammes en catégories par exemple).

## Objectifs de ce projet

Nous allons d'abord nous familiariser au langage de Lean \cite{avigad2014lean}, l'assistant de preuve de Microsoft Research qui sera utilisé pour ce projet, ses concepts à travers le « Number Games » de Kevin Buzzard \cite{natgames2019} qui consiste à redémontrer quelques théorèmes autour des entiers naturels en partant des axiomes de Peano.

Nous fournissons en \ref{number_games_solution}, des solutions détaillées et expliquées des théorèmes qu'on a jugé un peu subtil tout en introduisant le système de tactique, pièce fondamentale des assistants de preuve et de l'automatisation des démonstrations.

Ensuite, nous nous dirigerons vers les espaces métriques et construirons leur formalisme dans un cadre usuel, alors que la bibliothèque mathlib \cite{mathlib} construit les espaces topologiques, uniformes, métriques avec des notions de suites généralisées et de filtres.

Enfin, ambitieux mais si le temps le permet, nous attaquerons une démonstration formalisée du théorème d'Ostrowski\footnote{Dont le livre d'Artin fournit une démonstration} en posant la théorie des valuations d'Artin \cite{artin2005algebraic}.

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

\bibliographystyle{plain}
\bibliography{references}
