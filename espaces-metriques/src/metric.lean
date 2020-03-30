﻿import tactic
import data.real.basic
import data.real.cau_seq
import data.set
import order.bounds
import order.complete_lattice
import topology.algebra.ordered

noncomputable theory

-- Ce fichier prolonge un travail de Frédéric Le Roux qui a traité --
-- des propriétés topologiques des espaces métriques --

------------
-- ESSAIS --
------------
open set
open classical
local attribute [instance] prop_decidable -- on active la décidabilité partout.

-----------
-- DEBUT --
-----------


-- Une structure d'espace pré-métrique sur un type X --
class espace_pre_metrique (X : Type) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x=y → d x y = 0)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)

-- Une structure d'espace métrique sur un type X --
class espace_metrique (X : Type) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x=y → d x y = 0)
(sep : ∀ x y, d x y = 0 →  x = y)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)


open espace_metrique
-- open espace_pre_metrique --

/-- Instantiation des réels comme espace métrique. -/
instance real.metric_space : espace_metrique ℝ :=
{ d                  := λx y, abs (x - y),
  d_pos              := by simp [abs_nonneg],
  presep             := begin simp, apply sub_eq_zero_of_eq end,
  sep                := begin simp, apply eq_of_sub_eq_zero end,
  sym                := assume x y, abs_sub _ _,
  triangle           := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : d x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : d x 0 = abs x :=
by simp [real.dist_eq]


----------------------------------------------------
section suites
----------------------------------------------------
variables {X:Type} [espace_metrique X]
variables {Y:Type} [espace_metrique Y]
variables {Z:Type} [espace_metrique Z]

/-- Le but dans cette section est l'un des deux
-- buts suivants:
-- * construire l'écart naturel sur l'espace des suites de cauchy,
et si le temps le permet, construire sa completion
-- * montrer les propriétés de base des la continuité séquentielle
-- des fonctions entres espaces métriques --/

def converge (x: ℕ → X) (l : X) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ((d l (x n))  < ε)

def cauchy (x: ℕ → X) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < ε)

-- Pour tout élément de l'espace, 
-- la suite est au plus à M de l'élément de l'espace.
def bornee (x: ℕ → X) :=
  ∀ y : X, ∃ M: ℝ, M > 0 ∧ (∀ n : ℕ, d (x n) y ≤ M)

-- FIXME: à généraliser la notion de « suite image » et l'unifier avec celle de sous suite.
def suite_image (f : X → Y) (x : ℕ → X) (n: ℕ) := f (x n)
def sous_suite (x: ℕ → X) (φ : ℕ → ℕ) (n: ℕ) := x (φ n)

-- point limite: l adhère à S \ { l }
def point_limite (S: set X) (l: X) := ∃ (x : ℕ → X), (∀ n : ℕ, x n ∈ S ∧ x n ≠ l) ∧ (converge x l)

-- sous hypothèse que le sup ou l'inf ne sont pas dans l'ensemble, ils forment des points limites.
-- niveau: facile
lemma sup_est_un_point_limite [has_Sup X] (S: set X): 
  Sup S ∉ S → point_limite S (Sup S) := sorry
lemma inf_est_un_point_limite [has_Inf X] (S: set X): 
  Inf S ∉ S → point_limite S (Inf S) := sorry

-- valeur d'adhérence.
def adhere (x: ℕ → X) (l: X) := ∀ ε > 0, ∀ N : ℕ, ∃ p ≥ N, d (x p) l < ε

def complete (T: Type) [espace_metrique T] := ∀ x : ℕ → T, cauchy x → ∃ l : T, converge x l

/-- bornee => bounded (range x) -/
lemma bornee_est_bounded (x: ℕ → X): bornee x → ∃ M > 0, bounded (λ x y, d x y ≤ M) (range x) :=
begin
intro Hb,
have h: set.nonempty (range x) := range_nonempty_iff_nonempty.2 nonempty_of_inhabited,
obtain ⟨ y, hy ⟩ := h,
obtain ⟨ M, ⟨ hm, hbdd⟩ ⟩ := Hb y,
use M,
split,
exact hm,
use y,
intros x hx,
simp at hx,
obtain ⟨ n, hn ⟩ := hx,
rw ← hn,
exact hbdd n,
end

/-- bounded (range x) => bornee -/
-- niveau: moyen
lemma bounded_est_bornee (x: ℕ → X): ∃ M > 0, bounded (λ x y, d x y ≤ M) (range x) → bornee x := sorry

/-- Un exemple de preuve --
-- Toute suite convergente est de cauchy --
-- On utilise souvent la tactique linarith
-- pour simplifier des inégalités--/

lemma converge_cauchy (x: ℕ → X) (l : X) : converge x l → cauchy x :=
begin
 intros conv ε hε,
 have hε2 : ε/2 > 0 := by linarith,
 obtain ⟨ N ⟩ : ∃ N, ∀ n ≥ N, ((d l (x n)) < ε/2),
 apply conv, exact hε2,
 use N,
 assume p ≥ N,
 have H2 : d l (x p) < ε/2 := h p H,
 assume q ≥ N,
 have H3 : d l (x q) < ε/2 := h q H,
 have H4 : d (x p) l = d l (x p):= sym (x p) l,
 have H5 : d l (x p) < ε/2 := by linarith,
 have clef : d (x p) (x q) ≤ d (x p) l + d l (x q), from triangle (x p) l (x q),
 linarith,
end


-- le master lemme, gagnerait à se généraliser pour X séquentiellement compact
-- mais requiert dans ce cas de poser ce qu'est:
-- — compact
-- — quasi-compact
-- — séquentiellement compact
-- et il faut prouver que R est séquentiellement compact, ce qui reste à peu près la même galère pour R.
-- mais devient intéressant si on veut introduire la complétion d'un espace.

def strictement_croissante [linear_order X] (x: ℕ → X) := ∀ p : ℕ, ∀ q > p, x p < x q

-- il suffit que l'inf existe et soit atteint → (X, ≤) est bien fondé!
-- construire x_n = inf (S \ { x_i | i < n }) par induction forte.

def suite_st_croissante [linear_order X] [has_Inf X] {S: set X} (Hinf: set.infinite S)
  (Hset: ∀ M ⊆ S, M.nonempty → (Inf M ∈ M)): ℕ → X := 
  well_founded.fix nat.lt_wf
  (λ n suite_st_croissante, 
    Inf (S \ { x : X | ∃ k < n, x = suite_st_croissante k H}))

def suite_st_croissante_def [linear_order X] [has_Inf X] {S: set X} (Hinf: set.infinite S)
  (Hset: ∀ M ⊆ S, M.nonempty → (Inf M ∈ M)) (n: ℕ):
    suite_st_croissante Hinf Hset n = Inf (S \ { x: X | ∃ k < n, x = suite_st_croissante Hinf Hset k })
    := well_founded.fix_eq _ _ _

lemma suite_st_croissante_props [linear_order X] {S: set X} (Hlattice: complete_lattice S) (Hinf: set.infinite S):
  (∀ M ⊆ S, M.nonempty → (complete_lattice.Inf M ∈ M)) → ∃ x : ℕ → X, strictement_croissante x ∧ (range x) ⊆ S :=
  begin
  intro H,
  use suite_st_croissante Hinf H,
  split,
  intros p q hq,
  -- ici il s'agit de prouver une inégalité stricte entre deux infs.
  -- il faut comprendre: S_q est inclus strictement dans S_p
  -- donc inf S_p ≤ inf S_q
  -- de plus (inf S_p) = suite_st_croissante p
  -- donc, (inf S_p) n'est pas dans S_q
  -- or, inf S_q est dans S_q
  -- donc, inf S_p < inf S_q.
  -- niveau: moyen+
  apply lt_of_le_of_ne,
  rw suite_st_croissante_def,
  rw suite_st_croissante_def,
  apply cInf_le_cInf,
  sorry,
  sorry, -- preuve déjà faite plus bas.
  have: S \ {x : X | ∃ (k : ℕ) (H_1 : k < q), x = suite_st_croissante Hinf H k} ⊆ S \ {x : X | ∃ (k : ℕ) (H_1 : k < p), x = suite_st_croissante Hinf H k} := sorry,
  exact this,
  by_contra,
  push_neg at a,
  sorry,
  intros x hx,
  simp at hx,
  obtain ⟨ y ⟩ := hx,
  rw suite_st_croissante_def at hx_h,
  apply set.diff_subset,
  rw ← hx_h,
  apply H,
  apply set.diff_subset,
  apply set.nonempty_diff.2,
  by_contra,
  apply Hinf,
  have : ({x : X | ∃ (k : ℕ) (H_1 : k < y), x = suite_st_croissante Hinf H k}).finite := begin
    have:
    {x : X | ∃ (k : ℕ) (H_1 : k < y), x = suite_st_croissante Hinf H k}
      = (suite_st_croissante Hinf H) '' { i : ℕ | i < y} := begin
        ext,
        split,
        repeat {
          intro H1,
          simp at H1,
          simp,
          obtain ⟨ x, ⟨ hxy, heq ⟩ ⟩ := H1,
          use x,
          split,
          exact hxy,
          symmetry,
          exact heq,
        },
      end,
      rw this,
      apply set.finite_image,
      apply set.finite_lt_nat,
  end,
  apply set.finite_subset this,
  exact a,
  end

-- preuve un peu moche, à embellir?
-- proposition: prendre la contraposition plutôt que l'absurde et pour la preuve interne, faire du direct.
lemma lemme_fondateur_de_bw [linear_order X] [has_Sup X] [has_Inf X] (S: set X) 
  -- si pour toute partie M non vide de S, inf(M), sup(M) existent et sont dans M.
  (H: ∀ U ⊆ S, U.nonempty → Sup U ∈ U ∧ Inf U ∈ U): set.finite S :=
begin
by_contra,
-- en supposant S infini, on peut construire une infinité de x_n comme il suit:
suffices hsuite: ∃ x : ℕ → X, strictement_croissante x ∧ (range x) ⊆ S, from begin
  -- prendre X = { x_n | n ≥ 0 } partie de S non vide
  -- puisque (x_n)_n est une suite infine strictement croissante, alors sup(X) n'est pas dans X
  -- or, X est une partie de S, par caractère bien fondé, c'est absurde.
  -- donc S est fini.
  obtain ⟨ x, hm, R1 ⟩ := hsuite,
  have R2: (range x).nonempty := range_nonempty_iff_nonempty.2 nonempty_of_inhabited,
  have: ¬((Sup (range x)) ∈ (range x)) := begin
    by_contra,
    simp at a_1,
    -- puisque a_1 donne le fait que le sup (range x) est dans (range x)
    -- il existe donc n0 tel que x n0 = sup (range x)
    obtain ⟨ n₀, h ⟩ := a_1,
    -- or: x (n0 + 1) > x n0 = sup (range x).
    have : x (n₀ + 1) > x n₀ := begin
      apply hm,
      exact lt_add_one n₀,
    end,
    -- absurde par déf du sup (linarith ne suffira pas.)
    -- introduire l'inégalité du sup pour x (n0 + 1), réécrire le sup avec x n0.
    -- conclure avec linarith.
    sorry -- niveau: très facile
  end,
  apply this,
  exact (H (range x) R1 R2).1,
end,
exact suite_st_croissante_props a (λ M hs hn, (H M hs hn).2),
end

lemma bolzano_weierstrass_v2 (S: set ℝ): (set.infinite S) → bdd_above S ∧ bdd_below S → ∃ l : ℝ, point_limite S l :=
begin
intros hs hb,
by_contra,
push_neg at a,
apply hs,
apply lemme_fondateur_de_bw,
intros U subU hU,
split,
-- TODO: c'est la même preuve pour sup ou inf à sup/inf près. Autant utiliser l'automatisation.
by_contra,
apply a (Sup U),
have: point_limite U (Sup U) := sup_est_un_point_limite U a_1,
obtain ⟨ x, hx, hc ⟩ := this,
use x,
split,
intro n,
obtain ⟨ hsubset, hnotsup ⟩ := hx n,
split,
apply mem_of_subset_of_mem,

exact subU,
exact hsubset,
exact hnotsup,
exact hc,
by_contra,
apply a (Inf U),
have: point_limite U (Inf U) := inf_est_un_point_limite U a_1,
obtain ⟨ x, hx, hc ⟩ := this,
use x,
split,
intro n,
obtain ⟨ hsubset, hnotsup ⟩ := hx n,
split,
apply mem_of_subset_of_mem,
exact subU,
exact hsubset,
exact hnotsup,
exact hc,
end

-- le merveilleux.
-- niveau: magnifique.

lemma principe_des_tiroirs {A: Type} {B: Type} {f: A → B} (Hinfinite: infinite A) (Hfinite: (range f).finite):
  ∃ x ∈ (range f), (preimage f {x}).infinite := sorry

lemma bolzano_weierstrass {x: ℕ → ℝ}: bornee x → ∃ l : ℝ, adhere x l :=
begin
intro Hb,
have bdd_above_and_below_of_image: bdd_above (range x) ∧ bdd_below (range x) := sorry,
by_cases (set.finite (range x)),
{
  -- par principe des tiroirs, il existe x_0 dans S tel que x^-1{x_0} est infini.
  obtain ⟨ l, hl, hpreimage ⟩  := principe_des_tiroirs nat.infinite h,
  use l,
  intros ε hε N,
  -- niveau: moyen.
  -- prendre p = min (x^-1{x_0} \ [[0, N - 1]]) (non vide & partie de N & infini).
  -- un tel p vérifie x p = l, donc d (x p) l = 0 < ε.
  -- d'où le résultat désiré d'adhérence.
  sorry,
},
{
  obtain ⟨ l ⟩ := bolzano_weierstrass_v2 (range x) h bdd_above_and_below_of_image,
  use l,
  obtain ⟨ y, ⟨ hssuite, hcv ⟩ ⟩ := h_1,
  intros ε hε N,
  obtain ⟨ N₀, hcv ⟩ := hcv ε hε,
  suffices hX: ∃ n₀ ≥ N, ∃ p₀ ≥ N₀, x n₀ = y p₀, begin
    obtain ⟨ n₀, Hn0, p₀, Hpn0, Hxy ⟩ := hX,
    use n₀,
    split,
    exact Hn0,
    have := hcv p₀ Hpn0,
    rw ← Hxy at this,
    rw espace_metrique.sym at this,
    exact this,
  end,
  -- il suffit de prouver qu'on peut trouver n0 assez grand et p0 assez grand tel que x n0 = y p0
  -- c'est suffisant de prouver que par infinitude, on peut trouver p0 assez grand tel que y p0 possède un rang assez grand.
  -- niveau: moyen.
  -- preuve: prouver que la préimage de x par { y(p) | p ≥ N0} est infinie, c'est vrai car son complémentaire est finie (immédiatement).
  -- donc, on prend un n0 plus grand que N dedans, possible par définition de l'infinitude.
  sorry,
}
end

lemma finite_set_has_a_sup [conditionally_complete_lattice X] (S: set X):
  S.finite → conditionally_complete_lattice.Sup S ∈ S := sorry

-- image f S
-- preimage f S
-- niveau: facile

def fonction_distance (x : ℕ → X) (n: ℕ) (y: X) := d (x n) y

lemma cauchy_est_bornee {x: ℕ → X} : cauchy x → bornee x := 
begin
intros cauch y,
obtain ⟨ N, H ⟩ : ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < 1),
apply cauch, linarith,
have sup_est_atteint: conditionally_complete_lattice.Sup { M: ℝ | ∃ n ≤ N, M = d (x n) y } 
∈ { M: ℝ | ∃ n ≤ N, M = d (x n) y}:= begin apply finite_set_has_a_sup, set L:={ M: ℝ | ∃ n ≤ N, M = d (x n) y } , set F:={ M: ℝ | ∃ n ≤ N, M = fonction_distance(x)(n)(y)}, refine lemme_fondateur_de_bw L _,
intros h1 h2 h3, sorry, end, 
  -- f : n → d (x n) y
  -- f : ℕ → ℝ
  -- f([[0, N]]).finite <=> [[0, N]].finite
simp at sup_est_atteint,
obtain ⟨ n, hn, sup_atteint ⟩ := sup_est_atteint,
use (max (d (x n) y) (1 + d (x N) y)), -- max(d(x_n, y), 1 + d(x_N, y))
split,
refine lt_max_iff.mpr _,
right,
apply add_pos_of_pos_of_nonneg,
exact zero_lt_one,
exact d_pos _ _,
intro p,
by_cases (p ≥ N),
have h1: d (x p) (x N) + d (x N) y ≤ max (d (x n) y) (1 + d (x N) y) := begin 
    {
      transitivity,
      apply add_le_add,
      apply le_of_lt,
      apply H _ h N (le_refl _),
      exact le_refl (d (x N) y),
      exact le_max_right _ _,
    }
  end,
have h2: d (x p) y ≤ d (x p) (x N) + d (x N) y := triangle (x p) (x N) y,
exact le_trans h2 h1, 
refine le_max_iff.mpr _,
left,
simp at h,
rw ← sup_atteint,
apply le_cSup,
sorry, -- montrer que l'ensemble fini est bornée par en haut.
simp,
use p,
split,
exact le_of_lt h,
refl,
end
-- niveau: moyen
lemma cauchy_admet_une_va {x: ℕ → X} : cauchy x → ∀ l₁ : X, ∀ l₂ : X, adhere x l₁ ∧ adhere x l₂ → l₁ = l₂ := sorry
-- niveau: difficile
lemma unicite_de_la_va {x: ℕ → X} {l: X} : adhere x l → (∀ l₀ : X, adhere x l₀ →  l = l₀) → converge x l := sorry

theorem R_is_complete : complete ℝ :=
begin
 intros x c,
 have := bolzano_weierstrass (cauchy_est_bornee c),
 obtain ⟨ l ⟩ := this,
 use l,
 apply unicite_de_la_va this_h,
 intros l₀ adh,
 apply cauchy_admet_une_va c,
 split,
 exact this_h,
 exact adh,
end

lemma unicite_limite (x: ℕ → X) (l₁ : X) (l₂ : X) :
 (converge x l₁) ∧ (converge x l₂) →   l₁ = l₂ :=
begin
sorry
end

-- On définit la suite des distances entre deux suites,
-- appelée le pre_ecart --

def pre_ecart (x : ℕ → X) (y : ℕ → X) : ℕ → ℝ  :=
 λ n : ℕ, d (x n) (y n)

-- on pourra utiliser les tactiques linarith, rw, simp et split --
-- pour démontrer l'énoncé suivant, nécessaire pour démontrer --
-- que le pre_ecart est une suite de cauchy

-- d(d(x, y), d(z, t)) ≤ d(x, z) + d(y, t)
-- idée: |d(x, y) - d(z,t)| ≤ d(x, z) + d(y, t)
-- 1er cas: d(x, y) ≤ d(z, t)
-- DONC: d(z, t) ≤ d(x, y) + d(x, z) + d(y, t)
-- d(z, t) ≤ d(z, x) + d(x, y) + d(y, t) (inégalité trig)
-- 2ème cas: d(x, y) ≤ d(y, t) + d(t, z) + d(z, x)
-- or: d(x, y) ≤ d(x, z) + d(z, t) + d(t, y) (inég trig)
-- 2 coups d'inégalité triangulaires, en distiguant sur le signe de d(x,y) - d(z,t).
lemma dist_ineg_utile (x y z t:X) : d (d x y)  (d z t) ≤ d x z + d y t:=
begin
 sorry
end

/-- on démontre que le pré-écart est une suite de Cauchy --/
-- montrer que (d(x_n, y_n))_n est de Cauchy
-- i.e. pour tout eps > 0,
-- pour tout (n, m) assez grands, d(d(x_n, y_n), d(x_m, y_m)) < eps
-- or: d(d(x_n, y_n), d(x_m, y_m)) ≤ d(x_n, x_m) + d(y_n, y_m) ≤ 2eps
lemma pre_ecart_cauchy (x y : ℕ →  X) (h1 : cauchy x) (h2 : cauchy y):
  cauchy (λ n : ℕ, d (x n) (y n)):=
 begin
  sorry
 end

/-- on définit l'ensemble des suites de Cauchy --/

def cauchy_seqs (X : Type) [espace_metrique X] : Type := { f : ℕ → X // cauchy f }

/-- Si le temps le permet, et seulement dans ce cas,
-- montrer que le pre-ecart induit une structure
d'espace pre-metrique sur l'ensemble des suites de cauchy pour
pouvoir éventuellement construire la completion de l'espace X
comme le quotient de l'ensemble des suites de cauchy par la
relation d'équivalence appropriée --/

-- Définir la continuité séquentielle --/

-- f est continue en L si pour tout (x_n) ∈ ℝ^ℕ convergente de limite L, (f(x_n))_n est convergente de limite f(L).
def seq_continue_en_l (f: X → Y) (L: X) := ∀ (x: ℕ → X), converge x L → converge (suite_image f x) (f L)
def seq_continue (f: X → Y) := ∀ L : X, seq_continue_en_l f L

/-- On démontre que la continuité séquentielle est stable par composition --/

-- On démontre la composition des suites images.
theorem comp_suite_image (f: X → Y) (g: Y → Z) (x: ℕ → X): suite_image g (suite_image f x) = suite_image (g ∘ f) x :=
begin
ext,
repeat {rw suite_image},
end

-- On se ramène à la continuité séquentielle en un point.
theorem comp_seq_continue_ponctuel (f : X → Y) (g : Y → Z) (l: X):
  seq_continue_en_l f l ∧ seq_continue_en_l g (f l)
  → seq_continue_en_l (g ∘ f) l := begin
  intros H x x_cv,
  cases H with Hf Hg,
  have := Hg (suite_image f x) (Hf x x_cv),
  conv at this {
    congr,
    rw comp_suite_image f g x,
    skip,
    skip,
  },
  exact this,
end

theorem comp_seq_continue (f:X → Y) (g:Y → Z):
 seq_continue f ∧ seq_continue g → seq_continue (g ∘ f):=
 begin
 intro H,
 intro l,
 apply comp_seq_continue_ponctuel,
 cases H with Hf Hg,
 split,
 exact Hf l,
 exact Hg (f l),
 end

end suites