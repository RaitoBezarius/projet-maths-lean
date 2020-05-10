﻿import tactic
import data.real.basic
import data.real.cau_seq
import data.set
import data.set.finite
import data.finset
import order.bounds
import order.complete_lattice
import topology.algebra.ordered

import .custom.defs
import .custom.sequences
import .custom.sups
import .custom.topology
import .custom.bolzano_weierstrass


noncomputable theory


open set
open_locale classical
section suites

open espace_metrique
variables {X: Type} [espace_metrique X]
variables {Y: Type} [espace_metrique Y]
variables {Z: Type} [espace_metrique Z]

def fonction_distance (x : ℕ → X) (y: X) (n: ℕ) := d (x n) y

lemma cauchy_est_bornee {x: ℕ → X} : cauchy x → bornee x := 
begin
intros cauch y,
obtain ⟨ N, H ⟩ : ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < 1),
apply cauch, linarith,
set Limage := { M: ℝ | ∃ n ≤ N, M = d (x n) y },
have limage_finiteness: Limage.finite := begin
  have: ((fonction_distance x y) '' ({ i: ℕ | i ≤ N })) = Limage := begin
    {
      ext,
      split,
      intro h1,
      simp,
      simp at h1,
      cases h1 with n h1,
      rw fonction_distance at h1,
      use n,
      cc,  
      intro h2,
      simp,
      simp at h2,
      cases h2 with n h2,
      rw ← fonction_distance at h2,
      use n,
      cc, 
    }
  end,
  rw ← this,
  apply set.finite_image,
  exact set.finite_le_nat N,
  end,
have limage_nonempty: Limage.nonempty := begin
  use (d (x 0) y),
  simp,
  use 0,
  split,
  exact zero_le N,
  refl,
end,
have sup_est_atteint: Sup Limage ∈ Limage
  := set.finite.has_a_reached_sup limage_finiteness limage_nonempty,
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
apply set.bdd_above_finite,
exact limage_finiteness,
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

lemma epsilon_continuite {x: X} {y: X}: (∀ ε > 0, d x y < ε) → x = y := sorry
lemma unicite_limite (x: ℕ → X) (l₁ : X) (l₂ : X) :
 (converge x l₁) → (converge x l₂) → l₁ = l₂ :=
begin
intros hconv1 hconv2,
apply epsilon_continuite,
intros ε hε,
obtain ⟨ N₀, hcc1 ⟩ := hconv1 (ε/2) (by linarith),
obtain ⟨ N₁, hcc2 ⟩ := hconv2 (ε/2) (by linarith),
set N₂ := max N₀ N₁,
calc
  d l₁ l₂ ≤ d l₁ (x N₂) + d (x N₂) l₂ : espace_metrique.triangle _ _ _
  ... = d l₁ (x N₂) + d l₂ (x N₂) : by rw espace_metrique.sym (x N₂) l₂
  ... < d l₁ (x N₂) + ε/2 : add_lt_add_left (hcc2 N₂ (le_max_right _ _)) _
  ... < ε/2 + ε/2 : add_lt_add_right (hcc1 N₂ (le_max_left _ _)) _
  ... ≤ ε : by simp
end

-- On définit la suite des distances entre deux suites,
-- appelée le pre_ecart --

def pre_ecart (x : ℕ → X) (y : ℕ → X) : ℕ → ℝ  :=
 λ n : ℕ, d (x n) (y n)
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
rw real.dist_eq,
apply abs_le_of_le_of_neg_le,
rw sub_le_iff_le_add,
calc
  d x y ≤ d x z + d z y : espace_metrique.triangle _ _ _
  ... ≤ d x z + (d z t + d t y) : add_le_add_left (espace_metrique.triangle z t y) _
  ... = d x z + d z t + d y t : by rw [espace_metrique.sym t y, ← add_assoc] 
  ... = d x z + d y t + d z t : by ring, -- there must be something better.
simp,
rw sub_le_iff_le_add,
calc
  d z t ≤ d z x + d x t : espace_metrique.triangle _ _ _
  ... ≤ d z x + (d x y + d y t) : add_le_add_left (espace_metrique.triangle x y t) _
  ... = d x z + d x y + d y t : by rw [espace_metrique.sym z x, ← add_assoc]
  ... = d x z + d y t + d x y : by ring
end

/-- on démontre que le pré-écart est une suite de Cauchy --/
-- montrer que (d(x_n, y_n))_n est de Cauchy
-- i.e. pour tout eps > 0,
-- pour tout (n, m) assez grands, d(d(x_n, y_n), d(x_m, y_m)) < eps
-- or: d(d(x_n, y_n), d(x_m, y_m)) ≤ d(x_n, x_m) + d(y_n, y_m) ≤ 2eps

lemma pre_ecart_cauchy (x y : ℕ →  X) (h1 : cauchy x) (h2 : cauchy y):
  cauchy (pre_ecart x y):=
 begin
  set Cxy := pre_ecart x y with hceq,
  intros ε hε,
  obtain ⟨ N, hc1 ⟩ := h1 (ε/2) (by linarith),
  obtain ⟨ M, hc2 ⟩ := h2 (ε/2) (by linarith),
  use (max N M),
  intros p hp q hq,
  rw [hceq, pre_ecart],
  simp,
  calc
    d (d (x p) (y p)) (d (x q) (y q)) ≤ d (x p) (x q) + d (y p) (y q) : dist_ineg_utile _ _ _ _
    ... < ε/2 + d (y p) (y q) : add_lt_add_right (hc1 p (le_of_max_le_left hp) q (le_of_max_le_left hq)) _
    ... < ε/2 + ε/2 : add_lt_add_left (hc2 p (le_of_max_le_right hp) q (le_of_max_le_right hq)) _
    ... = ε : by simp,
 end

/-- on définit le *type* des suites de Cauchy --/

def cauchy_seqs (T: Type) [espace_metrique T] := { f : ℕ → T // cauchy f }

/-- Si le temps le permet, et seulement dans ce cas,
-- montrer que le pre-ecart induit une structure
d'espace pre-metrique sur l'ensemble des suites de cauchy pour
pouvoir éventuellement construire la completion de l'espace X
comme le quotient de l'ensemble des suites de cauchy par la
relation d'équivalence appropriée --/

-- Retourne la limite de d(x_n, y_n) (bien définie par complétude de R), requiert l'axiome du choix.
def cauchy.limit (x: ℕ → ℝ) (H: cauchy x): ℝ := classical.some (R_is_complete x H)
def cauchy.converge_of_limit (x: ℕ → ℝ) (H: cauchy x): converge x (cauchy.limit x H) := 
  classical.some_spec (R_is_complete x H)

def cauchy.limit_le_of_seq_le (x: ℕ → ℝ) (H: cauchy x) (a: ℝ): (∀ n ≥ 0, x n ≥ a) → (cauchy.limit x H) ≥ a :=
begin
intro Hineq,
set l := cauchy.limit x H,
by_contra,
push_neg at a_1,
-- idée: a = l - eps, par définition avec eps > 0.
-- on prend converge x l avec eps/2
-- donc abs (x_n - l) < eps/2 et x_n - a = x_n - l ≥ eps
-- absurde, by linarith.
sorry,
end

def cauchy.cauchy_of_constant_real_seq (c: ℝ): cauchy (λ n, c) := begin
intros ε hε,
simp,
use 0,
intros p hq q hp,
rw espace_metrique.presep,
exact hε,
refl,
end

def cauchy.converge_of_constant (c: ℝ): converge (λ x, c) c := begin
intros ε hε,
use 0,
intros n hn,
simp,
rw espace_metrique.presep,
exact hε,
refl,
end

def cauchy.constant_limit (c: ℝ): cauchy.limit (λ x, c) (cauchy.cauchy_of_constant_real_seq c) = c := begin
apply unicite_limite (λ x, c),
exact cauchy.converge_of_limit _ _,
exact cauchy.converge_of_constant _,
end
-- Définit la distance entre 2 suites de Cauchy par lim d(x_n, y_n).
def cauchy.dist (T: Type) [espace_metrique T] (x y: cauchy_seqs T): ℝ
  := cauchy.limit (pre_ecart x.val y.val) (pre_ecart_cauchy x.val y.val x.property y.property)

def cauchy.d_pos (T: Type) [espace_metrique T] (x y: cauchy_seqs T): cauchy.dist T x y ≥ 0 := begin
rw cauchy.dist,
apply cauchy.limit_le_of_seq_le,
intros n hn,
rw pre_ecart,
simp,
exact espace_metrique.d_pos _ _,
end

def cauchy.pre_ecart_sym (x y: ℕ → X): pre_ecart x y = pre_ecart y x := begin
rw pre_ecart,
rw pre_ecart,
ext,
exact espace_metrique.sym _ _,
end

def cauchy.pre_ecart_self_eq_zero_seq (T: Type) [espace_metrique T] (x: cauchy_seqs T):
  pre_ecart x.val x.val = ((λ n, 0): ℕ → ℝ) := begin
  rw pre_ecart,
  ext,
  apply espace_metrique.presep,
  refl,
end

instance pre_ecart.premetrique : espace_pre_metrique (cauchy_seqs X) :=
{ d := cauchy.dist X,
  d_pos := cauchy.d_pos X,
  presep := begin
  intros x y h,
  rw cauchy.dist,
  rw h,
  conv {
    congr,
    congr,
    rw cauchy.pre_ecart_self_eq_zero_seq X y,
    skip,
    skip,
  },
  apply cauchy.constant_limit 0,
  end,
  sym := begin
  intros x y,
  rw cauchy.dist,
  rw cauchy.dist,
  conv {
    congr,
    congr,
    rw cauchy.pre_ecart_sym,
    skip,
    skip,
  },
  end,
  triangle := sorry
}

def cauchy.cong (T: Type*) [espace_metrique T] (x y: cauchy_seqs T): Prop := cauchy.dist T x y = 0
lemma cauchy.cong_refl (T: Type*) [espace_metrique T]: reflexive (cauchy.cong T) := sorry -- presep
lemma cauchy.cong_symm (T: Type*) [espace_metrique T]: symmetric (cauchy.cong T) := sorry -- sym
lemma cauchy.cong_trans (T: Type*) [espace_metrique T]: transitive (cauchy.cong T) := sorry -- triangle
theorem cauchy.cong_equiv (T: Type*) [espace_metrique T]: equivalence (cauchy.cong T) :=
⟨cauchy.cong_refl T, cauchy.cong_symm T, cauchy.cong_trans T⟩

instance pre_ecart.setoid (T: Type*) [espace_metrique T] : setoid (cauchy_seqs T) :=
{
  r := cauchy.cong T,
  iseqv := cauchy.cong_equiv T
}

local attribute [instance] pre_ecart.setoid

-- en termes d'univers, quotient retourne un type d'univers u + 1 en partant de X : Type u.
/- FIXME: des erreurs de typeclasses, dûs p-ê au fait que le passage au quotient requiert une augmentation
du niveau d'univers.

def completion_of_metric_space (T: Type*) [espace_metrique T] := quotient (pre_ecart.setoid T)
-- set_option trace.class_instances true 
-- il est donc nécessaire d'employer des types avec des univers qui s'ajuste tout seul.
instance completion.metric_space (T: Type*) [espace_metrique T]: espace_metrique (completion_of_metric_space T)
{ d := sorry,
}

def completion_is_complete: complete (completion_of_metric_space X) := sorry
-/

end suites