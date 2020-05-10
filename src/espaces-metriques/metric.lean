import tactic
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
import .custom.cauchy


noncomputable theory


open set
open_locale classical
section suites

open espace_metrique
variables {X: Type} [espace_metrique X]
variables {Y: Type} [espace_metrique Y]
variables {Z: Type} [espace_metrique Z]

theorem R_is_complete : complete ℝ :=
begin
 intros x c,
 have := bolzano_weierstrass (cauchy_est_bornee c),
 obtain ⟨ l ⟩ := this,
 use l,
 exact converge_of_va_for_cauchy this_h c,
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

 lemma pre_ecart.triangle (x y z: ℕ → X):
  ∀ n, pre_ecart x z n ≤ pre_ecart x y n + pre_ecart y z n := begin
  intro n,
  rw pre_ecart,
  rw pre_ecart,
  rw pre_ecart,
  simp,
  exact espace_metrique.triangle _ _ _,
end

/-- on définit le *type* des suites de Cauchy --/

def cauchy_seqs (X: Type*) [espace_metrique X] := { f : ℕ → X // cauchy f }

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

def cauchy.limit_ge_of_seq_ge (x: ℕ → ℝ) (H: cauchy x) (a: ℝ): (∀ n, x n ≥ a) → (cauchy.limit x H) ≥ a :=
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

def cauchy.limit_le_of_seq_le (x: ℕ → ℝ) (H: cauchy x) (a: ℝ): (∀ n, x n ≤ a) → (cauchy.limit x H) ≤ a :=
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

def cauchy.le_of_limit_le {x y: ℕ → ℝ} (Hy: cauchy y):
  (∀ n, x n ≤ y n) → ∀ n, x n ≤ (cauchy.limit y Hy) := begin
  intros Hc n,
  set l := cauchy.limit y Hy,
  by_contra,
  push_neg at a,
  -- idée: l = x_n + eps
  sorry
end

def cauchy.limit_le_of_add_seq_le {x y z: ℕ → ℝ} (Hx: cauchy x) (Hy: cauchy y) (Hz: cauchy z):
  (∀ n: ℕ, x n ≤ y n + z n) → (cauchy.limit x Hx) ≤ (cauchy.limit y Hy) + (cauchy.limit z Hz) := begin
  intro Hc,
  apply cauchy.limit_le_of_seq_le,
  intro n,
  -- appliquer les lemmes précédent à la suite somme: y + z, qui est aussi de Cauchy.
  sorry
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
def cauchy.dist (T: Type*) [espace_metrique T] (x y: cauchy_seqs T): ℝ
  := cauchy.limit (pre_ecart x.val y.val) (pre_ecart_cauchy x.val y.val x.property y.property)

def cauchy.d_pos (T: Type*) [espace_metrique T] (x y: cauchy_seqs T): cauchy.dist T x y ≥ 0 := begin
rw cauchy.dist,
apply cauchy.limit_ge_of_seq_ge,
intro n,
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

def cauchy.pre_ecart_self_eq_zero_seq (T: Type*) [espace_metrique T] (x: cauchy_seqs T):
  pre_ecart x.val x.val = ((λ n, 0): ℕ → ℝ) := begin
  rw pre_ecart,
  ext,
  apply espace_metrique.presep,
  refl,
end

instance pre_ecart.premetrique (T: Type*) [espace_metrique T]: espace_pre_metrique (cauchy_seqs T) :=
{ d := cauchy.dist T,
  d_pos := cauchy.d_pos T,
  presep := begin
  intros x y h,
  rw cauchy.dist,
  rw h,
  conv {
    congr,
    congr,
    rw cauchy.pre_ecart_self_eq_zero_seq T y,
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
  triangle := begin
  intros x y z,
  rw cauchy.dist,
  rw cauchy.dist,
  rw cauchy.dist,
  apply cauchy.limit_le_of_add_seq_le,
  exact pre_ecart.triangle _ _ _,
  end
}

def cauchy.cong (T: Type*) [espace_metrique T] (x y: cauchy_seqs T): Prop := cauchy.dist T x y = 0
lemma cauchy.cong_refl (T: Type*) [espace_metrique T]: reflexive (cauchy.cong T) := begin
  intro x,
  rw cauchy.cong,
  exact espace_pre_metrique.presep x x (by refl),
end
lemma cauchy.cong_symm (T: Type*) [espace_metrique T]: symmetric (cauchy.cong T) := begin
  intros x y H,
  rw cauchy.cong,
  rw cauchy.cong at H,
  rw ← H,
  symmetry,
  exact espace_pre_metrique.sym x y,
end
lemma cauchy.cong_trans (T: Type*) [espace_metrique T]: transitive (cauchy.cong T) := begin
  intros x y z Hxy Hyz,
  rw cauchy.cong,
  rw cauchy.cong at Hxy,
  rw cauchy.cong at Hyz,
  apply le_antisymm,
  calc
    cauchy.dist T x z ≤ cauchy.dist T x y + cauchy.dist T y z : espace_pre_metrique.triangle x y z
    ... ≤ 0 + 0 : by rw [Hxy, Hyz]
    ... ≤ 0 : by simp,
  exact espace_pre_metrique.d_pos x z,
end
theorem cauchy.cong_equiv (T: Type*) [espace_metrique T]: equivalence (cauchy.cong T) :=
⟨cauchy.cong_refl T, cauchy.cong_symm T, cauchy.cong_trans T⟩

instance pre_ecart.setoid (T: Type*) [espace_metrique T] : setoid (cauchy_seqs T) :=
{
  r := cauchy.cong T,
  iseqv := cauchy.cong_equiv T
}

end suites

-- Le complété !
section completion
def completion (T: Type*) [espace_metrique T]: Type* := quotient (pre_ecart.setoid T)
local attribute [instance] pre_ecart.setoid
def completion.dist_soundness (T: Type*) [espace_metrique T]:
  ∀ x₁ x₂: cauchy_seqs T, ∀ y₁ y₂: cauchy_seqs T, (x₁ ≈ y₁) → (x₂ ≈ y₂) → (cauchy.dist T x₁ x₂ = cauchy.dist T y₁ y₂) := begin
  intros x y z t Hxz Hyt,
  simp at Hxz,
end
def completion.dist (T: Type*) [espace_metrique T] (x y: completion T): ℝ :=
  quotient.lift₂ (cauchy.dist T) (completion.dist_soundness T) x y

instance completion.metric_space (T: Type*) [espace_metrique T]: espace_metrique (completion T) :=
{
  d := completion.dist T,

}
end completion