import tactic
import data.real.basic

import .custom.defs
import .custom.sequences
import .custom.cauchy


noncomputable theory


open set
open_locale classical
section suites

open espace_metrique
variables {X: Type} [espace_metrique X]
variables {Y: Type} [espace_metrique Y]
variables {Z: Type} [espace_metrique Z]

/-- on définit le *type* des suites de Cauchy --/

def cauchy_seqs (X: Type*) [espace_metrique X] := { f : ℕ → X // cauchy f }

/-- Si le temps le permet, et seulement dans ce cas,
-- montrer que le pre-ecart induit une structure
d'espace pre-metrique sur l'ensemble des suites de cauchy pour
pouvoir éventuellement construire la completion de l'espace X
comme le quotient de l'ensemble des suites de cauchy par la
relation d'équivalence appropriée --/

-- Retourne la limite de d(x_n, y_n) (bien définie par complétude de R), requiert l'axiome du choix.

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

instance pre_ecart.premetrique (X: Type*) [espace_metrique X]: espace_pre_metrique (cauchy_seqs X) :=
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

local attribute [instance] pre_ecart.premetrique
def completion.dist_soundness (T: Type*) [espace_metrique T]:
  ∀ x₁ x₂: cauchy_seqs T, ∀ y₁ y₂: cauchy_seqs T, (x₁ ≈ y₁) → (x₂ ≈ y₂) → (cauchy.dist T x₁ x₂ = cauchy.dist T y₁ y₂) := begin
  intros x y z t Hxz Hyt,
  change (cauchy.dist T x z = 0) at Hxz,
  change (cauchy.dist T y t = 0) at Hyt,
  apply le_antisymm,
  calc
    cauchy.dist T x y ≤ cauchy.dist T x z + cauchy.dist T z y : espace_pre_metrique.triangle x z y
    ... ≤ cauchy.dist T x z + (cauchy.dist T z t + cauchy.dist T t y) : add_le_add_left (espace_pre_metrique.triangle z t y) _
    ... = cauchy.dist T z t + cauchy.dist T y t : by rw [Hxz, zero_add, espace_pre_metrique.sym t y]
    ... = cauchy.dist T z t : by rw Hyt,
  calc
    cauchy.dist T z t ≤ cauchy.dist T z x + cauchy.dist T x t : espace_pre_metrique.triangle z x t
    ... ≤ cauchy.dist T z x + (cauchy.dist T x y + cauchy.dist T y t) : add_le_add_left (espace_pre_metrique.triangle x y t) _
    ... = cauchy.dist T x z + cauchy.dist T x y : by rw [Hyt, add_zero, espace_pre_metrique.sym z x]
    ... = cauchy.dist T x y : by rw Hxz,
end

end suites

-- Le complété !
section completion
def completion (T: Type*) [espace_metrique T]: Type* := quotient (pre_ecart.setoid T)
local attribute [instance] pre_ecart.setoid

def completion.dist (T: Type*) [espace_metrique T] (x y: completion T): ℝ :=
  quotient.lift₂ (cauchy.dist T) (completion.dist_soundness T) x y

def completion.dist_self_eq_zero (T: Type*) [espace_metrique T] (x: completion T): completion.dist T x x = 0 := sorry
def completion.d_pos (T: Type*) [espace_metrique T] (x y: completion T): completion.dist T x y ≥ 0 := sorry

instance completion.metric_space (T: Type*) [espace_metrique T]: espace_metrique (completion T) :=
{
  d := completion.dist T,
  d_pos := completion.d_pos T,
  presep := begin
    intros x y h,
    rw h,
    exact completion.dist_self_eq_zero T y,
  end,
  sep := begin
    intros x y h,
    sorry,
  end,
  sym := begin
    intros x y,
    sorry
  end,
  triangle := sorry }

}
end completion