import data.real.basic
class metric_space (X : Type*) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x=y → d x y = 0)
(sep : ∀ x y, d x y = 0 →  x = y)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)

instance real.metric_space: metric_space ℝ :=
 { d := sorry, d_pos := sorry, presep := sorry, sep := sorry,
sym := sorry, triangle := sorry }
open_locale classical
noncomputable theory
section test
open metric_space
variables {X: Type*} [metric_space X]

def is_cauchy (x: ℕ → X) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < ε)
def converge (x: ℕ → X) (l : X) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ((d l (x n))  < ε)
def complete (T: Type) [metric_space T] := ∀ x : ℕ → T, is_cauchy x → ∃ l : T, converge x l

lemma R_is_complete: complete ℝ := sorry

def cauchy_seqs (X : Type*) [metric_space X] := { f : ℕ → X // is_cauchy f }
def cauchy.diff (x : ℕ → X) (y : ℕ → X) : ℕ → ℝ  :=
 λ n : ℕ, d (x n) (y n)
def cauchy.cauchy_of_diff (x y : ℕ →  X) (h1 : is_cauchy x) (h2 : is_cauchy y):
  is_cauchy (cauchy.diff x y) := sorry

def cauchy.limit (x: ℕ → ℝ) (H: is_cauchy x): ℝ := classical.some (R_is_complete x H)
def cauchy.dist (T: Type*) [metric_space T] (x y: cauchy_seqs T): ℝ
  := cauchy.limit (cauchy.diff x.val y.val) (cauchy.cauchy_of_diff x.val y.val x.property y.property)

def cauchy.cong (T: Type*) [metric_space T] (x y: cauchy_seqs T): Prop := cauchy.dist T x y = 0
instance cauchy.setoid (X : Type*) [metric_space X] : setoid (cauchy_seqs X) :=
{
  r := cauchy.cong X,
  iseqv := sorry
}
local attribute [instance] cauchy.setoid

def completion (X : Type*) [metric_space X] : Type* := quotient (cauchy.setoid X)

def completion.dist_soundness (T: Type*) [metric_space T]:
  ∀ x₁ x₂: cauchy_seqs T, ∀ y₁ y₂: cauchy_seqs T, (x₁ ≈ y₁) → (x₂ ≈ y₂) → (cauchy.dist T x₁ x₂ = cauchy.dist T y₁ y₂) := begin
  intros x y z t Hxz Hyt,
  change (x ≈ z) with (cauchy.dist T x z = 0) at Hxz,
  change (y ≈ t) with (cauchy.dist T y t = 0) at Hyt,
  apply le_antisymm,
  calc
    cauchy.dist T x y ≤ cauchy.dist T x z + cauchy.dist T z t + cauchy.dist T t y : sorry
    ... = cauchy.dist T z t + cauchy.dist T t y : by rw Hxz
    ... = cauchy.dist T z t + cauchy.dist T y t : sorry -- symmetry
    ... = cauchy.dist T z t : by rw Hyt,
  calc
    cauchy.dist T x 
end
def completion.dist (T: Type*) [metric_space T] (x y: completion T): ℝ :=
  quotient.lift₂ (cauchy.dist T) (completion.dist_soundness T) x y

instance completion.metric_space (X: Type*) [metric_space X]: metric_space (completion X) :=
{
  d := completion.dist X,
  d_pos := sorry,
  -- etc
}

end test