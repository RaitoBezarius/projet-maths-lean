import data.real.basic
class metric_space (X : Type*) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x=y → d x y = 0)
(sep : ∀ x y, d x y = 0 →  x = y)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)

section test
open metric_space
variables {X: Type*} [metric_space X]

def is_cauchy (x: ℕ → X) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < ε)

def cauchy_seqs (X : Type*) [metric_space X] := { f : ℕ → X // is_cauchy f }


def cauchy.setoid (X : Type*) [metric_space X] : setoid (cauchy_seqs X) :=
{
  r := sorry,
  iseqv := sorry
}
-- Définit la distance entre 2 suites de Cauchy par lim d(x_n, y_n).
def cauchy.dist (T: Type*) [metric_space T] (x y: cauchy_seqs T): ℝ
  := sorry -- some cauchy limit stuff.

def completion (X : Type*) [metric_space X] : Type* := quotient (cauchy.setoid X)
def completion.dist (T: Type*) [metric_space T] (x y: completion T): ℝ :=
  sorry -- quotient.lift₂ (cauchy.dist T) x y

  

instance completion.metric_space (X: Type*) [metric_space X]: metric_space (completion X) :=
{
  d := completion.dist,
  d_pos := sorry,
  -- etc
}

end test