import data.set
import data.real.basic
import algebra.pi_instances

section negative_sets

def negative_set (S: set ℝ): set ℝ := { x : ℝ | -x ∈ S}


def cv (x: ℕ → ℝ) (l: ℝ):= ∀ ε > 0, ∃ N ≥ 0, ∀ n ≥ N, abs ((x n) - l) < ε
def accu_point (S: set ℝ) (l: ℝ) :=
  ∃ (x: ℕ → ℝ), cv x l ∧ (∀ n, x n ∈ S)

-- where it is?
/-instance seq.neg : has_neg (ℕ → ℝ) := {
  neg := λ x, (λ n, - x n)
}-/

def negative_set.adhere_ens_iff {S: set ℝ} {l: ℝ}:
  accu_point S l ↔ accu_point (negative_set S) (-l) :=
begin
  split,
  intro adh,
  rw accu_point at adh,
  obtain ⟨ x, hx ⟩ := adh,
  use (-x),
  sorry
end

end negative_sets