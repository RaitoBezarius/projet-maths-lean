import .defs
import algebra.pi_instances

open espace_metrique

section suites

variables {X:Type} [espace_metrique X]
variables {Y:Type} [espace_metrique Y]
variables {Z:Type} [espace_metrique Z]


def strictement_croissante [linear_order X] (x: ℕ → X) := ∀ p : ℕ, ∀ q > p, x p < x q

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

-- valeur d'adhérence.
def adhere (x: ℕ → X) (l: X) := ∀ ε > 0, ∀ N : ℕ, ∃ p ≥ N, d (x p) l < ε

end suites

lemma neg_converge {x: ℕ → ℝ} {l: ℝ}:
  converge x l → converge (-x) (-l) := begin
  intro cv,
  intros ε hε,
  obtain ⟨ N, hN ⟩ := cv ε hε,
  use N,
  intros n hn,
  simp,
  rw real.dist_eq,
  simp,
  rw ← real.dist_eq,
  rw sym,
  exact hN n hn,
end

lemma converge_of_dist_lt_one_div_succ {x: ℕ → ℝ} {l: ℝ}: (∀ n, d l (x n) ≤ 1 / (n + 1)) → converge x l := begin
intro H,
intros ε hε,
obtain ⟨ N, hN ⟩ := exists_nat_one_div_lt hε,
use N,
intros n hn,
calc d l (x n) ≤ 1 / (n + 1) : H n
    ... ≤ 1 / (N + 1) : nat.one_div_le_one_div hn
    ... < ε : hN
end