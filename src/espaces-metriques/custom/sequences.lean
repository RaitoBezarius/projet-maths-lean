import .defs
import algebra.pi_instances

open espace_metrique
open_locale classical

section suites

variables {X:Type} [espace_metrique X]
variables {Y:Type} [espace_metrique Y]
variables {Z:Type} [espace_metrique Z]
variables {T: Type} [linear_order T]


def strictement_croissante (x: ℕ → T) := ∀ p : ℕ, ∀ q > p, x p < x q

def converge (x: ℕ → X) (l : X) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ((d l (x n))  < ε)

def diverge_inf (x: ℕ → ℕ) :=
  ∀ A, ∃ N, ∀ n ≥ N, x n ≥ A

def cauchy (x: ℕ → X) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < ε)

-- Pour tout élément de l'espace, 
-- la suite est au plus à M de l'élément de l'espace.
def bornee (x: ℕ → X) :=
  ∀ y : X, ∃ M: ℝ, M > 0 ∧ (∀ n : ℕ, d (x n) y ≤ M)

def suite_image (f : X → Y) (x : ℕ → X) (n: ℕ) := f (x n)
def sous_suite (x: ℕ → X) (φ: ℕ → ℕ) (n: ℕ) := x (φ n)

-- valeur d'adhérence.
def adhere (x: ℕ → X) (l: X) := ∀ ε > 0, ∀ N : ℕ, ∃ p ≥ N, d l (x p) < ε
def c_adhere (x: ℕ → X) (l: X) := ∀ N: ℕ, ∀ n: ℕ, ∃ p ≥ n, d l (x p) < 1 / (N + 1)

def seq_adhere (x: ℕ → X) (l: X)
  := ∃ φ : ℕ → ℕ, strictement_croissante φ ∧ converge (sous_suite x φ) l

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

lemma converge_of_dist_lt_one_div_succ {x: ℕ → X} {l: X}: (∀ n, d l (x n) ≤ 1 / (n + 1)) → converge x l := begin
intro H,
intros ε hε,
obtain ⟨ N, hN ⟩ := exists_nat_one_div_lt hε,
use N,
intros n hn,
calc d l (x n) ≤ 1 / (n + 1) : H n
    ... ≤ 1 / (N + 1) : nat.one_div_le_one_div hn
    ... < ε : hN
end

lemma countable_adhere_of_adhere {x: ℕ → X} {l: X}:
  adhere x l → c_adhere x l := begin
  intro adh,
  intros N n,
  obtain ⟨ p, ⟨ hp, hclose ⟩ ⟩ := adh (1/(N + 1)) (nat.one_div_pos_of_nat) n,
  use p,
  split,
  exact hp,
  exact hclose,
end

lemma seq_adhere_of_adhere {x: ℕ → X} {l: X}:
  adhere x l → seq_adhere x l := begin
  intro adh,
  choose Y hpos hdist using (countable_adhere_of_adhere adh),
  have R: ℕ → ℕ := well_founded.fix nat.lt_wf
    (λ n r,
    Y n 
    (r (n - 1) (sorry)
    )),
  have Req: ∀ n, R n = Y n (R (n - 1)) := sorry, -- ~satisfies fixpoint equation. (R 0 = Y 0 (R -1), which makes no sense.)
  use R,
  split,
  sorry, -- by fixpoint equation
  apply converge_of_dist_lt_one_div_succ,
  intro n,
  rw [sous_suite, Req],
  apply le_of_lt,
  exact hdist _ _,
end

def identity_seq (n: ℕ) := n
lemma diverge_of_identity_seq:
  diverge_inf identity_seq := begin
  intro A,
  use A,
  intros n hn,
  rw identity_seq,
  exact hn
end
lemma diverge_of_comparison_seq {φ: ℕ → ℕ} {x: ℕ → ℕ}:
  diverge_inf x → (∃ N, ∀ n ≥ N, φ n ≥ x n) → diverge_inf φ := begin
  intros hdivx hcomp,
  intro A,
  obtain ⟨ N, hdivx ⟩ := hdivx A,
  obtain ⟨ M, hcomp ⟩ := hcomp,
  use (max N M),
  intros n hn,
  calc
    φ n ≥ x n : hcomp n (le_of_max_le_right hn)
    ... ≥ A : hdivx n (le_of_max_le_left hn)
end

lemma pos_of_strictly_increasing_seq {φ: ℕ → ℕ}:
  strictement_croissante φ → ∀ n, φ n ≥ n := begin
  intro st,
  intro n,
  induction n with hn,
  simp,
  rw nat.succ_eq_add_one,
  calc
    φ (hn + 1) > φ hn : st hn (hn + 1) (lt_add_one hn)
    ... ≥ hn : n_ih
end

lemma diverge_of_strictly_increasing_seq {φ: ℕ → ℕ}:
  strictement_croissante φ → diverge_inf φ := begin
  intro st,
  apply diverge_of_comparison_seq (diverge_of_identity_seq),
  use 0,
  simp,
  exact pos_of_strictly_increasing_seq st,
end

lemma adhere_of_seq_adhere {x: ℕ → X} {l: X}:
  seq_adhere x l → adhere x l := begin
  intro sadh,
  obtain ⟨ φ, ⟨ hmon, hconv ⟩ ⟩ := sadh,
  intros ε hε N,
  obtain ⟨ P, hconv ⟩ := hconv ε hε,
  obtain ⟨ Q, hPhi ⟩ := diverge_of_strictly_increasing_seq hmon N,
  use (φ (max P Q)),
  split,
  exact hPhi _ (le_max_right _ _),
  exact hconv _ (le_max_left _ _),
end

lemma adhere_iff_seq_adhere {x: ℕ → X} {l: X}:
  adhere x l ↔ seq_adhere x l := begin
  split,
  exact seq_adhere_of_adhere,
  exact adhere_of_seq_adhere,
end

lemma generalized_extractor_of_seq_in_range (x: ℕ → X) (y: ℕ → X) (S: set X):
  S ⊆ (set.range x) → ∀ n, y n ∈ S → ∃ φ : ℕ → ℕ, y = sous_suite x φ := sorry

end suites
