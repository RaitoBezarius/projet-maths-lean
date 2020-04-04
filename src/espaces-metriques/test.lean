import data.set
import data.set.finite
import data.real.basic
import data.finset
import order.conditionally_complete_lattice

noncomputable theory
open_locale classical
open set

class metric_space (X : Type) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x = y → d x y = 0)
(sep : ∀ x y, d x y = 0 →  x = y)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)

variables {X:Type} [metric_space X]

open metric_space

/-- Instantiation des réels comme espace métrique. -/
instance real.metric_space : metric_space ℝ :=
{ d                  := λx y, abs (x - y),
  d_pos              := by simp [abs_nonneg],
  presep             := begin simp, apply sub_eq_zero_of_eq end,
  sep                := begin simp, apply eq_of_sub_eq_zero end,
  sym                := assume x y, abs_sub _ _,
  triangle           := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : d x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : d x 0 = abs x :=
by simp [real.dist_eq]

def converge (x: ℕ → X) (l : X) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ((d l (x n))  < ε)

lemma one_inv_lt_eps: ∀ ε > 0, ∃ N ≥ 0, 1 / (N + 1) ≤ ε := sorry
lemma seq_aux_1 (x: ℕ → ℝ) (l: ℝ): ∀ n, d (x n) l ≤ 1 / (n + 1) → converge x l := sorry

lemma sup_is_a_cv_seq (S: set ℝ):
  S.nonempty → bdd_above S → ∃ (x: ℕ → ℝ), (set.range x) ⊆ S ∧ converge x (Sup S) := begin
  intros hnn hbdd,
  have: ∀ ε > 0, ∃ x ∈ S, Sup S - x < ε := sorry,
  have: ∀ ε > 0, ∃ x ∈ S, d (Sup S) x < ε := begin
  intros ε hε,
  obtain ⟨ x, hx, hs_lt ⟩ := this ε hε,
  use x,
  split,
  exact hx,
  rw real.dist_eq,
  apply abs_lt_of_lt_of_neg_lt,
  exact hs_lt,
  sorry, -- by definition of sup.
  end,
  have: ∀ (N: ℕ), ∃ x ∈ S, d (Sup S) x < 1/(N + 1) := sorry,
  choose x hrange h using this,
  use x,
  split,
  intros y hy,
  obtain ⟨ N, hN ⟩ := hy,
  rw ← hN,
  exact hrange N,
  intros ε hε,
  -- 1/(N + 1) ≤ eps
  -- 1/eps ≤ N + 1
  -- 1/eps - 1 ≤ N
  have Hfloor_nonzero: floor(1/ε) > 0 := begin
  apply one_div_pos_of_pos,
  sorry,
  end
  lift floor(1/ε) to ℕ with N₀,
  use N₀,
  intros n hn,
  transitivity,
  exact h n,
  apply lt_of_le_of_lt,
  swap 2,
  -- 1/(N_0 + 1) = 1/(floor(1/eps) + 1) < eps <=> floor(1/eps) + 1 > 1/eps
  apply (one_div_lt hε _).1,
  apply lt_floor_add_one,
  norm_cast,
  rw ← h_1,
  refine add_pos _ trivial,
  exact Hfloor_nonzero,
  apply one_div_le_one_div_of_le,
  norm_cast,
  rw ← h_1,
  refine add_pos _ trivial,
  exact Hfloor_nonzero,
  rw ← h_1,
  norm_cast,
  simp,
  exact hn,
  exact le_of_lt Hfloor_nonzero,
  end