import tactic
import data.set
import .sequences
import .topology
import .negative_sets

noncomputable theory
open_locale classical
open espace_metrique

namespace real

lemma Sup_sub_lt_eps {S: set ℝ}: S.nonempty → bdd_above S → ∀ ε > 0, ∃ x ∈ S, Sup S - x < ε := begin
intros Hne Hbdd,
by_contra,
push_neg at a,
obtain ⟨ ε, ⟨ hε, hyp ⟩ ⟩ := a,
have: ∀ (x: ℝ), x ∈ S → x ≤ Sup S - ε := begin
intros x hx,
have hyp := hyp x hx,
linarith,
end,
have habsurd := cSup_le Hne this,
linarith,
end

lemma Sup_dist_lt_eps {S: set ℝ}: S.nonempty → bdd_above S → ∀ ε > 0, ∃ x ∈ S, d (Sup S) x < ε := begin
  intros Hne Hbdd,
  intros ε hε,
  obtain ⟨ x, hx, hs_lt ⟩ := Sup_sub_lt_eps Hne Hbdd ε hε,
  use x,
  split,
  exact hx,
  rw dist_eq,
  apply abs_lt_of_lt_of_neg_lt,
  exact hs_lt,
  calc -(Sup S - x) = x - Sup S : by simp
      ... ≤ Sup S - Sup S : (sub_le_sub_right (le_cSup Hbdd hx) (Sup S))
      ... ≤ 0 : by simp
      ... < ε : hε
end

lemma Sup_is_a_cv_seq (S: set ℝ):
  S.nonempty → bdd_above S → adhere_ens S (Sup S) := begin
  intros hnn hbdd,
  have: ∀ (N: ℕ), ∃ x ∈ S, d (Sup S) x ≤ 1/(N + 1) := λ N,
  let ⟨ x, ha, hb ⟩ := (Sup_dist_lt_eps hnn hbdd (1 / (N + 1)) (nat.one_div_pos_of_nat))
  in ⟨ x, ⟨ ha, le_of_lt hb ⟩ ⟩,
  choose x hrange h using this,
  use x,
  split,
  exact hrange,
  exact converge_of_dist_lt_one_div_succ h,
end

-- suffit de prendre une suite qui converge vers Sup S
-- puis de prendre la suite opposée, qui converge vers -Sup S = Inf S
lemma Inf_is_a_cv_seq (S: set ℝ):
  S.nonempty → bdd_below S → adhere_ens S (Inf S) := begin
  intros Hne Hbdd,
  apply negative_set.adhere_ens_iff.2,
  rw Inf_def,
  simp,
  exact Sup_is_a_cv_seq (negative_set S) (negative_set.nonempty Hne) (negative_set.bdd_above Hbdd)
  end

-- sous hypothèse que le sup ou l'inf ne sont pas dans l'ensemble, ils forment des points limites.
lemma Sup_is_a_limit_point (S: set ℝ):
  (Sup S) ∉ S → S.nonempty → bdd_above S → point_limite S (Sup S) := begin
  intros hsup hne hbdd,
  obtain ⟨ x, hrange, hcv ⟩ := Sup_is_a_cv_seq S hne hbdd,
  use x,
  split,
  rw set.diff_singleton_eq_self,
  exact hrange,
  exact hsup,
  exact hcv
end

lemma Inf_is_a_limit_point (S: set ℝ): 
  (Inf S) ∉ S → S.nonempty → bdd_below S → point_limite S (Inf S) := 
  begin
  intros hinf hne hbdd,
  obtain ⟨ x, hrange, hcv ⟩ := real.Inf_is_a_cv_seq S hne hbdd,
  use x,
  split,
  rw set.diff_singleton_eq_self,
  exact hrange,
  exact hinf,
  exact hcv
  end

end real

namespace set.finite
variables {X: Type}

lemma has_greatest_element [decidable_linear_order X] (S: set X):
  S.finite → S.nonempty → ∃ x ∈ S, is_greatest S x := begin
  intros Hf Hnn,
  lift S to (finset X) using Hf,
  use (finset.max' S Hnn),
  have Hmem := finset.max'_mem S Hnn,
  split,
  exact Hmem,
  rw is_greatest,
  split,
  exact Hmem,
  rw upper_bounds,
  simp,
  exact finset.le_max' S Hnn,
end

lemma has_a_reached_sup
  [conditionally_complete_linear_order X] {S: set X}:
  S.finite → S.nonempty → Sup S ∈ S := begin
  intros Hf Hnn,
  obtain ⟨ x, Hmem, Hgt ⟩ := (has_greatest_element S Hf Hnn),
  rw is_greatest.cSup_eq Hgt,
  exact Hmem,
end
end set.finite