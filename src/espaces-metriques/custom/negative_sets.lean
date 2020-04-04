import data.set
import algebra.pi_instances

import .topology

section negative_sets

def negative_set (S: set ℝ): set ℝ := { x : ℝ | -x ∈ S}

lemma negative_set.negative_set_eq_set
  (S: set ℝ): negative_set (negative_set S) = S :=
  begin
  rw negative_set,
  rw negative_set,
  simp,
  end

lemma negative_set.mem_iff {S: set ℝ} (x: ℝ):
  x ∈ S ↔ -x ∈ negative_set S := begin
  split,
  intro h,
  rw negative_set,
  finish,
  intro h,
  rw negative_set at h,
  finish,
end

lemma negative_set.nonempty {S: set ℝ}: 
  S.nonempty → (negative_set S).nonempty := begin
  intro hne,
  obtain ⟨ x, h ⟩ := hne,
  use (-x),
  rw negative_set,
  finish,
end

lemma negative_set.bdd_above {S: set ℝ}:
  bdd_below S → bdd_above (negative_set S) := begin
  intro bdd,
  obtain ⟨ M, hm ⟩ := bdd,
  rw lower_bounds at hm,
  simp at hm,
  use (-M),
  rw negative_set,
  rw upper_bounds,
  simp,
  intros a ha,
  apply le_neg.2,
  exact hm ha,
end


lemma negative_set.bdd_below {S: set ℝ}: 
  bdd_above S → bdd_below (negative_set S) :=
begin
  intro bdd,
  obtain ⟨ M, hm ⟩ := bdd,
  rw upper_bounds at hm,
  simp at hm,
  use (-M),
  rw negative_set,
  rw lower_bounds,
  simp,
  intros a ha,
  apply neg_le.1,
  exact hm ha,
end

lemma negative_set.bdd_above_iff {S: set ℝ}:
  bdd_below S ↔ bdd_above (negative_set S) := begin
  split,
  exact negative_set.bdd_above,
  set S' := negative_set S with hs,
  have Seq := negative_set.negative_set_eq_set S,
  rw ← Seq,
  rw ← hs,
  exact negative_set.bdd_below,
end

lemma negative_set.bdd_below_iff {S: set ℝ}:
  bdd_above S ↔ bdd_below (negative_set S) := begin
  split,
  exact negative_set.bdd_below,
  set S' := negative_set S with hs,
  have Seq := negative_set.negative_set_eq_set S,
  rw ← Seq,
  rw ← hs,
  exact negative_set.bdd_above,
end

lemma negative_set.adhere_ens {S: set ℝ} {l: ℝ}:
  adhere_ens S l → adhere_ens (negative_set S) (-l) :=
  begin
  intro adh,
  rw adhere_ens at adh,
  obtain ⟨ x, hx ⟩ := adh,
  use (-x),
  split,
  simp,
  intro n,
  exact (negative_set.mem_iff (x n)).1 (hx.1 n),
  exact neg_converge hx.2,
  end

lemma negative_set.adhere_ens_iff {S: set ℝ} {l: ℝ}:
  adhere_ens S l ↔ adhere_ens (negative_set S) (-l) :=
begin
  split,
  exact negative_set.adhere_ens,
  set S' := negative_set S with hs,
  have Seq := negative_set.negative_set_eq_set S,
  have leq: l = - -l := by simp,
  rw ← Seq,
  rw ← hs,
  set l' := -l with hl,
  rw leq,
  exact negative_set.adhere_ens,
end

end negative_sets