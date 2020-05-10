import tactic
import data.set
import order.conditionally_complete_lattice

import .defs
import .sequences

noncomputable theory
open_locale classical

section suites
variables {X: Type} [conditionally_complete_linear_order X]
def suite_st_croissante {S: set X}
  (Hinf: set.infinite S)
  (Hset: (∀ M ⊆ S, M.nonempty → is_least M (Inf M))) : ℕ → X := 
  well_founded.fix nat.lt_wf
  (λ n suite_st_croissante, 
    Inf (S \ { x : X | ∃ k < n, suite_st_croissante k H = x}))

def suite_st_croissante_def {S: set X}
  (Hinf: set.infinite S)
  (Hset: (∀ M ⊆ S, M.nonempty → is_least M (Inf M))) (n: ℕ):
    suite_st_croissante Hinf Hset n = Inf (S \ { x: X | ∃ k < n, suite_st_croissante Hinf Hset k = x })
    := well_founded.fix_eq _ _ _

lemma suite_st_croissante_image {S: set X}
 (Hinf: set.infinite S) (Hset: (∀ M ⊆ S, M.nonempty → is_least M (Inf M))) (n: ℕ):
    {x : X | ∃ k < n, suite_st_croissante Hinf Hset k = x}
      = (suite_st_croissante Hinf Hset) '' { i : ℕ | i < n} := by ext; simp

lemma suite_st_croissante_finite {S: set X}
 (Hinf: set.infinite S) (Hset: (∀ M ⊆ S, M.nonempty → is_least M (Inf M))) (n: ℕ):
  ({x : X | ∃ k < n, suite_st_croissante Hinf Hset k = x}).finite := begin
    rw suite_st_croissante_image,
    apply set.finite_image,
    apply set.finite_lt_nat,
 end

lemma suite_st_croissante_nonempty {S: set X}
 (Hinf: set.infinite S) (Hset: (∀ M ⊆ S, M.nonempty → is_least M (Inf M))) (n: ℕ):
    (S \ { x: X | ∃ k < n, suite_st_croissante Hinf Hset k = x }).nonempty :=
  begin
  set L := {x : X | ∃ (k : ℕ) (H : k < n), suite_st_croissante Hinf Hset k = x},
  by_contra,
  apply Hinf,
  have a := set.not_nonempty_iff_eq_empty.1 a,
  have := set.diff_eq_empty.1 a,
  apply set.finite_subset,
  exact suite_st_croissante_finite Hinf Hset n,
  exact this,
  end

lemma suite_st_croissante_subset {S: set X}
 (Hinf: set.infinite S) (Hset: (∀ M ⊆ S, M.nonempty → is_least M (Inf M))) (p: ℕ) (q: ℕ):
    p ≤ q → 
    S \ { x: X | ∃ k < q, suite_st_croissante Hinf Hset k = x } ⊆  S \ { x: X | ∃ k < p, suite_st_croissante Hinf Hset k = x } :=
    begin
    intro h,
    apply set.diff_subset_diff_right,
    rw suite_st_croissante_image,
    rw suite_st_croissante_image,
    apply set.image_subset,
    intros i hi,
    simp at hi,
    simp,
    exact lt_of_lt_of_le hi h,
    end

lemma suite_st_croissante_mem {S: set X}
 (Hinf: set.infinite S) (Hset: (∀ M ⊆ S, M.nonempty → is_least M (Inf M))) (n: ℕ):
    suite_st_croissante Hinf Hset n ∈ S :=
  begin
  rw suite_st_croissante_def,
  set L := S \ { x: X | ∃ k < n, suite_st_croissante Hinf Hset k = x },
  have Hmem: L ⊆ S := set.diff_subset S _,
  apply Hmem,
  exact (Hset L Hmem (suite_st_croissante_nonempty _ _ n)).1,
  end

lemma suite_st_croissante_props (S: set X)
  (Hinf: set.infinite S):
  (∀ M ⊆ S, M.nonempty → is_least M (Inf M)) → ∃ x : ℕ → X, strictement_croissante x ∧ (set.range x) ⊆ S :=
  begin
  intro H,
  use suite_st_croissante Hinf H,
  split,
  intros p q hq,
  -- ici il s'agit de prouver une inégalité stricte entre deux infs.
  -- il faut comprendre: S_q est inclus strictement dans S_p
  -- donc inf S_p ≤ inf S_q
  -- de plus (inf S_p) = suite_st_croissante p
  -- donc, (inf S_p) n'est pas dans S_q
  -- or, inf S_q est dans S_q
  -- donc, inf S_p < inf S_q.
  -- niveau: moyen+
  apply lt_of_le_of_ne,
  rw suite_st_croissante_def,
  rw suite_st_croissante_def,
  set ssc := suite_st_croissante Hinf H with ← hssc,
  have S_nonempty: ∀ n, (S \ { x : X | ∃ k < n, ssc k = x }).nonempty := suite_st_croissante_nonempty Hinf _,
  set Sp := S \ {x : X | ∃ k < p, ssc k = x} with ← hsp,
  set Sq := S \ {x : X | ∃ k < q, ssc k = x} with ← hsq,
  apply cInf_le_cInf,
  have S_bdd: ∀ n, bdd_below (S \ { x : X | ∃ k < n, ssc k = x }) :=
  begin
    {
      intro n,
      set Sn := (S \ { x : X | ∃ k < n, ssc k = x }),
      apply is_least.bdd_below,
      apply H,
      exact set.diff_subset S _,
      exact S_nonempty n,
    }
  end,
  apply S_bdd p,
  exact S_nonempty q,
  exact suite_st_croissante_subset Hinf H _ _ (le_of_lt hq),
  set ssc := suite_st_croissante Hinf H with ← hssc,
  set Sqq := {x : X | ∃ (k : ℕ) (H : k < q), ssc k = x} with ← hspp,
  set Sp := S \ {x : X | ∃ k < p, ssc k = x} with ← hsp,
  set Sq := S \ Sqq with ← hsq,
  by_contra,
  push_neg at a, -- x_p = x_q est impossible par construction de x.
  -- en effet, puisque p < q, alors x_p = x_q = inf S_q = inf (S \ (réunion_(k < q) S_k)), or x_p est dans S_p
  -- donc: x_p n'est pas dans S \ (réunion (k < q) S_k), donc x_p != inf (S \ …)
  -- ABSURDE.
  have Hn: ∀ n, ssc n ∈ (S \ { x: X | ∃ k < n, ssc k = x }) := begin
  {
    intro n,
    set Sn := S \ {x : X | ∃ k < n, ssc k = x} with ← hsn,
    rw ← hssc,
    rw suite_st_croissante_def,
    rw hssc,
    rw hsn,
    exact (H Sn (set.diff_subset S _) (suite_st_croissante_nonempty Hinf H _)).1,
  }
  end,
  have Hp := Hn q,
  rw ← a at Hp,
  rw hsq at Hp,
  have Hnp := set.not_mem_of_mem_diff Hp,
  have Hpp: ssc p ∈ Sqq := begin
    use p,
    split,
    exact hq,
    refl,
  end,
  exact Hnp Hpp,
  intros x hx,
  simp at hx,
  obtain ⟨ y ⟩ := hx,
  rw ← hx_h,
  exact suite_st_croissante_mem Hinf H _,
end
end suites