import tactic
import data.set
import order.conditionally_complete_lattice

import .sequences
import .si_sequence
import .topology
import .sups

noncomputable theory
open_locale classical

section bw
variables {X: Type} [espace_metrique X] [conditionally_complete_linear_order X]

open espace_metrique
open set

/-- FIXME: À déplacer -/
-- le merveilleux.
-- niveau: magnifique.

lemma principe_des_tiroirs {A: Type} {B: Type} {f: A → B} (Hinfinite: infinite A) (Hfinite: (range f).finite):
  ∃ x ∈ (range f), (preimage f {x}).infinite := sorry

lemma strictly_increasing_sequence_has_no_max (S: set X)
  (x: ℕ → X): bdd_above (range x) → strictement_croissante x → Sup (range x) ∉ (range x) := begin
  intro H,
  by_contra Hbdd,
  sorry
end

lemma smallest_element (S: set ℕ): S.nonempty → ∃ n : ℕ, ∀ m < n, m ∉ S := begin
  intro H,
  use (nat.find H),
  intro m,
  apply nat.find_min H,
end

lemma infinite_diff_finite_is_infinite {T: Type} {A: set T} {B: set T}:
  set.infinite A → set.finite B → set.infinite (A \ B) := sorry

lemma infinite_set_is_not_empty {T: Type} {S: set T}: set.infinite S → S.nonempty :=
begin
intro h,
by_contra,
rw set.not_nonempty_iff_eq_empty at a,
apply h,
rw a,
exact set.finite_empty,
end

/-- Fin du FIXME
-- Il faut comprendre ce lemme comme:
-- Dès lors que toutes parties de S ont des max et des min, alors S est finie.
-- Ce lemme est fondamental dans la mesure où il entraîne directement l'existence des points limites
-- dans le cas de parties infinies.
--/

lemma lemme_fondateur_de_bw (S: set X):
  (∀ U ⊆ S, U.nonempty → is_greatest U (Sup U) ∧ is_least U (Inf U)) → set.finite S :=
begin
  by_cases S.nonempty,
  by_contra H,
  push_neg at H,
  rw ← set.infinite at H,
  obtain ⟨ Hsupinf, Hinfinite ⟩ := H,
  have Hinf: ∀ U ⊆ S, U.nonempty → is_least U (Inf U) := λ U hU hN, (Hsupinf U hU hN).2,
  have HSup: ∀ U ⊆ S, U.nonempty → is_greatest U (Sup U) := λ U hU hN, (Hsupinf U hU hN).1,
  have Hbdd: bdd_above S := is_greatest.bdd_above (HSup S (by refl) h),
  obtain ⟨ x, hsc, hrange ⟩ := suite_st_croissante_props S Hinfinite Hinf,
  apply strictly_increasing_sequence_has_no_max S x (bdd_above.mono hrange Hbdd) hsc,
  apply (HSup (range x) hrange (set.range_nonempty _)).1,
  intro _,
  rw not_nonempty_iff_eq_empty at h,
  rw h,
  exact set.finite_empty,
end

-- TODO: À réparer
lemma bolzano_weierstrass_v2 (S: set ℝ): (set.infinite S) → bdd_below S ∧ bdd_above S → ∃ l : ℝ, point_limite S l :=
begin
intros hs hbdd,
by_contra,
push_neg at a,
apply hs,
apply lemme_fondateur_de_bw,
intros U subU hU,
split,
-- TODO: c'est la même preuve pour sup ou inf à sup/inf près. Autant utiliser l'automatisation.
by_contra,
apply a (Sup U),
rw is_greatest at a_1,
push_neg at a_1,
have := is_lub_cSup hU (bdd_above.mono subU hbdd.2),
cases a_1 with hsup hub,
exact real.Sup_is_a_limit_point U hsup (bdd_above.mono subU hbdd.2),
obtain ⟨ x, hx, hc ⟩ := this,
use x,
split,
intro n,
apply mem_of_subset_of_mem,
transitivity,
exact hx,
apply diff_subset_diff_left,
exact subU,
exact hc,
rw is_lub at this,
rw is_least at this,
exfalso,
exact hub this.1,
by_contra,
apply a (Inf U),
rw is_least at a_1,
push_neg at a_1,
cases a_1 with hinf hlb,
have: point_limite U (Inf U) := real.Inf_is_a_limit_point U hinf (bdd_below.mono subU hbdd.1),
obtain ⟨ x, hx, hc ⟩ := this,
use x,
split,
intro n,
apply mem_of_subset_of_mem,
transitivity,
exact hx,
apply diff_subset_diff_left,
exact subU,
exact hc,
have := is_glb_cInf hU (bdd_below.mono subU hbdd.1),
rw is_glb at this,
rw is_greatest at this,
exfalso,
exact hlb this.1,
end

lemma bolzano_weierstrass {x: ℕ → ℝ}: bornee x → ∃ l : ℝ, adhere x l :=
begin
intro Hb,
have bdd_above_and_below_of_image: bdd_below (range x) ∧ bdd_above (range x) := sorry,
by_cases (set.finite (range x)),
{
  -- par principe des tiroirs, il existe x_0 dans S tel que x^-1{x_0} est infini.
  obtain ⟨ l, hl, hpreimage ⟩  := principe_des_tiroirs nat.infinite h,
  use l,
  intros ε hε N,
  have: ((preimage x {l}) \ { n : ℕ | n < N}).nonempty := begin
  apply infinite_set_is_not_empty,
  apply infinite_diff_finite_is_infinite,
  exact hpreimage,
  exact set.finite_lt_nat N,
  end,
  obtain ⟨ n, hn ⟩ := this,
  use n,
  obtain ⟨ hn_preimage, hn_gt_N ⟩ := ((set.mem_diff n).1 hn),
  split,
  simp at hn_gt_N,
  exact hn_gt_N,
  simp at hn_preimage,
  rw hn_preimage,
  rw presep,
  exact hε,
  refl, -- l = l
},
{
  -- C'est un peu moche, on peut directement utiliser y et prouver que c'est une sous-suite
  -- Donc, en tirer qu'on a bien une VA.
  obtain ⟨ l ⟩ := bolzano_weierstrass_v2 (range x) h bdd_above_and_below_of_image,
  use l,
  rw point_limite at h_1,
  rw adhere_ens at h_1,
  apply adhere_of_seq_adhere,
  obtain ⟨ x, hrange, hcv ⟩ := h_1,
  sorry,
}
end

end bw