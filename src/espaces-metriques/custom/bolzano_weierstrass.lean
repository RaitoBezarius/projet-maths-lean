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

open set

lemma strictly_increasing_sequence_is_not_bdd_above (S: set X)
  (x: ℕ → X): strictement_croissante x → ¬ bdd_above (range x) := begin
  sorry,
end

/-- Il faut comprendre ce lemme comme:
-- Dès lors que toutes parties de S ont des max et des min, alors S est finie.
-- Ce lemme est fondamental dans la mesure où il entraîne directement l'existence des points limites
-- dans le cas de parties infinies.
--/
lemma lemme_fondateur_de_bw (S: set X):
  (∀ U ⊆ S, U.nonempty → is_greatest U (Sup U) ∧ is_least U (Inf U)) →  set.finite S :=
begin
  by_contra H,
  push_neg at H,
  rw ← set.infinite at H,
  obtain ⟨ Hsupinf, Hinfinite ⟩ := H,
  have Hinf: ∀ U ⊆ S, U.nonempty → is_least U (Inf U) := λ U hU hN, (Hsupinf U hU hN).2,
  obtain ⟨ x, hsc, hrange ⟩ := suite_st_croissante_props S Hinfinite Hinf,
  apply strictly_increasing_sequence_is_not_bdd_above S x hsc,
  apply is_greatest.bdd_above,
  exact (Hsupinf (range x) hrange (set.range_nonempty _)).1,
end

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
have: point_limite U (Sup U) := real.Sup_is_a_limit_point U hsup (bdd_above.mono subU hbdd.2),
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

-- le merveilleux.
-- niveau: magnifique.

lemma principe_des_tiroirs {A: Type} {B: Type} {f: A → B} (Hinfinite: infinite A) (Hfinite: (range f).finite):
  ∃ x ∈ (range f), (preimage f {x}).infinite := sorry

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
  -- niveau: moyen.
  -- prendre p = min (x^-1{x_0} \ [[0, N - 1]]) (non vide & partie de N & infini).
  -- un tel p vérifie x p = l, donc d (x p) l = 0 < ε.
  -- d'où le résultat désiré d'adhérence.
  sorry,
},
{
  obtain ⟨ l ⟩ := bolzano_weierstrass_v2 (range x) h bdd_above_and_below_of_image,
  use l,
  obtain ⟨ y, ⟨ hssuite, hcv ⟩ ⟩ := h_1,
  intros ε hε N,
  obtain ⟨ N₀, hcv ⟩ := hcv ε hε,
  suffices hX: ∃ n₀ ≥ N, ∃ p₀ ≥ N₀, x n₀ = y p₀, begin
    obtain ⟨ n₀, Hn0, p₀, Hpn0, Hxy ⟩ := hX,
    use n₀,
    split,
    exact Hn0,
    have := hcv p₀ Hpn0,
    rw ← Hxy at this,
    rw espace_metrique.sym at this,
    exact this,
  end,
  -- il suffit de prouver qu'on peut trouver n0 assez grand et p0 assez grand tel que x n0 = y p0
  -- c'est suffisant de prouver que par infinitude, on peut trouver p0 assez grand tel que y p0 possède un rang assez grand.
  -- niveau: moyen.
  -- preuve: prouver que la préimage de x par { y(p) | p ≥ N0} est infinie, c'est vrai car son complémentaire est finie (immédiatement).
  -- donc, on prend un n0 plus grand que N dedans, possible par définition de l'infinitude.
  sorry,
}
end
end bw