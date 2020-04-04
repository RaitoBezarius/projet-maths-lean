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
-- preuve un peu moche, à embellir?
-- proposition: prendre la contraposition plutôt que l'absurde et pour la preuve interne, faire du direct.
lemma lemme_fondateur_de_bw [conditionally_complete_linear_order X] (S: set X) 
  -- si pour toute partie M non vide de S, inf(M), sup(M) existent et sont dans M.
  (H: ∀ U ⊆ S, U.nonempty → is_greatest U (Sup U) ∧ is_least U (Inf U)): set.finite S :=
begin
by_contra,
-- en supposant S infini, on peut construire une infinité de x_n comme il suit:
suffices hsuite: ∃ x : ℕ → X, strictement_croissante x ∧ (set.range x) ⊆ S, from begin
  -- prendre X = { x_n | n ≥ 0 } partie de S non vide
  -- puisque (x_n)_n est une suite infine strictement croissante, alors sup(X) n'est pas dans X
  -- or, X est une partie de S, par caractère bien fondé, c'est absurde.
  -- donc S est fini.
  obtain ⟨ x, hm, R1 ⟩ := hsuite,
  have R2: (range x).nonempty := range_nonempty_iff_nonempty.2 nonempty_of_inhabited,
  have: ¬((Sup (range x)) ∈ (range x)) := begin
    by_contra,
    simp at a_1,
    -- puisque a_1 donne le fait que le sup (range x) est dans (range x)
    -- il existe donc n0 tel que x n0 = sup (range x)
    obtain ⟨ n₀, h ⟩ := a_1,
    -- or: x (n0 + 1) > x n0 = sup (range x).
    have : x (n₀ + 1) > x n₀ := begin
      apply hm,
      exact lt_add_one n₀,
    end,
    -- absurde par déf du sup (linarith ne suffira pas.)
    -- introduire l'inégalité du sup pour x (n0 + 1), réécrire le sup avec x n0.
    -- conclure avec linarith.
    sorry -- niveau: très facile
  end,
  apply this,
  exact (H (range x) R1 R2).1.1,
end,
apply suite_st_croissante_props S a,
intros M hs hn,
exact (H M hs hn).2,
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