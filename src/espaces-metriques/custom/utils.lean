import .defs
import .sequences

import data.set
import topology.algebra.ordered
open espace_metrique

section extra
variables {X: Type} [espace_metrique X]
/-- bornee => bounded (range x) -/
lemma bornee_est_bounded (x: ℕ → X): bornee x → ∃ M > 0, bounded (λ x y, d x y ≤ M) (set.range x) :=
begin
intro Hb,
have h: set.nonempty (set.range x) := range_nonempty_iff_nonempty.2 nonempty_of_inhabited,
obtain ⟨ y, hy ⟩ := h,
obtain ⟨ M, ⟨ hm, hbdd⟩ ⟩ := Hb y,
use M,
split,
exact hm,
use y,
intros x hx,
simp at hx,
obtain ⟨ n, hn ⟩ := hx,
rw ← hn,
exact hbdd n,
end

/-- bounded (range x) => bornee -/
-- niveau: moyen
lemma bounded_est_bornee (x: ℕ → X): ∃ M > 0, bounded (λ x y, d x y ≤ M) (set.range x) → bornee x := sorry

end extra