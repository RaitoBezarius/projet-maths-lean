import .defs
import .sequences

open espace_metrique
open_locale classical

section suites

variables {X:Type} [espace_metrique X]
variables {Y:Type} [espace_metrique Y]
variables {Z:Type} [espace_metrique Z]

-- Définir la continuité séquentielle --/

-- f est continue en L si pour tout (x_n) ∈ ℝ^ℕ convergente de limite L, (f(x_n))_n est convergente de limite f(L).
def seq_continue_en_l (f: X → Y) (L: X) := ∀ (x: ℕ → X), converge x L → converge (suite_image f x) (f L)
def seq_continue (f: X → Y) := ∀ L : X, seq_continue_en_l f L

/-- On démontre que la continuité séquentielle est stable par composition --/

-- On démontre la composition des suites images.
theorem comp_suite_image (f: X → Y) (g: Y → Z) (x: ℕ → X): suite_image g (suite_image f x) = suite_image (g ∘ f) x :=
begin
ext,
repeat {rw suite_image},
end

-- On se ramène à la continuité séquentielle en un point.
theorem comp_seq_continue_ponctuel (f : X → Y) (g : Y → Z) (l: X):
  seq_continue_en_l f l ∧ seq_continue_en_l g (f l)
  → seq_continue_en_l (g ∘ f) l := begin
  intros H x x_cv,
  cases H with Hf Hg,
  have := Hg (suite_image f x) (Hf x x_cv),
  conv at this {
    congr,
    rw comp_suite_image f g x,
    skip,
    skip,
  },
  exact this,
end

theorem comp_seq_continue (f:X → Y) (g:Y → Z):
 seq_continue f ∧ seq_continue g → seq_continue (g ∘ f):=
 begin
 intro H,
 intro l,
 apply comp_seq_continue_ponctuel,
 cases H with Hf Hg,
 split,
 exact Hf l,
 exact Hg (f l),
 end

end suites