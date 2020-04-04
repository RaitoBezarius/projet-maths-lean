import .defs
import .sequences

open espace_metrique

section topologie
variables {X:Type} [espace_metrique X]

-- Accumulation point of S
def adhere_ens (S: set X) (l: X) := ∃ (x: ℕ → X), (∀ n, x n ∈ S) ∧ (converge x l)

-- Limit point: l is an accumulation point of S \ { l }
def point_limite (S: set X) (l: X) := adhere_ens (S \ {l}) l

-- Completeness of the space.
def complete (T: Type) [espace_metrique T] := ∀ x : ℕ → T, cauchy x → ∃ l : T, converge x l

end topologie