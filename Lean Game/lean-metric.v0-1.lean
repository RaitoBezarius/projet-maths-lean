import tactic
import data.real.basic
import data.real.cau_seq
import data.set
import topology.algebra.ordered

noncomputable theory

-- Ce fichier prolonge un travail de Frédéric Le Roux qui a traité --
-- des propriétés topologiques des espaces métriques --

------------
-- ESSAIS --
------------
open set
open classical

-----------
-- DEBUT --
-----------


-- Une structure d'espace pré-métrique sur un type X --
class espace_pre_metrique (X : Type) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x=y → d x y = 0)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)

-- Une structure d'espace métrique sur un type X --
class espace_metrique (X : Type) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x=y → d x y = 0)
(sep : ∀ x y, d x y = 0 →  x = y)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)


open espace_metrique
-- open espace_pre_metrique --

/-- Instantiation des réels comme espace métrique. -/
instance real.metric_space : espace_metrique ℝ :=
{ d                  := λx y, abs (x - y),
  d_pos              := by simp [abs_nonneg],
  presep             := by simp [add_neg_eq_zero],
  sep                := by simp [add_neg_eq_zero],
  sym                := assume x y, abs_sub _ _,
  triangle           := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : d x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : d x 0 = abs x :=
by simp [real.dist_eq]


----------------------------------------------------
section suites
----------------------------------------------------
variables {X:Type} [espace_metrique X]
variables {Y:Type} [espace_metrique Y]
variables {Z:Type} [espace_metrique Z]

/-- Le but dans cette section est l'un des deux
-- buts suivants:
-- * construire l'écart naturel sur l'espace des suites de cauchy,
et si le temps le permet, construire sa completion
-- * montrer les propriétés de base des la continuité séquentielle
-- des fonctions entres espaces métriques --/

def converge (x: ℕ → X) (l : X) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ((d l (x n))  < ε)

def cauchy (x: ℕ → X) :=
  ∀ ε > 0, ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < ε)

def complete := ∀ x : ℕ → X, ∃ l : X, converge x l

/-- Un exemple de preuve --
-- Toute suite convergente est de cauchy --
-- On utilise souvent la tactique linarith
-- pour simplifier des inégalités--/

lemma converge_cauchy (x: ℕ → X) (l : X) : converge x l → cauchy x :=
begin
 intros conv ε hε,
 have hε2 : ε/2 > 0 := by linarith,
 obtain ⟨ N ⟩ : ∃ N, ∀ n ≥ N, ((d l (x n)) < ε/2),
 apply conv, exact hε2,
 use N,
 assume p ≥ N,
 have H2 : d l (x p) < ε/2 := h p H,
 assume q ≥ N,
 have H3 : d l (x q) < ε/2 := h q H,
 have H4 : d (x p) l = d l (x p):= sym (x p) l,
 have H5 : d l (x p) < ε/2 := by linarith,
 have clef : d (x p) (x q) ≤ d (x p) l + d l (x q), from triangle (x p) l (x q),
 linarith,
end


/-- Le résultat suivant pourra être admis ou démontré en utilisant la bibliotheque mathlib --/
theorem R_is_complete (x : ℕ → ℝ) : cauchy x → ∃ l : ℝ, converge x l:=
begin
 intros c,
 sorry
end

lemma unicite_limite (x: ℕ → X) (l₁ : X) (l₂ : X) :
 (converge x l₁) ∧ (converge x l₂) →   l₁ = l₂ :=
begin
 sorry
end

-- On définit la suite des distances entre deux suites,
-- appelée le pre_ecart --

def pre_ecart (x : ℕ → X) (y : ℕ → X) : ℕ → ℝ  :=
 λ n : ℕ, d (x n) (y n)

-- on pourra utiliser les tactiques linarith, rw, simp et split --
-- pour démontrer l'énoncé suivant, nécessaire pour démontrer --
-- que le pre_ecart est une suite de cauchy

lemma dist_ineg_utile (x y z t:X) : d (d x y)  (d z t) ≤ d x z + d y t:=
begin
 sorry
end

/-- on démontre que le pré-écart est une suite de Cauchy --/

lemma pre_ecart_cauchy (x y : ℕ →  X) (h1 : cauchy x) (h2 : cauchy y):
  cauchy (λ n : ℕ, d (x n) (y n)):=
 begin
  sorry
 end

/-- on définit l'ensemble des suites de Cauchy --/

def cauchy_seqs (X : Type) [espace_metrique X] : Type := { f : ℕ → X // cauchy f }

/-- Si le temps le permet, et seulement dans ce cas,
-- montrer que le pre-ecart induit une structure
d'espace pre-metrique sur l'ensemble des suites de cauchy pour
pouvoir éventuellement construire la completion de l'espace X
comme le quotient de l'ensemble des suites de cauchy par la
relation d'équivalence appropriée --/

-- Définir la continuité séquentielle --/

def seq_continue (f: X → Y):=sorry

/-- On démontre que la continuité séquentielle est stable par composition --/

theorem comp_seq_continue (f:X → Y) (g:Y → Z):
 seq_continue f ∧ seq_continue g → seq_continue g∘ f:=
 sorry

end suites