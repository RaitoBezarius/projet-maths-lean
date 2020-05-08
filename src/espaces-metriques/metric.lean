import tactic
import data.real.basic
import data.real.cau_seq
import data.set
import data.set.finite
import data.finset
import order.bounds
import order.complete_lattice
import topology.algebra.ordered

import .custom.defs
import .custom.sequences
import .custom.sups
import .custom.topology
import .custom.bolzano_weierstrass


noncomputable theory


open set
open_locale classical
section suites

open espace_metrique
variables {X: Type} [espace_metrique X]
variables {Y: Type} [espace_metrique Y]
variables {Z: Type} [espace_metrique Z]

def fonction_distance (x : ℕ → X) (y: X) (n: ℕ) := d (x n) y

lemma cauchy_est_bornee {x: ℕ → X} : cauchy x → bornee x := 
begin
intros cauch y,
obtain ⟨ N, H ⟩ : ∃ N, ∀ p ≥ N, ∀ q ≥ N, ((d (x p) (x q)) < 1),
apply cauch, linarith,
set Limage := { M: ℝ | ∃ n ≤ N, M = d (x n) y },
have limage_finiteness: Limage.finite := begin
  have: ((fonction_distance x y) '' ({ i: ℕ | i ≤ N })) = Limage := begin
    {
      ext,
      split,
      intro h1,
      simp,
      simp at h1,
      cases h1 with n h1,
      rw fonction_distance at h1,
      use n,
      cc,  
      intro h2,
      simp,
      simp at h2,
      cases h2 with n h2,
      rw ← fonction_distance at h2,
      use n,
      cc, 
    }
  end,
  rw ← this,
  apply set.finite_image,
  exact set.finite_le_nat N,
  end,
have limage_nonempty: Limage.nonempty := begin
  use (d (x 0) y),
  simp,
  use 0,
  split,
  exact zero_le N,
  refl,
end,
have sup_est_atteint: Sup Limage ∈ Limage
  := set.finite.has_a_reached_sup limage_finiteness limage_nonempty,
  -- f : n → d (x n) y
  -- f : ℕ → ℝ
  -- f([[0, N]]).finite <=> [[0, N]].finite
simp at sup_est_atteint,
obtain ⟨ n, hn, sup_atteint ⟩ := sup_est_atteint,
use (max (d (x n) y) (1 + d (x N) y)), -- max(d(x_n, y), 1 + d(x_N, y))
split,
refine lt_max_iff.mpr _,
right,
apply add_pos_of_pos_of_nonneg,
exact zero_lt_one,
exact d_pos _ _,
intro p,
by_cases (p ≥ N),
have h1: d (x p) (x N) + d (x N) y ≤ max (d (x n) y) (1 + d (x N) y) := begin 
    {
      transitivity,
      apply add_le_add,
      apply le_of_lt,
      apply H _ h N (le_refl _),
      exact le_refl (d (x N) y),
      exact le_max_right _ _,
    }
  end,
have h2: d (x p) y ≤ d (x p) (x N) + d (x N) y := triangle (x p) (x N) y,
exact le_trans h2 h1, 
refine le_max_iff.mpr _,
left,
simp at h,
rw ← sup_atteint,
apply le_cSup,
apply set.bdd_above_finite,
exact limage_finiteness,
simp,
use p,
split,
exact le_of_lt h,
refl,
end

lemma gendarmes {x y z: ℕ → ℝ} {l: ℝ} : converge x l → converge z l → ∀ n:ℕ, (x n) ≤ (y n) → y n ≤ z n → converge y l := 
begin 
intros cx cz n xy yz,
rw converge at cx,
rw converge at cz,
rw converge,
intros ε peps at cx,
obtain ⟨ Nx,Hx ⟩ : ∃ Nx:ℕ, ∀ n:ℕ, n ≥ Nx → d l (x n) < ε := cx ε peps,
obtain ⟨ Nz,Hz ⟩ : ∃ Nz:ℕ, ∀ n:ℕ, n ≥ Nz → d l (z n) < ε := cz ε peps,
use Nx + Nz,
intros n hn,
rw real.dist_eq,
sorry
end 

lemma non_egal_eps {a:X} {b:X} : ¬ a = b → ∃ ε : ℝ, ε > 0 → d a b > ε := 
begin 
intro h,
by_contra,
simp at a_1, 
apply h,
have x : ℕ → ℝ,
intro n,
exact n,
have n:ℕ,
exact 0,

sorry

end 

-- niveau: moyen
lemma cauchy_admet_une_va {x: ℕ → X} : cauchy x → ∀ l₁ : X, ∀ l₂ : X, adhere x l₁ ∧ adhere x l₂ → l₁ = l₂ := 
begin 
intros cauch l1 l2 h,
by_contra,
push_neg,

end



-- niveau: difficile
lemma unicite_de_la_va {x: ℕ → X} {l: X} : adhere x l → (∀ l₀ : X, adhere x l₀ →  l = l₀) → converge x l := sorry

theorem R_is_complete : complete ℝ :=
begin
 intros x c,
 have := bolzano_weierstrass (cauchy_est_bornee c),
 obtain ⟨ l ⟩ := this,
 use l,
 apply unicite_de_la_va this_h,
 intros l₀ adh,
 apply cauchy_admet_une_va c,
 split,
 exact this_h,
 exact adh,
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

-- d(d(x, y), d(z, t)) ≤ d(x, z) + d(y, t)
-- idée: |d(x, y) - d(z,t)| ≤ d(x, z) + d(y, t)
-- 1er cas: d(x, y) ≤ d(z, t)
-- DONC: d(z, t) ≤ d(x, y) + d(x, z) + d(y, t)
-- d(z, t) ≤ d(z, x) + d(x, y) + d(y, t) (inégalité trig)
-- 2ème cas: d(x, y) ≤ d(y, t) + d(t, z) + d(z, x)
-- or: d(x, y) ≤ d(x, z) + d(z, t) + d(t, y) (inég trig)
-- 2 coups d'inégalité triangulaires, en distiguant sur le signe de d(x,y) - d(z,t).
lemma dist_ineg_utile (x y z t:X) : d (d x y)  (d z t) ≤ d x z + d y t:=
begin

 sorry
end

/-- on démontre que le pré-écart est une suite de Cauchy --/
-- montrer que (d(x_n, y_n))_n est de Cauchy
-- i.e. pour tout eps > 0,
-- pour tout (n, m) assez grands, d(d(x_n, y_n), d(x_m, y_m)) < eps
-- or: d(d(x_n, y_n), d(x_m, y_m)) ≤ d(x_n, x_m) + d(y_n, y_m) ≤ 2eps
lemma pre_ecart_cauchy (x y : ℕ →  X) (h1 : cauchy x) (h2 : cauchy y):
  cauchy (λ n : ℕ, d (x n) (y n)):=
 begin
rw cauchy,
intros ε peps,
-- créer peps2 qui vaille ε/2 > 0 
have peps2 :ε/2 > 0 := sorry,
rw cauchy at h1,
rw cauchy at h2,
obtain ⟨ N1, h11 ⟩  : ∃ N1, ∀ p ≥ N1, ∀ q ≥ N1, ((d (x p) (x q)) < ε/2 ),
exact h1 (ε/2) peps2,
obtain ⟨ N2, h21 ⟩  : ∃ N2, ∀ p ≥ N2, ∀ q ≥ N2, ((d (y p) (y q)) < ε/2 ),
exact h2 (ε/2) peps2,
use N1 + N2,
intros p hp q hq,
rw real.dist_eq,
have H : d (x p) (y p) - d (x q) (y q) = d (x p) (y p) - d (x q) (y p) + d (x q) (y p) - d (x q) (y q) := begin simp, end,
rw H,
have H2 : abs(d (x p) (y p) - d (x q) (y p) + d (x q) (y p) - d (x q) (y q)) < abs(d (x p) (y p) - d (x q) (y p)) + abs(d (x q) (y p) - d (x q) (y q)) := sorry, --1ere IT
have H3 :abs(d (x p) (y p) - d (x q) (y p) + d (x q) (y p) - d (x q) (y q))  < abs(d (x p) (x q)) + abs(d (y p) (y q)) := sorry, --2eme IT
have H4 : abs(d (x p) (y p) - d (x q) (y p) + d (x q) (y p) - d (x q) (y q))  < d (x p) (x q) + d (y p) (y q) := sorry, --distance positives
have H5 : abs(d (x p) (y p) - d (x q) (y p) + d (x q) (y p) - d (x q) (y q)) < ε := sorry, --remplacer
exact H5,
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