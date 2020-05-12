import .defs
import .sequences
import .bolzano_weierstrass

open espace_metrique
open_locale classical
noncomputable theory

section suites

variables {X:Type} [espace_metrique X]
variables {Y:Type} [espace_metrique Y]
variables {Z:Type} [espace_metrique Z]

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

lemma dist_lt_of_ne {x: X} {y: X} : d x y ≠ 0 → d x y > 0 :=
begin
intro dnnz,
simp,
refine lt_of_le_of_ne _ (ne.symm dnnz),
apply espace_metrique.d_pos,
end 


lemma eq_of_dist_lt {x: X} {y: X} : (∀ ε > 0, d x y < ε) → x = y := begin
  contrapose!,
  intro hnnz,
  use ((d x y)/2),
  split,
  apply div_pos_of_pos_of_pos,
  apply dist_lt_of_ne,
  revert hnnz,
  contrapose!,
  exact espace_metrique.sep x y,
  exact zero_lt_two,
  apply le_of_lt,
  apply div_two_lt_of_pos,
  apply dist_lt_of_ne,
  revert hnnz,
  contrapose!,
  exact espace_metrique.sep x y,
end


lemma cauchy_admet_une_va {x: ℕ → X} : cauchy x → ∀ l₁ : X, ∀ l₂ : X, adhere x l₁ ∧ adhere x l₂ → l₁ = l₂ := 
begin 
intros cauch l1 l2 h,
apply eq_of_dist_lt,
intros ε hε,
have hε3 : ε/3 > 0 := by linarith,
obtain ⟨ n₀, h_cauchy ⟩ := cauch (ε/3) hε3,
obtain ⟨ p₁ , ⟨ hp₁, hl₁ ⟩ ⟩ := h.1 (ε/3) hε3 (n₀),
obtain ⟨ p₂ , ⟨ hp₂ , hl₂ ⟩ ⟩ := h.2 (ε/3) hε3 (n₀),
calc
  d l1 l2 ≤ d l1 (x p₁) + d (x p₁) l2 : espace_metrique.triangle _ _ _
    ... = d l1 (x p₁) + d (x p₁) l2 : by rw espace_metrique.sym l1 (x p₁)
    ... < ε/3 + d (x p₁) l2 : add_lt_add_right hl₁ (d (x p₁) l2)
    ... ≤ ε/3 + d (x p₁) (x p₂) + d (x p₂) l2 : begin have := espace_metrique.triangle (x p₁) (x p₂ ) l2, rw add_assoc (ε/3)  (d (x p₁) (x p₂)) (d (x p₂) l2), exact add_le_add_left this (ε/3), end 
    ... < ε/3 + ε/3 + d (x p₂) l2 : begin have := h_cauchy p₁ hp₁ p₂ hp₂, rw add_comm (ε/3) (d (x p₁) (x p₂)), rw add_assoc, rw add_assoc, exact add_lt_add_right this (ε / 3 + d (x p₂) l2), end 
    ... = ε/3 + ε/3 + d l2 (x p₂) : by rw espace_metrique.sym _ _
    ... < ε/3 + ε/3 + ε/3 : add_lt_add_left hl₂ (ε/3 + ε/3)
    ... = ε : by ring,
end

lemma converge_of_va_for_cauchy {x: ℕ → X} {l: X} : adhere x l → cauchy x → converge x l := 
begin
  intros hadh hc,
  intros ε hε,
  obtain ⟨ N, hc ⟩ := hc (ε/2) (by linarith),
  use N,
  obtain ⟨ M, ⟨ hM, hadh ⟩ ⟩ := hadh (ε/2) (by linarith) N,
  intros n hN,
  have hc := hc M hM n hN,
  calc
    d l (x n) ≤ d l (x M) + d (x M) (x n) : espace_metrique.triangle _ _ _
    ... < ε/2 + d (x M) (x n) : add_lt_add_right hadh _
    ... < ε/2 + ε/2 : add_lt_add_left hc _
    ... = ε : by ring
end

lemma converge_of_unicite_va (H: complete X) {x: ℕ → X} {l: X}: adhere x l → (∀ l', adhere x l' → l = l') → converge x l :=
  sorry


lemma unicite_limite (x: ℕ → X) (l₁ : X) (l₂ : X) :
 (converge x l₁) → (converge x l₂) → l₁ = l₂ :=
begin
intros hconv1 hconv2,
apply eq_of_dist_lt,
intros ε hε,
obtain ⟨ N₀, hcc1 ⟩ := hconv1 (ε/2) (by linarith),
obtain ⟨ N₁, hcc2 ⟩ := hconv2 (ε/2) (by linarith),
set N₂ := max N₀ N₁,
calc
  d l₁ l₂ ≤ d l₁ (x N₂) + d (x N₂) l₂ : espace_metrique.triangle _ _ _
  ... = d l₁ (x N₂) + d l₂ (x N₂) : by rw espace_metrique.sym (x N₂) l₂
  ... < d l₁ (x N₂) + ε/2 : add_lt_add_left (hcc2 N₂ (le_max_right _ _)) _
  ... < ε/2 + ε/2 : add_lt_add_right (hcc1 N₂ (le_max_left _ _)) _
  ... ≤ ε : by simp
end

theorem R_is_complete : complete ℝ :=
begin
 intros x c,
 have := bolzano_weierstrass (cauchy_est_bornee c),
 obtain ⟨ l ⟩ := this,
 use l,
 exact converge_of_va_for_cauchy this_h c,
end

-- On définit la suite des distances entre deux suites,
-- appelée le pre_ecart --

def pre_ecart (x : ℕ → X) (y : ℕ → X) : ℕ → ℝ  :=
 λ n : ℕ, d (x n) (y n)
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
rw real.dist_eq,
apply abs_le_of_le_of_neg_le,
rw sub_le_iff_le_add,
calc
  d x y ≤ d x z + d z y : espace_metrique.triangle _ _ _
  ... ≤ d x z + (d z t + d t y) : add_le_add_left (espace_metrique.triangle z t y) _
  ... = d x z + d z t + d y t : by rw [espace_metrique.sym t y, ← add_assoc] 
  ... = d x z + d y t + d z t : by ring, -- there must be something better.
simp,
rw sub_le_iff_le_add,
calc
  d z t ≤ d z x + d x t : espace_metrique.triangle _ _ _
  ... ≤ d z x + (d x y + d y t) : add_le_add_left (espace_metrique.triangle x y t) _
  ... = d x z + d x y + d y t : by rw [espace_metrique.sym z x, ← add_assoc]
  ... = d x z + d y t + d x y : by ring
end

/-- on démontre que le pré-écart est une suite de Cauchy --/
-- montrer que (d(x_n, y_n))_n est de Cauchy
-- i.e. pour tout eps > 0,
-- pour tout (n, m) assez grands, d(d(x_n, y_n), d(x_m, y_m)) < eps
-- or: d(d(x_n, y_n), d(x_m, y_m)) ≤ d(x_n, x_m) + d(y_n, y_m) ≤ 2eps

lemma pre_ecart_cauchy (x y : ℕ →  X) (h1 : cauchy x) (h2 : cauchy y):
  cauchy (pre_ecart x y):=
 begin
  set Cxy := pre_ecart x y with hceq,
  intros ε hε,
  obtain ⟨ N, hc1 ⟩ := h1 (ε/2) (by linarith),
  obtain ⟨ M, hc2 ⟩ := h2 (ε/2) (by linarith),
  use (max N M),
  intros p hp q hq,
  rw [hceq, pre_ecart],
  simp,
  calc
    d (d (x p) (y p)) (d (x q) (y q)) ≤ d (x p) (x q) + d (y p) (y q) : dist_ineg_utile _ _ _ _
    ... < ε/2 + d (y p) (y q) : add_lt_add_right (hc1 p (le_of_max_le_left hp) q (le_of_max_le_left hq)) _
    ... < ε/2 + ε/2 : add_lt_add_left (hc2 p (le_of_max_le_right hp) q (le_of_max_le_right hq)) _
    ... = ε : by simp,
 end

 lemma pre_ecart.triangle (x y z: ℕ → X):
  ∀ n, pre_ecart x z n ≤ pre_ecart x y n + pre_ecart y z n := begin
  intro n,
  rw pre_ecart,
  rw pre_ecart,
  rw pre_ecart,
  simp,
  exact espace_metrique.triangle _ _ _,
end

def cauchy.limit (x: ℕ → ℝ) (H: cauchy x): ℝ := classical.some (R_is_complete x H)
lemma cauchy.converge_of_limit (x: ℕ → ℝ) (H: cauchy x): converge x (cauchy.limit x H) := 
  classical.some_spec (R_is_complete x H)

lemma cauchy.limit_ge_of_seq_ge (x: ℕ → ℝ) (H: cauchy x) (a: ℝ): (∀ n, x n ≥ a) → (cauchy.limit x H) ≥ a :=
begin
intro Hineq,
set l := cauchy.limit x H with hl,
by_contra hla,
push_neg at hla,
set ε := a - l with hε,
obtain ⟨ N, hcv ⟩ := cauchy.converge_of_limit x H (ε/2) (by linarith),
rw ← hl at hcv,
have hcv_N: (x N) - l < ε/2 := by calc
    (x N) - l ≤ abs ((x N) - l) : le_abs_self _
    ... = abs (l - (x N)) : abs_sub _ _
    ... < ε/2 : hcv N (by simp),
have Hineq_N: (x N) ≥ l + ε := by calc
    (x N) ≥ a : Hineq _
    ... = l + ε : by linarith,
  linarith,
end

lemma cauchy.limit_le_of_seq_le (x: ℕ → ℝ) (H: cauchy x) (a: ℝ): (∀ n, x n ≤ a) → (cauchy.limit x H) ≤ a :=
begin
intro Hineq,
set l := cauchy.limit x H with hl,
by_contra hla,
push_neg at hla,
set ε := l - a with hε,
obtain ⟨ N, hcv ⟩ := cauchy.converge_of_limit x H (ε/2) (by linarith),
rw ← hl at hcv,
have hcv_N: l - (x N) < ε/2 := by calc
    l - (x N) ≤ abs (l - (x N)) : le_abs_self _
    ... < ε/2 : hcv N (by simp),
have Hineq_N: (x N) ≤ l - ε := by calc
  (x N) ≤ a : Hineq _
  ... = l - ε: by linarith,
  linarith,
end

lemma cauchy.cauchy_of_add {x y: ℕ → ℝ} (Hx: cauchy x) (Hy: cauchy y): cauchy (x + y) := begin
  intros ε hε,
  obtain ⟨ N, hX ⟩ := Hx (ε/2) (by linarith),
  obtain ⟨ M, hY ⟩ := Hy (ε/2) (by linarith),
  use (max N M),
  intros p hNMp q hNMq,
  rw real.dist_eq,
  calc
    abs ((x + y) p - (x + y) q) = abs ((x p + y p) - (x q + y q)) : by simp
    ... = abs (x p - x q + (y p - y q)) : by rw add_sub_comm _ _ _ _
    ... ≤ abs (x p - x q) + abs (y p - y q) : abs_add _ _
    ... = d (x p) (x q) + d (y p) (y q) : by rw [← real.dist_eq (x p) (x q), ← real.dist_eq (y p) (y q)]
    ... < ε/2 + ε/2 : 
      add_lt_add (hX p (le_of_max_le_left hNMp) q (le_of_max_le_left hNMq)) (hY p (le_of_max_le_right hNMp) q (le_of_max_le_right hNMq))
    ... = ε : by simp,
end

lemma cauchy.cauchy_of_neg {x: ℕ → ℝ} (Hx: cauchy x):
  cauchy (-x) := begin
  intros ε hε,
  obtain ⟨ N, hN ⟩ := Hx ε hε,
  use N,
  intros p hp q hq,
  rw real.dist_eq,
  simp,
  rw ← real.dist_eq,
  rw espace_metrique.sym _ _,
  exact hN p hp q hq,
end

lemma cauchy.cauchy_of_sub {x y: ℕ → ℝ} (Hx: cauchy x) (Hy: cauchy y): cauchy (x - y) := begin
  rw sub_eq_add_neg,
  apply cauchy.cauchy_of_add,
  exact Hx,
  exact cauchy.cauchy_of_neg Hy,
end

@[simp]
lemma cauchy.limit_add_eq_add_limit {x y: ℕ → ℝ} (Hx: cauchy x) (Hy: cauchy y):
  cauchy.limit (x + y) (cauchy.cauchy_of_add Hx Hy) = cauchy.limit x Hx + cauchy.limit y Hy := begin
  apply unicite_limite (x + y),
  exact cauchy.converge_of_limit _ _,
  apply add_converge_add,
  split,
  repeat {exact cauchy.converge_of_limit _ _},
end

@[simp]
lemma cauchy.limit_neg_eq_neg_limit {x: ℕ → ℝ} (Hx: cauchy x): cauchy.limit (-x) (cauchy.cauchy_of_neg Hx) = - cauchy.limit x Hx :=
begin
  apply unicite_limite (-x),
  exact cauchy.converge_of_limit _ _,
  apply neg_converge,
  exact cauchy.converge_of_limit _ _,
end

lemma cauchy.limit_sub_eq_sub_limit (x y: ℕ → ℝ) (Hx: cauchy x) (Hy: cauchy y):
  cauchy.limit (x - y) (cauchy.cauchy_of_sub Hx Hy) = cauchy.limit x Hx - cauchy.limit y Hy := begin
  conv {
    congr,
    congr,
    rw sub_eq_add_neg x y,
    skip,
    skip,
  },
  rw cauchy.limit_add_eq_add_limit Hx (cauchy.cauchy_of_neg Hy),
  rw cauchy.limit_neg_eq_neg_limit Hy,
  rw sub_eq_add_neg,
end

lemma cauchy.limit_le_of_limit_le {x y: ℕ → ℝ} (Hx: cauchy x) (Hy: cauchy y):
  (∀ n: ℕ, x n ≤ y n) → (cauchy.limit x Hx) ≤ (cauchy.limit y Hy) := begin
  intro Hc,
  rw ← sub_nonpos,
  rw ← cauchy.limit_sub_eq_sub_limit,
  apply cauchy.limit_le_of_seq_le,
  simp,
  exact Hc,
end

lemma cauchy.limit_le_of_add_seq_le {x y z: ℕ → ℝ} (Hx: cauchy x) (Hy: cauchy y) (Hz: cauchy z):
  (∀ n: ℕ, x n ≤ y n + z n) → (cauchy.limit x Hx) ≤ (cauchy.limit y Hy) + (cauchy.limit z Hz) := begin
  intro Hc,
  rw ← cauchy.limit_add_eq_add_limit Hy Hz,
  apply cauchy.limit_le_of_limit_le,
  exact Hc,
end

lemma cauchy.cauchy_of_constant_real_seq (c: ℝ): cauchy (λ n, c) := begin
intros ε hε,
simp,
use 0,
intros p hq q hp,
rw espace_metrique.presep,
exact hε,
refl,
end

lemma cauchy.converge_of_constant (c: ℝ): converge (λ x, c) c := begin
intros ε hε,
use 0,
intros n hn,
simp,
rw espace_metrique.presep,
exact hε,
refl,
end

lemma cauchy.constant_limit (c: ℝ): cauchy.limit (λ x, c) (cauchy.cauchy_of_constant_real_seq c) = c := begin
apply unicite_limite (λ x, c),
exact cauchy.converge_of_limit _ _,
exact cauchy.converge_of_constant _,
end

lemma cauchy.pre_ecart_sym (x y: ℕ → X): pre_ecart x y = pre_ecart y x := begin
rw pre_ecart,
rw pre_ecart,
ext,
exact espace_metrique.sym _ _,
end

end suites