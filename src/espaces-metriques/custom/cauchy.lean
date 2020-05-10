import .defs
import .sequences

open espace_metrique
open_locale classical

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
rw espace_metrique.sym l2 (x p₂) at hl₂,
have Tr := espace_metrique.triangle (x p₁) (x p₂) l2,
have Hc:= h_cauchy p₁ hp₁ p₂ hp₂,
calc
  d l1 l2 ≤ d l1 (x p₁) + d (x p₁) l2 : espace_metrique.triangle _ _ _
    ... < ε/3 + d (x p₁) l2 :  add_lt_add_right hl₁ (d (x p₁) l2)
    ... ≤ ε/3 + (d (x p₁) (x p₂) + d (x p₂) l2) : add_le_add_left Tr (ε/3)
    ... = d (x p₁) (x p₂) + (ε / 3 + d (x p₂) l2) : by ring 
    ... < ε/3 + (ε/3 + d (x p₂) l2) : add_lt_add_right Hc (ε / 3 + d (x p₂) l2)
    ... = ε/3 + ε/3 + d (x p₂) l2 : by ring
    ... < ε/3 + ε/3 + ε/3 :  add_lt_add_left hl₂ (ε/3 + ε/3)
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

end suites