import solutions.world1_addition -- addition lemmas

import mynat.mul
/- Here's what you get from the import:

1) The following data:
  * a function called mynat.mul, and notation a * b for this function

2) The following axioms:

  * `mul_zero : ∀ a : mynat, a * 0 = 0`
  * `mul_succ : ∀ a b : mynat, a * succ(b) = a * b + a`

These axiom between them tell you how to work out a * x for every x; use induction on x to
reduce to the case either `x = 0` or `x = succ b`, and then use `mul_zero` or `mul_succ` appropriately.
-/

namespace mynat

--MULTIPLICATION WORLD

--Level 1 :
lemma zero_mul (m : mynat) : 0 * m = 0 :=
begin [nat_num_game]
  -- On fait une induction sur m :
  induction m with d hd,

  -- Le cas de base :
  rw mul_zero,
  refl,

  -- Le cas d'induction :
  rw mul_succ,
  rw add_zero,
  rw hd,
  refl,
end

--Level 2 :
lemma mul_one (m : mynat) : m * 1 = m :=
begin [nat_num_game]
  -- On fait une induction sur m :
  induction m with d hd,

  -- Le cas de base :
  rw zero_mul,
  refl,

  -- Le cas d'induction :
  rw one_eq_succ_zero,
  rw mul_succ,
  rw mul_zero,
  rw zero_add,
  refl,
end

--Level 3 :
lemma one_mul (m : mynat) : 1 * m = m :=
begin [nat_num_game]
  -- On fait une induction sur m :
  induction m with d hd,
  
  -- Le cas de base :
  rw mul_zero,
  refl,

  -- Le cas d'induction :
  rw mul_succ,
  rw hd,
  rw succ_eq_add_one,
  refl,
end

-- mul_assoc immediately, leads to this:
-- ⊢ a * (b * d) + a * b = a * (b * d + b)

-- so let's prove mul_add first.

--Level 4 :
lemma mul_add (a b c : mynat) : a * (b + c) = a * b + a * c :=
begin [nat_num_game]
  -- On fait une induction sur b :
  induction c with d hd,

  -- Le cas de base :
  refl,

  -- Le cas d'induction :  
  rw mul_succ,
  rw ← add_assoc,
  rw ← hd,
  rw add_succ,
  rw mul_succ,
  refl,
end

-- just ignore this
def left_distrib := mul_add -- stupid field name, 
-- I just don't instinctively know what left_distrib means

--Level 5 :
lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) :=
begin [nat_num_game]
  -- On fait une induction sur c :
  induction c with d hd,

  -- Le cas de base :
  repeat {rw mul_zero},

  -- Le cas d'induction :
  repeat {rw mul_succ},
  rw mul_add,
  rw hd,
  refl,
end

-- goal : mul_comm. 
-- mul_comm leads to ⊢ a * d + a = succ d * a
-- so perhaps we need add_mul
-- but add_mul leads to either a+b+c=a+c+b or (a+b)+(c+d)=(a+c)+(b+d)
-- (depending on whether we do induction on b or c)

-- I need this for mul_comm
--Level 6 :
lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin [nat_num_game]
-- Attention, ne pas oublier de taper 'espace' après les '\l' !!!
  -- On fait une induction sur b :
  induction b with d hd,

  -- Le cas de base :
  refl,

  -- Le cas d'induction :
  rw succ_eq_add_one d,
  rw mul_add,
  rw hd,
  rw succ_eq_add_one,
  rw mul_add,
  repeat {rw mul_one},
  repeat {rw ← add_assoc},
  rw add_assoc,
  rw add_assoc  (a * d) (d) (a + 1),
  rw add_comm d _,
  rw add_right_comm,
  rw ← add_assoc (a*d) (a+d) 1,
  rw ← add_assoc (a*d) a d,
  refl,
end

--Level 7 :
lemma add_mul (a b c : mynat) : (a + b) * c = a * c + b * c :=
begin [nat_num_game]
  -- On fait une induction sur t :
  induction c with d hd,

  -- Le cas de base :
  refl,

  -- Le cas d'induction :  
  repeat {rw mul_succ},
  rw hd,
  rw ← add_assoc,
  rw ← add_assoc (a*d +a) _ _,
  rw add_assoc (a*d) a _,
  rw add_comm a (b*d),
  rw ← add_assoc,
  refl,
end

-- ignore this
def right_distrib := add_mul -- stupid field name, 

--Level 8 :
lemma mul_comm (a b : mynat) : a * b = b * a :=
begin [nat_num_game]
  -- On fait une induction sur b :
  induction b with d hd,

  -- Le cas de base :
  rw zero_mul,
  rw mul_zero,
  refl,

  -- Le cas d'induction :  
  rw mul_succ,
  rw succ_mul,
  rw hd,
  refl,
end

--Level 9 :
lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin [nat_num_game]
  -- On met tout dans le bon ordre
  rw ← mul_assoc,
  rw mul_comm a b,
  rw mul_assoc,
  refl,
end


--ADVANCED MULTIPLICATION WORLD

--Level 1 :
theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin [nat_num_game]
  intros ha hb hab,
  apply ha,

  --On divise le goal en 2 cas :
  cases b with n,
  
  --Le cas 'b = 0' :
  exfalso,
  apply hb,
  refl,

  --Le cas 'b = succ n' :
  rw mul_succ at hab,
  rw add_left_eq_zero hab,
  refl,
end

--Level 2 :
theorem eq_zero_or_eq_zero_of_mul_eq_zero ⦃a b : mynat⦄ (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin [nat_num_game]
  --On fait une distintion de cas sur b :
  cases b with n,

  --Cas 'b = 0' :
  right,
  refl,

  --Cas 'b = succ n' :
  rw mul_succ at h,   --Pas strictement nécessaire car les notations sont égales par définition.
  left,
  apply add_left_eq_zero h,
end

--Level 3 :
theorem mul_eq_zero_iff : ∀ (a b : mynat), a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin [nat_num_game]
  intros a b,
  --On divise le goal en 2 implications :
  split,

  --Sens → 
  intro h,
  exact eq_zero_or_eq_zero_of_mul_eq_zero h,

  --Sens ← 
  intro h,
  cases h with g h,
  rw g,
  rw zero_mul,
  refl,
  rw h,
  rw mul_zero,
  refl,
end

instance : comm_semiring mynat := by structure_helper

--Level 4 :
theorem mul_left_cancel ⦃a b c : mynat⦄ (ha : a ≠ 0) : a * b = a * c → b = c :=
begin [nat_num_game]
-- Attention, ne pas oublier de taper 'espace' après les '\or' et '\ne'!!!
  revert b,
  -- On fait une induction sur c :
  induction c with n hn,

  --Le cas de base :
  rw mul_zero,
  intros b h,
  rw mul_eq_zero_iff a b at h,
  --On casse le ∨ :
  cases h with hha hhb,
  --Si 'a = 0' :
  exfalso,
  apply ha,
  exact hha,
  --Si 'b = 0' :
  exact hhb,

  --Le cas d'induction :
  intros b h,
  --On fait une distinction de cas sur b :
  cases b with c,

  --Cas 'b = 0' :
  rw mul_zero at h,
  exfalso,
  apply mul_pos a (succ n), --On a besoin de démontrer les hypothèses de mul_pos :
  --Hypothèse 'a ≠ 0' :
  exact ha,
  --Hypothèse 'succ n ≠ 0' :
  intro hnn,
  exact succ_ne_zero hnn,
  --Retour à la preuve par l'absurde :
  symmetry,
  exact h,

  --Cas 'b = succ c' :
  repeat {rw succ_eq_add_one},
  rw add_right_cancel_iff,
  apply hn,
  repeat {rw mul_succ at h},
  rw add_right_cancel_iff at h,
  exact h,
end

end mynat
