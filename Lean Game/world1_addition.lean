import mynat.definition -- Imports the natural numbers.

/- Here's what you get from the import:

1) The following data:
  * a type called `mynat`
  * a term `0 : mynat`, interpreted as the number zero.
  * a function `succ : mynat → mynat`, with `succ n` interpreted as "the number after n".
  * Usual numerical notation 0,1,2,3,4,5 etc.

2) The following axioms:
  * `zero_ne_succ : ∀ (a : mynat), zero ≠ succ(a)`, the statement that zero isn't a successor.
  -- this ensures that there is more than one natural number.
  * `succ_inj : ∀ {a b : mynat}, succ(a) = succ(b) → a = b`, the statement that
     if succ(a) = succ(b) then a = b.
  -- this ensures that there are infinitely many natural numbers.

3) The principle of mathematical induction.

  * In practice this means that if you have `n : mynat` then you can use the tactic `induction n`.

4) A few useful extra things:

  * The theorem `one_eq_succ_zero : 1 = succ 0`
  * The theorem `ne_iff_implies_false : a ≠ b ↔ (a = b) → false`

-/

import mynat.add -- definition of addition

/- Here's what you get from the import:

1) The following data:
  * a function called mynat.add, and notation a + b for this function

2) The following axioms:

  * `add_zero : ∀ a : mynat, a + 0 = a`
  * `add_succ : ∀ a b : mynat, a + succ(b) = succ(a + b)`

These axiom between them tell you how to work out a + x for every x; use induction on x to
reduce to the case either `x = 0` or `x = succ b`, and then use `add_zero` or `add_succ` appropriately.
-/

namespace mynat

-- Summary:

-- Naturals:
-- 1) 0 and succ are constants
-- 2) succ_inj and zero_ne_succ are axioms
-- 3) Induction works.

-- Addition:
-- 1) add_zero and add_succ are the axioms
-- 2) notation is a + b

/-
 Collectibles in this level:

add_comm_monoid -- collectible_02
  add_monoid [zero_add] -- collectible_01
    (has_zero)
    add_semigroup [add_assoc]
      (has_add)
  add_comm_semigroup [add_comm]
    add_semigroup (see above)
-/


-- ADDITION WORLD

--Level 1 :
lemma zero_add (n : mynat) : 0 + n = n :=
begin [nat_num_game]
  -- On fait une induction sur n :
  induction n with d hd,

  -- Le cas de base :
  rw add_zero,
  refl,

  -- Le cas d'induction :
  rw add_succ,
  rw hd,
  refl,
  
end

--Level 2 :
lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) :=
begin [nat_num_game]
  -- On fait une induction sur c :
  induction c with d hd,

  -- Le cas de base :
  rw add_zero,
  rw add_zero,
  refl,

  -- Le cas d'induction :
  rw add_succ,
  rw add_succ,
  rw add_succ,
  rw hd,
  refl,
end

-- first point: needs add_assoc, zero_add, add_zero
def collectible_01 : add_monoid mynat := by structure_helper
--#print axioms collectible_01 -- prove you got this by uncommenting

-- proving add_comm immediately is still tricky; trying it
-- reveals a natural intermediate lemma which we prove first.

--Level 3 :
lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin [nat_num_game]
  -- On fait une induction sur b :
  induction b with n hn,

  -- Le cas de base :
  rw add_zero,
  rw add_zero,
  refl,

  -- Le cas d'induction :
  rw add_succ,
  rw add_succ,
  rw hn,
  refl,
end

--Level 4 :
lemma add_comm (a b : mynat) : a + b = b + a :=
begin [nat_num_game]
  -- On fait une induction sur b :
  induction b with n hn,

  -- Le cas de base :
  rw zero_add,
  rw add_zero,
  refl,

  -- Le cas d'induction :
  rw add_succ,
  rw succ_add,
  rw hn,
  refl,
end

-- level up
def collectible_02 : add_comm_monoid mynat := by structure_helper
--#print axioms collectible_02

-- no more collectibles beyond this point in this file, however
-- stuff below is used in other collectibles in other files.

--Level 5 :
theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin [nat_num_game]
  -- Il suffit d'utiliser l'axiome '1 = succ 0' puis de simplifier :
  rw one_eq_succ_zero,
  rw add_succ,
  rw add_zero,
  refl,
end

--Level 6 :
lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b :=
begin [nat_num_game]
  --Une combinaison d'associativité et de commutativité :
  rw add_assoc,
  rw add_comm b c,
  rw add_assoc,
  refl,
end


-- ADVANCED ADDITION WORLD

--Level 1 :
theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b := 
begin [nat_num_game]
  apply succ_inj,
  exact hs,
end

--Level 2 :
theorem succ_succ_inj {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) :  a = b := 
begin [nat_num_game]
  apply succ_inj,
  apply succ_inj,
  exact h,
end

--Level 3 :
theorem succ_eq_succ_of_eq {a b : mynat} : a = b → succ(a) = succ(b) :=
begin [nat_num_game]
  intro h,
  rw h,
end

-- Level 4 :
theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b :=
begin [nat_num_game]
  split,
 
  -- → 
  exact succ_inj,
 
  -- ← 
  exact succ_eq_succ_of_eq,
end

--Level 5 :
theorem add_right_cancel ⦃a b c : mynat⦄ : a + b = c + b → a = c :=
begin [nat_num_game]
  intro h,

  -- On fait une induction sur t :
  induction b with n hn,

  -- Le cas de base :
  repeat {rw add_zero at h},
  exact h,

  -- Le cas d'induction :
  apply hn,
  repeat {rw add_succ at h},
  apply succ_inj,
  exact h,
end

--Level 6 :
theorem add_left_cancel ⦃ a b c : mynat⦄ : a + b = a + c → b = c :=
begin [nat_num_game]
  --On utilise la commutativité de l'addition pour se ramener au cas précédent :
  rw add_comm,
  rw add_comm a c,
  intro h,
  exact add_right_cancel h,
end

--Level 7 :
theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=
begin [nat_num_game]
  split,

  intro h,
  exact add_right_cancel h,

  cc,
end

-- this is used for antisymmetry of ≤
--Level 8 :
lemma eq_zero_of_add_right_eq_self {{a b : mynat}} : a + b = a → b = 0 :=
begin [nat_num_game]
  intro h,
  exact add_left_cancel h,
end

--Level 9 :
theorem succ_ne_zero : ∀ {{a : mynat}}, succ a ≠ 0 := 
begin [nat_num_game]
  intro a,
  symmetry,
  exact zero_ne_succ a,
end

-- now used for antisymmetry of ≤
--Level 10 :
lemma add_left_eq_zero {{a b : mynat}} : a + b = 0 → b = 0 :=
begin [nat_num_game]
  intro H,
  --On fait une distinction de cas 'b = 0' ou 'b = succ(d)' :
  cases b with d,

  --Cas 'b = 0' :
  refl,

  --Cas 'b = succ(d)' :
  rw add_succ at H,
  exfalso,
  exact succ_ne_zero H,
end

--Level 11 :
lemma add_right_eq_zero {{a b : mynat}} : a + b = 0 → a = 0 :=
begin [nat_num_game]
  intro h,
  rw add_comm at h,
  exact add_left_eq_zero h,
end

--Level 12 :
theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin [nat_num_game]
  symmetry,
  refl,
end

def ne_succ_self (n : mynat) : n ≠ succ n :=
begin [nat_num_game]
  -- On fait une induction sur n :
  induction n with d hd,

  -- Le cas de base :  
  exact zero_ne_succ 0,

  -- Le cas d'induction :
  intro h,
  apply hd,
  apply succ_inj,
  exact h,
end

end mynat