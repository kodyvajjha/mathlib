-- import algebra.field
import data.nat.modeq order.lattice
import tactic.tidy
import algebra.archimedean
import data.padics.padic_norm
import data.padics.padic_integers
import data.nat.prime
import data.zmod.basic
import tactic.library_search
import set_theory.cardinal
import tactic.find
import order.conditionally_complete_lattice
open rat nat lattice list padic_val_rat padic_norm multiplicity int tactic

section harmonic

variable [prime_two : nat.prime 2]
include prime_two

local infix ` /. `:70 := mk

variable x:ℚ

def harmonic_number : ℕ → ℚ
| 0 := 0
| 1 := 1
| (succ n) := (harmonic_number n) + 1 /. (n+1)

@[simp] lemma finite_two (q : ℕ) (hq : q ≠ 0) : finite 2 q :=
begin
  apply (@finite_nat_iff 2 q).2,
  split, exact (prime.ne_one prime_two),
  apply nat.pos_of_ne_zero, assumption
end

lemma two_val_neg_denom_even (x : ℚ) : (x ≠ 0) → (padic_val_rat 2 x < 0) → 2 ∣ x.denom :=
begin
  intros h₁ h₂,
  rw padic_val_rat_def _ h₁ at h₂, swap, exact prime_two,
  rw [sub_lt_zero] at h₂,
  have := lt_of_le_of_lt (int.coe_nat_nonneg _) h₂,
  have := int.coe_nat_pos.1 this,
  rw [←enat.coe_lt_coe,enat.coe_get] at this,
  replace := dvd_of_multiplicity_pos this,
  rw int.coe_nat_dvd at this, assumption,
end

lemma two_val_rec_pow_two (r : ℕ) : padic_val_rat 2 (1 /. (2^r)) = -r :=
begin
  rw [←inv_def,←coe_int_eq_mk], simp,
  rw padic_val_rat.inv,
  {
    rw padic_val_rat.pow,
    have h : padic_val_rat 2 2 = padic_val_rat 2 ↑2, by refl,
    rw h,
    rw padic_val_rat_self one_lt_two,
    simp, exact two_ne_zero,
  },
  apply pow_ne_zero, exact two_ne_zero,
end


def pow_two_near (n : ℤ) : (n > 1) → ∃ k : ℕ, (2 ^ k ≤ n ∧ n < 2^(k+1)) :=
by intro h ; exact (exists_nat_pow_near h one_lt_two)

#check eq_neg_iff_eq_neg
#check _root_.pow_two
#check pow_eq_mul_pow_sub
#check pow_eq_mul_pow_sub

#check pow_ne_zero

lemma pow_eq_iff_eq (n m : ℤ) (p : ℚ) (hp : p ≠ 0): n = m ↔ p^n = p^m :=
begin
fsplit, intro eq, rw eq,
intro eq,
suffices h : m = (m - n) + n, rw h at eq,

end


#check eq_inv_mul_iff_mul_eq
#check _root_.pow_add
-- lemma val_of_sum_eq_of_lt {q r : ℚ} (hqr : padic_val_rat 2 q < padic_val_rat 2 r) : (padic_val_rat 2 (q+r)) = (padic_val_rat 2 r) :=
-- begin
-- have : padic_val_rat 2 q ≤ max (padic_val_rat 2 (q + r)) (padic_val_rat 2 r),

-- end
#check @fpow_le_of_le
#check pow_eq_iff_eq
#check inv_mul_eq_iff_eq_mul
#check pow_mul
#check pow_eq_pow
#check pow_le_pow
#check fpow
#check pow_eq_mul_pow_sub
#check pow_le_max_of_min_le
#check padic_val_rat_le_padic_val_rat_iff
#check min_le_padic_val_rat_add
#check ne_iff_lt_or_gt
#check eq_of_neg_eq_neg
#check eq_neg_iff_eq_neg
#check add_eq_max_of_ne
-- #check padic_val_rat

lemma two_val_add_eq_min {q r : ℚ} (hne : padic_val_rat 2 q ≠ padic_val_rat 2 r) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
  padic_val_rat 2 (q + r) = min (padic_val_rat 2 q) (padic_val_rat 2 r) :=
have h₁ : padic_norm 2 q ≠ padic_norm 2 r, {
  simp [padic_norm, hq, hr], assume not,
  rw ←pow_eq_iff_eq at not, rw eq_neg_iff_eq_neg at not, rw _root_.neg_neg at not, exact hne not.symm, norm_num,
},
begin
have := @add_eq_max_of_ne 2 _ q r h₁,
simp [padic_norm, hq, hr, hqr] at this,
rw min_eq_neg_max_neg_neg,
rw eq_neg_iff_eq_neg, rw pow_eq_iff_eq _ _ 2, rw this,
by_cases (-padic_val_rat 2 q ≤ -padic_val_rat 2 r),
  simp [h], have := @fpow_le_of_le ℚ _ 2 (le_of_lt one_lt_two) _ _ h,
  simp [this],
  rw not_le at h, replace := int.le_of_lt h, have g := @fpow_le_of_le ℚ _ 2 (le_of_lt one_lt_two) _ _ this,
  simp [g], rw ←not_le at h, simp [max,h], norm_num,
end

end harmonic
