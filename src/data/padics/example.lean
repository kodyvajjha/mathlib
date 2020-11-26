<<<<<<< HEAD
import data.padics.padic_norm tactic.tidy
import data.padics.padic_integers

open rat nat lattice list padic_val_rat padic_norm multiplicity int tactic finset
=======
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
open rat nat lattice list padic_val_rat multiplicity int tactic
>>>>>>> 3781df41d... feat(padics/example.lean):Add a few lemmas about 2-adic valuations.

section harmonic

variable [prime_two : nat.prime 2]
include prime_two

local infix ` /. `:70 := mk

variable x:ℚ

def harmonic_number : ℕ → ℚ
| 0 := 0
<<<<<<< HEAD
| (succ n) := (harmonic_number n) + 1 /. (n+1)

def harmonic_number' : ℤ → ℚ
| -[1+ n]  := 0
| 0        := 0
| (succ n) := (harmonic_number n) + 1 /. (n+1)

def pow_two_near {n : ℤ} (hn : n > 1) : ∃ k : ℕ, (2 ^ k ≤ n ∧ n < 2^(k+1)) := (exists_nat_pow_near hn one_lt_two)

/- TODO: Generalize and move. -/
lemma to_nat_succ_of_nonneg {n : ℤ} (hn : n > 1) : to_nat (succ n) = succ n.to_nat :=
begin
  rw ←int.coe_nat_eq_coe_nat_iff, rw int.coe_nat_succ,
  rw to_nat_of_nonneg, rw to_nat_of_nonneg, refl, linarith,
  refine int.le_of_lt _,
  suffices : n > 0,
  refine lt_trans this (lt_succ _),
  exact lt_trans (zero_lt_one) hn,
end

lemma harmonic_num_eq_finset_sum (n : ℕ) : harmonic_number n  = sum (range (succ n)) (λ i, 1 /. i) :=
begin
  induction n with k ih, refl,
  rw [harmonic_number, finset.sum_range_succ, ih, add_comm], refl,
end

lemma harmonic_num_eq_add {n : ℤ} (hn : n > 1) : ∃ k : ℕ, (2^k ≤ n ∧ n < 2^(k+1)) ∧  harmonic_number n.to_nat = sum (erase (range (succ n.to_nat)) (2^k)) (λ i, 1/.i) + 1/. ↑(2^k) :=
begin
  have := pow_two_near hn,
  choose k hk using this,
  existsi k, refine ⟨hk,_⟩, rw add_comm,
  rw harmonic_num_eq_finset_sum,
  have h₁ : 2^k ∉ erase (range (succ n.to_nat)) (2^k), by exact not_mem_erase _ _,
  have h₂ : finset.sum (erase (range (succ n.to_nat)) (2^k)) (λ i, 1 /. i) + 1/. ↑(2^k)  = finset.sum (insert (2^k) (erase (range (succ n.to_nat)) (2^k))) (λ i, 1 /. i), by rw [finset.sum_insert h₁, add_comm],
  rw add_comm, rw h₂, rw insert_erase, rw finset.mem_range,
  refine lt_of_le_of_lt _ _, exact n.to_nat,
  rw ←coe_nat_le_coe_nat_iff, simp, rw to_nat_of_nonneg (int.le_of_lt (lt_trans zero_lt_one hn)), exact hk.1,
  exact nat.lt_succ_self _,
end


=======
| 1 := 1
| (succ n) := (harmonic_number n) + 1 /. (n+1)

>>>>>>> 3781df41d... feat(padics/example.lean):Add a few lemmas about 2-adic valuations.
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
<<<<<<< HEAD
  rwa int.coe_nat_dvd at this,
end

lemma nin_int_of_denom_even {x : ℚ} (hx : 2 ∣ x.denom) : x.denom ≠ 1 :=
begin
  assume h, rw h at hx,
  have := prime.not_dvd_one prime_two, exact this hx,
=======
  rw int.coe_nat_dvd at this, assumption,
>>>>>>> 3781df41d... feat(padics/example.lean):Add a few lemmas about 2-adic valuations.
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

<<<<<<< HEAD
lemma pow_eq_iff_eq (n m : ℤ) {p : ℚ} (hp : p ≠ 0): n = m ↔ p^n = p^m :=
begin
fsplit, intro eq, rw eq,
intro eq,
=======

def pow_two_near (n : ℤ) : (n > 1) → ∃ k : ℕ, (2 ^ k ≤ n ∧ n < 2^(k+1)) :=
by intro h ; exact (exists_nat_pow_near h one_lt_two)

#check eq_neg_iff_eq_neg
#check _root_.pow_two
#check pow_eq_mul_pow_sub
#check pow_eq_mul_pow_sub
lemma pow_eq_of_eq (n m : ℕ) (p : ℚ): n = m ↔ p^n = p^m :=
begin
fsplit, intro eq, rw eq,
contrapose, intro eq,
>>>>>>> 3781df41d... feat(padics/example.lean):Add a few lemmas about 2-adic valuations.
sorry,
end

lemma two_val_add_eq_min {q r : ℚ} (hne : padic_val_rat 2 q ≠ padic_val_rat 2 r) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
  padic_val_rat 2 (q + r) = min (padic_val_rat 2 q) (padic_val_rat 2 r) :=
<<<<<<< HEAD
have h₁ : padic_norm 2 q ≠ padic_norm 2 r, {
  simp [padic_norm, hq, hr], assume not,
  rw ←pow_eq_iff_eq at not, rw eq_neg_iff_eq_neg at not, rw _root_.neg_neg at not, exact hne not.symm, norm_num,
},
begin
  have := @add_eq_max_of_ne 2 _ q r h₁,
  simp [padic_norm, hq, hr, hqr] at this,
  rw min_eq_neg_max_neg_neg,
  rw eq_neg_iff_eq_neg, rw @pow_eq_iff_eq _ _ _ 2, rw this,
  by_cases (-padic_val_rat 2 q ≤ -padic_val_rat 2 r),
    simp [h], have := @fpow_le_of_le ℚ _ 2 (le_of_lt one_lt_two) _ _ h,
    simp [this],
    rw not_le at h, replace := int.le_of_lt h, have g := @fpow_le_of_le ℚ _ 2 (le_of_lt one_lt_two) _ _ this,
    simp [g], rw ←not_le at h, simp [max,h], norm_num,
end


lemma two_val_add_lt_of_two_val_lt {q r : ℚ}  (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) (a : ℤ) (qlt : a < padic_val_rat 2 q) (plt : a < padic_val_rat 2 r ) : a < padic_val_rat 2 (q+r) := lt_of_lt_of_le (lt_min qlt plt) (min_le_padic_val_rat_add 2 hq hr hqr)


lemma two_val_finset_sum_lt {s : finset ℕ} {k : ℕ} (hk : 0 < k) (hp : ∀ i:ℕ, i ∈ s → padic_val_rat 2 (1 /. 2^k) < padic_val_rat 2 (1 /. i)) : padic_val_rat 2 (1 /. 2^k) < padic_val_rat 2 (finset.sum s (λ i, 1/.i)) :=
begin
apply finset.induction_on s,
simp, rw two_val_rec_pow_two, simpa [padic_val_rat,neg_lt],
intros a s ha ih, rw sum_insert ha, refine two_val_add_lt_of_two_val_lt _ _ _ _ _ ih,
end

lemma two_val_of_summand {n : ℤ} (hn : n > 1) : ∃ k : ℕ, (2^k ≤ n ∧ n < 2^(k+1)) ∧
(
  ∀ i ∈ erase (range (succ n).to_nat) (2^k) , padic_val_rat 2 (1 /. 2^k) < padic_val_rat 2 (1 /. i)
  →
  padic_val_rat 2 (1 /. 2^k) < padic_val_rat 2 (sum (erase (range (succ n.to_nat)) (2^k)) (λ i, 1/.i))
) :=
begin
  have := pow_two_near hn,
  choose k hk using this,
  existsi k, refine ⟨hk,_⟩,
  assume i hmem hval, rw mem_erase at hmem, rw finset.mem_range at hmem, rw to_nat_succ_of_nonneg hn at hmem,
  simp [two_val_rec_pow_two] at *,

end


#check padic_val_rat.inv
#check le_padic_val_rat_add_of_le
#check multiplicity
#check enat.coe_get
#check enat.coe_le_coe
#check dvd_trans
#check ne_from_not_eq
#check not_not
#check mul_nonneg
#check mul_lt_iff_lt_one_right
#check mul_lt_iff_lt_one_right
#check mul_lt_mul_left
#check nat.pow_pos
#check @mul_lt_mul_of_pos_left
#check mul_lt_mul_right
#check nat.cast_lt
#check not_le
#check lt_irrefl
#check _root_.pow_pos
#check ne_iff_lt_or_gt
#check int.le_refl
#check le_iff_eq_or_lt
#check int.cast_eq_zero
#check rat.cast_eq_zero
#check int.lt_iff_add_one_le
-- #check int.pow_dvd_of_le_of_pow_dvd

lemma two_val_harmonic_neg {n : ℤ} (hn : n > 1) : padic_val_rat 2 (harmonic_number n.to_nat) < 0 :=
begin
have := pow_two_near hn,
choose r hr using this,
have zero_lt_two : 0 < (2 : ℤ), by norm_num,
have := _root_.pow_pos (zero_lt_two) r, clear zero_lt_two,
have h : ∀ m:ℤ, (m ≠ 2^r) → (0 < m ∧ m < n) → padic_val_rat 2 m < r,
{
  intros m hm hmn,
  by_contra, rw not_lt at a,
  rw padic_val_rat at a,split_ifs at a, simp at a, rw ←enat.coe_le_coe at a, rw enat.coe_get at a,
  rw ← pow_dvd_iff_le_multiplicity at a,
  choose c hc using a,
  have cnoneg : c ≥ 0,
  {
    by_contra, rw not_le at a,
    rw ←mul_lt_mul_left this at a, simp at a, rw ←hc at a,
    exact lt_irrefl _ (lt_trans (hmn.1) a),
  },
  have cnez : c ≠ 0,
  {
    by_contra, rw ne_from_not_eq at a, rw not_not at a, rw a at hc, rw mul_zero at hc, exact h.1 (int.cast_eq_zero.2 hc),
  },
  have cne : c ≠ 1,
  {
    by_contra, rw ne_from_not_eq at a, rw not_not at a, rw a at hc, rw mul_one at hc, exact hm hc,
  },
  have cnetwo : c ≥ 2,
  {
    by_contra, rw not_le at a,
    have := le_of_lt_add_one a, clear a, rw le_iff_eq_or_lt at this,
    cases this with l r, exact cne l,
    have := le_sub_one_of_lt r, simp at this, rw le_iff_eq_or_lt at this, cases this with l₁ r₁, exact cnez l₁, linarith,
  },
  have hmle :  2^(r+1) ≤ m,
  {
    rw _root_.pow_succ, rw hc, rw mul_comm,
    refine mul_le_mul_of_nonneg_left cnetwo (int.le_of_lt _),
    refine _root_.pow_pos _ r,
    norm_num,
  },
  exact lt_irrefl _ (lt_trans (lt_of_le_of_lt hmle hmn.2) hr.2),
  simp at h,
  suffices : 2 ≠ 1, apply this, apply h, exact ne_of_gt hmn.1,
  norm_num,
},
clear this,
have :  ∀ (m : ℤ), m ≠ 2 ^ r → 0 < m ∧ m < n → -padic_val_rat 2 (1 /. m) < -padic_val_rat 2 (1 /. 2^r),
{
  intros m hm hmn,
  convert h m hm hmn,
  rw [←inv_def,←coe_int_eq_mk, padic_val_rat.inv, _root_.neg_neg],
  swap, rw two_val_rec_pow_two, rw _root_.neg_neg, assume not,
  rw int.cast_eq_zero at not, rw not at hmn,
  exact lt_irrefl _ hmn.1,
},
simp only [neg_lt_neg_iff] at this,
sorry,
end



=======
begin
have pqr : padic_norm 2 (q + r) = 2^(-padic_val_rat 2 (q+r)), by simp [hqr],
have pr : padic_norm 2 (r) = 2^(-padic_val_rat 2 (r)), by simp [hr],
have pq : padic_norm 2 (q) = 2^(-padic_val_rat 2 (q)), by simp [hq],
rw min_eq_neg_max_neg_neg, rw eq_neg_iff_eq_neg,
sorry,
end

>>>>>>> 3781df41d... feat(padics/example.lean):Add a few lemmas about 2-adic valuations.
end harmonic
