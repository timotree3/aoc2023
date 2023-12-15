import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.AbsoluteValue

theorem Nat.coprime_mod (m n : ℕ) : Coprime (m % n) n ↔ Coprime m n := by
  rw [coprime_iff_gcd_eq_one (m := m), gcd_comm, gcd_rec]

theorem ZMod.dvd_of_val_dvd_val {p : ℕ} [NeZero p] (m n : ZMod p) : m.val ∣ n.val → m ∣ n := by
  intro ⟨k, h⟩
  use k
  rw [← ZMod.nat_cast_zmod_val n, h]
  simp

theorem ZMod.char_ne_one (p : ℕ) [Nontrivial (ZMod p)] : p ≠ 1 := by
  rintro rfl
  exact false_of_nontrivial_of_subsingleton (ZMod 1)

theorem ZMod.char_eq_zero_or_gt_one (p : ℕ) [Nontrivial (ZMod p)] : p = 0 ∨ 1 < p := by
  have := ZMod.char_ne_one p
  rcases p with ⟨⟩|⟨⟩|n <;> simp at this ⊢


@[simp]
theorem ZMod.val_inj {p : ℕ} [NeZero p] (n m : ZMod p) : n.val = m.val ↔ n = m :=
  (ZMod.val_injective p).eq_iff

@[simp]
theorem ZMod.val_one'' (p : ℕ) [Nontrivial (ZMod p)] : (1 : ZMod p).val = 1 := by
  rcases ZMod.char_eq_zero_or_gt_one p with rfl | h
  . exact ZMod.val_one'
  . exact @ZMod.val_one p ⟨h⟩

theorem ZMod.inv_one (p : ℕ) : (1 : ZMod p)⁻¹ = 1 := by
  nth_rewrite 2 [← ZMod.mul_inv_of_unit 1 isUnit_one]
  simp

#eval (9 : ZMod 12)⁻¹

instance ZMod.instInvOneClass (p : ℕ) : InvOneClass (ZMod p) where
  inv_one := ZMod.inv_one p

theorem ZMod.isUnit_inv_of_isUnit {p : ℕ} {n : ZMod p} (h : IsUnit n) : IsUnit n⁻¹ := by
  apply isUnit_of_mul_eq_one n⁻¹ n
  apply ZMod.inv_mul_of_unit
  exact h


theorem ZMod.isUnit_coe_iff_coprime {p n : ℕ} : IsUnit (n : ZMod p) ↔ Nat.Coprime n p := by
  constructor
  . intro ⟨n, h⟩
    rw [← Nat.coprime_mod, ←ZMod.val_nat_cast, ←h]
    exact val_coe_unit_coprime n
  . intro h
    use ZMod.unitOfCoprime n h
    simp

theorem ZMod.val_eq_abs (n : ℤ) : ZMod.val (show ZMod 0 from n) = |n| := by
  match n with
  | Int.ofNat n =>
    simp only [Int.ofNat_eq_coe, Nat.abs_cast, Nat.cast_inj]
    rw [ZMod.val_nat_cast]
    simp
  | Int.negSucc n =>
    rw [Int.negSucc_eq, val_neg', abs_neg, ←Nat.cast_succ,
        Nat.abs_cast, ZMod.val_nat_cast]
    simp

#synth Abs ℤˣ

#synth CommRing (ZMod 0)
#synth CommRing ℤ
#synth Abs ℤ
@[simp]
theorem ZMod_zero_eq_Int : ZMod 0 = ℤ := rfl

@[simp]
theorem ZMod.instCommRing_zero : ZMod.commRing 0 = Int.instCommRingInt := rfl

@[simp]
theorem Int.isUnit_abs {n : ℤ} : IsUnit |n| ↔ IsUnit n := by
  cases' Int.natAbs_eq n with h h
    <;> rw [h]
    <;> simp

theorem ZMod.coprime_val_iff_isUnit {p : ℕ} {n : ZMod p} : Nat.Coprime n.val p ↔ IsUnit n := by
  rw [←ZMod.isUnit_coe_iff_coprime]
  match p with
  | 0 =>
    change ℤ at n
    rw [ZMod.val_eq_abs]
    simp
  | (p + 1) => simp

-- @[simp]
-- theorem ZMod.val_cast_eq_val_of_lt

theorem extracted_1 {m n : ℕ} (hm : ¬m = 0) (h_co : ¬Nat.Coprime m n) : m / gcd m n < m := by
  have mpos := Nat.pos_of_ne_zero hm
  rw [Nat.coprime_iff_gcd_eq_one] at h_co
  suffices 1 < gcd m n from Nat.div_lt_self mpos this
  suffices 0 < gcd m n from Ne.lt_of_le' h_co this
  exact Nat.gcd_pos_of_pos_left n mpos

-- greatest _coprime_ divisor
def gcod (m n : ℕ) : ℕ :=
  if hm : m = 0 then
    1
  else if h_co : Nat.Coprime m n then
    m
  else
    have : m / gcd m n < m := extracted_1 hm h_co
    gcod (m / gcd m n) n

@[simp]
theorem gcod_zero (n : ℕ) : gcod 0 n = 1 := by
  unfold gcod
  simp

theorem gcod_of_coprime {m n : ℕ} (hm : m ≠ 0) (h : Nat.Coprime m n) : gcod m n = m := by
  unfold gcod
  simp [h, hm]

theorem gcod_rec (m n : ℕ) : gcod m n = gcod (m / gcd m n) n := by
  conv => lhs; unfold gcod
  split_ifs with hm h_co
  . subst m
    simp
  . have : gcd m n = 1 := Nat.Coprime.gcd_eq_one (by assumption)
    simp [this, gcod_of_coprime hm h_co]
  . rfl

theorem gcod_dvd (m n : ℕ) : gcod m n ∣ m := by
  unfold gcod
  split_ifs with hm h_co
  . simp
  . simp
  . have : m / gcd m n < m := extracted_1 hm h_co
    have ih := gcod_dvd (m / gcd m n) n
    have : m / gcd m n ∣ m := Nat.div_dvd_of_dvd (gcd_dvd_left m n)
    exact Nat.dvd_trans ih this

theorem gcod_coprime (m n : ℕ) : Nat.Coprime (gcod m n) n := by
  unfold gcod
  split_ifs with hm h_co
  . simp
  . assumption
  . have : m / gcd m n < m := extracted_1 hm h_co
    apply gcod_coprime

theorem gcod_mul_of_coprime {k m n : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) (h_k_co : k.Coprime n) : gcod (k * m) n = k * gcod m n := by
  conv => lhs; unfold gcod
  split_ifs with hkm h_co
  . aesop
  . suffices m.Coprime n by rw [gcod_of_coprime hm this]
    exact Nat.Coprime.coprime_mul_left h_co
  . have h_m_co : ¬Nat.Coprime m n := (Nat.Coprime.mul h_k_co).mt h_co
    have : m / Nat.gcd m n < m := extracted_1 hm h_m_co
    dsimp only
    rw [gcd_eq_nat_gcd, h_k_co.gcd_mul_left_cancel m, Nat.mul_div_assoc k,
        gcod_mul_of_coprime, ← gcd_eq_nat_gcd, ← gcod_rec]
    . rw [← Nat.pos_iff_ne_zero]
      apply Nat.div_pos
      . apply Nat.gcd_le_left
        exact Nat.pos_of_ne_zero hm
      . apply Nat.gcd_pos_of_pos_left
        exact Nat.pos_of_ne_zero hm
    . exact hk
    . exact h_k_co
    . exact Nat.gcd_dvd_left m n

theorem dvd_gcod_of_dvd_of_coprime {k m n : ℕ} (hm : m ≠ 0) (h_dvd : k ∣ m) (h_co : k.Coprime n) : k ∣ gcod m n := by
  obtain ⟨m_div_k, rfl⟩ := h_dvd
  rw [gcod_mul_of_coprime] <;> aesop

theorem gcod_pos (m n : ℕ) : 0 < gcod m n := by
  unfold gcod
  split_ifs with hm h_co
  . simp
  . exact Nat.pos_of_ne_zero hm
  . have := extracted_1 hm h_co
    apply gcod_pos

lemma foo {p q n : ℕ} (h : p.Coprime n) (hpq: p ∣ q) : Nat.Coprime q n ↔ Nat.Coprime (q / p) n := by
  constructor
  . intro h2
    exact Nat.Coprime.coprime_div_left h2 hpq
  . intro h2
    rw [← Nat.div_mul_cancel hpq]
    exact Nat.Coprime.mul h2 h

lemma baz {p n : ℕ} (h_co : n.Coprime p) (m : ℕ) : Nat.Coprime p (m * p + n) := by
  rwa [Nat.coprime_mul_right_add_right, Nat.coprime_comm]

#eval gcod 12 10

lemma zorp {q p n : ℕ} (hq : q ≠ 0) (h1 : Nat.Coprime (gcod q p) n) (h2 : Nat.Coprime p n) : Nat.Coprime q n := by
  apply Nat.coprime_of_dvd
  intro k k_prime k_dvd_q k_dvd_n
  have h3 := Nat.Coprime.coprime_dvd_right k_dvd_n h1
  have h4 := Nat.Coprime.coprime_dvd_right k_dvd_n h2
  have := dvd_gcod_of_dvd_of_coprime hq k_dvd_q h4.symm
  have := Nat.Coprime.coprime_dvd_left this h3
  rw [Nat.coprime_self] at this
  subst k
  exact Nat.not_prime_one k_prime

theorem timo {p q n : ℕ} (h2 : n.Coprime p) (hq : 0 < q): ∃ m < q, Nat.Coprime q (m * p + n) := by
  wlog h3 : q.Coprime p generalizing q
  . suffices ∃ m < gcod q p, Nat.Coprime (gcod q p) (m * p + n) by
      obtain ⟨m, hm, h_co⟩ := this
      refine ⟨m, ?_, ?_⟩
      . refine hm.trans_le ?_
        apply Nat.le_of_dvd hq
        exact gcod_dvd q p
      . have : Nat.Coprime p (m * p + n) := baz h2 m
        apply zorp hq.ne' h_co this
    apply this
    . exact gcod_pos q p
    . exact gcod_coprime q p
  suffices ∃ m, (m * p + n : ZMod q) = 1 by
    rcases this with ⟨m, hm⟩
    have : NeZero q := NeZero.of_gt hq
    refine ⟨m.val, ZMod.val_lt m, ?_⟩
    apply Nat.Coprime.symm
    apply Nat.coprime_of_mul_modEq_one 1
    simp [← ZMod.eq_iff_modEq_nat, hm]
  use (1 - ↑n) * (p : ZMod q)⁻¹
  have := ZMod.isUnit_coe_iff_coprime.mpr h3.symm
  rw [mul_assoc, ZMod.inv_mul_of_unit _ this]
  simp

theorem timo2 {p q : ℕ} (n : (ZMod p)ˣ) (hq : 0 < q) : ∃ m : ZMod q, IsUnit (m * p + n : ZMod (p * q)) := by
  have n_co_p : Nat.Coprime (n : ZMod p).val p := by
    rw [ZMod.coprime_val_iff_isUnit]
    simp
  have ⟨m, m_lt_q, hm⟩ := timo n_co_p hq
  use m
  rw [← ZMod.coprime_val_iff_isUnit, Nat.coprime_mul_iff_right]
  have mpn_eq : ((m : ZMod q) * p + (n : ZMod p) : ZMod (p * q)).val = m * p + (n : ZMod p).val := by
    have : NeZero q := NeZero.of_gt hq
    by_cases hp : p = 0
    . subst p
      have : CharP (ZMod (0 * q)) 0 := by rw [zero_mul]; exact inferInstance
      have : Nontrivial (ZMod (0 * q)) := by rw [zero_mul]; exact inferInstance
      rcases Int.units_eq_one_or n with rfl|rfl
      . simp
      . rw [Units.val_neg, Units.val_one, ZMod.cast_neg (Nat.dvd_zero 0)]
        simp
        congr
        <;> try simp
        rw [zero_mul, ZMod.instCommRing_zero]
    have : NeZero p := ⟨hp⟩
    by_cases hq1 : q = 1
    . subst q
      rw [Nat.lt_one_iff] at m_lt_q
      subst m
      have : (n : ZMod p).val < (p * 1) := by simpa using ZMod.val_lt (n : ZMod p)
      simp [ZMod.val_cast_eq_val_of_lt this]
    have one_lt_q : 1 < q := Ne.lt_of_le' hq1 hq
    have p_pos : 0 < p := NeZero.pos p
    have p_lt_q : p < p * q := lt_mul_right p_pos one_lt_q
    rw [ZMod.val_add, ZMod.val_mul,
        ZMod.val_cast_eq_val_of_lt (lt_mul_of_lt_of_one_le (ZMod.val_lt _) hq),
        ZMod.val_cast_eq_val_of_lt (lt_mul_of_one_le_of_lt (NeZero.pos p) (ZMod.val_lt _)),
        Nat.mod_add_mod, ZMod.val_nat_cast_of_lt m_lt_q, ZMod.val_nat_cast,
        Nat.mod_eq_of_lt p_lt_q, Nat.mod_eq_of_lt]
    calc m * p + ZMod.val (n : ZMod p)
      _ < m * p + p := by gcongr; exact ZMod.val_lt _
      _ = p * (m + 1) := by ring
      _ ≤ p * q := by gcongr; exact m_lt_q
  rw [mpn_eq]
  constructor
  . rw [Nat.coprime_comm]
    exact baz n_co_p m
  . rw [Nat.coprime_comm]
    exact hm

theorem timo25 (p n : ℕ) [NeZero p] : IsUnit ((n⁻¹ : ZMod p) : ZMod (p / gcd p n)) := by
  sorry

theorem timo26 (p n : ℕ) : (p / gcd p n : ZMod p) * (n : ZMod p) = 0 := by
  norm_cast
  rw [ZMod.nat_cast_zmod_eq_zero_iff_dvd]
  have ⟨k, hk⟩ := gcd_dvd_right p n
  nth_rewrite 2 [hk]
  use k
  have := gcd_dvd_left p n
  rw [← mul_assoc, Nat.div_mul_cancel this]

#check addOrderOf

theorem ZMod.mul_cancel_right {p : ℕ} (n m k : ZMod p) : n * k = m * k ↔ (n : ZMod (p / addOrderOf n)) = m := by
  sorry

@[simp]
theorem Int.addOrderOf_eq_zero {x : ℤ} (hx : ¬x = 0) : addOrderOf x = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intro n n_pos
  dsimp at *
  simp [n_pos.ne', hx]

@[simp]
theorem ZMod.addOrderOf_eq_zero {x : ZMod 0} (hx : ¬x = 0) : addOrderOf x = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intro n n_pos
  dsimp at *
  simp [n_pos.ne', hx]

example (p n : ℕ) : p.succ ∣ gcod p.succ n * n := by slim_check

theorem ZMod.extracted_1 (p n m : ℕ) (m_pos : m.succ % (p.succ / gcd p.succ n.succ) ≠ 0) :
  ¬p.succ ∣ (m.succ % (p.succ / gcd p.succ n.succ)) * n.succ := by
  -- slim_check
  sorry

theorem ZMod.extracted_2 (p n : ℕ) (npos : 0 < n) (hp : ¬p = 0) (m : ℕ) (m_lt : m < p / gcd p n) (m_pos : 0 < m) :
  ¬p ∣ m * n :=


theorem ZMod.addOrderOf_nat_cast (p n : ℕ) (npos : 0 < n): addOrderOf (n : ZMod p) = p / gcd p n := by
  by_cases hp : p = 0
  . subst p
    have : (n : ℤ) ≠ 0 := by simp [npos.ne']
    simp [Int.addOrderOf_eq_zero this]
  rw [addOrderOf_eq_iff]
  constructor
  . simp [timo26]
  . intro m m_lt m_pos
    rw [nsmul_eq_mul]
    norm_cast
    rw [ZMod.nat_cast_zmod_eq_zero_iff_dvd]
    extract_goal
    intro p_dvd
    have : p / gcd p n ∣ p := sorry
    have := dvd_trans this p_dvd
    have : p ∣ p / gcd p n * n := sorry
    -- p ∣ m * n → p ∣ m * gcod n p * (n / gcod n p)
    -- but Coprime (gcod n p) p; therefore
    -- p ∣ m * (n / gcod n p)
    --

  . apply Nat.div_pos
    . apply Nat.gcd_le_left
      exact Nat.pos_of_ne_zero hp
    . exact Nat.gcd_pos_of_pos_right p npos


theorem timo3 {p : ℕ} [NeZero p] (n : ℕ) : ∃ inv : ZMod p, inv * n = (n⁻¹ : ZMod p) * n ∧ inv * inv⁻¹ = 1 := by
  have ⟨inv', inv'_eq⟩ := timo25 p n
  have gcd_pos : 0 < gcd p n := Nat.gcd_pos_of_pos_left n (NeZero.pos p)
  have ⟨m, hm⟩ := timo2 inv' gcd_pos
  use m * (p / gcd p n : ZMod p) + inv'
  constructor
  . rw [add_mul, mul_assoc, timo26 p n]
    simp
  .

-- example {p : ℕ} {n : ℕ} (h : ¬ p ∣ n ) : (n : ZMod p)⁻¹ * (n : ZMod p)⁻¹⁻¹ = 1 := by
--   -- slim_check


-- #eval (6 : ZMod 9)⁻¹
-- #eval (6⁻¹ : ZMod 9)
-- #eval (8 * ((6⁻¹ : ZMod 9) : ZMod (9 / gcd 9 6))⁻¹ : ZMod (9 / gcd 9 6))
-- example {p n : ℕ} (hn : 0 < n) : ((n⁻¹ : ZMod p) * ((n⁻¹ : ZMod p)⁻¹ : ZMod (p / gcd p n)) : ZMod (p / gcd p n)) = 1 := by
--   -- slim_check

-- #eval (8 : ZMod 18)⁻¹
-- #eval (16 : ZMod 18)⁻¹
-- #eval (16 * 17 : ZMod 18)

theorem ZMod.isUnit_inv {p : ℕ} {n : ZMod p} (h : n ≠ 0) : IsUnit n⁻¹ := by
  apply isUnit_of_mul_eq_one n⁻¹ n⁻¹
  -- slim_check
-- TODO: without `isUnit` hypothesis

theorem ZMod.inv_inv_of_unit {p : ℕ} {n : ZMod p} (h : IsUnit n) : n⁻¹⁻¹ = n := by
  have := ZMod.isUnit_inv_of_isUnit h
  rw [← IsUnit.mul_right_inj this, ZMod.inv_mul_of_unit n h, ZMod.mul_inv_of_unit n⁻¹ this]



-- theorem Nat.gcd_eq_gcd_ab (x : ℕ) (y : ℕ) :
-- ↑(Nat.gcd x y) = ↑x * Nat.gcdA x y + ↑y * Nat.gcdB x y

attribute [simp] Nat.mod_one ZMod.inv_zero

@[simp]
theorem Nat.gcdA_one_left (n : ℕ) : gcdA 1 n = 1 := by
  cases n <;> simp [gcdA, xgcd, xgcdAux]

@[simp]
theorem Nat.gcdA_self (n : ℕ) (h : n ≠ 0) : gcdA n n = 1 := by
  cases n
  . contradiction
  simp [gcdA, xgcd, xgcdAux]

open Nat

#eval xgcd 1 1

def normal {p : ℕ} (n : ZMod p) : ZMod p := gcd n.val p
-- Pseudo-inverse (is this an established term?)
-- TODO: Should `pInv 0` be defined as `1` so that `pInv n` is always a unit?
-- def pInv {p : ℕ} (n : ZMod p) : ZMod p := gcdA n.val p
abbrev pInv {p : ℕ} (n : ZMod p) : ZMod p := n⁻¹

-- define char as well? (m = char n ↔ n * m = 0) → normal n = p / char n

-- TODO: Could be generalized for p = 0
variable {p : ℕ} [NeZero p] (m n : ZMod p)

theorem normal_zero : normal (0 : ZMod p) = 0 := by
  simp [normal]

theorem pInv_zero : pInv (0 : ZMod p) = 0 := by
  simp [pInv]

theorem normal_one : normal (1 : ZMod p) = 1 := by
  nontriviality
  simp [normal]

theorem pInv_one : pInv (1 : ZMod p) = 1 := by
  nontriviality
  simp [pInv]

theorem mul_pInv : n * pInv n = normal n := by
  dsimp [pInv, normal]
  rw [← Int.cast_ofNat, Nat.gcd_eq_gcd_ab]
  simp

#reduce (0 : ZMod 9)⁻¹
#reduce (3 : ZMod 9)⁻¹
#reduce (6 : ZMod 9)⁻¹

-- theorem normal_unit (h : IsUnit n) : normal n = 1 := by


theorem normal_dvd : normal n ∣ n := by
  apply ZMod.dvd_of_val_dvd_val
  by_cases h : gcd n.val p = p
  . suffices n = 0 by
      subst this
      simp [normal]
    rw [← Nat.gcd_eq_right_iff_dvd] at h
    have : n.val < p := ZMod.val_lt n
    simpa using Nat.eq_zero_of_dvd_of_lt h this
  . have : gcd n.val p < p := Nat.lt_of_le_of_ne (Nat.gcd_le_right _ (NeZero.pos p)) h
    simp only [normal, ZMod.val_nat_cast_of_lt this]
    apply Nat.gcd_dvd_left

theorem pInv_mul_pInv_pInv : pInv n * pInv (pInv n) = 1 := by
  sorry


theorem dvd_normal : n ∣ normal n := by
  use pInv n
  rw [mul_pInv]

-- simp?
theorem normal_dvd_iff : normal n ∣ m ↔ n ∣ m := by
  have h1:= normal_dvd n
  have h2 := dvd_normal n
  refine ⟨fun h => ?_, fun h => ?_⟩
  . exact dvd_trans h2 h
  . exact dvd_trans h1 h

def divMod {p : ℕ} (m n : ZMod p) : ZMod p :=
  let r := gcd p n.val
  let t := gcdB p n.val
  (m.val / r : ℕ) * t

theorem mul_divMod_cancel {p : ℕ} (m n : ZMod p) : divMod (n * m) m = n := by
  unfold divMod
  have ⟨x, h⟩ := Nat.gcd_dvd_left p n.val

theorem divMod_mul_cancel {p : ℕ} (m n : ZMod p) : n ∣ m → (divMod m n) * n = m := by
  intro ⟨mDivN, h⟩
  subst h
  rw [mul_comm n, mul_divMod_cancel]

#eval Nat.xgcd 5 3
#eval divMod 5 1 1 -- Ok 1
#eval divMod 5 1 2 -- Ok 3
#eval divMod 5 1 3 -- Ok 2
#eval divMod 5 1 4 -- Ok 4
#eval divMod 9 3 6 -- Ok 2
#eval divMod 9 6 6 -- Ok 1
#eval divMod 102 98 4 -- Ok 50
