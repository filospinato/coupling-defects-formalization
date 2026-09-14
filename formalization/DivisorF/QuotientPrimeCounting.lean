import DivisorF.EffectiveFixedTypeTransfer
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact prime counting in a quotient interval

Project-original discrete bridge from Section 5.  No prime-distribution theorem
is used.  When the lower quotient endpoint lies above `sqrt N`, the
`LargePrime N` cutoff is inactive, so `t_s(N)` is literally the number of
ordinary primes in the exact quotient interval

`(floor(N/(s+1)), floor(N/s)]`.

This isolates the literature boundary cleanly: an external theorem may estimate
the cardinality of the ordinary-prime finset below, while the conversion to
large-prime fibres and coupling defect remains inside `DivisorF`.
-/

namespace DivisorF

/-- Ordinary prime values in the exact quotient interval of type `s`. -/
def quotientIntervalPrimeValues (N s : ℕ) : Finset ℕ :=
  (Finset.Ioc (N / (s + 1)) (N / s)).filter Nat.Prime

@[simp]
theorem mem_quotientIntervalPrimeValues
    {N s p : ℕ} :
    p ∈ quotientIntervalPrimeValues N s ↔
      Nat.Prime p ∧ N / (s + 1) < p ∧ p ≤ N / s := by
  simp only [quotientIntervalPrimeValues, Finset.mem_filter, Finset.mem_Ioc]
  aesop

/-- The manuscript condition under which the large-prime lower cutoff is
inactive for the complete quotient interval. -/
def LargePrimeCutoffInactive (N s : ℕ) : Prop :=
  Real.sqrt (N : ℝ) < (N / (s + 1) : ℕ)

/-- Every ordinary prime in the exact quotient interval becomes a genuine
`LargePrime N` when the lower endpoint is above `sqrt N`. -/
def largePrimeOfQuotientInterval
    {N s p : ℕ}
    (_hs : 1 ≤ s)
    (hoff : LargePrimeCutoffInactive N s)
    (hp : p ∈ quotientIntervalPrimeValues N s) : LargePrime N := by
  have hpdata := mem_quotientIntervalPrimeValues.mp hp
  have hpprime : Nat.Prime p := hpdata.1
  have hlower : N / (s + 1) < p := hpdata.2.1
  have hupper : p ≤ N / s := hpdata.2.2
  have hpN : p ≤ N := le_trans hupper (Nat.div_le_self N s)
  have hsqrtp : Real.sqrt (N : ℝ) < (p : ℝ) := by
    have hlowerR : ((N / (s + 1) : ℕ) : ℝ) < (p : ℝ) := by
      exact_mod_cast hlower
    exact lt_trans hoff hlowerR
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt hNnonneg
  have hpnonneg : 0 ≤ (p : ℝ) := by positivity
  have hlargeR : (N : ℝ) < (p : ℝ) * (p : ℝ) := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hlarge : N < p * p := by exact_mod_cast hlargeR
  exact ⟨p, hpprime, hlarge, hpN⟩

@[simp]
theorem largePrimeOfQuotientInterval_val
    {N s p : ℕ}
    (hs : 1 ≤ s)
    (hoff : LargePrimeCutoffInactive N s)
    (hp : p ∈ quotientIntervalPrimeValues N s) :
    (largePrimeOfQuotientInterval hs hoff hp).val = p := rfl

/-- A prime constructed from the exact quotient interval has quotient type
exactly `s`. -/
theorem largePrimeOfQuotientInterval_type
    {N s p : ℕ}
    (hs : 1 ≤ s)
    (hoff : LargePrimeCutoffInactive N s)
    (hp : p ∈ quotientIntervalPrimeValues N s) :
    (largePrimeOfQuotientInterval hs hoff hp).quotientType = s := by
  apply mem_typePrimes.mp
  apply (mem_typePrimes_iff_quotient_interval (lt_of_lt_of_le Nat.zero_lt_one hs)).2
  simpa using (mem_quotientIntervalPrimeValues.mp hp).2

/-- With inactive cutoff, the value-set of type-`s` large primes is exactly the
ordinary-prime set in the quotient interval. -/
theorem typePrimeValues_eq_quotientIntervalPrimeValues
    {N s : ℕ} (hs : 1 ≤ s)
    (hoff : LargePrimeCutoffInactive N s) :
    typePrimeValues N s = quotientIntervalPrimeValues N s := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hqtype, rfl⟩
    have hinterval :=
      (mem_typePrimes_iff_quotient_interval (lt_of_lt_of_le Nat.zero_lt_one hs)).1 hqtype
    exact mem_quotientIntervalPrimeValues.mpr
      ⟨q.prime, hinterval.1, hinterval.2⟩
  · intro hp
    let q : LargePrime N := largePrimeOfQuotientInterval hs hoff hp
    apply Finset.mem_image.mpr
    refine ⟨q, ?_, rfl⟩
    exact mem_typePrimes.mpr
      (largePrimeOfQuotientInterval_type hs hoff hp)

/-- **Section 5 exact counting identity.**  If the lower quotient endpoint is
above `sqrt N`, then `t_s(N)` is exactly the number of ordinary primes in the
complete quotient interval.  This is the finite Lean realization of
` t_s(N)=π(X)-π(X_-) `. -/
theorem typeMultiplicity_eq_quotientIntervalPrimeValues_card
    {N s : ℕ} (hs : 1 ≤ s)
    (hoff : LargePrimeCutoffInactive N s) :
    typeMultiplicity N s = (quotientIntervalPrimeValues N s).card := by
  rw [← typePrimeValues_card_eq_typeMultiplicity]
  rw [typePrimeValues_eq_quotientIntervalPrimeValues hs hoff]

/-- Exact ordinary-prime-count transfer to zero defect.  External prime
estimates need only prove the cardinal inequality on the left; the quotient
localization and defect conclusion are project-original. -/
theorem paperTypeDefect_eq_zero_of_quotient_prime_count
    {N s : ℕ} (hs : 2 ≤ s)
    (hoff : LargePrimeCutoffInactive N s)
    (hcount : 2 * (s - 1) < (quotientIntervalPrimeValues N s).card) :
    paperTypeDefect N s = 0 := by
  have hmult :
      2 * (s - 1) < typeMultiplicity N s := by
    rw [typeMultiplicity_eq_quotientIntervalPrimeValues_card (by omega) hoff]
    exact hcount
  have hpos : 0 < typeMultiplicity N s :=
    lt_of_le_of_lt (Nat.zero_le _) hmult
  have hocc : TypeOccupied N s := typeMultiplicity_pos_iff_occupied.mp hpos
  rw [paperTypeDefect_eq_of_occupied hocc]
  exact typeDefect_eq_zero_of_large_multiplicity hocc hmult

/-- Binary counterpart of the exact ordinary-prime-count transfer. -/
theorem paperTypeDefect_le_one_of_quotient_prime_count
    {N s : ℕ} (hs : 2 ≤ s)
    (hoff : LargePrimeCutoffInactive N s)
    (hcount : s - 1 < (quotientIntervalPrimeValues N s).card) :
    paperTypeDefect N s ≤ 1 := by
  have hmult : s - 1 < typeMultiplicity N s := by
    rw [typeMultiplicity_eq_quotientIntervalPrimeValues_card (by omega) hoff]
    exact hcount
  have hpos : 0 < typeMultiplicity N s :=
    lt_of_le_of_lt (Nat.zero_le _) hmult
  have hocc : TypeOccupied N s := typeMultiplicity_pos_iff_occupied.mp hpos
  rw [paperTypeDefect_eq_of_occupied hocc]
  exact typeDefect_le_one_of_large_multiplicity hocc hmult

end DivisorF
