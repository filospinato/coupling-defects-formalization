import DivisorF.TailLevels
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite defect spectrum

Original Section 4 finite distribution layer.  The principal result here is the
finite variational inequality for

`A_r(N) = #{sqrt N < q ≤ N : q prime, D_N(q) ≥ r}`.

No asymptotic prime-distribution input is used.  The paper term
`π(Q) - π(sqrt N)` is represented by the cardinality of the finite subtype of
`LargePrime N` with `q ≤ Q`; under `Q ≤ N` this is exactly the same set of
primes.
-/

namespace DivisorF

/-- One stable decidable-equality witness for the finite large-prime subtype. -/
noncomputable local instance largePrimeDecidableEq (N : ℕ) :
    DecidableEq (LargePrime N) :=
  Classical.decEq _

/-- Large-prime fibres whose defect is at least the integer level `r`. -/
noncomputable def defectLevelPrimes (N r : ℕ) : Finset (LargePrime N) := by
  classical
  exact Finset.univ.filter fun q => r ≤ Int.toNat (fibreDefect q)

@[simp]
theorem mem_defectLevelPrimes
    {N r : ℕ} {q : LargePrime N} :
    q ∈ defectLevelPrimes N r ↔ r ≤ Int.toNat (fibreDefect q) := by
  classical
  simp [defectLevelPrimes]

/-- The paper's defect spectrum `A_r(N)`. -/
noncomputable def defectSpectrum (N r : ℕ) : ℕ :=
  (defectLevelPrimes N r).card

/-- Large primes in the lower part of the variational split, `q ≤ Q`. -/
noncomputable def largePrimePrefix (N : ℕ) (Q : ℝ) : Finset (LargePrime N) := by
  classical
  exact Finset.univ.filter fun q => (q.val : ℝ) ≤ Q

@[simp]
theorem mem_largePrimePrefix
    {N : ℕ} {Q : ℝ} {q : LargePrime N} :
    q ∈ largePrimePrefix N Q ↔ (q.val : ℝ) ≤ Q := by
  classical
  simp [largePrimePrefix]

/-- Finite realization of the paper term `π(Q) - π(sqrt N)` for `Q ≤ N`. -/
noncomputable def largePrimePrefixCount (N : ℕ) (Q : ℝ) : ℕ :=
  (largePrimePrefix N Q).card

/-- Level fibres in the lower part `q ≤ Q` of the variational split. -/
noncomputable def headLevelPrimes (N : ℕ) (Q : ℝ) (r : ℕ) :
    Finset (LargePrime N) := by
  classical
  exact (defectLevelPrimes N r).filter fun q => (q.val : ℝ) ≤ Q

@[simp]
theorem mem_headLevelPrimes
    {N r : ℕ} {Q : ℝ} {q : LargePrime N} :
    q ∈ headLevelPrimes N Q r ↔
      r ≤ Int.toNat (fibreDefect q) ∧ (q.val : ℝ) ≤ Q := by
  classical
  simp [headLevelPrimes]

/-- Every level fibre lies on exactly one side of the threshold `Q`. -/
theorem defectLevelPrimes_eq_head_union_tail
    {N r : ℕ} {Q : ℝ} :
    defectLevelPrimes N r =
      headLevelPrimes N Q r ∪ tailLevelPrimes N Q r := by
  classical
  ext q
  rw [Finset.mem_union, mem_defectLevelPrimes, mem_headLevelPrimes,
    mem_tailLevelPrimes, mem_tailPrimes]
  constructor
  · intro hlevel
    by_cases hq : (q.val : ℝ) ≤ Q
    · exact Or.inl ⟨hlevel, hq⟩
    · exact Or.inr ⟨lt_of_not_ge hq, hlevel⟩
  · rintro (h | h)
    · exact h.1
    · exact h.2

/-- The two parts of the threshold split are disjoint. -/
theorem headLevelPrimes_disjoint_tailLevelPrimes
    {N r : ℕ} {Q : ℝ} :
    Disjoint (headLevelPrimes N Q r) (tailLevelPrimes N Q r) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro q hhead htail
  have hle : (q.val : ℝ) ≤ Q := (mem_headLevelPrimes.mp hhead).2
  have hgt : Q < (q.val : ℝ) :=
    mem_tailPrimes.mp (mem_tailLevelPrimes.mp htail).1
  exact (not_lt_of_ge hle) hgt

/-- Exact cardinality decomposition at a threshold `Q`. -/
theorem defectLevelPrimes_card_eq_head_add_tail
    {N r : ℕ} {Q : ℝ} :
    (defectLevelPrimes N r).card =
      (headLevelPrimes N Q r).card + (tailLevelPrimes N Q r).card := by
  rw [defectLevelPrimes_eq_head_union_tail]
  exact Finset.card_union_of_disjoint
    headLevelPrimes_disjoint_tailLevelPrimes

/-- The lower level set is contained in the complete large-prime prefix. -/
theorem headLevelPrimes_subset_largePrimePrefix
    {N r : ℕ} {Q : ℝ} :
    headLevelPrimes N Q r ⊆ largePrimePrefix N Q := by
  intro q hq
  exact mem_largePrimePrefix.mpr (mem_headLevelPrimes.mp hq).2

/-- The lower contribution is bounded by the number of large primes up to `Q`. -/
theorem headLevelPrimes_card_le_largePrimePrefixCount
    {N r : ℕ} {Q : ℝ} :
    (headLevelPrimes N Q r).card ≤ largePrimePrefixCount N Q := by
  unfold largePrimePrefixCount
  exact Finset.card_le_card headLevelPrimes_subset_largePrimePrefix

/-- **Theorem 4.1 candidate (finite variational bound).**

For `sqrt N ≤ Q ≤ N`, the first term is exactly the manuscript's
`π(Q) - π(sqrt N)` and the second is `floor(2 M_N(Q) / r)`, represented by
natural-number division because both quantities are integral and `r > 0`.
-/
theorem defectSpectrum_le_variational
    {N r : ℕ} {Q : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hQlo : Real.sqrt (N : ℝ) ≤ Q)
    (_hQhi : Q ≤ (N : ℝ)) :
    defectSpectrum N r ≤
      largePrimePrefixCount N Q + (2 * tailEndpointCount N Q) / r := by
  unfold defectSpectrum
  rw [defectLevelPrimes_card_eq_head_add_tail (Q := Q)]
  apply Nat.add_le_add
  · exact headLevelPrimes_card_le_largePrimePrefixCount
  · exact tailLevel_card_le hN hQlo hr

/-- The integer large-prime condition implies the manuscript inequality
`sqrt N < q`. -/
theorem sqrt_lt_largePrime_val
    {N : ℕ} (q : LargePrime N) :
    Real.sqrt (N : ℝ) < (q.val : ℝ) := by
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt hNnonneg
  have hlarge : (N : ℝ) < (q.val : ℝ) * (q.val : ℝ) := by
    exact_mod_cast q.large
  have hqnonneg : 0 ≤ (q.val : ℝ) := by positivity
  nlinarith

/-- At `Q = sqrt N`, the lower prime-counting part of the split is empty. -/
theorem largePrimePrefix_sqrt_eq_empty
    {N : ℕ} :
    largePrimePrefix N (Real.sqrt (N : ℝ)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hle : (q.val : ℝ) ≤ Real.sqrt (N : ℝ) :=
    mem_largePrimePrefix.mp hq
  exact (not_le_of_gt (sqrt_lt_largePrime_val q)) hle

/-- For `N ≥ 2`, the tail endpoint count at `Q = sqrt N` is exactly
`ceil(sqrt N) - 2`. -/
theorem tailEndpointCount_sqrt_eq
    {N : ℕ} (hN : 2 ≤ N) :
    tailEndpointCount N (Real.sqrt (N : ℝ)) =
      Nat.ceil (Real.sqrt (N : ℝ)) - 2 := by
  unfold tailEndpointCount
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt hNnonneg
  have hdiv :
      (N : ℝ) / Real.sqrt (N : ℝ) = Real.sqrt (N : ℝ) := by
    apply (div_eq_iff hsqrt_pos.ne').2
    nlinarith
  rw [hdiv]

/-- Purely finite high-level bound obtained by taking `Q = sqrt N`. -/
theorem defectSpectrum_le_sqrt_tail
    {N r : ℕ}
    (hN : 2 ≤ N)
    (hr : 0 < r) :
    defectSpectrum N r ≤
      (2 * tailEndpointCount N (Real.sqrt (N : ℝ))) / r := by
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt hNnonneg
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt_le_N : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hvar := defectSpectrum_le_variational
    (N := N) (r := r) (Q := Real.sqrt (N : ℝ))
    hN hr le_rfl hsqrt_le_N
  simpa [largePrimePrefixCount, largePrimePrefix_sqrt_eq_empty] using hvar

/-- **High defect levels candidate.**  This is the manuscript's exact finite
bound `A_r(N) ≤ floor(2 max(0, ceil(sqrt N)-2) / r)`; natural subtraction
implements the `max(0, ...)` convention. -/
theorem defectSpectrum_le_high_level
    {N r : ℕ}
    (hN : 2 ≤ N)
    (hr : 0 < r) :
    defectSpectrum N r ≤
      (2 * (Nat.ceil (Real.sqrt (N : ℝ)) - 2)) / r := by
  rw [← tailEndpointCount_sqrt_eq hN]
  exact defectSpectrum_le_sqrt_tail hN hr

/-- The exact endpoint count is bounded by its real interval length.  This is
the elementary relaxation `M_N(Q) ≤ N/Q` used in Section 4 after applying the
finite tail theorem. -/
theorem tailEndpointCount_cast_le_div
    {N : ℕ} {Q : ℝ}
    (hQ : 0 < Q) :
    (tailEndpointCount N Q : ℝ) ≤ (N : ℝ) / Q := by
  unfold tailEndpointCount
  have hx : 0 ≤ (N : ℝ) / Q := by positivity
  by_cases hceil : 2 ≤ Nat.ceil ((N : ℝ) / Q)
  · rw [Nat.cast_sub hceil]
    have hlt := Nat.ceil_lt_add_one hx
    norm_num at hlt ⊢
    linarith
  · have hle : Nat.ceil ((N : ℝ) / Q) ≤ 2 := Nat.le_of_not_ge hceil
    have hzero : Nat.ceil ((N : ℝ) / Q) - 2 = 0 := Nat.sub_eq_zero_of_le hle
    rw [hzero]
    norm_num
    exact hx

/-- Real-valued form of the variational estimate used by the asymptotic
arguments in the manuscript.  It discards only the two harmless floors:
`floor(2 M/r) ≤ 2 M/r` and `M_N(Q) ≤ N/Q`. -/
theorem defectSpectrum_real_le_variational_relaxed
    {N r : ℕ} {Q : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hQlo : Real.sqrt (N : ℝ) ≤ Q)
    (hQhi : Q ≤ (N : ℝ)) :
    (defectSpectrum N r : ℝ) ≤
      (largePrimePrefixCount N Q : ℝ) +
        2 * (N : ℝ) / ((r : ℝ) * Q) := by
  have hQpos : 0 < Q := lt_of_lt_of_le
    (lt_of_lt_of_le zero_lt_one (one_le_of_sqrt_le hN hQlo)) le_rfl
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnat := defectSpectrum_le_variational hN hr hQlo hQhi
  have hcast :
      (defectSpectrum N r : ℝ) ≤
        (largePrimePrefixCount N Q : ℝ) +
          (((2 * tailEndpointCount N Q) / r : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hdivCast :
      ((((2 * tailEndpointCount N Q) / r : ℕ) : ℝ)) ≤
        ((2 * tailEndpointCount N Q : ℕ) : ℝ) / (r : ℝ) := by
    exact Nat.cast_div_le
  have htail :
      2 * (tailEndpointCount N Q : ℝ) / (r : ℝ) ≤
        2 * ((N : ℝ) / Q) / (r : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (tailEndpointCount_cast_le_div hQpos) (by norm_num))
      (le_of_lt hrR)
  calc
    (defectSpectrum N r : ℝ)
        ≤ (largePrimePrefixCount N Q : ℝ) +
            (((2 * tailEndpointCount N Q) / r : ℕ) : ℝ) := hcast
    _ ≤ (largePrimePrefixCount N Q : ℝ) +
          ((2 * tailEndpointCount N Q : ℕ) : ℝ) / (r : ℝ) :=
        add_le_add le_rfl hdivCast
    _ = (largePrimePrefixCount N Q : ℝ) +
          2 * (tailEndpointCount N Q : ℝ) / (r : ℝ) := by norm_num
    _ ≤ (largePrimePrefixCount N Q : ℝ) +
          2 * ((N : ℝ) / Q) / (r : ℝ) :=
        add_le_add le_rfl htail
    _ = (largePrimePrefixCount N Q : ℝ) +
          2 * (N : ℝ) / ((r : ℝ) * Q) := by
        field_simp [ne_of_gt hrR, ne_of_gt hQpos]

/-- The analytic input can be supplied only through a bound for the lower
prime-counting part.  This is the project-original transfer step; no prime
number theorem or literature estimate is built into the formalization. -/
theorem defectSpectrum_real_le_of_prefix_bound
    {N r : ℕ} {Q B : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hQlo : Real.sqrt (N : ℝ) ≤ Q)
    (hQhi : Q ≤ (N : ℝ))
    (hprefix : (largePrimePrefixCount N Q : ℝ) ≤ B) :
    (defectSpectrum N r : ℝ) ≤
      B + 2 * (N : ℝ) / ((r : ℝ) * Q) := by
  apply le_trans
    (defectSpectrum_real_le_variational_relaxed hN hr hQlo hQhi)
  exact add_le_add hprefix le_rfl

/-- The second inequality in the manuscript's high-defect theorem:
`A_r(N) ≤ 2 sqrt(N) / r`. -/
theorem defectSpectrum_le_high_level_real
    {N r : ℕ}
    (hN : 2 ≤ N)
    (hr : 0 < r) :
    (defectSpectrum N r : ℝ) ≤
      2 * Real.sqrt (N : ℝ) / (r : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt hNnonneg
  have hsqrt_le_N : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hvar := defectSpectrum_real_le_variational_relaxed
    (N := N) (r := r) (Q := Real.sqrt (N : ℝ))
    hN hr le_rfl hsqrt_le_N
  have hempty :
      largePrimePrefixCount N (Real.sqrt (N : ℝ)) = 0 := by
    unfold largePrimePrefixCount
    rw [largePrimePrefix_sqrt_eq_empty]
    simp
  rw [hempty] at hvar
  norm_num at hvar
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  calc
    (defectSpectrum N r : ℝ)
        ≤ 2 * (N : ℝ) / ((r : ℝ) * Real.sqrt (N : ℝ)) := hvar
    _ = 2 * Real.sqrt (N : ℝ) / (r : ℝ) := by
        field_simp [ne_of_gt hsqrt_pos, ne_of_gt hrR]
        nlinarith [hsqrt_sq]

/-- Finite order-statistic inversion behind the manuscript bound
`Delta_j(N) ≤ 2 sqrt(N)/j`: if at least `j` fibres have defect at least `r`,
then that threshold cannot exceed `2 sqrt(N)/j`. -/
theorem defectThreshold_le_linear_quantile
    {N r j : ℕ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hj : 0 < j)
    (hcount : j ≤ defectSpectrum N r) :
    (r : ℝ) ≤ 2 * Real.sqrt (N : ℝ) / (j : ℝ) := by
  have hhigh := defectSpectrum_le_high_level_real (N := N) (r := r) hN hr
  have hjA : (j : ℝ) ≤ (defectSpectrum N r : ℝ) := by exact_mod_cast hcount
  have hjbound : (j : ℝ) ≤ 2 * Real.sqrt (N : ℝ) / (r : ℝ) :=
    le_trans hjA hhigh
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hmul : (j : ℝ) * (r : ℝ) ≤ 2 * Real.sqrt (N : ℝ) :=
    (le_div_iff₀ hrR).mp hjbound
  apply (le_div_iff₀ hjR).2
  nlinarith

end DivisorF
