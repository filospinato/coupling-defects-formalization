import DivisorF.DefectSpectrum
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Defect-spectrum support and quantile deductions

Discrete and algebraic consequences of the Section 4 spectrum estimates.  No
prime-distribution theorem is used here.  The ordered defects are represented
by the largest level whose spectrum still contains at least the requested
number of fibres; the finite high-level theorem supplies the harmless bound
`2N` needed by `Nat.findGreatest`.  The final quadratic theorem isolates
exactly the deduction used in the manuscript after the low/moderate spectrum
bound has been supplied as an explicit external-input interface.
-/

namespace DivisorF

/-- The level `r = 1` is exactly positive defect. -/
theorem mem_defectLevelPrimes_one_iff_positive
    {N : ℕ} {q : LargePrime N} :
    q ∈ defectLevelPrimes N 1 ↔ 0 < fibreDefect q := by
  rw [mem_defectLevelPrimes]
  have hnonneg := fibreDefect_nonneg q
  have hcast : (Int.toNat (fibreDefect q) : ℤ) = fibreDefect q :=
    Int.toNat_of_nonneg hnonneg
  omega

/-- The level `r = 2` is exactly non-binary defect. -/
theorem mem_defectLevelPrimes_two_iff_nonbinary
    {N : ℕ} {q : LargePrime N} :
    q ∈ defectLevelPrimes N 2 ↔ 2 ≤ fibreDefect q := by
  rw [mem_defectLevelPrimes]
  have hnonneg := fibreDefect_nonneg q
  have hcast : (Int.toNat (fibreDefect q) : ℤ) = fibreDefect q :=
    Int.toNat_of_nonneg hnonneg
  omega

/-- The manuscript's positive-defect support as an explicit finite set. -/
noncomputable def positiveDefectPrimes (N : ℕ) : Finset (LargePrime N) :=
  defectLevelPrimes N 1

@[simp]
theorem mem_positiveDefectPrimes
    {N : ℕ} {q : LargePrime N} :
    q ∈ positiveDefectPrimes N ↔ 0 < fibreDefect q := by
  exact mem_defectLevelPrimes_one_iff_positive

/-- The manuscript's non-binary support as an explicit finite set. -/
noncomputable def nonbinaryDefectPrimes (N : ℕ) : Finset (LargePrime N) :=
  defectLevelPrimes N 2

@[simp]
theorem mem_nonbinaryDefectPrimes
    {N : ℕ} {q : LargePrime N} :
    q ∈ nonbinaryDefectPrimes N ↔ 2 ≤ fibreDefect q := by
  exact mem_defectLevelPrimes_two_iff_nonbinary

/-- Positive-defect support cardinality is exactly `A_1(N)`. -/
theorem positiveDefectPrimes_card_eq_spectrum_one
    {N : ℕ} :
    (positiveDefectPrimes N).card = defectSpectrum N 1 := by
  rfl

/-- Non-binary support cardinality is exactly `A_2(N)`. -/
theorem nonbinaryDefectPrimes_card_eq_spectrum_two
    {N : ℕ} :
    (nonbinaryDefectPrimes N).card = defectSpectrum N 2 := by
  rfl

/-- The fixed-level `r=1` estimate transfers verbatim to the manuscript's
positive-defect support.  The actual analytic estimate is deliberately an
explicit hypothesis. -/
theorem positiveDefectSupport_real_le_of_spectrum_one_bound
    {N : ℕ} {B : ℝ}
    (hbound : (defectSpectrum N 1 : ℝ) ≤ B) :
    ((positiveDefectPrimes N).card : ℝ) ≤ B := by
  simpa [positiveDefectPrimes_card_eq_spectrum_one] using hbound

/-- The fixed-level `r=2` estimate transfers verbatim to the manuscript's
non-binary support.  The actual analytic estimate is deliberately an explicit
hypothesis. -/
theorem nonbinaryDefectSupport_real_le_of_spectrum_two_bound
    {N : ℕ} {B : ℝ}
    (hbound : (defectSpectrum N 2 : ℝ) ≤ B) :
    ((nonbinaryDefectPrimes N).card : ℝ) ≤ B := by
  simpa [nonbinaryDefectPrimes_card_eq_spectrum_two] using hbound

/-- The spectrum is antitone in its defect threshold. -/
theorem defectSpectrum_antitone
    {N r s : ℕ} (hrs : r ≤ s) :
    defectSpectrum N s ≤ defectSpectrum N r := by
  unfold defectSpectrum
  apply Finset.card_le_card
  intro q hq
  apply mem_defectLevelPrimes.mpr
  exact le_trans hrs (mem_defectLevelPrimes.mp hq)

/-- Every actual natural-valued defect is at most `2N`.  This bound is not a
new estimate: it is only a finite search bound extracted from the already
proved high-level spectrum inequality. -/
theorem fibreDefectNat_le_two_mul_N
    {N : ℕ} (hN : 2 ≤ N) (q : LargePrime N) :
    Int.toNat (fibreDefect q) ≤ 2 * N := by
  let r := Int.toNat (fibreDefect q)
  by_cases hr0 : r = 0
  · simp [r, hr0]
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  have hmem : q ∈ defectLevelPrimes N r := by
    apply mem_defectLevelPrimes.mpr
    exact le_rfl
  have hcount : 1 ≤ defectSpectrum N r := by
    unfold defectSpectrum
    exact Finset.one_le_card.mpr ⟨q, hmem⟩
  have hlinear := defectThreshold_le_linear_quantile
    (N := N) (r := r) (j := 1) hN hr (by decide) hcount
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt hNnonneg
  have hsqrt_le_N : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    nlinarith
  have hreal : (r : ℝ) ≤ 2 * (N : ℝ) := by
    have hlinear' : (r : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
      simpa using hlinear
    nlinarith
  exact_mod_cast hreal

/-- A nonempty spectrum level cannot occur above `2N`. -/
theorem defectThreshold_le_two_mul_N_of_spectrum_pos
    {N r : ℕ} (hN : 2 ≤ N)
    (hpos : 0 < defectSpectrum N r) :
    r ≤ 2 * N := by
  unfold defectSpectrum at hpos
  rcases Finset.card_pos.mp hpos with ⟨q, hq⟩
  exact le_trans (mem_defectLevelPrimes.mp hq)
    (fibreDefectNat_le_two_mul_N hN q)

/-- The manuscript's ordered defect `Δ_j(N)`, padded by zero once the positive
support is exhausted.  For `j>0`, this is the largest positive threshold `r`
for which at least `j` large-prime fibres have defect at least `r`.

The search bound `2N` is exhaustive by `fibreDefectNat_le_two_mul_N`. -/
noncomputable def orderedDefect (N j : ℕ) : ℕ :=
  if j = 0 then 0
  else Nat.findGreatest (fun r => j ≤ defectSpectrum N r) (2 * N)

@[simp]
theorem orderedDefect_zero_index (N : ℕ) : orderedDefect N 0 = 0 := by
  simp [orderedDefect]

/-- Exact threshold characterization of the ordered defect sequence.  This is
the formal counterpart of listing positive defects in decreasing order and
padding with zeros. -/
theorem le_orderedDefect_iff_spectrum_count
    {N j r : ℕ}
    (hN : 2 ≤ N)
    (hj : 0 < j)
    (hr : 0 < r) :
    r ≤ orderedDefect N j ↔ j ≤ defectSpectrum N r := by
  rw [orderedDefect, if_neg (Nat.ne_of_gt hj)]
  constructor
  · intro hrD
    have hDpos : 0 < Nat.findGreatest
        (fun t => j ≤ defectSpectrum N t) (2 * N) :=
      lt_of_lt_of_le hr hrD
    have hDspec :
        j ≤ defectSpectrum N
          (Nat.findGreatest (fun t => j ≤ defectSpectrum N t) (2 * N)) :=
      Nat.findGreatest_of_ne_zero
        (P := fun t => j ≤ defectSpectrum N t)
        (m := Nat.findGreatest (fun t => j ≤ defectSpectrum N t) (2 * N))
        (n := 2 * N) rfl (Nat.ne_of_gt hDpos)
    exact le_trans hDspec (defectSpectrum_antitone hrD)
  · intro hcount
    have hspecpos : 0 < defectSpectrum N r := lt_of_lt_of_le hj hcount
    have hrbound : r ≤ 2 * N :=
      defectThreshold_le_two_mul_N_of_spectrum_pos hN hspecpos
    exact Nat.le_findGreatest hrbound hcount

/-- `Δ_j(N)>0` exactly when the positive-defect support contains at least `j`
fibres. -/
theorem orderedDefect_pos_iff
    {N j : ℕ}
    (hN : 2 ≤ N)
    (hj : 0 < j) :
    0 < orderedDefect N j ↔ j ≤ defectSpectrum N 1 := by
  constructor
  · intro hD
    have hD1 : 1 ≤ orderedDefect N j := hD
    exact
      (le_orderedDefect_iff_spectrum_count
        (N := N) (j := j) (r := 1) hN hj (by decide)).mp hD1
  · intro hcount
    have hD1 : 1 ≤ orderedDefect N j :=
      (le_orderedDefect_iff_spectrum_count
        (N := N) (j := j) (r := 1) hN hj (by decide)).mpr hcount
    omega

/-- Literal ordered-defect form of the manuscript's linear quantile bound
`Δ_j(N) ≤ 2 sqrt(N)/j`. -/
theorem orderedDefect_le_linear_quantile
    {N j : ℕ}
    (hN : 2 ≤ N)
    (hj : 0 < j) :
    (orderedDefect N j : ℝ) ≤
      2 * Real.sqrt (N : ℝ) / (j : ℝ) := by
  by_cases hD : orderedDefect N j = 0
  · simp only [hD, Nat.cast_zero]
    positivity
  have hDpos : 0 < orderedDefect N j := Nat.pos_of_ne_zero hD
  have hcount : j ≤ defectSpectrum N (orderedDefect N j) :=
    (le_orderedDefect_iff_spectrum_count hN hj hDpos).mp le_rfl
  exact defectThreshold_le_linear_quantile
    hN hDpos hj hcount

/-- If a threshold has at least `j` fibres above it and `j` lies in the bulk
`j ≥ 2 sqrt(N) / log N`, the linear quantile estimate already forces that
threshold below `log N`.  This is the entry condition used before applying the
low/moderate spectrum theorem in the manuscript's ordered-defect argument. -/
theorem defectThreshold_le_log_of_bulk
    {N r j : ℕ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hj : 0 < j)
    (hlog : 0 < Real.log (N : ℝ))
    (hcount : j ≤ defectSpectrum N r)
    (hbulk :
      2 * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ≤ (j : ℝ)) :
    (r : ℝ) ≤ Real.log (N : ℝ) := by
  have hlinear := defectThreshold_le_linear_quantile
    (N := N) (r := r) (j := j) hN hr hj hcount
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hmul :
      2 * Real.sqrt (N : ℝ) ≤ (j : ℝ) * Real.log (N : ℝ) :=
    (div_le_iff₀ hlog).mp hbulk
  have hquot :
      2 * Real.sqrt (N : ℝ) / (j : ℝ) ≤ Real.log (N : ℝ) := by
    apply (div_le_iff₀ hjR).2
    nlinarith
  exact le_trans hlinear hquot

/-- Algebraic inversion behind the manuscript's quadratic bulk quantile bound.
If at least `j` fibres have defect at least `r` and a low/moderate estimate
`A_r(N) ≤ C sqrt(N/(r log N))` is available, then
`r ≤ C^2 N/(j^2 log N)`.

The spectrum estimate is an explicit hypothesis because its proof is the place
where the external prime-counting input enters; this theorem itself is purely
discrete/algebraic. -/
theorem defectThreshold_le_quadratic_of_spectrum_bound
    {N r j : ℕ} {C : ℝ}
    (hr : 0 < r)
    (hj : 0 < j)
    (hlog : 0 < Real.log (N : ℝ))
    (hC : 0 ≤ C)
    (hcount : j ≤ defectSpectrum N r)
    (hspectrum :
      (defectSpectrum N r : ℝ) ≤
        C * Real.sqrt
          ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)))) :
    (r : ℝ) ≤
      C ^ 2 * (N : ℝ) /
        ((j : ℝ) ^ 2 * Real.log (N : ℝ)) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hden : 0 < (r : ℝ) * Real.log (N : ℝ) := mul_pos hrR hlog
  have hx :
      0 ≤ (N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)) := by
    positivity
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) :=
    Real.sqrt_nonneg _
  have hright_nonneg :
      0 ≤ C * Real.sqrt ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) :=
    mul_nonneg hC hsqrt_nonneg
  have hjA : (j : ℝ) ≤ (defectSpectrum N r : ℝ) := by
    exact_mod_cast hcount
  have hjbound :
      (j : ℝ) ≤
        C * Real.sqrt ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) :=
    le_trans hjA hspectrum
  have hsq := mul_self_le_mul_self (le_of_lt hjR) hjbound
  have hsqrt_sq :
      (Real.sqrt ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)))) ^ 2 =
        (N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)) :=
    Real.sq_sqrt hx
  have hsq' :
      (j : ℝ) ^ 2 ≤
        C ^ 2 * ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) := by
    nlinarith
  have hmul :
      (j : ℝ) ^ 2 * ((r : ℝ) * Real.log (N : ℝ)) ≤
        C ^ 2 * (N : ℝ) := by
    calc
      (j : ℝ) ^ 2 * ((r : ℝ) * Real.log (N : ℝ))
          ≤ (C ^ 2 * ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)))) *
              ((r : ℝ) * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hsq' (le_of_lt hden)
      _ = C ^ 2 * (N : ℝ) := by
        field_simp [ne_of_gt hden]
  have htargetDen :
      0 < (j : ℝ) ^ 2 * Real.log (N : ℝ) := by positivity
  apply (le_div_iff₀ htargetDen).2
  nlinarith

/-- Complete project-original transfer behind the quadratic bulk-quantile
corollary, with the external low/moderate spectrum estimate kept visible.
The linear high-level estimate first puts `r` into the range `r ≤ log N`; the
supplied low/moderate estimate is then inverted to the quadratic threshold. -/
theorem defectThreshold_le_quadratic_of_bulk_low_bound
    {N r j : ℕ} {C : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hj : 0 < j)
    (hlog : 0 < Real.log (N : ℝ))
    (hC : 0 ≤ C)
    (hcount : j ≤ defectSpectrum N r)
    (hbulk :
      2 * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ≤ (j : ℝ))
    (hlow :
      (r : ℝ) ≤ Real.log (N : ℝ) →
        (defectSpectrum N r : ℝ) ≤
          C * Real.sqrt
            ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)))) :
    (r : ℝ) ≤
      C ^ 2 * (N : ℝ) /
        ((j : ℝ) ^ 2 * Real.log (N : ℝ)) := by
  have hrlog := defectThreshold_le_log_of_bulk
    (N := N) (r := r) (j := j) hN hr hj hlog hcount hbulk
  exact defectThreshold_le_quadratic_of_spectrum_bound
    hr hj hlog hC hcount (hlow hrlog)

/-- Literal ordered-defect form of the manuscript's quadratic bulk quantile
corollary.  The low/moderate spectrum theorem remains an explicit interface;
this result formalizes the project's order-statistic deduction from it. -/
theorem orderedDefect_le_quadratic_of_bulk_low_bound
    {N j : ℕ} {C : ℝ}
    (hN : 2 ≤ N)
    (hj : 0 < j)
    (hlog : 0 < Real.log (N : ℝ))
    (hC : 0 ≤ C)
    (hbulk :
      2 * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ≤ (j : ℝ))
    (hlow :
      ∀ r : ℕ, 0 < r → (r : ℝ) ≤ Real.log (N : ℝ) →
        (defectSpectrum N r : ℝ) ≤
          C * Real.sqrt
            ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)))) :
    (orderedDefect N j : ℝ) ≤
      C ^ 2 * (N : ℝ) /
        ((j : ℝ) ^ 2 * Real.log (N : ℝ)) := by
  by_cases hD : orderedDefect N j = 0
  · simp only [hD, Nat.cast_zero]
    positivity
  have hDpos : 0 < orderedDefect N j := Nat.pos_of_ne_zero hD
  have hcount : j ≤ defectSpectrum N (orderedDefect N j) :=
    (le_orderedDefect_iff_spectrum_count hN hj hDpos).mp le_rfl
  exact defectThreshold_le_quadratic_of_bulk_low_bound
    hN hDpos hj hlog hC hcount hbulk
    (hlow (orderedDefect N j) hDpos)

end DivisorF
