import DivisorF.DefectSpectrumEnvelope
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Fixed-level defect-spectrum transfer corollaries

Finite epsilon-level formulations of the project-original Section 4 fixed-level
argument and its support consequences.  The asymptotic prime number theorem
input remains visible as the supplied prefix estimate at the balanced threshold
or, for relative density, as an explicit lower bound for the total large-prime
population.
-/

namespace DivisorF

/-- Finite epsilon form of the paper's fixed-level `(4 + o(1))` argument.
If the external prime-counting input at the balanced threshold has coefficient
`2 + eps`, the project-original variational optimization gives coefficient
`4 + eps` for the defect spectrum. -/
theorem defectSpectrum_real_le_fixed_of_balanced_prefix
    {N r : ℕ} {eps : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hlog : 0 < Real.log (N : ℝ))
    (heps : 0 ≤ eps)
    (hQlo :
      Real.sqrt (N : ℝ) ≤ defectSpectrumBalanceQ N r)
    (hQhi :
      defectSpectrumBalanceQ N r ≤ (N : ℝ))
    (hprefix :
      (largePrimePrefixCount N (defectSpectrumBalanceQ N r) : ℝ) ≤
        (2 + eps) * defectSpectrumBalanceQ N r /
          Real.log (N : ℝ)) :
    (defectSpectrum N r : ℝ) ≤
      (4 + eps) * Real.sqrt
        ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) := by
  have h := defectSpectrum_real_le_low_of_balanced_prefix_bound
    (N := N) (r := r) (C := 2 + eps)
    hN hr hlog hQlo hQhi (by positivity) hprefix
  convert h using 1
  ring

/-- The `r=1` specialization is exactly the positive-defect support bound in
finite epsilon form.  PNT supplies the prefix hypothesis externally; this
corollary performs only the project's fixed-level transfer. -/
theorem positiveDefectSupport_real_le_fixed_of_balanced_prefix
    {N : ℕ} {eps : ℝ}
    (hN : 2 ≤ N)
    (hlog : 0 < Real.log (N : ℝ))
    (heps : 0 ≤ eps)
    (hQlo :
      Real.sqrt (N : ℝ) ≤ defectSpectrumBalanceQ N 1)
    (hQhi :
      defectSpectrumBalanceQ N 1 ≤ (N : ℝ))
    (hprefix :
      (largePrimePrefixCount N (defectSpectrumBalanceQ N 1) : ℝ) ≤
        (2 + eps) * defectSpectrumBalanceQ N 1 /
          Real.log (N : ℝ)) :
    ((positiveDefectPrimes N).card : ℝ) ≤
      (4 + eps) * Real.sqrt
        ((N : ℝ) / Real.log (N : ℝ)) := by
  have h := defectSpectrum_real_le_fixed_of_balanced_prefix
    (N := N) (r := 1) (eps := eps)
    hN (by decide) hlog heps hQlo hQhi hprefix
  simpa [positiveDefectPrimes_card_eq_spectrum_one] using h

/-- The same fixed-level transfer at `r=2` controls the non-binary support.
This is an immediate project consequence, with the external prime estimate
still explicit. -/
theorem nonbinaryDefectSupport_real_le_fixed_of_balanced_prefix
    {N : ℕ} {eps : ℝ}
    (hN : 2 ≤ N)
    (hlog : 0 < Real.log (N : ℝ))
    (heps : 0 ≤ eps)
    (hQlo :
      Real.sqrt (N : ℝ) ≤ defectSpectrumBalanceQ N 2)
    (hQhi :
      defectSpectrumBalanceQ N 2 ≤ (N : ℝ))
    (hprefix :
      (largePrimePrefixCount N (defectSpectrumBalanceQ N 2) : ℝ) ≤
        (2 + eps) * defectSpectrumBalanceQ N 2 /
          Real.log (N : ℝ)) :
    ((nonbinaryDefectPrimes N).card : ℝ) ≤
      (4 + eps) * Real.sqrt
        ((N : ℝ) / (2 * Real.log (N : ℝ))) := by
  have h := defectSpectrum_real_le_fixed_of_balanced_prefix
    (N := N) (r := 2) (eps := eps)
    hN (by decide) hlog heps hQlo hQhi hprefix
  simpa [nonbinaryDefectPrimes_card_eq_spectrum_two] using h

/-- A supplied uniform low/moderate theorem plus the finite high-level theorem
immediately controls the positive-defect support in the uniform envelope. -/
theorem positiveDefectSupport_real_le_of_uniform_low
    {N : ℕ} {C : ℝ}
    (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hC2 : 2 ≤ C)
    (hlow :
      (1 : ℝ) ≤ Real.log (N : ℝ) →
        (defectSpectrum N 1 : ℝ) ≤
          C * Real.sqrt
            ((N : ℝ) / Real.log (N : ℝ))) :
    ((positiveDefectPrimes N).card : ℝ) ≤
      C * Real.sqrt (N : ℝ) /
        Real.sqrt (Real.log (N : ℝ)) := by
  have hlogpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have h := defectSpectrum_real_le_uniform_envelope_of_low_sqrt_bound
    (N := N) (r := 1) (C := C)
    hN (by decide) hlogpos hC2 (by
      intro _
      simpa using hlow hlog)
  have hmax : max (1 : ℝ) (Real.log (N : ℝ)) = Real.log (N : ℝ) :=
    max_eq_right hlog
  simpa [positiveDefectPrimes_card_eq_spectrum_one, hmax] using h

/-- Number of primes in the manuscript's large-prime range. -/
noncomputable def largePrimeCount (N : ℕ) : ℕ :=
  Fintype.card (LargePrime N)

/-- Relative density of positive-defect fibres among all large-prime fibres.
Real division already assigns value zero to an empty denominator, while the
asymptotic corollary is used only once the external prime-count lower bound is
positive. -/
noncomputable def positiveDefectRelativeDensity (N : ℕ) : ℝ :=
  ((positiveDefectPrimes N).card : ℝ) / (largePrimeCount N : ℝ)

/-- Finite transfer behind the manuscript's vanishing-relative-density
corollary.  The numerator estimate is supplied by the project's fixed-level
spectrum theorem, while the denominator lower bound is where PNT enters and is
therefore kept as an explicit external hypothesis. -/
theorem positiveDefectRelativeDensity_le_of_bounds
    {N : ℕ} {U L : ℝ}
    (hU : 0 ≤ U)
    (hL : 0 < L)
    (hsupport : ((positiveDefectPrimes N).card : ℝ) ≤ U)
    (hprimes : L ≤ (largePrimeCount N : ℝ)) :
    positiveDefectRelativeDensity N ≤ U / L := by
  have hcountpos : 0 < (largePrimeCount N : ℝ) := lt_of_lt_of_le hL hprimes
  unfold positiveDefectRelativeDensity
  calc
    ((positiveDefectPrimes N).card : ℝ) / (largePrimeCount N : ℝ)
        ≤ U / (largePrimeCount N : ℝ) := by
          exact div_le_div_of_nonneg_right hsupport (le_of_lt hcountpos)
    _ ≤ U / L := by
          exact div_le_div_of_nonneg_left hU hL hprimes

/-- Section 4 relative-density transfer in the natural finite PNT shape.
If the positive support is bounded by `C sqrt(N/log N)` and the external prime
count gives at least `c N/log N` large primes, their ratio is bounded by the
quotient of those two scales.  The subsequent fact that this tends to zero is
standard real analysis plus PNT and is intentionally not re-proved here. -/
theorem positiveDefectRelativeDensity_le_pnt_scale
    {N : ℕ} {C c : ℝ}
    (hN : 2 ≤ N)
    (hlog : 0 < Real.log (N : ℝ))
    (hC : 0 ≤ C)
    (hc : 0 < c)
    (hsupport :
      ((positiveDefectPrimes N).card : ℝ) ≤
        C * Real.sqrt ((N : ℝ) / Real.log (N : ℝ)))
    (hprimes :
      c * (N : ℝ) / Real.log (N : ℝ) ≤
        (largePrimeCount N : ℝ)) :
    positiveDefectRelativeDensity N ≤
      (C * Real.sqrt ((N : ℝ) / Real.log (N : ℝ))) /
        (c * (N : ℝ) / Real.log (N : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hL : 0 < c * (N : ℝ) / Real.log (N : ℝ) := by
    positivity
  apply positiveDefectRelativeDensity_le_of_bounds
    (N := N)
    (U := C * Real.sqrt ((N : ℝ) / Real.log (N : ℝ)))
    (L := c * (N : ℝ) / Real.log (N : ℝ))
  · positivity
  · exact hL
  · exact hsupport
  · exact hprimes

end DivisorF
