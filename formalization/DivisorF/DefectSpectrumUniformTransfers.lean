import DivisorF.DefectSpectrumCorollaries
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Uniform Section 4 transfer statements

This module packages the finite Section 4 machinery with the quantifiers used
in the canonical manuscript.  Prime distribution remains outside the project
formalization: the only analytic-number-theory input is the explicit
`UniformBalancedPrimePrefixInput` hypothesis below.  The theorems proved here
are the project's uniform transfer from that input to the low/moderate defect
spectrum, the all-level envelope, and the quadratic ordered-defect bulk bound.
-/

namespace DivisorF

/-- Explicit external interface used by the manuscript's low/moderate spectrum
argument.  For all sufficiently large `N` and every level `1 ≤ r ≤ log N`, the
balanced threshold is admissible and the prime prefix has the standard
`Cpi * Q / log N` upper bound.

The prime-counting assertion is external input; this definition is only an
interface and introduces no axiom. -/
def UniformBalancedPrimePrefixInput (Cpi : ℝ) (N₀ : ℕ) : Prop :=
  0 ≤ Cpi ∧
    ∀ (N r : ℕ),
      N₀ ≤ N →
      2 ≤ N →
      0 < r →
      (r : ℝ) ≤ Real.log (N : ℝ) →
      0 < Real.log (N : ℝ) →
      Real.sqrt (N : ℝ) ≤ defectSpectrumBalanceQ N r ∧
        defectSpectrumBalanceQ N r ≤ (N : ℝ) ∧
        (largePrimePrefixCount N (defectSpectrumBalanceQ N r) : ℝ) ≤
          Cpi * defectSpectrumBalanceQ N r / Real.log (N : ℝ)

/-- Uniform low/moderate defect-spectrum transfer.  This is the quantified
project-original implication behind the manuscript's low/moderate theorem;
the prime-counting estimate itself is kept in
`UniformBalancedPrimePrefixInput`. -/
theorem defectSpectrum_uniform_low_of_balanced_prefix_input
    {Cpi : ℝ} {N₀ : ℕ}
    (hinput : UniformBalancedPrimePrefixInput Cpi N₀) :
    ∀ (N r : ℕ),
      N₀ ≤ N →
      2 ≤ N →
      0 < r →
      (r : ℝ) ≤ Real.log (N : ℝ) →
      0 < Real.log (N : ℝ) →
      (defectSpectrum N r : ℝ) ≤
        (Cpi + 2) * Real.sqrt
          ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) := by
  rcases hinput with ⟨hCpi, hprefix⟩
  intro N r hN₀ hN hr hrlog hlog
  rcases hprefix N r hN₀ hN hr hrlog hlog with
    ⟨hQlo, hQhi, hprime⟩
  exact defectSpectrum_real_le_low_of_balanced_prefix_bound
    hN hr hlog hQlo hQhi hCpi hprime

/-- Exact quantified transfer to the manuscript's all-level uniform envelope.
Taking `C = Cpi + 2` and `N₁ = max N₀ 2`, the low/moderate transfer and the
finite high-level mass estimate combine for every integer `r ≥ 1`. -/
theorem exists_uniform_defect_spectrum_envelope_of_balanced_prefix_input
    {Cpi : ℝ} {N₀ : ℕ}
    (hinput : UniformBalancedPrimePrefixInput Cpi N₀) :
    ∃ C : ℝ, ∃ N₁ : ℕ,
      0 < C ∧
        ∀ (N r : ℕ),
          N₁ ≤ N →
          0 < r →
          (defectSpectrum N r : ℝ) ≤
            C * Real.sqrt (N : ℝ) /
              Real.sqrt
                ((r : ℝ) * max (r : ℝ) (Real.log (N : ℝ))) := by
  rcases hinput with ⟨hCpi, hprefix⟩
  refine ⟨Cpi + 2, max N₀ 2, by linarith, ?_⟩
  intro N r hN₁ hr
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN₁
  have hN : 2 ≤ N := le_trans (le_max_right _ _) hN₁
  have hNgt1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNgt1
  have hC2 : (2 : ℝ) ≤ Cpi + 2 := by linarith
  apply defectSpectrum_real_le_uniform_envelope_of_low_sqrt_bound
    hN hr hlog hC2
  intro hrlog
  rcases hprefix N r hN₀ hN hr hrlog hlog with
    ⟨hQlo, hQhi, hprime⟩
  exact defectSpectrum_real_le_low_of_balanced_prefix_bound
    hN hr hlog hQlo hQhi hCpi hprime

/-- Quantified project-original transfer giving the manuscript's quadratic
bulk bound for ordered defects.  The constants can be taken explicitly as
`C₁ = 2`, `C₂ = (Cpi + 2)^2`, and `N₁ = max N₀ 2` once the external balanced
prime-prefix interface is supplied. -/
theorem exists_orderedDefect_quadratic_bulk_constants_of_balanced_prefix_input
    {Cpi : ℝ} {N₀ : ℕ}
    (hinput : UniformBalancedPrimePrefixInput Cpi N₀) :
    ∃ C₁ C₂ : ℝ, ∃ N₁ : ℕ,
      0 < C₁ ∧ 0 < C₂ ∧
        ∀ (N j : ℕ),
          N₁ ≤ N →
          0 < j →
          C₁ * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ≤ (j : ℝ) →
          (orderedDefect N j : ℝ) ≤
            C₂ * (N : ℝ) /
              ((j : ℝ) ^ 2 * Real.log (N : ℝ)) := by
  rcases hinput with ⟨hCpi, hprefix⟩
  refine ⟨2, (Cpi + 2) ^ 2, max N₀ 2, by norm_num, ?_, ?_⟩
  · have hCpos : 0 < Cpi + 2 := by linarith
    positivity
  · intro N j hN₁ hj hbulk
    have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN₁
    have hN : 2 ≤ N := le_trans (le_max_right _ _) hN₁
    have hNgt1 : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hN)
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNgt1
    have hC : 0 ≤ Cpi + 2 := by linarith
    apply orderedDefect_le_quadratic_of_bulk_low_bound
      (N := N) (j := j) (C := Cpi + 2)
      hN hj hlog hC
    · simpa using hbulk
    · intro r hr hrlog
      rcases hprefix N r hN₀ hN hr hrlog hlog with
        ⟨hQlo, hQhi, hprime⟩
      exact defectSpectrum_real_le_low_of_balanced_prefix_bound
        hN hr hlog hQlo hQhi hCpi hprime

end DivisorF
