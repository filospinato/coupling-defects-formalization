import Mathlib.Tactic

set_option linter.style.header false

/-!
# Section 5 power-cone exponent selection

This module formalizes the project-original elementary exponent calculation
used when passing from the fixed-exponent quotient range to an `N`-power cone.
No short-interval prime theorem is formalized here.
-/

namespace DivisorF

/-- The algebraic heart of the Section 5 cone conversion.

If `1/2 < beta < 1` and

`0 < gamma < (1-beta)/(2-beta)`,

then one may choose a fixed exponent `rho` with

`0 < rho < 1-beta` and `gamma < rho/(1+rho)`.

This is exactly the strict-exponent choice used before the manuscript's
comparison `s ≤ N^gamma => s ≤ (N/s)^rho`. -/
theorem exists_rho_for_power_cone
    {beta gamma : ℝ}
    (hbetaLower : (1 : ℝ) / 2 < beta)
    (hbetaUpper : beta < 1)
    (hgammaPos : 0 < gamma)
    (hgammaUpper : gamma < (1 - beta) / (2 - beta)) :
    ∃ rho : ℝ, 0 < rho ∧ rho < 1 - beta ∧ gamma < rho / (1 + rho) := by
  have htwoBeta : 0 < 2 - beta := by linarith
  have honeBeta : 0 < 1 - beta := by linarith
  have hfracLtOne : (1 - beta) / (2 - beta) < (1 : ℝ) := by
    rw [div_lt_one htwoBeta]
    linarith
  have hgammaLtOne : gamma < 1 := lt_trans hgammaUpper hfracLtOne
  have honeGamma : 0 < 1 - gamma := by linarith
  have hratio : gamma / (1 - gamma) < 1 - beta := by
    rw [div_lt_iff₀ honeGamma]
    rw [lt_div_iff₀ htwoBeta] at hgammaUpper
    nlinarith
  let rho : ℝ := (gamma / (1 - gamma) + (1 - beta)) / 2
  have hratioRho : gamma / (1 - gamma) < rho := by
    dsimp [rho]
    linarith
  have hrhoUpper : rho < 1 - beta := by
    dsimp [rho]
    linarith
  have hratioPos : 0 < gamma / (1 - gamma) := div_pos hgammaPos honeGamma
  have hrhoPos : 0 < rho := lt_trans hratioPos hratioRho
  have honeRho : 0 < 1 + rho := by linarith
  have hgammaRho : gamma < rho / (1 + rho) := by
    rw [lt_div_iff₀ honeRho]
    have h := hratioRho
    rw [div_lt_iff₀ honeGamma] at h
    nlinarith
  exact ⟨rho, hrhoPos, hrhoUpper, hgammaRho⟩

/-- **Section 5 real-power range comparison.**

This is the elementary inequality used in Corollary 5.3.  If
`gamma < rho/(1+rho)`, then every point of the `N^gamma` cone lies in
the quotient cone `s ≤ (N/s)^rho` (for positive `N,s`).  The proof is
kept separate from the prime-distribution input: it is purely the logarithmic
rearrangement appearing in the manuscript. -/
theorem le_div_rpow_of_le_rpow
    {N s gamma rho : ℝ}
    (hN : 1 ≤ N)
    (hs : 1 ≤ s)
    (_hgamma : 0 ≤ gamma)
    (hrho : 0 < rho)
    (hgammaRho : gamma < rho / (1 + rho))
    (hcone : s ≤ N ^ gamma) :
    s ≤ (N / s) ^ rho := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have honeRho : 0 < 1 + rho := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogCone : Real.log s ≤ gamma * Real.log N :=
    (Real.le_rpow_iff_log_le hspos hNpos).1 hcone
  have hgammaRhoLe : gamma ≤ rho / (1 + rho) := le_of_lt hgammaRho
  have hlogBound :
      Real.log s ≤ (rho / (1 + rho)) * Real.log N :=
    hlogCone.trans (mul_le_mul_of_nonneg_right hgammaRhoLe hlogN)
  have hscaled :
      (1 + rho) * Real.log s ≤ rho * Real.log N := by
    calc
      (1 + rho) * Real.log s ≤
          (1 + rho) * ((rho / (1 + rho)) * Real.log N) :=
        mul_le_mul_of_nonneg_left hlogBound (le_of_lt honeRho)
      _ = rho * Real.log N := by
        field_simp [ne_of_gt honeRho]
  have hlogQuot : Real.log s ≤ rho * (Real.log N - Real.log s) := by
    nlinarith
  have hquotPos : 0 < N / s := div_pos hNpos hspos
  rw [← Real.log_div hNpos.ne' hspos.ne'] at hlogQuot
  exact (Real.le_rpow_iff_log_le hspos hquotPos).2 hlogQuot

end DivisorF
