import DivisorF.DefectSpectrumQuantiles
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Defect-spectrum analytic transfer envelope

Project-original Section 4 transfer layer.  External prime-distribution input is
kept visible as a hypothesis on the lower prime-counting term.  The results in
this file formalize the paper's balancing/optimization step and the combination
of the low/moderate and high-defect regimes; they do not prove the prime number
theorem or any literature estimate.
-/

namespace DivisorF

/-- Algebraic balancing identity used after choosing the variational threshold.
If `Q^2 = N log N / r`, then the tail term `2N/(rQ)` is exactly `2Q/log N`.
This is support for the project-original optimization step. -/
theorem variational_tail_eq_balanced_term
    {N r : ℕ} {Q : ℝ}
    (hr : 0 < r)
    (hQ : 0 < Q)
    (hlog : 0 < Real.log (N : ℝ))
    (hbalance :
      Q ^ 2 = (N : ℝ) * Real.log (N : ℝ) / (r : ℝ)) :
    2 * (N : ℝ) / ((r : ℝ) * Q) =
      2 * Q / Real.log (N : ℝ) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hlogne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlog
  have hbalance' :
      (r : ℝ) * Q ^ 2 = (N : ℝ) * Real.log (N : ℝ) := by
    rw [hbalance]
    field_simp [hrne]
  field_simp [hrne, hQne, hlogne]
  nlinarith [hbalance']

/-- Balanced finite transfer behind both the fixed-level and low/moderate
Section 4 estimates.  Once the external prime-counting input gives
`prefix(Q) ≤ C Q/log N` at a threshold satisfying
`Q^2 = N log N/r`, the original variational theorem gives
`A_r(N) ≤ (C+2) Q/log N`.

The prime-counting estimate itself is deliberately an explicit hypothesis. -/
theorem defectSpectrum_real_le_balanced_of_prefix_bound
    {N r : ℕ} {Q C : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hQlo : Real.sqrt (N : ℝ) ≤ Q)
    (hQhi : Q ≤ (N : ℝ))
    (hQ : 0 < Q)
    (hlog : 0 < Real.log (N : ℝ))
    (_hC : 0 ≤ C)
    (hbalance :
      Q ^ 2 = (N : ℝ) * Real.log (N : ℝ) / (r : ℝ))
    (hprefix :
      (largePrimePrefixCount N Q : ℝ) ≤
        C * Q / Real.log (N : ℝ)) :
    (defectSpectrum N r : ℝ) ≤
      (C + 2) * Q / Real.log (N : ℝ) := by
  have hvar := defectSpectrum_real_le_of_prefix_bound
    (N := N) (r := r) (Q := Q)
    hN hr hQlo hQhi hprefix
  rw [variational_tail_eq_balanced_term hr hQ hlog hbalance] at hvar
  calc
    (defectSpectrum N r : ℝ)
        ≤ C * Q / Real.log (N : ℝ) +
            2 * Q / Real.log (N : ℝ) := hvar
    _ = (C + 2) * Q / Real.log (N : ℝ) := by ring

/-- The balanced threshold used in Section 4. -/
noncomputable def defectSpectrumBalanceQ (N r : ℕ) : ℝ :=
  Real.sqrt
    ((N : ℝ) * Real.log (N : ℝ) / (r : ℝ))

/-- The chosen balanced threshold has the required square. -/
theorem defectSpectrumBalanceQ_sq
    {N r : ℕ}
    (hr : 0 < r)
    (hlog : 0 < Real.log (N : ℝ)) :
    defectSpectrumBalanceQ N r ^ 2 =
      (N : ℝ) * Real.log (N : ℝ) / (r : ℝ) := by
  unfold defectSpectrumBalanceQ
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hx :
      0 ≤ (N : ℝ) * Real.log (N : ℝ) / (r : ℝ) := by
    positivity
  exact Real.sq_sqrt hx

/-- The balanced threshold is positive under the paper's nontrivial
hypotheses. -/
theorem defectSpectrumBalanceQ_pos
    {N r : ℕ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hlog : 0 < Real.log (N : ℝ)) :
    0 < defectSpectrumBalanceQ N r := by
  unfold defectSpectrumBalanceQ
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  apply Real.sqrt_pos.2
  positivity

/-- Exact real identity converting the balanced scale into the normalized
Section 4 factor `sqrt(N/(r log N))`. -/
theorem defectSpectrumBalanceQ_div_log
    {N r : ℕ}
    (hr : 0 < r)
    (hlog : 0 < Real.log (N : ℝ)) :
    defectSpectrumBalanceQ N r / Real.log (N : ℝ) =
      Real.sqrt
        ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hlogR : 0 < Real.log (N : ℝ) := hlog
  let x : ℝ := (N : ℝ) * Real.log (N : ℝ) / (r : ℝ)
  let y : ℝ := (N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have hleft : 0 ≤ Real.sqrt x / Real.log (N : ℝ) := by
    positivity
  have hright : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have hsq :
      (Real.sqrt x / Real.log (N : ℝ)) ^ 2 = y := by
    dsimp [x, y] at hsx ⊢
    rw [div_pow, hsx]
    field_simp [ne_of_gt hrR, ne_of_gt hlogR]
  unfold defectSpectrumBalanceQ
  dsimp [x, y] at hleft hright hsq hsy ⊢
  nlinarith

/-- Project-original balanced transfer in the paper's normalized low/moderate
shape.  The only analytic input is the explicit prime-prefix estimate at the
chosen threshold `Q = sqrt(N log N/r)`; the theorem performs the paper's
variational balancing step. -/
theorem defectSpectrum_real_le_low_of_balanced_prefix_bound
    {N r : ℕ} {C : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hlog : 0 < Real.log (N : ℝ))
    (hQlo :
      Real.sqrt (N : ℝ) ≤ defectSpectrumBalanceQ N r)
    (hQhi :
      defectSpectrumBalanceQ N r ≤ (N : ℝ))
    (hC : 0 ≤ C)
    (hprefix :
      (largePrimePrefixCount N (defectSpectrumBalanceQ N r) : ℝ) ≤
        C * defectSpectrumBalanceQ N r / Real.log (N : ℝ)) :
    (defectSpectrum N r : ℝ) ≤
      (C + 2) * Real.sqrt
        ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) := by
  have hbalanced := defectSpectrum_real_le_balanced_of_prefix_bound
    (N := N) (r := r) (Q := defectSpectrumBalanceQ N r) (C := C)
    hN hr hQlo hQhi
    (defectSpectrumBalanceQ_pos hN hr hlog)
    hlog hC (defectSpectrumBalanceQ_sq hr hlog) hprefix
  rw [← defectSpectrumBalanceQ_div_log hr hlog]
  simpa [mul_div_assoc] using hbalanced

/-- **Uniform defect-spectrum envelope transfer.**

This formalizes the project-original combination step of the manuscript.  If a
single constant `C` controls the low/moderate regime in the paper's normalized
shape and `C ≥ 2`, then the already-proved high-level estimate supplies the
complementary regime, giving

`A_r(N) ≤ C sqrt N / sqrt(r * max(r, log N))`

for every positive integer level `r`.  The low/moderate estimate is an explicit
hypothesis because that is where external prime-counting input enters. -/
theorem defectSpectrum_real_le_uniform_envelope
    {N r : ℕ} {C : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (_hlog : 0 < Real.log (N : ℝ))
    (hC2 : 2 ≤ C)
    (hlow :
      (r : ℝ) ≤ Real.log (N : ℝ) →
        (defectSpectrum N r : ℝ) ≤
          C * Real.sqrt (N : ℝ) /
            Real.sqrt ((r : ℝ) * Real.log (N : ℝ))) :
    (defectSpectrum N r : ℝ) ≤
      C * Real.sqrt (N : ℝ) /
        Real.sqrt
          ((r : ℝ) * max (r : ℝ) (Real.log (N : ℝ))) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  by_cases hrlog : (r : ℝ) ≤ Real.log (N : ℝ)
  · rw [max_eq_right hrlog]
    exact hlow hrlog
  · have hlog_le_r : Real.log (N : ℝ) ≤ (r : ℝ) := le_of_not_ge hrlog
    rw [max_eq_left hlog_le_r]
    have hhigh := defectSpectrum_le_high_level_real
      (N := N) (r := r) hN hr
    have hsqr : Real.sqrt ((r : ℝ) * (r : ℝ)) = (r : ℝ) := by
      rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hrR]
    rw [hsqr]
    exact le_trans hhigh (by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)
      · exact le_of_lt hrR)

/-- The standard low/moderate square-root shape is identical to the normalized
form consumed by `defectSpectrum_real_le_uniform_envelope`. -/
theorem lowSpectrum_sqrt_ratio_eq_normalized
    {N r : ℕ}
    (hr : 0 < r)
    (hlog : 0 < Real.log (N : ℝ)) :
    Real.sqrt
      ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ))) =
      Real.sqrt (N : ℝ) /
        Real.sqrt ((r : ℝ) * Real.log (N : ℝ)) := by
  have hden : 0 ≤ (r : ℝ) * Real.log (N : ℝ) := by positivity
  exact Real.sqrt_div' (N : ℝ) hden

/-- Uniform envelope transfer directly from the manuscript's low/moderate
statement `A_r ≤ C sqrt(N/(r log N))`. -/
theorem defectSpectrum_real_le_uniform_envelope_of_low_sqrt_bound
    {N r : ℕ} {C : ℝ}
    (hN : 2 ≤ N)
    (hr : 0 < r)
    (hlog : 0 < Real.log (N : ℝ))
    (hC2 : 2 ≤ C)
    (hlow :
      (r : ℝ) ≤ Real.log (N : ℝ) →
        (defectSpectrum N r : ℝ) ≤
          C * Real.sqrt
            ((N : ℝ) / ((r : ℝ) * Real.log (N : ℝ)))) :
    (defectSpectrum N r : ℝ) ≤
      C * Real.sqrt (N : ℝ) /
        Real.sqrt
          ((r : ℝ) * max (r : ℝ) (Real.log (N : ℝ))) := by
  apply defectSpectrum_real_le_uniform_envelope hN hr hlog hC2
  intro hrlog
  have h := hlow hrlog
  rw [lowSpectrum_sqrt_ratio_eq_normalized hr hlog] at h
  simpa [mul_div_assoc] using h

end DivisorF
