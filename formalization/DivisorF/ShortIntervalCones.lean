import DivisorF.AsymptoticPrimeTransfer
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `SI(beta)` and the manuscript's named zero-defect cones

Section 5 turns its conditional machinery into arithmetic statements by feeding
in three published inputs: Guth–Maynard (`SI(17/30)`), Li's preprint
(`SI(beta)` for `13/25 < beta < 21/40`), and the Riemann hypothesis
(`SI(beta)` for every `beta > 1/2`). The cone exponents `13/43`, `12/37` and
`1/3` of Theorem 5.4, Corollary 5.8 and Corollary 5.9 come out of that
substitution.

Before this module nothing in the formalization named `SI(beta)`, and none of
those exponents appeared anywhere: `beta` and `gamma` were free variables
constrained only by `gamma < (1-beta)/(2-beta)`. So the step a reader is most
likely to want checked — the arithmetic taking `beta = 17/30` to `gamma < 13/43`
— was not machine-checked.

This module supplies:

- `ShortIntervalPrimeInput`, Definition 5.1 verbatim;
- the exponent arithmetic for all three inputs, as `rfl`-level real identities;
- the three cone statements, each with its published input as a single named
  hypothesis.

**No literature theorem is proved here, and none should be.** `SI(17/30)` *is*
Guth–Maynard; asserting it would be re-proving published analytic number
theory, which `formalization/AGENTS.md` forbids. What changes is that the
implication from it to the manuscript's stated exponent is now machine-checked,
so exactly one named hypothesis stands between the formalization and each
unconditional corollary.

The manuscript's own Theorem 5.2 Steps 1–2 — the passage from `SI(beta)` to the
exact quotient-interval prime richness the transfer consumes — is stated here as
`ShortIntervalQuotientRichness` and *proved* in `DivisorF.ShortIntervalTransfer`,
which also restates the three cones below with their published short-interval
input as the single remaining hypothesis.
-/

namespace DivisorF

open scoped Nat

/-- **Definition 5.1.** `SI(beta)`: primes are dense in short intervals of
length `T ^ beta` above every sufficiently large `T`. -/
def ShortIntervalPrimeInput (beta : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    c * ((T : ℝ) ^ beta / Real.log T) ≤
      ((Nat.primeCounting ⌊T⌋₊ : ℝ) -
        (Nat.primeCounting ⌊T - (T : ℝ) ^ beta⌋₊ : ℝ))

/-- The manuscript's Theorem 5.2, Steps 1–2.

Given `SI(beta)`, the manuscript localises the quotient interval inside a short
interval and counts primes there, obtaining `t_s(N) > 2(s-1)` uniformly on the
fixed-exponent range. That argument is the paper's own, not a literature
result. It is named here so that the cone theorems below can carry it
explicitly, and it is discharged for every `1/2 < beta < 1` by
`DivisorF.shortIntervalQuotientRichness`. -/
def ShortIntervalQuotientRichness (beta : ℝ) : Prop :=
  ShortIntervalPrimeInput beta →
    FixedExponentPrimeRichInput beta QuotientPowerRange

/-- The manuscript's generic cone exponent `(1-beta)/(2-beta)`. -/
noncomputable def coneExponent (beta : ℝ) : ℝ := (1 - beta) / (2 - beta)

/-- **Guth–Maynard exponent.** `beta = 17/30` gives the cone exponent `13/43`
of Theorem 5.4. -/
theorem coneExponent_guthMaynard : coneExponent (17 / 30) = 13 / 43 := by
  unfold coneExponent
  norm_num

/-- **Li exponent.** The infimum `beta = 13/25` of the admissible range in
Corollary 5.8 gives the cone exponent `12/37`. -/
theorem coneExponent_li : coneExponent (13 / 25) = 12 / 37 := by
  unfold coneExponent
  norm_num

/-- **Riemann exponent.** `beta = 1/2` gives the cubic exponent `1/3`. It is a
limit rather than an admissible value: `SI(1/2)` is not what RH supplies, and
the transfer needs `1/2 < beta`. -/
theorem coneExponent_half : coneExponent (1 / 2) = 1 / 3 := by
  unfold coneExponent
  norm_num

/-- The cone exponent approaches `1/3` from below as `beta` decreases to `1/2`:
every `gamma < 1/3` is admissible for some `beta > 1/2`.

This is the exact content of "for every fixed `eps > 0`" in Corollary 5.9. -/
theorem exists_beta_of_lt_third
    {gamma : ℝ} (hgamma : 0 < gamma) (hcubic : gamma < 1 / 3) :
    ∃ beta : ℝ, 1 / 2 < beta ∧ beta < 1 ∧ gamma < coneExponent beta := by
  set g : ℝ := (gamma + 1 / 3) / 2 with hgdef
  have hg_pos : 0 < g := by positivity
  have hg_lt : g < 1 / 3 := by simp only [hgdef]; linarith
  have hg_gt : gamma < g := by simp only [hgdef]; linarith
  have hg_ne : (1 : ℝ) - g ≠ 0 := by linarith
  refine ⟨(1 - 2 * g) / (1 - g), ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 1 - g)]
    linarith
  · rw [div_lt_one (by linarith)]
    linarith
  · have hcone : coneExponent ((1 - 2 * g) / (1 - g)) = g := by
      unfold coneExponent
      field_simp
      ring
    rw [hcone]
    exact hg_gt

/-- **Theorem 5.4, as the implication it is.**

Guth–Maynard supplies `SI(17/30)`. Given that input and the manuscript's own
Step 1–2 transfer, every fixed `0 < gamma < 13/43` has eventual zero defect on
the cone `2 ≤ s ≤ N ^ gamma`.

The `13/43` is machine-checked here as `coneExponent (17/30)`; `SI(17/30)`
itself is the published theorem and is not proved. -/
theorem eventuallyZeroDefect_guthMaynard_cone
    (hstep : ShortIntervalQuotientRichness (17 / 30))
    (hSI : ShortIntervalPrimeInput (17 / 30))
    {gamma : ℝ} (hgamma : 0 < gamma) (hcone : gamma < 13 / 43) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) := by
  refine eventuallyZeroDefectOn_naturalPowerCone_of_fixedExponentPrimeRich
    (by norm_num) (by norm_num) hgamma ?_ (hstep hSI)
  rw [show (1 - (17 : ℝ) / 30) / (2 - 17 / 30) = 13 / 43 from coneExponent_guthMaynard]
  exact hcone

/-- **Corollary 5.8, as the implication it is.**

Li's preprint bound supplies `SI(beta)` throughout `13/25 < beta < 21/40`; the
manuscript takes `beta` down to the infimum `13/25`, giving the cone exponent
`12/37`. -/
theorem eventuallyZeroDefect_li_cone
    (hstep : ShortIntervalQuotientRichness (13 / 25))
    (hSI : ShortIntervalPrimeInput (13 / 25))
    {gamma : ℝ} (hgamma : 0 < gamma) (hcone : gamma < 12 / 37) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) := by
  refine eventuallyZeroDefectOn_naturalPowerCone_of_fixedExponentPrimeRich
    (by norm_num) (by norm_num) hgamma ?_ (hstep hSI)
  rw [show (1 - (13 : ℝ) / 25) / (2 - 13 / 25) = 12 / 37 from coneExponent_li]
  exact hcone

/-- **Corollary 5.9, as the implication it is.**

The Riemann hypothesis supplies `SI(beta)` for every fixed `beta > 1/2`. Given
that family of inputs and the manuscript's Step 1–2 transfer at each `beta`,
every fixed `0 < gamma < 1/3` has eventual zero defect on the cone.

The exponent `1/3` is machine-checked here as the limit of `coneExponent` at
`beta = 1/2`: `exists_beta_of_lt_third` produces, for each admissible `gamma`,
an actual `beta > 1/2` whose cone exponent already exceeds it. -/
theorem eventuallyZeroDefect_riemann_cone
    (hstep : ∀ beta : ℝ, 1 / 2 < beta → beta < 1 →
      ShortIntervalQuotientRichness beta)
    (hSI : ∀ beta : ℝ, 1 / 2 < beta → beta < 1 → ShortIntervalPrimeInput beta)
    {gamma : ℝ} (hgamma : 0 < gamma) (hcubic : gamma < 1 / 3) :
    EventuallyZeroDefectOn (NaturalPowerCone gamma) := by
  obtain ⟨beta, hlow, hhigh, hcone⟩ := exists_beta_of_lt_third hgamma hcubic
  exact eventuallyZeroDefectOn_naturalPowerCone_of_fixedExponentPrimeRich
    hlow hhigh hgamma hcone (hstep beta hlow hhigh (hSI beta hlow hhigh))

end DivisorF
