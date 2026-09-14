import DivisorF.RegularEndpointCanonicalScalar
import DivisorF.TranslatedEndpointPaperBounds
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Elementary bounds for the concrete translated endpoint

For

`g_eta(X)=X-3X^eta`, `0<eta<1`,

most of the manuscript's scalar package is elementary without calculus:
`g_eta(X)` is eventually at least one, eventually lies between `X/2` and `X`,
and its one-step increment is always at most one.  The only genuinely
asymptotic one-step estimate left is the lower bound

`1/2 <= g_eta(X+1)-g_eta(X)`.

This module proves the elementary pieces and shows that this single lower-step
fact suffices to recover the full `EventuallyTranslatedEndpointPaperBounds`
interface consumed by the discrete bounded-multiplicity machinery.
-/

namespace DivisorF

/-- Positive powers are monotone in the endpoint, so subtracting
`3 X^eta` makes the translated increment at most the underlying unit step. -/
theorem translatedEndpointReal_step_le_one
    {eta : ℝ} (heta : 0 < eta) (X : ℕ) :
    translatedEndpointReal eta (X + 1) - translatedEndpointReal eta X ≤ 1 := by
  have hbase : (X : ℝ) ≤ ((X + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show X ≤ X + 1 by omega)
  have hpow : (X : ℝ) ^ eta ≤ ((X + 1 : ℕ) : ℝ) ^ eta :=
    Real.rpow_le_rpow (by positivity) hbase (le_of_lt heta)
  dsimp [translatedEndpointReal]
  push_cast at hpow ⊢
  linarith

/-- For `0<=eta<1`, the concrete translated endpoint is eventually positive
and lies in the coarse interval `[floor(X/2),X]` used by Section 6. -/
theorem eventually_translatedEndpointReal_envelope
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      1 ≤ translatedEndpointReal eta X ∧
      (((X / 2 : ℕ) : ℝ) ≤ translatedEndpointReal eta X ∧
        translatedEndpointReal eta X ≤ (X : ℝ)) := by
  rcases eventually_ten_mul_rpow_le_self heta0 heta1 with ⟨Xpow, hpow⟩
  refine ⟨max Xpow 2, ?_⟩
  intro X hX
  have hXpow : Xpow ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hX2 : 2 ≤ X := le_trans (Nat.le_max_right _ _) hX
  have hp := hpow X hXpow
  have hrpow : 0 ≤ (X : ℝ) ^ eta := Real.rpow_nonneg (by positivity) _
  have hX2real : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hhalfNat : 2 * (X / 2) ≤ X := by omega
  have hhalfCast : 2 * ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hhalfNat
  have hlowerHalf :
      ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) - 3 * (X : ℝ) ^ eta := by
    linarith
  have hone : 1 ≤ (X : ℝ) - 3 * (X : ℝ) ^ eta := by
    linarith
  have hupper : (X : ℝ) - 3 * (X : ℝ) ^ eta ≤ (X : ℝ) := by
    linarith
  dsimp [translatedEndpointReal]
  exact ⟨hone, hlowerHalf, hupper⟩

/-- Isolate the sole remaining calculus-shaped estimate in the manuscript's
`g_eta` bounds. -/
def EventuallyTranslatedEndpointLowerStep (eta : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    (1 : ℝ) / 2 ≤
      translatedEndpointReal eta (X + 1) - translatedEndpointReal eta X

/-- **Reduction of the paper-shaped scalar package.**

For `0<eta<1`, the eventual lower one-step estimate alone implies the complete
paper interface: positivity, both one-step inequalities, and the `X/2..X`
envelope. -/
theorem eventuallyTranslatedEndpointPaperBounds_of_lowerStep
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1)
    (hlower : EventuallyTranslatedEndpointLowerStep eta) :
    EventuallyTranslatedEndpointPaperBounds eta := by
  rcases hlower with ⟨Xstep, hstep⟩
  rcases eventually_translatedEndpointReal_envelope (le_of_lt heta) heta1 with
    ⟨Xenv, henv⟩
  refine ⟨max Xstep Xenv, ?_⟩
  intro X hX
  have hS : Xstep ≤ X := le_trans (Nat.le_max_left _ _) hX
  have hE : Xenv ≤ X := le_trans (Nat.le_max_right _ _) hX
  rcases henv X hE with ⟨hone, hlowerEnv, hupperEnv⟩
  exact ⟨hone, hstep X hS, translatedEndpointReal_step_le_one heta X,
    hlowerEnv, hupperEnv⟩

/-- Once the lower-step estimate is supplied, the concrete translated map has
all downstream bounded-multiplicity and dyadic-comparability consequences
already proved from `EventuallyTranslatedEndpointPaperBounds`. -/
theorem eventuallyDyadicallySparse_pulledBack_translatedEndpointMap_of_lowerStep
    {eta : ℝ} {target : ℕ → Finset ℕ}
    (heta : 0 < eta) (heta1 : eta < 1)
    (hlower : EventuallyTranslatedEndpointLowerStep eta)
    (hsparse : EventuallyDyadicallySparse target) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y (translatedEndpointMap eta) (target Y)) := by
  exact eventuallyDyadicallySparse_pulledBack_translatedEndpointMap_of_paperBounds
    hsparse (eventuallyTranslatedEndpointPaperBounds_of_lowerStep heta heta1 hlower)

end DivisorF
