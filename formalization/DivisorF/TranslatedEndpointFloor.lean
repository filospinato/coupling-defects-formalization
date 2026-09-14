import DivisorF.TranslatedEndpointGeometry
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Floor bridge for the Section 6 translated endpoint

The manuscript defines

`g_η(X) = X - 3 X^η`,  `ν_η(X) = floor(g_η(X))`.

`TranslatedEndpointGeometry` reduces bounded multiplicity to a discrete
monotonicity/two-step property.  This module bridges that property to the real
increment estimates actually proved for `g_η`: nonnegativity, monotonicity, and
a gain of at least one over two source steps.

The remaining support obligation is now the elementary real-power estimate for
the concrete function `g_η`; no exceptional-set or prime-distribution theorem
is hidden here.
-/

namespace DivisorF

/-- The real translated endpoint function from Section 6. -/
noncomputable def translatedEndpointReal (eta : ℝ) (X : ℕ) : ℝ :=
  (X : ℝ) - 3 * (X : ℝ) ^ eta

/-- The integer translated endpoint `ν_η(X)`.  Natural floor agrees with the
paper's ordinary floor once `g_η(X) ≥ 0`, which is included in every eventual
package below. -/
noncomputable def translatedEndpointMap (eta : ℝ) (X : ℕ) : ℕ :=
  ⌊translatedEndpointReal eta X⌋₊

/-- A generic real-valued map whose late values are nonnegative, monotone, and
increase by at least one every two integer steps has a natural-floor map with
the exact discrete step control used by the exceptional-endpoint transfer. -/
theorem eventuallyTranslatedEndpointStepControl_natFloor_of_real_twoStep
    {g : ℕ → ℝ}
    (hreal : ∃ X₀ : ℕ,
      (∀ X : ℕ, X₀ ≤ X → 0 ≤ g X) ∧
      (∀ {a b : ℕ}, X₀ ≤ a → a ≤ b → g a ≤ g b) ∧
      (∀ X : ℕ, X₀ ≤ X → g X + 1 ≤ g (X + 2))) :
    EventuallyTranslatedEndpointStepControl (fun X => ⌊g X⌋₊) := by
  rcases hreal with ⟨X₀, hnonneg, hmono, htwo⟩
  refine ⟨X₀, ?_, ?_⟩
  · intro a b ha hab
    exact Nat.floor_mono (hmono ha hab)
  · intro X hX
    have hfloor : ((⌊g X⌋₊ : ℕ) : ℝ) ≤ g X :=
      Nat.floor_le (hnonneg X hX)
    have hnext : ((⌊g X⌋₊ : ℕ) : ℝ) + 1 ≤ g (X + 2) := by
      linarith [htwo X hX]
    have hnext' : (((⌊g X⌋₊ + 1 : ℕ) : ℝ) ≤ g (X + 2)) := by
      norm_num at hnext ⊢
      exact hnext
    have hfloorSucc : ⌊g X⌋₊ + 1 ≤ ⌊g (X + 2)⌋₊ :=
      Nat.le_floor hnext'
    exact Nat.lt_of_succ_le hfloorSucc

/-- Concrete floor bridge for `ν_η`: once the manuscript's eventual real
bounds for `g_η` are supplied, every translated integer value has the discrete
step control needed for bounded fibres. -/
theorem eventuallyTranslatedEndpointStepControl_of_realBounds
    {eta : ℝ}
    (hreal : ∃ X₀ : ℕ,
      (∀ X : ℕ, X₀ ≤ X → 0 ≤ translatedEndpointReal eta X) ∧
      (∀ {a b : ℕ}, X₀ ≤ a → a ≤ b →
        translatedEndpointReal eta a ≤ translatedEndpointReal eta b) ∧
      (∀ X : ℕ, X₀ ≤ X →
        translatedEndpointReal eta X + 1 ≤ translatedEndpointReal eta (X + 2))) :
    EventuallyTranslatedEndpointStepControl (translatedEndpointMap eta) := by
  exact eventuallyTranslatedEndpointStepControl_natFloor_of_real_twoStep hreal

/-- Hence the concrete translated map has fibres of size at most two as soon as
the elementary real increment package is established. -/
theorem eventuallyBoundedTranslatedEndpointFibres_two_of_realBounds
    {eta : ℝ} {target : ℕ → Finset ℕ}
    (hreal : ∃ X₀ : ℕ,
      (∀ X : ℕ, X₀ ≤ X → 0 ≤ translatedEndpointReal eta X) ∧
      (∀ {a b : ℕ}, X₀ ≤ a → a ≤ b →
        translatedEndpointReal eta a ≤ translatedEndpointReal eta b) ∧
      (∀ X : ℕ, X₀ ≤ X →
        translatedEndpointReal eta X + 1 ≤ translatedEndpointReal eta (X + 2))) :
    EventuallyBoundedTranslatedEndpointFibres (translatedEndpointMap eta) target 2 := by
  exact eventuallyBoundedTranslatedEndpointFibres_two_of_stepControl
    (eventuallyTranslatedEndpointStepControl_of_realBounds hreal)

/-- The corresponding sparsity transfer for the actual formula `ν_η`.  The
integer exceptional family remains an explicit input; the only extra hypothesis
is the elementary real-power/floor control of the translated map. -/
theorem eventuallyDyadicallySparse_pulledBack_translatedEndpointMap
    {eta : ℝ} {target : ℕ → Finset ℕ}
    (hsparse : EventuallyDyadicallySparse target)
    (hreal : ∃ X₀ : ℕ,
      (∀ X : ℕ, X₀ ≤ X → 0 ≤ translatedEndpointReal eta X) ∧
      (∀ {a b : ℕ}, X₀ ≤ a → a ≤ b →
        translatedEndpointReal eta a ≤ translatedEndpointReal eta b) ∧
      (∀ X : ℕ, X₀ ≤ X →
        translatedEndpointReal eta X + 1 ≤ translatedEndpointReal eta (X + 2))) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y (translatedEndpointMap eta) (target Y)) := by
  exact eventuallyDyadicallySparse_pulledBack_of_stepControl hsparse
    (eventuallyTranslatedEndpointStepControl_of_realBounds hreal)

/-- A coarse real envelope transfers directly through natural floor to the
integer comparability package used for adjacent dyadic blocks. -/
theorem eventuallyTranslatedEndpointComparable_natFloor_of_realEnvelope
    {g : ℕ → ℝ}
    (henv : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((X / 2 : ℕ) : ℝ) ≤ g X ∧ g X ≤ (X : ℝ))) :
    EventuallyTranslatedEndpointComparable (fun X => ⌊g X⌋₊) := by
  rcases henv with ⟨X₀, henv⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  rcases henv X hX with ⟨hlower, hupper⟩
  constructor
  · exact Nat.le_floor hlower
  · exact Nat.floor_le_of_le hupper

/-- Concrete comparability bridge for `ν_η`. -/
theorem eventuallyTranslatedEndpointComparable_of_realEnvelope
    {eta : ℝ}
    (henv : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((X / 2 : ℕ) : ℝ) ≤ translatedEndpointReal eta X ∧
        translatedEndpointReal eta X ≤ (X : ℝ))) :
    EventuallyTranslatedEndpointComparable (translatedEndpointMap eta) := by
  exact eventuallyTranslatedEndpointComparable_natFloor_of_realEnvelope henv

end DivisorF
