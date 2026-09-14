import DivisorF.TranslatedEndpointFloor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Paper-shaped bounds for the Section 6 translated endpoint

The manuscript does not use arbitrary monotonicity assumptions for
`g_η(X)=X-3X^η`.  It proves the eventual one-step estimate

`1/2 ≤ g_η(X+1)-g_η(X) ≤ 1`

together with positivity and the coarse asymptotic envelope `X/2 ≤ g_η(X) ≤ X`.
This module packages exactly that paper-shaped interface and derives the
monotonicity, two-step growth, bounded fibres and dyadic comparability required
by the already formalized integer exceptional-endpoint transfer.

The only remaining obligation after this module is the elementary real-power
estimate establishing these bounds for the concrete formula; no
prime-distribution theorem is hidden here.
-/

namespace DivisorF

/-- The exact eventual scalar shape used in Section 6 for the translated
endpoint function. -/
def EventuallyTranslatedEndpointPaperBounds (eta : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    1 ≤ translatedEndpointReal eta X ∧
    (1 : ℝ) / 2 ≤
      translatedEndpointReal eta (X + 1) - translatedEndpointReal eta X ∧
    translatedEndpointReal eta (X + 1) - translatedEndpointReal eta X ≤ 1 ∧
    (((X / 2 : ℕ) : ℝ) ≤ translatedEndpointReal eta X ∧
      translatedEndpointReal eta X ≤ (X : ℝ))

/-- A lower one-step increment of `1/2` already makes the real translated
endpoint monotone on the entire eventual tail. -/
theorem translatedEndpointReal_monotone_of_paperBounds
    {eta : ℝ}
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    ∃ X₀ : ℕ, ∀ {a b : ℕ}, X₀ ≤ a → a ≤ b →
      translatedEndpointReal eta a ≤ translatedEndpointReal eta b := by
  rcases hpaper with ⟨X₀, hpaper⟩
  refine ⟨X₀, ?_⟩
  intro a b ha hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n han ihn =>
      have hX₀n : X₀ ≤ n := ha.trans han
      have hstep := (hpaper n hX₀n).2.1
      have hmonoStep :
          translatedEndpointReal eta n ≤ translatedEndpointReal eta (n + 1) := by
        linarith
      exact ihn.trans hmonoStep

/-- Two consecutive paper increments give the unit gain over two source steps
used to force fibres of `ν_η` to have size at most two. -/
theorem translatedEndpointReal_twoStep_of_paperBounds
    {eta : ℝ}
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      translatedEndpointReal eta X + 1 ≤
        translatedEndpointReal eta (X + 2) := by
  rcases hpaper with ⟨X₀, hpaper⟩
  refine ⟨X₀, ?_⟩
  intro X hX
  have h₁ := (hpaper X hX).2.1
  have hXsucc : X₀ ≤ X + 1 := by omega
  have h₂ := (hpaper (X + 1) hXsucc).2.1
  norm_num [Nat.add_assoc] at h₂ ⊢
  linarith

/-- The paper-shaped one-step bounds imply exactly the real package consumed by
`TranslatedEndpointFloor`. -/
theorem translatedEndpointRealBounds_of_paperBounds
    {eta : ℝ}
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    ∃ X₀ : ℕ,
      (∀ X : ℕ, X₀ ≤ X → 0 ≤ translatedEndpointReal eta X) ∧
      (∀ {a b : ℕ}, X₀ ≤ a → a ≤ b →
        translatedEndpointReal eta a ≤ translatedEndpointReal eta b) ∧
      (∀ X : ℕ, X₀ ≤ X →
        translatedEndpointReal eta X + 1 ≤
          translatedEndpointReal eta (X + 2)) := by
  rcases hpaper with ⟨X₀, hpaper⟩
  have hpaper' : EventuallyTranslatedEndpointPaperBounds eta := ⟨X₀, hpaper⟩
  rcases translatedEndpointReal_monotone_of_paperBounds hpaper' with
    ⟨Xm, hmono⟩
  rcases translatedEndpointReal_twoStep_of_paperBounds hpaper' with
    ⟨Xt, htwo⟩
  let X₁ := max X₀ (max Xm Xt)
  refine ⟨X₁, ?_, ?_, ?_⟩
  · intro X hX
    have hX₀ : X₀ ≤ X := le_trans (Nat.le_max_left _ _) hX
    linarith [(hpaper X hX₀).1]
  · intro a b ha hab
    have hXm : Xm ≤ a := by
      exact le_trans (le_trans (Nat.le_max_left Xm Xt) (Nat.le_max_right X₀ (max Xm Xt))) ha
    exact hmono hXm hab
  · intro X hX
    have hXt : Xt ≤ X := by
      exact le_trans (le_trans (Nat.le_max_right Xm Xt) (Nat.le_max_right X₀ (max Xm Xt))) hX
    exact htwo X hXt

/-- The paper's exact increment bounds therefore imply the discrete step
control of the actual integer map `ν_η`. -/
theorem eventuallyTranslatedEndpointStepControl_of_paperBounds
    {eta : ℝ}
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    EventuallyTranslatedEndpointStepControl (translatedEndpointMap eta) := by
  exact eventuallyTranslatedEndpointStepControl_of_realBounds
    (translatedEndpointRealBounds_of_paperBounds hpaper)

/-- Consequently every translated value has at most two preimages on each
sufficiently late dyadic source block. -/
theorem eventuallyBoundedTranslatedEndpointFibres_two_of_paperBounds
    {eta : ℝ} {target : ℕ → Finset ℕ}
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    EventuallyBoundedTranslatedEndpointFibres (translatedEndpointMap eta) target 2 := by
  exact eventuallyBoundedTranslatedEndpointFibres_two_of_stepControl
    (eventuallyTranslatedEndpointStepControl_of_paperBounds hpaper)

/-- The envelope contained in the paper-shaped package gives the coarse
comparability `X/2 ≤ ν_η(X) ≤ X` after flooring. -/
theorem eventuallyTranslatedEndpointComparable_of_paperBounds
    {eta : ℝ}
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    EventuallyTranslatedEndpointComparable (translatedEndpointMap eta) := by
  rcases hpaper with ⟨X₀, hpaper⟩
  apply eventuallyTranslatedEndpointComparable_of_realEnvelope
  refine ⟨X₀, ?_⟩
  intro X hX
  exact (hpaper X hX).2.2.2

/-- Full Section 6 sparsity pullback for the concrete translated endpoint,
assuming only the manuscript's eventual scalar bounds and a sparse family of
integer exceptional values. -/
theorem eventuallyDyadicallySparse_pulledBack_translatedEndpointMap_of_paperBounds
    {eta : ℝ} {target : ℕ → Finset ℕ}
    (hsparse : EventuallyDyadicallySparse target)
    (hpaper : EventuallyTranslatedEndpointPaperBounds eta) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y (translatedEndpointMap eta) (target Y)) := by
  exact eventuallyDyadicallySparse_pulledBack_of_stepControl hsparse
    (eventuallyTranslatedEndpointStepControl_of_paperBounds hpaper)

end DivisorF
