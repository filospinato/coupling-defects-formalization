import DivisorF.ExceptionalEndpointTransfer
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite multiplicity counting for translated exceptional endpoints

The Section 6 pullback through `ν_η` uses only one finite combinatorial fact:
inside a dyadic block, every exceptional translated value has uniformly bounded
many preimages.  `ExceptionalEndpointTransfer` previously packaged that fact
only as the already-counted inequality

`#pullback ≤ M * #target`.

This module exposes the underlying fibres and proves that inequality from the
pointwise fibre bound.  Thus the eventual sparsity transfer no longer needs an
opaque counting hypothesis: the remaining concrete `ν_η` obligation is exactly
to bound each finite fibre (the manuscript obtains a bound from the eventual
increment estimate for `X ↦ floor (X - 3 X^η)`).

No analytic prime-distribution input occurs here.
-/

namespace DivisorF

/-- Preimage of one translated endpoint value inside the dyadic source block
`[Y,2Y)`. -/
def translatedEndpointFibre
    (Y : ℕ) (ν : ℕ → ℕ) (y : ℕ) : Finset ℕ :=
  (Finset.Ico Y (2 * Y)).filter (fun X => ν X = y)

@[simp]
theorem mem_translatedEndpointFibre
    {Y X y : ℕ} {ν : ℕ → ℕ} :
    X ∈ translatedEndpointFibre Y ν y ↔
      Y ≤ X ∧ X < 2 * Y ∧ ν X = y := by
  simp [translatedEndpointFibre, and_assoc]

/-- The pullback of a finite target is exactly the union of its translated
endpoint fibres. -/
theorem pulledBackBadEndpoints_eq_biUnion_fibres
    (Y : ℕ) (ν : ℕ → ℕ) (E : Finset ℕ) :
    pulledBackBadEndpoints Y ν E =
      E.biUnion (translatedEndpointFibre Y ν) := by
  ext X
  simp [pulledBackBadEndpoints, translatedEndpointFibre, and_assoc]
  aesop

/-- Finite bounded-multiplicity counting lemma used by the `ν_η` construction.
If every target value has at most `M` source endpoints in one dyadic block, the
whole exceptional pullback has size at most `M #E`. -/
theorem pulledBackBadEndpoints_card_le_mul_of_fibre_bound
    {Y M : ℕ} {ν : ℕ → ℕ} {E : Finset ℕ}
    (hfibre : ∀ y ∈ E, (translatedEndpointFibre Y ν y).card ≤ M) :
    (pulledBackBadEndpoints Y ν E).card ≤ M * E.card := by
  rw [pulledBackBadEndpoints_eq_biUnion_fibres]
  calc
    (E.biUnion (translatedEndpointFibre Y ν)).card
        ≤ ∑ y ∈ E, (translatedEndpointFibre Y ν y).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ E, M := by
      exact Finset.sum_le_sum fun y hy => hfibre y hy
    _ = M * E.card := by
      simp [Nat.mul_comm]

/-- Eventual pointwise fibre bound for the translated map.  This is the exact
finite property that the concrete `ν_η` arithmetic has to establish. -/
def EventuallyBoundedTranslatedEndpointFibres
    (ν : ℕ → ℕ) (target : ℕ → Finset ℕ) (M : ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    ∀ y ∈ target Y, (translatedEndpointFibre Y ν y).card ≤ M

/-- A pointwise eventual fibre bound implies the older packaged pullback-count
interface. -/
theorem eventuallyBoundedExceptionalPullback_of_fibre_bound
    {ν : ℕ → ℕ} {target : ℕ → Finset ℕ} {M : ℕ}
    (hfibre : EventuallyBoundedTranslatedEndpointFibres ν target M) :
    EventuallyBoundedExceptionalPullback ν target M := by
  rcases hfibre with ⟨Y₀, hfibre⟩
  refine ⟨Y₀, ?_⟩
  intro Y hY
  exact pulledBackBadEndpoints_card_le_mul_of_fibre_bound (hfibre Y hY)

/-- Direct sparsity-transfer interface from the pointwise fibre bound. -/
theorem eventuallyDyadicallySparse_pulledBack_of_fibre_bound
    {ν : ℕ → ℕ} {target : ℕ → Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M)
    (htarget : EventuallyDyadicallySparse target)
    (hfibre : EventuallyBoundedTranslatedEndpointFibres ν target M) :
    EventuallyDyadicallySparse (fun Y => pulledBackBadEndpoints Y ν (target Y)) := by
  exact eventuallyDyadicallySparse_pulledBack_of_boundedMultiplicity hM htarget
    (eventuallyBoundedExceptionalPullback_of_fibre_bound hfibre)

end DivisorF
