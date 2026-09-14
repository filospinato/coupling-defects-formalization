import DivisorF.ExceptionalEndpointMultiplicity
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Geometry of translated endpoint maps

The Section 6 map `ν_η(X) = floor (X - 3 X^η)` is used in two purely discrete
ways after the real-variable increment estimate has been proved:

* it is eventually nondecreasing and advances by at least one integer every two
  source steps, so every integer value has at most two preimages;
* it is comparable with the source endpoint, so a dyadic source block maps into
  a bounded enlargement of comparable endpoint scales.

This module formalizes those project-owned discrete consequences.  It does not
prove the calculus estimate for `X - 3 X^η`, and it contains no prime-distribution
input.  The remaining concrete `ν_η` obligation is therefore reduced to the
real-power/floor bridge establishing the two eventual scalar properties below.
-/

namespace DivisorF

/-- Eventual discrete step control sufficient for the translated map.  Beyond
`X₀`, the map is monotone and every two source steps strictly increase its
integer value.  The manuscript obtains this for `ν_η` from
`1/2 ≤ g_η(X+1)-g_η(X) ≤ 1`. -/
def EventuallyTranslatedEndpointStepControl (ν : ℕ → ℕ) : Prop :=
  ∃ X₀ : ℕ,
    (∀ {a b : ℕ}, X₀ ≤ a → a ≤ b → ν a ≤ ν b) ∧
    (∀ a : ℕ, X₀ ≤ a → ν a < ν (a + 2))

/-- Eventual dyadic comparability of the translated endpoint with its source.
The constants `1/2` and `1` are deliberately coarse: `ν_η(X) ∼ X` is much
stronger, while these bounds are exactly enough to keep the image of `[Y,2Y)`
inside a bounded union of comparable dyadic blocks. -/
def EventuallyTranslatedEndpointComparable (ν : ℕ → ℕ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → X / 2 ≤ ν X ∧ ν X ≤ X

/-- Under eventual step control, equal translated values can occur only at
adjacent source endpoints. -/
theorem translatedEndpoint_eq_forces_adjacent
    {ν : ℕ → ℕ} {X₀ a b : ℕ}
    (hmono : ∀ {u v : ℕ}, X₀ ≤ u → u ≤ v → ν u ≤ ν v)
    (htwo : ∀ u : ℕ, X₀ ≤ u → ν u < ν (u + 2))
    (ha : X₀ ≤ a) (_hab : a ≤ b) (heq : ν a = ν b) :
    b ≤ a + 1 := by
  by_contra h
  have ha2b : a + 2 ≤ b := by omega
  have hstep : ν a < ν (a + 2) := htwo a ha
  have ha2 : X₀ ≤ a + 2 := by omega
  have htail : ν (a + 2) ≤ ν b := hmono ha2 ha2b
  omega

/-- Every fibre of an eventually controlled translated endpoint map has at most
two elements on every sufficiently late dyadic source block.  This is the
bounded-multiplicity assertion used in the manuscript's pullback of the integer
exceptional set. -/
theorem eventuallyBoundedTranslatedEndpointFibres_two_of_stepControl
    {ν : ℕ → ℕ} {target : ℕ → Finset ℕ}
    (hstep : EventuallyTranslatedEndpointStepControl ν) :
    EventuallyBoundedTranslatedEndpointFibres ν target 2 := by
  rcases hstep with ⟨X₀, hmono, htwo⟩
  refine ⟨X₀, ?_⟩
  intro Y hY y _hy
  let F := translatedEndpointFibre Y ν y
  by_cases hF : F.Nonempty
  · let m : ℕ := F.min' hF
    have hmF : m ∈ F := F.min'_mem hF
    have hmY : Y ≤ m := (mem_translatedEndpointFibre.mp hmF).1
    have hmX₀ : X₀ ≤ m := le_trans hY hmY
    have hmval : ν m = y := (mem_translatedEndpointFibre.mp hmF).2.2
    have hsub : F ⊆ ({m, m + 1} : Finset ℕ) := by
      intro x hx
      have hmx : m ≤ x := F.min'_le x hx
      have hxval : ν x = y := (mem_translatedEndpointFibre.mp hx).2.2
      have hxclose : x ≤ m + 1 :=
        translatedEndpoint_eq_forces_adjacent hmono htwo hmX₀ hmx
          (hmval.trans hxval.symm)
      have : x = m ∨ x = m + 1 := by omega
      simp [this]
    calc
      F.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 2 := by simp
  · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 2
    simp [hEmpty]

/-- Consequently, dyadic sparsity survives the translated pullback with the
fixed multiplicity constant `2`, once the discrete two-step control is known. -/
theorem eventuallyDyadicallySparse_pulledBack_of_stepControl
    {ν : ℕ → ℕ} {target : ℕ → Finset ℕ}
    (hsparse : EventuallyDyadicallySparse target)
    (hstep : EventuallyTranslatedEndpointStepControl ν) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y ν (target Y)) := by
  exact eventuallyDyadicallySparse_pulledBack_of_fibre_bound
    (by decide : 1 ≤ 2) hsparse
    (eventuallyBoundedTranslatedEndpointFibres_two_of_stepControl hstep)

/-- Eventual comparability sends every late source point in `[Y,2Y)` into the
coarse comparable interval `[Y/2,2Y)`.  This is the finite range fact needed to
replace one target dyadic block by a bounded number of adjacent blocks. -/
theorem translatedEndpoint_mem_comparableInterval
    {ν : ℕ → ℕ}
    (hcomp : EventuallyTranslatedEndpointComparable ν) :
    ∃ Y₀ : ℕ, ∀ Y X : ℕ, Y₀ ≤ Y →
      X ∈ Finset.Ico Y (2 * Y) →
      ν X ∈ Finset.Ico (Y / 2) (2 * Y) := by
  rcases hcomp with ⟨X₀, hcomp⟩
  refine ⟨X₀, ?_⟩
  intro Y X hY hXY
  have hYX : Y ≤ X := (Finset.mem_Ico.mp hXY).1
  have hX2Y : X < 2 * Y := (Finset.mem_Ico.mp hXY).2
  have hX₀X : X₀ ≤ X := le_trans hY hYX
  rcases hcomp X hX₀X with ⟨hlower, hupper⟩
  apply Finset.mem_Ico.mpr
  constructor
  · have hhalf : Y / 2 ≤ X / 2 := Nat.div_le_div_right hYX
    exact le_trans hhalf hlower
  · exact lt_of_le_of_lt hupper hX2Y

end DivisorF
