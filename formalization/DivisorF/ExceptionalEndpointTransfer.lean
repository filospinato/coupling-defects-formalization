import DivisorF.TranslatedRegularEndpoint

set_option linter.style.header false

/-!
# Sparse exceptional endpoints under the translated map

Section 6 does not use the integer exceptional set directly.  It first replaces
an endpoint `X` by the translated integer `nu_eta(X)`, and calls `X` irregular
when that translated integer is exceptional.  The manuscript proves that
`X ↦ nu_eta(X)` has bounded multiplicity and is comparable with `X`; therefore
an `o(Y)` exceptional set remains `o(Y)` after pullback, after enlarging to a
bounded number of adjacent dyadic blocks.

This module formalizes that project-owned counting transfer.  The analytic
construction of the integer exceptional set remains outside the formalization;
its only output here is dyadic sparsity.  Likewise, the calculus estimates used
to prove bounded multiplicity/comparability of the concrete power map are kept
as explicit finite hypotheses until the concrete `nu_eta` arithmetic layer is
instantiated.
-/

namespace DivisorF

/-- Division-free `o(Y)` for a family of finite exceptional endpoint sets.
For every reciprocal precision `1/C`, eventually the exceptional cardinality is
at most `Y/C`. -/
def EventuallyDyadicallySparse (E : ℕ → Finset ℕ) : Prop :=
  ∀ C : ℕ, 1 ≤ C → ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (E Y).card * C ≤ Y

/-- Pull back a finite exceptional set through an integer endpoint map, while
restricting to the manuscript's dyadic endpoint block `[Y,2Y)`. -/
def pulledBackBadEndpoints
    (Y : ℕ) (ν : ℕ → ℕ) (E : Finset ℕ) : Finset ℕ :=
  (Finset.Ico Y (2 * Y)).filter (fun X => ν X ∈ E)

@[simp]
theorem mem_pulledBackBadEndpoints
    {Y X : ℕ} {ν : ℕ → ℕ} {E : Finset ℕ} :
    X ∈ pulledBackBadEndpoints Y ν E ↔
      Y ≤ X ∧ X < 2 * Y ∧ ν X ∈ E := by
  simp [pulledBackBadEndpoints, and_assoc]

/-- Abstract finite bounded-multiplicity estimate needed for the concrete
`nu_eta` map.  It records exactly the counting consequence of the manuscript's
statement that each integer has only `O(1)` preimages. -/
def EventuallyBoundedExceptionalPullback
    (ν : ℕ → ℕ) (target : ℕ → Finset ℕ) (M : ℕ) : Prop :=
  ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
    (pulledBackBadEndpoints Y ν (target Y)).card ≤ M * (target Y).card

/-- **Section 6 bounded-multiplicity sparsity transfer.**

If the integer exceptional values form an `o(Y)` family and pullback through
the translated endpoint map costs only a fixed multiplicity factor `M`, then
the irregular quotient endpoints are still `o(Y)`.  This is the exact
counting step used in the manuscript after the `nu_eta` construction. -/
theorem eventuallyDyadicallySparse_pulledBack_of_boundedMultiplicity
    {ν : ℕ → ℕ} {target : ℕ → Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M)
    (hsparse : EventuallyDyadicallySparse target)
    (hpull : EventuallyBoundedExceptionalPullback ν target M) :
    EventuallyDyadicallySparse
      (fun Y => pulledBackBadEndpoints Y ν (target Y)) := by
  rcases hpull with ⟨Ypull, hpull⟩
  intro C hC
  have hMC : 1 ≤ M * C := by
    calc
      1 = 1 * 1 := by simp
      _ ≤ M * C := Nat.mul_le_mul hM hC
  rcases hsparse (M * C) hMC with ⟨Ysparse, hsparse⟩
  refine ⟨max Ypull Ysparse, ?_⟩
  intro Y hY
  have hYpull : Ypull ≤ Y := le_trans (Nat.le_max_left _ _) hY
  have hYsparse : Ysparse ≤ Y := le_trans (Nat.le_max_right _ _) hY
  calc
    (pulledBackBadEndpoints Y ν (target Y)).card * C
        ≤ (M * (target Y).card) * C :=
          Nat.mul_le_mul_right C (hpull Y hYpull)
    _ = (target Y).card * (M * C) := by ac_rfl
    _ ≤ Y := hsparse Y hYsparse

/-- The same transfer with a direct one-scale cardinality hypothesis.  This is
useful when the concrete `nu_eta` arithmetic supplies the multiplicity estimate
block by block rather than through the packaged eventual predicate. -/
theorem pulledBackBadEndpoints_card_mul_le
    {Y M C : ℕ} {ν : ℕ → ℕ} {E : Finset ℕ}
    (hpull : (pulledBackBadEndpoints Y ν E).card ≤ M * E.card)
    (hsmall : E.card * (M * C) ≤ Y) :
    (pulledBackBadEndpoints Y ν E).card * C ≤ Y := by
  calc
    (pulledBackBadEndpoints Y ν E).card * C
        ≤ (M * E.card) * C := Nat.mul_le_mul_right C hpull
    _ = E.card * (M * C) := by ac_rfl
    _ ≤ Y := hsmall

/-- Package the manuscript's definition of regularity: an endpoint is bad
exactly when its translated value belongs to the integer exceptional set. -/
theorem not_mem_pulledBackBadEndpoints_iff_translated_regular
    {Y X : ℕ} {ν : ℕ → ℕ} {E : Finset ℕ}
    (hX : X ∈ Finset.Ico Y (2 * Y)) :
    X ∉ pulledBackBadEndpoints Y ν E ↔ ν X ∉ E := by
  simp [pulledBackBadEndpoints, hX]

end DivisorF
