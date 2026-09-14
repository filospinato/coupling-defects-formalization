import DivisorF.CumulativeBoundary
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Global boundary slack

Exact Section 3.4 accounting in one common maximum spanning linear forest.
-/

namespace DivisorF

open scoped BigOperators

/-- Total side-restriction loss of the cumulative family in a fixed forest. -/
noncomputable def cumulativeRestrictionLoss {N : ℕ} (K : ℕ)
    (L : SimpleGraph (HVertex N)) : ℤ :=
  ∑ q ∈ cumulativeFibres N K,
    (fibreRestrictionLoss q L + complementRestrictionLoss q L)

/-- Unused or diverted cumulative boundary capacity `u_K(L)`. -/
noncomputable def cumulativeUnusedCapacity {N : ℕ} (K : ℕ)
    (L : SimpleGraph (HVertex N)) : ℕ :=
  cumulativeBoundaryCapacity K - cumulativeCrossingMass K L

/-- Total side-restriction loss is nonnegative in every linear forest. -/
theorem cumulativeRestrictionLoss_nonneg
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    0 ≤ cumulativeRestrictionLoss K L := by
  unfold cumulativeRestrictionLoss
  apply Finset.sum_nonneg
  intro q _
  exact add_nonneg
    (fibreRestrictionLoss_nonneg q hL)
    (complementRestrictionLoss_nonneg q hL)

/-- Summed exact decomposition `Σ_B D_B = Σ_B m_B(L) - Σ_B ℓ_B(L)`. -/
theorem cumulativeDefectSum_eq_crossing_sub_losses
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N)) :
    cumulativeDefectSum N K
      = (cumulativeCrossingMass K L : ℤ) - cumulativeRestrictionLoss K L := by
  unfold cumulativeDefectSum cumulativeCrossingMass cumulativeRestrictionLoss
  calc
    ∑ q ∈ cumulativeFibres N K, fibreDefect q
        = ∑ q ∈ cumulativeFibres N K,
            ((crossingCount q L : ℤ)
              - fibreRestrictionLoss q L
              - complementRestrictionLoss q L) := by
          apply Finset.sum_congr rfl
          intro q _
          exact fibreDefect_eq_crossing_sub_losses q hmax
    _ = (∑ q ∈ cumulativeFibres N K, (crossingCount q L : ℤ))
          - ∑ q ∈ cumulativeFibres N K,
              (fibreRestrictionLoss q L + complementRestrictionLoss q L) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          ring
    _ = ((∑ q ∈ cumulativeFibres N K, crossingCount q L : ℕ) : ℤ)
          - ∑ q ∈ cumulativeFibres N K,
              (fibreRestrictionLoss q L + complementRestrictionLoss q L) := by
          norm_cast

/-- Cast form of `u_K(L)=2(K-1)-Σ_B m_B(L)`. -/
theorem cumulativeUnusedCapacity_cast
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    (cumulativeUnusedCapacity K L : ℤ)
      = (cumulativeBoundaryCapacity K : ℤ) - cumulativeCrossingMass K L := by
  unfold cumulativeUnusedCapacity
  rw [Int.ofNat_sub]
  exact cumulativeCrossingMass_le hL

/--
**Theorem 3.8 candidate.** For every maximum spanning linear forest `L`,

`2(K-1)-Σ_B D_B = u_K(L)+Σ_B ℓ_B(L)`.
-/
theorem globalBoundarySlackIdentity
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N)) :
    (cumulativeBoundaryCapacity K : ℤ) - cumulativeDefectSum N K
      = cumulativeUnusedCapacity K L + cumulativeRestrictionLoss K L := by
  rw [cumulativeDefectSum_eq_crossing_sub_losses hmax,
    cumulativeUnusedCapacity_cast hL]
  ring

end DivisorF
