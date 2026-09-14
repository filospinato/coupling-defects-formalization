import DivisorF.CumulativeLevels
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Cumulative nonbinary stability and rigidity

Original Proposition 3.10 consequences of the cumulative boundary slack
identity.  All accounting is performed in one fixed maximum spanning linear
forest; no endpoint profiles from incompatible optima are combined.
-/

namespace DivisorF

/-- Cumulative fibres of defect exactly one. -/
noncomputable def cumulativeDefectOneFibres (N K : ℕ) : Finset (LargePrime N) := by
  classical
  exact (cumulativeFibres N K).filter fun q => fibreDefect q = 1

@[simp]
theorem mem_cumulativeDefectOneFibres {N K : ℕ} {q : LargePrime N} :
    q ∈ cumulativeDefectOneFibres N K ↔
      q ∈ cumulativeFibres N K ∧ fibreDefect q = 1 := by
  classical
  simp [cumulativeDefectOneFibres]

/-- `n_1`: number of cumulative fibres of defect exactly one. -/
noncomputable def cumulativeDefectOneCount (N K : ℕ) : ℕ :=
  (cumulativeDefectOneFibres N K).card

/-- `b_K`: number of cumulative nonbinary fibres. -/
noncomputable def cumulativeNonbinaryCount (N K : ℕ) : ℕ :=
  (cumulativeLevelFibres N K 2).card

/-- `E_K = Σ_{D_B≥2}(D_B-2)`. -/
noncomputable def cumulativeNonbinaryExcess (N K : ℕ) : ℤ :=
  ∑ q ∈ cumulativeLevelFibres N K 2, (fibreDefect q - 2)

/-- The nonbinary excess is nonnegative. -/
theorem cumulativeNonbinaryExcess_nonneg {N K : ℕ} :
    0 ≤ cumulativeNonbinaryExcess N K := by
  unfold cumulativeNonbinaryExcess
  apply Finset.sum_nonneg
  intro q hq
  have htwo : (2 : ℤ) ≤ fibreDefect q :=
    (mem_cumulativeLevelFibres.mp hq).2
  omega

/-- `b_K ≤ K-1`, the numerical nonbinary bound from Corollary 3.9. -/
theorem cumulativeNonbinaryCount_le {N K : ℕ} :
    cumulativeNonbinaryCount N K ≤ K - 1 := by
  exact cumulativeNonbinary_card_le (N := N) (K := K)

/--
Exact arithmetic decomposition

`Σ_B D_B = n_1 + 2 b_K + E_K`.
-/
theorem cumulativeDefectSum_decomposition {N K : ℕ} :
    cumulativeDefectSum N K
      = (cumulativeDefectOneCount N K : ℤ)
        + 2 * (cumulativeNonbinaryCount N K : ℤ)
        + cumulativeNonbinaryExcess N K := by
  classical
  unfold cumulativeDefectSum
  calc
    ∑ q ∈ cumulativeFibres N K, fibreDefect q
        = ∑ q ∈ cumulativeFibres N K,
            ((if fibreDefect q = 1 then (1 : ℤ) else 0)
              + if (2 : ℤ) ≤ fibreDefect q then
                  2 + (fibreDefect q - 2)
                else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          have hnonneg := fibreDefect_nonneg q
          split_ifs with h1 h2
          · omega
          · omega
          · omega
          · omega
    _ = (cumulativeDefectOneCount N K : ℤ)
        + 2 * (cumulativeNonbinaryCount N K : ℤ)
        + cumulativeNonbinaryExcess N K := by
          simp only [Finset.sum_add_distrib]
          unfold cumulativeDefectOneCount cumulativeDefectOneFibres
          unfold cumulativeNonbinaryCount cumulativeNonbinaryExcess
          unfold cumulativeLevelFibres
          simp [Finset.sum_filter]
          ring

/--
**Proposition 3.10 candidate: nonbinary stability identity.**

For every maximum spanning linear forest `L`,

`2(K-1)-2b_K = u_K(L)+Σ_B ℓ_B(L)+n_1+E_K`.
-/
theorem nonbinaryStabilityIdentity
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N)) :
    (cumulativeBoundaryCapacity K : ℤ)
        - 2 * (cumulativeNonbinaryCount N K : ℤ)
      = (cumulativeUnusedCapacity K L : ℤ)
        + cumulativeRestrictionLoss K L
        + (cumulativeDefectOneCount N K : ℤ)
        + cumulativeNonbinaryExcess N K := by
  have hslack := globalBoundarySlackIdentity
    (N := N) (K := K) hL hmax
  rw [cumulativeDefectSum_decomposition] at hslack
  linarith

/--
At the extremal count `b_K=K-1`, every nonnegative term in the stability
identity vanishes.
-/
theorem extremalRigidity_terms_vanish
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    cumulativeUnusedCapacity K L = 0 ∧
      cumulativeRestrictionLoss K L = 0 ∧
      cumulativeDefectOneCount N K = 0 ∧
      cumulativeNonbinaryExcess N K = 0 := by
  have h := nonbinaryStabilityIdentity
    (N := N) (K := K) hL hmax
  have hloss := cumulativeRestrictionLoss_nonneg
    (N := N) (K := K) hL
  have hexcess := cumulativeNonbinaryExcess_nonneg (N := N) (K := K)
  have hcap : (cumulativeBoundaryCapacity K : ℤ) = 2 * ((K - 1 : ℕ) : ℤ) := by
    simp [cumulativeBoundaryCapacity]
  rw [hcap, hsat] at h
  constructor
  · exact_mod_cast (by omega : (cumulativeUnusedCapacity K L : ℤ) = 0)
  constructor
  · omega
  constructor
  · exact_mod_cast (by omega : (cumulativeDefectOneCount N K : ℤ) = 0)
  · omega

/-- Extremality excludes every defect-one fibre in the cumulative family. -/
theorem no_defect_one_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    cumulativeDefectOneFibres N K = ∅ := by
  have hterms := extremalRigidity_terms_vanish
    (N := N) (K := K) (L := L) hL hmax hsat
  have hzero := hterms.2.2.1
  apply Finset.card_eq_zero.mp
  exact hzero

/-- Every nonbinary cumulative fibre has defect exactly two at extremality. -/
theorem fibreDefect_eq_two_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N}
    (hq : q ∈ cumulativeLevelFibres N K 2) :
    fibreDefect q = 2 := by
  have hterms := extremalRigidity_terms_vanish
    (N := N) (K := K) (L := L) hL hmax hsat
  have hexcess0 := hterms.2.2.2
  have hsumzero :
      (∑ r ∈ cumulativeLevelFibres N K 2, (fibreDefect r - 2)) = 0 := by
    simpa [cumulativeNonbinaryExcess] using hexcess0
  have hallzero :
      ∀ r ∈ cumulativeLevelFibres N K 2, fibreDefect r - 2 = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun r hr => by
        have htwo := (mem_cumulativeLevelFibres.mp hr).2
        omega)).1 hsumzero
  have hqzero := hallzero q hq
  omega

/--
Near-extremal rigidity in a truncation-free natural formulation: if
`b_K+h=K-1`, then all deviations from the rigid pattern have total mass `2h`.
-/
theorem nearExtremalRigidityIdentity
    {N K h : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hcount : cumulativeNonbinaryCount N K + h = K - 1) :
    (cumulativeUnusedCapacity K L : ℤ)
        + cumulativeRestrictionLoss K L
        + (cumulativeDefectOneCount N K : ℤ)
        + cumulativeNonbinaryExcess N K
      = 2 * (h : ℤ) := by
  have hstab := nonbinaryStabilityIdentity
    (N := N) (K := K) hL hmax
  have hcap : (cumulativeBoundaryCapacity K : ℤ) = 2 * ((K - 1 : ℕ) : ℤ) := by
    simp [cumulativeBoundaryCapacity]
  rw [hcap] at hstab
  have hcountz :
      (cumulativeNonbinaryCount N K : ℤ) + (h : ℤ) = ((K - 1 : ℕ) : ℤ) := by
    exact_mod_cast hcount
  linarith

end DivisorF
