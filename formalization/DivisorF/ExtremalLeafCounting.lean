import DivisorF.ExtremalRightCounting
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extremal right-leaf and contracted-count arithmetic

This module advances the concrete counting part of the original Corollary 3.11.
The previous layer proves that an extremal nonbinary fibre activates either one
or two post-cut restriction components, and that the total number of active
right components is `K-1+a`, where `a` counts the fibres whose two crossings
land on distinct fibre paths.

Here we package the corresponding right-leaf contribution and prove its exact
total `2a`.  We also record the exact contracted vertex/edge arithmetic that
will yield `a` connected components once the concrete incidence graph is shown
to be a forest with these nodes and retained crossings.
-/

namespace DivisorF

noncomputable local instance leafLargePrimeDecidableEq {N : ℕ} :
    DecidableEq (LargePrime N) :=
  Classical.decEq _

/--
A nonbinary fibre contributes two right leaves exactly when it splits its two
crossings between two distinct active restriction components; otherwise it
contributes none.
-/
noncomputable def activeRightLeafContribution
    {N K : ℕ} (q : LargePrime N) (L : SimpleGraph (HVertex N)) : ℕ :=
  if activeFibreRestrictionComponentCount (K := K) q L = 2 then 2 else 0

/--
On the cumulative nonbinary family, the leaf contribution is precisely the
indicator of membership in `splitNonbinaryFibres`, weighted by two.
-/
theorem activeRightLeafContribution_eq_split_indicator
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2) :
    activeRightLeafContribution (K := K) q L =
      if q ∈ splitNonbinaryFibres N K L then 2 else 0 := by
  classical
  simp [activeRightLeafContribution, mem_splitNonbinaryFibres, hq]

/-- Total number of degree-one right nodes predicted by the fibre profile. -/
noncomputable def totalActiveRightLeafCount
    (N K : ℕ) (L : SimpleGraph (HVertex N)) : ℕ :=
  ∑ q ∈ cumulativeLevelFibres N K 2,
    activeRightLeafContribution (K := K) q L

/--
**Corollary 3.11 leaf count:** if `a` fibres split, the active right side has
exactly `2a` degree-one nodes.
-/
theorem totalActiveRightLeafCount_eq_two_mul_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)} :
    totalActiveRightLeafCount N K L = 2 * splitNonbinaryFibreCount N K L := by
  classical
  unfold totalActiveRightLeafCount splitNonbinaryFibreCount
  calc
    (∑ q ∈ cumulativeLevelFibres N K 2,
        activeRightLeafContribution (K := K) q L)
        = ∑ q ∈ cumulativeLevelFibres N K 2,
            if q ∈ splitNonbinaryFibres N K L then 2 else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              exact activeRightLeafContribution_eq_split_indicator hq
    _ = ∑ q ∈ splitNonbinaryFibres N K L, 2 := by
          have hsub :
              splitNonbinaryFibres N K L ⊆ cumulativeLevelFibres N K 2 := by
            intro q hq
            exact (mem_splitNonbinaryFibres.mp hq).1
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    _ = 2 * (splitNonbinaryFibres N K L).card := by
          simp [Nat.mul_comm]

/--
Total active-node count of the contracted incidence profile: `K-1` boundary
singletons plus all active right restriction components.
-/
noncomputable def extremalContractedVertexCount
    (N K : ℕ) (L : SimpleGraph (HVertex N)) : ℕ :=
  (K - 1) +
    ∑ q ∈ cumulativeLevelFibres N K 2,
      activeFibreRestrictionComponentCount (K := K) q L

/--
At extremality the contracted incidence profile has exactly `2(K-1)+a`
vertices.
-/
theorem extremalContractedVertexCount_eq
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    extremalContractedVertexCount N K L =
      2 * (K - 1) + splitNonbinaryFibreCount N K L := by
  unfold extremalContractedVertexCount
  rw [sum_activeFibreRestrictionComponentCount_eq_boundary_add_split
    hL hmax hsat]
  omega

/--
The retained incidence-edge count in the extremal profile.  Every one of the
`K-1` nonbinary fibres has exactly two selected crossings.
-/
noncomputable def extremalContractedEdgeCount (_N K : ℕ) : ℕ :=
  2 * (K - 1)

/--
The finite-forest Euler deficit of the intended contracted profile is exactly
`a`.  Once the concrete contraction is shown to preserve acyclicity and to
realize these node/edge counts, this becomes the connected-component count in
Corollary 3.11.
-/
theorem extremalContractedVertexCount_sub_edgeCount_eq_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    extremalContractedVertexCount N K L - extremalContractedEdgeCount N K =
      splitNonbinaryFibreCount N K L := by
  rw [extremalContractedVertexCount_eq hL hmax hsat]
  unfold extremalContractedEdgeCount
  omega

end DivisorF
