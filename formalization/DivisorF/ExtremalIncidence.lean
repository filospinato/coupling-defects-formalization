import DivisorF.ExtremalBoundary
import DivisorF.ExtremalFibre
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extremal counted-incidence layer

Concrete incidence consequences for the original Corollary 3.11.  Under the
extremal hypothesis `b_K = K-1`, every cumulative fibre outside the nonbinary
level has zero selected crossings, every nonbinary fibre has exactly two, and
the whole selected boundary incidence set is therefore exactly the disjoint
union of the nonbinary crossing sets.

This module deliberately stops before contracting fibre-restriction path
components; that contraction is the next geometric layer.
-/

namespace DivisorF

open SimpleGraph

/-- Selected crossings contributed by the cumulative nonbinary fibres. -/
noncomputable def nonbinaryCrossingUnion
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    Finset (Sym2 (HVertex N)) :=
  crossingUnion (cumulativeLevelFibres N K 2) L

/--
At extremality a cumulative fibre outside the nonbinary level contributes no
selected crossing edge at all.
-/
theorem crossingFinset_eq_empty_of_not_nonbinary_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeFibres N K)
    (hqnot : q ∉ cumulativeLevelFibres N K 2) :
    crossingFinset q L = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [card_crossingFinset]
  exact crossingCount_eq_zero_of_not_nonbinary_extremal hL hmax hsat hq hqnot

/--
At extremality the crossing union of all cumulative fibres is already the
crossing union of the nonbinary fibres.
-/
theorem cumulativeCrossingUnion_eq_nonbinaryCrossingUnion_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    crossingUnion (cumulativeFibres N K) L = nonbinaryCrossingUnion N K L := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    rw [crossingUnion, Finset.mem_biUnion] at he
    obtain ⟨q, hqcum, hqe⟩ := he
    by_cases hqnb : q ∈ cumulativeLevelFibres N K 2
    · rw [nonbinaryCrossingUnion, crossingUnion, Finset.mem_biUnion]
      exact ⟨q, hqnb, hqe⟩
    · have hempty := crossingFinset_eq_empty_of_not_nonbinary_extremal
        hL hmax hsat hqcum hqnb
      rw [hempty] at hqe
      simp at hqe
  · intro e he
    rw [nonbinaryCrossingUnion, crossingUnion, Finset.mem_biUnion] at he
    obtain ⟨q, hqnb, hqe⟩ := he
    have hqcum := (mem_cumulativeLevelFibres.mp hqnb).1
    rw [crossingUnion, Finset.mem_biUnion]
    exact ⟨q, hqcum, hqe⟩

/--
**Corollary 3.11 incidence input:** under extremality, every selected edge
incident to the common boundary is a crossing of a nonbinary counted fibre,
and conversely.
-/
theorem incidentEdges_eq_nonbinaryCrossingUnion_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    incidentEdgesOn L (smallEndpointVertices N K) =
      nonbinaryCrossingUnion N K L := by
  rw [incidentEdges_eq_cumulativeCrossingUnion_of_extremal hKN hL hmax hsat,
      cumulativeCrossingUnion_eq_nonbinaryCrossingUnion_of_extremal hL hmax hsat]

/-- Every extremal nonbinary fibre contributes exactly two crossing edges. -/
theorem card_crossingFinset_eq_two_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2) :
    (crossingFinset q L).card = 2 := by
  rw [card_crossingFinset]
  exact crossingCount_eq_two_of_extremal hL hmax hsat hq

/--
Every selected boundary-incidence edge belongs to at least one nonbinary fibre.
-/
theorem exists_nonbinary_fibre_for_boundary_edge_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {e : Sym2 (HVertex N)}
    (he : e ∈ incidentEdgesOn L (smallEndpointVertices N K)) :
    ∃ q ∈ cumulativeLevelFibres N K 2, e ∈ crossingFinset q L := by
  have he' : e ∈ nonbinaryCrossingUnion N K L := by
    rw [← incidentEdges_eq_nonbinaryCrossingUnion_of_extremal hKN hL hmax hsat]
    exact he
  rw [nonbinaryCrossingUnion, crossingUnion, Finset.mem_biUnion] at he'
  exact he'

/--
The nonbinary fibre attached to a selected boundary-incidence edge is unique.
This uses the already-formalized disjointness of crossing sets of distinct
large-prime fibres.
-/
theorem unique_nonbinary_fibre_for_boundary_edge_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {e : Sym2 (HVertex N)}
    (he : e ∈ incidentEdgesOn L (smallEndpointVertices N K)) :
    ∃! q : LargePrime N,
      q ∈ cumulativeLevelFibres N K 2 ∧ e ∈ crossingFinset q L := by
  obtain ⟨q, hq, hqe⟩ :=
    exists_nonbinary_fibre_for_boundary_edge_of_extremal
      hKN hL hmax hsat he
  refine ⟨q, ⟨hq, hqe⟩, ?_⟩
  intro r hr
  by_contra hqr
  have hval : q.val ≠ r.val := by
    intro hv
    apply hqr
    cases q
    cases r
    simp_all
  have hdisj := crossingFinset_disjoint_of_ne hL hval
  rw [Finset.disjoint_left] at hdisj
  exact hdisj hqe hr.2

end DivisorF
