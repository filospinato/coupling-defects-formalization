import DivisorF.Rigidity
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extremal boundary saturation

Equality-case geometry for the original Proposition 3.10 / Corollary 3.11.
At the extremal nonbinary count, all available selected degree on the common
boundary `2,...,K` is exhausted by counted fibre crossings.
-/

namespace DivisorF

open SimpleGraph
open scoped BigOperators

/-- Under `K ≤ N`, the boundary vertices are exactly the values `2,...,K`. -/
theorem smallEndpointVertices_card_eq
    {N K : ℕ} (hKN : K ≤ N) :
    (smallEndpointVertices N K).card = K - 1 := by
  classical
  let vals : Finset ℕ := (smallEndpointVertices N K).image HVertex.value
  have hvals : vals = Finset.Icc 2 K := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨v, hv, rfl⟩
      exact Finset.mem_Icc.mpr
        ⟨HVertex.two_le_value v, (mem_smallEndpointVertices).mp hv⟩
    · intro ha
      have haI := Finset.mem_Icc.mp ha
      let v : HVertex N := HVertex.ofValue haI.1 (le_trans haI.2 hKN)
      exact Finset.mem_image.mpr
        ⟨v,
          (mem_smallEndpointVertices).2 (by simpa [v] using haI.2),
          by simp [v]⟩
  have hcard : vals.card = (smallEndpointVertices N K).card := by
    unfold vals
    exact Finset.card_image_of_injective _ (fun _ _ h => HVertex.ext_value h)
  calc
    (smallEndpointVertices N K).card = vals.card := hcard.symm
    _ = (Finset.Icc 2 K).card := by rw [hvals]
    _ = K - 1 := by simp

/-- All cumulative crossing edges are selected incidences on the common boundary. -/
theorem cumulativeCrossingUnion_subset_incidentEdges
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    crossingUnion (cumulativeFibres N K) L ⊆
      incidentEdgesOn L (smallEndpointVertices N K) := by
  intro e he
  rw [crossingUnion, Finset.mem_biUnion] at he
  obtain ⟨q, hq, heq⟩ := he
  exact cumulative_crossing_cover (N := N) (K := K) hL q hq heq

/-- Extremality forces the cumulative crossing mass to attain full capacity. -/
theorem cumulativeCrossingMass_eq_capacity_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    cumulativeCrossingMass K L = cumulativeBoundaryCapacity K := by
  have hu := (extremalRigidity_terms_vanish hL hmax hsat).1
  unfold cumulativeUnusedCapacity at hu
  have hle := cumulativeCrossingMass_le (N := N) (K := K) hL
  omega

/--
**Proposition 3.10 equality case:** every selected edge incident to the common
boundary is one of the counted fibre crossings.
-/
theorem incidentEdges_eq_cumulativeCrossingUnion_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    incidentEdgesOn L (smallEndpointVertices N K) =
      crossingUnion (cumulativeFibres N K) L := by
  classical
  have hsub := cumulativeCrossingUnion_subset_incidentEdges
    (N := N) (K := K) hL
  have hcrossCard :
      (crossingUnion (cumulativeFibres N K) L).card = 2 * (K - 1) := by
    rw [card_crossingUnion (cumulativeFibres N K) hL]
    have hm := cumulativeCrossingMass_eq_capacity_of_extremal hL hmax hsat
    simpa [cumulativeCrossingMass, cumulativeBoundaryCapacity] using hm
  have hincLe :
      (incidentEdgesOn L (smallEndpointVertices N K)).card ≤ 2 * (K - 1) := by
    calc
      (incidentEdgesOn L (smallEndpointVertices N K)).card
          ≤ 2 * (smallEndpointVertices N K).card :=
        card_incidentEdgesOn_le_two_mul_card hL _
      _ = 2 * (K - 1) := by rw [smallEndpointVertices_card_eq hKN]
  apply Finset.Subset.antisymm
  · intro e he
    by_contra hnot
    have hstrict :
        (crossingUnion (cumulativeFibres N K) L).card <
          (incidentEdgesOn L (smallEndpointVertices N K)).card := by
      exact Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
          intro heq
          apply hnot
          simpa [heq] using he⟩)
    omega
  · exact hsub

/--
At extremality every common-boundary vertex has selected degree exactly two.
-/
theorem selectedDegree_eq_two_on_boundary_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {v : HVertex N} (hv : v ∈ smallEndpointVertices N K) :
    selectedDegree L v = 2 := by
  classical
  have hK2 : 2 ≤ K :=
    le_trans (HVertex.two_le_value v) ((mem_smallEndpointVertices).mp hv)
  have hincEq := incidentEdges_eq_cumulativeCrossingUnion_of_extremal
    hKN hL hmax hsat
  have hincCard :
      (incidentEdgesOn L (smallEndpointVertices N K)).card = 2 * (K - 1) := by
    rw [hincEq, card_crossingUnion (cumulativeFibres N K) hL]
    have hm := cumulativeCrossingMass_eq_capacity_of_extremal hL hmax hsat
    simpa [cumulativeCrossingMass, cumulativeBoundaryCapacity] using hm
  have hsumLe :
      (incidentEdgesOn L (smallEndpointVertices N K)).card ≤
        ∑ x ∈ smallEndpointVertices N K, selectedDegree L x :=
    card_incidentEdgesOn_le_sum_selectedDegree L _
  have hallLe :
      ∑ x ∈ smallEndpointVertices N K, selectedDegree L x ≤
        2 * (K - 1) := by
    calc
      ∑ x ∈ smallEndpointVertices N K, selectedDegree L x
          ≤ ∑ _x ∈ smallEndpointVertices N K, 2 := by
            apply Finset.sum_le_sum
            intro x _
            exact hL.2.2 x
      _ = 2 * (smallEndpointVertices N K).card := by simp [Nat.mul_comm]
      _ = 2 * (K - 1) := by rw [smallEndpointVertices_card_eq hKN]
  have hsumEq :
      ∑ x ∈ smallEndpointVertices N K, selectedDegree L x = 2 * (K - 1) := by
    omega
  by_contra hvne
  have hvlt : selectedDegree L v < 2 := by
    have hvle := hL.2.2 v
    omega
  have hothers :
      ∑ x ∈ (smallEndpointVertices N K).erase v, selectedDegree L x ≤
        2 * ((smallEndpointVertices N K).erase v).card := by
    calc
      ∑ x ∈ (smallEndpointVertices N K).erase v, selectedDegree L x
          ≤ ∑ _x ∈ (smallEndpointVertices N K).erase v, 2 := by
            apply Finset.sum_le_sum
            intro x _
            exact hL.2.2 x
      _ = 2 * ((smallEndpointVertices N K).erase v).card := by
            simp [Nat.mul_comm]
  have hcardErase :
      ((smallEndpointVertices N K).erase v).card = K - 2 := by
    rw [Finset.card_erase_of_mem hv, smallEndpointVertices_card_eq hKN]
    omega
  have hsplit :
      ∑ x ∈ smallEndpointVertices N K, selectedDegree L x =
        selectedDegree L v +
          ∑ x ∈ (smallEndpointVertices N K).erase v, selectedDegree L x := by
    rw [← Finset.sum_erase_add _ _ hv]
    exact Nat.add_comm _ _
  omega

end DivisorF
