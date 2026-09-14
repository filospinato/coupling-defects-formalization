import DivisorF.Multiplicity
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Simultaneous crossing packing

This module formalizes the crossing-to-degree-slot mechanism behind the
original Section 3.4 multiplicity bounds.  Distinct large-prime fibres have
disjoint selected crossing-edge sets; after charging every crossing to its
external endpoint, all crossings of quotient type at most `K` fit into the two
selected degree slots of the boundary vertices `2,...,K`.
-/

namespace DivisorF

open SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- Finite selected crossing-edge set of one large-prime fibre. -/
noncomputable def crossingFinset (q : LargePrime N)
    (L : SimpleGraph (HVertex N)) : Finset (Sym2 (HVertex N)) := by
  classical
  exact (crossSet L (InFibre q)).toFinite.toFinset

@[simp]
theorem mem_crossingFinset {q : LargePrime N}
    {L : SimpleGraph (HVertex N)} {e : Sym2 (HVertex N)} :
    e ∈ crossingFinset q L ↔ e ∈ crossSet L (InFibre q) := by
  classical
  simp [crossingFinset]

@[simp]
theorem card_crossingFinset (q : LargePrime N)
    (L : SimpleGraph (HVertex N)) :
    (crossingFinset q L).card = crossingCount q L := by
  classical
  unfold crossingFinset crossingCount crossingCard
  exact ((crossSet L (InFibre q)).ncard_eq_toFinset_card (Set.toFinite _)).symm

/-- One selected edge cannot be a crossing for two distinct large-prime fibres. -/
theorem crossingFinset_disjoint_of_ne
    {q r : LargePrime N} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hqr : q.val ≠ r.val) :
    Disjoint (crossingFinset q L) (crossingFinset r L) := by
  classical
  rw [Finset.disjoint_left]
  intro e heq her
  have heq' := mem_crossingFinset.mp heq
  have her' := mem_crossingFinset.mp her
  rcases heq' with ⟨heL, ⟨x, hx, hqx⟩, ⟨y, hy, _hqy⟩⟩
  rcases her' with ⟨_, ⟨u, hu, hru⟩, ⟨v, hv, _hrv⟩⟩
  induction e using Sym2.ind with
  | _ a b =>
      have habL : L.Adj a b := by
        simpa only [SimpleGraph.mem_edgeSet] using heL
      have hab : (reducedDivisorGraph N).Adj a b := hL.1 habL
      simp only [Sym2.mem_iff] at hx hy hu hv
      rcases hx with rfl | rfl <;>
        rcases hy with rfl | rfl <;>
        rcases hu with rfl | rfl <;>
        rcases hv with rfl | rfl
      all_goals
        first
        | exact (distinct_fibres_disjoint q r hqr hqx) hru
        | exact (distinct_fibres_anticomplete q r hqr hqx hru) hab
        | exact (distinct_fibres_anticomplete q r hqr hqx hru) hab.symm

/-- Union of the selected crossing edges of a finite family of fibres. -/
noncomputable def crossingUnion (P : Finset (LargePrime N))
    (L : SimpleGraph (HVertex N)) : Finset (Sym2 (HVertex N)) := by
  classical
  exact P.biUnion fun q => crossingFinset q L

/-- Distinct fibres in any finite family contribute disjoint crossing-edge sets. -/
theorem crossingFinsets_pairwiseDisjoint
    (P : Finset (LargePrime N)) {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    (↑P : Set (LargePrime N)).PairwiseDisjoint (fun q => crossingFinset q L) := by
  classical
  intro q hq r hr hne
  apply crossingFinset_disjoint_of_ne hL
  intro hval
  apply hne
  cases q
  cases r
  simp_all

/-- Cardinality of the disjoint crossing union is the sum of crossing counts. -/
theorem card_crossingUnion
    (P : Finset (LargePrime N)) {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    (crossingUnion P L).card = ∑ q ∈ P, crossingCount q L := by
  classical
  unfold crossingUnion
  rw [Finset.card_biUnion (crossingFinsets_pairwiseDisjoint P hL)]
  apply Finset.sum_congr rfl
  intro q _
  exact card_crossingFinset q L

/-- Selected edges incident to at least one vertex of `S`. -/
noncomputable def incidentEdgesOn (L : SimpleGraph (HVertex N))
    (S : Finset (HVertex N)) : Finset (Sym2 (HVertex N)) := by
  classical
  exact S.biUnion fun v => L.incidenceFinset v

/-- `SimpleGraph.degree` is the existing `selectedDegree`. -/
theorem graphDegree_eq_selectedDegree
    (L : SimpleGraph (HVertex N)) (v : HVertex N)
    [Fintype (L.neighborSet v)] :
    L.degree v = selectedDegree L v := by
  classical
  unfold SimpleGraph.degree selectedDegree SimpleGraph.neighborFinset
  simp

/-- The union of selected incidences is bounded by the sum of selected degrees. -/
theorem card_incidentEdgesOn_le_sum_selectedDegree
    (L : SimpleGraph (HVertex N)) (S : Finset (HVertex N)) :
    (incidentEdgesOn L S).card ≤ ∑ v ∈ S, selectedDegree L v := by
  classical
  calc
    (incidentEdgesOn L S).card
        ≤ ∑ v ∈ S, (L.incidenceFinset v).card := by
          exact Finset.card_biUnion_le
    _ = ∑ v ∈ S, selectedDegree L v := by
          apply Finset.sum_congr rfl
          intro v _
          rw [SimpleGraph.card_incidenceFinset_eq_degree,
            graphDegree_eq_selectedDegree]

/-- A linear forest has at most two selected incidence slots per boundary vertex. -/
theorem card_incidentEdgesOn_le_two_mul_card
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (S : Finset (HVertex N)) :
    (incidentEdgesOn L S).card ≤ 2 * S.card := by
  calc
    (incidentEdgesOn L S).card
        ≤ ∑ v ∈ S, selectedDegree L v :=
      card_incidentEdgesOn_le_sum_selectedDegree L S
    _ ≤ ∑ _v ∈ S, 2 := by
      apply Finset.sum_le_sum
      intro v _
      exact hL.2.2 v
    _ = 2 * S.card := by simp [Nat.mul_comm]

/-- Generic simultaneous crossing packing from a finite endpoint cover. -/
theorem sum_crossingCount_le_two_mul_card_of_cover
    (P : Finset (LargePrime N)) {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (S : Finset (HVertex N))
    (hcover : ∀ q ∈ P, crossingFinset q L ⊆ incidentEdgesOn L S) :
    ∑ q ∈ P, crossingCount q L ≤ 2 * S.card := by
  classical
  have hunion : crossingUnion P L ⊆ incidentEdgesOn L S := by
    intro e he
    rw [crossingUnion, Finset.mem_biUnion] at he
    obtain ⟨q, hq, heq⟩ := he
    exact hcover q hq heq
  calc
    ∑ q ∈ P, crossingCount q L
        = (crossingUnion P L).card := (card_crossingUnion P hL).symm
    _ ≤ (incidentEdgesOn L S).card := Finset.card_le_card hunion
    _ ≤ 2 * S.card := card_incidentEdgesOn_le_two_mul_card hL S

/-- Boundary vertices represented by the integers `2,...,K`. -/
noncomputable def smallEndpointVertices (N K : ℕ) : Finset (HVertex N) := by
  classical
  exact Finset.univ.filter fun v => v.value ≤ K

@[simp]
theorem mem_smallEndpointVertices {K : ℕ} {v : HVertex N} :
    v ∈ smallEndpointVertices N K ↔ v.value ≤ K := by
  classical
  simp [smallEndpointVertices]

/-- The boundary set contains at most `K-1` vertices. -/
theorem smallEndpointVertices_card_le (K : ℕ) :
    (smallEndpointVertices N K).card ≤ K - 1 := by
  classical
  let vals : Finset ℕ := (smallEndpointVertices N K).image HVertex.value
  have hcard : vals.card = (smallEndpointVertices N K).card := by
    unfold vals
    exact Finset.card_image_of_injective _ (fun _ _ h => HVertex.ext_value h)
  have hsub : vals ⊆ Finset.Icc 2 K := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨v, hv, rfl⟩ := ha
    exact Finset.mem_Icc.mpr
      ⟨HVertex.two_le_value v, mem_smallEndpointVertices.mp hv⟩
  calc
    (smallEndpointVertices N K).card = vals.card := hcard.symm
    _ ≤ (Finset.Icc 2 K).card := Finset.card_le_card hsub
    _ = K - 1 := by simp

/-- Every crossing of a type-`s` fibre uses an external endpoint in `2,...,s`. -/
theorem crossingFinset_subset_smallEndpoint_incidence
    {s : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (_hL : IsLinearForest (reducedDivisorGraph N) L)
    (hqtype : q.quotientType = s) :
    crossingFinset q L ⊆ incidentEdgesOn L (smallEndpointVertices N s) := by
  classical
  intro e he
  have hecross := mem_crossingFinset.mp he
  rcases hecross with ⟨heL, ⟨v, hv, hvfibre⟩, ⟨x, hx, hxoutside⟩⟩
  have hAdj : (reducedDivisorGraph N).Adj x v := by
    induction e using Sym2.ind with
    | _ a b =>
        have habL : L.Adj a b := by
          simpa only [SimpleGraph.mem_edgeSet] using heL
        have hab : (reducedDivisorGraph N).Adj a b := _hL.1 habL
        simp only [Sym2.mem_iff] at hv hx
        rcases hv with rfl | rfl <;> rcases hx with rfl | rfl
        · exact (hxoutside hvfibre).elim
        · exact hab.symm
        · exact hab
        · exact (hxoutside hvfibre).elim
  have hxle : x.value ≤ fibreCoefficient q v :=
    crossing_value_le_coefficient q hvfibre hxoutside hAdj
  have hcoeff : fibreCoefficient q v ≤ q.quotientType :=
    fibreCoefficient_le_quotientType q hvfibre
  have hxs : x.value ≤ s := by
    rw [← hqtype]
    exact le_trans hxle hcoeff
  have hxsmall : x ∈ smallEndpointVertices N s :=
    mem_smallEndpointVertices.mpr hxs
  rw [incidentEdgesOn, Finset.mem_biUnion]
  refine ⟨x, hxsmall, ?_⟩
  rw [SimpleGraph.mem_incidenceFinset]
  exact ⟨heL, hx⟩

/-- The simultaneous same-type crossing budget in one fixed linear forest. -/
theorem typePrimes_crossingCount_sum_le
    {s : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    ∑ q ∈ typePrimes N s, crossingCount q L ≤ 2 * (s - 1) := by
  have hcover :
      ∀ q ∈ typePrimes N s,
        crossingFinset q L ⊆ incidentEdgesOn L (smallEndpointVertices N s) := by
    intro q hq
    exact crossingFinset_subset_smallEndpoint_incidence hL (mem_typePrimes.mp hq)
  calc
    ∑ q ∈ typePrimes N s, crossingCount q L
        ≤ 2 * (smallEndpointVertices N s).card :=
      sum_crossingCount_le_two_mul_card_of_cover
        (typePrimes N s) hL (smallEndpointVertices N s) hcover
    _ ≤ 2 * (s - 1) :=
      Nat.mul_le_mul_left 2 (smallEndpointVertices_card_le (N := N) s)

/-- **Corollary 3.6 candidate:** the same-type multiplicity budget. -/
theorem typeMultiplicity_mul_typeDefectNat_le
    {s : ℕ} (hocc : TypeOccupied N s) :
    typeMultiplicity N s * typeDefectNat hocc ≤ 2 * (s - 1) := by
  obtain ⟨L, hL, hmax⟩ :=
    exists_maximumLinearForest (reducedDivisorGraph N)
  exact le_trans
    (typeMultiplicity_mul_typeDefectNat_le_crossingSum hocc hL hmax)
    (typePrimes_crossingCount_sum_le hL)

/-- Large enough multiplicity forces zero common defect. -/
theorem typeDefect_eq_zero_of_large_multiplicity
    {s : ℕ} (hocc : TypeOccupied N s)
    (hmult : 2 * (s - 1) < typeMultiplicity N s) :
    typeDefect hocc = 0 := by
  have hbudget := typeMultiplicity_mul_typeDefectNat_le hocc
  have hz : typeDefectNat hocc = 0 := by
    by_contra hne
    have hpos : 1 ≤ typeDefectNat hocc := Nat.one_le_iff_ne_zero.mpr hne
    nlinarith
  rw [← coe_typeDefectNat hocc, hz]
  simp

/-- **Corollary 3.7 candidate:** multiplicity above `s-1` forces binary defect. -/
theorem typeDefect_le_one_of_large_multiplicity
    {s : ℕ} (hocc : TypeOccupied N s)
    (hmult : s - 1 < typeMultiplicity N s) :
    typeDefect hocc ≤ 1 := by
  have hbudget := typeMultiplicity_mul_typeDefectNat_le hocc
  have hle : typeDefectNat hocc ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ typeDefectNat hocc := by omega
    nlinarith
  rw [← coe_typeDefectNat hocc]
  exact_mod_cast hle

end DivisorF
