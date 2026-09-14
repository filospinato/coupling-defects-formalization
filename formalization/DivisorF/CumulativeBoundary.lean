import DivisorF.CrossingPacking
import Mathlib.Tactic

set_option linter.style.header false

namespace DivisorF

open SimpleGraph
open scoped BigOperators

noncomputable def cumulativeFibres (N K : ℕ) : Finset (LargePrime N) := by
  classical
  exact Finset.univ.filter fun q => 2 ≤ q.quotientType ∧ q.quotientType ≤ K

@[simp]
theorem mem_cumulativeFibres {N K : ℕ} {q : LargePrime N} :
    q ∈ cumulativeFibres N K ↔ 2 ≤ q.quotientType ∧ q.quotientType ≤ K := by
  classical
  simp [cumulativeFibres]

noncomputable def cumulativeCrossingMass {N : ℕ} (K : ℕ)
    (L : SimpleGraph (HVertex N)) : ℕ :=
  ∑ q ∈ cumulativeFibres N K, crossingCount q L

noncomputable def cumulativeDefectSum (N K : ℕ) : ℤ :=
  ∑ q ∈ cumulativeFibres N K, fibreDefect q

def cumulativeBoundaryCapacity (K : ℕ) : ℕ := 2 * (K - 1)

theorem crossingFinset_subset_boundary_incidence_of_type_le
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hqK : q.quotientType ≤ K) :
    crossingFinset q L ⊆ incidentEdgesOn L (smallEndpointVertices N K) := by
  classical
  intro e he
  have hecross := mem_crossingFinset.mp he
  rcases hecross with ⟨heL, ⟨v, hv, hvfibre⟩, ⟨x, hx, hxoutside⟩⟩
  have hcharge :
      ∀ {v x : HVertex N}, v ∈ e → InFibre q v → x ∈ e → ¬ InFibre q x →
        (reducedDivisorGraph N).Adj x v →
        e ∈ incidentEdgesOn L (smallEndpointVertices N K) := by
    intro v x hv hvfibre hx hxoutside hxv
    have hxle : x.value ≤ fibreCoefficient q v :=
      crossing_value_le_coefficient q hvfibre hxoutside hxv
    have hcoeff : fibreCoefficient q v ≤ q.quotientType :=
      fibreCoefficient_le_quotientType q hvfibre
    have hxK : x.value ≤ K := le_trans hxle (le_trans hcoeff hqK)
    have hxsmall : x ∈ smallEndpointVertices N K :=
      (mem_smallEndpointVertices).2 hxK
    rw [incidentEdgesOn, Finset.mem_biUnion]
    refine ⟨x, hxsmall, ?_⟩
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨heL, hx⟩
  induction e using Sym2.ind with
  | _ a b =>
      have habL : L.Adj a b := by
        simpa only [SimpleGraph.mem_edgeSet] using heL
      have hab : (reducedDivisorGraph N).Adj a b := hL.1 habL
      simp only [Sym2.mem_iff] at hv hx
      rcases hv with hva | hvb
      · rcases hx with hxa | hxb
        · subst v
          subst x
          exact (hxoutside hvfibre).elim
        · subst v
          subst x
          exact hcharge (by simp) hvfibre (by simp) hxoutside hab.symm
      · rcases hx with hxa | hxb
        · subst v
          subst x
          exact hcharge (by simp) hvfibre (by simp) hxoutside hab
        · subst v
          subst x
          exact (hxoutside hvfibre).elim

theorem cumulative_crossing_cover
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    ∀ q ∈ cumulativeFibres N K,
      crossingFinset q L ⊆ incidentEdgesOn L (smallEndpointVertices N K) := by
  intro q hq
  exact crossingFinset_subset_boundary_incidence_of_type_le
    hL (mem_cumulativeFibres.mp hq).2

theorem cumulativeCrossingMass_le
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    cumulativeCrossingMass K L ≤ cumulativeBoundaryCapacity K := by
  unfold cumulativeCrossingMass cumulativeBoundaryCapacity
  calc
    ∑ q ∈ cumulativeFibres N K, crossingCount q L
        ≤ 2 * (smallEndpointVertices N K).card :=
      sum_crossingCount_le_two_mul_card_of_cover
        (cumulativeFibres N K) hL (smallEndpointVertices N K)
        (cumulative_crossing_cover hL)
    _ ≤ 2 * (K - 1) :=
      Nat.mul_le_mul_left 2 (smallEndpointVertices_card_le (N := N) K)

theorem cumulativeDefectSum_le {N K : ℕ} :
    cumulativeDefectSum N K ≤ (cumulativeBoundaryCapacity K : ℤ) := by
  obtain ⟨L, hL, hmax⟩ :=
    exists_maximumLinearForest (reducedDivisorGraph N)
  have hcross :
      (cumulativeCrossingMass K L : ℤ) ≤
        (cumulativeBoundaryCapacity K : ℤ) := by
    exact_mod_cast cumulativeCrossingMass_le (N := N) (K := K) hL
  calc
    cumulativeDefectSum N K
        = ∑ q ∈ cumulativeFibres N K, fibreDefect q := rfl
    _ ≤ ∑ q ∈ cumulativeFibres N K, (crossingCount q L : ℤ) := by
          apply Finset.sum_le_sum
          intro q _
          exact fibreDefect_le_crossingCount q hL hmax
    _ = (cumulativeCrossingMass K L : ℤ) := by
          unfold cumulativeCrossingMass
          norm_cast
    _ ≤ (cumulativeBoundaryCapacity K : ℤ) := hcross

end DivisorF
