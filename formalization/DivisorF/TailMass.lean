import DivisorF.Rigidity
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact finite large-prime tail mass

Original Section 3.5 finite tail theorem. The strict endpoint `c < N / Q` is
retained exactly, including the integral-endpoint case.
-/

namespace DivisorF

open scoped BigOperators

noncomputable def tailPrimes (N : ℕ) (Q : ℝ) : Finset (LargePrime N) := by
  classical
  exact Finset.univ.filter fun q => Q < (q.val : ℝ)

@[simp]
theorem mem_tailPrimes {N : ℕ} {Q : ℝ} {q : LargePrime N} :
    q ∈ tailPrimes N Q ↔ Q < (q.val : ℝ) := by
  classical
  simp [tailPrimes]

noncomputable def tailEndpointVertices (N : ℕ) (Q : ℝ) : Finset (HVertex N) := by
  classical
  exact Finset.univ.filter fun c => (c.value : ℝ) < (N : ℝ) / Q

@[simp]
theorem mem_tailEndpointVertices {N : ℕ} {Q : ℝ} {c : HVertex N} :
    c ∈ tailEndpointVertices N Q ↔ (c.value : ℝ) < (N : ℝ) / Q := by
  classical
  simp [tailEndpointVertices]

/-- `M_N(Q)=max(0,ceil(N/Q)-2)`, via natural subtraction. -/
noncomputable def tailEndpointCount (N : ℕ) (Q : ℝ) : ℕ :=
  Nat.ceil ((N : ℝ) / Q) - 2

/-- Exact count of integers `c` with `2 ≤ c < N/Q`. -/
theorem tailEndpointVertices_card_eq
    {N : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) :
    (tailEndpointVertices N Q).card = tailEndpointCount N Q := by
  classical
  let C : ℕ := Nat.ceil ((N : ℝ) / Q)
  let vals : Finset ℕ := (tailEndpointVertices N Q).image HVertex.value
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hdiv : (N : ℝ) / Q ≤ (N : ℝ) := by
    rw [div_le_iff₀ hQpos]
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    nlinarith
  have hC_le_N : C ≤ N := (Nat.ceil_le).2 hdiv
  have hvals : vals = Finset.Ico 2 C := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨c, hc, rfl⟩
      exact Finset.mem_Ico.mpr
        ⟨HVertex.two_le_value c,
          (Nat.lt_ceil).2 (mem_tailEndpointVertices.mp hc)⟩
    · intro hn
      have hnI := Finset.mem_Ico.mp hn
      have hnN : n ≤ N := le_trans (Nat.le_of_lt hnI.2) hC_le_N
      let c : HVertex N := HVertex.ofValue hnI.1 hnN
      have hcval : c.value = n := HVertex.value_ofValue hnI.1 hnN
      have hreal : (n : ℝ) < (N : ℝ) / Q := (Nat.lt_ceil).1 hnI.2
      have hc : c ∈ tailEndpointVertices N Q := by
        apply mem_tailEndpointVertices.mpr
        simpa [hcval] using hreal
      exact Finset.mem_image.mpr ⟨c, hc, hcval⟩
  have hcard : vals.card = (tailEndpointVertices N Q).card := by
    unfold vals
    exact Finset.card_image_of_injective _
      (fun _ _ h => HVertex.ext_value h)
  calc
    (tailEndpointVertices N Q).card = vals.card := hcard.symm
    _ = (Finset.Ico 2 C).card := by rw [hvals]
    _ = C - 2 := by simp
    _ = tailEndpointCount N Q := rfl

/-- The paper hypotheses imply the endpoint-count hypothesis `Q ≥ 1`. -/
theorem one_le_of_sqrt_le
    {N : ℕ} {Q : ℝ}
    (hN : 2 ≤ N)
    (hQ : Real.sqrt (N : ℝ) ≤ Q) :
    1 ≤ Q := by
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt hNnonneg
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt_one : 1 ≤ Real.sqrt (N : ℝ) := by nlinarith
  exact le_trans hsqrt_one hQ

/-- Every crossing of a tail prime is charged to the exact strict endpoint set. -/
theorem crossingFinset_subset_tailEndpoint_incidence
    {N : ℕ} {Q : ℝ} {q : LargePrime N}
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hQpos : 0 < Q)
    (hq : q ∈ tailPrimes N Q) :
    crossingFinset q L ⊆ incidentEdgesOn L (tailEndpointVertices N Q) := by
  classical
  intro e he
  have hecross := mem_crossingFinset.mp he
  rcases hecross with ⟨heL, ⟨v, hv, hvfibre⟩, ⟨x, hx, hxoutside⟩⟩
  have hAdj : (reducedDivisorGraph N).Adj x v := by
    induction e using Sym2.ind with
    | _ a b =>
        have habL : L.Adj a b := by
          simpa only [SimpleGraph.mem_edgeSet] using heL
        have hab : (reducedDivisorGraph N).Adj a b := hL.1 habL
        simp only [Sym2.mem_iff] at hx hv
        rcases hx with rfl | rfl <;> rcases hv with rfl | rfl
        · exact (hxoutside hvfibre).elim
        · exact hab
        · exact hab.symm
        · exact (hxoutside hvfibre).elim
  have hxle : x.value ≤ fibreCoefficient q v :=
    crossing_value_le_coefficient q hvfibre hxoutside hAdj
  have hxq_le : x.value * q.val ≤ N := by
    calc
      x.value * q.val ≤ fibreCoefficient q v * q.val :=
        Nat.mul_le_mul_right q.val hxle
      _ = q.val * fibreCoefficient q v := Nat.mul_comm _ _
      _ = v.value := (value_eq_prime_mul_coefficient q hvfibre).symm
      _ ≤ N := HVertex.value_le v
  have hqQ : Q < (q.val : ℝ) := mem_tailPrimes.mp hq
  have hxpos : 0 < (x.value : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (HVertex.two_le_value x))
  have hxQ_lt_N : (x.value : ℝ) * Q < (N : ℝ) := by
    calc
      (x.value : ℝ) * Q < (x.value : ℝ) * q.val :=
        mul_lt_mul_of_pos_left hqQ hxpos
      _ ≤ (N : ℝ) := by exact_mod_cast hxq_le
  have hxdiv : (x.value : ℝ) < (N : ℝ) / Q :=
    (lt_div_iff₀ hQpos).2 hxQ_lt_N
  have hxsmall : x ∈ tailEndpointVertices N Q :=
    mem_tailEndpointVertices.mpr hxdiv
  rw [incidentEdgesOn, Finset.mem_biUnion]
  refine ⟨x, hxsmall, ?_⟩
  rw [SimpleGraph.mem_incidenceFinset]
  exact ⟨heL, hx⟩

noncomputable def tailDefectSum (N : ℕ) (Q : ℝ) : ℤ :=
  ∑ q ∈ tailPrimes N Q, fibreDefect q

/-- **Theorem 3.12 candidate:** `Σ_{Q<q≤N} D_N(q) ≤ 2 M_N(Q)`. -/
theorem tailDefectSum_le
    {N : ℕ} {Q : ℝ}
    (hN : 2 ≤ N)
    (hQ : Real.sqrt (N : ℝ) ≤ Q) :
    tailDefectSum N Q ≤ (2 * tailEndpointCount N Q : ℕ) := by
  have hQone : 1 ≤ Q := one_le_of_sqrt_le hN hQ
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQone
  obtain ⟨L, hL, hmax⟩ :=
    exists_maximumLinearForest (reducedDivisorGraph N)
  have hcover :
      ∀ q ∈ tailPrimes N Q,
        crossingFinset q L ⊆ incidentEdgesOn L (tailEndpointVertices N Q) := by
    intro q hq
    exact crossingFinset_subset_tailEndpoint_incidence hL hQpos hq
  have hcross :
      ∑ q ∈ tailPrimes N Q, crossingCount q L
        ≤ 2 * (tailEndpointVertices N Q).card :=
    sum_crossingCount_le_two_mul_card_of_cover
      (tailPrimes N Q) hL (tailEndpointVertices N Q) hcover
  unfold tailDefectSum
  calc
    ∑ q ∈ tailPrimes N Q, fibreDefect q
        ≤ ∑ q ∈ tailPrimes N Q, (crossingCount q L : ℤ) := by
          apply Finset.sum_le_sum
          intro q _
          exact fibreDefect_le_crossingCount q hL hmax
    _ = ((∑ q ∈ tailPrimes N Q, crossingCount q L : ℕ) : ℤ) := by
          norm_cast
    _ ≤ (2 * (tailEndpointVertices N Q).card : ℕ) := by
          exact_mod_cast hcross
    _ = (2 * tailEndpointCount N Q : ℕ) := by
          rw [tailEndpointVertices_card_eq hQone]

end DivisorF
