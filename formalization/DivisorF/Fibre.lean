import DivisorF.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Large-prime fibres

The condition `N < q^2` is the integer form of `sqrt N < q`.  Together with
`q ≤ N`, it makes the large-prime domain finite and excludes the undefined
`q > N` case.
-/

namespace DivisorF

/-- A prime `q` in the paper's large-prime range `sqrt N < q ≤ N`. -/
structure LargePrime (N : ℕ) where
  val : ℕ
  prime : Nat.Prime val
  large : N < val * val
  le_N : val ≤ N

namespace LargePrime

@[simp]
theorem pos {N : ℕ} (q : LargePrime N) : 0 < q.val :=
  q.prime.pos

@[simp]
theorem ne_one {N : ℕ} (q : LargePrime N) : q.val ≠ 1 :=
  q.prime.ne_one

/-- Quotient type `s = floor(N / q)`. -/
def quotientType {N : ℕ} (q : LargePrime N) : ℕ :=
  N / q.val

end LargePrime

/-- Membership in `B_q(N)`: the represented integer is divisible by `q`. -/
def InFibre {N : ℕ} (q : LargePrime N) (v : HVertex N) : Prop :=
  q.val ∣ v.value

instance instDecidablePredInFibre {N : ℕ} (q : LargePrime N) :
    DecidablePred (InFibre q) :=
  fun v ↦ inferInstanceAs (Decidable (q.val ∣ v.value))

/-- Coefficient `a` of a fibre vertex `a q`. -/
def fibreCoefficient {N : ℕ} (q : LargePrime N) (v : HVertex N) : ℕ :=
  v.value / q.val

theorem value_eq_prime_mul_coefficient {N : ℕ} (q : LargePrime N)
    {v : HVertex N} (hv : InFibre q v) :
    v.value = q.val * fibreCoefficient q v := by
  exact Nat.eq_mul_of_div_eq_right hv rfl

theorem fibreCoefficient_pos {N : ℕ} (q : LargePrime N)
    {v : HVertex N} (hv : InFibre q v) :
    0 < fibreCoefficient q v := by
  by_contra h
  have hz : fibreCoefficient q v = 0 := Nat.eq_zero_of_not_pos h
  have heq := value_eq_prime_mul_coefficient q hv
  rw [hz, mul_zero] at heq
  have hv_pos : 0 < v.value := lt_of_lt_of_le (by decide : 0 < 2) v.two_le_value
  exact (Nat.ne_of_gt hv_pos) heq

/-- Every fibre coefficient is smaller than every large prime for the same `N`. -/
theorem fibreCoefficient_lt_largePrime {N : ℕ} (q r : LargePrime N)
    {v : HVertex N} (hv : InFibre r v) :
    fibreCoefficient r v < q.val := by
  let a := fibreCoefficient r v
  have ha_pos : 0 < a := fibreCoefficient_pos r hv
  have ha_lt_r : a < r.val := by
    apply (Nat.div_lt_iff_lt_mul r.pos).2
    exact lt_of_le_of_lt v.value_le r.large
  have hav : a * r.val = v.value := by
    simpa [a, Nat.mul_comm] using (value_eq_prime_mul_coefficient r hv).symm
  have har_le : a * r.val ≤ N := by
    rw [hav]
    exact v.value_le
  have haa_le : a * a ≤ N := by
    nlinarith
  nlinarith [q.large]

/-- Distinct large-prime fibres have no divisor edge between them. -/
theorem distinct_fibres_anticomplete {N : ℕ} (q r : LargePrime N)
    (hqr : q.val ≠ r.val) {v w : HVertex N}
    (hv : InFibre q v) (hw : InFibre r w) :
    ¬(reducedDivisorGraph N).Adj v w := by
  intro hadj
  rcases (reducedDivisorGraph_adj v w).mp hadj with ⟨_, hvw | hwv⟩
  · have hq_dvd_w : q.val ∣ w.value := dvd_trans hv hvw
    have hq_mul : q.val ∣ r.val * fibreCoefficient r w := by
      rwa [← value_eq_prime_mul_coefficient r hw]
    rcases (q.prime.dvd_mul.mp hq_mul) with hq_r | hq_coeff
    · rcases (Nat.dvd_prime r.prime).mp hq_r with hq_one | hq_eq
      · exact q.ne_one hq_one
      · exact hqr hq_eq
    · exact (Nat.not_dvd_of_pos_of_lt
        (fibreCoefficient_pos r hw)
        (fibreCoefficient_lt_largePrime q r hw)) hq_coeff
  · have hr_dvd_v : r.val ∣ v.value := dvd_trans hw hwv
    have hr_mul : r.val ∣ q.val * fibreCoefficient q v := by
      rwa [← value_eq_prime_mul_coefficient q hv]
    rcases (r.prime.dvd_mul.mp hr_mul) with hr_q | hr_coeff
    · rcases (Nat.dvd_prime q.prime).mp hr_q with hr_one | hr_eq
      · exact r.ne_one hr_one
      · exact hqr hr_eq.symm
    · exact (Nat.not_dvd_of_pos_of_lt
        (fibreCoefficient_pos q hv)
        (fibreCoefficient_lt_largePrime r q hv)) hr_coeff

/-- A vertex cannot belong to two fibres associated with distinct large primes. -/
theorem distinct_fibres_disjoint {N : ℕ} (q r : LargePrime N)
    (hqr : q.val ≠ r.val) {v : HVertex N} (hv : InFibre q v) :
    ¬InFibre r v := by
  intro hr
  have hr_mul : r.val ∣ q.val * fibreCoefficient q v := by
    rwa [← value_eq_prime_mul_coefficient q hv]
  rcases (r.prime.dvd_mul.mp hr_mul) with hr_q | hr_coeff
  · rcases (Nat.dvd_prime q.prime).mp hr_q with hr_one | hr_eq
    · exact r.ne_one hr_one
    · exact hqr hr_eq.symm
  · exact (Nat.not_dvd_of_pos_of_lt
      (fibreCoefficient_pos q hv)
      (fibreCoefficient_lt_largePrime r q hv)) hr_coeff

/-- Adjacency inside one fibre is exactly divisibility comparability of its
coefficients. -/
theorem same_fibre_adj_iff {N : ℕ} (q : LargePrime N) {v w : HVertex N}
    (hv : InFibre q v) (hw : InFibre q w) :
    (reducedDivisorGraph N).Adj v w ↔
      fibreCoefficient q v ≠ fibreCoefficient q w ∧
        (fibreCoefficient q v ∣ fibreCoefficient q w ∨
          fibreCoefficient q w ∣ fibreCoefficient q v) := by
  rw [reducedDivisorGraph_adj]
  constructor
  · rintro ⟨hvw, hdvd⟩
    refine ⟨?_, ?_⟩
    · intro hcoeff
      apply hvw
      apply HVertex.ext_value
      rw [value_eq_prime_mul_coefficient q hv,
        value_eq_prime_mul_coefficient q hw, hcoeff]
    · rcases hdvd with hdvd | hdvd
      · left
        apply (Nat.mul_dvd_mul_iff_left q.pos).mp
        simpa [← value_eq_prime_mul_coefficient q hv,
          ← value_eq_prime_mul_coefficient q hw] using hdvd
      · right
        apply (Nat.mul_dvd_mul_iff_left q.pos).mp
        simpa [← value_eq_prime_mul_coefficient q hv,
          ← value_eq_prime_mul_coefficient q hw] using hdvd
  · rintro ⟨hcoeff, hdvd⟩
    refine ⟨?_, ?_⟩
    · intro hvw
      apply hcoeff
      rw [hvw]
    · rcases hdvd with hdvd | hdvd
      · left
        rw [value_eq_prime_mul_coefficient q hv,
          value_eq_prime_mul_coefficient q hw]
        exact (Nat.mul_dvd_mul_iff_left q.pos).mpr hdvd
      · right
        rw [value_eq_prime_mul_coefficient q hv,
          value_eq_prime_mul_coefficient q hw]
        exact (Nat.mul_dvd_mul_iff_left q.pos).mpr hdvd

/-- A crossing from a fibre to its complement lands at a divisor of the
coefficient of the fibre vertex. -/
theorem crossing_localization {N : ℕ} (q : LargePrime N)
    {x v : HVertex N} (hv : InFibre q v) (hx : ¬InFibre q x)
    (hadj : (reducedDivisorGraph N).Adj x v) :
    x.value ∣ fibreCoefficient q v := by
  rcases (reducedDivisorGraph_adj x v).mp hadj with ⟨_, hxv | hvx⟩
  · have hcop : Nat.Coprime x.value q.val :=
      (q.prime.coprime_iff_not_dvd.mpr hx).symm
    apply hcop.dvd_of_dvd_mul_left
    rwa [← value_eq_prime_mul_coefficient q hv]
  · exact (hx (dvd_trans hv hvx)).elim

theorem outside_adj_fibre_iff {N : ℕ} (q : LargePrime N)
    {x v : HVertex N} (hv : InFibre q v) (hx : ¬InFibre q x) :
    (reducedDivisorGraph N).Adj x v ↔ x.value ∣ fibreCoefficient q v := by
  constructor
  · exact crossing_localization q hv hx
  · intro hdvd
    apply (reducedDivisorGraph_adj x v).2
    refine ⟨?_, Or.inl ?_⟩
    · intro hxv
      apply hx
      simpa [hxv] using hv
    · rw [value_eq_prime_mul_coefficient q hv]
      exact dvd_mul_of_dvd_right hdvd q.val

theorem crossing_value_le_coefficient {N : ℕ} (q : LargePrime N)
    {x v : HVertex N} (hv : InFibre q v) (hx : ¬InFibre q x)
    (hadj : (reducedDivisorGraph N).Adj x v) :
    x.value ≤ fibreCoefficient q v := by
  exact Nat.le_of_dvd (fibreCoefficient_pos q hv)
    (crossing_localization q hv hx hadj)

/-- Every fibre coefficient is at most the quotient type. -/
theorem fibreCoefficient_le_quotientType {N : ℕ} (q : LargePrime N)
    {v : HVertex N} (_hv : InFibre q v) :
    fibreCoefficient q v ≤ q.quotientType :=
  Nat.div_le_div_right v.value_le

/-- A coefficient in the quotient range names a vertex of `H_N`. -/
theorem fibre_value_bounds {N : ℕ} (q : LargePrime N) {a : ℕ}
    (ha1 : 1 ≤ a) (ha : a ≤ q.quotientType) :
    2 ≤ a * q.val ∧ a * q.val ≤ N := by
  refine ⟨?_, (Nat.le_div_iff_mul_le q.pos).mp ha⟩
  calc
    2 = 1 * 2 := by norm_num
    _ ≤ a * q.val := Nat.mul_le_mul ha1 q.prime.two_le

/-- The fibre vertex `a q` attached to a vertex `a` of the quotient graph. -/
def fibreVertex {N : ℕ} (q : LargePrime N) (a : GVertex q.quotientType) : HVertex N :=
  HVertex.ofValue (fibre_value_bounds q a.one_le_value a.value_le).1
    (fibre_value_bounds q a.one_le_value a.value_le).2

@[simp]
theorem fibreVertex_value {N : ℕ} (q : LargePrime N) (a : GVertex q.quotientType) :
    (fibreVertex q a).value = a.value * q.val := by
  simp [fibreVertex]

theorem fibreVertex_mem {N : ℕ} (q : LargePrime N) (a : GVertex q.quotientType) :
    InFibre q (fibreVertex q a) := by
  rw [InFibre, fibreVertex_value]
  exact Dvd.intro_left _ rfl

@[simp]
theorem fibreCoefficient_fibreVertex {N : ℕ} (q : LargePrime N)
    (a : GVertex q.quotientType) :
    fibreCoefficient q (fibreVertex q a) = a.value := by
  unfold fibreCoefficient
  rw [fibreVertex_value]
  exact Nat.mul_div_cancel _ q.pos

/-- The subgraph of `H_N` induced by the complete fibre `B_q(N)`. -/
def fibreGraph {N : ℕ} (q : LargePrime N) :
    SimpleGraph {v : HVertex N // InFibre q v} :=
  (reducedDivisorGraph N).induce {v | InFibre q v}

/--
Dividing by `q` identifies the fibre `B_q(N)` with the divisor graph on
`{1, ..., s}`, where `s = ⌊N/q⌋` is the quotient type.  This is the Lean form
of the isomorphism `B_q(N) ≅ G_s` used throughout the paper.
-/
def fibreIso {N : ℕ} (q : LargePrime N) :
    fibreGraph q ≃g divisorGraph q.quotientType where
  toFun v := ⟨fibreCoefficient q v.1 - 1, by
    have h1 := fibreCoefficient_pos q v.2
    have h2 := fibreCoefficient_le_quotientType q v.2
    omega⟩
  invFun a := ⟨fibreVertex q a, fibreVertex_mem q a⟩
  left_inv v := by
    have h1 := fibreCoefficient_pos q v.2
    apply Subtype.ext
    apply HVertex.ext_value
    rw [fibreVertex_value]
    simp only [GVertex.value]
    rw [Nat.sub_add_cancel (by omega), Nat.mul_comm]
    exact (value_eq_prime_mul_coefficient q v.2).symm
  right_inv a := by
    apply Fin.ext
    simp [GVertex.value]
  map_rel_iff' := by
    intro v w
    have hv : InFibre q v.1 := v.2
    have hw : InFibre q w.1 := w.2
    have h1v := fibreCoefficient_pos q hv
    have h1w := fibreCoefficient_pos q hw
    have ev : fibreCoefficient q v.1 - 1 + 1 = fibreCoefficient q v.1 :=
      Nat.sub_add_cancel (by omega)
    have ew : fibreCoefficient q w.1 - 1 + 1 = fibreCoefficient q w.1 :=
      Nat.sub_add_cancel (by omega)
    have hrhs : (fibreGraph q).Adj v w ↔
        fibreCoefficient q v.1 ≠ fibreCoefficient q w.1 ∧
          (fibreCoefficient q v.1 ∣ fibreCoefficient q w.1 ∨
            fibreCoefficient q w.1 ∣ fibreCoefficient q v.1) :=
      same_fibre_adj_iff q hv hw
    rw [divisorGraph_adj, hrhs]
    simp only [Equiv.coe_fn_mk, GVertex.value, Fin.val_mk, ne_eq, Fin.mk.injEq, ev, ew]
    constructor
    · rintro ⟨hne, hdvd⟩
      exact ⟨fun h ↦ hne (by omega), hdvd⟩
    · rintro ⟨hne, hdvd⟩
      exact ⟨fun h ↦ hne (by omega), hdvd⟩


/-- Vertex map exchanging the complete fibres of two primes with the same
quotient type and fixing every other vertex. -/
noncomputable def swapFibreVertex {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) (v : HVertex N) : HVertex N := by
  by_cases hq : InFibre q v
  · let a := fibreCoefficient q v
    have ha_pos : 0 < a := fibreCoefficient_pos q hq
    have ha_le_qtype : a ≤ q.quotientType := by
      exact Nat.div_le_div_right v.value_le
    have ha_le_rtype : a ≤ r.quotientType := htype ▸ ha_le_qtype
    have har_le : a * r.val ≤ N :=
      (Nat.le_div_iff_mul_le r.pos).mp ha_le_rtype
    exact HVertex.ofValue (by nlinarith [r.prime.two_le]) har_le
  · by_cases hr : InFibre r v
    · let a := fibreCoefficient r v
      have ha_pos : 0 < a := fibreCoefficient_pos r hr
      have ha_le_rtype : a ≤ r.quotientType := by
        exact Nat.div_le_div_right v.value_le
      have ha_le_qtype : a ≤ q.quotientType := htype.symm ▸ ha_le_rtype
      have haq_le : a * q.val ≤ N :=
        (Nat.le_div_iff_mul_le q.pos).mp ha_le_qtype
      exact HVertex.ofValue (by nlinarith [q.prime.two_le]) haq_le
    · exact v

@[simp]
theorem swapFibreVertex_value_of_mem_left {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) {v : HVertex N}
    (hv : InFibre q v) :
    (swapFibreVertex q r htype v).value = fibreCoefficient q v * r.val := by
  simp [swapFibreVertex, hv]

theorem swapFibreVertex_value_of_not_mem_left_mem_right {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    {v : HVertex N} (hq : ¬InFibre q v) (hr : InFibre r v) :
    (swapFibreVertex q r htype v).value = fibreCoefficient r v * q.val := by
  simp [swapFibreVertex, hq, hr]

theorem swapFibreVertex_of_not_mem {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) {v : HVertex N}
    (hq : ¬InFibre q v) (hr : ¬InFibre r v) :
    swapFibreVertex q r htype v = v := by
  simp [swapFibreVertex, hq, hr]

theorem swapFibreVertex_mem_right_of_mem_left {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    {v : HVertex N} (hv : InFibre q v) :
    InFibre r (swapFibreVertex q r htype v) := by
  rw [InFibre, swapFibreVertex_value_of_mem_left q r htype hv]
  exact ⟨fibreCoefficient q v, by simp [Nat.mul_comm]⟩

theorem swapFibreVertex_not_mem_left_of_mem_left {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    (hqr : q.val ≠ r.val) {v : HVertex N} (hv : InFibre q v) :
    ¬InFibre q (swapFibreVertex q r htype v) := by
  rw [InFibre, swapFibreVertex_value_of_mem_left q r htype hv]
  intro hdvd
  rcases (q.prime.dvd_mul.mp hdvd) with hcoeff | hprime
  · exact (Nat.not_dvd_of_pos_of_lt
      (fibreCoefficient_pos q hv)
      (fibreCoefficient_lt_largePrime q q hv)) hcoeff
  · rcases (Nat.dvd_prime r.prime).mp hprime with hq_one | hq_eq
    · exact q.ne_one hq_one
    · exact hqr hq_eq

theorem swapFibreVertex_coefficient_right_of_mem_left {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    {v : HVertex N} (hv : InFibre q v) :
    fibreCoefficient r (swapFibreVertex q r htype v) = fibreCoefficient q v := by
  unfold fibreCoefficient
  rw [swapFibreVertex_value_of_mem_left q r htype hv]
  exact Nat.mul_div_cancel _ r.pos

theorem swapFibreVertex_mem_left_of_mem_right {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    {v : HVertex N} (hq : ¬InFibre q v) (hr : InFibre r v) :
    InFibre q (swapFibreVertex q r htype v) := by
  rw [InFibre, swapFibreVertex_value_of_not_mem_left_mem_right q r htype hq hr]
  exact ⟨fibreCoefficient r v, by simp [Nat.mul_comm]⟩

theorem swapFibreVertex_not_mem_right_of_mem_right {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    (hqr : q.val ≠ r.val) {v : HVertex N}
    (hq : ¬InFibre q v) (hr : InFibre r v) :
    ¬InFibre r (swapFibreVertex q r htype v) := by
  rw [InFibre, swapFibreVertex_value_of_not_mem_left_mem_right q r htype hq hr]
  intro hdvd
  rcases (r.prime.dvd_mul.mp hdvd) with hcoeff | hprime
  · exact (Nat.not_dvd_of_pos_of_lt
      (fibreCoefficient_pos r hr)
      (fibreCoefficient_lt_largePrime r r hr)) hcoeff
  · rcases (Nat.dvd_prime q.prime).mp hprime with hr_one | hr_eq
    · exact r.ne_one hr_one
    · exact hqr hr_eq.symm

theorem swapFibreVertex_coefficient_left_of_mem_right {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    {v : HVertex N} (hq : ¬InFibre q v) (hr : InFibre r v) :
    fibreCoefficient q (swapFibreVertex q r htype v) = fibreCoefficient r v := by
  unfold fibreCoefficient
  rw [swapFibreVertex_value_of_not_mem_left_mem_right q r htype hq hr]
  exact Nat.mul_div_cancel _ q.pos

theorem swapFibreVertex_involutive {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) (hqr : q.val ≠ r.val) :
    Function.Involutive (swapFibreVertex q r htype) := by
  intro v
  by_cases hq : InFibre q v
  · have hq' := swapFibreVertex_not_mem_left_of_mem_left q r htype hqr hq
    have hr' := swapFibreVertex_mem_right_of_mem_left q r htype hq
    apply HVertex.ext_value
    rw [swapFibreVertex_value_of_not_mem_left_mem_right q r htype hq' hr']
    rw [swapFibreVertex_coefficient_right_of_mem_left q r htype hq]
    simpa [Nat.mul_comm] using (value_eq_prime_mul_coefficient q hq).symm
  · by_cases hr : InFibre r v
    · have hq' := swapFibreVertex_mem_left_of_mem_right q r htype hq hr
      have hr' := swapFibreVertex_not_mem_right_of_mem_right q r htype hqr hq hr
      apply HVertex.ext_value
      rw [swapFibreVertex_value_of_mem_left q r htype hq']
      rw [swapFibreVertex_coefficient_left_of_mem_right q r htype hq hr]
      simpa [Nat.mul_comm] using (value_eq_prime_mul_coefficient r hr).symm
    · simp [swapFibreVertex_of_not_mem q r htype hq hr]

theorem swapFibreVertex_adj_of_adj {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) (hqr : q.val ≠ r.val)
    {v w : HVertex N} (hadj : (reducedDivisorGraph N).Adj v w) :
    (reducedDivisorGraph N).Adj
      (swapFibreVertex q r htype v) (swapFibreVertex q r htype w) := by
  by_cases hvq : InFibre q v
  · by_cases hwq : InFibre q w
    · apply (same_fibre_adj_iff r
        (swapFibreVertex_mem_right_of_mem_left q r htype hvq)
        (swapFibreVertex_mem_right_of_mem_left q r htype hwq)).2
      simpa [swapFibreVertex_coefficient_right_of_mem_left q r htype hvq,
        swapFibreVertex_coefficient_right_of_mem_left q r htype hwq] using
        (same_fibre_adj_iff q hvq hwq).1 hadj
    · by_cases hwr : InFibre r w
      · exact (distinct_fibres_anticomplete q r hqr hvq hwr hadj).elim
      · have hcoeff : w.value ∣ fibreCoefficient q v :=
          (outside_adj_fibre_iff q hvq hwq).1 hadj.symm
        have hvmem := swapFibreVertex_mem_right_of_mem_left q r htype hvq
        rw [swapFibreVertex_of_not_mem q r htype hwq hwr]
        apply (reducedDivisorGraph_adj _ _).2
        refine ⟨?_, Or.inr ?_⟩
        · intro heq
          apply hwr
          rw [← heq]
          exact hvmem
        · rw [swapFibreVertex_value_of_mem_left q r htype hvq]
          exact dvd_mul_of_dvd_left hcoeff r.val
  · by_cases hvr : InFibre r v
    · by_cases hwq : InFibre q w
      · exact (distinct_fibres_anticomplete r q hqr.symm hvr hwq hadj).elim
      · by_cases hwr : InFibre r w
        · apply (same_fibre_adj_iff q
            (swapFibreVertex_mem_left_of_mem_right q r htype hvq hvr)
            (swapFibreVertex_mem_left_of_mem_right q r htype hwq hwr)).2
          simpa [swapFibreVertex_coefficient_left_of_mem_right q r htype hvq hvr,
            swapFibreVertex_coefficient_left_of_mem_right q r htype hwq hwr] using
            (same_fibre_adj_iff r hvr hwr).1 hadj
        · have hcoeff : w.value ∣ fibreCoefficient r v :=
            (outside_adj_fibre_iff r hvr hwr).1 hadj.symm
          have hvmem := swapFibreVertex_mem_left_of_mem_right q r htype hvq hvr
          rw [swapFibreVertex_of_not_mem q r htype hwq hwr]
          apply (reducedDivisorGraph_adj _ _).2
          refine ⟨?_, Or.inr ?_⟩
          · intro heq
            apply hwq
            rw [← heq]
            exact hvmem
          · rw [swapFibreVertex_value_of_not_mem_left_mem_right q r htype hvq hvr]
            exact dvd_mul_of_dvd_left hcoeff q.val
    · by_cases hwq : InFibre q w
      · have hcoeff : v.value ∣ fibreCoefficient q w :=
          (outside_adj_fibre_iff q hwq hvq).1 hadj
        have hwmem := swapFibreVertex_mem_right_of_mem_left q r htype hwq
        rw [swapFibreVertex_of_not_mem q r htype hvq hvr]
        apply (reducedDivisorGraph_adj _ _).2
        refine ⟨?_, Or.inl ?_⟩
        · intro heq
          apply hvr
          rw [heq]
          exact hwmem
        · rw [swapFibreVertex_value_of_mem_left q r htype hwq]
          exact dvd_mul_of_dvd_left hcoeff r.val
      · by_cases hwr : InFibre r w
        · have hcoeff : v.value ∣ fibreCoefficient r w :=
            (outside_adj_fibre_iff r hwr hvr).1 hadj
          have hwmem := swapFibreVertex_mem_left_of_mem_right q r htype hwq hwr
          rw [swapFibreVertex_of_not_mem q r htype hvq hvr]
          apply (reducedDivisorGraph_adj _ _).2
          refine ⟨?_, Or.inl ?_⟩
          · intro heq
            apply hvq
            rw [heq]
            exact hwmem
          · rw [swapFibreVertex_value_of_not_mem_left_mem_right q r htype hwq hwr]
            exact dvd_mul_of_dvd_left hcoeff q.val
        · simpa [swapFibreVertex_of_not_mem q r htype hvq hvr,
            swapFibreVertex_of_not_mem q r htype hwq hwr] using hadj

theorem swapFibreVertex_adj_iff {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) (hqr : q.val ≠ r.val)
    (v w : HVertex N) :
    (reducedDivisorGraph N).Adj
        (swapFibreVertex q r htype v) (swapFibreVertex q r htype w) ↔
      (reducedDivisorGraph N).Adj v w := by
  constructor
  · intro hadj
    have h := swapFibreVertex_adj_of_adj q r htype hqr hadj
    simpa [swapFibreVertex_involutive q r htype hqr v,
      swapFibreVertex_involutive q r htype hqr w] using h
  · exact swapFibreVertex_adj_of_adj q r htype hqr

theorem swapFibreVertex_mem_right_iff_mem_left {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    (hqr : q.val ≠ r.val) (v : HVertex N) :
    InFibre r (swapFibreVertex q r htype v) ↔ InFibre q v := by
  constructor
  · intro hr
    have hnq : ¬InFibre q (swapFibreVertex q r htype v) :=
      distinct_fibres_disjoint r q hqr.symm hr
    have hback := swapFibreVertex_mem_left_of_mem_right q r htype hnq hr
    simpa [swapFibreVertex_involutive q r htype hqr v] using hback
  · exact swapFibreVertex_mem_right_of_mem_left q r htype

theorem swapFibreVertex_complement_bijOn {N : ℕ}
    (q r : LargePrime N) (htype : q.quotientType = r.quotientType)
    (hqr : q.val ≠ r.val) :
    Set.BijOn (swapFibreVertex q r htype)
      {v | ¬InFibre q v} {v | ¬InFibre r v} := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact fun hr ↦ hv ((swapFibreVertex_mem_right_iff_mem_left q r htype hqr v).mp hr)
  · exact (swapFibreVertex_involutive q r htype hqr).injective.injOn
  · intro w hw
    refine ⟨swapFibreVertex q r htype w, ?_,
      swapFibreVertex_involutive q r htype hqr w⟩
    intro hq
    have hr := swapFibreVertex_mem_right_of_mem_left q r htype hq
    rw [swapFibreVertex_involutive q r htype hqr w] at hr
    exact hw hr

/-- The graph automorphism exchanging two distinct fibres of the same type. -/
noncomputable def sameTypeFibreIso {N : ℕ} (q r : LargePrime N)
    (htype : q.quotientType = r.quotientType) (hqr : q.val ≠ r.val) :
    reducedDivisorGraph N ≃g reducedDivisorGraph N where
  toFun := swapFibreVertex q r htype
  invFun := swapFibreVertex q r htype
  left_inv := swapFibreVertex_involutive q r htype hqr
  right_inv := swapFibreVertex_involutive q r htype hqr
  map_rel_iff' := by
    intro v w
    exact swapFibreVertex_adj_iff q r htype hqr v w

end DivisorF
