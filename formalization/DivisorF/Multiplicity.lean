import DivisorF.Defect
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Quotient-type multiplicity and common-defect packaging

This module starts the original Section 3.4 boundary/multiplicity layer. It
packages the finite same-type prime classes `Q_s(N)`, their multiplicities
`t_s(N)`, and the common defect `d_s(N)`, then lifts the already machine-checked
pointwise bound `D_N(q) ≤ m_L(q)` to one common maximum forest across the whole
same-type class.
-/

namespace DivisorF

namespace LargePrime

private def toBounded {N : ℕ} (q : LargePrime N) : Fin (N + 1) :=
  ⟨q.val, Nat.lt_succ_of_le q.le_N⟩

private theorem toBounded_injective {N : ℕ} :
    Function.Injective (@toBounded N) := by
  intro q r h
  have hval : q.val = r.val := congrArg Fin.val h
  cases q with
  | mk qval qprime qlarge qle =>
      cases r with
      | mk rval rprime rlarge rle =>
          simp only at hval
          subst rval
          rfl

instance finite (N : ℕ) : Finite (LargePrime N) :=
  Finite.of_injective (@toBounded N) (@toBounded_injective N)

noncomputable instance fintype (N : ℕ) : Fintype (LargePrime N) :=
  Fintype.ofFinite _

end LargePrime

/-- `Q_s(N)`: large primes whose quotient type is exactly `s`. -/
noncomputable def typePrimes (N s : ℕ) : Finset (LargePrime N) := by
  classical
  exact Finset.univ.filter (fun q => q.quotientType = s)

@[simp]
theorem mem_typePrimes {N s : ℕ} {q : LargePrime N} :
    q ∈ typePrimes N s ↔ q.quotientType = s := by
  classical
  simp [typePrimes]

/-- `t_s(N)=|Q_s(N)|`. -/
noncomputable def typeMultiplicity (N s : ℕ) : ℕ :=
  (typePrimes N s).card

/-- The quotient type `s` actually occurs among the large-prime fibres. -/
def TypeOccupied (N s : ℕ) : Prop :=
  (typePrimes N s).Nonempty

/-- A canonical representative of an occupied quotient type. -/
noncomputable def typeRepresentative {N s : ℕ}
    (h : TypeOccupied N s) : LargePrime N :=
  h.choose

@[simp]
theorem typeRepresentative_mem {N s : ℕ}
    (h : TypeOccupied N s) :
    typeRepresentative h ∈ typePrimes N s :=
  h.choose_spec

/-- `d_s(N)`, represented in `ℤ` as in the existing defect layer. -/
noncomputable def typeDefect {N s : ℕ}
    (h : TypeOccupied N s) : ℤ :=
  fibreDefect (typeRepresentative h)

/-- Same-type invariance makes the representative definition canonical. -/
theorem fibreDefect_eq_typeDefect {N s : ℕ}
    (h : TypeOccupied N s) {q : LargePrime N}
    (hq : q ∈ typePrimes N s) :
    fibreDefect q = typeDefect h := by
  unfold typeDefect
  apply sameType_fibreDefect
  rw [(mem_typePrimes.mp hq),
    (mem_typePrimes.mp (typeRepresentative_mem h))]

/-- The common type defect is genuinely nonnegative. -/
theorem typeDefect_nonneg {N s : ℕ}
    (h : TypeOccupied N s) : 0 ≤ typeDefect h := by
  unfold typeDefect
  exact fibreDefect_nonneg _

/-- Natural form of the already-proved nonnegative common defect. -/
noncomputable def typeDefectNat {N s : ℕ}
    (h : TypeOccupied N s) : ℕ :=
  Int.toNat (typeDefect h)

@[simp]
theorem coe_typeDefectNat {N s : ℕ}
    (h : TypeOccupied N s) :
    (typeDefectNat h : ℤ) = typeDefect h := by
  exact Int.toNat_of_nonneg (typeDefect_nonneg h)

/-- Pointwise defect bound rewritten at quotient-type level. -/
theorem typeDefectNat_le_crossingCount {N s : ℕ}
    (hocc : TypeOccupied N s)
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    {q : LargePrime N}
    (hq : q ∈ typePrimes N s) :
    typeDefectNat hocc ≤ crossingCount q L := by
  have hle := fibreDefect_le_crossingCount q hL hmax
  rw [fibreDefect_eq_typeDefect hocc hq,
    ← coe_typeDefectNat hocc] at hle
  exact_mod_cast hle

/--
One-common-optimum form of the same-type accounting step:

` t_s(N) d_s(N) ≤ Σ_{q∈Q_s(N)} m_L(q) `.

The next theorem in the block will bound the right-hand side by the available
boundary degree slots `2(s-1)`.
-/
theorem typeMultiplicity_mul_typeDefectNat_le_crossingSum {N s : ℕ}
    (hocc : TypeOccupied N s)
    {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N)) :
    typeMultiplicity N s * typeDefectNat hocc
      ≤ Finset.sum (typePrimes N s) (fun q => crossingCount q L) := by
  calc
    typeMultiplicity N s * typeDefectNat hocc
        = Finset.sum (typePrimes N s) (fun _q => typeDefectNat hocc) := by
            simp [typeMultiplicity, Nat.mul_comm]
    _ ≤ Finset.sum (typePrimes N s) (fun q => crossingCount q L) := by
          apply Finset.sum_le_sum
          intro q hq
          exact typeDefectNat_le_crossingCount hocc hL hmax hq

end DivisorF
