import DivisorF.Defect
import DivisorF.PathForest
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The coupling defect in the manuscript's own form

`DivisorF.Defect` defines the coupling defect by the `lambda` identity (2.6),

`D_N(q) = lambda(H_N) - lambda(R_{N,q}) - lambda(G_s)`,

whereas Definition 2.3 of the manuscript defines it by (2.5),

`D_N(q) = P(R_{N,q}) + F(s) - P(H_N)`,

and derives (2.6) from it through Lemma 2.2. With Lemma 2.2 machine-checked in
`DivisorF.PathForest`, the two forms can now be shown to agree: what remains is
the vertex count `|V(H_N)| = |V(R_{N,q})| + s`, which is exactly the statement
that the fibre `B_q(N)` has `s` vertices.

After this module the formalized defect is the manuscript's defect, not merely a
quantity that happens to satisfy the same identity.
-/

namespace DivisorF

open SimpleGraph

/-- `F(N) = P(G_N)`, the manuscript's minimum path-partition number of the
divisor graph on `{1, ..., N}`. -/
noncomputable def divisorPathPartitionNumber (N : ℕ) : ℕ :=
  pathPartitionNumber (divisorGraph N)

@[simp]
theorem card_GVertex (N : ℕ) : Fintype.card (GVertex N) = N := by
  simp [GVertex]

/-- The fibre `B_q(N)` has exactly `s = ⌊N/q⌋` vertices. -/
theorem card_inFibre {N : ℕ} (q : LargePrime N) :
    Fintype.card {v : HVertex N // InFibre q v} = q.quotientType := by
  classical
  have h := Fintype.card_congr (fibreIso q).toEquiv
  rw [h, card_GVertex]

/-- The fibre and its complement split the vertices of `H_N`. -/
theorem card_fibreComplement_add_quotientType {N : ℕ} (q : LargePrime N) :
    Fintype.card {v : HVertex N // ¬ InFibre q v} + q.quotientType
      = Fintype.card (HVertex N) := by
  classical
  have hsplit :=
    Fintype.card_congr (Equiv.sumCompl (InFibre q))
  rw [Fintype.card_sum] at hsplit
  rw [← card_inFibre q]
  omega

/-- **Definition 2.3, in the manuscript's own form.**

The defect represented in `DivisorF` by the `lambda` identity (2.6) is the
manuscript's `P(R_{N,q}) + F(s) - P(H_N)` of (2.5). -/
theorem fibreDefect_eq_pathPartitionForm {N : ℕ} (q : LargePrime N) :
    fibreDefect q =
      (pathPartitionNumber (fibreComplement q) : ℤ)
        + (divisorPathPartitionNumber q.quotientType : ℤ)
        - (pathPartitionNumber (reducedDivisorGraph N) : ℤ) := by
  classical
  have hH := pathPartitionNumber_add_linearForestNumber (reducedDivisorGraph N)
  have hR := pathPartitionNumber_add_linearForestNumber (fibreComplement q)
  have hG := pathPartitionNumber_add_linearForestNumber (divisorGraph q.quotientType)
  have hcard := card_fibreComplement_add_quotientType q
  have hGs : Fintype.card (GVertex q.quotientType) = q.quotientType := card_GVertex _
  unfold fibreDefect divisorPathPartitionNumber
  omega

end DivisorF
