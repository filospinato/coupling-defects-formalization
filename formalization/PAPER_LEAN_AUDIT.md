# Paper-to-Lean correspondence

References below follow *Coupling defects of large-prime fibres in optimal path
partitions of the divisor graph* by Filippo Cavallari. Declaration names are in
the `DivisorF` namespace; sources are in [DivisorF/](DivisorF/).
See the [README](../README.md) for verification commands.

**Checked** means proved from the stated mathematical hypotheses.
**Conditional** means an additional analytic input remains an explicit hypothesis.
The formalization uses only `propext`, `Classical.choice`, and `Quot.sound`.

| Paper | Lean declarations | Scope |
| --- | --- | --- |
| 2.1 | `pathPartitionNumber_add_linearForestNumber` | Checked; subtraction-free form |
| 2.2 | `fibreDefect`, `fibreDefect_eq_pathPartitionForm` | Definition and checked equivalence |
| 2.3 | `fibreDefect_nonneg` | Checked |
| 2.4 | `crossing_localization`, `crossing_value_le_coefficient` | Checked |
| 2.5 | `distinct_fibres_disjoint`, `distinct_fibres_anticomplete` | Checked |
| 2.6 | `sameType_fibreDefect` | Checked |
| 2.7 | `factorizingPartitionNumber_eq`, `fibreDefect_eq_factorizationPenalty`, `fibreDefect_eq_zero_iff_exists_factorizing_optimum` | Checked |
| 2.8 | [Python certificate verifier](../ancillary/verify_certificate.py) | `D_507(23)=2`; outside Lean |
| 3.1 | `fibreDefect_eq_crossing_sub_losses`, `fibreDefect_nonneg`, `fibreDefect_le_crossingCount` | Checked, with support lemmas |
| 3.2 | `cumulativeDefectSum_eq_paperTypeContributionSum`, `cumulativeDefectSum_le` | Checked |
| 3.3 | `paperTypeMultiplicity_mul_typeDefect_le`, `paperTypeDefect_le_multiplicity_floor`, `exact_zero_threshold`, `exact_binary_threshold` | Checked |
| 3.4 | `tailDefectSum_le` | Checked |
| 4.1 | `defectSpectrum_le_variational` | Checked |
| 4.2 | `defectSpectrum_real_le_fixed_of_balanced_prefix` | Conditional; finite `(4+ε)` form |
| 4.3 | `exists_uniform_defect_spectrum_envelope_of_balanced_prefix_input` | Conditional |
| 4.4 | `positiveDefectRelativeDensity_le_pnt_scale` | Conditional; density bound only |
| 5.1 | `vertexSensitivity_linearForestNumber`, `vertexSensitivity_pathPartitionNumber`, `abs_divisorPathPartitionNumber_sub_le` | Checked |
| 5.2 | `truncatedComplementIso`, `crossTypeTransport`, `crossTypeDefectLipschitz` | Checked |
| 5.3 | `primeWindowBound_real`, `primeWindowBound` | Checked |
| 5.4 | `fibreDefect_le_explicit_of_bhp`, `fibreDefect_le_uniform_of_bhp`, `fibreDefect_le_quotient_power_of_bhp`, `fibreDefect_le_ambient_power_of_bhp` | Conditional |
| 6.1 | `ShortIntervalPrimeInput` | Definition |
| 6.2 | `shortIntervalQuotientRichness`, `eventuallyZeroDefectOn_quotientPowerRange_of_shortInterval`, `eventuallyZeroDefectOn_naturalPowerCone_of_shortInterval` | Checked from the stated `SI(β)` hypothesis |
| 6.3 | `coneExponent_bakerHarmanPintz`, `fibreDefect_eq_zero_of_cone_and_prime_lower`, short-interval transfer | Conditional |
| 6.4 | `exists_beta_of_lt_third`, `eventuallyZeroDefect_riemann_cone_of_shortInterval` | Conditional |
| A.1 | `fibreDefect_ge_crossing_sub_losses` | Checked; arbitrary-forest form |
| B.1 | `integerDiscretisationCore_of_manuscript` | Partial, conditional coverage |
| B.2 | `section6RegularEndpointPackage_of_fixedPrecision_and_packetDominates` | Conditional |
| B.3 | `cubicNaturalRelativeDensityZero_of_sparse_bad_endpoints_cubicScale` | Conditional |
| B.4 | — | Scoping remark; no separate Lean statement |

## External inputs and limits

- **4.2–4.4:** prime-counting inputs at the prime number theorem scale remain
  hypotheses. The high-level branch of 4.3 is unconditional; the final elementary
  limit to zero in 4.4 is not separately formalized.
- **5.4:** assumes `BakerHarmanPintzInput`. **6.3:** assumes
  `ShortIntervalPrimeInput (21/40)`; the deduction of this input from the
  Baker–Harman–Pintz theorem is not formalized.
- **6.4:** assumes `SI(β)` for every `1/2 < β < 1`, with constants and thresholds
  allowed to depend on `β`. Lean proves the cone for each fixed `0 < γ < 1/3`.
  The implication from RH/Schoenfeld to this family is not formalized.
- **B.1–B.3:** exceptional-set and prime-packet estimates remain explicit inputs.
  B.1 uses a fixed-precision/diagonalisation construction; the paper's shortened
  one-set argument and proper-prime-power removal are not separately formalized.
- The universal-vertex normalisation and `D_8(3)=1` are not Lean targets.
  The unnumbered Section 5 asymptotic and inverse bounds are not separately
  packaged. The transport penalty and ramp are checked in `transportPenalty_bounds`,
  `fibreDefect_sub_transportPenalty_le`, and `transportRampSum_le`; the Lean proof
  of 5.3 instead uses the cumulative window budget.
