# Theorem Map - C2 to RH

This map connects the paper-level route to Lean declarations in the public
`LeanC2/` tree. It is intentionally conservative: it distinguishes statements
proved directly in Lean from certificate interfaces consumed by the terminal
route.

Public facade:

```lean
import LeanC2.PeerReview
```

Namespace:

```lean
namespace C2.PeerReview
```

## Layer 1 - Dyadic foundations

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| Odd legs have the expected effective depth | C2 bracket depth | `LeanC2/Foundations/Dyadic.lean` | `C2.keff_left_leg`, `C2.keff_right_leg` | Lean-proved |
| Every odd integer `n >= 3` has a unique C2 leg address | C2 bracket bijection | `LeanC2/Foundations/Dyadic.lean` | `C2.bracket_bijection_odd_ge_three` | Lean-proved |
| Direct and bracket weights agree on odd legs | Halving law | `LeanC2/Foundations/Dyadic.lean` | `C2.halving_law_odd_ge_three` | Lean-proved |

## Layer 2 - Finite and infinite lateral cancellation

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| A finite C2 address cancels laterals and leaves the center term | Local lateral cancellation | `LeanC2/Operators/FiniteCancellation.lean` | `C2.local_lateral_cancellation` | Lean-proved |
| Finite C2 rectangles cancel laterals | Rectangular cancellation | `LeanC2/Operators/FiniteCancellation.lean` | `C2.rectangular_lateral_cancellation` | Lean-proved |
| The infinite lateral difference collapses to the central tower in `Re(s)>1` | Genuine lateral cancellation | `LeanC2/Analytic/GenuineInfinite.lean` | `C2.directLateralInfinite_sub_bracketLateralInfinite_eq_central_of_one_lt_re` | Lean-proved |

## Layer 3 - Genuine numerator and fundamental identity

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| The genuine numerator is `D_infty - B_infty` | Genuine numerator | `LeanC2/Analytic/GenuineLateralInfinite.lean` | `C2.genuineFInfinite` | Definition |
| The central tower factors through the odd Dirichlet channel | Central odd-channel identity | `LeanC2/Analytic/GenuineInfinite.lean` | `C2.genuineCentralDoubleSeries_eq_centralFromOddChannel` | Lean-proved |
| The genuine numerator satisfies `F = c0 * zeta` for `Re(s)>1` | Fundamental identity | `LeanC2/Analytic/GenuineLateralInfinite.lean` | `C2.genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re` | Lean-proved |
| Roadmap spelling of the same identity | Fundamental identity | `LeanC2/Analytic/GenuineLateralInfinite.lean` | `C2.F_eq_c0_mul_zeta_sigma_gt_one` | Lean-proved |
| The normalizing factor is nonzero in the positive half-plane | `c0` nonvanishing | `LeanC2/Identity/C0.lean` | `C2.c0_ne_zero_of_re_pos` | Lean-proved |
| The normalizing factor is nonzero on the critical line | Critical-line `c0` nonvanishing | `LeanC2/Identity/C0.lean` | `C2.c0_ne_zero_on_critical` | Lean-proved |

## Layer 4 - Critical barrier and transversal tilt

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| Branch norm has a closed form depending only on `sigma` | Branch norm formula | `LeanC2/Operators/BranchBarrier.lean` | `C2.branchNormSq_closed_form` | Lean-proved |
| Branch norm is exactly critical at `sigma = 1/2` | Branch barrier | `LeanC2/Operators/BranchBarrier.lean` | `C2.branchNormSq_barrier` | Lean-proved |
| Complex branch wrapper is critical on the critical line | Critical-line branch norm | `LeanC2/Operators/BranchBarrier.lean` | `C2.branchNormSqSigmaT_eq_one_on_critical` | Lean-proved |
| The tilt bracket vanishes on the critical line | Tilt zero | `LeanC2/Operators/Tilt.lean` | `C2.bracket_tilt_zero` | Lean-proved |
| The tilt bracket has definite sign off the line | Tilt sign | `LeanC2/Operators/Tilt.lean` | `C2.bracket_tilt_pos`, `C2.bracket_tilt_neg` | Lean-proved |
| Vanishing of the tilt bracket characterizes zero displacement | Tilt zero iff | `LeanC2/Operators/Tilt.lean` | `C2.bracket_tilt_zero_iff_delta_zero` | Lean-proved |

## Layer 5 - Continuation and near-critical-zero regime

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| Continuation package for the genuine C2 operator | Genuine continuation | `LeanC2/Analytic/GenuineContinuation.lean` | `C2.GenuineFInfiniteContinuationData` | Optional certificate interface |
| Continuation gives the fundamental identity in the required region | Continued identity | `LeanC2/Analytic/GenuineContinuation.lean` | `C2.GenuineFInfiniteContinuationData.fundamentalIdentity` | Lean wrapper over certificate |
| Continued C2 model is analytic on the punctured right half-plane | Continued-model analyticity | `LeanC2/Analytic/GenuineBulkConcrete/Base.lean` | `C2.c2OddTailContinuedBalancingSeedBulkModel_analyticOnNhd_punctured` | Lean-proved |
| Continued C2 model supplies near-critical-zero data | Near-critical-zero from continued model | `LeanC2/Analytic/GenuineBulkConcrete/Base.lean` | `C2.C2OddTailContinuedBalancingSeedBulkModelNearAxisData.ofContinuedModel` | Lean-proved |

## Layer 6 - Vertical resolvent and middle-region bulk

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| Vertical depth ratio has norm `< 1` in the strip | Vertical ratio | `LeanC2/Operators/VerticalResolvent.lean` | `C2.q_norm_lt_one_of_offCriticalStrip` | Lean-proved |
| The vertical tower is a geometric resolvent | Dyadic resolvent | `LeanC2/Operators/VerticalResolvent.lean` | `C2.geom_resolvent` | Lean-proved |
| Resolvent lower bound | Resolvent non-cancellation lower bound | `LeanC2/Operators/VerticalResolvent.lean` | `C2.resolvent_lower_bound_of_offCriticalStrip` | Lean-proved |
| Quartet prefix is formalized | Dominant four-level block | `LeanC2/Operators/VerticalResolvent.lean` | `C2.verticalQuartetPrefix` | Definition |
| Quartet lower bound in the off-critical strip | Quartet dominance | `LeanC2/Operators/VerticalResolvent.lean` | `C2.verticalQuartetPrefix_norm_lower_bound_of_offCriticalStrip` | Lean-proved |
| Public middle-region dominance interface | Resolvent non-cancellation criterion | `LeanC2/PeerReview.lean` | `C2.PeerReview.ResolventNonCancellationCriterion_of_budgetBounds` | Lean-proved wrapper |
| Adjusted residual-budget dominance interface | Adjusted non-cancellation criterion | `LeanC2/PeerReview.lean` | `C2.PeerReview.AdjustedResolventNonCancellationCriterion_of_residualBudgetBounds` | Lean-proved wrapper |

## Layer 7 - Cutoff, witnesses, and terminal middle certificate

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| Cutoff estimate packages are exposed for audit | Cutoff control | `LeanC2/PeerReview.lean` | `C2.PeerReview.BalancingSeedExplicitCutoffEstimates` | Facade alias |
| Oscillatory residual witnesses are exposed for audit | Oscillatory witness | `LeanC2/PeerReview.lean` | `C2.PeerReview.PointwiseOscillatoryResidualUpper`, `C2.PeerReview.ExponentialPointwiseOscillatoryResidualUpper` | Facade aliases |
| Canonical local middle witness | Middle local certificate | `LeanC2/Analytic/GenuineBulkConcrete/Terminal.lean` | `C2.C2CanonicalClosedScaledMiddleLocalData` | Certificate interface |
| Terminal package | Terminal C2 certificate | `LeanC2/Analytic/GenuineBulkConcrete/Terminal.lean` | `C2.RiemannHypothesisTerminalData` | Certificate interface |
| Public constructor from continued-model near-axis and middle-local data | Canonical terminal assembly | `LeanC2/PeerReview.lean` | `C2.PeerReview.TerminalCertificate_of_continuedModelMiddleLocal` | Facade constructor |
| Public constructor from continued-model residual bounds | Residual terminal assembly | `LeanC2/PeerReview.lean` | `C2.PeerReview.TerminalCertificate_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds` | Facade constructor |
| Public continued-model residual middle endpoint | Residual middle bounds | `LeanC2/PeerReview.lean` | `C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds` | Lean-proved wrapper over pointwise bounds |
| Public constructor from continuation and middle-local data | Continuation audit assembly | `LeanC2/PeerReview.lean` | `C2.PeerReview.TerminalCertificate_of_continuationAndMiddleLocal` | Facade constructor |

## Layer 8 - Gluing and transfer to RH

| Claim | Paper label | Lean file | Lean declaration | Status |
| --- | --- | --- | --- | --- |
| A regional cover gives off-critical nonvanishing | Regional gluing | `LeanC2/PeerReview.lean` | `C2.PeerReview.OffCriticalNonvanishing_of_regionalCover` | Lean-proved wrapper |
| C2 nonvanishing transfers to zeta nonvanishing | C2/zeta transfer | `LeanC2/PeerReview.lean` | `C2.PeerReview.ZetaNonvanishing_of_C2Nonvanishing` | Lean-proved wrapper |
| C2 nonvanishing transfers to mathlib RH | Transfer to RH | `LeanC2/PeerReview.lean` | `C2.PeerReview.RiemannHypothesis_of_C2Nonvanishing` | Lean-proved wrapper |
| Terminal certificate implies mathlib RH | Final endpoint | `LeanC2/PeerReview.lean` | `C2.PeerReview.RiemannHypothesis_of_terminalCertificate` | Lean-proved implication over terminal certificate |
| Continued-model near-axis plus canonical middle-local data imply mathlib RH | Canonical terminal endpoint | `LeanC2/PeerReview.lean` | `C2.PeerReview.RiemannHypothesis_of_continuedModelMiddleLocal` | Lean-proved wrapper over route packages |
| Continuation plus canonical middle-local data imply mathlib RH | Continuation audit endpoint | `LeanC2/PeerReview.lean` | `C2.PeerReview.RiemannHypothesis_of_continuationAndMiddleLocal` | Lean-proved wrapper over route packages |

## Reading rule

The paper should use the conceptual labels. Auditors should use the Lean
declarations above and the fuller public maps in:

```text
docs/MAIN_ROUTE_MAP.md
docs/THEOREM_MAP_REVIEW.md
docs/BOUNDS_CERTIFICATES_WITNESSES.md
docs/LEAN_MODULE_LAYOUT.md
```

As of this working revision, no closed zero-argument declaration named
`C2.PeerReview.terminalCertificate` is exposed.  The facade does expose the
canonical constructor and endpoint from the continued-model near-axis package
plus middle-local data:
`C2.PeerReview.TerminalCertificate_of_continuedModelMiddleLocal` and
`C2.PeerReview.RiemannHypothesis_of_continuedModelMiddleLocal`.  It also
exposes a terminal-certificate constructor from residual pointwise bounds and
the continued-model pointwise and residual middle-bound endpoints:
`C2.PeerReview.TerminalCertificate_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds`,
`C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddlePointwiseBounds`,
`C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds`,
and
`C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualAnalyticBounds`.
