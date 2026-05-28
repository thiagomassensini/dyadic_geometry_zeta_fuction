# Formalization Companion - C2 to RH

This companion records the formal side of the paper draft.  The paper should
communicate the mathematical route; this file records the Lean entry points,
certificate boundary, build command, and audit checks.

## Environment

Repository:

```text
https://github.com/thiagomassensini/dyadic_geometry_zeta_fuction
```

Current certified Lean release referenced by the draft:

```text
tag: v1.1.0
commit: 78fd56e
Zenodo DOI: 10.5281/zenodo.20401742
```

Toolchain:

```text
lean-toolchain: leanprover/lean4:v4.29.1
Lean: Lean 4.29.1, commit f72c35b3f637c8c6571d353742168ab66cc22c00
Lake: Lake 5.0.0-src+f72c35b
mathlib: inputRev v4.29.1
mathlib revision: 5e932f97dd25535344f80f9dd8da3aab83df0fe6
```

The paper files in this directory are a working paper snapshot.  If they are
archived separately, the release tag and DOI in the paper should be updated to
the tag that contains the final paper source.

## Build Command

The formal Lean route is checked from the repository root by:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

The same target is used by the GitHub Actions workflow.

## Final Endpoint

Review-facing import:

```lean
import LeanC2.PeerReview
```

Public endpoint:

```lean
C2.PeerReview.RiemannHypothesis_of_terminalCertificate
```

Public terminal certificate:

```lean
C2.PeerReview.RiemannHypothesisTerminalCertificate
```

Internal endpoint:

```lean
C2.mathlibRiemannHypothesis_of_terminalData
```

Target proposition:

```lean
RiemannHypothesis
```

The endpoint is mathlib's official `RiemannHypothesis` proposition.  It is not
a local replacement definition.

## Closed Certificate Status

As of this working revision, there is no exposed zero-argument declaration
named:

```lean
C2.PeerReview.terminalCertificate
```

The review-facing endpoint is therefore the checked implication:

```lean
C2.PeerReview.RiemannHypothesis_of_terminalCertificate :
  C2.PeerReview.RiemannHypothesisTerminalCertificate ->
  RiemannHypothesis
```

The facade also exposes the canonical route-package assembly layer:

```lean
C2.PeerReview.TerminalCertificate_of_continuedModelMiddleLocal
C2.PeerReview.RiemannHypothesis_of_continuedModelMiddleLocal
```

These declarations build and consume terminal data from the canonical
near-critical-zero data for the continued C2 model plus the canonical
middle-local witness.  The older continuation-based pair
`C2.PeerReview.TerminalCertificate_of_continuationAndMiddleLocal` and
`C2.PeerReview.RiemannHypothesis_of_continuationAndMiddleLocal` remain exposed
as an audit variant.  None of these declarations is a zero-argument closed
theorem; they make the route boundary explicit.

The current smallest public middle-region target is no longer the raw
middle-local certificate.  The review facade now exposes the continued-model
middle region:

```lean
C2.PeerReview.ContinuedModelTerminalMiddleRegion
```

and three sharper endpoints:

```lean
C2.PeerReview.TerminalCertificate_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds
C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddlePointwiseBounds
C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds
C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualAnalyticBounds
```

These reduce the remaining closure target to pointwise middle-region estimates:
positivity and nonnegativity of the horizontal scale data, the geometric
horizontal-layer budget, and either the full canonical dominance inequality or
a residual dominance inequality.  Once those estimates are constructed for
concrete cutoff and budget functions, the public endpoint derives
`RiemannHypothesis` directly through the continued-model terminal route.

The older local map in `local/MAPA_ROTA_PRINCIPAL.md` is consistent with this:
it does not contain a closed zero-argument terminal certificate, and it marks
the fully explicit finite exact-zeta residual route as non-terminal.

## Paper-to-Lean Route

The detailed theorem map is maintained in:

```text
paper/THEOREM_MAP.md
docs/MAIN_ROUTE_MAP.md
docs/THEOREM_MAP_REVIEW.md
docs/BOUNDS_CERTIFICATES_WITNESSES.md
docs/LEAN_MODULE_LAYOUT.md
```

Minimal route table:

| Paper layer | Lean declaration | Status |
| --- | --- | --- |
| C2 bracket bijection | `C2.bracket_bijection_odd_ge_three` | Lean-proved |
| Halving law | `C2.halving_law_odd_ge_three` | Lean-proved |
| Infinite lateral cancellation | `C2.directLateralInfinite_sub_bracketLateralInfinite_eq_central_of_one_lt_re` | Lean-proved |
| Genuine numerator identity | `C2.genuineFInfinite_eq_c0_mul_riemannZeta_of_one_lt_re` | Lean-proved in `Re(s)>1` |
| Nonvanishing of `c0` | `C2.c0_ne_zero_of_re_pos` | Lean-proved |
| Genuine continuation | `C2.PeerReview.GenuineC2ContinuationData` | Optional certificate interface |
| Continued-model near-critical-zero data | `C2.PeerReview.ContinuedBulkNearCriticalZeroData_canonical` | Lean-proved |
| Branch barrier | `C2.branchNormSq_barrier` | Lean-proved |
| Transversal tilt | `C2.bracket_tilt_zero_iff_delta_zero` | Lean-proved |
| Resolvent lower bound | `C2.resolvent_lower_bound_of_offCriticalStrip` | Lean-proved |
| Quartet lower bound | `C2.verticalQuartetPrefix_norm_lower_bound_of_offCriticalStrip` | Lean-proved |
| Middle-region dominance | `C2.PeerReview.ResolventNonCancellationCriterion_of_budgetBounds` | Lean wrapper over budget hypotheses |
| Adjusted residual-budget dominance | `C2.PeerReview.AdjustedResolventNonCancellationCriterion_of_residualBudgetBounds` | Lean wrapper over budget hypotheses |
| Canonical terminal assembly | `C2.PeerReview.RiemannHypothesis_of_continuedModelMiddleLocal` | Lean-proved wrapper over canonical near-axis data plus middle-local data |
| Continued-model residual middle bounds | `C2.PeerReview.RiemannHypothesis_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds` | Public endpoint from horizontal budget plus residual dominance |
| Continued-model residual terminal certificate | `C2.PeerReview.TerminalCertificate_of_continuedModelCanonicalClosedScaledMiddleResidualPointwiseBounds` | Public constructor of the terminal certificate from the same residual bounds |
| Regional gluing | `C2.PeerReview.OffCriticalNonvanishing_of_regionalCover` | Lean-proved wrapper |
| C2/zeta transfer | `C2.PeerReview.ZetaNonvanishing_of_C2Nonvanishing` | Lean-proved wrapper |
| Terminal endpoint | `C2.PeerReview.RiemannHypothesis_of_terminalCertificate` | Lean-proved implication over terminal certificate |

## Certificate Boundary

The paper must keep the following boundary explicit.

Lean-proved structural layers:

- C2 dyadic addressing and halving law.
- Finite and infinite lateral cancellation.
- The `F = c0 * zeta` identity in the absolute-convergence half-plane.
- Nonvanishing of the normalizing factor `c0` in the required region.
- Branch barrier and transversal tilt identities.
- Resolvent and quartet lower-bound lemmas.
- Regional-cover, transfer, and endpoint wrappers.

Certificate/interface layers:

- Optional analytic continuation package for the genuine operator.
- Canonical near-critical-zero local data for the continued C2 model.
- Middle-region cutoff, residual, and witness budgets.
- Terminal C2 certificate data consumed by the final endpoint.

The paper should not present certificate interfaces as unconditional analytic
theorems unless the corresponding Lean declaration proves the data internally.

## Terminal Certificate Fields

Internal structure:

```lean
C2.RiemannHypothesisTerminalData
```

Public alias:

```lean
C2.PeerReview.RiemannHypothesisTerminalCertificate
```

Main fields:

| Field | Meaning |
| --- | --- |
| `coreCutoff : Nat -> Nat` | cutoff schedule for the finite certified model |
| `K : Nat`, `M : Nat` | calibrated dyadic and truncation parameters |
| `horizontalConstant : Complex -> Real` | horizontal budget constant |
| `horizontalScale : Complex -> Real` | horizontal scale budget |
| `horizontalRatio : Complex -> Real` | horizontal contraction ratio |
| `middle : C2CanonicalClosedScaledMiddleLocalData ...` | near/edge data plus pointwise canonical middle witness |

## Public Naming Policy

Use these names in the paper:

- resolvent non-cancellation
- dominant four-level block
- residual budget
- calibrated residual seed
- finite certification
- terminal C2 certificate

Do not use historical discovery labels in paper theorem names.

## Placeholder Audit

Recommended check for unclosed Lean placeholders:

```bash
rg "\bsorry\b|\badmit\b|^\s*axiom\b|^\s*constant\b" LeanC2 LeanC2.lean
```

For the `v1.1.0` certified snapshot this check is expected to return no
matches in the public `LeanC2` tree.

## Paper Build

The LaTeX draft is built by:

```bash
cd paper
pdflatex main.tex
```

The generated PDF is a build artifact.  The source of record is `paper/main.tex`
plus the formal companion files above.
