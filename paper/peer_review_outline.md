# Dyadic Geometry of the Zeta Function

Draft outline for peer-review preparation.

## Abstract draft

We present a dyadic C2 operator framework for studying the off-critical nonvanishing problem associated with the Riemann zeta function. The construction separates the proof architecture into a local near-critical-zero regime, a middle-region dominance regime, an edge regime, and a transfer theorem. The formal endpoint is the official `RiemannHypothesis` proposition in mathlib. The accompanying Lean development verifies the route from the stated C2 certificates and the C2/zeta identity to this endpoint.

## 1. Introduction

### 1.1 Motivation

The central aim is to express the zeta nonvanishing problem through a structured dyadic C2 operator route.

The proof architecture is organized around:

- a C2 operator identity with `riemannZeta`;
- a regional cover of the off-critical strip;
- local nonvanishing near critical-line zeros;
- middle-region non-cancellation via dominance;
- edge-region nonvanishing;
- transfer to mathlib's `RiemannHypothesis`.

### 1.2 Contributions

The review-facing claims should be stated as:

1. A formal C2/zeta transfer layer.
2. A regional-cover abstraction for off-critical nonvanishing.
3. A continuation bridge for the genuine C2 operator.
4. A terminal certificate packaging the route to mathlib `RiemannHypothesis`.
5. A Lean-checked implementation of the route.

### 1.3 What is formalized

State precisely which theorem closes the route and which data it consumes.

### 1.4 What is not hidden

List the mathematical inputs/certificates required by the chosen terminal theorem.

This section must distinguish:

- Lean-verified plumbing;
- analytic identities already packaged;
- regional bound/certificate inputs;
- optional stronger middle-region routes.

## 2. Preliminaries

Define `s = σ + it`, the critical strip, the critical line, and the off-critical strip.

Explain the mathlib endpoint:

```lean
RiemannHypothesis
```

Introduce:

```lean
offCriticalStripNonvanishing riemannZeta
```

## 3. The C2 operator identity

Introduce the genuine C2 operator and the scalar factor `c0`.

State the identity:

```text
F(s) = c0(s) * ζ(s)
```

on the required domain.

Then state the transfer theorem:

```text
C2 operator nonvanishing on the off-critical strip
  -> zeta nonvanishing on the off-critical strip
  -> RiemannHypothesis
```

## 4. Regional cover of the off-critical strip

Define:

- near-critical-zero region;
- middle region;
- edge region.

State the regional assembly theorem:

```text
Near certificate + middle certificate + edge certificate + cover
  -> off-critical nonvanishing of F
```

## 5. Near-critical-zero regime

Explain why local punctured nonvanishing near critical-line zeros is enough for the near region.

State the continuation-based near certificate.

Optionally state the more explicit Taylor/Leibniz formulation.

## 6. Middle-region non-cancellation regime

Introduce the middle-region decomposition into a main term and residual terms.

State the clean theorem:

```text
main term > sum of residual budgets
  -> F(s) ≠ 0
```

Use formal names:

- `ResolventNonCancellationCriterion`
- `DominantFourLevelBlockInequality`
- `ResidualBudgetDominance`
- `CalibratedResidualSeed`

## 7. Edge-region regime

State the edge certificate used in the terminal route.

If the edge is empty for the selected model, say so explicitly and explain the cover consequence.

## 8. Terminal theorem

State the final theorem:

```text
RiemannHypothesisTerminalCertificate
  -> RiemannHypothesis
```

Include a compact table mapping paper theorem names to Lean declarations.

## 9. Reproducibility

Refer to:

```text
docs/REPRODUCIBILITY.md
```

Include the build command:

```bash
lake build LeanC2.Analytic.GenuineBulkConcrete LeanC2.PeerReview LeanC2
```

## 10. Discussion

Explain why identity, cover, local nonvanishing, middle dominance, and transfer are separate layers.

Emphasize that the endpoint is mathlib's official `RiemannHypothesis` proposition.

## Appendix A. Lean theorem map

Summarize `docs/THEOREM_MAP_REVIEW.md`.

## Appendix B. Historical naming dictionary

Summarize `docs/FORMAL_NAMING.md`.

## Appendix C. Optional stronger middle-region packages

List alternative routes without using them in the main proof.
