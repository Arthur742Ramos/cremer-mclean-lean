# Cremer–McLean Full Surplus Extraction in Lean 4

A Lean 4 / Mathlib formalization of the **Cremer–McLean full surplus extraction
theorem** (Crémer & McLean, *Econometrica* 56(6), 1988):

> For a single indivisible object with finitely many bidders, finite type
> spaces, and a correlated joint prior with full support: if every bidder's
> family of conditional distributions over the others' types is **convex
> independent** (no conditional lies in the convex hull of the rest), then
> there exists a Bayesian incentive compatible, interim individually rational
> direct mechanism that allocates ex post efficiently and **extracts the full
> surplus** — every bidder's interim expected utility is zero, so the
> seller's expected revenue equals the expected maximum value.

The proof hinges on the paper's lottery construction: strict separation of
each conditional distribution from the convex hull of the others yields
side-bet lotteries with zero own-conditional expectation and strictly
positive cross-conditional expectation; scaled up, they dominate any
misreport gain while vanishing in truthful expectation.

## Status

M0 scaffold (in development). Milestones:

- M0: repository scaffold, pinned toolchain, CI
- M1: core definitions and theorem statements
- M2: convex independence → lottery construction (strict separation core)
- M3: mechanism construction and Bayesian incentive compatibility
- M4: interim individual rationality and full surplus extraction
- M5–M7: Palomar packaging, prose audit, verifier replica

## Layout

- `CremerMcLean/` — the proof library (complete proofs, no placeholders)
- `Challenge.lean` — the comparator statement surface (definitions genuine,
  theorem proofs as deliberate placeholders only where the comparator selects)
- `Solution.lean` — imports the library; the submission's proof module
- `scripts/verify.sh` — build, axiom audit, and package checks
- `formalization.yaml` — registry metadata (authors, classification, sources)

## Building

Requires [Elan](https://github.com/leanprover/elan). Pinned toolchain:
`leanprover/lean4:v4.35.0-rc2`, Mathlib at the revision in `lake-manifest.json`.

```bash
lake build
./scripts/verify.sh
```

## References

- Jacques Crémer and Richard P. McLean, "Full Extraction of the Surplus in
  Bayesian and Dominant Strategy Auctions," *Econometrica* 56(6):1247–1257,
  1988. <https://www.jstor.org/stable/1913096>
- Jacques Crémer and Richard P. McLean, "Optimal Selling Strategies under
  Uncertainty for a Discriminating Monopolist when Demands are
  Interdependent," *Econometrica* 53(2):345–361, 1985 (background).

## License

BSD-3-Clause. See `LICENSE`.
