# Formalization of *Same Coeffect, Different Base*

All files live in `RequestProject/` under the namespace `Coeffect`; `RequestProject/Diagram.lean`
states every arrow of the diagram as one theorem about the named calculi.

Terms are intrinsically scoped with `Fin n` de Bruijn indices: `LTm F n`, `GTm F n`, `PTm R k n`
(`n = 0` means closed). Each lineage is a single level-indexed grammar; the constructors of the
bigger calculi carry a proof that the level contains them:

| calculus | level |
|---|---|
| Linear Base / Linear Core / Linear Push Core | `LLevel.base` / `.core` / `.push` (`LinearBase`, …) |
| Graded Base / Graded Modal Base / Graded Modal Core | `GLevel.base` / `.modal` / `.core` |
| Graded Poly Base | `PTy R k`, `PTm R k n` (Section 4) |

## Files by chapter

* `Sec2/` – semirings, de Bruijn helpers, syntax/typing/semantics of both lineages,
  `Embedding.lean` (dotted inclusion arrows), `GradedToLinear.lean` (`⟦-⟧`: GB/GMB → LB,
  GMC → LPC), `LinearToGradedCPS.lean` (CPS translation LB → GB).
* `Sec3/` – `LinearToGradedModal.lean` (`⦇-⦈`: LB → GMB, LC → GMC, LPC → GMC, with grade maps
  including the linearity-preserving one), `ObservationalIso.lean` (round trips).
* `Sec4/` – Graded Poly Base (`PolySyntax`, `PolyTyping`), `GradedToPoly.lean` (GB ⊆ GPB),
  `LinearToPoly.lean` (derivation-based translation LB → GPB).
* `Sec5/` – `NaiveGradedToLinear.lean` (GMC ⇢ LC unsound), `PushCoreCounterexample.lean`.

## Points where the formal results differ from the paper's statements

1. **LPC → GMC operational correspondence** (Thm 5.4 states `⦇t⦈ ⇝* ⦇t'⦈`): false for the
   `push`-box-congruence rules; `LStep.toG_counterexample` gives a closed counterexample. The
   corrected statement (common reduct) is `LStep.toG_join`.
2. **LPC → GMC equation preservation**: proved for the theory without the `push`-η rules
   (`LAxSel.noPushEta`), which the paper's proof does not treat.
3. **CPS operational correspondence** (Thm 2.7) holds up to `≡_G` (as in the paper's appendix
   proof), with full β-reduction in the target.
4. **LB → GPB**: only type preservation (and existence of the translation of every derivation)
   is formalized; operational correspondence / equation preservation are not.
