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

## Files by section and topic

Files are grouped first by the paper section where the material is introduced (`Sec2/` … `Sec5/`)
and then, inside each section, by meaning (`Foundations/`, `Linear/`, `Graded/`, `Poly/`,
`Inclusions/`, `Translations/`, `Counterexamples/`). A suggested reading order is in
`READING_GUIDE.md`.

```
RequestProject/
├── Diagram.lean                      one theorem per arrow of the diagram
├── Main.lean                         (template, not used)
├── Sec2/                             §2  linear and graded base calculi, first translations
│   ├── Foundations/  DeBruijn.lean   environments `a .: f`, renamings, `invTable` / `pushAlong`
│   │                 Semiring.lean   pre-ordered semirings, linearity semiring, products
│   ├── Linear/       Syntax, Typing, Semantics      LB / LC / LPC (one level-indexed grammar)
│   ├── Graded/       Syntax, Typing, Semantics      GB / GMB / GMC (one level-indexed grammar)
│   ├── Inclusions/   Levels.lean     LB ⊆ LC ⊆ LPC and GB ⊆ GMB ⊆ GMC
│   └── Translations/ GradedToLinear.lean     `⟦-⟧`: GB/GMB → LB, GMC → LPC
│                     LinearToGradedCPS.lean  CPS, LB → GB
├── Sec3/                             §3  graded modal base
│   └── Translations/ LinearToGradedModal.lean  `⦇-⦈`: LB → GMB, LC → GMC, LPC → GMC
│                     ObservationalIso.lean     round trips LB ⇄ GMB
├── Sec4/                             §4  graded poly base
│   ├── Poly/         Syntax, Typing (with reduction), Subst, Equations (`≡_{G∀}`)
│   ├── Linear/       UsageAlgebra.lean  arithmetic on usage contexts (for substitution)
│   ├── Inclusions/   GradedToPoly.lean  GB ⊆ GPB
│   ├── Translations/ LinearToPoly/      LB → GPB: Basic (derivation-based translation),
│   │                                    Structural, Subst, Soundness (operational
│   │                                    correspondence), Equations (equation preservation),
│   │                                    Direct (as the direct-style alternative to CPS)
│   └── Counterexamples/ LinearToPolyLiteral.lean  literal reading of Thm 4.1 fails
└── Sec5/                             §5  core calculi
    └── Counterexamples/ GradedModalCoreToLinearCore.lean  GMC ⇢ LC is unsound
                         PushCoreSimulation.lean           LPC → GMC simulation fails as stated
```

The `Linear/` and `Graded/` grammars of `Sec2/` already contain the constructors of the core
calculi of §5 (they are single grammars indexed by a level), and `LinearToGradedModal.lean`
also covers the §5 translations LC → GMC and LPC → GMC.

Feature flags are propositions: `F.Core`, `F.Push`, `F.Modal` (levels), the fields of
`LAxSel` (optional axioms of `≡_L`), and the flags of `GStep`/`GAxF` (`GStep False` is
call-by-name reduction, `GStep True` also reduces under λ).

## Points where the formal results differ from the paper's statements

1. **LPC → GMC operational correspondence** (Thm 5.4 states `⦇t⦈ ⇝* ⦇t'⦈`): false for the
   `push`-box-congruence rules; `LStep.toG_counterexample` gives a closed counterexample. The
   corrected statement (common reduct) is `LStep.toG_join`.
2. **LPC → GMC equation preservation**: proved for the theory without the `push`-η rules
   (`LAxSel.noPushEta`), which the paper's proof does not treat.
3. **CPS operational correspondence** (Thm 2.7) holds up to `≡_G` (as in the paper's appendix
   proof), with full β-reduction in the target.
4. **LB → GPB** (Thm 4.1). The translation is defined on typing derivations, so the results are
   stated as "for every derivation `Π` of the source there is a derivation `Π'` of the target":
   * type preservation: `LToP.toP_exists`, `LToP.typed`;
   * operational correspondence: `LToP.step` / `LToP.steps` (`t ⇝ t'` gives `Π'` with
     `⦇Π⦈ ⇝* ⦇Π'⦈`), together with subject reduction for Linear Base;
   * the literal reading "for *all* derivations `Π'` of `t'`" is false:
     `LToP.step_forall_counterexample` (closed terms, linearity semiring);
   * equation preservation: `LToP.eq_preserve` gives `⦇Π⦈ ≡_{G∀} ⦇Π'⦈` for the β-, η-(function)
     and box-β axioms of `≡_L^{-η□}` used left to right under any context (`LEqDir
     LAxSel.polyPreserved`). Commuting conversions and the symmetric closure (which would need
     a coherence result relating different derivations of the same term) are not formalized.

## Constructivity

No declaration in the project depends on `Classical.choice`: every theorem uses only the axioms
`propext` and `Quot.sound` (checked with `#print axioms` / `collectAxioms` over all project
declarations).
