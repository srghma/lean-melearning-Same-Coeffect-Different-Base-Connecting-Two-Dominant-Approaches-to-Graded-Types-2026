# Reading guide

A suggested order for reading the formalization (all paths are relative to
`RequestProject/`). Each step only depends on earlier steps. The section numbers refer to the
paper. `FORMALIZATION.md` lists where the formal results differ from the paper's statements.

## Layout

Files are split in two levels:

* **by paper section** — `Sec2/` (linear and graded base calculi, §2), `Sec3/` (graded modal
  base, §3), `Sec4/` (graded poly base, §4), `Sec5/` (core calculi, §5); a file lives in the
  section where its material is first introduced;
* **by meaning, inside each section** — `Foundations/` (de Bruijn indices, semirings),
  `Linear/` and `Graded/` (the two lineages), `Poly/` (Graded Poly Base), `Inclusions/` (dotted
  arrows), `Translations/` (solid arrows) and `Counterexamples/` (negative results, including
  the ❌ arrow).

`Diagram.lean` (all arrows) stays at the top. Because each lineage is *one* grammar indexed by a
level, the files `Sec2/Linear/*` and `Sec2/Graded/*` also contain the constructors of the §5
core calculi, and `Sec3/Translations/LinearToGradedModal.lean` also covers the §5 translations
LC → GMC and LPC → GMC.

| section | folder contents |
|---|---|
| `Sec2/` | `Foundations/{DeBruijn,Semiring}`, `Linear/{Syntax,Typing,Semantics}`, `Graded/{Syntax,Typing,Semantics}`, `Inclusions/Levels`, `Translations/{GradedToLinear,LinearToGradedCPS}` |
| `Sec3/` | `Translations/{LinearToGradedModal,ObservationalIso}` |
| `Sec4/` | `Poly/{Syntax,Typing,Subst,Equations}`, `Linear/UsageAlgebra`, `Inclusions/GradedToPoly`, `Translations/LinearToPoly/{Basic,Structural,Subst,Soundness,Equations}`, `Counterexamples/LinearToPolyLiteral` |
| `Sec5/` | `Counterexamples/{GradedModalCoreToLinearCore,PushCoreSimulation}` |

## 0. The big picture (10 minutes)

1. **`Diagram.lean`.** Every arrow of the diagram is one theorem here (`arrow_*`). Skim the
   statements to see what is claimed. Don't read the proofs yet: each is a one-liner that
   points to the file where the real work is done.
2. **`FORMALIZATION.md`.** Design choices, and the places where the paper's statements had to be
   corrected.

## 1. Foundations

3. **`Sec2/Foundations/DeBruijn.lean`.** Intrinsically scoped syntax: `Tm n` has its free variables
   in `Fin n`, so `Tm 0` is the closed terms. Learn the environment extension `a .: f`
   (`scons`) and `upRen` (moving a renaming under a binder). The file also has `invTable` and
   `pushAlong`, which are used only in the weakening proofs; you can skip them on a first read.
4. **`Sec2/Foundations/Semiring.lean`** (§2.1). `PreorderedSemiring`, the linearity semiring `Lin`
   (`0, 1, ω`) and products of semirings.

## 2. The linear-base lineage (LB ⊆ LC ⊆ LPC)

5. **`Sec2/Linear/Syntax.lean`** (§2.1, §5.1, §5.4). This file sets the pattern for the whole
   project: *one grammar indexed by a level*. `LLevel` has the values `base`, `core` and
   `push`. The predicates `F.Core` and `F.Push` (both `Prop`) say which constructors exist.
   For example, `LTm.pair` takes a proof of `F.Core`, so at level `base` it cannot be used.
   Then read `rename`, `subst`, `subst1` and `subst2`.
6. **`Sec2/Linear/Typing.lean`** (Fig. 1, 4, 5). A context is a type assignment
   `Γ : Fin n → LTy R F` together with a usage assignment `u : Fin n → Use R`, where a usage is
   `none`, `lin` or `grd r`. Learn `Use.Add`, `CtxAdd` and `smulCtx` before `LTyped`.
7. **`Sec2/Linear/Semantics.lean`** (Fig. 2, App. A). `LStep` is call-by-name reduction.
   `LAxF S` is the set of axioms; the selector `S : LAxSel` has `Prop` fields that switch the
   optional axioms on and off. `LCong` is the congruence closure, and `LEq` is the full
   theory `≡_L`.

## 3. The graded-base lineage (GB ⊆ GMB ⊆ GMC)

8. **`Sec2/Graded/Syntax.lean`** (§2.2, §3.1, §5.3). Same pattern as the linear lineage, with
   levels `base`, `modal` and `core` and predicates `F.Modal` and `F.Core`.
9. **`Sec2/Graded/Typing.lean`** (Fig. 3, Fig. 6). A context is a type assignment plus a grade
   vector `δ : Fin n → R`. Weakening is built in, because unused variables have grade `0`.
10. **`Sec2/Graded/Semantics.lean`.** `GStep b`: `GStep False` is call-by-name reduction, and
    `GStep True` also reduces under λ (this is the target of the CPS translation). `GAxF`,
    `GCong` and `GEq` are the equational theory.
    *Optional:* **`Sec2/Graded/Examples.lean`** works through the §2.2 example
    `h = λf. λx. f (f x)` (`twice_body`, `twice_typed`). The application rule gives `f` grade
    `1 + r`, not the `1 + 1` originally printed in the paper (the `.tex` sources are now corrected
    to `1 + r`). The originally printed judgment holds when `r ⊑ 1`
    (`twice_body_paper_of_le_one`) but not in general (`twice_body_paper_not_always`).

## 4. The dotted arrows (inclusions)

11. **`Sec2/Inclusions/Levels.lean`.** For levels `F ≤ G`, `embed` maps types, terms and derivations
    of the smaller calculus into the bigger one, preserving typing and reduction. This is a
    good first example of a proof by induction on derivations.

## 5. Translations between the base calculi

12. **`Sec2/Translations/GradedToLinear.lean`** (§2.3.1, §3.2.3, §5.5). `⟦-⟧` maps GB/GMB to LB and
    GMC to LPC: `GTyped.toL` (types), `GStep.toL` (reduction) and `GEq.toL` (equations). This
    is the simplest translation, so read it first. Note the general pattern: a renaming
    lemma, then a substitution lemma, then simulation.
13. **`Sec3/Translations/LinearToGradedModal.lean`** (§3.2, §5.3, §5.6). `⦇-⦈` maps LB to GMB,
    LC to GMC and LPC to GMC, parameterised by a `GradeMap` (`GradeMap.id`, or
    `GradeMap.linPair` for the linearity-preserving version). Key results: `LTyped.toG`,
    `LStep.toG`, `LStep.toG_join` and `LEq.toG`.
14. **`Sec3/Translations/ObservationalIso.lean`** (§3.2.4). The round trips LB → GMB → LB and
    GMB → LB → GMB. The file also defines the names `LinearBase`, …, `GradedModalCore`.
15. **`Sec2/Translations/LinearToGradedCPS.lean`** (§2.3.2). The CPS translation LB → GB
    (`LTm.cps`, `LTyped.cps`, `LStep.cps`, `LCong.cps`). It is harder than the previous ones,
    because simulation only holds up to `≡_G`, with reduction under λ allowed.

## 6. Graded Poly Base and the Church encoding of `□`

16. **`Sec4/Poly/Syntax.lean`, `Sec4/Poly/Typing.lean`** (§4.1). Types `PTy R k` have `k` type
    variables, and terms `PTm R k n` have `k` type variables and `n` term variables.
17. **`Sec4/Inclusions/GradedToPoly.lean`.** GB ⊆ GPB (a short file).
18. **`Sec4/Poly/Subst.lean`, `Sec4/Poly/Equations.lean`.** Renaming and substitution algebra, and the
    theory `≡_{G∀}`. Skim these files; they are infrastructure.
19. **`Sec4/Translations/LinearToPoly/Basic.lean`** (§4.2). The translation is defined on *typing
    derivations*, as a relation `LToP Γ u t A p`. Read `LTyped.toP_exists` and `LToP.typed`.
20. **`Sec4/Linear/UsageAlgebra.lean`.** Arithmetic on usage contexts, needed for simultaneous
    substitution (`SubstUse`). Read it when the next files need it.
21. **`Sec4/Translations/LinearToPoly/Structural.lean`, `…/Subst.lean`, `…/Soundness.lean`,
    `…/Equations.lean`.** These follow the usual route: structural lemmas, then the
    substitution lemma, then operational correspondence (`LToP.step`), then equation
    preservation (`LToP.eq_preserve`).

## 7. Negative results

22. **`Sec5/Counterexamples/GradedModalCoreToLinearCore.lean`** (§5.4). The naive GMC → LC
    translation is not type-sound. Inversion lemmas show that a linear variable can never
    occur under a box.
23. **`Sec5/Counterexamples/PushCoreSimulation.lean`** (§5.6). A closed LPC reduction whose
    translation does not reduce to the translation of the reduct.
24. **`Sec4/Counterexamples/LinearToPolyLiteral.lean`** (§4.2). The literal reading of Theorem 4.1,
    which quantifies over *all* derivations of the reduct, is false.

## Shorter routes

* **Only the definitions of the seven calculi:** steps 3, 5–10 and 16.
* **One complete translation end to end:** steps 3, 5–10, 12 and 14.
* **The ❌ arrow of the diagram:** steps 5–9, 13 and 22.
