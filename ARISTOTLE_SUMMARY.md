# Summary of changes for run 935c8c07-89f0-4c93-8930-cc2456390bf5
I reorganized the files in two levels: first by paper section, then by meaning. The full project builds with no `sorry`, no warnings and no errors. I spot-checked the axioms of two of the main theorems (`arrow_LB_GPB` and `arrow_GMC_LC_unsound`), and both use only `propext` and `Quot.sound`.

**New layout** (`RequestProject/SecN/<Topic>/…`). A file goes in the section where its material is first introduced, which follows your original `Sec2`–`Sec5` tree:
- **`Sec2/`**
  - `Foundations/` (`DeBruijn`, `Semiring`)
  - `Linear/` (`Syntax`, `Typing`, `Semantics`)
  - `Graded/` (`Syntax`, `Typing`, `Semantics`)
  - `Inclusions/Levels`
  - `Translations/` (`GradedToLinear`, `LinearToGradedCPS`)
- **`Sec3/`**
  - `Translations/` (`LinearToGradedModal`, `ObservationalIso`)
- **`Sec4/`**
  - `Poly/` (`Syntax`, `Typing`, `Subst`, `Equations`)
  - `Linear/UsageAlgebra`
  - `Inclusions/GradedToPoly`
  - `Translations/LinearToPoly/` (`Basic`, `Structural`, `Subst`, `Soundness`, `Equations`)
  - `Counterexamples/LinearToPolyLiteral`
- **`Sec5/`**
  - `Counterexamples/` (`GradedModalCoreToLinearCore`, `PushCoreSimulation`)
- `Diagram.lean` and `Main.lean` stay at the top.

**Where §5 material sits.** Each lineage is a single grammar indexed by a level, so the files in `Sec2/Linear` and `Sec2/Graded` also contain the constructors of the §5 core calculi. Likewise, `Sec3/Translations/LinearToGradedModal.lean` also covers the §5 translations LC → GMC and LPC → GMC. Splitting these files further by section would mean splitting single definitions, so I kept them whole. The docs say this explicitly.

**What else changed:**
- Every file was moved with `git mv`, so its history is kept.
- All imports and the `Diagram.lean` docstring were updated. No declarations or proofs changed.
- **`READING_GUIDE.md`:** a new "Layout" section explains the two-level split and has a table of folders per section. All 24 reading steps and the shorter routes now point to the new paths.
- **`FORMALIZATION.md`:** the "Files by topic" section is replaced by a "Files by section and topic" tree.
- **Properties table:** the file paths of the three grammar definitions and one comment were updated. Every result keeps its previous status.

All work is committed.

# Summary of changes for run 684cd749-7887-47d6-9203-f78f1117e16c
I made all four changes. The full project builds with no `sorry`, no warnings and no errors. All 1708 project declarations still use only the axioms `propext` and `Quot.sound` (no `Classical.choice`).

**1. `Prop` instead of `= true` / `= false`.**
- **Levels:** `LLevel.Core`, `LLevel.Push`, `GLevel.Modal` and `GLevel.Core` are now `Prop`-valued (`| base => False | _ => True`, as you suggested), each with a `DecidablePred` instance.
- **Constructors:** they now take `F.Core` / `F.Push` / `F.Modal` directly; for example `pair : F.Core → …`.
- **Other flags:** the axiom selector `LAxSel` has `Prop` fields (default `True`; e.g. `LAxSel.cps := { eta := False, letComm := False }`). The flags of `GStep` and `GAxF` are also `Prop`, so call-by-name reduction is `GStep False` and reduction under λ is `GStep True`.
- **Hypotheses:** these became `¬ F.Core` / `¬ F.Push`.
- **Proofs:** rewritten to match (`trivial`, `False.elim`, `decide`).
- **Properties table:** the statements there are updated to the new forms and remain proved.

**2. Folders by meaning** (previously `Sec2/`–`Sec5/`):
- `Foundations/` (`DeBruijn`, `Semiring`)
- `Linear/` (`Syntax`, `Typing`, `Semantics`, `UsageAlgebra`)
- `Graded/` (`Syntax`, `Typing`, `Semantics`)
- `Poly/` (`Syntax`, `Typing`, `Subst`, `Equations`)
- `Inclusions/` (dotted arrows: `Levels`, `GradedToPoly`)
- `Translations/` (`GradedToLinear`, `LinearToGradedCPS`, `LinearToGradedModal`, `ObservationalIso`, and `LinearToPoly/` with `Basic`, `Structural`, `Subst`, `Soundness`, `Equations`)
- `Counterexamples/` (`GradedModalCoreToLinearCore`, `PushCoreSimulation`, `LinearToPolyLiteral`)
- `Diagram.lean` stays at the top.

Imports, docstrings and `FORMALIZATION.md` are updated. I left the paper's `.tex` files where they were, because one Properties-table entry points to a line in one of them.

**3. Reading guide.** The new `READING_GUIDE.md` gives a 24-step reading order with paper section numbers and the key declarations for each file. It also has shorter routes: just the seven calculi, one complete translation end to end, or the ❌ arrow.

**4. Speed of `pushAlong`.** The old version searched for a preimage by recursing on `ρ ∘ Fin.succ`. Because the compositions pile up, each lookup cost O(n²). Now `invTable ρ` builds an inverse table (`Vector (Option (Fin n)) m`) once in O(n + m), and `pushAlong` reads it in O(1) per lookup. The old search `findPre` is removed.

The lemmas used downstream (`pushAlong_apply`, `pushAlong_off`, `range_or_off`) keep their statements and are re-proved without classical logic. A quick evaluation confirmed the expected output.

I did not change `subst` or `rename`. Re-shifting substitutions under binders is the usual de Bruijn cost. A faster version would mean re-proving the substitution lemmas across all three grammars, and these functions are only used in proofs, never run.

# Summary of changes for run 7483a750-25b1-4148-ba27-674f79966b86
I proved operational correspondence and equation preservation for LB → GPB (Theorem 4.1), and the whole project now avoids classical logic. The full build passes with no `sorry` and no warnings. One of the paper's statements turned out to be false in its literal form (details below).

**Constructivity.** I checked the axioms used by every declaration in the project: 2140 declarations across all 29 files. None depends on `Classical.choice`; the only axioms used are `propext` and `Quot.sound`. To get there:
- `pushAlong` (in `Sec2/Fin.lean`) is now defined constructively.
- The Mathlib lemmas that pulled in classical logic were replaced with constructive versions.
- `LTyped.weak_many` was rewritten without `Finset`.
- The template file `RequestProject/Main.lean` no longer opens `Classical`.

**LB → GPB.** The translation is defined on typing derivations, as in the paper, so the results say "for every derivation Π there is a derivation Π′". The theorem `arrow_LB_GPB` in `RequestProject/Diagram.lean` has four parts, all proved:
1. **Type preservation:** every derivation has a translation, and it is well typed.
2. **Operational correspondence:** if Π derives `t` and `t ⇝ t′`, there is a derivation Π′ of `t′` with `⦇Π⦈ ⇝* ⦇Π′⦈`. This rests on substitution lemmas for translated derivations and on subject reduction for Linear Base.
3. **The literal reading is false.** The paper's form, which quantifies over *all* derivations Π′ of `t′`, fails. `LToP.step_forall_counterexample` gives a closed counterexample over the linearity semiring.
4. **Equation preservation:** for the β, function-η and box-β axioms of `≡_L^{-η□}`, used left to right in any context, there is Π′ with `⦇Π⦈ ≡_{G∀} ⦇Π′⦈`. The Graded Poly Base equational theory `≡_{G∀}` is defined in `PolyEq.lean`.

**Not formalized:**
- The commuting conversions.
- Using equations right to left (the symmetric version), because that would need a coherence result relating different derivations of the same term.

**New files (all in `Sec4/`):**
- `PolySubst.lean`: renaming and substitution for Graded Poly Base.
- `UsageAlgebra.lean`: usage arithmetic for substitution.
- `LinearToPolyStructural.lean` and `LinearToPolySubst.lean`: renaming, weakening and substitution for translated derivations.
- `PolyEq.lean`: the equational theory `≡_{G∀}`.
- `LinearToPolySoundness.lean`: operational correspondence.
- `LinearToPolyCounterexample.lean`: the counterexample to part 3.
- `LinearToPolyEquations.lean`: equation preservation.

`FORMALIZATION.md` now describes these results and has a new section on constructivity. The `arrow-lb-gpb` entry in the Properties table shows the four-part statement and is marked proved.

# Summary of changes for run 37fe75b4-1dc6-48eb-845b-5cf315811d5a
I formalized the paper's seven calculi and every arrow in your diagram in Lean. The whole project builds with no `sorry`. The main theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Setup.** Each lineage is a single grammar indexed by a level. A constructor that belongs only to a bigger calculus carries a proof that the level includes it.
- `LTm F n` / `LTy R F` for Linear Base, Linear Core and Linear Push Core.
- `GTm F n` / `GTy R F` for Graded Base, Graded Modal Base and Graded Modal Core.
- `PTy R k`, `PTm R k n` for Graded Poly Base.

Variables are `Fin n` de Bruijn indices, so `Tm 0` means closed. Each calculus has typing, call-by-name reduction and an equational theory. Files are grouped by chapter (`Sec2`–`Sec5`). `RequestProject/Diagram.lean` states each arrow as one theorem about the named calculi, and `FORMALIZATION.md` maps the files.

**Arrows proved**
- **Subset arrows** LB⊆LC⊆LPC, GB⊆GMB⊆GMC and GB⊆GPB: typing and reduction are preserved.
- **GB/GMB → LB:** typing, reduction and equations are preserved.
- **LB → GB (CPS):** typing is preserved, and so are equations of the theory without η for functions and without the commuting conversions. Reduction is preserved only up to ≡ (see point 3 below).
- **LB → GPB:** defined on typing derivations, as the paper does. Every derivation has a translation, and every translation is well typed.
- **LB → GMB and LC → GMC:** typing is preserved for any grade map, including the linearity-preserving one. Each step is simulated by one step, and the full equational theory is preserved.
- **LB ⇄ GMB round trips:** the observational-isomorphism corollary holds in both directions.
- **GMC → LPC:** typing and reduction are preserved, and so are equations without the η rules for products and sums.
- **LPC → GMC:** typing is preserved, plus a corrected form of operational correspondence and of equation preservation (see points 1 and 2).
- **GMC ⇢ LC ❌:** I proved it unsound. The well-typed Graded Modal Core term `λp. let ⟨x,y⟩ = p in ⟨[x],[y]⟩` translates to a term that has no Linear Core typing in any context at any type.

**Where the paper's statements don't hold as written**
1. **LPC → GMC operational correspondence (Thm 5.4) is false as stated.** Lean checks a counterexample: `push⊗ [(λx.x)⟨⟨⟩,⟨⟩⟩]` steps to `push⊗ [⟨⟨⟩,⟨⟩⟩]`, but the translation of the first can't reduce to the translation of the second. The cause is the push-box-congruence rules, because Graded Modal Core does not reduce under boxes. What I proved instead is that both sides reduce to a common term.
2. **LPC → GMC equation preservation:** the paper's proof doesn't cover the push-η rules, so I proved it for the theory without them.
3. **CPS operational correspondence (Thm 2.7):** this holds only up to ≡, with reduction allowed under λ, which is also what the paper's own appendix proof shows.

**Not done:** for LB → GPB, I did not formalize operational correspondence or equation preservation; only type preservation is proved.