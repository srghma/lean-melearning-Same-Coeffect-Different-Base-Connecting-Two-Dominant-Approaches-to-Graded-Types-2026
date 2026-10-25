# Summary of changes for run b4c4a3c4-b206-45d8-8015-065a338f2645
**Short answer: no. The project follows the paper, so pushing a box into a pair is total. There is no `Pushable` side condition and no partial "c ⨱ c" operation.** I did not change any code.

**What the project has (Linear Push Core, `RequestProject/Sec2/Linear/Typing.lean`)**
- `pushProd` (push⊗): from \(t : \Box_r(A\otimes B)\) you get \(\mathsf{push}_\otimes\,t : \Box_r A \otimes \Box_r B\). This works for **every** grade \(r\) in **every** preordered semiring, with no extra hypothesis. It is the counterpart of Granule's `pushPair`.
- `pushSum` (push⊕): this one has a side condition, \(1 \le r\). It is the only push rule with a restriction, and the restriction is about \(r\) compared with \(1\), not about pairs.
- `pushUnit`: \(\Box_r\,\mathsf{unit} \multimap \mathsf{unit}\), with no condition.

**On the graded side (Graded Modal Core)**
Product elimination `letpair` in `RequestProject/Sec2/Graded/Typing.lean` scales the scrutinee by \(r\) and binds both components at grade \(r\). It has no condition on \(r\). So the translation of push⊗,
\[\mathsf{let}\,[x]=t\,\mathsf{in}\,\mathsf{let}\,(a,b)=x\,\mathsf{in}\,([a],[b]),\]
type-checks at every grade (`typed_pushProd_body` in `RequestProject/Sec3/Translations/LinearToGradedModal.lean`). The translation back is likewise unconditional. The push⊕ translation needs \(1 \le r\), because Graded Modal Core's `case` rule requires it.

**How this compares with Granule**
- Granule's `pushPair` needs `{Pushable c}` and, by its own comment, is undefined for some grades, such as \(c = 1\) in LNL. Our system, like the paper, allows push⊗ at every grade. So it is more permissive than Granule's stdlib.
- Neither the paper's text in the project nor the Lean code mentions `Pushable`, a partial "⨱", or the LNL semiring. The project therefore does not model Granule's restriction, and I can't confirm from the project why Granule imposes it.
- In the project's own system the permissive version is consistent. The proved type preservation and translation results for Linear Push Core ⇄ Graded Modal Core use the unrestricted push⊗.
- One caveat, which earlier work recorded: the paper's step-by-step simulation claim (Theorem 5.4) fails for one rule that reduces under a box inside `push⊗` (`RequestProject/Sec5/Counterexamples/PushCoreSimulation.lean`). That issue is separate from Granule's partiality concern.

**If you want to match Granule:** you would add a predicate on grades and make it a premise of `pushProd`. The same premise would then be needed on Graded Modal Core's `letpair` (or on the push⊗ translation) for the two systems to stay in correspondence. That is a change to the system, not what the paper formalizes, so I left it out as you asked.

# Summary of changes for run 00550689-c3e4-433b-bc01-9b4ed6cea2fb
This passage closes the paper's discussion of "flattening" nested graded boxes (the section in `flattening-ottput.tex`). Here is what it says, step by step.

**1. The two elimination rules**

The ordinary rule (`GradBoxlet`; `Linlet` is the linear-base version) is:
\[\frac{\Delta_1 \vdash t_1 : \Box_r A \qquad \Delta_2,\ x :_r A \vdash t_2 : B}{\Delta_1 + \Delta_2 \vdash \mathsf{let}\,[x]=t_1\,\mathsf{in}\,t_2 : B}\]
The grade on \(x\) must be exactly the grade \(r\) of the box.

The generalised rule (`GradBoxletGen`, used in Abel & Bernardy's system and in GrTT) is:
\[\frac{\Delta_1 \vdash t_1 : \Box_r A \qquad \Delta_2,\ x :_{s\cdot r} A \vdash t_2 : B}{(s\cdot\Delta_1) + \Delta_2 \vdash \mathsf{let}\,[x]=t_1\,\mathsf{in}\,t_2 : B}\]
Here \(t_2\) may use \(x\) \(s\) times as much as the box offers. You pay for that by scaling \(t_1\)'s resources by \(s\). Informally, you behave as if \(t_1\) were evaluated \(s\) times. With \(s = 1\) you get the ordinary rule back.

**2. What the extra power gives you**

With the generalised rule you can write a term of type
\[\Box_r(\Box_s A) \multimap \Box_{r\cdot s} A\]
namely \(\mathsf{let}\,[y]=x\,\mathsf{in}\,\mathsf{let}\,[z]=y\,\mathsf{in}\,[z]\). This "flattens" two nested boxes into one. The ordinary rule cannot type this term in general.

**3. Why this matters for the semantics (the passage you asked about)**

Graded-modal calculi are usually modelled by a *graded comonad*. Such a structure provides two operations:
- **counit** \(\varepsilon_A : \Box_1 A \to A\): use a value once.
- **comultiplication** \(\delta_{r,s,A} : \Box_{r\cdot s} A \to \Box_r \Box_s A\): split a budget of \(r\cdot s\) uses into \(r\) groups of \(s\).

That is everything the ordinary `let` and promotion rules need. In particular, ordinary `let` is just substitution (composition): \(t_1\) already produces exactly the \(\Box_r A\) that \(t_2\)'s variable \(x :_r A\) expects.

The generalised rule needs to go the *other* way. \(t_2\) wants \(\Box_{s\cdot r} A\). Promoting \(t_1\) by \(s\) only gives \(\Box_s(\Box_r A)\). To bridge the gap you need a **multiplication**
\[\mu_{s,r,A} : \Box_s \Box_r A \to \Box_{s\cdot r} A\]
which merges nested budgets back into one. This is the operation a graded *monad* has, and it runs opposite to \(\delta\). A graded comonad's axioms do not provide it. The counit gives it only in the trivial case of grade \(1\) (\(\varepsilon : \Box_1 \Box_r A \to \Box_r A\)), not for arbitrary grades. So some graded comonads have such a \(\mu\) and others do not.

**4. Why the rule was left out**

The derivation in point 2 shows that the generalised rule *defines* \(\mu\). So any model of a calculus with that rule must support \(\mu\). Adding the rule therefore excludes every graded comonad that lacks a multiplication; the rule is not free. Without it, the calculus can be modelled by any graded comonad.

The paper's aim is to compare the linear-base and graded-base styles under their standard, general semantics. So the authors kept the simpler `Linlet` and `GradBoxlet` rules. Every result in the paper (the translations in your diagram: LB ⇄ GB, LB ⇄ GMB, LC → GMC, LPC ⇄ GMC, …) is stated for those simpler rules. The paper also notes that no linear-base system in the literature has the generalised rule, but it could be added to both styles to keep them equally expressive.

**5. How this shows up in the project**

This matches what the previous session reported (I made no changes this time). The main graded typing and all the diagram translations use only the ordinary rule. The generalised rule exists only in a separate, optional system in `RequestProject/Sec3/Examples/GranuleFlattening.lean`, covering just the base fragment. That file:
- types the flattening term \(\Box_q\Box_r A \to \Box_{q\cdot r} A\) with the generalised rule;
- shows the ordinary rule cannot type it over \(\mathbb N\) at grades \(2\) and \(3\);
- proves substitution and subject reduction for the extended system.

The file's generalised rule has the same shape as the paper's, with its extra factor named \(q\) instead of \(s\). No other part of the project depends on that file, which mirrors the paper's choice to keep the rule out of its main results.

# Summary of changes for run c721cc83-15c3-445e-8e59-b13c8e505c16
**Short answer:** the rule is in the project, but only as a separate, optional typing system. The main grammar does not use it, and none of the diagram's translations do either. That matches the paper. I made no changes for this question. I rebuilt the project, which completed with no errors and no `sorry`.

**What the paper does (Sec. 3.3, "Generalised \(\Box\)-elimination").** It writes the rule as \(\mathsf{let}'_{\mathsf G}\), with premise \(x :_{s\cdot r} A\) and conclusion context \((s\cdot\Delta_1)+\Delta_2\). This is your rule with \(q = s\). The paper uses it for one thing only: deriving \(\Box_r\Box_s A \multimap \Box_{r\cdot s} A\). It then says the rule was "omitted from the main part of our results", because not every graded comonad has the multiplication \(\mu_{r,s}\) needed to model it. So none of the paper's theorems (LB ⇄ GB, LB ⇄ GMB, LC → GMC, LPC ⇄ GMC, and so on) depend on it.

**The main grammar: not there.** The Graded Modal Base / Graded Modal Core typing `GTyped` (in `RequestProject/Sec2/Graded/Typing.lean`) only has the paper's ordinary rule `letbox`:
\[\frac{\Delta_1 \vdash t : \Box_r A \qquad \Delta_2,\ x :_{r} A \vdash u : B}{\Delta_1 + \Delta_2 \vdash \mathsf{let}\,[x]=t\,\mathsf{in}\,u : B}\]
This is your rule with \(q = 1\). The scrutinee is not scaled. In Graded Modal Core, the product, unit and sum eliminations (`letpair`, `letunit`, `case`) *do* scale their scrutinee by \(r\). Boxes do not. All the translations and diagram theorems in `RequestProject/Diagram.lean` are stated for `GTyped`.

**As a separate system: yes, added in an earlier session.** `RequestProject/Sec3/Examples/GranuleFlattening.lean` defines `GTypedQ`. This is Graded Modal Base typing with your rule (constructor `letboxq h q`) in place of `letbox`. It covers the base fragment only (no products or sums), over any pre-ordered semiring. That file proves:
- `GTypedQ.letbox`: the paper's ordinary rule is the special case \(q = 1\).
- `GTyped.toQ`: every ordinary Graded Modal Base derivation is also a `GTypedQ` derivation.
- `flatten_typedQ`: the paper's own Sec. 3.3 example, \(\lambda y.\,\mathsf{let}\,[z]=y\,\mathsf{in}\,\mathsf{let}\,[x]=z\,\mathsf{in}\,[x] : \Box_q\Box_r A \to^1 \Box_{q\cdot r} A\).
- `flatten_untypable_two_three`: over \(\mathbb N\), the ordinary rule cannot type that term at \(q=2, r=3\). So the generalised rule really does type more terms.
- `gradedToModal_typedQ`: with the generalised rule, the converter \((C\to^{y\cdot x}D)\to(\Box_x C\to^y D)\) types for every \(x, y\). The ordinary rule fails at \(x=2, y=3\) (see `BoxCurry.lean`).
- `GTypedQ.subst`, `GTypedQ.preservation`, `GTypedQ.preservation_steps`: substitution and subject reduction. So the rule is sound for the project's reduction semantics.

**Where it is used:** only inside that file. No other module imports it, and the diagram and translation theorems don't depend on it. The paper says a similar rule "could easily be added" to Linear Base. The project has no such Linear Base version, and Graded Modal Core has no version that also includes products and sums.

# Summary of changes for run 6f617e3b-a5f5-4673-9df4-e1ef47e719d1
**Short answer: Granule isn't wrong, and the earlier answer isn't wrong either. They describe two different elimination rules for boxes.**

The earlier "not isomorphic" result was about the paper's Graded Modal Base (GMB) rule for `let [x] = t in u`. That rule binds `x` at exactly the box's grade `r`, and the scrutinee `t` is not scaled. Granule's `flattenCoeffects` implements a stronger rule. When a box pattern sits under an enclosing grade `q` (a `% q` arrow or an outer box), the scrutinee is counted `q` times and `x` gets the flattened grade `q·r`:

\[\frac{\Delta_1 \vdash t : \Box_r A \qquad \Delta_2,\ x :_{q\cdot r} A \vdash u : B}{q\cdot\Delta_1 + \Delta_2 \vdash \mathsf{let}\,[x]=t\,\mathsf{in}\,u : B}\]

The paper's rule is the special case `q = 1`. The product and sum eliminations of Graded Modal Core already scale their scrutinee this way; Granule does the same for boxes.

**Checked in Lean** (new file `RequestProject/Sec3/Examples/GranuleFlattening.lean`; builds with no `sorry` and uses only the standard axioms):
- `GTypedQ` is GMB typing with the rule above in place of the paper's box elimination. `GTyped.toQ` shows every derivation in the paper's GMB (no products or sums) is still a derivation here.
- `gradedToModal_typedQ`: with Granule's rule, `λf. λb. let [z] = b in f z : (C →^(y·x) D) →^1 (□_x C →^y D)` holds for **all** `x, y`. This is the same term the paper's rule can't type at `x=2, y=3`. So the converter that was missing in GMB exists in Granule's system.
- `flatten_typedQ` and `flatten_untypable_two_three`: `λy. let [z]=y in let [x]=z in [x]` has type `□_q □_r A → □_(q·r) A` with Granule's rule. Over ℕ, the paper's rule gives it no type `□_2 □_3 A → □_6 A` in any context.
- `GTypedQ.subst` and `GTypedQ.preservation`: a substitution lemma for grades, and subject reduction for every reduction step. The key case is `let [x] = [s] in u ⇝ u[s/x]`: building `[s]` costs `q·r` times `s`'s resources, which is exactly what the `q·r` uses of `x` consume. So under the project's reduction semantics, flattening is **sound**. This covers the GMB fragment only (no products or sums), over any pre-ordered semiring.

**Not proved:** that the two converters are inverses up to an equational theory. That would need a βη theory for the new rule (including η for boxes). So "isomorphic in Granule" is plausible but not verified here.

**Your other questions.** These answers are informal and not checked in Lean.
- *Compilation to C or assembly:* this is a typing question, not a representation question. If boxes are erased or just wrap a value at runtime, `□_q □_r A` and `□_(q·r) A` look the same, and flattening compiles to nothing (or an unwrap and rewrap). Whether the two *types* can be converted depends only on which elimination rule the type system has.
- *Where a real distinction remains:*
  1. In the paper's calculus, or any model where `□_q □_r A → □_(q·r) A` isn't required, the types differ. A graded comonad always gives `□_(q·r) A → □_q □_r A`, but not the reverse. Granule's rule forces that reverse map to exist. That is an extra demand on semantic models, and it may matter for translations into the linear calculi (I haven't checked this in Lean).
  2. Granule itself only flattens when the two grade types match. It uses meet for security levels, and for mismatched grade types it builds a product grade or refuses. In those cases the nested type stays distinct.
  3. Captured variables and FFI resources such as a file handle don't create a gap. To put such a value in a box you must already have scaled its whole context by the box grade. The subject reduction proof shows the flattened grade accounts for that exactly.

The new file is listed in `READING_GUIDE.md` and `FORMALIZATION.md`, and the main results are in the Properties table as proved. The work is committed and pushed.

# Summary of changes for run cdbd986f-03cc-4a73-a09a-80f9caa1b75d
**Short answer:** it fails before observational equivalence even comes into it. Observational equivalence compares two terms *of the same type*. An "observational isomorphism" between two types, which is the paper's notion for LB ⇄ GMB (Corollary 3.4), needs two **well-typed** maps whose round trips are observationally the identity. For \(x = 2, y = 3\) over \(\mathbb{N}\), the candidate inverse \(\lambda f.\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,f\,z\) has no type at all. So there is no round trip to observe. The obstruction comes from the type system, not from behaviour.

Ignoring the type system, the two candidate maps do compute like inverses. This part I worked out by hand and did not check in Lean:
- \(\lambda c.\,(\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,f\,z)\,[c]\) reduces to \(\lambda c.\,f\,c\).
- The other round trip reduces to \(\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,g\,[z]\). Getting from there back to \(g\) needs an η-rule for boxes.

The grades are what stop it. \(\Box_x C \to^y D\) may open its box up to \(y\) times, and each opening gives a *separate* variable usable \(x\) times. \(C \to^{xy} D\) needs *one* argument usable \(xy\) times. The `letbox` rule has no way to merge separate unboxed variables into one at a higher grade.

**Now checked in Lean** (new file `RequestProject/Sec3/Examples/BoxCurry.lean`; it builds with no `sorry` and uses only the standard axioms):
- `modalToGraded_typed`: \(\lambda g.\lambda c.\,g\,[c] : (\Box_x C \to^y D) \to^1 (C \to^{y\cdot x} D)\), for any grades over any pre-ordered semiring.
- `gradedToModal_typed`: \(\lambda f.\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,f\,z : (C \to^{x\cdot y} D) \to^1 (\Box_x C \to^y D)\), whenever \(x\cdot y \sqsubseteq x\) and \(1 \sqsubseteq y\).
- `gradedToModal_typed_nat_necessary`: over \(\mathbb{N}\), in any context and at any outer grade, if that term has type \((C \to^s D) \to^r (\Box_x C \to^y D)\), then \(s \le x\) and \(1 \le y\). The proof uses a new inversion lemma for `let [x] = …` (`letbox_inv`).
- `gradedToModal_typed_nat_iff`: over \(\mathbb{N}\), the closed typing holds **exactly when** \(xy \le x\) and \(1 \le y\), i.e. when \(y = 1\), or when \(x = 0\) and \(y \ge 1\). This confirms the conditions from my previous answer, which were informal at the time.
- `gradedToModal_untypable_two_three`: the example \(x=2, y=3\) has no typing at all.

**Not proved:** that *no other* pair of terms gives an isomorphism (or observational isomorphism) between \(\Box_2 C \to^3 D\) and \(C \to^6 D\). The results cover only this candidate inverse. Ruling out every term would need a separate argument, such as a resource-counting model in which the two types differ.

I also added the new file to `READING_GUIDE.md` and `FORMALIZATION.md`, and added the two main theorems to the Properties table as proved. The work is committed and pushed.

# Summary of changes for run d33fdf65-db26-447d-a7e1-23788ecb0c42
**Short answer: no, GMB and GPB are not equivalent in the way LB and GMB are.** There is a translation from GMB into GPB. But the paper gives none in the other direction, and I proved that no translation that simply erases the polymorphism can work. This is all checked in Lean: the project builds with no `sorry`, and the new theorems use only the standard axioms `propext` and `Quot.sound`.

Recall what "equivalent" means for LB and GMB in the project: there are translations both ways, and the round trips are observationally the identity (Corollary 3.4). For GMB and GPB:

**GMB → GPB exists.** It is the composite of GMB → LB (Theorem 3.2) and LB → GPB (Theorem 4.1):
- `GTyped.toGPB` (type preservation): every GMB derivation `Δ ⊢ t : A` has a GPB translation `p`, with `Δ ⊢ p : ⦇⟦A⟧⦈` at the same grades.
- `GStep.toGPB` (operational correspondence): if `t ⇝ t'`, then `p ⇝* p'` for some translation `p'` of `t'`.
- Equation preservation doesn't carry over to the composite. GMB → LB preserves all equations, but LB → GPB only preserves the β-equations, without η for □ and without commuting conversions.

**GPB → GMB: no translation that erases the polymorphism.** The paper gives no translation from GPB back to GMB, so no round-trip result is possible. What I proved:
- `selfApp_typed`: the closed GPB term `λx. (x @ (∀α. α →¹ α)) x` has type `(∀α. α →¹ α) →^(1+1) (∀α. α →¹ α)`.
- Erasing its type abstractions and applications gives `λx. x x`. `GExample.lam_selfApp_untypable` shows `λx. x x` has no typing in GB, GMB or GMC, in any context, at any type.
- So any translation that keeps variables, `λ` and application and drops `Λ` and `@` breaks type preservation (`selfApp_erase_untypable`). That includes "replace every type variable by `K`".
- This does **not** rule out every possible translation. A non-compositional one, or one that doesn't erase, isn't covered.

**Where it is:**
- `RequestProject/Diagram.lean`: a new theorem `relation_GMB_GPB` collects all of the above, alongside the existing arrow theorems.
- `RequestProject/Sec4/Translations/GradedModalVsPoly.lean` (new file): the proofs, plus an inversion lemma for `λ` in the graded calculi.
- `READING_GUIDE.md` and `FORMALIZATION.md` now mention the new file.

Both results are in the Properties table, marked proved. The work is committed and pushed.

# Summary of changes for run b1040374-19f5-4a1d-b53c-b26c1464f49d
**Short answer: yes, in one direction only.** You can split a box \(\square_4 A\) into two boxes \(\square_2 A\). You can't merge two \(\square_2 A\) back into one \(\square_4 A\). I didn't change any code. What follows is an informal reading of the typing rules in `RequestProject/Sec2/Graded/Typing.lean` and hasn't been checked in Lean.

One thing to know first: the project has no `PreorderedSemiring ℕ` instance. The only instances are `Lin` (\(\{0,1,\omega\}\)) and products of semirings. To work over \(\mathbb{N}\) you'd have to add an instance yourself and pick its order: either equality (exact usage) or \(\le\) (upper bounds).

**Why splitting works.** The `letbox` rule binds \(z\) at exactly the box's grade, 4. Each `[z]` uses \(z\) at \(2\cdot 1 = 2\) (rule `pr 2`). Two uses add up to \(2 + 2 = 4\), which matches exactly, so no approximation is needed.
- **Graded Modal Core** has products, so you can write the split directly: \[\lambda b.\ \mathsf{let}\,[z]=b\ \mathsf{in}\ ([z],[z]) \;:\; \square_4 A \to^1 \square_2 A \times \square_2 A.\]
- **Graded Modal Base** has no products, so you write it in curried form: \[\lambda k.\lambda b.\ \mathsf{let}\,[z]=b\ \mathsf{in}\ k\,[z]\,[z] \;:\; (\square_2 A \to^1 \square_2 A \to^1 B) \to^1 \square_4 A \to^1 B.\]
- The same works for any split \(r = r_1 + r_2\), not just \(2+2\).
- With the \(\le\) order you can also split unevenly or throw grade away, for example \(\square_4 A \to \square_2 A \times \square_1 A\), because `approx` can raise the body's usage from 3 to 4. With the equality order only exact sums work.

**Merging back doesn't typecheck in general.** Going from \(\square_2 A \times \square_2 A\) to \(\square_4 A\) fails. Unpacking the pair gives two separate values \(a_1, a_2 : A\), each at grade 2. To build \([t] : \square_4 A\), the body \(t : A\) would have to use one variable at grade 4, and nothing lets you combine two different values of type \(A\) into one. So the split is a one-way map, not an isomorphism.

**The multiplicative reading, \(4 = 2\cdot 2\), behaves the same way.** \(\lambda b.\ \mathsf{let}\,[z]=b\ \mathsf{in}\ [[z]] : \square_4 A \to \square_2\square_2 A\) typechecks. The reverse, \(\square_2\square_2 A \to \square_4 A\), fails: it would need \(4 \sqsubseteq 2\), because `letbox` doesn't scale the scrutinee.

# Summary of changes for run 1be4485a-5a46-4daa-8893-d2b120b0191c
I didn't change any code. Nothing below has been checked in Lean: it is an informal analysis based on the Graded Modal Base (GMB) rules as formalized in `RequestProject/Sec2/Graded/Typing.lean` and the equational theory in `RequestProject/Sec2/Graded/Semantics.lean`.

By "iso" I mean two closed maps \(f : A \to^1 B\) and \(g : B \to^1 A\) where both round trips \(g(f\,x) \equiv x\) and \(f(g\,y) \equiv y\) follow from GMB's equations. Those equations are: β and η for functions, β and η for boxes, and three commuting conversions. Two of these move a `let [x] = t₁ in t₂` past an application. The third, `letCommBox`, only fires when the scrutinee is literally a box `[t]`. Three typing facts matter throughout:
- `pr` multiplies grades by \(r\).
- `app` gives the argument's context \(r\cdot\Delta\), with \(r\) on the left.
- `letbox` does not scale the scrutinee, and the bound variable must have exactly the box's grade. The only rule that changes grades is `approx`, and it can only raise them.

**1. Genuine isos (both round trips follow from the equations)**
- **Swapping arguments:** \(A \to^r (B \to^s C) \cong B \to^s (A \to^r C)\), via \(\lambda f.\lambda b.\lambda a.\,f\,a\,b\). This works for any \(r, s\), and both round trips use β and η for functions. Arrows whose argument is a box are a special case.
- **Equivalent grades** (\(r \sqsubseteq s\) and \(s \sqsubseteq r\)):
  - \(A \to^r B \cong A \to^s B\), via \(\lambda f.\lambda a.\,f\,a\) plus `approx`.
  - \(\square_r A \cong \square_s A\), via \(\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,[z]\). Both round trips reduce with β for functions and η for boxes inside a congruence.
- **Congruence:** you can apply these isos inside \(\to^r\) and \(\square_r\).

**2. Maps that type in one direction only (for general grades)**
- **Weakening a grade:**
  - \(A \to^r B \to A \to^s B\) when \(r \sqsubseteq s\).
  - \(\square_r A \to \square_s A\) when \(s \sqsubseteq r\). For example, \(\square_\omega A \to \square_1 A\) in \(\{0,1,\omega\}\).
- **Splitting a box always types:** \(\square_{r\cdot s} A \to \square_r\square_s A\), via \(\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,[[z]]\). Here \(z\) gets grade \(r\cdot s\), which matches the box exactly.
- **The reverse (merging, \(\square_r\square_s A \to \square_{r\cdot s} A\)) does not type with these rules:**
  - \(z\) is bound at grade \(s\), but you need \(r\cdot s \sqsubseteq s\).
  - This is exactly the paper's "Generalised □-elimination" section: merging needs the extra elimination rule that scales the scrutinee. The paper leaves that rule out of the main calculi, and the project doesn't formalize it either.
- **Unboxing and boxing:**
  - \(\square_r A \to A\) needs \(1 \sqsubseteq r\).
  - \(A \to^1 \square_r A\) needs \(r \sqsubseteq 1\). Without that condition, \(A \to^r \square_r A\) always types.
- **Box on the left of an arrow (your earlier question):**
  - \(\square_x C \to^y D\) always maps to \(C \to^{y\cdot x} D\).
  - Going back needs \(x\cdot y \sqsubseteq x\) and \(1 \sqsubseteq y\).
- **Pushing a box inside a function:** \(\square_r(A\to^s B) \to (\square_{r\cdot s}A \to^1 \square_r B)\) types. Its argument is \(\square_{r\cdot s}A\), not \(\square_r A\).

**3. Pairs that type both ways, but where I can't derive one round trip (open, not proved either way)**
- \(\square_1 A \leftrightarrow A\).
- \(\square_1\square_r A \leftrightarrow \square_r A\).
- \(\square_r\square_1 A \leftrightarrow \square_r A\). Here, use \(\lambda b.\,\mathsf{let}\,[y]=b\,\mathsf{in}\,[\mathsf{let}\,[z]=y\,\mathsf{in}\,z]\) for the merging direction.

In each case one round trip follows by β for boxes. For example, unboxing \([a]\) gives back \(a\). The other round trip would need equations like:
- \([\mathsf{let}\,[y]=b\,\mathsf{in}\,y] \equiv b\), or
- reassociating two nested `let`s, for a variable \(b\).

The theory has neither equation in general: `letCommBox` only applies when the scrutinee is literally a box, and there is no let–let rule. So, as formalized, these pairs are a section and a retraction, not proven isos. They would become isos if the theory had a general rule commuting `[–]` past `let`. I have not proved that the equation can't be derived.

**4. The translations between LB and GMB**
- **Not mutually inverse:** going round trip turns \(A \multimap B\) into \(\square_1 A \multimap B\) in Linear Base.
- **What is proved:** only the paper's "observational isomorphism" (Corollary 3.4). If a term steps, its round-trip image reaches the round-trip image of the result in zero or more steps. This holds in both directions: `LStep.roundTrip` and `GStep.roundTrip` in `RequestProject/Sec3/Translations/ObservationalIso.lean`.
- **Not formalized:** the paper also argues that the translations are not adjoint, in either direction. For example, over the one-point semiring there is no derivation of \(\square_1 K \multimap K \vdash K \multimap K\).

**In short:** in GMB as formalized, only argument swapping and coercions between equivalent grades (plus congruence) are isos with both round trips derivable. Every iso involving \(\square\) beyond that either fails to type in one direction (merging, unboxing and boxing at arbitrary grades), or types both ways but has one round trip I can't derive from these equations (the grade-1 cases).

# Summary of changes for run a963d3a3-857c-4082-88e0-b7f5ff2050ff
**Short answer: no, not in general.** In the project's Graded Modal Base, only one direction works for any grades \(x, y\). The other direction needs \(y\) to be essentially 1, which is the case you proved. I didn't change any code. The reasoning below follows the typing rules in `RequestProject/Sec2/Graded/Typing.lean`, but it is an informal answer: none of it has been checked in Lean.

Write \(C = D = A \to^1 A\).

**1. Modal → graded always works, but you get \(y\cdot x\), not \(x\cdot y\).**
Take the same term as your `modalToGraded`, \(\lambda g.\lambda c.\, g\,[c]\):
- `pr x` gives \(c\) grade \(x\).
- `app` through \(g : \Box_x C \to^y D\) scales that by \(y\), so \(c\) ends up with grade \(y\cdot x\).
- \(g\) is used once, so the result type is \((\Box_x C \to^y D) \to^1 (C \to^{y\cdot x} D)\).

The grade is \(y\cdot x\) because `app` multiplies on the left (`δ₁ + r • δ₂`). The class `PreorderedSemiring` doesn't assume multiplication is commutative, so \(x\cdot y\) and \(y\cdot x\) only coincide when your semiring is commutative.

**2. Graded → modal needs extra conditions.**
Take your `gradedToModal`, \(\lambda f.\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,f\,z\), with \(f : C \to^{xy} D\):
- **Inner grade:** in the body, \(z\) gets grade \(xy\) from `app`. But the project's `letbox` rule requires \(z\) to have exactly the box's grade \(x\). The only rule that changes a grade, `approx`, can only raise it. So you need \(x\cdot y \sqsubseteq x\).
- **Outer grade:** \(b\) is used once, by a variable at grade 1. To get the arrow \(\to^y\) you need \(1 \sqsubseteq y\).

When \(y = 1\) both conditions hold trivially, which is why \(\Box_2 C \to^1 D \cong C \to^2 D\) goes through.

**A failing example.** Take \(R = \mathbb{N}\) with the usual \(\le\), \(x = 2\), \(y = 3\). Direction 1 gives \(C \to^6 D\), but direction 2 would need \(6 \le 2\).

**Why I expect no other term to work either (not proved).** Building an iso in general would mean merging \(y\) copies of a grade-\(x\) box into one grade-\(xy\) capability. That amounts to a "join" \(\Box_y\Box_x C \to \Box_{yx} C\). It doesn't typecheck here: the `letbox` rule in this formalization doesn't scale the scrutinee's context, so \(\mathsf{let}\,[v]=u\,\mathsf{in}\,[v]\) runs into the same \(yx \sqsubseteq x\) condition. Ruling out every possible term would need a separate metatheoretic argument, which I haven't done.

**Equations.** Even where both directions typecheck, your `from_to_beta` covers only one round trip, using `betaBox`. The other round trip, \(\lambda b.\,\mathsf{let}\,[z]=b\,\mathsf{in}\,g\,[z] \equiv g\), also needs an η-rule for boxes, not just β.

**Summary:** \(\Box_x C \to^y D\) always maps into \(C \to^{y\cdot x} D\). It maps back (with the same terms) when \(x\cdot y \sqsubseteq x\) and \(1 \sqsubseteq y\), in practice when \(y = 1\).

# Summary of changes for run c0d223bb-19d9-47b7-be35-024cd918f533
I added the direct translation as an alternative to the CPS one. It was already formalized, but it can't target Graded Base: \(\forall\beta\), \(\Lambda\beta\) and `@` are not part of Graded Base, so it translates into **Graded Poly Base**. In fact it is exactly the paper's §4.2 translation LB → GPB, which the project already formalizes: types as `LTy.toP`, terms as `LToP` and context grades as `toGGrades (GradeMap.id R)`. Type preservation, operational correspondence and equation preservation are already proved and collected in `arrow_LB_GPB` in `Diagram.lean`.

**New file `RequestProject/Sec4/Translations/LinearToPoly/Direct.lean`** presents it as the direct-style alternative to CPS:
- **The three type equations and the context translation in your notation**, each proved by `rfl`: \(\Gamma, x : A \mapsto x :_1\), \(\Gamma, x : [A]_r \mapsto x :_r\), and a variable not in \(\Gamma\) gets grade 0. The five term equations are the cases of `LToP` itself.
- **`LToP.erase_eq` (proved):** the `let` case uses \(⦇B⦈\), so the translation is defined on typing derivations, not terms. This theorem says that the dependence only touches type annotations. If you erase \(\Lambda\) and `@` from the translation of any derivation of `t`, you get `LTm.direct t`. That is the plain term map \(x\mapsto x\), \(\lambda x.t\mapsto\lambda x.⦇t⦈\), \(t_1t_2\mapsto⦇t_1⦈⦇t_2⦈\), \([t]\mapsto\lambda f.f⦇t⦈\), \(\mathsf{let}\,[x]=t_1\,\mathsf{in}\,t_2\mapsto⦇t_1⦈(\lambda x.⦇t_2⦈)\).
- **`directK_not_typeSound` (proved):** this is why staying in Graded Base would need polymorphism. If you fix \(\beta := K\), giving \(⦇\Box_r A⦈ = (⦇A⦈\to^r K)\to^1 K\), type preservation fails:
  - In Linear Base, \(z : \Box_1(K\multimap K) \vdash \mathsf{let}\,[x]=z\,\mathsf{in}\,x : K\multimap K\).
  - Its translation \(z\,(\lambda x.x)\) has no Graded Base typing at \(K\to^1 K\) in the translated context, whatever the grades.

**Documentation:** the CPS file header and the `arrow_LB_GPB` docstring now point to the new file. `READING_GUIDE.md` (optional note under step 19) and `FORMALIZATION.md` list it too.

The whole project builds with no `sorry`. The two new theorems use only `propext` and `Quot.sound` (`LToP.erase_eq` uses only `propext`). Both are registered as proved in the Properties table, and the work is committed and pushed. I didn't change the paper's `.tex` sources. Section 4.2 there already gives this direct translation.

# Summary of changes for run f3d30fa2-f5a7-421e-b8b5-68aa8318ed6a
I fixed the wrong grade for `f` in the paper's "apply twice" example, in the two places where it appeared.

- **`calculi-ottput.tex`** (the §2.2 example after Fig. 3): the conclusion of the derivation tree now gives `f` the grade \((1 + r)\) instead of \((1+1)\). This is the grade the paper's own application rule \(\Delta_1 + r\cdot\Delta_2\) produces. The grade \(x :_{(r\cdot r)}\) was already correct and is unchanged.
- **`introduction-ottput.tex`**: the generalised type now reads \((A \xrightarrow{r} A) \xrightarrow{1+r} (A \xrightarrow{r*r} A)\) instead of having \(\xrightarrow{2}\) on the outer arrow. I left the sentence just before it alone. That sentence gives the type \((A \xrightarrow{1} A) \xrightarrow{2} (A \xrightarrow{1} A)\) for the case \(r = 1\), where \(1 + 1 = 2\) is correct.

The corrected text matches what the project already proves in `RequestProject/Sec2/Graded/Examples.lean`: `twice_body` proves the derivation with \(f :_{1+r}\), and `twice_typed` proves the corrected type. I updated that file's header comment and `READING_GUIDE.md` to say the paper sources are now corrected. The two theorems about the old \((1+1)\) version are kept and now describe it as the "originally printed" judgment: one shows it holds when \(r \sqsubseteq 1\), the other that it fails over \(\mathbb{N}\) with \(r = 2\). I updated their Properties-table entries to match, and they stay proved.

No Lean statements or proofs changed. The whole project still builds with no `sorry`, and the changes are committed. I didn't recompile the paper PDF from the `.tex` files.

# Summary of changes for run d711f6f1-a168-4ab1-9e98-88253de03325
**No, it wasn't formalized before.** Nothing in the project covered this example, so I added it in a new file, `RequestProject/Sec2/Graded/Examples.lean`. Formalizing it showed that **the grade printed for `f` in the paper's conclusion is wrong**.

**The grade problem.** The paper's application rule gives the conclusion the grades \(\Delta_1 + r\cdot\Delta_2\). In the outer application:
- \(\Delta_1\) is \(f :_1\), from the variable rule for the outer `f`.
- \(\Delta_2\) is \(f :_1, x :_r\), from the inner derivation of `f x`.

So the conclusion gives `f` grade \(1 + r\cdot 1 = 1 + r\), not \((1+1)\). The grade \(x :_{r\cdot r}\) is correct. (The paper's introduction also gives the type \((A \xrightarrow{r} A) \xrightarrow{2} (A \xrightarrow{r*r} A)\), with grade 2 on `f`, which has the same problem.)

**What I proved.** In the formalization the term is the body `app (var 1) (app (var 1) (var 0))`, where `x` is index 0 and `f` is index 1, with `Fin` de Bruijn indices as in the rest of the project. Each theorem is about the existing Graded Base typing judgment `GTyped`:
- `twice_body`: `f :_(1 + r) (A →^r A), x :_(r·r) A ⊢ f (f x) : A`, for any pre-ordered semiring. This is the paper's derivation tree with the grades its rules actually produce.
- `twice_typed`: `⊢ λf.λx. f (f x) : (A →^r A) →^(1 + r) (A →^(r·r) A)`.
- `twice_body_paper_of_le_one`: the paper's judgment as printed, with `f :_(1+1)`, holds whenever \(r \sqsubseteq 1\), using the approximation rule. For example, it holds for every \(r\) in the linearity semiring \(\{0,1,\omega\}\), because \(1+1=\omega\) there.
- `twice_body_paper_not_always`: the printed judgment can fail. Over \(\mathbb{N}\) with the usual order and \(r = 2\), it has no derivation, because every derivation of `f (f x)` gives `f` a grade of at least \(1 + r = 3\). The proof uses two inversion lemmas, for variables and for applications, that account for the approximation rule. To use \(\mathbb{N}\) here I also added an instance making \(\mathbb{N}\) with its usual order a pre-ordered semiring.

**Checks.** The whole project builds with no `sorry`, no warnings and no errors. The four theorems use only the axioms `propext` and `Quot.sound`. I added an optional entry for the new file to `READING_GUIDE.md`, registered the four results in the Properties table as proved, and committed the work.

## Suggested follow-up

The paper's example gives `f` the grade (1+1) in its conclusion, but its own application rule gives 1 + r. The introduction's type `(A →^r A) →^2 (A →^(r*r) A)` has the same problem. If you like, I can draft corrected text for both places in the `.tex` files.

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