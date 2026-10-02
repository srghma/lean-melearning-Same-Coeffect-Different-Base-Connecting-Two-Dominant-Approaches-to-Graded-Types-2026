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