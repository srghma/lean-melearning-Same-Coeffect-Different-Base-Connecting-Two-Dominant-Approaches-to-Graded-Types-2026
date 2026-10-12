module

public import RequestProject.Sec2.LinearSyntax

/-!
# Operational semantics and equational theory of the linear-base lineage

* `LStep` is the call-by-name reduction `t ⇝_L t'` (Figure 2, Figure 4 and Figure 5).
* `LAx` collects the axioms of the equational theory `≡_L` (Figure 2 and Appendix A), and
  `LCong Ax` is the closure of a set of axioms `Ax` under reflexivity, symmetry, transitivity
  and all congruence rules ("congruence rules omitted" in the paper). The full equational theory
  is `LEq := LCong LAx`.
-/

@[expose] public section

namespace Coeffect

variable {F : LLevel}

open LTm

/-- Call-by-name reduction `t ⇝_L t'` of the linear-base calculi. -/
inductive LStep : {n : ℕ} → LTm F n → LTm F n → Prop
  | beta {n : ℕ} (t₂ : LTm F (n + 1)) (t₁ : LTm F n) : LStep (app (lam t₂) t₁) (t₂.subst1 t₁)
  | congAppL {n : ℕ} {t₁ t₁' : LTm F n} (t₂ : LTm F n) :
      LStep t₁ t₁' → LStep (app t₁ t₂) (app t₁' t₂)
  | betaBox {n : ℕ} (t₁ : LTm F n) (t₂ : LTm F (n + 1)) :
      LStep (letbox (box t₁) t₂) (t₂.subst1 t₁)
  | congLetL {n : ℕ} {t₁ t₁' : LTm F n} (t₂ : LTm F (n + 1)) :
      LStep t₁ t₁' → LStep (letbox t₁ t₂) (letbox t₁' t₂)
  | prodCong {n : ℕ} (h : F.Core) {t₁ t₁' : LTm F n} (t₂ : LTm F (n + 2)) :
      LStep t₁ t₁' → LStep (letpair h t₁ t₂) (letpair h t₁' t₂)
  | prodBeta {n : ℕ} (h : F.Core) (t₁ t₂ : LTm F n) (t₃ : LTm F (n + 2)) :
      LStep (letpair h (pair h t₁ t₂) t₃) (t₃.subst2 t₁ t₂)
  | unitCong {n : ℕ} (h : F.Core) {t₁ t₁' : LTm F n} (t₂ : LTm F n) :
      LStep t₁ t₁' → LStep (letunit h t₁ t₂) (letunit h t₁' t₂)
  | unitBeta {n : ℕ} (h : F.Core) (t₂ : LTm F n) : LStep (letunit h (unit h) t₂) t₂
  | congCase {n : ℕ} (h : F.Core) {t t' : LTm F n} (t₁ t₂ : LTm F (n + 1)) :
      LStep t t' → LStep (case h t t₁ t₂) (case h t' t₁ t₂)
  | caseInl {n : ℕ} (h : F.Core) (t : LTm F n) (t₁ t₂ : LTm F (n + 1)) :
      LStep (case h (inl h t) t₁ t₂) (t₁.subst1 t)
  | caseInr {n : ℕ} (h : F.Core) (t : LTm F n) (t₁ t₂ : LTm F (n + 1)) :
      LStep (case h (inr h t) t₁ t₂) (t₂.subst1 t)
  | pushProdCong {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LStep t t' → LStep (pushProd h t) (pushProd h t')
  | pushProdBoxCong {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LStep t t' → LStep (pushProd h (box t)) (pushProd h (box t'))
  | pushProd {n : ℕ} (h : F.Push) (hc : F.Core) (t₁ t₂ : LTm F n) :
      LStep (pushProd h (box (pair hc t₁ t₂))) (pair hc (box t₁) (box t₂))
  | pushSumCong {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LStep t t' → LStep (pushSum h t) (pushSum h t')
  | pushSumBoxCong {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LStep t t' → LStep (pushSum h (box t)) (pushSum h (box t'))
  | pushSumInl {n : ℕ} (h : F.Push) (hc : F.Core) (t : LTm F n) :
      LStep (pushSum h (box (inl hc t))) (inl hc (box t))
  | pushSumInr {n : ℕ} (h : F.Push) (hc : F.Core) (t : LTm F n) :
      LStep (pushSum h (box (inr hc t))) (inr hc (box t))
  | pushUnitCong {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LStep t t' → LStep (pushUnit h t) (pushUnit h t')
  | pushUnitBoxCong {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LStep t t' → LStep (pushUnit h (box t)) (pushUnit h (box t'))
  | pushUnit {n : ℕ} (h : F.Push) (hc : F.Core) :
      LStep (pushUnit h (box (unit hc)) : LTm F n) (unit hc)

/-- Reflexive-transitive closure `⇝_L*`. -/
abbrev LSteps {n : ℕ} : LTm F n → LTm F n → Prop := Relation.ReflTransGen LStep

/-- Selection of optional axioms of `≡_L`; used to state the sub-theories of the paper
(`≡_L^{β→βη□}` for the CPS translation, `≡_L^{-η□}` for the polymorphic translation, and the
theory without the `push` η-rules). -/
structure LAxSel where
  /-- `η` for functions -/
  eta : Bool := true
  /-- `η` for the graded modality -/
  etaBox : Bool := true
  /-- the commuting conversions `letCommOne`, `letCommTwo`, `letCommBox` -/
  letComm : Bool := true
  /-- the `η`-rules for `push⊗` and `push⊕` -/
  pushEta : Bool := true

/-- All axioms. -/
def LAxSel.all : LAxSel := {}

/-- The axioms of the equational theory `≡_L` (all calculi of the lineage), restricted to the
optional axioms enabled by `S`. -/
inductive LAxF (S : LAxSel) : {n : ℕ} → LTm F n → LTm F n → Prop
  | beta {n : ℕ} (t₂ : LTm F (n + 1)) (t₁ : LTm F n) : LAxF S (app (lam t₂) t₁) (t₂.subst1 t₁)
  /-- `λx. t x ≡ t` when `x # t` -/
  | eta {n : ℕ} (he : S.eta = true) (t : LTm F n) : LAxF S (lam (app (shift t) (var 0))) t
  | betaBox {n : ℕ} (t₁ : LTm F n) (t₂ : LTm F (n + 1)) :
      LAxF S (letbox (box t₁) t₂) (t₂.subst1 t₁)
  | etaBox {n : ℕ} (he : S.etaBox = true) (t : LTm F n) : LAxF S (letbox t (box (var 0))) t
  /-- `t₀ (let [x] = t₁ in t₂) ≡ let [x] = t₁ in (t₀ t₂)` when `x # t₀` -/
  | letCommOne {n : ℕ} (he : S.letComm = true) (t₀ t₁ : LTm F n) (t₂ : LTm F (n + 1)) :
      LAxF S (app t₀ (letbox t₁ t₂)) (letbox t₁ (app (shift t₀) t₂))
  /-- `(let [x] = t₁ in t₂) t₀ ≡ let [x] = t₁ in (t₂ t₀)` when `x # t₀` -/
  | letCommTwo {n : ℕ} (he : S.letComm = true) (t₀ t₁ : LTm F n) (t₂ : LTm F (n + 1)) :
      LAxF S (app (letbox t₁ t₂) t₀) (letbox t₁ (app t₂ (shift t₀)))
  | letCommBox {n : ℕ} (he : S.letComm = true) (t₁ : LTm F n) (t₂ : LTm F (n + 1)) :
      LAxF S (letbox (box t₁) (box t₂)) (box (letbox (box t₁) t₂))
  | betaUnit {n : ℕ} (h : F.Core) (t : LTm F n) : LAxF S (letunit h (unit h) t) t
  | etaUnit {n : ℕ} (h : F.Core) (t : LTm F n) : LAxF S (letunit h t (unit h)) (unit h)
  | betaProd {n : ℕ} (h : F.Core) (t₁ t₂ : LTm F n) (t : LTm F (n + 2)) :
      LAxF S (letpair h (pair h t₁ t₂) t) (t.subst2 t₁ t₂)
  | etaProd {n : ℕ} (h : F.Core) (t : LTm F n) :
      LAxF S (letpair h t (pair h (var 1) (var 0))) t
  | betaSumOne {n : ℕ} (h : F.Core) (t : LTm F n) (t₁ t₂ : LTm F (n + 1)) :
      LAxF S (case h (inl h t) t₁ t₂) (t₁.subst1 t)
  | betaSumTwo {n : ℕ} (h : F.Core) (t : LTm F n) (t₁ t₂ : LTm F (n + 1)) :
      LAxF S (case h (inr h t) t₁ t₂) (t₂.subst1 t)
  | etaSum {n : ℕ} (h : F.Core) (t : LTm F n) :
      LAxF S (case h t (inl h (var 0)) (inr h (var 0))) t
  | pushProdBeta {n : ℕ} (h : F.Push) (hc : F.Core) (t₁ t₂ : LTm F n) :
      LAxF S (pushProd h (box (pair hc t₁ t₂))) (pair hc (box t₁) (box t₂))
  /-- `let ⟨x', y'⟩ = push⊗ t in let [x] = x' in let [y] = y' in [⟨x, y⟩] ≡ t` -/
  | pushProdEta {n : ℕ} (he : S.pushEta = true) (h : F.Push) (hc : F.Core) (t : LTm F n) :
      LAxF S (letpair hc (pushProd h t) (letbox (var 1) (letbox (var 1) (box (pair hc (var 1) (var 0))))))
        t
  | pushSumBetaOne {n : ℕ} (h : F.Push) (hc : F.Core) (t : LTm F n) :
      LAxF S (pushSum h (box (inl hc t))) (inl hc (box t))
  | pushSumBetaTwo {n : ℕ} (h : F.Push) (hc : F.Core) (t : LTm F n) :
      LAxF S (pushSum h (box (inr hc t))) (inr hc (box t))
  /-- `case push⊕ t of {inj₁ x → let [x'] = x in [inj₁ x']; inj₂ y → let [y'] = y in [inj₂ y']} ≡ t` -/
  | pushSumEta {n : ℕ} (he : S.pushEta = true) (h : F.Push) (hc : F.Core) (t : LTm F n) :
      LAxF S (case hc (pushSum h t) (letbox (var 0) (box (inl hc (var 0))))
        (letbox (var 0) (box (inr hc (var 0))))) t
  | pushUnitBeta {n : ℕ} (h : F.Push) (hc : F.Core) :
      LAxF S (pushUnit h (box (unit hc)) : LTm F n) (unit hc)

/-- All axioms of `≡_L`. -/
abbrev LAx {n : ℕ} : LTm F n → LTm F n → Prop := LAxF (F := F) LAxSel.all

/-- Closure of a set of axioms under equivalence and all congruences. -/
inductive LCong (Ax : ∀ {n : ℕ}, LTm F n → LTm F n → Prop) : {n : ℕ} → LTm F n → LTm F n → Prop
  | ax {n : ℕ} {t t' : LTm F n} : Ax t t' → LCong Ax t t'
  | refl {n : ℕ} (t : LTm F n) : LCong Ax t t
  | symm {n : ℕ} {t t' : LTm F n} : LCong Ax t t' → LCong Ax t' t
  | trans {n : ℕ} {t t' t'' : LTm F n} : LCong Ax t t' → LCong Ax t' t'' → LCong Ax t t''
  | app {n : ℕ} {t₁ t₁' t₂ t₂' : LTm F n} :
      LCong Ax t₁ t₁' → LCong Ax t₂ t₂' → LCong Ax (app t₁ t₂) (app t₁' t₂')
  | lam {n : ℕ} {t t' : LTm F (n + 1)} : LCong Ax t t' → LCong Ax (lam t) (lam t')
  | box {n : ℕ} {t t' : LTm F n} : LCong Ax t t' → LCong Ax (box t) (box t')
  | letbox {n : ℕ} {t₁ t₁' : LTm F n} {t₂ t₂' : LTm F (n + 1)} :
      LCong Ax t₁ t₁' → LCong Ax t₂ t₂' → LCong Ax (letbox t₁ t₂) (letbox t₁' t₂')
  | pair {n : ℕ} (h : F.Core) {t₁ t₁' t₂ t₂' : LTm F n} :
      LCong Ax t₁ t₁' → LCong Ax t₂ t₂' → LCong Ax (pair h t₁ t₂) (pair h t₁' t₂')
  | letpair {n : ℕ} (h : F.Core) {t₁ t₁' : LTm F n} {t₂ t₂' : LTm F (n + 2)} :
      LCong Ax t₁ t₁' → LCong Ax t₂ t₂' → LCong Ax (letpair h t₁ t₂) (letpair h t₁' t₂')
  | letunit {n : ℕ} (h : F.Core) {t₁ t₁' t₂ t₂' : LTm F n} :
      LCong Ax t₁ t₁' → LCong Ax t₂ t₂' → LCong Ax (letunit h t₁ t₂) (letunit h t₁' t₂')
  | inl {n : ℕ} (h : F.Core) {t t' : LTm F n} :
      LCong Ax t t' → LCong Ax (inl h t) (inl h t')
  | inr {n : ℕ} (h : F.Core) {t t' : LTm F n} :
      LCong Ax t t' → LCong Ax (inr h t) (inr h t')
  | case {n : ℕ} (h : F.Core) {t t' : LTm F n} {t₁ t₁' t₂ t₂' : LTm F (n + 1)} :
      LCong Ax t t' → LCong Ax t₁ t₁' → LCong Ax t₂ t₂' →
      LCong Ax (case h t t₁ t₂) (case h t' t₁' t₂')
  | pushProd {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LCong Ax t t' → LCong Ax (pushProd h t) (pushProd h t')
  | pushSum {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LCong Ax t t' → LCong Ax (pushSum h t) (pushSum h t')
  | pushUnit {n : ℕ} (h : F.Push) {t t' : LTm F n} :
      LCong Ax t t' → LCong Ax (pushUnit h t) (pushUnit h t')

/-- The equational theory `t ≡_L t'`. -/
abbrev LEq {n : ℕ} (t t' : LTm F n) : Prop := LCong LAx t t'

/-- Reduction is contained in the equational theory: `⇝_L ⊆ ≡_L`. -/
theorem LStep.toLEq {n : ℕ} {t t' : LTm F n} (h : LStep t t') : LEq t t' := by
  induction h with
  | beta => exact .ax (.beta _ _)
  | congAppL _ _ ih => exact .app ih (.refl _)
  | betaBox => exact .ax (.betaBox _ _)
  | congLetL _ _ ih => exact .letbox ih (.refl _)
  | prodCong h _ _ ih => exact .letpair h ih (.refl _)
  | prodBeta => exact .ax (.betaProd _ _ _ _)
  | unitCong h _ _ ih => exact .letunit h ih (.refl _)
  | unitBeta => exact .ax (.betaUnit _ _)
  | congCase h _ _ _ ih => exact .case h ih (.refl _) (.refl _)
  | caseInl => exact .ax (.betaSumOne _ _ _ _)
  | caseInr => exact .ax (.betaSumTwo _ _ _ _)
  | pushProdCong h _ ih => exact .pushProd h ih
  | pushProdBoxCong h _ ih => exact .pushProd h (.box ih)
  | pushProd => exact .ax (.pushProdBeta _ _ _ _)
  | pushSumCong h _ ih => exact .pushSum h ih
  | pushSumBoxCong h _ ih => exact .pushSum h (.box ih)
  | pushSumInl => exact .ax (.pushSumBetaOne _ _ _)
  | pushSumInr => exact .ax (.pushSumBetaTwo _ _ _)
  | pushUnitCong h _ ih => exact .pushUnit h ih
  | pushUnitBoxCong h _ ih => exact .pushUnit h (.box ih)
  | pushUnit => exact .ax (.pushUnitBeta _ _)

theorem LSteps.toLEq {n : ℕ} {t t' : LTm F n} (h : LSteps t t') : LEq t t' := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact .trans ih h.toLEq

/-- Monotonicity of the congruence closure in the set of axioms. -/
theorem LCong.mono {Ax Ax' : ∀ {n : ℕ}, LTm F n → LTm F n → Prop}
    (hAx : ∀ {n : ℕ} {t t' : LTm F n}, Ax t t' → Ax' t t') {n : ℕ} {t t' : LTm F n}
    (h : LCong Ax t t') : LCong Ax' t t' := by
  induction h with
  | ax h => exact .ax (hAx h)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ ih => exact .lam ih
  | box _ ih => exact .box ih
  | letbox _ _ ih₁ ih₂ => exact .letbox ih₁ ih₂
  | pair h _ _ ih₁ ih₂ => exact .pair h ih₁ ih₂
  | letpair h _ _ ih₁ ih₂ => exact .letpair h ih₁ ih₂
  | letunit h _ _ ih₁ ih₂ => exact .letunit h ih₁ ih₂
  | inl h _ ih => exact .inl h ih
  | inr h _ ih => exact .inr h ih
  | case h _ _ _ ih ih₁ ih₂ => exact .case h ih ih₁ ih₂
  | pushProd h _ ih => exact .pushProd h ih
  | pushSum h _ ih => exact .pushSum h ih
  | pushUnit h _ ih => exact .pushUnit h ih

end Coeffect

namespace Coeffect

variable {F : LLevel}

open LTm in
theorem LAxF.rename {S : LAxSel} {n m : ℕ} {t t' : LTm F n} (h : LAxF S t t') (ρ : Fin n → Fin m) :
    LAxF S (t.rename ρ) (t'.rename ρ) := by
  cases h with
  | beta t₂ t₁ => rw [rename_subst1]; exact .beta _ _
  | eta he t => simp only [LTm.rename, rename_shift]; exact .eta he _
  | betaBox t₁ t₂ => rw [rename_subst1]; exact .betaBox _ _
  | etaBox he t => exact .etaBox he _
  | letCommOne he t₀ t₁ t₂ => simp only [LTm.rename, rename_shift]; exact .letCommOne he _ _ _
  | letCommTwo he t₀ t₁ t₂ => simp only [LTm.rename, rename_shift]; exact .letCommTwo he _ _ _
  | letCommBox he t₁ t₂ => exact .letCommBox he _ _
  | betaUnit h t => exact .betaUnit _ _
  | etaUnit h t => exact .etaUnit _ _
  | betaProd h t₁ t₂ t => rw [rename_subst2]; exact .betaProd _ _ _ _
  | etaProd h t => exact .etaProd _ _
  | betaSumOne h t t₁ t₂ => rw [rename_subst1]; exact .betaSumOne _ _ _ _
  | betaSumTwo h t t₁ t₂ => rw [rename_subst1]; exact .betaSumTwo _ _ _ _
  | etaSum h t => exact .etaSum _ _
  | pushProdBeta h hc t₁ t₂ => exact .pushProdBeta _ _ _ _
  | pushProdEta he h hc t => exact .pushProdEta he _ _ _
  | pushSumBetaOne h hc t => exact .pushSumBetaOne _ _ _
  | pushSumBetaTwo h hc t => exact .pushSumBetaTwo _ _ _
  | pushSumEta he h hc t => exact .pushSumEta he _ _ _
  | pushUnitBeta h hc => exact .pushUnitBeta _ _

/-- The congruence closure of renaming-closed axioms is closed under renaming. -/
theorem LCong.rename {Ax : ∀ {n : ℕ}, LTm F n → LTm F n → Prop}
    (hAx : ∀ {n m : ℕ} {t t' : LTm F n} (ρ : Fin n → Fin m), Ax t t' → Ax (t.rename ρ) (t'.rename ρ))
    {n m : ℕ} {t t' : LTm F n} (h : LCong Ax t t') (ρ : Fin n → Fin m) :
    LCong Ax (t.rename ρ) (t'.rename ρ) := by
  induction h generalizing m with
  | ax h => exact .ax (hAx ρ h)
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ ρ) (ih₂ ρ)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ ρ) (ih₂ ρ)
  | lam _ ih => exact .lam (ih _)
  | box _ ih => exact .box (ih ρ)
  | letbox _ _ ih₁ ih₂ => exact .letbox (ih₁ ρ) (ih₂ _)
  | pair h _ _ ih₁ ih₂ => exact .pair h (ih₁ ρ) (ih₂ ρ)
  | letpair h _ _ ih₁ ih₂ => exact .letpair h (ih₁ ρ) (ih₂ _)
  | letunit h _ _ ih₁ ih₂ => exact .letunit h (ih₁ ρ) (ih₂ ρ)
  | inl h _ ih => exact .inl h (ih ρ)
  | inr h _ ih => exact .inr h (ih ρ)
  | case h _ _ _ ih ih₁ ih₂ => exact .case h (ih ρ) (ih₁ _) (ih₂ _)
  | pushProd h _ ih => exact .pushProd h (ih ρ)
  | pushSum h _ ih => exact .pushSum h (ih ρ)
  | pushUnit h _ ih => exact .pushUnit h (ih ρ)

theorem LEq.rename {n m : ℕ} {t t' : LTm F n} (h : LEq t t') (ρ : Fin n → Fin m) :
    LEq (t.rename ρ) (t'.rename ρ) :=
  LCong.rename (Ax := fun a b => LAxF LAxSel.all a b) (fun ρ h => LAxF.rename h ρ) h ρ

end Coeffect
