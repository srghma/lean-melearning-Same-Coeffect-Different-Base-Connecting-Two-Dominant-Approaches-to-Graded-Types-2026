module

public import RequestProject.Sec2.Fin

/-!
# Graded Poly Base: syntax (Section 4.1)

Graded Poly Base extends Graded Base with System F style polymorphism:

```
A ::= K | A →^r B | α | ∀α. B          t ::= x | λx.t | t₁ t₂ | Λα. t | t @ A
```

Both term variables and type variables are de Bruijn indices: `PTy R k` is the type of types
with `k` free type variables and `PTm R k n` the type of terms with `k` free type variables and
`n` free term variables (`PTm R 0 0` are the closed terms). Terms mention types only in type
applications `t @ A`.
-/

@[expose] public section

namespace Coeffect

universe u

/-- Types of Graded Poly Base with `k` free type variables. -/
inductive PTy (R : Type u) : ℕ → Type u
  /-- a type variable `α` -/
  | tvar {k : ℕ} : Fin k → PTy R k
  /-- the base type `K` -/
  | base {k : ℕ} : PTy R k
  /-- graded functions `A →^r B` -/
  | fn {k : ℕ} : R → PTy R k → PTy R k → PTy R k
  /-- universal quantification `∀α. B` -/
  | all {k : ℕ} : PTy R (k + 1) → PTy R k

namespace PTy

variable {R : Type u}

/-- Renaming of type variables. -/
def rename {k l : ℕ} (ρ : Fin k → Fin l) : PTy R k → PTy R l
  | tvar i => tvar (ρ i)
  | base => base
  | fn r A B => fn r (rename ρ A) (rename ρ B)
  | all B => all (rename (upRen ρ) B)

/-- Lift a type substitution under a type binder. -/
def up {k l : ℕ} (σ : Fin k → PTy R l) : Fin (k + 1) → PTy R (l + 1) :=
  tvar 0 .: (fun i => rename Fin.succ (σ i))

/-- Simultaneous substitution of type variables. -/
def subst {k l : ℕ} (σ : Fin k → PTy R l) : PTy R k → PTy R l
  | tvar i => σ i
  | base => base
  | fn r A B => fn r (subst σ A) (subst σ B)
  | all B => all (subst (up σ) B)

/-- Single substitution `[A/α] B`. -/
abbrev subst1 {k : ℕ} (B : PTy R (k + 1)) (A : PTy R k) : PTy R k := subst (A .: tvar) B

end PTy

/-- Terms of Graded Poly Base with `k` free type variables and `n` free term variables. -/
inductive PTm (R : Type u) : ℕ → ℕ → Type u
  | var {k n : ℕ} : Fin n → PTm R k n
  | app {k n : ℕ} : PTm R k n → PTm R k n → PTm R k n
  | lam {k n : ℕ} : PTm R k (n + 1) → PTm R k n
  /-- type abstraction `Λα. t` -/
  | tlam {k n : ℕ} : PTm R (k + 1) n → PTm R k n
  /-- type application `t @ A` -/
  | tapp {k n : ℕ} : PTm R k n → PTy R k → PTm R k n

namespace PTm

variable {R : Type u}

/-- Renaming of type variables in a term. -/
def trename {k l n : ℕ} (ρ : Fin k → Fin l) : PTm R k n → PTm R l n
  | var i => var i
  | app t₁ t₂ => app (trename ρ t₁) (trename ρ t₂)
  | lam t => lam (trename ρ t)
  | tlam t => tlam (trename (upRen ρ) t)
  | tapp t A => tapp (trename ρ t) (A.rename ρ)

/-- Substitution of types for type variables in a term. -/
def tsubst {k l n : ℕ} (σ : Fin k → PTy R l) : PTm R k n → PTm R l n
  | var i => var i
  | app t₁ t₂ => app (tsubst σ t₁) (tsubst σ t₂)
  | lam t => lam (tsubst σ t)
  | tlam t => tlam (tsubst (PTy.up σ) t)
  | tapp t A => tapp (tsubst σ t) (A.subst σ)

/-- Renaming of term variables. -/
def rename {k n m : ℕ} (ρ : Fin n → Fin m) : PTm R k n → PTm R k m
  | var i => var (ρ i)
  | app t₁ t₂ => app (rename ρ t₁) (rename ρ t₂)
  | lam t => lam (rename (upRen ρ) t)
  | tlam t => tlam (rename ρ t)
  | tapp t A => tapp (rename ρ t) A

/-- Lift a term substitution under a term binder. -/
def up {k n m : ℕ} (σ : Fin n → PTm R k m) : Fin (n + 1) → PTm R k (m + 1) :=
  var 0 .: (fun i => rename Fin.succ (σ i))

/-- Simultaneous substitution of terms for term variables. Under a type binder the substituted
terms are weakened by the new type variable. -/
def subst {k n m : ℕ} (σ : Fin n → PTm R k m) : PTm R k n → PTm R k m
  | var i => σ i
  | app t₁ t₂ => app (subst σ t₁) (subst σ t₂)
  | lam t => lam (subst (up σ) t)
  | tlam t => tlam (subst (fun i => trename Fin.succ (σ i)) t)
  | tapp t A => tapp (subst σ t) A

/-- Single substitution `[s/x] t`. -/
abbrev subst1 {k n : ℕ} (t : PTm R k (n + 1)) (s : PTm R k n) : PTm R k n := subst (s .: var) t

/-- Single type substitution `[A/α] t`. -/
abbrev tsubst1 {k n : ℕ} (t : PTm R (k + 1) n) (A : PTy R k) : PTm R k n :=
  tsubst (A .: PTy.tvar) t

end PTm

end Coeffect
