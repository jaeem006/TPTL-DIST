Automation

\begin{code}
{-# OPTIONS --with-K #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Axiom.ExcludedMiddle -- used to prove rule-classical-sat
open import Data.Product
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Maybe
open import Agda.Builtin.Equality
open import Data.List using (List ; _∷_ ; [])

open import Misc
open import World

module Index2026(W : World)
                (EM : ExcludedMiddle (lsuc(0ℓ)))
       where

-- Data is ℕ
open import Index2025(ℕ)(W)(EM) public

open import Syntax(ℕ)(W)
open import Subst(ℕ)(W)
open import Decidable(W)
open import Semantics(ℕ)(W)

open import RulesProp(ℕ)(W)          -- propositional logic
open import RulesPred(ℕ)(W)          -- predicate logic
open import RulesTemp(ℕ)(W)          -- timed/temporal rules
open import RulesClassical(ℕ)(W)(EM) -- rules that require classical reasoning
open import RulesInd(ℕ)(W)           -- induction rule
open import RulesMisc(ℕ)(W)          -- other rules
open import RulesNonEmpty(ℕ)(W)      -- otherNon empty rules

open import Plug(W)
open import Automation(W)
open import Examples(W)

-- hand written proof of the validity of rule◇↓R
Section5-hand-written-rule◇↓R-sat : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ)
                                  → sat-rule M (rule◇↓R Γ t r r₁ A)
Section5-hand-written-rule◇↓R-sat = rule◇↓R-sat

section5-1-⊢ : Sequent → Set₂
section5-1-⊢ = ⊢

Section5-1-sound : (M : Model₀) {s : Sequent} → ⊢ s → sat-sequent M s
Section5-1-sound = sound

Section5-1-search⊢ : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
Section5-1-search⊢ = search⊢

Section5-2-Form-dec : {Γ : Ctxt} → decidable (Form Γ)
Section5-2-Form-dec = Form-dec

Section5-2-plug-⊢ : (Γ : ℂ₀) (σ : FormSub⋆ (ℂtxt Γ)) (ρ : ResSub⋆ (ℂtxt Γ))
                    {Δ : ℂ₀} {T : ℂCE Δ} {C : ℂForm Δ}
                  → ⊢ (seq Δ T C)
                  → ⊢ (seq (plug Γ σ ρ Δ) (⟪ Γ ⟫CE σ ρ Δ T) (⟪ Γ ⟫ σ ρ Δ C))
Section5-2-plug-⊢ = plug-⊢

Section5-3-hyps→rule : (M : Model₀) (Γ : ℂ₀) (ps : Prems Γ) (T : ℂCE Γ) (D : ℂForm Γ)
                     → sat-sequent M (seq (addHyps Γ ps) (castCEₕ Γ ps T) (castFₕ Γ ps D))
                     → sat-rule M (rule (Data.List.map (mkSeq Γ) ps) (seq Γ T D))
Section5-3-hyps→rule = hyps→rule

Section5-3-◇↓R-subst : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ)
                     → sat-rule M (rule◇↓R Γ t r r₁ A)
Section5-3-◇↓R-subst = ◇↓R-subst

\end{code}
