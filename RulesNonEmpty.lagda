Propositional logic rules

\begin{code}
{-# OPTIONS --with-K #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)

open import Agda.Builtin.Equality

open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle -- used to prove rule-classical-sat

open import Misc
open import World

module RulesNonEmpty(𝔻 : Set)
                    (W : World)
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

--open import RulesMisc(𝔻)(W)

open World.World W

--
-- ---------
--   Γ ⊢ r

nonEmptyRes : (Γ : ℂ₀) (r : ℂRes Γ) → Rule
nonEmptyRes Γ r =
  rule [] (nonEmpty Γ (CEr r))

abstract
  nonEmptyRes-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ)
                  → sat-rule M (nonEmptyRes Γ r)
  nonEmptyRes-sat M Γ r h s satΓ = tt

--
-- ---------
--   Γ ⊢ ·

nonEmptyU : (Γ : ℂ₀) → Rule
nonEmptyU Γ =
  rule [] (nonEmpty Γ CEu)

abstract
  nonEmptyU-sat : (M : Model₀) (Γ : ℂ₀)
                → sat-rule M (nonEmptyU Γ)
  nonEmptyU-sat M Γ h s satΓ = tt

--   Γ ⊢ r₁ ⊑ r₂
-- ----------------
--   Γ ⊢ ［r₁,r₂］

nonEmptyI₁ : (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ) → Rule
nonEmptyI₁ Γ r₁ r₂ =
  rule (useq Γ (r₁ ⊑ r₂) ∷ [])
       (nonEmpty Γ (CEi ［ r₁ , r₂ ］))

abstract
  nonEmptyI₁-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ)
                 → sat-rule M (nonEmptyI₁ Γ r₁ r₂)
  nonEmptyI₁-sat M Γ r₁ r₂ (sat₁ , h) s satΓ =
    (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) , ≼-refl , sat₁ s satΓ .lower

--   Γ ⊢ r₁ ⊏ r₂
-- ----------------
--   Γ ⊢ ［r₁,r₂）

nonEmptyI₂ : (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ) → Rule
nonEmptyI₂ Γ r₁ r₂ =
  rule (useq Γ (r₁ ⊏ r₂) ∷ [])
       (nonEmpty Γ (CEi ［ r₁ , r₂ ）))

abstract
  nonEmptyI₂-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ)
                 → sat-rule M (nonEmptyI₂ Γ r₁ r₂)
  nonEmptyI₂-sat M Γ r₁ r₂ (sat₁ , h) s satΓ =
    (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) , ≼-refl , sat₁ s satΓ .lower

--   Γ ⊢ r₁ ⊏ r₂
-- ----------------
--   Γ ⊢ （r₁,r₂］

nonEmptyI₃ : (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ) → Rule
nonEmptyI₃ Γ r₁ r₂ =
  rule (useq Γ (r₁ ⊏ r₂) ∷ [])
       (nonEmpty Γ (CEi （ r₁ , r₂ ］))

abstract
  nonEmptyI₃-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ)
                 → sat-rule M (nonEmptyI₃ Γ r₁ r₂)
  nonEmptyI₃-sat M Γ r₁ r₂ (sat₁ , h) s satΓ =
    (⟦ r₂ ⟧ᵣ· (M ≔ₛ s)) , sat₁ s satΓ .lower , ≼-refl

--   Γ ⊢ r₁ ⊏ r   Γ ⊢ r₁ ⊏ r
-- ---------------------------
--        Γ ⊢ （r₁,r₂）

nonEmptyI₄ : (Γ : ℂ₀) (r₁ r₂ r : ℂRes Γ) → Rule
nonEmptyI₄ Γ r₁ r₂ r =
  rule (useq Γ (r₁ ⊏ r) ∷ useq Γ (r ⊏ r₂) ∷ [])
       (nonEmpty Γ (CEi （ r₁ , r₂ ）))

abstract
  nonEmptyI₄-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ r : ℂRes Γ)
                 → sat-rule M (nonEmptyI₄ Γ r₁ r₂ r)
  nonEmptyI₄-sat M Γ r₁ r₂ r (sat₁ , sat₂ , h) s satΓ =
    (⟦ r ⟧ᵣ· (M ≔ₛ s)) , sat₁ s satΓ .lower  , sat₂ s satΓ .lower

\end{code}
