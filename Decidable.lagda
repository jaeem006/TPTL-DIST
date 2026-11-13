\begin{code}

{-# OPTIONS --safe #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open import Data.Nat
open import Data.Nat.Properties using (suc-injective ; _≟_)
open import Data.List
open import Data.List.Properties using (∷-injectiveˡ ; ∷-injectiveʳ)
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

open import Misc
open import World

module Decidable(W : World)
       where

𝔻 : Set
𝔻 = ℕ

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)

open World.World W


-- Deciders

Comparison-dec : decidable Comparison
Comparison-dec LE LE = inj₁ refl
Comparison-dec LE LT = inj₂ (λ ())
Comparison-dec LE EQ = inj₂ (λ ())
Comparison-dec LE PR = inj₂ (λ ())
Comparison-dec LT LE = inj₂ (λ ())
Comparison-dec LT LT = inj₁ refl
Comparison-dec LT EQ = inj₂ (λ ())
Comparison-dec LT PR = inj₂ (λ ())
Comparison-dec EQ LE = inj₂ (λ ())
Comparison-dec EQ LT = inj₂ (λ ())
Comparison-dec EQ EQ = inj₁ refl
Comparison-dec EQ PR = inj₂ (λ ())
Comparison-dec PR LE = inj₂ (λ ())
Comparison-dec PR LT = inj₂ (λ ())
Comparison-dec PR EQ = inj₂ (λ ())
Comparison-dec PR PR = inj₁ refl

𝕌-dec : decidable 𝕌
𝕌-dec 𝕌Agent  𝕌Agent  = inj₁ refl
𝕌-dec 𝕌Agent  𝕌Agents = inj₂ (λ ())
𝕌-dec 𝕌Agent  𝕌Prop   = inj₂ (λ ())
𝕌-dec 𝕌Agent  𝕌Data   = inj₂ (λ ())
𝕌-dec 𝕌Agents 𝕌Agent  = inj₂ (λ ())
𝕌-dec 𝕌Agents 𝕌Agents = inj₁ refl
𝕌-dec 𝕌Agents 𝕌Prop   = inj₂ (λ ())
𝕌-dec 𝕌Agents 𝕌Data   = inj₂ (λ ())
𝕌-dec 𝕌Prop   𝕌Agent  = inj₂ (λ ())
𝕌-dec 𝕌Prop   𝕌Agents = inj₂ (λ ())
𝕌-dec 𝕌Prop   𝕌Prop   = inj₁ refl
𝕌-dec 𝕌Prop   𝕌Data   = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Agent  = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Agents = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Prop   = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Data   = inj₁ refl

𝕍-dec : decidable 𝕍
𝕍-dec (𝕍𝕌 u) (𝕍𝕌 v) with 𝕌-dec u v
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ h → p (𝕍𝕌-inj h))
𝕍-dec (𝕍𝕌 x) 𝕍ℝ = inj₂ (λ ())
𝕍-dec 𝕍ℝ (𝕍𝕌 x) = inj₂ (λ ())
𝕍-dec 𝕍ℝ 𝕍ℝ = inj₁ refl

Ctxt-dec : decidable Ctxt
Ctxt-dec ⟨⟩ ⟨⟩ = inj₁ refl
Ctxt-dec ⟨⟩ (Δ ، u) = inj₂ (λ ())
Ctxt-dec (Γ ، u) ⟨⟩ = inj₂ (λ ())
Ctxt-dec (Γ ، u) (Δ ، v) with Ctxt-dec Γ Δ
... | inj₂ p = inj₂ (λ k → p (،-inj₁ k))
... | inj₁ refl with 𝕍-dec u v
... |   inj₂ p = inj₂ (λ k → p (،-inj₂ k))
... |   inj₁ refl = inj₁ refl

Form-dec-⊥ : {Γ : Ctxt} (A : Form Γ) → A ≡ ⊥· ⊎ ¬ (A ≡ ⊥·)
Form-dec-⊥ {Γ} (𝕒 x) = inj₂ (λ ())
Form-dec-⊥ {Γ} (var x) = inj₂ (λ ())
Form-dec-⊥ {Γ} ⊤· = inj₂ (λ ())
Form-dec-⊥ {Γ} ⊥· = inj₁ refl
Form-dec-⊥ {Γ} (A ∧· A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A ∨· A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A →· A₁) = inj₂ (λ ())
--Form-dec-⊥ {Γ} (¬· A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (∀· u A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (∃· u A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (𝔸 A) = inj₂ (λ ())
--Form-dec-⊥ {Γ} (x ∈ᵢ x₁) = inj₂ (λ ())
--Form-dec-⊥ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A Ｕ A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｏ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A Ｓ A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｙ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｂ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｆ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ ())

Form-dec-⊤ : {Γ : Ctxt} (A : Form Γ) → A ≡ ⊤· ⊎ ¬ (A ≡ ⊤·)
Form-dec-⊤ {Γ} (𝕒 x) = inj₂ (λ ())
Form-dec-⊤ {Γ} (var x) = inj₂ (λ ())
Form-dec-⊤ {Γ} ⊤· = inj₁ refl
Form-dec-⊤ {Γ} ⊥· = inj₂ (λ ())
Form-dec-⊤ {Γ} (A ∧· A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A ∨· A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A →· A₁) = inj₂ (λ ())
--Form-dec-⊤ {Γ} (¬· A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (∀· u A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (∃· u A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (𝔸 A) = inj₂ (λ ())
--Form-dec-⊤ {Γ} (x ∈ᵢ x₁) = inj₂ (λ ())
--Form-dec-⊤ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A Ｕ A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｏ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A Ｓ A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｙ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｂ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｆ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ ())

Form-dec-∧ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a ∧· b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a ∧· b))
Form-dec-∧ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (var x) = inj₂ (λ a b ())
Form-dec-∧ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∧ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A ∧· A₁) = inj₁ (A , A₁ , refl)
Form-dec-∧ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A →· A₁) = inj₂ (λ a b ())
--Form-dec-∧ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (𝔸 A) = inj₂ (λ a b ())
--Form-dec-∧ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∧ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∨ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a ∨· b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a ∨· b))
Form-dec-∨ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (var x) = inj₂ (λ a b ())
Form-dec-∨ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∨ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A ∨· A₁) = inj₁ (A , A₁ , refl)
Form-dec-∨ {Γ} (A →· A₁) = inj₂ (λ a b ())
--Form-dec-∨ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (𝔸 A) = inj₂ (λ a b ())
--Form-dec-∨ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∨ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-→ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a →· b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a →· b))
Form-dec-→ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-→ {Γ} (var x) = inj₂ (λ a b ())
Form-dec-→ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-→ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-→ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A →· A₁) = inj₁ (A , A₁ , refl)
--Form-dec-→ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (𝔸 A) = inj₂ (λ a b ())
--Form-dec-→ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-→ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-Ｕ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a Ｕ b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a Ｕ b))
Form-dec-Ｕ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (var x) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A →· A₁) = inj₂ (λ a b ())
--Form-dec-Ｕ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (𝔸 A) = inj₂ (λ a b ())
--Form-dec-Ｕ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-Ｕ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A Ｕ A₁) = inj₁ (A , A₁ , refl)
Form-dec-Ｕ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-Ｓ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a Ｓ b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a Ｓ b))
Form-dec-Ｓ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (var x) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A →· A₁) = inj₂ (λ a b ())
--Form-dec-Ｓ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (𝔸 A) = inj₂ (λ a b ())
--Form-dec-Ｓ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-Ｓ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A Ｓ A₁) = inj₁ (A , A₁ , refl)
Form-dec-Ｓ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∀ : {Γ : Ctxt} (A : Form Γ)
           → (Σ 𝕌 (λ a → Σ (Form (Γ ، 𝕍𝕌 a)) (λ b → A ≡ ∀· a b)))
           ⊎ ((a : 𝕌) (b : Form (Γ ، 𝕍𝕌 a)) → ¬ (A ≡ ∀· a b))
Form-dec-∀ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (var x) = inj₂ (λ a b ())
Form-dec-∀ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∀ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A →· A₁) = inj₂ (λ a b ())
--Form-dec-∀ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (∀· u A) = inj₁ (u , A , refl)
Form-dec-∀ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (𝔸 A) = inj₂ (λ a b ())
--Form-dec-∀ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∀ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∃ : {Γ : Ctxt} (A : Form Γ)
           → (Σ 𝕌 (λ a → Σ (Form (Γ ، 𝕍𝕌 a)) (λ b → A ≡ ∃· a b)))
           ⊎ ((a : 𝕌) (b : Form (Γ ، 𝕍𝕌 a)) → ¬ (A ≡ ∃· a b))
Form-dec-∃ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (var x) = inj₂ (λ a b ())
Form-dec-∃ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∃ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A →· A₁) = inj₂ (λ a b ())
--Form-dec-∃ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (∃· u A) = inj₁ (u , A , refl)
Form-dec-∃ {Γ} (𝔸 A) = inj₂ (λ a b ())
--Form-dec-∃ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∃ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-𝔸 : {Γ : Ctxt} (A : Form Γ)
           → (Σ (SetAtom Γ) (λ a → A ≡ 𝔸 a))
           ⊎ ((a : SetAtom Γ) → ¬ (A ≡ 𝔸 a))
Form-dec-𝔸 {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (var x) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} ⊤· = inj₂ (λ a ())
Form-dec-𝔸 {Γ} ⊥· = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (A →· A₁) = inj₂ (λ a ())
--Form-dec-𝔸 {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (𝔸 A) = inj₁ (A , refl)
--Form-dec-𝔸 {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-𝔸 {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-𝔸 {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

{--
Form-dec-∈ₐ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Agent Γ) (λ a → Σ (Agents Γ) (λ b → A ≡ a ∈ₐ b)))
           ⊎ ((a : Agent Γ) (b : Agents Γ) → ¬ (A ≡ a ∈ₐ b))
Form-dec-∈ₐ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (x ∈ₐ x₁) = inj₁ (x , x₁ , refl)
Form-dec-∈ₐ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-∈ₐ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∈ₐ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())
--}

{--
Form-dec-∣∣ₛ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Agents Γ) (λ a → Σ ℕ (λ b → A ≡ ∣ a ∣ₛ＝ b)))
           ⊎ ((a : Agents Γ) (b : ℕ) → ¬ (A ≡ ∣ a ∣ₛ＝ b))
Form-dec-∣∣ₛ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (∣ x ∣ₛ＝ x₁) = inj₁ (x , x₁ , refl)
--Form-dec-∣∣ₛ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∣∣ₛ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())
--}

Form-dec-Ｏ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ Ｏ a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ Ｏ a))
Form-dec-Ｏ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (var x) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｏ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A →· A₁) = inj₂ (λ a ())
--Form-dec-Ｏ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (𝔸 A) = inj₂ (λ a ())
--Form-dec-Ｏ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｏ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｏ A) = inj₁ (A , refl)
Form-dec-Ｏ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-Ｙ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ Ｙ a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ Ｙ a))
Form-dec-Ｙ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (var x) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｙ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A →· A₁) = inj₂ (λ a ())
--Form-dec-Ｙ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (𝔸 A) = inj₂ (λ a ())
--Form-dec-Ｙ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｙ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (Ｙ A) = inj₁ (A , refl)
Form-dec-Ｙ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-Ｂ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ Ｂ a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ Ｂ a))
Form-dec-Ｂ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (var x) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｂ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A →· A₁) = inj₂ (λ a ())
--Form-dec-Ｂ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (𝔸 A) = inj₂ (λ a ())
--Form-dec-Ｂ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｂ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (Ｂ A) = inj₁ (A , refl)
Form-dec-Ｂ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

{--
Form-dec-¬ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ ¬· a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ ¬· a))
Form-dec-¬ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-¬ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-¬ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-¬ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A →· A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (¬· A) = inj₁ (A , refl)
Form-dec-¬ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (𝔸 A) = inj₂ (λ a ())
--Form-dec-¬ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-¬ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())
--}

Form-dec-Ｆ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form (Γ ، 𝕍ℝ)) (λ a → A ≡ Ｆ a))
           ⊎ ((a : Form (Γ ، 𝕍ℝ)) → ¬ (A ≡ Ｆ a))
Form-dec-Ｆ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (var x) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｆ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A →· A₁) = inj₂ (λ a ())
--Form-dec-Ｆ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (𝔸 A) = inj₂ (λ a ())
--Form-dec-Ｆ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｆ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｆ A) = inj₁ (A , refl)
Form-dec-Ｆ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-⟨⟩ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Res Γ) (λ a → Σ (Comparison) (λ b → Σ (Res Γ) (λ c → A ≡ a ⟨ b ⟩ c))))
           ⊎ ((a : Res Γ) (b : Comparison) (c : Res Γ) → ¬ (A ≡ a ⟨ b ⟩ c))
Form-dec-⟨⟩ {Γ} (𝕒 x) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (var x) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} ⊤· = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} ⊥· = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A ∧· A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A ∨· A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A →· A₁) = inj₂ (λ a b c ())
--Form-dec-⟨⟩ {Γ} (¬· A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (∀· u A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (∃· u A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (𝔸 A) = inj₂ (λ a b c ())
--Form-dec-⟨⟩ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b c ())
--Form-dec-⟨⟩ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A Ｕ A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｏ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A Ｓ A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｙ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｂ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｆ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₁ (t₁ , x , t₂ , refl)

Form-dec-𝕒 : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Atom Γ) (λ a → A ≡ 𝕒 a))
           ⊎ ((a : Atom Γ) → ¬ (A ≡ 𝕒 a))
Form-dec-𝕒 {Γ} (𝕒 x) = inj₁ (x , refl)
Form-dec-𝕒 {Γ} (var x) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} ⊤· = inj₂ (λ a ())
Form-dec-𝕒 {Γ} ⊥· = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A →· A₁) = inj₂ (λ a ())
--Form-dec-𝕒 {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (𝔸 A) = inj₂ (λ a ())
--Form-dec-𝕒 {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-𝕒 {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-var : {Γ : Ctxt} (A : Form Γ)
             → (Σ FormVar (λ a → A ≡ var a))
             ⊎ ((a : FormVar) → ¬ (A ≡ var a))
Form-dec-var {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-var {Γ} (var x) = inj₁ (x , refl)
Form-dec-var {Γ} ⊤· = inj₂ (λ a ())
Form-dec-var {Γ} ⊥· = inj₂ (λ a ())
Form-dec-var {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-var {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-var {Γ} (A →· A₁) = inj₂ (λ a ())
--Form-dec-var {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-var {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-var {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-var {Γ} (𝔸 A) = inj₂ (λ a ())
--Form-dec-var {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-var {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-var {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-var {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-var {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-var {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-var {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-var {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-var {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

𝐯-dec : {Γ : Ctxt} {v : 𝕍} → decidable (∈Ctxt v Γ)
𝐯-dec {Γ} {v} (∈Ctxt0 Γ₁) (∈Ctxt0 .Γ₁) = inj₁ refl
𝐯-dec {Γ} {v} (∈Ctxt0 Γ₁) (∈CtxtS .v j) = inj₂ (λ ())
𝐯-dec {Γ} {v} (∈CtxtS u i) (∈Ctxt0 _) = inj₂ (λ ())
𝐯-dec {Γ} {v} (∈CtxtS u i) (∈CtxtS .u j)
  with 𝐯-dec i j
... | inj₂ p = inj₂ (λ k → p (∈CtxtS-inj k))
... | inj₁ refl = inj₁ refl

ℕ-dec : decidable ℕ
ℕ-dec zero zero = inj₁ refl
ℕ-dec zero (suc b) = inj₂ (λ ())
ℕ-dec (suc a) zero = inj₂ (λ ())
ℕ-dec (suc a) (suc b)
  with ℕ-dec a b
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (suc-injective k))

Res-dec : {Γ : Ctxt} → decidable (Res Γ)
Res-dec {Γ} (𝐯 i) (𝐯 j) with 𝐯-dec i j
... | inj₂ p = inj₂ (λ k → p (𝐯-inj k))
... | inj₁ refl = inj₁ refl
Res-dec {Γ} (𝐯 i) 𝟎 = inj₂ (λ ())
Res-dec {Γ} (𝐯 i) (s ⋆ s₁) = inj₂ (λ ())
Res-dec {Γ} 𝟎 (𝐯 i) = inj₂ (λ ())
Res-dec {Γ} 𝟎 𝟎 = inj₁ refl
Res-dec {Γ} 𝟎 (s ⋆ s₁) = inj₂ (λ ())
Res-dec {Γ} (r ⋆ r₁) (𝐯 i) = inj₂ (λ ())
Res-dec {Γ} (r ⋆ r₁) 𝟎 = inj₂ (λ ())
Res-dec {Γ} (r ⋆ r₁) (s ⋆ s₁)
  with Res-dec r s
... | inj₂ p = inj₂ (λ k → p (⋆-inj₁ k))
... | inj₁ refl
  with Res-dec r₁ s₁
... | inj₂ p = inj₂ (λ k → p (⋆-inj₂ k))
... | inj₁ refl = inj₁ refl
Res-dec {Γ} (rvar a) (rvar b) with ℕ-dec a b
... | inj₂ p = inj₂ (λ k → p (rvar-inj k))
... | inj₁ refl = inj₁ refl
Res-dec {Γ} (rvar a) (𝐯 i) = inj₂ (λ ())
Res-dec {Γ} (rvar a) 𝟎 = inj₂ (λ ())
Res-dec {Γ} (rvar a) (s ⋆ s₁) = inj₂ (λ ())
Res-dec {Γ} (𝐯 i) (rvar b) = inj₂ (λ ())
Res-dec {Γ} 𝟎 (rvar b) = inj₂ (λ ())
Res-dec {Γ} (r ⋆ r₁) (rvar b) = inj₂ (λ ())

atomProp-dec : decidable atomProp
atomProp-dec = ℕ-dec

agent-dec : decidable agent
agent-dec = ℕ-dec

AtomProp-dec : {Γ : Ctxt} → decidable (AtomProp Γ)
AtomProp-dec {Γ} (atomPropV i) (atomPropV i₁)
  with 𝐯-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atomPropV-inj k))
AtomProp-dec {Γ} (atomPropV i) (atomPropC x) = inj₂ (λ ())
AtomProp-dec {Γ} (atomPropC x) (atomPropV i) = inj₂ (λ ())
AtomProp-dec {Γ} (atomPropC x) (atomPropC x₁)
  with atomProp-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atomPropC-inj k))

Data-dec : {Γ : Ctxt} → decidable (Data Γ)
Data-dec {Γ} (dataV i) (dataV i₁)
  with 𝐯-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (dataV-inj k))
Data-dec {Γ} (dataV i) (dataC x) = inj₂ (λ ())
Data-dec {Γ} (dataC x) (dataV i) = inj₂ (λ ())
Data-dec {Γ} (dataC x) (dataC x₁)
  with ℕ-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (dataC-inj k))

Agent-dec : {Γ : Ctxt} → decidable (Agent Γ)
Agent-dec {Γ} (agentV i) (agentV i₁)
  with 𝐯-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (agentV-inj k))
Agent-dec {Γ} (agentV i) (agentC x) = inj₂ (λ ())
Agent-dec {Γ} (agentC x) (agentV i) = inj₂ (λ ())
Agent-dec {Γ} (agentC x) (agentC x₁)
  with agent-dec x x₁
... | inj₂ p = inj₂ (λ k → p (agentC-inj k))
... | inj₁ refl = inj₁ refl

AgentL-dec : {Γ : Ctxt} → decidable (List (Agent Γ))
AgentL-dec {Γ} [] [] = inj₁ refl
AgentL-dec {Γ} [] (x ∷ b) = inj₂ (λ ())
AgentL-dec {Γ} (x ∷ a) [] = inj₂ (λ ())
AgentL-dec {Γ} (x ∷ a) (x₁ ∷ b)
  with Agent-dec x x₁
... | inj₂ p = inj₂ (λ k → p (∷-injectiveˡ k))
... | inj₁ refl
  with AgentL-dec a b
... | inj₂ p = inj₂ (λ k → p (∷-injectiveʳ k))
... | inj₁ refl = inj₁ refl

agents-dec : decidable agents
agents-dec [] [] = inj₁ refl
agents-dec [] (x ∷ b) = inj₂ (λ ())
agents-dec (x ∷ a) [] = inj₂ (λ ())
agents-dec (x ∷ a) (x₁ ∷ b)
  with agent-dec x x₁
... | inj₂ p = inj₂ (λ k → p (∷-injectiveˡ k))
... | inj₁ refl
  with agents-dec a b
... | inj₂ p = inj₂ (λ k → p (∷-injectiveʳ k))
... | inj₁ refl = inj₁ refl

Agents-dec : {Γ : Ctxt} → decidable (Agents Γ)
Agents-dec {Γ} (agentsV i) (agentsV i₁)
  with 𝐯-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (agentsV-inj k))
Agents-dec {Γ} (agentsV i) (agentsL x) = inj₂ (λ ())
--Agents-dec {Γ} (agentsV i) (agentsS x) = inj₂ (λ ())
Agents-dec {Γ} (agentsL x) (agentsV i) = inj₂ (λ ())
Agents-dec {Γ} (agentsL x) (agentsL x₁)
  with AgentL-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (agentsL-inj k))
--Agents-dec {Γ} (agentsL x) (agentsS x₁) = inj₂ (λ ())
--Agents-dec {Γ} (agentsS x) (agentsV i) = inj₂ (λ ())
--Agents-dec {Γ} (agentsS x) (agentsL x₁) = inj₂ (λ ())
--Agents-dec {Γ} (agentsS x) (agentsS x₁)
--  with agents-dec x x₁
--... | inj₁ refl = inj₁ refl
--... | inj₂ p = inj₂ (λ k → p (agentsS-inj k))

Action-dec : {Γ : Ctxt} → decidable (Action Γ)
Action-dec {Γ} (ActSend p a A) (ActSend p₁ a₁ A₁)
  with Data-dec p p₁
... | inj₂ q = inj₂ (λ k → q (ActSend-inj₁ k))
... | inj₁ refl
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (ActSend-inj₂ k))
... | inj₁ refl
  with Agents-dec A A₁
... | inj₂ q = inj₂ (λ k → q (ActSend-inj₃ k))
... | inj₁ refl = inj₁ refl

Event-dec : {Γ : Ctxt} → decidable (Event Γ)
Event-dec {Γ} (EvtReceive p a b) (EvtReceive p₁ a₁ b₁)
  with Data-dec p p₁
... | inj₂ q = inj₂ (λ k → q (EvtReceive-inj₁ k))
... | inj₁ refl
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (EvtReceive-inj₂ k))
... | inj₁ refl
  with Agent-dec b b₁
... | inj₂ q = inj₂ (λ k → q (EvtReceive-inj₃ k))
... | inj₁ refl = inj₁ refl
Event-dec {Γ} (EvtReceive p a b₁) (EvtInternal a₁ d) = inj₂ (λ ())
Event-dec {Γ} (EvtInternal a d) (EvtReceive p a₁ b) = inj₂ (λ ())
Event-dec {Γ} (EvtInternal a d) (EvtInternal a₁ d₁)
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (EvtInternal-inj₁ k))
... | inj₁ refl
  with Data-dec d d₁
... | inj₂ q = inj₂ (λ k → q (EvtInternal-inj₂ k))
... | inj₁ refl = inj₁ refl

Fault-dec : {Γ : Ctxt} → decidable (Fault Γ)
Fault-dec {Γ} (FaultCorrect a b) (FaultCorrect a₁ b₁)
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (FaultCorrect-inj₁ k))
... | inj₁ refl
  with Agent-dec b b₁
... | inj₂ q = inj₂ (λ k → q (FaultCorrect-inj₂ k))
... | inj₁ refl = inj₁ refl

Atom-dec : {Γ : Ctxt} → decidable (Atom Γ)
Atom-dec {Γ} (atProp x) (atProp x₁)
  with AtomProp-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atProp-inj k))
Atom-dec {Γ} (atProp x) (atAction x₁) = inj₂ (λ ())
Atom-dec {Γ} (atProp x) (atEvent x₁) = inj₂ (λ ())
Atom-dec {Γ} (atProp x) (atCorrect x₁) = inj₂ (λ ())
Atom-dec {Γ} (atAction x) (atProp x₁) = inj₂ (λ ())
Atom-dec {Γ} (atAction x) (atAction x₁)
  with Action-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atAction-inj k))
Atom-dec {Γ} (atAction x) (atEvent x₁) = inj₂ (λ ())
Atom-dec {Γ} (atAction x) (atCorrect x₁) = inj₂ (λ ())
Atom-dec {Γ} (atEvent x) (atProp x₁) = inj₂ (λ ())
Atom-dec {Γ} (atEvent x) (atAction x₁) = inj₂ (λ ())
Atom-dec {Γ} (atEvent x) (atEvent x₁)
  with Event-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atEvent-inj k))
Atom-dec {Γ} (atEvent x) (atCorrect x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atProp x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atAction x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atEvent x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atCorrect x₁)
  with Fault-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atCorrect-inj k))

SetAtom-dec : {Γ : Ctxt} → decidable (SetAtom Γ)
SetAtom-dec {Γ} (x ∈ₐ X) (y ∈ₐ Y) with Agent-dec x y
... | inj₂ p = inj₂ (λ k → p (∈ₐ-inj₁ k))
... | inj₁ refl with Agents-dec X Y
... | inj₂ q = inj₂ (λ k → q (∈ₐ-inj₂ k))
... | inj₁ refl = inj₁ refl
SetAtom-dec {Γ} (x ∈ₐ X) (∣ y ∣ₛ＝ n) = inj₂ (λ ())
SetAtom-dec {Γ} (∣ x ∣ₛ＝ n) (y ∈ₐ Y) = inj₂ (λ ())
SetAtom-dec {Γ} (∣ x ∣ₛ＝ n) (∣ y ∣ₛ＝ m) with Agents-dec x y
... | inj₂ p = inj₂ (λ k → p (∣∣ₛ-inj₁ k))
... | inj₁ refl with ℕ-dec n m
... | inj₂ q = inj₂ (λ k → q (∣∣ₛ-inj₂ k))
... | inj₁ refl = inj₁ refl

Form-dec : {Γ : Ctxt} → decidable (Form Γ)
Form-dec {Γ} (𝕒 x) B with Form-dec-𝕒 B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Atom-dec x a
... | inj₂ p = inj₂ (λ k → p (𝕒-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (var x) B with Form-dec-var B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with x ≟ a
... | yes p = inj₁ (cong var p)
... | no q = inj₂ (λ k → q (var-inj k))
Form-dec {Γ} ⊤· B with Form-dec-⊤ B
... | inj₂ p = inj₂ (λ k → p (sym k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} ⊥· B with Form-dec-⊥ B
... | inj₂ p = inj₂ (λ k → p (sym k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A ∧· A₁) B with Form-dec-∧ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (∧-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (∧-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A ∨· A₁) B with Form-dec-∨ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (∨-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (∨-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A →· A₁) B with Form-dec-→ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (→-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (→-inj₂ k))
... | inj₁ refl = inj₁ refl
{--Form-dec {Γ} (¬· A) B with Form-dec-¬ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (¬-inj k))
... | inj₁ refl = inj₁ refl--}
Form-dec {Γ} (∀· u A) B with Form-dec-∀ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with 𝕌-dec u a
... | inj₂ p = inj₂ (λ k → p (∀-inj₁ k))
... | inj₁ refl with Form-dec A b
... | inj₂ p = inj₂ (λ k → p (∀-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (∃· u A) B with Form-dec-∃ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with 𝕌-dec u a
... | inj₂ p = inj₂ (λ k → p (∃-inj₁ k))
... | inj₁ refl with Form-dec A b
... | inj₂ p = inj₂ (λ k → p (∃-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (𝔸 A) B with Form-dec-𝔸 B
... | inj₂ p = inj₂ (λ k → p A (sym k))
... | inj₁ (a , refl) with SetAtom-dec A a
... | inj₂ q = inj₂ (λ k → q (𝔸-inj k))
... | inj₁ refl = inj₁ refl
{--Form-dec {Γ} (∣ x ∣ₛ＝ x₁) B with Form-dec-∣∣ₛ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Agents-dec x a
... | inj₂ p = inj₂ (λ k → p (∣∣ₛ-inj₁ k))
... | inj₁ refl with ℕ-dec x₁ b
... | inj₂ p = inj₂ (λ k → p (∣∣ₛ-inj₂ k))
... | inj₁ refl = inj₁ refl--}
--Form-dec {Γ} (x ∈ᵢ x₁) B = {!!}
--Form-dec {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) B = {!!}
Form-dec {Γ} (A Ｕ A₁) B with Form-dec-Ｕ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｕ-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (Ｕ-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｏ A) B with Form-dec-Ｏ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｏ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A Ｓ A₁) B with Form-dec-Ｓ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｓ-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (Ｓ-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｙ A) B with Form-dec-Ｙ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｙ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｂ A) B with Form-dec-Ｂ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｂ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｆ A) B with Form-dec-Ｆ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｆ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (t₁ ⟨ x ⟩ t₂) B with Form-dec-⟨⟩ B
... | inj₂ p = inj₂ (λ k → p _ _ _ (sym k))
... | inj₁ (a , b , c , refl) with Res-dec t₁ a
... | inj₂ p = inj₂ (λ k → p (comp-inj₁ k))
... | inj₁ refl with Comparison-dec x b
... | inj₂ p = inj₂ (λ k → p (comp-inj₂ k))
... | inj₁ refl with Res-dec t₂ c
... | inj₂ p = inj₂ (λ k → p (comp-inj₃ k))
... | inj₁ refl = inj₁ refl

≡⊆-dec : {Γ Δ : Ctxt} (i j : Γ ⊆ Δ) → ≡⊆ i j ⊎ ¬ (≡⊆ i j)
≡⊆-dec {⟨⟩} {Δ} i j = inj₁ (λ ())
≡⊆-dec {Γ ، U} {Δ} i j with 𝐯-dec (i (∈Ctxt0 Γ)) (j (∈Ctxt0 Γ))
... | inj₂ p = inj₂ (λ z → p (z (∈Ctxt0 Γ)))
... | inj₁ p with ≡⊆-dec {Γ} {Δ} (λ z → i (∈CtxtS _ z)) (λ z → j (∈CtxtS _ z))
... |   inj₂ q = inj₂ (λ z → q (λ {u} k → z (∈CtxtS U k)))
... |   inj₁ q = inj₁ h
  where
  h : {u : 𝕍} (z : ∈Ctxt u (Γ ، U)) → i z ≡ j z
  h {u} (∈Ctxt0 .Γ) = p
  h {u} (∈CtxtS .U z) = q z


∈Ctxt-dec : {Γ Δ : Ctxt}
            (e : Γ ⊆ Δ)
            (v : 𝕍)
            (c : ∈Ctxt v Δ)
          → (Σ (∈Ctxt v Γ) (λ d → c ≡ e d)) ⊎ ((d : ∈Ctxt v Γ) → ¬ c ≡ e d)
∈Ctxt-dec {⟨⟩} e v c = inj₂ (λ ())
∈Ctxt-dec {Γ ، w} {Δ} e v c with 𝕍-dec v w
... | inj₁ refl with 𝐯-dec c (e (∈Ctxt0 Γ))
...   | inj₁ refl = inj₁ (∈Ctxt0 Γ , refl)
...   | inj₂ ¬eq
        with ∈Ctxt-dec {Γ} {Δ} (λ {u} d → e (∈CtxtS w d)) v c
...       | inj₁ (d , eq)  = inj₁ (∈CtxtS w d , eq)
...       | inj₂ ¬p        = inj₂ (λ { (∈Ctxt0 .Γ)    → ¬eq
                                     ; (∈CtxtS .w d) → ¬p d })
∈Ctxt-dec {Γ ، w} {Δ} e v c
    | inj₂ v≢w
      with ∈Ctxt-dec {Γ} {Δ} (λ {u} d → e (∈CtxtS w d)) v c
...     | inj₁ (d , eq) = inj₁ (∈CtxtS w d , eq)
...     | inj₂ ¬p       = inj₂ (λ { (∈Ctxt0 .Γ)    → λ z → v≢w refl
                                  ; (∈CtxtS .w d) → ¬p d })

↑ᵣ-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Res Δ)
       → (Σ (Res Γ) (λ d → c ≡ ↑ᵣ e d)) ⊎ ((d : Res Γ) → ¬ c ≡ ↑ᵣ e d)
↑ᵣ-dec {Γ} {Δ} e (𝐯 i)
  with ∈Ctxt-dec e 𝕍World i
... | inj₁ (x , refl) = inj₁ (𝐯 x , refl)
... | inj₂ p = inj₂ (λ { (𝐯 x) refl → p x refl })
↑ᵣ-dec {Γ} {Δ} e 𝟎 = inj₁ (𝟎 , refl)
↑ᵣ-dec {Γ} {Δ} e (c ⋆ c₁)
  with ↑ᵣ-dec e c | ↑ᵣ-dec e c₁
... | inj₁ (x , p) | inj₁ (y , q) = inj₁ ((x ⋆ y) , (cong₂ _⋆_ p q))
... | inj₂ p | _ = inj₂ (λ { (x ⋆ y) z → p x (⋆-inj₁ z) })
... | _ | inj₂ p = inj₂ (λ { (x ⋆ y) z → p y (⋆-inj₂ z) })
↑ᵣ-dec {Γ} {Δ} e (rvar ρ) = inj₁ (rvar ρ , refl)

↑ₚ-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : AtomProp Δ)
       → (Σ (AtomProp Γ) (λ d → c ≡ ↑ₚ e d)) ⊎ ((d : AtomProp Γ) → ¬ c ≡ ↑ₚ e d)
↑ₚ-dec {Γ} {Δ} e (atomPropV i)
  with ∈Ctxt-dec e 𝕍Prop i
... | inj₁ (j , refl) = inj₁ (atomPropV j , refl)
... | inj₂ p = inj₂ λ { (atomPropV j) refl → p j refl }
↑ₚ-dec {Γ} {Δ} e (atomPropC x) = inj₁ (atomPropC x , refl)

↑ᵢ-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Agent Δ)
       → (Σ (Agent Γ) (λ d → c ≡ ↑ᵢ e d)) ⊎ ((d : Agent Γ) → ¬ c ≡ ↑ᵢ e d)
↑ᵢ-dec {Γ} {Δ} e (agentV i)
  with ∈Ctxt-dec e 𝕍Agent i
... | inj₁ (j , refl) = inj₁ (agentV j , refl)
... | inj₂ p = inj₂ λ { (agentV j) refl → p j refl }
↑ᵢ-dec {Γ} {Δ} e (agentC x) = inj₁ (agentC x , refl)

↑ᵢₛ-dec : {Γ Δ : Ctxt}
          (e : Γ ⊆ Δ)
          (c : List (Agent Δ))
        → (Σ (List (Agent Γ)) (λ d → c ≡ Data.List.map (↑ᵢ e) d)) ⊎ ((d : List (Agent Γ)) → ¬ c ≡ Data.List.map (↑ᵢ e) d)
↑ᵢₛ-dec {Γ} {Δ} e [] = inj₁ ([] , refl)
↑ᵢₛ-dec {Γ} {Δ} e (x ∷ c)
  with ↑ᵢ-dec e x | ↑ᵢₛ-dec e c
... | inj₁ (y , refl) | inj₁ (d , refl) = inj₁ (y ∷ d , refl)
... | inj₂ p | _ = inj₂ (λ { (y ∷ d) refl → p y refl })
... | _ | inj₂ p = inj₂ (λ { (y ∷ d) refl → p d refl })

↑ₛ-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Agents Δ)
       → (Σ (Agents Γ) (λ d → c ≡ ↑ₛ e d)) ⊎ ((d : Agents Γ) → ¬ c ≡ ↑ₛ e d)
↑ₛ-dec {Γ} {Δ} e (agentsV i)
  with ∈Ctxt-dec e 𝕍Agents i
... | inj₁ (j , refl) = inj₁ (agentsV j , refl)
... | inj₂ p = inj₂ λ { (agentsV j) refl → p j refl }
↑ₛ-dec {Γ} {Δ} e (agentsL x)
  with ↑ᵢₛ-dec e x
... | inj₁ (y , refl) = inj₁ (agentsL y , refl)
... | inj₂ p = inj₂ λ { (agentsL y) refl → p y refl }

↑d-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Data Δ)
       → (Σ (Data Γ) (λ d → c ≡ ↑d e d)) ⊎ ((d : Data Γ) → ¬ c ≡ ↑d e d)
↑d-dec {Γ} {Δ} e (dataV i)
  with ∈Ctxt-dec e 𝕍Data i
... | inj₁ (j , refl) = inj₁ (dataV j , refl)
... | inj₂ p = inj₂ λ { (dataV j) refl → p j refl }
↑d-dec {Γ} {Δ} e (dataC x) = inj₁ (dataC x , refl)

↑ₜ-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Action Δ)
       → (Σ (Action Γ) (λ d → c ≡ ↑ₜ e d)) ⊎ ((d : Action Γ) → ¬ c ≡ ↑ₜ e d)
↑ₜ-dec {Γ} {Δ} e (ActSend p a A)
  with ↑d-dec e p | ↑ᵢ-dec e a | ↑ₛ-dec e A
... | inj₁ (x , refl) | inj₁ (y , refl) | inj₁ (z , refl) = inj₁ (ActSend x y z , refl)
... | inj₂ p | _ | _ = inj₂ (λ { (ActSend x y z) refl → p x refl })
... | _ | inj₂ p | _ = inj₂ (λ { (ActSend x y z) refl → p y refl })
... | _ | _ | inj₂ p = inj₂ (λ { (ActSend x y z) refl → p z refl })

↑ₑ-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Event Δ)
       → (Σ (Event Γ) (λ d → c ≡ ↑ₑ e d)) ⊎ ((d : Event Γ) → ¬ c ≡ ↑ₑ e d)
↑ₑ-dec {Γ} {Δ} e (EvtReceive p a b)
  with ↑d-dec e p | ↑ᵢ-dec e a | ↑ᵢ-dec e b
... | inj₁ (x , refl) | inj₁ (y , refl) | inj₁ (z , refl) = inj₁ (EvtReceive x y z , refl)
... | inj₂ p | _ | _ = inj₂ (λ { (EvtReceive x y z) refl → p x refl })
... | _ | inj₂ p | _ = inj₂ (λ { (EvtReceive x y z) refl → p y refl })
... | _ | _ | inj₂ p = inj₂ (λ { (EvtReceive x y z) refl → p z refl })
↑ₑ-dec {Γ} {Δ} e (EvtInternal a d)
  with ↑ᵢ-dec e a | ↑d-dec e d
... | inj₁ (x , refl) | inj₁ (y , refl) = inj₁ (EvtInternal x y , refl)
... | inj₂ p | _ = inj₂ (λ { (EvtInternal x y) refl → p x refl })
... | _ | inj₂ p = inj₂ (λ { (EvtInternal x y) refl → p y refl })

↑f-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Fault Δ)
       → (Σ (Fault Γ) (λ d → c ≡ ↑f e d)) ⊎ ((d : Fault Γ) → ¬ c ≡ ↑f e d)
↑f-dec {Γ} {Δ} e (FaultCorrect a b)
  with ↑ᵢ-dec e a | ↑ᵢ-dec e b
... | inj₁ (x , refl) | inj₁ (y , refl) = inj₁ (FaultCorrect x y , refl)
... | inj₂ p | _ = inj₂ (λ { (FaultCorrect x y) refl → p x refl })
... | _ | inj₂ p = inj₂ (λ { (FaultCorrect x y) refl → p y refl })

↑ₐ-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Atom Δ)
       → (Σ (Atom Γ) (λ d → c ≡ ↑ₐ e d)) ⊎ ((d : Atom Γ) → ¬ c ≡ ↑ₐ e d)
↑ₐ-dec {Γ} {Δ} e (atProp x)
  with ↑ₚ-dec e x
... | inj₁ (y , refl) = inj₁ (atProp y , refl)
... | inj₂ p = inj₂ λ { (atProp y) refl → p y refl }
↑ₐ-dec {Γ} {Δ} e (atAction x)
  with ↑ₜ-dec e x
... | inj₁ (y , refl) = inj₁ (atAction y , refl)
... | inj₂ p = inj₂ λ { (atAction y) refl → p y refl }
↑ₐ-dec {Γ} {Δ} e (atEvent x)
  with ↑ₑ-dec e x
... | inj₁ (y , refl) = inj₁ (atEvent y , refl)
... | inj₂ p = inj₂ λ { (atEvent y) refl → p y refl }
↑ₐ-dec {Γ} {Δ} e (atCorrect x)
  with ↑f-dec e x
... | inj₁ (y , refl) = inj₁ (atCorrect y , refl)
... | inj₂ p = inj₂ λ { (atCorrect y) refl → p y refl }

↑A-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : SetAtom Δ)
       → (Σ (SetAtom Γ) (λ d → c ≡ ↑A e d)) ⊎ ((d : SetAtom Γ) → ¬ c ≡ ↑A e d)
↑A-dec {Γ} {Δ} e (a ∈ₐ A)
  with ↑ᵢ-dec e a | ↑ₛ-dec e A
... | inj₁ (x , refl) | inj₁ (y , refl) = inj₁ (x ∈ₐ y , refl)
... | inj₂ p | _ = inj₂ (λ { (x ∈ₐ y) refl → p x refl })
... | _ | inj₂ p = inj₂ (λ { (x ∈ₐ y) refl → p y refl })
↑A-dec {Γ} {Δ} e (∣ a ∣ₛ＝ n)
  with ↑ₛ-dec e a
... | inj₁ (x , refl) = inj₁ (∣ x ∣ₛ＝ n , refl)
... | inj₂ p = inj₂ (λ { (∣ x ∣ₛ＝ n) refl → p x refl })

↑dec : {Γ Δ : Ctxt}
       (e : Γ ⊆ Δ)
       (f : Form Δ)
     → (Σ (Form Γ) (λ g → f ≡ ↑ e g)) ⊎ ((g : Form Γ) → ¬ f ≡ ↑ e g)
↑dec {Γ} {Δ} e (𝕒 x)
  with ↑ₐ-dec e x
... | inj₁ (y , refl) = inj₁ (𝕒 y , refl)
... | inj₂ p = inj₂ λ { (𝕒 y) refl → p y refl }
↑dec {Γ} {Δ} e (var x) = inj₁ (var x , refl)
↑dec {Γ} {Δ} e ⊤· = inj₁ (⊤· , refl)
↑dec {Γ} {Δ} e ⊥· = inj₁ (⊥· , refl)
↑dec {Γ} {Δ} e (f ∧· f₁)
  with ↑dec e f | ↑dec e f₁
... | inj₁ (g , refl) | inj₁ (g₁ , refl) = inj₁ (g ∧· g₁ , refl)
... | _ | inj₂ q = inj₂ (λ { (k ∧· k₁) refl → q k₁ refl })
... | inj₂ q | _ = inj₂ (λ { (k ∧· k₁) refl → q k refl })
↑dec {Γ} {Δ} e (f ∨· f₁)
  with ↑dec e f | ↑dec e f₁
... | inj₁ (g , refl) | inj₁ (g₁ , refl) = inj₁ (g ∨· g₁ , refl)
... | _ | inj₂ q = inj₂ (λ { (k ∨· k₁) refl → q k₁ refl })
... | inj₂ q | _ = inj₂ (λ { (k ∨· k₁) refl → q k refl })
↑dec {Γ} {Δ} e (f →· f₁)
  with ↑dec e f | ↑dec e f₁
... | inj₁ (g , refl) | inj₁ (g₁ , refl) = inj₁ (g →· g₁ , refl)
... | _ | inj₂ q = inj₂ (λ { (k →· k₁) refl → q k₁ refl })
... | inj₂ q | _ = inj₂ (λ { (k →· k₁) refl → q k refl })
↑dec {Γ} {Δ} e (∀· u f)
  with ↑dec (⊆، (𝕍𝕌 u) e) f
... | inj₁ (g , refl) = inj₁ (∀· u g , refl)
... | inj₂ p = inj₂ λ { (∀· u g) refl → p g refl }
↑dec {Γ} {Δ} e (∃· u f)
  with ↑dec (⊆، (𝕍𝕌 u) e) f
... | inj₁ (g , refl) = inj₁ (∃· u g , refl)
... | inj₂ p = inj₂ λ { (∃· u g) refl → p g refl }
↑dec {Γ} {Δ} e (𝔸 x)
  with ↑A-dec e x
... | inj₁ (g , refl) = inj₁ (𝔸 g , refl)
... | inj₂ q = inj₂ (λ { (𝔸 k) refl → q k refl })
↑dec {Γ} {Δ} e (f Ｕ f₁)
  with ↑dec e f | ↑dec e f₁
... | inj₁ (g , refl) | inj₁ (g₁ , refl) = inj₁ (g Ｕ g₁ , refl)
... | _ | inj₂ q = inj₂ (λ { (k Ｕ k₁) refl → q k₁ refl })
... | inj₂ q | _ = inj₂ (λ { (k Ｕ k₁) refl → q k refl })
↑dec {Γ} {Δ} e (Ｏ f)
  with ↑dec e f
... | inj₁ (g , refl) = inj₁ (Ｏ g , refl)
... | inj₂ q = inj₂ (λ { (Ｏ k) refl → q k refl })
↑dec {Γ} {Δ} e (f Ｓ f₁)
  with ↑dec e f | ↑dec e f₁
... | inj₁ (g , refl) | inj₁ (g₁ , refl) = inj₁ (g Ｓ g₁ , refl)
... | _ | inj₂ q = inj₂ (λ { (k Ｓ k₁) refl → q k₁ refl })
... | inj₂ q | _ = inj₂ (λ { (k Ｓ k₁) refl → q k refl })
↑dec {Γ} {Δ} e (Ｙ f)
  with ↑dec e f
... | inj₁ (g , refl) = inj₁ (Ｙ g , refl)
... | inj₂ q = inj₂ (λ { (Ｙ k) refl → q k refl })
↑dec {Γ} {Δ} e (Ｂ f)
  with ↑dec e f
... | inj₁ (g , refl) = inj₁ (Ｂ g , refl)
... | inj₂ q = inj₂ (λ { (Ｂ k) refl → q k refl })
↑dec {Γ} {Δ} e (Ｆ f)
  with ↑dec (⊆، 𝕍ℝ e) f
... | inj₁ (g , refl) = inj₁ (Ｆ g , refl)
... | inj₂ q = inj₂ (λ { (Ｆ k) refl → q k refl })
↑dec {Γ} {Δ} e (t₁ ⟨ x ⟩ t₂)
  with ↑ᵣ-dec e t₁ | ↑ᵣ-dec e t₂
... | inj₁ (g , refl) | inj₁ (g₁ , refl) = inj₁ (g ⟨ x ⟩ g₁ , refl)
... | _ | inj₂ q = inj₂ (λ { (k ⟨ x ⟩ k₁) refl → q k₁ refl })
... | inj₂ q | _ = inj₂ (λ { (k ⟨ x ⟩ k₁) refl → q k refl })

\end{code}
