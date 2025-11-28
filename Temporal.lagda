Some properties of the temporal operators

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

module Temporal(𝔻 : Set)
               (W : World)
               (funExt : Extensionality 0ℓ (lsuc(0ℓ)))
               (EM : ExcludedMiddle (lsuc(0ℓ)))
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)(funExt)

open World.World W


-- Prove this from the existing rules
¬◇↓-semantics→ : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
               → M ⊨ (¬· (◇↓ r F))
               → M ⊨ □↓ r (¬· F)
¬◇↓-semantics→ {Γ} M r F h (t , c₁ , c₂ , c₃)
  with EM {Lift _ (t ≼ (⟦ 𝕣₁ ⋆ ↑ᵣ₁ r ⟧ᵣ· ((((M ≔ Model.w M) ≔ₜ t) ≔⟨ 𝕍ℝ ⟩ t))))}
... | yes p with EM {((((M ≔⟨ 𝕍ℝ ⟩ Model.w M) ≔ₜ t) ≔⟨ 𝕍ℝ ⟩ t)) ⊨ ↑₁ F}
... |   yes q = h (t , c₁ , (p , q) , c₃)
... |   no q = c₂ (λ x y → q y)
¬◇↓-semantics→ {Γ} M r F h (t , c₁ , c₂ , c₃) | no p = c₂ λ x → ⊥-elim (p x)

-- Prove this from the existing rules
□-semantics← : {Γ : Ctxt} (M : Model Γ) (F : Form Γ)
             → ((r : 𝕎) → M ≤ₜ r → (M ≔ₜ r) ⊨ F)
             → M ⊨ □  F
□-semantics← {Γ} M F h (t , c₁ , c₂ , c₃) = c₂ (h t c₁)

-- Prove this from the existing rules
□-semantics→ : {Γ : Ctxt} (M : Model Γ) (F : Form Γ)
             → M ⊨ □  F
             → ((r : 𝕎) → M ≤ₜ r → (M ≔ₜ r) ⊨ F)
□-semantics→ {Γ} M F h w c with EM {(M ≔ₜ w) ⊨ F}
... | yes p = p
... | no p = ⊥-elim (h (w , c , p , λ _ _ _ → lift tt))

□↓-semantics→ : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
              → M ⊨ □↓ r F
              → (t : 𝕎) → (Model.w M) ≼ t → t ≼ (Model.w M · (⟦ r ⟧ᵣ· M)) → (M ≔ₜ t) ⊨ F
□↓-semantics→ {Γ} M r F h t c₁ c₂ with EM {(M ≔ₜ t) ⊨ F}
... | yes p = p
... | no p =
  ⊥-elim (h (t ,
             c₁ ,
             (λ x → p (⊨-↑₁→ {_} {M ≔ₜ t} {F} {𝕍ℝ} (Model.w M) {𝕍ℝ} t
                             (x (lift (subst (λ x → t ≼ Model.w M · x) (sym (⟦↑ᵣ₁⟧ᵣ r (Model.subΓ M) _ _ _ _)) c₂))))) ,
             (λ _ _ _ → lift tt)))

□↓-semantics← : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
              → ((t : 𝕎) → (Model.w M) ≼ t → t ≼ (Model.w M · (⟦ r ⟧ᵣ· M)) → (M ≔ₜ t) ⊨ F)
              → M ⊨ □↓ r F
□↓-semantics← {Γ} M r F h (t , c₁ , c₂ , c₃) =
  c₂ (λ (lift x) → →⊨-↑₁ {_} {M ≔ₜ t} {F} {𝕍ℝ} (Model.w M) {𝕍ℝ} t
                         (h t c₁ (subst (λ x → t ≼ Model.w M · x) (⟦↑ᵣ₁⟧ᵣ r (Model.subΓ M) _ _ _ _) x)))

-- Prove this from the existing rules
□↓-dist : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (P Q : Form Γ)
        → M ⊨ □ (P →· Q)
        → M ⊨ □↓ r P
        → M ⊨ □↓ r Q
□↓-dist {Γ} M r P Q h q =
  □↓-semantics← M r Q
    (λ t c₁ c₂ → □-semantics→ M (P →· Q) h t c₁ (□↓-semantics→ M r P q t c₁ c₂))

-- Prove this from the existing rules
¬◆-semantics→ : {Γ : Ctxt} (M : Model Γ) (F : Form Γ)
              → M ⊨ (¬· (◆ F))
              → M ⊨ ■ (¬· F)
¬◆-semantics→ {Γ} M F h (t , c₁ , c₂ , c₃) with EM {(M ≔ₜ t) ⊨ F}
... | yes p = h (t , c₁ , p , c₃)
... | no p = c₂ p

-- Prove this from the existing rules
¬◇↓◆-semantics→ : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
                → M ⊨ (¬· (◇↓◆ r F))
                → M ⊨ □↓■ r (¬· F)
¬◇↓◆-semantics→ {Γ} M r F h = □↓-dist M r (¬· ◆ F) (■ (¬· F)) 𝕀𝕀 𝕀
  where
  𝕀 : M ⊨ □↓ r (¬· (◆ F))
  𝕀 = ¬◇↓-semantics→ M r (◆ F) h

  𝕀𝕀 : M ⊨ □ ((¬· ◆ F) →· ■ (¬· F))
  𝕀𝕀 = □-semantics← M ((¬· ◆ F) →· ■ (¬· F)) (λ t c q → ¬◆-semantics→ (M ≔ₜ t) F q)

-- ¬· (◇↓◆ Δ ϕ)
-- ⇔ ¬· (◇↓ Δ (◆ ϕ))
-- ⇔ □↓ Δ (■ (¬· ϕ))

\end{code}
