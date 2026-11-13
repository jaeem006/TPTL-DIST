\begin{code}

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

--open import Relation.Nullary using (Dec; yes; no ; ¬)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

open import Axiom.Extensionality.Propositional

open import Misc
open import World

module Automation(𝔻 : Set)
                 (W : World)
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import WorldUtil(W)
open import Semantics(𝔻)(W)

open World.World W

dec∈ : {ℓ : Level} {A : Set ℓ} (a : A) (l : List A)
     → decidable A
     → (a ∈ l) ⊎ ¬ (a ∈ l)
dec∈ {ℓ} {A} a [] dec = inj₂ λ ()
dec∈ {ℓ} {A} a (x ∷ l) dec with dec a x
... | inj₁ p = inj₁ (here p)
... | inj₂ p with dec∈ a l dec
... |   inj₁ q = inj₁ (there q)
... |   inj₂ q = inj₂ 𝕀
  where
  𝕀 : a ∈ (x ∷ l) → ⊥
  𝕀 (here px) = p px
  𝕀 (there r) = q r

decℕ : decidable ℕ
decℕ zero zero = inj₁ refl
decℕ zero (suc b) = inj₂ (λ ())
decℕ (suc a) zero = inj₂ (λ ())
decℕ (suc a) (suc b) with decℕ a b
... | inj₁ p = inj₁ (cong suc p)
... | inj₂ p = inj₂ (λ q → p (suc-injective q))

data DecForm : {Γ : Ctxt} (f : Form Γ) → Set₁ where
  Dec⊤ : {Γ : Ctxt} → DecForm (⊤· {Γ})
  Dec⊥ : {Γ : Ctxt} → DecForm (⊥· {Γ})
  Dec∧ : {Γ : Ctxt} (f g : Form Γ) → DecForm f → DecForm g → DecForm (f ∧· g)
  Dec∨ : {Γ : Ctxt} (f g : Form Γ) → DecForm f → DecForm g → DecForm (f ∨· g)
  Dec→ : {Γ : Ctxt} (f g : Form Γ) → DecForm f → DecForm g → DecForm (f →· g)
--  Dec¬ : {Γ : Ctxt} (f : Form Γ) → DecForm f → DecForm (¬· f)
--  Dec∈ : {Γ : Ctxt} (a : Agent Γ) (A : Agents Γ) → DecForm (a ∈ₐ A)
--  Dec∣ : {Γ : Ctxt} (A : Agents Γ) (n : ℕ) → DecForm (∣ A ∣ₛ＝ n)
  DecＯ : {Γ : Ctxt} (f : Form Γ) → DecForm f → DecForm (Ｏ f)
-- add atoms, Ｓ, Ｙ, Ｂ, Ｆ, _⟨_⟩_

record 𝕎props : Set where
  constructor 𝕨props
  field
    𝕊     : 𝕎 → 𝕎
    𝕊◃    : (w : 𝕎) → w ◃ (𝕊 w)
    ◃injᵣ : {w₁ w₂ w : 𝕎} → w ◃ w₁ → w ◃ w₂ → w₁ ≡ w₂

isDecidable : (WP : 𝕎props)
              {Γ : Ctxt}
              (m : Model Γ)
              (f : Form Γ)
            → DecForm f
            → m ⊨ f ⊎ ¬ m ⊨ f
isDecidable WP {Γ} m f Dec⊤ = inj₁ (lift tt)
isDecidable WP {Γ} m f Dec⊥ = inj₂ (λ ())
-- ∧
isDecidable WP {Γ} m f (Dec∧ g h dg dh) with isDecidable WP m g dg
isDecidable WP {Γ} m f (Dec∧ g h dg dh) | inj₁ p with isDecidable WP m h dh
... | inj₁ q = inj₁ (p , q)
... | inj₂ q = inj₂ (λ (a , b) → q b)
isDecidable WP {Γ} m f (Dec∧ g h dg dh) | inj₂ p = inj₂ (λ (a , b) → p a)
-- ∨
isDecidable WP {Γ} m f (Dec∨ g h dg dh) with isDecidable WP m g dg
isDecidable WP {Γ} m f (Dec∨ g h dg dh) | inj₁ p = inj₁ (inj₁ p)
isDecidable WP {Γ} m f (Dec∨ g h dg dh) | inj₂ p with isDecidable WP m h dh
isDecidable WP {Γ} m f (Dec∨ g h dg dh) | inj₂ p | inj₁ q = inj₁ (inj₂ q)
isDecidable WP {Γ} m f (Dec∨ g h dg dh) | inj₂ p | inj₂ q = inj₂ 𝕀
  where
  𝕀 : (m ⊨ g) ⊎ (m ⊨ h) → ⊥
  𝕀 (inj₁ r) = p r
  𝕀 (inj₂ r) = q r
-- →
isDecidable WP {Γ} m f (Dec→ g h dg dh) with isDecidable WP m g dg
isDecidable WP {Γ} m f (Dec→ g h dg dh) | inj₁ p with isDecidable WP m h dh
... | inj₁ q = inj₁ (λ _ → q)
... | inj₂ q = inj₂ (λ r → q (r p))
isDecidable WP {Γ} m f (Dec→ g h dg dh) | inj₂ p = inj₁ (λ q → ⊥-elim (p q))
{---- ¬
isDecidable WP {Γ} m f (Dec¬ g dg) with isDecidable WP m g dg
isDecidable WP {Γ} m f (Dec¬ g dg) | inj₁ p = inj₂ (λ q → q p)
isDecidable WP {Γ} m f (Dec¬ g dg) | inj₂ p = inj₁ p
--}
{---- ∈
isDecidable WP {Γ} m f (Dec∈ a A) with dec∈ (⟦ a ⟧ᵢ· m) (⟦ A ⟧ₛ· m) decℕ
... | inj₁ p = inj₁ (lift p)
... | inj₂ p = inj₂ (λ z → p (lower z))
-- ∣_∣ₛ＝_
isDecidable WP {Γ} m f (Dec∣ A n) with decℕ (length (⟦ A ⟧ₛ· m)) n
... | inj₁ q = inj₁ (lift q)
... | inj₂ q = inj₂ (λ z → q (lower z))
--}
-- Ｏ
isDecidable WP {Γ} m f (DecＯ g dg) with isDecidable WP (m ≔ₜ (𝕎props.𝕊 WP (Model.w m))) g dg
... | inj₁ q = inj₁ (𝕎props.𝕊 WP (Model.w m) , 𝕎props.𝕊◃ WP (Model.w m) , q)
... | inj₂ q = inj₂ λ (t , r , s) → q (subst (λ z → model (Model.interp m) (Model.run m) z (Model.subΓ m) ⊨ g)
                                             (𝕎props.◃injᵣ WP r (𝕎props.𝕊◃ WP (Model.w m)))
                                             s)

decide : (WP : 𝕎props) {Γ : Ctxt} (m : Model Γ) (f : Form Γ)
       → DecForm f
       → Dec (m ⊨ f)
decide WP m f df = toDec (isDecidable WP m f df)

example0 : (M : Model₀)
           (A : Form₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (⊤· →· ⊤·)))
example0 M A p s h = {!toWitness {Q = decide WP m f df} tt!}
-- toWitness {Q = decide WP m f df} tt

{--
example0′ : (M : Model₀)
            (A : Form₀)
          → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (⊤· →· ⊤·)))
example0′ M A p s h with isDecidable {!!} ((M ≔ₛ s) ≔ₜ 𝟘) (⊤· →· ⊤·) {!!}
... | inj₁ q = {!!}
... | inj₂ q = {!!}

example1′ : (M : Model₀)
            (A : Form₀)
          → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (A →· A)))
example1′ M A p s h with isDecidable {!!} ((M ≔ₛ s) ≔ₜ 𝟘) (A →· A) {!!}
... | inj₁ q = {!--something--!}
... | inj₂ q = {!!}

example1 : (M : Model₀)
           (A : Form₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (A →· A)))
example1 M A p s h = {!--something--!}
--}

\end{code}
