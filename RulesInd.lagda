\begin{code}

{-# OPTIONS --with-K #-}
{-# OPTIONS --safe #-}

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

module RulesInd(𝔻 : Set)
               (W : World)
       where

open import WorldUtil(W)
open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open World.World W

-- Wrong Induction:
--     Γ, x:𝕍ℝ, A^[0,x) ⊢[x] A
-- -----------------------------------
--        Γ, x:𝕍ℝ ⊢[x] A

wrong-induction : (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ)) → Rule
wrong-induction Γ A =
  rule [ rseq (ℂi (ℂv Γ 𝕍ℝ) A ［ ↑ᵣ₀ 𝟎 , 𝕣₀ ）) 𝕣₀ A ]
       (rseq (ℂv Γ 𝕍ℝ) 𝕣₀ A)

{--
abstract
  wrong-induction-sat : (L : Linear {lsuc(0ℓ)} W)
                        (M : Model₀)
                        (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ))
                      → sat-rule M (wrong-induction Γ A)
  wrong-induction-sat L M Γ A (hyp , _) (s ⹁ .𝕍ℝ ∶ v) satΓ =
    Linear.ind L (λ v → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ v)) ≔ₜ v) ⊨ A) 𝕀 v
    where
    𝕀 : (w : 𝕎)
      → ((z u : 𝕎) → u ≼ z → z ◃ w → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ u)) ≔ₜ u) ⊨ A)
      → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ w) ⊨ A
    𝕀 w I = hyp (s ⹁ 𝕍ℝ ∶ w) (satΓ , 𝕀𝕀)
      where
      𝕀𝕀 : (y : 𝕎)
         → (𝟘 ≼ y) × (y ≺ w)
         → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ y) ⊨ A
      𝕀𝕀 y (c₁ , c₂) with ≺⇒◃ᵣ y w c₂
      ... | w₀ , d₁ , d₂ =
        {!I w₀ y !} {--→⊨-↑⊆ {ℂtxt Γ ، 𝕍ℝ} {ℂtxt Γ ، 𝕍ℝ ، 𝕍ℝ}
              {((M ≔ₛ s) ≔ y) ≔ₜ y} {A}
              ((s ⹁ 𝕍ℝ ∶ w) ⹁ 𝕍ℝ ∶ y)
              (⊆، 𝕍ℝ ⊆₀) Sub⊆-⊆،-⊆₀ (I w₀ y d₁ d₂)--}
--}

-- Induction on resources:
--     Γ, x:𝕍ℝ, (Ｆ A)^[0,x) ⊢[x] A
-- -----------------------------------
--        Γ, x:𝕍ℝ ⊢[x] A

rule-induction : (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ)) → Rule
rule-induction Γ A =
  rule [ rseq (ℂi (ℂv Γ 𝕍ℝ) (↑₀ (Ｆ A)) ［ ↑ᵣ₀ 𝟎 , 𝕣₀ ）) 𝕣₀ A ]
       (rseq (ℂv Γ 𝕍ℝ) 𝕣₀ A)

abstract
  rule-induction-sat : (L : Induction {lsuc(0ℓ)} W)
                       (M : Model₀)
                       (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ))
                     → sat-rule M (rule-induction Γ A)
  rule-induction-sat L M Γ A (hyp , _) (s ⹁ .𝕍ℝ ∶ v) satΓ =
    Induction.ind L (λ v → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ v)) ≔ₜ v) ⊨ A) 𝕀 v
    where
    𝕀 : (w : 𝕎)
      → ((z u : 𝕎) → u ≼ z → z ◃ w → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ u)) ≔ₜ u) ⊨ A)
      → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ w) ⊨ A
    𝕀 w I = hyp (s ⹁ 𝕍ℝ ∶ w) (satΓ , 𝕀𝕀)
      where
      𝕀𝕀 : (y : 𝕎)
         → (𝟘 ≼ y) × (y ≺ w)
         → (((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ y) ≔ₜ y) ⊨ ↑ (⊆، 𝕍ℝ ⊆₀) A
      𝕀𝕀 y (c₁ , c₂) with ≺⇒◃ᵣ y w c₂
      ... | w₀ , d₁ , d₂ =
        →⊨-↑⊆ {ℂtxt Γ ، 𝕍ℝ} {ℂtxt Γ ، 𝕍ℝ ، 𝕍ℝ}
              {((M ≔ₛ s) ≔ y) ≔ₜ y} {A}
              ((s ⹁ 𝕍ℝ ∶ w) ⹁ 𝕍ℝ ∶ y)
              (⊆، 𝕍ℝ ⊆₀) Sub⊆-⊆،-⊆₀ (I w₀ y d₁ d₂)

→Ｂ : {Γ : Ctxt} (M : Model Γ) (A : Form Γ)
   → ((w : 𝕎) → w ◃ Model.w M → (M ≔ₜ w) ⊨ A)
   → M ⊨ Ｂ A
→Ｂ {Γ} M A h = h

→■ : {Γ : Ctxt} (M : Model Γ) (A : Form Γ)
   → ((w : 𝕎) → w ≼ Model.w M → (M ≔ₜ w) ⊨ A)
   → M ⊨ ■ A
→■ {Γ} M A h (t , c₁ , c₂ , c₃) = c₂ (h t c₁)

→■· : {Γ : Ctxt} (M : Model Γ) (A : Form Γ)
    → ((w : 𝕎) → w ≺ Model.w M → (M ≔ₜ w) ⊨ A)
    → M ⊨ ■· A
→■· {Γ} M A h w q = →■ (M ≔ₜ w) A (λ u c → h u (≼-≺-trans c (◃→≺ q)))

-- Another way to state induction
--     Γ, x:𝕍ℝ, (Ｆ (◆· A))^x ⊢[x] A
-- -----------------------------------
--        Γ, x:𝕍ℝ ⊢[x] A

wrong-induction′ : (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ)) → Rule
wrong-induction′ Γ A =
  rule [ rseq (ℂe (ℂv Γ 𝕍ℝ) (↑₀ (Ｆ (■· A))) 𝕣₀) 𝕣₀ A ]
       (rseq (ℂv Γ 𝕍ℝ) 𝕣₀ A)

-- This is not true if we were to define ■· as Ｙ (■ _) because Ｙ requires the existence of a previous point in time.
-- We need another Ｙ, namely Ｂ, that uses a ∀ instead of an ∃.
-- This one is wrong for a similar reason to above.
{--
abstract
  wrong-induction′-sat : (L : Linear {lsuc(0ℓ)} W)
                         (M : Model₀)
                         (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ))
                       → sat-rule M (wrong-induction′ Γ A)
  wrong-induction′-sat L M Γ A (hyp , _) (s ⹁ .𝕍ℝ ∶ v) satΓ =
    Linear.ind L (λ v → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ v)) ≔ₜ v) ⊨ A) 𝕀 v
    where
    𝕀 : (w : 𝕎)
      → ((z u : 𝕎) → u ≼ z → z ◃ w → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ u)) ≔ₜ u) ⊨ A)
      → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ w) ⊨ A
    𝕀 w I = hyp (s ⹁ 𝕍ℝ ∶ w) (satΓ , 𝕀𝕀)
      where
      𝕀𝕀𝕀 : ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ w) ⊨ ■· A
      𝕀𝕀𝕀 = →■· ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ w) A (λ u c → {!I!})

      𝕀𝕀 : (((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ w) ≔ₜ w) ⊨ ↑ ⊆₀، (■· A)
      𝕀𝕀 = →⊨-↑⊆ {ℂtxt Γ ، 𝕍ℝ} {ℂtxt Γ ، 𝕍ℝ ، 𝕍ℝ} {((M ≔ₛ s) ≔ w) ≔ₜ w} {■· A}
            ((s ⹁ 𝕍ℝ ∶ w) ⹁ 𝕍ℝ ∶ w) ⊆₀، Sub⊆-⊆،-⊆₀
            𝕀𝕀𝕀
--}

-- Another way to state induction
--     Γ, x:𝕍ℝ, (Ｆ (◆· A))^x ⊢[x] A
-- -----------------------------------
--        Γ, x:𝕍ℝ ⊢[x] A

rule-induction′ : (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ)) → Rule
rule-induction′ Γ A =
  rule [ rseq (ℂe (ℂv Γ 𝕍ℝ) (↑₀ (■· (Ｆ A))) 𝕣₀) 𝕣₀ A ]
       (rseq (ℂv Γ 𝕍ℝ) 𝕣₀ A)
abstract
  rule-induction′-sat : (L : Induction {lsuc(0ℓ)} W)
                        (M : Model₀)
                        (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ))
                      → sat-rule M (rule-induction′ Γ A)
  rule-induction′-sat L M Γ A (hyp , _) (s ⹁ .𝕍ℝ ∶ v) satΓ =
    Induction.ind L (λ v → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ v)) ≔ₜ v) ⊨ A) 𝕀 v
    where
    𝕀 : (w : 𝕎)
      → ((z u : 𝕎) → u ≼ z → z ◃ w → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ u)) ≔ₜ u) ⊨ A)
      → ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ w) ⊨ A
    𝕀 w I = hyp (s ⹁ 𝕍ℝ ∶ w) (satΓ , 𝕀𝕀)
      where
      𝕀𝕀𝕀 : (u : 𝕎) → u ≺ w → ((M ≔ₛ s) ≔ₜ u) ⊨ (Ｆ A)
      𝕀𝕀𝕀 u c with ≺⇒◃ᵣ u w c
      ... | v , c₁ , c₂ = I v u c₁ c₂

      𝕀𝕀 : ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ w)) ≔ₜ w) ⊨ ↑ ⊆₀ (■· (Ｆ A))
      𝕀𝕀 = →⊨-↑⊆ {ℂtxt Γ} {ℂtxt Γ ، 𝕍ℝ} {(M ≔ₛ s) ≔ₜ w} {■· (Ｆ A)}
            (s ⹁ 𝕍ℝ ∶ w) ⊆₀ Sub⊆-⊆₀ (→■· ((M ≔ₛ s) ≔ₜ w) (Ｆ A) 𝕀𝕀𝕀)

\end{code}
