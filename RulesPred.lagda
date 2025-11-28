Predicate logic rules

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

module RulesPred(𝔻 : Set)
                (W : World)
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open import RulesMisc(𝔻)(W)

open World.World W

--      Γ, u ⊢ᵣ A
--  ------------------
--     Γ ⊢ᵣ ∀ u A

rule∀I : (Γ : ℂ₀) (r : ℂCE Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) → Rule
rule∀I Γ r u A =
  rule [ seq (ℂv Γ (𝕍𝕌 u)) (↑CE₀ r) A ]
       (seq Γ r (∀· u A))

abstract
  rule∀I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u)))
             → sat-rule M (rule∀I Γ r u A)
  rule∀I-sat M Γ r u A (satA , _) s satΓ =
    sat-ctxt-annot∀ u A r (M ≔ₛ s) concl
    where
    concl : (v : ⟦𝕌⟧ u) → sat-ctxt-annot A (↑CE₀ r) ((M ≔ₛ s) ≔ v)
    concl v = satA (s ⹁ 𝕍𝕌 u ∶ v) satΓ

--   Γ,(∀u.A)ᴿ,σ(A)ᴿ ⊢[T] B
-- --------------------------
--      Γ,(∀u.A)ᴿ ⊢[T] B

rule∀L : (Γ : ℂ₀) (T : ℂCE Γ) (R : ℂCE Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ) (v : ℂ⟦𝕌⟧ Γ u) → Rule
rule∀L Γ T R u A B v =
  rule (seq (ℂx (ℂx Γ (∀· u A) R) (sub A (CSub،ₗ v)) R) T B ∷ [])
       (seq (ℂx Γ (∀· u A) R) T B)

abstract
  rule∀L-sat : (M : Model₀) (Γ : ℂ₀) (T : ℂCE Γ) (R : ℂCE Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ) (v : ℂ⟦𝕌⟧ Γ u)
             → sat-rule M (rule∀L Γ T R u A B v)
  rule∀L-sat M Γ T R u A B v (satB , _) s (satΓ , sat∀A) =
    satB s ((satΓ , sat∀A) , sat-ctxt-annot→sub A R v (sat-ctxt-annot∀→ u A R (M ≔ₛ s) sat∀A (⟦ 𝕍𝕌 u ، v ⟧c· (M ≔ₛ s))))

-- Derived from ∀L & thin:
--     Γ,σ(A)ᴿ ⊢[T] B
-- ----------------------
--    Γ,(∀u.A)ᴿ ⊢[T] B

rule∀L′ : (Γ : ℂ₀) (T R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ) (v : ℂ⟦𝕌⟧ Γ u) → Rule
rule∀L′ Γ T R u A B v =
  rule (rseq (ℂe Γ (sub A (CSub،ₗ v)) R) T B ∷ [])
       (rseq (ℂe Γ (∀· u A) R) T B)

abstract
  rule∀L′-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ) (v : ℂ⟦𝕌⟧ Γ u)
              → sat-rule M (rule∀L′ Γ T R u A B v)
  rule∀L′-sat M Γ T R u A B v (satB , _) =
    rule∀L-sat M Γ (CEr T) (CEr R) u A B v
      (rule-thin1-sat M Γ (∀· u A) (sub A (CSub،ₗ v)) (CEr R) (CEr R) (CEr T) B (satB , lift tt) ,
      lift tt)

--    Γ,x:U,(A)ᴿ ⊢[T] B
-- -------------------------
--    Γ,(∃ U A)ᴿ ⊢[T] B

rule∃L : (Γ : ℂ₀) (T : ℂCE Γ) (R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ) → Rule
rule∃L Γ T R u A B =
  rule (seq (ℂe (ℂv Γ (𝕍𝕌 u)) A (↑ᵣ₀ R)) (↑CE₀ T) (↑₀ B) ∷ [])
       (seq (ℂe Γ (∃· u A) R) T B)

abstract
  rule∃L-sat : (M : Model₀) (Γ : ℂ₀) (T : ℂCE Γ) (R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ)
             → sat-rule M (rule∃L Γ T R u A B)
  rule∃L-sat M Γ T R u A B (satB , _) s (satΓ , (v , sat∃)) =
    sat-ctxt-annot↑⊆→
      {ℂtxt Γ} {ℂtxt Γ ، 𝕍𝕌 u} B T (s ⹁ 𝕍𝕌 u ∶ v) ⊆₀ Sub⊆-⊆₀
      (satB (s ⹁ 𝕍𝕌 u ∶ v) (satΓ , (subst (λ x → ((M ≔ₛ (s ⹁ 𝕍𝕌 u ∶ v)) ≔ₜ x) ⊨ A) (sym (⟦↑ᵣ₀⟧ᵣ R s (𝕍𝕌 u) v)) sat∃)))

--    Γ ⊢[T] A[0\v]
-- -------------------------
--    Γ ⊢[T] ∃ U A

rule∃R : (Γ : ℂ₀) (T : ℂCE Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (v : ℂ⟦𝕌⟧ Γ u) → Rule
rule∃R Γ T u A v =
  rule (seq Γ T (sub A (CSub،ₗ v)) ∷ [])
       (seq Γ T (∃· u A))

abstract
  rule∃R-sat : (M : Model₀) (Γ : ℂ₀) (T : ℂCE Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (v : ℂ⟦𝕌⟧ Γ u)
             → sat-rule M (rule∃R Γ T u A v)
  rule∃R-sat M Γ T u A v (satA , _) s satΓ =
    sat-ctxt-annot∃ u A T (M ≔ₛ s)
      (𝕌⟦ v ⟧c s , sat-ctxt-annot→sub-rev A T v (satA s satΓ))

\end{code}
