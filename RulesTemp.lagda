Temporal logic rules

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

module RulesTemp(𝔻 : Set)
                (W : World)
       where

open import WorldUtil(W)
open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)
open import RulesProp(𝔻)(W)
open import RulesMisc(𝔻)(W)

open World.World W

--    Γ ⊢[t₂] r₁ ⟨ c ⟩ r₂
-- ------------------------
--    Γ ⊢[t₁] r₁ ⟨ c ⟩ r₂

rule-comp-change-resources : (Γ : ℂ₀) (t₁ t₂ r₁ r₂ : ℂRes Γ) (c : Comparison) → Rule
rule-comp-change-resources Γ t₁ t₂ r₁ r₂ c =
  rule (rseq Γ t₂ (r₁ ⟨ c ⟩ r₂) ∷ [])
       (rseq Γ t₁ (r₁ ⟨ c ⟩ r₂))

abstract
  rule-comp-change-resources-sat : (M : Model₀) (Γ : ℂ₀) (t₁ t₂ r₁ r₂ : ℂRes Γ) (c : Comparison)
                                 → sat-rule M (rule-comp-change-resources Γ t₁ t₂ r₁ r₂ c)
  rule-comp-change-resources-sat M Γ t₁ t₂ r₁ r₂ c (sat1 , _) s satΓ = lift (lower (sat1 s satΓ))

--    Γ ⊢[t₂] ∣ A ∣ₛ＝ n
-- ------------------------
--    Γ ⊢[t₁] ∣ A ∣ₛ＝ n

rule-size-change-resources : (Γ : ℂ₀) (t₁ t₂ : ℂRes Γ) (A : ℂAgents Γ) (n : ℕ) → Rule
rule-size-change-resources Γ t₁ t₂ A n =
  rule (rseq Γ t₂ (𝔸 (∣ A ∣ₛ＝ n)) ∷ [])
       (rseq Γ t₁ (𝔸 (∣ A ∣ₛ＝ n)))

abstract
  rule-size-change-resources-sat : (M : Model₀) (Γ : ℂ₀) (t₁ t₂ : ℂRes Γ) (A : ℂAgents Γ) (n : ℕ)
                                 → sat-rule M (rule-size-change-resources Γ t₁ t₂ A n)
  rule-size-change-resources-sat M Γ t₁ t₂ A n (sat1 , _) s satΓ = lift (lower (sat1 s satΓ))

--    Γ ⊢ r ≤ r₁    Γ ⊢ᵣ₁ B     Γ, r ≤ x, x ≤ r₁ ⊢ₓ A
-- ----------------------------------------------------
--                   Γ ⊢ᵣ A Ｕ B

ruleＵR : (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A B : ℂForm Γ) → Rule
ruleＵR Γ r r₁ A B =
  rule (useq Γ (r ⊑ r₁)
        ∷ rseq Γ r₁ B
        ∷ rseq (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ x)) (x ⊏ ↑ᵣ₀ r₁)) x (↑₀ A)
        ∷ [])
    (rseq Γ r (A Ｕ B))
  where
  x : Res (ℂtxt Γ ، 𝕍ℝ)
  x = 𝕣₀

abstract
  ruleＵR-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A B : ℂForm Γ)
               → sat-rule M (ruleＵR Γ r r₁ A B)
  ruleＵR-sat M Γ r r₁ A B (sat1 , sat2 , sat3 , _) s satΓ =
    (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) ,
    𝕀 , 𝕀𝕀 , 𝕀𝕀𝕀
    where
    𝕀 : (⟦ r ⟧ᵣ s) ≼ (⟦ r₁ ⟧ᵣ s)
    𝕀 = lower (sat1 s satΓ)

    𝕀𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ r₁ ⟧ᵣ s)) ⊨ B
    𝕀𝕀 = sat2 s satΓ

    𝕀𝕀𝕀 : (t′ : 𝕎)
        → (⟦ r ⟧ᵣ s) ≼ t′
        → t′ ≺ (⟦ r₁ ⟧ᵣ s)
        → ((M ≔ₛ s) ≔ₜ t′) ⊨ A
    𝕀𝕀𝕀 t′ satT1 satT2 = ⊨⊨ₜ-↑₀→ {ℂtxt Γ} {M ≔ₛ s} {A} {𝕍ℝ} t′ t′ s3
      where
      s3 : ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ t′)) ≔ₜ t′) ⊨ (↑₀ A)
      s3 = sat3 (s ⹁ 𝕍ℝ ∶ t′) ((satΓ , lift s4) , lift s5)
        where
        s4 : (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t′)) ≼ t′
        s4 =  subst (λ x → x ≼ t′) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t′)) satT1

        s5 : t′ ≺ (⟦ ↑ᵣ₀ r₁ ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t′))
        s5 = subst (λ x → t′ ≺ x) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r₁ s t′)) satT2


--    Γ , r ≤ x , B^x , A^[r,x) ⊢T C
-- ------------------------------------
--          Γ, (A Ｕ B)^r ⊢T C

ruleＵL : (Γ : ℂ₀) (T r : ℂRes Γ) (A B C : ℂForm Γ) → Rule
ruleＵL Γ T r A B C =
  rule (rseq (ℂi (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ B) 𝕣₀) (↑₀ A) ［ ↑ᵣ₀ r , 𝕣₀ ）)
            (↑ᵣ₀ T)
            (↑₀ C)
        ∷ [])
       (rseq (ℂe Γ (A Ｕ B) r) T C)

abstract
  ruleＵL-sat : (M : Model₀) (Γ : ℂ₀) (T r : ℂRes Γ) (A B C : ℂForm Γ)
             → sat-rule M (ruleＵL Γ T r A B C)
  ruleＵL-sat M Γ T r A B C (sat1 , _) s (satΓ , t , c₁ , c₂ , c₃) = 𝕀
    where
    𝕀𝕀𝕀 : ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ t)) ≔ₜ (⟦ ↑ᵣ₀ T ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t))) ⊨ (↑₀ C)
    𝕀𝕀𝕀 =
      sat1 (s ⹁ 𝕍ℝ ∶ t)
           (((satΓ , lift (subst (λ x → x ≼ t) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) c₁)) ,
             →⊨⊨ₜ-↑₀ {ℂtxt Γ} {M ≔ₛ s} {B} {𝕍ℝ} t (⟦ 𝕣₀ ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t)) c₂) ,
           λ w (d₁ , d₂) →
             →⊨⊨ₜ-↑₀ {ℂtxt Γ} {M ≔ₛ s} {A} {𝕍ℝ} t w
                     (c₃ w (≼-trans (subst (λ x → (⟦ r ⟧ᵣ s) ≼ x) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) ≼-refl) d₁) d₂))

    𝕀𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ₀ T ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t))) ⊨ C
    𝕀𝕀 = ⊨⊨ₜ-↑₀→ {ℂtxt Γ} {M ≔ₛ s} {C} {𝕍ℝ} t (⟦ ↑ᵣ₀ T ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t)) 𝕀𝕀𝕀

    𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ T ⟧ᵣ s)) ⊨ C
    𝕀 = subst (λ z → ((M ≔ₛ s) ≔ₜ z) ⊨ C) (⟦↑ᵣ₀⟧ᵣ𝕎 T s t) 𝕀𝕀

--    Γ , x ≤ r , B^x , A^(x,r] ⊢T C
-- ------------------------------------
--          Γ, (A Ｓ B)^r ⊢T C

ruleＳL : (Γ : ℂ₀) (R r : ℂRes Γ) (A B C : ℂForm Γ) → Rule
ruleＳL Γ T r A B C =
  rule (rseq (ℂi (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ r)) (↑₀ B) 𝕣₀) (↑₀ A) （ 𝕣₀ , ↑ᵣ₀ r ］)
            (↑ᵣ₀ T)
            (↑₀ C)
        ∷ [])
       (rseq (ℂe Γ (A Ｓ B) r) T C)

abstract
  ruleＳL-sat : (M : Model₀) (Γ : ℂ₀) (T r : ℂRes Γ) (A B C : ℂForm Γ)
             → sat-rule M (ruleＳL Γ T r A B C)
  ruleＳL-sat M Γ T r A B C (sat1 , _) s (satΓ , t , c₁ , c₂ , c₃) = 𝕀
    where
    𝕀𝕀𝕀 : ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ t)) ≔ₜ (⟦ ↑ᵣ₀ T ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t))) ⊨ (↑₀ C)
    𝕀𝕀𝕀 =
      sat1 (s ⹁ 𝕍ℝ ∶ t)
           (((satΓ , lift (subst (λ x → t ≼ x) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) c₁)) ,
             →⊨⊨ₜ-↑₀ {ℂtxt Γ} {M ≔ₛ s} {B} {𝕍ℝ} t (⟦ 𝕣₀ ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t)) c₂) ,
           λ w (d₁ , d₂) →
             →⊨⊨ₜ-↑₀ {ℂtxt Γ} {M ≔ₛ s} {A} {𝕍ℝ} t w
                     (c₃ w d₁ (≼-trans d₂ (subst (λ x → x ≼ (⟦ r ⟧ᵣ s)) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) ≼-refl))))

    𝕀𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ₀ T ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t))) ⊨ C
    𝕀𝕀 = ⊨⊨ₜ-↑₀→ {ℂtxt Γ} {M ≔ₛ s} {C} {𝕍ℝ} t (⟦ ↑ᵣ₀ T ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t)) 𝕀𝕀𝕀

    𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ T ⟧ᵣ s)) ⊨ C
    𝕀 = subst (λ z → ((M ≔ₛ s) ≔ₜ z) ⊨ C) (⟦↑ᵣ₀⟧ᵣ𝕎 T s t) 𝕀𝕀

--    Γ ⊢ r ◁ r₁   Γ ⊢ᵣ₁ A
-- --------------------------
--         Γ ⊢ᵣ Ｏ A

ruleＯR : (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ) → Rule
ruleＯR Γ r  r₁ A =
  rule (useq Γ (r ◁ r₁)
       ∷ rseq Γ r₁ A
       ∷ [])
  (rseq Γ r (Ｏ A))

abstract
  ruleＯR-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (ruleＯR Γ r r₁ A)
  ruleＯR-sat M Γ r r₁ A (satR , satA , _) s satΓ =
    (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) ,
    𝕀 , 𝕀𝕀
    where
    𝕀 :  (⟦ r ⟧ᵣ· (M ≔ₛ s)) ◃ (⟦ r₁ ⟧ᵣ· (M ≔ₛ s))
    𝕀 = lower (satR s satΓ)

    𝕀𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ r₁ ⟧ᵣ s)) ⊨ A
    𝕀𝕀 = satA s satΓ

--    Γ ⊢ r₁ ≤ r    Γ ⊢ᵣ₁ B     Γ, r₁ ≤ x, x ≤ r ⊢ₓ A
-- ----------------------------------------------------
--                   Γ ⊢ᵣ A Ｓ B

ruleＳR : (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A B : ℂForm Γ) → Rule
ruleＳR Γ r r₁ A B =
  rule (useq Γ (r₁ ⊑ r)
        ∷ rseq Γ r₁ B
        ∷ rseq (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r₁ ⊏ x)) (x ⊑ ↑ᵣ₀ r)) x (↑₀ A)
        ∷ [])
    (rseq Γ r (A Ｓ B))
  where
  x : Res (ℂtxt Γ ، 𝕍ℝ)
  x = 𝕣₀

abstract
  ruleＳR-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A B : ℂForm Γ)
             → sat-rule M (ruleＳR Γ r r₁ A B)
  ruleＳR-sat M Γ r r₁ A B (sat1 , sat2 , sat3 , _) s satΓ =
    (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) ,
    𝕀 , 𝕀𝕀 , 𝕀𝕀𝕀
    where
    𝕀 : (⟦ r₁ ⟧ᵣ s) ≼ (⟦ r ⟧ᵣ s)
    𝕀 = lower (sat1 s satΓ)

    𝕀𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ r₁ ⟧ᵣ s)) ⊨ B
    𝕀𝕀 = sat2 s satΓ

    𝕀𝕀𝕀 : (t′ : 𝕎)
        → (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) ≺ t′
        → ((M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)) ≥ₜ t′
        → ((M ≔ₛ s) ≔ₜ t′) ⊨ A
    𝕀𝕀𝕀 t′ satT1 satT2 = ⊨⊨ₜ-↑₀→ {ℂtxt Γ} {M ≔ₛ s} {A} {𝕍ℝ} t′ t′ s3
      where
      s3 : ((M ≔ₛ (s ⹁ 𝕍ℝ ∶ t′)) ≔ₜ t′) ⊨ (↑₀ A)
      s3 = sat3 (s ⹁ 𝕍ℝ ∶ t′) ((satΓ , lift s4) , lift s5)
        where
        s4 : (⟦ ↑ᵣ₀ r₁ ⟧ᵣ· (M ≔ₛ (s ⹁ 𝕍ℝ ∶ t′))) ≺ t′
        s4 = subst (λ x → x ≺ t′) (sym (⟦⊆⟧ᵣ s ⊆₀ (s ⹁ 𝕍ℝ ∶ t′) Sub⊆-⊆₀ r₁)) satT1

        s5 :  t′ ≼ (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t′))
        s5 = subst (λ x → t′ ≼ x) (sym (⟦⊆⟧ᵣ s ⊆₀ (s ⹁ 𝕍ℝ ∶ t′) Sub⊆-⊆₀ r)) satT2


--    Γ ⊢ r₁ ◁ r   Γ ⊢ᵣ₁ A
-- --------------------------
--         Γ ⊢ᵣ Ｙ A

ruleＹR : (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ) → Rule
ruleＹR Γ r r₁ A =
  rule (useq Γ (r₁ ◁ r)
       ∷ rseq Γ r₁ A
       ∷ [])
  (rseq Γ r (Ｙ A))

abstract
  ruleＹR-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (ruleＹR Γ r r₁ A)
  ruleＹR-sat M Γ r r₁ A (satR , satA , _) s satΓ =
    (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) ,
    𝕀 , 𝕀𝕀
    where
    𝕀 :  (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) ◃ (⟦ r ⟧ᵣ· (M ≔ₛ s))
    𝕀 = lower (satR s satΓ)

    𝕀𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ r₁ ⟧ᵣ s)) ⊨ A
    𝕀𝕀 = satA s satΓ


--   Γ ⊢ᵣ A[x/r]
-- ----------------
--   Γ ⊢ᵣ x Ｆ A

ruleＦR : (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm (ℂv Γ 𝕍ℝ)) → Rule
ruleＦR Γ r A =
  rule (rseq Γ r (subℝ A r) ∷  [])
       (rseq Γ r (Ｆ A))

abstract
  ruleＦR-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm (ℂv Γ 𝕍ℝ))
               → sat-rule M (ruleＦR Γ r A)
  ruleＦR-sat M Γ r A (satA , _) s satΓ =
    𝕀
    where
    ℍ : ((M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)) ⊨ (subℝ A r)
    ℍ = satA s satΓ

    𝕀 : (((M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)) ≔ (⟦ r ⟧ᵣ s)) ⊨ A
    𝕀 = ≔→sub-rev (ℂtxt Γ) A r ℍ


{--
--     ⟦r₁⟧ ⟦c⟧ ⟦r₂⟧
-- -----------------------
--    Γ ⊢ᵣ r₁ ⟨ c ⟩ r₂


rule⟨c⟩ : (Γ : ℂ₀) ( r r₁ r₂ : ℂRes Γ) (c : Comparison) → Rule
rule⟨c⟩ Γ r r₁ r₂ c =
  rule []
  (rseq Γ r (r₁ ⟨ c ⟩ r₂))
--}

ruleＦL : (Γ : ℂ₀) (r : ℂRes Γ) (T : ℂCE Γ) (A : Form (ℂtxt Γ ، 𝕍ℝ)) (C : ℂForm Γ) → Rule
ruleＦL Γ r T A C =
  rule (seq (ℂe Γ (subℝ A r) r) T C ∷ [])
       (seq (ℂe Γ (Ｆ A) r) T C)

abstract
  ruleＦL-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (T : ℂCE Γ) (A : Form (ℂtxt Γ ، 𝕍ℝ)) (C : ℂForm Γ)
             → sat-rule M (ruleＦL Γ r T A C)
  ruleＦL-sat M Γ r T A C (sat1 , _) s (satΓ , satA) =
    sat1 s (satΓ , 𝕀)
    where
    𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)) ⊨ subℝ A r
    𝕀 = ≔→sub (ℂtxt Γ) {(M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)} {𝕍ℝ} A r satA

--   r ∈［r₀,r₁］   Γ, Aʳ ⊢ₜ B
-- -----------------------------
--       Γ,A［r₀,r₁］ ⊢ₜ B

ruleIn : (Γ : ℂ₀) (r r′ : ℂRes Γ) (i : ℂInterval Γ) (A B : ℂForm Γ) → Rule
ruleIn Γ r r′ i A B =
  rule (rseq Γ r′ (interval r i) ∷ rseq (ℂe Γ A r) r′ B ∷ [] )
       (rseq (ℂi Γ A i) r′ B)

abstract
  ruleIn-sat : (M : Model₀) (Γ : ℂ₀) (r r′ : ℂRes Γ) (i : ℂInterval Γ) (A B : ℂForm Γ)
             → sat-rule M (ruleIn Γ r r′ i A B)
  ruleIn-sat M Γ r r′ i A B (sat1 , sat2 , _) s (satΓ , h) =
    sat2 s (satΓ , (h (⟦ r ⟧ᵣ s) (⊨interval→inter-cond M Γ s _ r i (sat1 s satΓ))))

--     Γ, r₁ ⟨c⟩ r₂ ⊢ᵣ A
-- -------------------------
--    Γ, (r₁ ⟨c⟩ r₂)ˡ ⊢ᵣ A

ruleLE : (Γ : ℂ₀) (r r′ r₁ r₂ : ℂRes Γ) (c : Comparison) (A : ℂForm Γ) → Rule
ruleLE Γ r r′ r₁ r₂ c A =
  rule [ rseq (ℂu Γ (r₁ ⟨ c ⟩ r₂)) r A ]
       (rseq (ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) r A)

{--
--     Γ, r₁ ⟨c⟩ r₂, Δ ⊢ᵣ A
-- -------------------------
--    Γ, (r₁ ⟨c⟩ r₂)ˡ, Δ ⊢ᵣ A

ruleLE′ : (Γ : ℂ₀) (Δ : ℂℂ Γ) (r : ℂRes Δ) (r′ r₁ r₂ : ℂRes Γ) (c : Comparison) (A : ℂForm Δ) → Rule
ruleLE′ Γ Δ r r′ r₁ r₂ c A =
  rule [ rseq ((ℂu Γ (r₁ ⟨ c ⟩ r₂)) ⨾ Δ) (⋆Res (≡ℂtxt⨾ (ℂu Γ (r₁ ⟨ c ⟩ r₂)) Δ) r) (⋆Form (≡ℂtxt⨾ (ℂu Γ (r₁ ⟨ c ⟩ r₂)) Δ) A) ]
       (rseq ((ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) ⨾ Δ) (⋆Res (≡ℂtxt⨾ (ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) Δ) r) (⋆Form (≡ℂtxt⨾ (ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) Δ) A))
--}

--     Γ, r₁ ⟨c⟩ r₂, Δ ⊢ᵣ A
-- -------------------------
--    Γ, (r₁ ⟨c⟩ r₂)ˡ, Δ ⊢ᵣ A

ruleLE′ : (Γ : ℂ₀) (Δ : ℂℂ Γ)
          (r′ r₁ r₂ : ℂRes Γ)
          (c : Comparison)
          (r : ℂRes ((ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) ⨾ Δ))
          (A : ℂForm ((ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) ⨾ Δ)) → Rule
ruleLE′ Γ Δ r′ r₁ r₂ c r A =
  rule [ rseq ((ℂu Γ (r₁ ⟨ c ⟩ r₂)) ⨾ Δ) (⋆Res (≡ℂtxt⨾⨾ (ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) (ℂu Γ (r₁ ⟨ c ⟩ r₂)) Δ Δ refl) r)
                                        (⋆Form (≡ℂtxt⨾⨾ (ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) (ℂu Γ (r₁ ⟨ c ⟩ r₂)) Δ Δ refl) A) ]
       (rseq ((ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) ⨾ Δ) r A)

ruleLE′-sat-ctxt : (c : ℂ₀) (d : ℂℂ c)
                   (r′ r₁ r₂ : ℂRes c)
                   (x : Comparison)
                   (e : ℂtxt (ℂe c (r₁ ⟨ x ⟩ r₂) r′ ⨾ d) ≡ ℂtxt (ℂu c (r₁ ⟨ x ⟩ r₂) ⨾ d))
                   (M : Model₀)
                   (s : ℂSub (ℂe c (r₁ ⟨ x ⟩ r₂) r′ ⨾ d))
                 → sat-ctxt (ℂe c (r₁ ⟨ x ⟩ r₂) r′ ⨾ d) (M ≔ₛ s)
                 → sat-ctxt (ℂu c (r₁ ⟨ x ⟩ r₂) ⨾ d) (M ≔ₛ ⋆Sub e s)
ruleLE′-sat-ctxt c ℂ⟨⟩ r′ r₁ r₂ x refl M s h = h
ruleLE′-sat-ctxt c (ℂx d f a) r′ r₁ r₂ x e M s (h , q) =
  (ruleLE′-sat-ctxt c d r′ r₁ r₂ x e M s h) ,
  sat-ctxt-annot-*subst M
   (ℂtxt {ℂtxt {⟨⟩} (ℂe c (r₁ ⟨ x ⟩ r₂) r′)} d)
   (ℂtxt (ℂe c (r₁ ⟨ x ⟩ r₂) r′ ⨾ d))
   (ℂtxt (ℂu c (r₁ ⟨ x ⟩ r₂) ⨾ d))
   e (≡ℂtxt⨾ (ℂe c (r₁ ⟨ x ⟩ r₂) r′) d) (≡ℂtxt⨾ (ℂu c (r₁ ⟨ x ⟩ r₂)) d) s f a q
ruleLE′-sat-ctxt c (ℂv d v) r′ r₁ r₂ x e M s h =
  subst (λ z → sat-ctxt (ℂu c (r₁ ⟨ x ⟩ r₂) ⨾ d) (M ≔ₛ z))
        (sym (Sub،→-⋆Sub e s))
        (ruleLE′-sat-ctxt c d r′ r₁ r₂ x (،-inj e) M (Sub،→ s) h)

abstract
  ruleLE′-sat : (M : Model₀) (Γ : ℂ₀) (Δ : ℂℂ Γ)
                (r′ r₁ r₂ : ℂRes Γ)
                (c : Comparison)
                (r : ℂRes ((ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) ⨾ Δ))
                (A : ℂForm ((ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) ⨾ Δ))
              → sat-rule M (ruleLE′ Γ Δ r′ r₁ r₂ c r A)
  ruleLE′-sat M Γ Δ r′ r₁ r₂ c r A (satA , _) s satΓ =
    sat-⋆Sub M e s r A (satA (⋆Sub e s) (ruleLE′-sat-ctxt Γ Δ r′ r₁ r₂ c e M s satΓ))
    where
    e : ℂtxt (ℂe Γ (r₁ ⟨ c ⟩ r₂) r′ ⨾ Δ) ≡ ℂtxt (ℂu Γ (r₁ ⟨ c ⟩ r₂) ⨾ Δ)
    e = ≡ℂtxt⨾⨾ (ℂe Γ (r₁ ⟨ c ⟩ r₂) r′) (ℂu Γ (r₁ ⟨ c ⟩ r₂)) Δ Δ refl

{--
ruleLEIn : (Γ : ℂ₀) ( r r₁ r₂ : ℂRes Γ) (i : ℂInterval Γ) (c : Comparison) (A : ℂForm Γ) → Rule
ruleLEIn Γ r r₁ r₂ i c A =
  rule (rseq (ℂu Γ (r₁ ⟨ c ⟩ r₂)) r A ∷ [])
       (rseq (ℂi Γ (r₁ ⟨ c ⟩ r₂) i) r A)
--}

--  Γ ⊢[T] r₁ ⊑ r     Γ ⊢[T] r ⊑ r₂
-- ------------------------------------
--    Γ ⊢[T] r₁ ⊑ r₂

rule⊑-trans : (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ) → Rule
rule⊑-trans Γ r₁ r r₂ R =
  rule (rseq Γ R (r₁ ⊑ r) ∷ rseq Γ R (r ⊑ r₂) ∷ [])
       (rseq Γ R (r₁ ⊑ r₂))

abstract
  rule⊑-trans-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ)
                  → sat-rule M (rule⊑-trans Γ r₁ r r₂ R)
  rule⊑-trans-sat M Γ r₁ r r₂ R (sat1 , sat2 , _) s satΓ =
    lift (≼-trans (lower (sat1 s satΓ)) (lower (sat2 s satΓ)))

--  Γ ⊢[T] r₁ ⊑ r     Γ ⊢[T] r ⊏ r₂
-- ------------------------------------
--    Γ ⊢[T] r₁ ⊏ r₂

rule⊏-transᵣ : (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ) → Rule
rule⊏-transᵣ Γ r₁ r r₂ R =
  rule (rseq Γ R (r₁ ⊑ r) ∷ rseq Γ R (r ⊏ r₂) ∷ [])
       (rseq Γ R (r₁ ⊏ r₂))

abstract
  rule⊏-transᵣ-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ)
                   → sat-rule M (rule⊏-transᵣ Γ r₁ r r₂ R)
  rule⊏-transᵣ-sat M Γ r₁ r r₂ R (sat1 , sat2 , _) s satΓ =
    lift (≼-≺-trans (lower (sat1 s satΓ)) (lower (sat2 s satΓ)))

--
-- -----------------------
--    Γ ⊢[T] r ⊑ r


rule⊑-refl : (Γ : ℂ₀) (r R : ℂRes Γ) → Rule
rule⊑-refl Γ r R =
  rule []
       (rseq Γ R (r ⊑ r))

abstract
  rule⊑-refl-sat : (M : Model₀) (Γ : ℂ₀) (r R : ℂRes Γ)
                 → sat-rule M (rule⊑-refl Γ r R)
  rule⊑-refl-sat M Γ r R _ s satΓ =
    lift ≼-refl

--    Γ ⊢[T] r₁ ⊑ r₂      Γ ⊢[T] s₁ ⊑ s₂
-- ----------------------------------------
--       Γ ⊢[T] r₁ ⋆ s₁ ⊑ r₂ ⋆ s₂

rule⊑-⋆-cong : (Γ : ℂ₀) (r₁ s₁ r₂ s₂ R : ℂRes Γ) → Rule
rule⊑-⋆-cong Γ r₁ s₁ r₂ s₂ R =
  rule (rseq Γ R (r₁ ⊑ r₂) ∷ rseq Γ R (s₁ ⊑ s₂) ∷ [])
       (rseq Γ R (r₁ ⋆ s₁ ⊑ r₂ ⋆ s₂))

abstract
  rule⊑-⋆-cong-sat : (M : Model₀) (Γ : ℂ₀) (r₁ s₁ r₂ s₂ R : ℂRes Γ)
                   → sat-rule M (rule⊑-⋆-cong Γ r₁ s₁ r₂ s₂ R)
  rule⊑-⋆-cong-sat M Γ r₁ s₁ r₂ s₂ R (sat1 , sat2 , _) s satΓ =
    lift (·-cong-≼ (lower (sat1 s satΓ)) (lower (sat2 s satΓ)))


-- Derived:
--             Γ ⊢[T] r₁ ⊑ r₂
-- ----------------------------------------
--       Γ ⊢[T] r₁ ⋆ s₁ ⊑ r₂ ⋆ s₁

rule⊑-⋆-cong2 : (Γ : ℂ₀) (r₁ s₁ r₂ R : ℂRes Γ) → Rule
rule⊑-⋆-cong2 Γ r₁ s₁ r₂ R =
  rule (rseq Γ R (r₁ ⊑ r₂) ∷ [])
       (rseq Γ R (r₁ ⋆ s₁ ⊑ r₂ ⋆ s₁))

abstract
  rule⊑-⋆-cong2-sat : (M : Model₀) (Γ : ℂ₀) (r₁ s₁ r₂  R : ℂRes Γ)
                    → sat-rule M (rule⊑-⋆-cong2 Γ r₁ s₁ r₂ R)
  rule⊑-⋆-cong2-sat M Γ r₁ s₁ r₂  R (sat1  , _) =
    rule⊑-⋆-cong-sat M Γ r₁ s₁ r₂ s₁ R
      (sat1 ,
       rule⊑-refl-sat M Γ s₁ R (lift tt) ,
       lift tt)

-- ---------------------------------------------
--    Γ ⊢[R] r₁ ⋆ (r₂ ⋆ r₃) = (r₁ ⋆ r₂) ⋆ r₃

rule＝-⋆-assoc : (Γ : ℂ₀) (r₁ r₂ r₃ R : ℂRes Γ) → Rule
rule＝-⋆-assoc Γ r₁ r₂ r₃ R =
  rule []
       (rseq Γ R (r₁ ⋆ (r₂ ⋆ r₃) ＝ (r₁ ⋆ r₂) ⋆ r₃))

abstract
  rule＝-⋆-assoc-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ r₃ R : ℂRes Γ)
                     → sat-rule M (rule＝-⋆-assoc Γ r₁ r₂ r₃ R)
  rule＝-⋆-assoc-sat M Γ r₁ r₂ r₃ R _ s satΓ =
    lift (·-assoc _ _ _)

rule＝-⋆-sym : (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ) (R : ℂCE Γ) → Rule
rule＝-⋆-sym Γ r₁ r₂ R =
  rule []
       (seq Γ R (r₁ ⋆ r₂ ＝ r₂ ⋆ r₁))

abstract
  rule＝-⋆-sym-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ : ℂRes Γ) (R : ℂCE Γ)
                   → sat-rule M (rule＝-⋆-sym Γ r₁ r₂ R)
  rule＝-⋆-sym-sat M Γ r₁ r₂ R _ s satΓ =
    sat-ctxt-annot＝ (r₁ ⋆ r₂) (r₂ ⋆ r₁) R _ (lift (·-sym _ _))

--   Γ ⊢[R] r₁ ＝ r₂   Γ ⊢[R] s₁ ＝ s₂
-- -------------------------------------
--    Γ ⊢[R] r₁ ⋆ s₁ ＝ r₂ ⋆ s₂

rule＝-⋆-cong : (Γ : ℂ₀) (r₁ s₁ r₂ s₂ R : ℂRes Γ) → Rule
rule＝-⋆-cong Γ r₁ s₁ r₂ s₂ R =
  rule (rseq Γ R (r₁ ＝ r₂) ∷ rseq Γ R (s₁ ＝ s₂) ∷ [])
       (rseq Γ R (r₁ ⋆ s₁ ＝ r₂ ⋆ s₂))

abstract
  rule＝-⋆-cong-sat : (M : Model₀) (Γ : ℂ₀) (r₁ s₁ r₂ s₂ R : ℂRes Γ)
                   → sat-rule M (rule＝-⋆-cong Γ r₁ s₁ r₂ s₂ R)
  rule＝-⋆-cong-sat M Γ r₁ s₁ r₂ s₂ R (sat1 , sat2 , _) s satΓ =
    lift (cong₂ _·_ (lower (sat1 s satΓ)) (lower (sat2 s satΓ)))

--
-- ----------------------------
--    Γ ⊢[R] r ＝ r

rule＝-refl : (Γ : ℂ₀) (r : ℂRes Γ) (R : ℂCE Γ) → Rule
rule＝-refl Γ r R =
  rule []
       (seq Γ R (r ＝ r))

abstract
  rule＝-refl-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (R : ℂCE Γ)
                 → sat-rule M (rule＝-refl Γ r R)
  rule＝-refl-sat M Γ r R _ s satΓ =
    sat-ctxt-annot＝ r r R _ (lift refl)

-- Derived:
--
--        Γ ⊢[R] r₁ ＝ r₂
-- ----------------------------
--    Γ ⊢[R] r ⋆ r₁ ＝ r ⋆ r₂

rule＝-⋆-congᵣ : (Γ : ℂ₀) (r r₁ r₂ R : ℂRes Γ) → Rule
rule＝-⋆-congᵣ Γ r r₁ r₂ R =
  rule (rseq Γ R (r₁ ＝ r₂) ∷ [])
       (rseq Γ R (r ⋆ r₁ ＝ r ⋆ r₂))

abstract
  rule＝-⋆-congᵣ-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ r₂ R : ℂRes Γ)
                    → sat-rule M (rule＝-⋆-congᵣ Γ r r₁ r₂ R)
  rule＝-⋆-congᵣ-sat M Γ r r₁ r₂ R (sat1 , _) =
    rule＝-⋆-cong-sat M Γ r r₁ r r₂ R (rule＝-refl-sat M Γ r (CEr R) (lift tt) , sat1 , lift tt)

--    Γ ⊢[R] r₂ ＝ r₁
-- --------------------
--    Γ ⊢[R] r₁ ＝ r₂

rule＝-sym : (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ) → Rule
rule＝-sym Γ r₁ r₂ R =
  rule [ rseq Γ R (r₂ ＝ r₁) ]
       (rseq Γ R (r₁ ＝ r₂))

abstract
  rule＝-sym-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ)
                 → sat-rule M (rule＝-sym Γ r₁ r₂ R)
  rule＝-sym-sat M Γ r₁ r₂ R (sat1 , _) s satΓ =
    lift (sym (lower (sat1 s satΓ)))

--    Γ ⊢[R] r₁ ＝ r₂
-- --------------------
--    Γ ⊢[R] r₁ ⊑ r₂

rule＝→⊑ : (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ) → Rule
rule＝→⊑ Γ r₁ r₂ R =
  rule (rseq Γ R (r₁ ＝ r₂) ∷ [])
       (rseq Γ R (r₁ ⊑ r₂))

abstract
  rule＝→⊑-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ)
              → sat-rule M (rule＝→⊑ Γ r₁ r₂ R)
  rule＝→⊑-sat M Γ r₁ r₂ R (sat1 , _) s satΓ =
    lift (subst (λ x → x ≼ (⟦ r₂ ⟧ᵣ s)) (sym (lower (sat1 s satΓ))) ≼-refl)

-- Derived:
--
--    Γ ⊢[R] r₁ ＝ r    Γ ⊢[R] r ⊑ r₂
-- -----------------------------------
--            Γ ⊢[R] r₁ ⊑ r₂

rule＝-⊑-trans : (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ) → Rule
rule＝-⊑-trans Γ r₁ r r₂ R =
  rule (rseq Γ R (r₁ ＝ r) ∷ rseq Γ R (r ⊑ r₂) ∷ [])
       (rseq Γ R (r₁ ⊑ r₂))

abstract
  rule＝-⊑-trans-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ)
                      → sat-rule M (rule＝-⊑-trans Γ r₁ r r₂ R)
  rule＝-⊑-trans-sat M Γ r₁ r r₂ R (sat1 , sat2 , _) =
    rule⊑-trans-sat M Γ r₁ r r₂ R (rule＝→⊑-sat M Γ r₁ r R (sat1 , lift tt) , sat2 , lift tt)

-- Derived:
--
--    Γ ⊢[R] r₂ ⊑ r    Γ ⊢[R] r₁ ⊑ r
-- -----------------------------------
--            Γ ⊢[R] r₁ ⊑ r₂

rule＝-⊑-transR : (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ) → Rule
rule＝-⊑-transR Γ r₁ r r₂ R =
  rule (rseq Γ R (r₂ ＝ r) ∷ rseq Γ R (r₁ ⊑ r) ∷ [])
       (rseq Γ R (r₁ ⊑ r₂))

abstract
  rule＝-⊑-transR-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ)
                     → sat-rule M (rule＝-⊑-transR Γ r₁ r r₂ R)
  rule＝-⊑-transR-sat M Γ r₁ r r₂ R (sat1 , sat2 , _) =
    rule⊑-trans-sat M Γ r₁ r r₂ R
      (sat2 ,
       rule＝→⊑-sat M Γ r r₂ R (rule＝-sym-sat M Γ r r₂ R (sat1 , lift tt) , lift tt) ,
       lift tt)

--    Γ ⊢[R] r₁ ＝ r    Γ ⊢[R] r ＝ r₂
-- -----------------------------------
--            Γ ⊢[R] r₁ ＝ r₂

rule＝-trans : (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ) → Rule
rule＝-trans Γ r₁ r r₂ R =
  rule (rseq Γ R (r₁ ＝ r) ∷ rseq Γ R (r ＝ r₂) ∷ [])
       (rseq Γ R (r₁ ＝ r₂))

abstract
  rule＝-trans-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ)
                    → sat-rule M (rule＝-trans Γ r₁ r r₂ R)
  rule＝-trans-sat M Γ r₁ r r₂ R (sat1 , sat2 , _) s satΓ =
    lift (trans (lower (sat1 s satΓ)) (lower (sat2 s satΓ)))

--  Γ ⊢[r] r ⊑ r₁     Γ ⊢[r₁] A
-- ----------------------------
--         Γ ⊢[r] ◇ A

rule◇R : (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ) → Rule
rule◇R Γ r r₁ A =
  rule (rseq Γ r (r ⊑ r₁)
        ∷ rseq Γ r₁ A
        ∷ [])
    (rseq Γ r (◇ A))

-- TODO: prove this using the rules
abstract
  rule◇R-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (rule◇R Γ r r₁ A)
  rule◇R-sat M Γ r r₁ A (sat1 , sat2 , _) =
    ruleＵR-sat M Γ r r₁ ⊤· A (sat1 , sat2 , (λ s _ → lift tt) , lift tt)

--      Γ ⊢[r] r₁ ⊑ t
-- ----------------------
--   Γ ⊢[r₁] r₁ ⊑ r ⋆ t

derived-rule-⊑⋆ᵣ : (Γ : ℂ₀) (t r r₁ : ℂRes Γ) → Rule
derived-rule-⊑⋆ᵣ Γ t r r₁ =
  rule (rseq Γ r (r₁ ⊑ t) ∷ [])
       (rseq Γ r₁ (r₁ ⊑ (r ⋆ t)))

-- TODO: prove from the rules
abstract
  derived-rule-⊑⋆ᵣ-sat : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ)
                       → sat-rule M (derived-rule-⊑⋆ᵣ Γ t r r₁)
  derived-rule-⊑⋆ᵣ-sat M Γ t r r₁ (sat , _) s satΓ =
    lift (·-cong-≼-r₂ (⟦ r₁ ⟧ᵣ s) (⟦ t ⟧ᵣ s) (⟦ r ⟧ᵣ s ) (lower (sat s satΓ)))

--      Γ ⊢[r] r₁ ⊑ r
-- ----------------------
--   Γ ⊢[r₁] r₁ ⊑ r ⋆ t

derived-rule-⊑⋆ₗ : (Γ : ℂ₀) (t r r₁ : ℂRes Γ) → Rule
derived-rule-⊑⋆ₗ Γ t r r₁ =
  rule (rseq Γ r (r₁ ⊑ r) ∷ [])
       (rseq Γ r₁ (r₁ ⊑ (r ⋆ t)))

-- TODO: prove from the rules
abstract
  derived-rule-⊑⋆ₗ-sat : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ)
                       → sat-rule M (derived-rule-⊑⋆ₗ Γ t r r₁)
  derived-rule-⊑⋆ₗ-sat M Γ t r r₁ (sat , _) s satΓ =
    lift (·-cong-≼-r₁ (⟦ r₁ ⟧ᵣ s) (⟦ r ⟧ᵣ s) (⟦ t ⟧ᵣ s ) (lower (sat s satΓ)))

--    Γ ⊢[r] r ⊑ r₁    Γ ⊢[r] r₁ ⊑ r ⋆ t    Γ ⊢[r₁] A
-- ----------------------------------------------------
--                  Γ ⊢[r] ◇↓ t A

rule◇↓R : (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ) → Rule
rule◇↓R Γ t r r₁ A =
  rule (rseq Γ r (r ⊑ r₁)
        ∷ rseq Γ r (r₁ ⊑ r ⋆ t)
        ∷ rseq Γ r₁ A
        ∷ [])
    (rseq Γ r (◇↓ t A))

{--
abstract
  rule◇↓R-sat : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ)
              → sat-rule M (rule◇↓R Γ t r r₁ A)
  rule◇↓R-sat M Γ t r r₁ A (sat1 , sat2 , sat3 , _) s satΓ =
    (⟦ r₁ ⟧ᵣ· (M ≔ₛ s)) ,
    (𝕀 , ((lift 𝕀𝕀 , 𝕀𝕀𝕀) , λ _ _ _ → lift tt))
    where
    𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)) ≤ₜ (⟦ r₁ ⟧ᵣ· (M ≔ₛ s))
    𝕀 = lower (sat1 s satΓ)

    𝕀𝕀 : (⟦ r₁ ⟧ᵣ s)
      ≼ (⟦ r ⟧ᵣ s) · (⟦ ↑ᵣ₁ t ⟧ᵣ ((s ⹁ 𝕍ℝ ∶ (⟦ r ⟧ᵣ s)) ⹁ 𝕍ℝ ∶ (⟦ r₁ ⟧ᵣ s)))
    𝕀𝕀 = subst (λ x → (⟦ r₁ ⟧ᵣ s) ≼ (⟦ r ⟧ᵣ s) · x)
               (sym (⟦↑ᵣ₁⟧ᵣ t s 𝕍ℝ (⟦ r ⟧ᵣ s) 𝕍ℝ (⟦ r₁ ⟧ᵣ s)))
               (lower (sat2 s satΓ))

    𝕀𝕀𝕀 : ((((M ≔ₛ s) ≔ₜ (⟦ r₁ ⟧ᵣ s)) ≔r (⟦ r ⟧ᵣ s)) ≔r (⟦ r₁ ⟧ᵣ s)) ⊨ ↑₁ A
    𝕀𝕀𝕀 =
      →⊨-↑₁ {_} {((M ≔ₛ s) ≔ₜ (⟦ r₁ ⟧ᵣ s))} {A}
            {𝕍ℝ} (⟦ r ⟧ᵣ s) {𝕍ℝ} (⟦ r₁ ⟧ᵣ s)
            (sat3 s satΓ)
--}

-- This is another attempt at rule◇↓R-sat, where we don't go down to the semantics
-- of the operators but instead use existing rules to prove it - we don't break the
-- sat-sequent abstraction.
abstract
  rule◇↓R-sat : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ)
              → sat-rule M (rule◇↓R Γ t r r₁ A)
  rule◇↓R-sat M Γ t r r₁ A (sat1 , sat2 , sat3 , _) =
    𝕀
    where
    𝕀𝕍′ : sat-sequent M (rseq Γ r₁ ((r₁ ⊑ (r ⋆ t)) ∧· A))
    𝕀𝕍′ = rule∧I-sat
            M Γ (CEr r₁) (r₁ ⊑ (r ⋆ t)) A
            (sat2 , sat3 , lift tt)

    helper₀ : subℝ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A) r₁ ≡ (r₁ ⊑ (r ⋆ t)) ∧· A
    helper₀ = cong₂ _∧·_ (cong₂ _⊑_ refl (cong₂ _⋆_ (sub-Res-↑ᵣ₀ (ℂtxt Γ) 𝕍ℝ r₁ r) (sub-Res-↑ᵣ₀ (ℂtxt Γ) 𝕍ℝ r₁ t)))
                         (sub-↑₀ (ℂtxt Γ) 𝕍ℝ r₁ A)

    𝕀𝕍 : sat-sequent M (rseq Γ r₁ (subℝ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A) r₁))
    𝕀𝕍 = subst (λ z → sat-sequent M (rseq Γ r₁ z)) (sym helper₀) 𝕀𝕍′

    𝕀𝕀𝕀 : sat-sequent M (rseq Γ r₁ (Ｆ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A)))
    𝕀𝕀𝕀 = ruleＦR-sat
            M Γ r₁ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A)
            (𝕀𝕍 , lift tt)

    𝕀𝕀′ : sat-sequent M (rseq Γ r (◇ (Ｆ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A))))
    𝕀𝕀′ = rule◇R-sat
            M Γ r r₁ (Ｆ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A))
            (sat1 , 𝕀𝕀𝕀 , lift tt)

    s₁ : CSub ((ℂtxt Γ ، 𝕍ℝ) ، 𝕍ℝ) (ℂtxt Γ ، 𝕍ℝ)
    s₁ = CSub، 𝕍ℝ (CSub،ₗ r)

    helper₁ : ((sub-Res 𝕣₀ s₁) ⊑ ((sub-Res 𝕣₁ s₁) ⋆ (sub-Res (↑ᵣ₁ t) s₁))) ∧· sub (↑₁ A) s₁
            ≡ (𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A
    helper₁ = cong₂ _∧·_ (cong₂ _⊑_ refl (cong₂ _⋆_ refl (sub-Res-↑ᵣ₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r t))) (sub-↑₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r A)

    𝕀𝕀 : sat-sequent M (rseq Γ r (subℝ (◇ (Ｆ ((𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₁ t)) ∧· ↑₁ A))) r))
    𝕀𝕀 = subst (λ x → sat-sequent M (rseq Γ r (◇ (Ｆ x)))) (sym helper₁) 𝕀𝕀′

    𝕀 : sat-sequent M (rseq Γ r (◇↓ t A))
    𝕀 = ruleＦR-sat
          M Γ r (◇ (Ｆ ((𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₁ t)) ∧· ↑₁ A)))
          (𝕀𝕀 , lift tt)

-- Derived rule:
--   Γ, x:ℝ, r ⊑ x, A@x ⊢[T] C
-- -----------------------------
--      Γ,(◇ A)@r ⊢[T] C

rule◇L : (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule◇L Γ r T A C =
  rule (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ A) 𝕣₀)
            (↑ᵣ₀ T)
            (↑₀ C)
        ∷ [])
       (rseq (ℂe Γ (◇ A) r) T C)

abstract
  rule◇L-sat : (M : Model₀) (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ)
             → sat-rule M (rule◇L Γ r T A C)
  rule◇L-sat M Γ r T A C (sat1 , _) =
    ruleＵL-sat M Γ T r ⊤· A C
      (rule-thin-sat M (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ A) 𝕣₀) (↑₀ ⊤·) (CEi ［ ↑ᵣ₀ r , 𝕣₀ ）) (CEr (↑ᵣ₀ T)) (↑₀ C)
         (sat1 , lift tt) ,
       lift tt)


-- Derived rule:
--   Γ, x:ℝ, r ⊑ x, x ⊑ r ⋆ t, A@x ⊢[T] C
-- ----------------------------------------
--          Γ,(◇↓ t A)@r ⊢[T] C

rule◇↓L : (Γ : ℂ₀) (t r T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule◇↓L Γ t r T A C =
  rule (rseq (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) (↑₀ A) 𝕣₀)
            (↑ᵣ₀ T)
            (↑₀ C)
        ∷ [])
       (rseq (ℂe Γ (◇↓ t A) r) T C)

abstract
  rule◇↓L-sat : (M : Model₀) (Γ : ℂ₀) (t r T : ℂRes Γ) (A C : ℂForm Γ)
              → sat-rule M (rule◇↓L Γ t r T A C)
  rule◇↓L-sat M Γ t r T A C (sat1 , _) =
    ruleＦL-sat
      M Γ r (CEr T) (◇ (Ｆ ((𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₁ t)) ∧· ↑₁ A))) C
      (𝕀 , lift tt)
    where
    𝕀𝕍 : sat-sequent M (rseq (ℂe (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) 𝕣₀) (↑₀ A) 𝕣₀) (↑ᵣ₀ T) (↑₀ C))
    𝕀𝕍 = ruleLE′-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (ℂe ℂ⟨⟩ (↑₀ A) 𝕣₀) 𝕣₀ 𝕣₀ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t) LE (↑ᵣ₀ T) (↑₀ C) (sat1 , (lift tt))

    𝕀𝕀𝕀′ : sat-sequent M (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A) 𝕣₀) (↑ᵣ₀ T) (↑₀ C))
    𝕀𝕀𝕀′ = rule∧E-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (CEr (↑ᵣ₀ T)) (CEr 𝕣₀) (𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) (↑₀ A) (↑₀ C) (𝕀𝕍 , lift tt)

    helper₀ : subℝ (↑₀، ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A)) 𝕣₀
            ≡ (𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A
    helper₀ =
      trans (cong₃ (λ x y z → (𝕣₀ ⊑ (sub-Resℝ x 𝕣₀ ⋆ sub-Resℝ y 𝕣₀)) ∧· subℝ z 𝕣₀) (↑ᵣ₀،-↑ᵣ₀ r) (↑ᵣ₀،-↑ᵣ₀ t) (↑₀،-↑₀ A))
            (cong₃ (λ x y z → (𝕣₀ ⊑ (x ⋆ y)) ∧· z)
                   (sub-Res-↑ᵣ₁ (ℂtxt Γ) _ _ _ r)
                   (sub-Res-↑ᵣ₁ (ℂtxt Γ) _ _ _ t)
                   (sub-↑₁ (ℂtxt Γ) _ _ _ A))

    𝕀𝕀𝕀 : sat-sequent M (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (subℝ (↑₀، ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A)) 𝕣₀) 𝕣₀) (↑ᵣ₀ T) (↑₀ C))
    𝕀𝕀𝕀 = subst (λ x → sat-sequent M (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) x 𝕣₀) (↑ᵣ₀ T) (↑₀ C)))
                (sym helper₀) 𝕀𝕀𝕀′

    𝕀𝕀 : sat-sequent M (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ (Ｆ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A))) 𝕣₀) (↑ᵣ₀ T) (↑₀ C))
    𝕀𝕀 = ruleＦL-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕣₀ (CEr (↑ᵣ₀ T)) (↑₀، ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A)) (↑₀ C) (𝕀𝕀𝕀 , lift tt)

    𝕀′ : sat-sequent M (rseq (ℂe Γ (◇ (Ｆ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A))) r) T C)
    𝕀′ = rule◇L-sat M Γ r T (Ｆ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A)) C (𝕀𝕀 , lift tt)

    s₁ : CSub ((ℂtxt Γ ، 𝕍ℝ) ، 𝕍ℝ) (ℂtxt Γ ، 𝕍ℝ)
    s₁ = CSub، 𝕍ℝ (CSub،ₗ r)

    helper₁ : ((sub-Res 𝕣₀ s₁) ⊑ ((sub-Res 𝕣₁ s₁) ⋆ (sub-Res (↑ᵣ₁ t) s₁))) ∧· sub (↑₁ A) s₁
            ≡ (𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A
    helper₁ = cong₂ _∧·_ (cong₂ _⊑_ refl (cong₂ _⋆_ refl (sub-Res-↑ᵣ₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r t))) (sub-↑₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r A)

    𝕀 : sat-sequent M (rseq (ℂe Γ (subℝ (◇ (Ｆ ((𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₁ t)) ∧· ↑₁ A))) r) r) T C)
    𝕀 = subst (λ x → sat-sequent M (rseq (ℂe Γ (◇ (Ｆ x)) r) T C)) (sym helper₁) 𝕀′

--    Γ, x : ℝ, T ⊑ x ⊢[x] A
-- ---------------------------
--        Γ ⊢[T] □ A

rule□R : (Γ : ℂ₀) (T : ℂRes Γ) (A : ℂForm Γ) → Rule
rule□R Γ T A =
  rule [ rseq (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (↑₀ A) ]
       (rseq Γ T (□ A))

abstract
  rule□R-sat : (M : Model₀) (Γ : ℂ₀) (T : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (rule□R Γ T A)
  rule□R-sat M Γ T A (sat1 , _) =
    rule¬I-sat M Γ T (◇ (¬· A))
      (rule◇L-sat M Γ T T (¬· A) ⊥·  -- use rule◇L-sat
        (rule¬E-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) ℂ⟨⟩ 𝕣₀ (↑₀ A) (CEr (↑ᵣ₀ T)) (↑₀ ⊥·)  -- use rule¬E-sat to move the ¬ A to the conclusion
          (𝕀 , lift tt) -- then use the assumption
        , (lift tt)) ,
       lift tt)
   where
   𝕀 : sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (↑ ⊆-refl (↑₀ A)))
   𝕀 = subst (λ x → sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ x)) (sym (↑⊆-refl (↑₀ A))) sat1

--
-- ------------------
--    Γ ⊢[R] 𝟎 ⊑ r

rule𝟎min : (Γ : ℂ₀) (R r : ℂRes Γ) → Rule
rule𝟎min Γ R r =
  rule [] (rseq Γ R (𝟎 ⊑ r))

abstract
  rule𝟎min-sat : (M : Model₀) (Γ : ℂ₀) (R r : ℂRes Γ)
               → sat-rule M (rule𝟎min Γ R r)
  rule𝟎min-sat M Γ R r _ s satΓ = lift 𝟘≼

--
-- -----------------------
--    Γ ⊢[R] 𝟎 ⋆ t ＝ t

rule-left-id : (Γ : ℂ₀) (R t : ℂRes Γ) → Rule
rule-left-id Γ R t =
  rule [] (rseq Γ R (𝟎 ⋆ t ＝ t))

abstract
  rule-left-id-sat : (M : Model₀) (Γ : ℂ₀) (R t : ℂRes Γ)
                   → sat-rule M (rule-left-id Γ R t)
  rule-left-id-sat M Γ R t _ s satΓ = lift ·-left-id

-- Derived rule:
--   Γ, x:ℝ, x ⊑ r, A@x ⊢[T] C
-- -----------------------------
--      Γ,(◆ A)@r ⊢[T] C

rule◆L : (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule◆L Γ r T A C =
  rule (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ r)) (↑₀ A) 𝕣₀)
            (↑ᵣ₀ T)
            (↑₀ C)
        ∷ [])
       (rseq (ℂe Γ (◆ A) r) T C)

abstract
  rule◆L-sat : (M : Model₀) (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ)
             → sat-rule M (rule◆L Γ r T A C)
  rule◆L-sat M Γ r T A C (sat1 , _) =
    ruleＳL-sat M Γ T r ⊤· A C
      (rule-thin-sat M (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ r)) (↑₀ A) 𝕣₀) (↑₀ ⊤·) (CEi （ 𝕣₀ , ↑ᵣ₀ r ］) (CEr (↑ᵣ₀ T)) (↑₀ C)
         (sat1 , lift tt) ,
       lift tt)

-- Derived:
--
--  Γ ⊢[r] r₁ ⊑ r     Γ ⊢[r₁] A
-- ----------------------------
--         Γ ⊢[r] ◆ A

rule◆R : (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ) → Rule
rule◆R Γ r r₁ A =
  rule (rseq Γ r (r₁ ⊑ r)
        ∷ rseq Γ r₁ A
        ∷ [])
    (rseq Γ r (◆ A))

abstract
  rule◆R-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (rule◆R Γ r r₁ A)
  rule◆R-sat M Γ r r₁ A (sat1 , sat2 , _) =
    ruleＳR-sat M Γ r r₁ ⊤· A (sat1 , sat2 , (λ _ _ → lift tt) , lift tt)

--    Γ ⊢[r] A
-- --------------
--   Γ ⊢[r] ◆ A

rule◆R-now : (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ) → Rule
rule◆R-now Γ r A =
  rule [ rseq Γ r A ]
       (rseq Γ r (◆ A))

abstract
  rule◆R-now-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ)
                 → sat-rule M (rule◆R-now Γ r A)
  rule◆R-now-sat M Γ r A (sat1 , _) =
    rule◆R-sat M Γ r r A (rule⊑-refl-sat M Γ r r (lift tt) , sat1 , lift tt)

--    Γ, x : ℝ, x ⊑ T ⊢[x] A
-- ---------------------------
--        Γ ⊢[T] ■ A

rule■R : (Γ : ℂ₀) (T : ℂRes Γ) (A : ℂForm Γ) → Rule
rule■R Γ T A =
  rule [ rseq (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ T)) 𝕣₀ (↑₀ A) ]
       (rseq Γ T (■ A))

abstract
  rule■R-sat : (M : Model₀) (Γ : ℂ₀) (T : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (rule■R Γ T A)
  rule■R-sat M Γ T A (sat1 , _) =
    rule¬I-sat M Γ T (◆ (¬· A))
      (rule◆L-sat M Γ T T (¬· A) ⊥·  -- use rule◇L-sat
        (rule¬E-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ T)) ℂ⟨⟩ 𝕣₀ (↑₀ A) (CEr (↑ᵣ₀ T)) (↑₀ ⊥·)  -- use rule¬E-sat to move the ¬ A to the conclusion
          (𝕀 , lift tt) -- then use the assumption
        , (lift tt)) ,
       lift tt)
   where
   𝕀 : sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ T)) 𝕣₀ (↑ ⊆-refl (↑₀ A)))
   𝕀 = subst (λ x → sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ T)) 𝕣₀ x)) (sym (↑⊆-refl (↑₀ A))) sat1


-- Either t is 0 or there is a variable less than 0:
--
--    Γ, t ＝ 0 ⊢[R] C    Γ, x:ℝ, x ⊏ t ⊢[R] C
-- ---------------------------------------------------
--                 Γ ⊢[R] C

splitLℝ : (Γ : ℂ₀) (t R : ℂRes Γ) (C : ℂForm Γ) → Rule
splitLℝ Γ t R C =
  rule (rseq (ℂu Γ (t ＝ 𝟎)) R C ∷ rseq (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊏ ↑ᵣ₀ t)) (↑ᵣ₀ R) (↑₀ C) ∷ [])
       (rseq Γ R C)

abstract
  splitLℝ-sat : (M : Model₀) (Γ : ℂ₀) (t R : ℂRes Γ) (C : ℂForm Γ)
              → sat-rule M (splitLℝ Γ t R C)
  splitLℝ-sat M Γ t R C (sat1 , sat2 , _) s satΓ with 𝟘⊎◃ (⟦ t ⟧ᵣ s)
  ... | inj₁ p = sat1 s (satΓ , lift p)
  ... | inj₂ (w , c) =
    ⊨-↑₀→ {_} {(M ≔ₛ s) ≔ₜ (⟦ R ⟧ᵣ s)} {C} {𝕍ℝ} w 𝕀
    where
    𝕀𝕀 : (((M ≔ₛ s) ≔⟨ 𝕍ℝ ⟩ w) ≔ₜ (⟦ ↑ᵣ₀ R ⟧ᵣ (s ⹁ 𝕍ℝ ∶ w))) ⊨ ↑₀ C
    𝕀𝕀 = sat2 (s ⹁ 𝕍ℝ ∶ w) (satΓ , lift (◃→≺ (subst (λ x → w ◃ x) (sym (⟦↑ᵣ₀⟧ᵣ t s 𝕍ℝ w)) c)))

    𝕀 : (((M ≔ₛ s) ≔ₜ (⟦ R ⟧ᵣ s)) ≔⟨ 𝕍ℝ ⟩ w) ⊨ ↑₀ C
    𝕀 = subst (λ x → (((M ≔ₛ s) ≔ₜ x) ≔⟨ 𝕍ℝ ⟩ w) ⊨ ↑₀ C) (⟦↑ᵣ₀⟧ᵣ R s 𝕍ℝ w) 𝕀𝕀

-- Derived:
--
--      Γ ⊢[r] A
-- ------------------
--    Γ ⊢[r] ◇↓ t A

rule◇↓R-now : (Γ : ℂ₀) (t r : ℂRes Γ) (A : ℂForm Γ) → Rule
rule◇↓R-now Γ t r A =
  rule [ rseq Γ r A ]
       (rseq Γ r (◇↓ t A))

abstract
  rule◇↓R-now-sat : (M : Model₀) (Γ : ℂ₀) (t r : ℂRes Γ) (A : ℂForm Γ)
                  → sat-rule M (rule◇↓R-now Γ t r A)
  rule◇↓R-now-sat M Γ t r A (sat1 , _) =
    rule◇↓R-sat M Γ t r r A
      (rule⊑-refl-sat M Γ r r (lift tt) ,
       derived-rule-⊑⋆ₗ-sat M Γ t r r (rule⊑-refl-sat M Γ r r (lift tt) , lift tt) ,
       sat1 ,
       lift tt)

-- Derived:
--
--       Γ ⊢[R] A
-- -------------------
--    Γ ⊢[R] ◇↓◆ r A

◇↓◆-now : (Γ : ℂ₀) (R r : ℂRes Γ) (A : ℂForm Γ) → Rule
◇↓◆-now Γ R r A =
  rule [ rseq Γ R A ]
       (rseq Γ R (◇↓◆ r A))

abstract
  ◇↓◆-now-sat : (M : Model₀) (Γ : ℂ₀) (R r : ℂRes Γ) (A : ℂForm Γ)
              → sat-rule M (◇↓◆-now Γ R r A)
  ◇↓◆-now-sat M Γ R r A (sat1 , _) =
    rule◇↓R-now-sat M Γ r R (◆ A)
      (rule◆R-now-sat M Γ R A (sat1 , lift tt) , lift tt)

-- Derived:
--
-- -------------------------------
--    Γ, (◇↓◆ r A) @ 𝟎 ⊢[𝟎] ◇↓ A

◇↓◆𝟎→◇↓ : (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ) → Rule
◇↓◆𝟎→◇↓ Γ r A =
  rule [] (rseq (ℂe Γ (◇↓◆ r A) 𝟎) 𝟎 (◇↓ r A))

◇↓◆𝟎→◇↓-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ)
            → sat-rule M (◇↓◆𝟎→◇↓ Γ r A)
◇↓◆𝟎→◇↓-sat M Γ r A _ =
  rule◇↓L-sat M Γ r 𝟎 𝟎 (◆ A) (◇↓ r A)
    (rule◆L-sat
      M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (𝟎 ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (𝟎 ⋆ r))) 𝕣₀ 𝟎 (↑₀ A) (↑₀ (◇↓ r A))
      (ℍ₁ , lift tt) , lift tt)
  where
  Γ₀ : ℂ₀
  Γ₀ = ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (𝟎 ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (𝟎 ⋆ r))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁)

  Γ₁ : ℂ₀
  Γ₁ = ℂe Γ₀ (↑₀ (↑₀ A)) 𝕣₀

  ℍ₂ : sat-sequent M (rseq Γ₁ 𝟎 (𝕣₀ ⊑ (𝟎 ⋆ ↑ᵣ₀ (↑ᵣ₀ r))))
  ℍ₂ = rule⊑-trans-sat M Γ₁ 𝕣₀ 𝕣₁ (𝟎 ⋆ ↑ᵣ₀ (↑ᵣ₀ r)) 𝟎
         (rule-thin-sat M Γ₀ (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr 𝟎) (𝕣₀ ⊑ 𝕣₁)
           (rule-id-comp-u-sat M (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (𝟎 ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (𝟎 ⋆ r))) 𝕍ℝ) (CEr 𝟎) 𝕣₀ 𝕣₁ LE (lift tt) ,
            lift tt) ,
          rule-thin-sat M Γ₀ (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr 𝟎) (𝕣₁ ⊑ 𝟎 ⋆ ↑ᵣ₀ (↑ᵣ₀ r))
            (rule-thin-sat M (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (𝟎 ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (𝟎 ⋆ r))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁) CEu (CEr 𝟎) (𝕣₁ ⊑ 𝟎 ⋆ ↑ᵣ₀ (↑ᵣ₀ r))
              (rule-thin-v-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (𝟎 ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (𝟎 ⋆ r))) 𝕍ℝ 𝟎 (𝕣₀ ⊑ 𝟎 ⋆ ↑ᵣ₀ r)
                (rule-id-comp-u-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝟎 ⊑ 𝕣₀)) (CEr 𝟎) 𝕣₀ (↑ᵣ₀ (𝟎 ⋆ r)) LE (lift tt) , lift tt) ,
               lift tt) ,
             lift tt) ,
          lift tt)

  ℍ₁ : sat-sequent M (rseq Γ₁ 𝟎 (↑₀ (↑₀ (◇↓ r A))))
  ℍ₁ = subst (λ x → sat-sequent M (rseq Γ₁ 𝟎 (↑₀ x)))
             (sym (↑◇↓ ⊆₀ r A))
             (subst (λ x → sat-sequent M (rseq Γ₁ 𝟎 x))
                    (sym (↑◇↓ ⊆₀ (↑ᵣ₀ r) (↑₀ A)))
                    (rule◇↓R-sat M Γ₁ (↑ᵣ₀ (↑ᵣ₀ r)) 𝟎 𝕣₀ (↑₀ (↑₀ A))
                      (rule𝟎min-sat M Γ₁ 𝟎 𝕣₀ (lift tt) ,
                       ℍ₂ ,
                       ruleLbl-sat M Γ₀ (CEr 𝕣₀) (↑₀ (↑₀ A)) (lift tt) ,
                       lift tt)))

--    Γ ⊢[r₂] A    Γ ⊢[r] r₁ ＝ r₂
-- ---------------------------------
--          Γ ⊢[r₁] A

replace-resource : (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ) (A : ℂForm Γ) → Rule
replace-resource Γ r r₁ r₂ A =
  rule (rseq Γ r₂ A ∷ rseq Γ r (r₁ ＝ r₂) ∷ [])
       (rseq Γ r₁ A)

abstract
  replace-resource-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ) (A : ℂForm Γ)
                       → sat-rule M (replace-resource Γ r r₁ r₂ A)
  replace-resource-sat M Γ r r₁ r₂ A (sat1 , sat2 , _) s satΓ =
    subst (λ x → ((M ≔ₛ s) ≔ₜ x) ⊨ A) (sym (lower (sat2 s satΓ))) (sat1 s satΓ)

--    Γ, A@r₂ ⊢[r] C    Γ ⊢[r] r₁ ＝ r₂
-- ---------------------------------
--          Γ, A@r₁ ⊢[r] C

replace-resource-hyp : (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ) (A C : ℂForm Γ) → Rule
replace-resource-hyp Γ r r₁ r₂ A C =
  rule (rseq (ℂe Γ A r₂) r C ∷ rseq Γ r (r₁ ＝ r₂) ∷ [])
       (rseq (ℂe Γ A r₁) r C)

abstract
  replace-resource-hyp-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ) (A C : ℂForm Γ)
                           → sat-rule M (replace-resource-hyp Γ r r₁ r₂ A C)
  replace-resource-hyp-sat M Γ r r₁ r₂ A C (sat1 , sat2 , _) s (satΓ , satA) =
    sat1 s (satΓ , subst (λ x → ((M ≔ₛ s) ≔ₜ x) ⊨ A) (lower (sat2 s satΓ)) satA)

--   Γ ⊢[T] r₁ ⊏ r₂
-- ------------------
--   Γ ⊢[T] r₁ ⊑ r₂

⊏→⊑ : (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ) → Rule
⊏→⊑ Γ r₁ r₂ R =
  rule [ rseq Γ R (r₁ ⊏ r₂) ]
       (rseq Γ R (r₁ ⊑ r₂))

abstract
  ⊏→⊑-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ)
          → sat-rule M (⊏→⊑ Γ r₁ r₂ R)
  ⊏→⊑-sat M Γ r₁ r₂ R (sat1 , _) s satΓ =
    lift (≺→≼ (lower (sat1 s satΓ)))

-- Derived:
--
--   Γ ⊢[r] A      Γ ⊢[R] r ⊑ R ⋆ t
-- ----------------------------------
--          Γ ⊢[R] ◇↓◆ t A

◇↓◆R : (Γ : ℂ₀) (R r t : ℂRes Γ) (A : ℂForm Γ) → Rule
◇↓◆R Γ R r t A =
  rule (rseq Γ r A ∷ rseq Γ R (r ⊑ R ⋆ t) ∷ [])
       (rseq Γ R (◇↓◆ t A))

abstract
  ◇↓◆R-sat : (M : Model₀) (Γ : ℂ₀) (R r t : ℂRes Γ) (A : ℂForm Γ)
           → sat-rule M (◇↓◆R Γ R r t A)
  ◇↓◆R-sat M Γ R r t A (sat1 , sat2 , _) =
    rule◇↓R-sat M Γ t R (R ⋆ t) (◆ A)
      (derived-rule-⊑⋆ₗ-sat M Γ t R R (rule⊑-refl-sat M Γ R R (lift tt) , lift tt) ,
       rule⊑-refl-sat M Γ (R ⋆ t) R (lift tt) ,
       rule◆R-sat M Γ (R ⋆ t) r A
         (rule-comp-change-resources-sat M Γ (R ⋆ t) R r (R ⋆ t) LE
           (sat2 , lift tt) ,
          sat1 ,
          lift tt) ,
       lift tt)

-- Derived rule:
--   Γ, x:ℝ, x ⊑ r ⋆ t, A@x ⊢[T] C
-- ---------------------------------
--      Γ,(◇↓◆ t A)@r ⊢[T] C

rule◇↓◆L : (Γ : ℂ₀) (t r T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule◇↓◆L Γ t r T A C =
  rule (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) (↑₀ A) 𝕣₀)
            (↑ᵣ₀ T)
            (↑₀ C)
        ∷ [])
       (rseq (ℂe Γ (◇↓◆ t A) r) T C)

abstract
  rule◇↓◆L-sat : (M : Model₀) (Γ : ℂ₀) (t r T : ℂRes Γ) (A C : ℂForm Γ)
               → sat-rule M (rule◇↓◆L Γ t r T A C)
  rule◇↓◆L-sat M Γ t r T A C (sat1 , _) =
    rule◇↓L-sat M Γ t r T (◆ A) C
      (rule◆L-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕣₀
        (↑ᵣ₀ T) (↑₀ A) (↑₀ C)
        (rule-cut-u-sat M
          (ℂe (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁)) (↑₀ (↑₀ A)) 𝕣₀)
          (↑ᵣ₀ (↑ᵣ₀ T)) 𝕣₁ (↑₀ (↑₀ C)) 𝕣₀ (↑ᵣ₀ (↑ᵣ₀ (r ⋆ t))) LE
          (rule⊑-trans-sat M
            (ℂe (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁)) (↑₀ (↑₀ A)) 𝕣₀)
            𝕣₀ 𝕣₁ (↑ᵣ₀ (↑ᵣ₀ (r ⋆ t))) 𝕣₁
            (rule-thin-sat M
              (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁))
              (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr 𝕣₁) (𝕣₀ ⊑ 𝕣₁)
              (rule-id-comp-u-sat M (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ) (CEr 𝕣₁) 𝕣₀ 𝕣₁ LE (lift tt) ,
               lift tt) ,
             rule-thin-sat M
              (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁))
              (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr 𝕣₁) (𝕣₁ ⊑ ↑ᵣ₀ (↑ᵣ₀ (r ⋆ t)))
              (rule-thin-sat M
                (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ)
                (𝕣₀ ⊑ 𝕣₁) CEu (CEr 𝕣₁) (𝕣₁ ⊑ ↑ᵣ₀ (↑ᵣ₀ (r ⋆ t)))
                (rule-thin-v-sat M
                  (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ 𝕣₀
                  (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))
                  (rule-id-comp-u-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (CEr 𝕣₀) 𝕣₀ (↑ᵣ₀ (r ⋆ t)) LE (lift tt) , lift tt) ,
                 lift tt) ,
               lift tt) ,
             lift tt) ,
           rule-thin-gen-sat M
            (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t))) 𝕍ℝ)
            (ℂu (ℂe ℂ⟨⟩ (↑₀ (↑₀ A)) 𝕣₀) (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (r ⋆ t))))
            (𝕣₀ ⊑ 𝕣₁) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ T))) (↑₀ (↑₀ C))
            (rule-thin-gen-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀))
              (ℂu (ℂe (ℂv ℂ⟨⟩ 𝕍ℝ) (↑₀ (↑₀ A)) 𝕣₀) (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (r ⋆ t))))
              (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t)) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ T))) (↑₀ (↑₀ C))
              (rule-thin-gen-sat M (ℂv Γ 𝕍ℝ)
                (ℂu (ℂe (ℂv ℂ⟨⟩ 𝕍ℝ) (↑₀ (↑₀ A)) 𝕣₀) (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (r ⋆ t))))
                (↑ᵣ₀ r ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ T))) (↑₀ (↑₀ C))
                (h₁ ,
                 lift tt) , lift tt) , lift tt) , lift tt) , lift tt) , lift tt)
    where
    h₁ : sat-sequent M (rseq (ℂx (ℂx (ℂv (ℂv Γ 𝕍ℝ) 𝕍ℝ) (↑₀ (↑₀ A)) (CEr 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (r ⋆ t))) CEu) (↑ᵣ₀ (↑ᵣ₀ T)) (↑₀ (↑₀ C)))
    h₁ = subst₄ (λ x y z w → sat-sequent M (rseq (ℂx (ℂx (ℂv (ℂv Γ 𝕍ℝ) 𝕍ℝ) x (CEr 𝕣₀)) (𝕣₀ ⊑ y) CEu) z w))
                (↑₀،↑₀ A) (↑ᵣ₀،↑ᵣ₀ (r ⋆ t))
                (↑ᵣ₀،↑ᵣ₀ T) (↑₀،↑₀ C)
                (rule-thin-v-v11-sat M Γ 𝕍ℝ 𝕍ℝ (↑ᵣ₀ T) (↑₀ C) (↑₀ A) (𝕣₀ ⊑ (↑ᵣ₀ (r ⋆ t))) (CEr 𝕣₀) CEu
                  (rule-swap-sat M (ℂv Γ 𝕍ℝ) (↑₀ A) (𝕣₀ ⊑ ↑ᵣ₀ (r ⋆ t)) (CEr 𝕣₀) CEu (CEr (↑ᵣ₀ T)) (↑₀ C)
                    (sat1 , lift tt) ,
                   lift tt))

{--
--    Γ ⊢[r] A     Γ ⊢[R] r ◁ R
-- ------------------------------
--         Γ ⊢[R] Ｙ A

rule-ＹR : (Γ : ℂ₀) (r R : ℂRes Γ) (A : ℂForm Γ) → Rule
rule-ＹR Γ r R A =
  rule (rseq Γ r A ∷ rseq Γ R (r ◁ R) ∷ [])
       (rseq Γ R (Ｙ A))

abstract
  rule-ＹR-sat : (M : Model₀) (Γ : ℂ₀) (r R : ℂRes Γ) (A : ℂForm Γ)
              → sat-rule M (rule-ＹR Γ r R A)
  rule-ＹR-sat M Γ r R A (sat1 , sat2 , _) s satΓ = ⟦ r ⟧ᵣ s , lower (sat2 s satΓ) , (sat1 s satΓ)
--}


--    Γ, x : ℝ, r₁ ⊑ x, x ◁ r₂ ⊢[r] A
-- -------------------------------------
--         Γ, r₁ ⊏ r₂ ⊢[R] A

⊏Lᵣ : (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ) (A : ℂForm Γ) → Rule
⊏Lᵣ Γ r₁ r₂ R A =
  rule (rseq (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r₁ ⊑ 𝕣₀)) (𝕣₀ ◁ ↑ᵣ₀ r₂)) (↑ᵣ₀ R) (↑₀ A) ∷ [])
       (rseq (ℂu Γ (r₁ ⊏ r₂)) R A)

abstract
  ⊏Lᵣ-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ R : ℂRes Γ) (A : ℂForm Γ)
          → sat-rule M (⊏Lᵣ Γ r₁ r₂ R A)
  ⊏Lᵣ-sat M Γ r₁ r₂ R A (sat1 , _) s (satΓ , satLE) with ≺⇒◃ᵣ (⟦ r₁ ⟧ᵣ s) (⟦ r₂ ⟧ᵣ s) (lower satLE)
  ... | w , c₁ , c₂ =
    ⊨-↑₀→ {_} {(M ≔ₛ s) ≔ₜ (⟦ R ⟧ᵣ s)} {A} {𝕍ℝ} w
          (subst (λ x → (((M ≔ₛ s) ≔ₜ x) ≔ w) ⊨ ↑₀ A)
                 (⟦↑ᵣ₀⟧ᵣ R s 𝕍ℝ w)
                 (sat1 (s ⹁ 𝕍ℝ ∶ w) ((satΓ , lift (subst (_≼ w) (sym (⟦↑ᵣ₀⟧ᵣ r₁ s 𝕍ℝ w)) c₁)) ,
                                     lift (subst (w ◃_) (sym (⟦↑ᵣ₀⟧ᵣ r₂ s 𝕍ℝ w)) c₂))))

-- Derived:
--
--    Γ ⊢[r] A     Γ ⊢[R] r ⊏ R
-- ------------------------------
--         Γ ⊢[R] ◆· A

◆·R : (Γ : ℂ₀) (r R : ℂRes Γ) (A : ℂForm Γ) → Rule
◆·R Γ r R A =
  rule (rseq Γ r A ∷ rseq Γ R (r ⊏ R) ∷ [])
       (rseq Γ R (◆· A))

abstract
  ◆·R-sat : (M : Model₀) (Γ : ℂ₀) (r R : ℂRes Γ) (A : ℂForm Γ)
          → sat-rule M (◆·R Γ r R A)
  ◆·R-sat M Γ r R A (sat1 , sat2 , _) =
    rule-cut-sat M Γ (CEr R) (CEr R) (◆· A) (r ⊏ R)
      (sat2 ,
       ⊏Lᵣ-sat M Γ r R R (◆· A)
         (ruleＹR-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ◁ ↑ᵣ₀ R)) (↑ᵣ₀ R) 𝕣₀ (↑₀ (◆ A))
           (rule-id-comp-u-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (CEr (↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ R) PR (lift tt) ,
            rule◆R-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ◁ ↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ r) (↑₀ A)
             (rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ◁ ↑ᵣ₀ R) CEu (CEr 𝕣₀) (↑ᵣ₀ r ⊑ 𝕣₀)
               (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr 𝕣₀) (↑ᵣ₀ r) 𝕣₀ LE (lift tt) , lift tt) ,
              rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ◁ ↑ᵣ₀ R) CEu (CEr (↑ᵣ₀ r)) (↑₀ A)
                (rule-thin-sat M (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ r)) (↑₀ A)
                  (rule-thin-v-sat M Γ 𝕍ℝ r A (sat1 , lift tt) , lift tt) , lift tt) ,
              lift tt) ,
            lift tt) , lift tt) ,
       lift tt)

--    Γ, x : ℝ, A@x, x ◁ r ⊢[R] C
-- --------------------------------
--         Γ, (Ｙ A)@r ⊢[R] C

ＹL : (Γ : ℂ₀) (r R : ℂRes Γ) (A C : ℂForm Γ) → Rule
ＹL Γ r R A C =
  rule (rseq (ℂu (ℂe (ℂv Γ 𝕍ℝ) (↑₀ A) 𝕣₀) (𝕣₀ ◁ ↑ᵣ₀ r)) (↑ᵣ₀ R) (↑₀ C) ∷ [])
       (rseq (ℂe Γ (Ｙ A) r) R C)

abstract
  ＹL-sat : (M : Model₀) (Γ : ℂ₀) (r R : ℂRes Γ) (A C : ℂForm Γ)
          → sat-rule M (ＹL Γ r R A C)
  ＹL-sat M Γ r R A C (sat1 , _) s (satΓ , t , c , satA) =
    ⊨-↑₀→ {_} {(M ≔ₛ s) ≔ₜ (⟦ R ⟧ᵣ s)} {C} {𝕍ℝ} t
          (subst (λ x → (((M ≔ₛ s) ≔ₜ x) ≔ t) ⊨ ↑₀ C)
                 (⟦↑ᵣ₀⟧ᵣ R s 𝕍ℝ t)
                 (sat1 (s ⹁ 𝕍ℝ ∶ t)
                       ((satΓ , →⊨-↑₀ {_} {(M ≔ₛ s) ≔ₜ t} {A} {𝕍ℝ} t satA) ,
                        (lift (subst (t ◃_) (sym (⟦↑ᵣ₀⟧ᵣ r s 𝕍ℝ t)) c)))))

--    Γ ⊢ᵣ r₁ ◁ r₂
-- -----------------
--    Γ ⊢ᵣ r₁ ⊑ r₂

◁⇒⊑ : (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ) → Rule
◁⇒⊑ Γ r r₁ r₂ =
  rule (rseq Γ r (r₁ ◁ r₂) ∷ [])
       (rseq Γ r (r₁ ⊑ r₂))

abstract
  ◁⇒⊑-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ)
          → sat-rule M (◁⇒⊑ Γ r r₁ r₂)
  ◁⇒⊑-sat M Γ r r₁ r₂ (satR , _) s satΓ =
    lift (◃→≼ (lower (satR s satΓ)))

--    Γ ⊢ᵣ r₁ ◁ r₂
-- -----------------
--    Γ ⊢ᵣ r₁ ⊏ r₂

◁⇒⊏ : (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ) → Rule
◁⇒⊏ Γ r r₁ r₂ =
  rule (rseq Γ r (r₁ ◁ r₂) ∷ [])
       (rseq Γ r (r₁ ⊏ r₂))

abstract
  ◁⇒⊏-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ r₂ : ℂRes Γ)
          → sat-rule M (◁⇒⊏ Γ r r₁ r₂)
  ◁⇒⊏-sat M Γ r r₁ r₂ (satR , _) s satΓ =
    lift (◃→≺ (lower (satR s satΓ)))

-- Derived:
--
--    Γ, x : ℝ, A@x, x ⊏ r ⊢[R] C
-- --------------------------------
--         Γ, (◆· A)@r ⊢[R] C

◆·L : (Γ : ℂ₀) (r R : ℂRes Γ) (A C : ℂForm Γ) → Rule
◆·L Γ r R A C =
  rule (rseq (ℂu (ℂe (ℂv Γ 𝕍ℝ) (↑₀ A) 𝕣₀) (𝕣₀ ⊏ ↑ᵣ₀ r)) (↑ᵣ₀ R) (↑₀ C) ∷ [])
       (rseq (ℂe Γ (◆· A) r) R C)

abstract
  ◆·L-sat : (M : Model₀) (Γ : ℂ₀) (r R : ℂRes Γ) (A C : ℂForm Γ)
          → sat-rule M (◆·L Γ r R A C)
  ◆·L-sat M Γ r R A C (sat1 , _) =
    ＹL-sat M Γ r R (◆ A) C
      (rule-swap-sat M (ℂv Γ 𝕍ℝ) (↑₀ (◆ A)) (𝕣₀ ◁ ↑ᵣ₀ r) (CEr 𝕣₀) CEu (CEr (↑ᵣ₀ R)) (↑₀ C)
        (rule◆L-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕣₀ (↑ᵣ₀ R) (↑₀ A) (↑₀ C)
          (rule-cut-u-sat M Γ₁ (↑ᵣ₀ (↑ᵣ₀ R)) 𝕣₁ (↑₀ (↑₀ C)) 𝕣₀ (↑ᵣ₀ (↑ᵣ₀ r)) LT
            (rule⊏-transᵣ-sat M Γ₁ 𝕣₀ 𝕣₁ (↑ᵣ₀ (↑ᵣ₀ r)) 𝕣₁
              ((rule-thin-sat M (ℂu (ℂv (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁)) (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr 𝕣₁) (𝕣₀ ⊑ 𝕣₁)
                 (rule-id-comp-u-sat M (ℂv (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ) (CEr 𝕣₀) 𝕣₀ 𝕣₁ LE (lift tt) , lift tt)) ,
                (rule-thin-sat M (ℂu (ℂv (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁))
                  (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr 𝕣₁) (𝕣₁ ⊏ ↑ᵣ₀ (↑ᵣ₀ r))
                  ((rule-thin-sat M (ℂv (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁) CEu (CEr 𝕣₁) (𝕣₁ ⊏ ↑ᵣ₀ (↑ᵣ₀ r))
                     (rule-thin-v-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ 𝕣₀ (𝕣₀ ⊏ ↑ᵣ₀ r)
                       (◁⇒⊏-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕣₀ 𝕣₀ (↑ᵣ₀ r)
                         (ruleLbl-sat M (ℂv Γ 𝕍ℝ) (CEr 𝕣₀) (𝕣₀ ◁ ↑ᵣ₀ r) (lift tt) , lift tt) , lift tt) , lift tt)) , lift tt)) ,
                lift tt) ,
             rule-thin-gen-sat M (ℂv (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ) (ℂu (ℂe ℂ⟨⟩ (↑₀ (↑₀ A)) 𝕣₀) (𝕣₀ ⊏ ↑ᵣ₀ (↑ᵣ₀ r)))
               (𝕣₀ ⊑ 𝕣₁) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (↑₀ (↑₀ C))
               (ℍ₁  , lift tt) ,
             lift tt) , lift tt) , lift tt) , lift tt)
    where
    Γ₁ : ℂ₀
    Γ₁ = ℂe (ℂu (ℂv (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁)) (↑₀ (↑₀ A)) 𝕣₀

    ℍ₂ : sat-sequent M (rseq (ℂu (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍ℝ) (↑₀ (↑₀ A)) 𝕣₀) (𝕣₀ ⊏ ↑ᵣ₀ (↑ᵣ₀ r)))
                            (↑ᵣ₀ (↑ᵣ₀ R))
                            (↑₀ (↑₀ C)))
    ℍ₂ = subst₄ (λ x y z w → sat-sequent M (rseq (ℂu (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍ℝ) x 𝕣₀) (𝕣₀ ⊏ y)) z w))
                (↑₀،↑₀ A) (↑ᵣ₀،↑ᵣ₀ r) (↑ᵣ₀،↑ᵣ₀ R) (↑₀،↑₀ C)
                (rule-thin-v-v11-sat M Γ 𝕍ℝ 𝕍ℝ (↑ᵣ₀ R) (↑₀ C) (↑₀ A) (𝕣₀ ⊏ ↑ᵣ₀ r) (CEr 𝕣₀) CEu
                  (sat1 , lift tt))

    ℍ₁ : sat-sequent M (rseq (ℂu (ℂe (ℂv (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕍ℝ) (↑₀ (↑₀ A)) 𝕣₀) (𝕣₀ ⊏ ↑ᵣ₀ (↑ᵣ₀ r)))
                            (↑ᵣ₀ (↑ᵣ₀ R))
                            (↑₀ (↑₀ C)))
    ℍ₁ = rule-thin-gen-sat M (ℂv Γ 𝕍ℝ)
          (ℂu (ℂe (ℂv ℂ⟨⟩ 𝕍ℝ) (↑₀ (↑₀ A)) 𝕣₀) (𝕣₀ ⊏ ↑ᵣ₀ (↑ᵣ₀ r)))
          (𝕣₀ ◁ ↑ᵣ₀ r) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (↑₀ (↑₀ C))
          (ℍ₂ , lift tt)

-- Derived:
--
--    Γ ⊢[r₁] ◇↓◆ t A      Γ ⊢[r] r₁ ⊑ r₂
-- -----------------------------------------
--              Γ ⊢[r₂] ◇↓◆ t A

◇↓◆⊑ : (Γ : ℂ₀) (r r₁ r₂ t : ℂRes Γ) (A : ℂForm Γ) → Rule
◇↓◆⊑ Γ r r₁ r₂ t A =
  rule (rseq Γ r₁ (◇↓◆ t A) ∷ rseq Γ r (r₁ ⊑ r₂) ∷ [])
       (rseq Γ r₂ (◇↓◆ t A))

◇↓◆⊑-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ r₂ t : ℂRes Γ) (A : ℂForm Γ)
         → sat-rule M (◇↓◆⊑ Γ r r₁ r₂ t A)
◇↓◆⊑-sat M Γ r r₁ r₂ t A (sat1 , sat2 , _) =
  rule-cut-sat M Γ (CEr r₂) (CEr r₁) (◇↓◆ t A) (◇↓◆ t A)
    (sat1 ,
     rule◇↓◆L-sat M Γ t r₁ r₂ A (◇↓◆ t A)
       (subst (λ x → sat-sequent M (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r₁ ⋆ t))) (↑₀ A) 𝕣₀) (↑ᵣ₀ r₂) x))
              (sym (↑◇↓◆ ⊆₀ t A))
              (◇↓◆R-sat M (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r₁ ⋆ t))) (↑₀ A) 𝕣₀)
                (↑ᵣ₀ r₂) 𝕣₀ (↑ᵣ₀ t) (↑₀ A)
                (ruleLbl-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r₁ ⋆ t))) (CEr 𝕣₀) (↑₀ A) (lift tt) ,
                 rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r₁ ⋆ t))) (↑₀ A) (CEr 𝕣₀)
                  (CEr (↑ᵣ₀ r₂)) (𝕣₀ ⊑ ↑ᵣ₀ (r₂ ⋆ t))
                  (rule⊑-trans-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r₁ ⋆ t))) 𝕣₀
                    (↑ᵣ₀ (r₁ ⋆ t)) (↑ᵣ₀ (r₂ ⋆ t)) (↑ᵣ₀ r₂)
                    (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ r₂)) 𝕣₀ (↑ᵣ₀ (r₁ ⋆ t)) LE (lift tt) ,
                     rule⊑-⋆-cong2-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r₁ ⋆ t))) (↑ᵣ₀ r₁)
                      (↑ᵣ₀ t) (↑ᵣ₀ r₂) (↑ᵣ₀ r₂)
                      (rule-thin-sat M (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (r₁ ⋆ t)) CEu (CEr (↑ᵣ₀ r₂))
                        (↑ᵣ₀ r₁ ⊑ ↑ᵣ₀ r₂)
                        (rule-thin-v-sat M Γ 𝕍ℝ r₂ (r₁ ⊑ r₂) (sat2 , lift tt) , lift tt) , lift tt) ,
                     lift tt) ,
                   lift tt) ,
                 lift tt)) ,
        lift tt) ,
     lift tt)

--    Γ, x : ℝ, T ⊑ x, x ⊑ t ⊢[x] A
-- ----------------------------------
--           Γ ⊢[T] □↓ t A

rule□↓R : (Γ : ℂ₀) (T t : ℂRes Γ) (A : ℂForm Γ) → Rule
rule□↓R Γ T t A =
  rule [ rseq (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (T ⋆ t))) 𝕣₀ (↑₀ A) ]
       (rseq Γ T (□↓ t A))

abstract
  rule□↓R-sat : (M : Model₀) (Γ : ℂ₀) (T t : ℂRes Γ) (A : ℂForm Γ)
              → sat-rule M (rule□↓R Γ T t A)
  rule□↓R-sat M Γ T t A (hyp1 , _) =
    ruleＦR-sat M Γ T (□ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ t →· ↑₁ A))) (𝕙₁ , lift tt)
    where
    𝕙₃ : sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (𝕣₀ ⊑ ↑ᵣ₀ T ⋆ ↑ᵣ₀ t →· ↑₀ A))
    𝕙₃ = rule→I-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (𝕣₀ ⊑ ↑ᵣ₀ T ⋆ ↑ᵣ₀ t) (↑₀ A) (hyp1 , lift tt)

    𝕙₂ : sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (Ｆ (𝕣₀ ⊑ ↑ᵣ₀، (↑ᵣ₀ T) ⋆ ↑ᵣ₀، (↑ᵣ₀ t) →· ↑₀، (↑₀ A))))
    𝕙₂ = subst₃ (λ x y z → sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (Ｆ (𝕣₀ ⊑ x ⋆ y →· z))))
                (sym (↑ᵣ₀،-↑ᵣ₀ T)) (sym (↑ᵣ₀،-↑ᵣ₀ t)) (sym (↑₀،-↑₀ A))
                (ruleＦR-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (𝕣₀ ⊑ ↑ᵣ₁ T ⋆ ↑ᵣ₁ t →· ↑₁ A)
                  (subst₃ (λ x y z → sat-sequent M (rseq (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ T ⊑ 𝕣₀)) 𝕣₀ (𝕣₀ ⊑ x ⋆ y →· z)))
                          (sym (sub-Res-↑ᵣ₁ _ _ _ 𝕣₀ T))
                          (sym (sub-Res-↑ᵣ₁ _ _ _ 𝕣₀ t))
                          (sym (sub-↑₁ _ _ _ 𝕣₀ A))
                          𝕙₃ , lift tt))

    𝕙₁ : sat-sequent M (rseq Γ T (□ (Ｆ (𝕣₀ ⊑ ↑ᵣ₀ T ⋆ sub-Res (↑ᵣ₁ t) (CSub، 𝕍ℝ (CSub،ₗ {_} {𝕍ℝ} T)) →· sub (↑₁ A) (CSub، 𝕍ℝ (CSub،ₗ {_} {𝕍ℝ} T))))))
    𝕙₁ = subst₂ (λ x y → sat-sequent M (rseq Γ T (□ (Ｆ (𝕣₀ ⊑ ↑ᵣ₀ T ⋆ x →· y)))))
                (sym (sub-Res-↑ᵣ₁₀ _ _ _ T t))
                (sym (sub-↑₁₀ _ _ _ T A))
                (rule□R-sat M Γ T (Ｆ (𝕣₀ ⊑ ↑ᵣ₀ T ⋆ ↑ᵣ₀ t →· ↑₀ A))
                  (𝕙₂ , lift tt))

-- Derived:
--
--    Γ ⊢[R] ¬· (◇↓ r F)
-- -------------------------
--    Γ ⊢[R] □↓ r (¬· F)

¬◇↓R : (Γ : ℂ₀) (R r : ℂRes Γ) (F : ℂForm Γ) → Rule
¬◇↓R Γ R r F =
  rule [ rseq Γ R (¬· (◇↓ r F)) ]
       (rseq Γ R (□↓ r (¬· F)))

abstract
  ¬◇↓R-sat : (M : Model₀) (Γ : ℂ₀) (R r : ℂRes Γ) (F : ℂForm Γ)
           → sat-rule M (¬◇↓R Γ R r F)
  ¬◇↓R-sat M Γ R r F (hyp1 , _) =
    rule□↓R-sat M Γ R r (¬· F)
      (rule¬I-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) 𝕣₀ (↑₀ F)
        (rule-cut-sat M (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) ⊥· (↑₀ (¬· ◇↓ r F))
          (rule-thin-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (↑₀ (¬· ◇↓ r F))
            (rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)) CEu (CEr (↑ᵣ₀ R)) (↑₀ (¬· ◇↓ r F))
              (rule-thin-sat M (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ R)) (↑₀ (¬· ◇↓ r F))
                (rule-thin-v-sat M Γ 𝕍ℝ R (¬· ◇↓ r F)
                  (hyp1 , lift tt) , lift tt) , lift tt) , lift tt) ,
           subst (λ x → sat-sequent M (rseq (ℂe (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀) (¬· x) (↑ᵣ₀ R)) 𝕣₀ ⊥·))
                 (sym (↑◇↓ ⊆₀ r F))
                 (rule¬E-last-sat M
                   (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀)
                   (↑ᵣ₀ R) (◇↓ (↑ᵣ₀ r) (↑₀ F)) 𝕣₀ ⊥·
                   (rule◇↓R-sat M
                     (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀)
                     (↑ᵣ₀ r) (↑ᵣ₀ R) 𝕣₀ (↑₀ F)
                     (rule-thin-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)))
                       (↑₀ F) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R ⊑ 𝕣₀)
                       (rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)) CEu
                         (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R ⊑ 𝕣₀)
                         (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R) 𝕣₀ LE (lift tt) , lift tt) , lift tt) ,
                      rule-thin-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)))
                       (↑₀ F) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))
                       (rule-id-comp-u-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (CEr (↑ᵣ₀ R)) 𝕣₀
                         (↑ᵣ₀ (R ⋆ r)) LE (lift tt) , lift tt) ,
                      ruleLbl-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (CEr 𝕣₀) (↑₀ F) (lift tt) ,
                      lift tt) , lift tt)) ,
           lift tt) , lift tt) , lift tt)

-- Derived:
--
--   Γ, x : ℝ, x ⊑ R ⋆ t ⊢[x] A
-- ------------------------------
--          Γ ⊢[R] □↓■ t A

□↓■R : (Γ : ℂ₀) (R t : ℂRes Γ) (A : ℂForm Γ) → Rule
□↓■R Γ R t A =
  rule (rseq (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕣₀ (↑₀ A) ∷ [])
       (rseq Γ R (□↓■ t A))

abstract
  □↓■R-sat : (M : Model₀) (Γ : ℂ₀) (R t : ℂRes Γ) (A : ℂForm Γ)
           → sat-rule M (□↓■R Γ R t A)
  □↓■R-sat M Γ R t A (sat1 , _) =
    rule□↓R-sat M Γ R t (■ A)
      (rule■R-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕣₀ (↑₀ A)
        (rule-cut-u-sat M
          (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁))
          𝕣₀ 𝕣₁ (↑₀ (↑₀ A)) 𝕣₀ (↑ᵣ₀ (↑ᵣ₀ (R ⋆ t))) LE
          (rule⊑-trans-sat M
            (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕍ℝ) (𝕣₀ ⊑ 𝕣₁))
            𝕣₀ 𝕣₁ (↑ᵣ₀ (↑ᵣ₀ (R ⋆ t))) 𝕣₁
            (rule-id-comp-u-sat M (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕍ℝ) (CEr 𝕣₁) 𝕣₀ 𝕣₁ LE (lift tt) ,
             rule-thin-sat M
              (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕍ℝ)
              (𝕣₀ ⊑ 𝕣₁) CEu (CEr 𝕣₁) (𝕣₁ ⊑ ↑ᵣ₀ (↑ᵣ₀ (R ⋆ t)))
              (rule-thin-v-sat M
                (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕍ℝ 𝕣₀
                (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))
                (rule-id-comp-u-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (CEr 𝕣₀) 𝕣₀ (↑ᵣ₀ (R ⋆ t)) LE (lift tt) , lift tt) , lift tt) ,
             lift tt) ,
           rule-thin-gen-sat M
            (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) 𝕍ℝ)
            (ℂu ℂ⟨⟩ (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (R ⋆ t)))) (𝕣₀ ⊑ 𝕣₁) CEu (CEr 𝕣₀) (↑₀ (↑₀ A))
            (rule-thin-gen-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀))
              (ℂu (ℂv ℂ⟨⟩ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (R ⋆ t)))) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t)) CEu (CEr 𝕣₀)
              (↑₀ (↑₀ A))
              (rule-thin-gen-sat M (ℂv Γ 𝕍ℝ)
                (ℂu (ℂv ℂ⟨⟩ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (R ⋆ t)))) (↑ᵣ₀ R ⊑ 𝕣₀) CEu (CEr 𝕣₀)
                (↑₀ (↑₀ A))
                (h₁ , lift tt) , lift tt) , lift tt) ,
           lift tt) , lift tt) , lift tt)
    where
    h₁ : sat-sequent M (rseq (ℂu (ℂv (ℂv Γ 𝕍ℝ) 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ (R ⋆ t)))) 𝕣₀ (↑₀ (↑₀ A)))
    h₁ = subst₂ (λ x y → sat-sequent M (rseq (ℂx (ℂv (ℂv Γ 𝕍ℝ) 𝕍ℝ) (𝕣₀ ⊑ x) CEu) 𝕣₀ y))
                (↑ᵣ₀،↑ᵣ₀ (R ⋆ t))
                (↑₀،↑₀ A)
                (rule-thin-v-v1-sat M Γ 𝕍ℝ 𝕍ℝ 𝕣₀ (↑₀ A) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t)) CEu
                  (sat1 , lift tt))

-- Derived:
--
--    Γ ⊢[R] ¬· (◇↓◆ r F)
-- -------------------------
--    Γ ⊢[R] □↓■ r (¬· F)

¬◇↓◆R : (Γ : ℂ₀) (R r : ℂRes Γ) (F : ℂForm Γ) → Rule
¬◇↓◆R Γ R r F =
  rule [ rseq Γ R (¬· (◇↓◆ r F)) ]
       (rseq Γ R (□↓■ r (¬· F)))

¬◇↓◆R-sat : (M : Model₀) (Γ : ℂ₀) (R r : ℂRes Γ) (F : ℂForm Γ)
          → sat-rule M (¬◇↓◆R Γ R r F)
¬◇↓◆R-sat M Γ R r F (hyp1 , _) =
  □↓■R-sat M Γ R r (¬· F)
    (rule¬I-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) 𝕣₀ (↑₀ F)
      (rule-cut-sat M (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀) (CEr 𝕣₀)
        (CEr (↑ᵣ₀ R)) ⊥· (↑₀ (¬· ◇↓◆ r F))
        (rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) (CEr 𝕣₀)
          (CEr (↑ᵣ₀ R)) (↑₀ (¬· ◇↓◆ r F))
          (rule-thin-sat M (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)) CEu (CEr (↑ᵣ₀ R))
            (↑₀ (¬· ◇↓◆ r F))
            (rule-thin-v-sat M Γ 𝕍ℝ R (¬· ◇↓◆ r F) (hyp1 , lift tt) , lift tt) , lift tt) ,
         rule¬E-last-sat M (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀)
          (↑ᵣ₀ R) (↑₀ (◇↓◆ r F)) 𝕣₀ ⊥·
          (subst (λ x → sat-sequent M (rseq (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀) (↑ᵣ₀ R) x))
                 (sym (↑◇↓◆ ⊆₀ r F))
                 (◇↓◆R-sat M (ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) 𝕣₀)
                   (↑ᵣ₀ R) 𝕣₀ (↑ᵣ₀ r) (↑₀ F)
                   (ruleLbl-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (CEr 𝕣₀) (↑₀ F) (lift tt) ,
                    rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))) (↑₀ F) (CEr 𝕣₀)
                     (CEr (↑ᵣ₀ R)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))
                     (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ (R ⋆ r)) LE (lift tt) , lift tt) ,
                    lift tt)) , lift tt) ,
         lift tt) , lift tt) , lift tt)

-- Derived:
--
--    Γ, □↓■ r (¬· F) @ t ⊢[R] C
-- -------------------------------
--    Γ, ¬· (◇↓◆ r F) @ t ⊢[R] C

¬◇↓◆L : (Γ : ℂ₀) (t R r : ℂRes Γ) (F C : ℂForm Γ) → Rule
¬◇↓◆L Γ t R r F C =
  rule [ rseq (ℂe Γ (□↓■ r (¬· F)) t) R C ]
       (rseq (ℂe Γ (¬· (◇↓◆ r F)) t) R C)

¬◇↓◆L-sat : (M : Model₀) (Γ : ℂ₀) (t R r : ℂRes Γ) (F C : ℂForm Γ)
          → sat-rule M (¬◇↓◆L Γ t R r F C)
¬◇↓◆L-sat M Γ t R r F C (hyp1 , _) =
  rule-cut-sat M (ℂe Γ (¬· ◇↓◆ r F) t) (CEr R) (CEr t) C (□↓■ r (¬· F))
    (¬◇↓◆R-sat M (ℂe Γ (¬· ◇↓◆ r F) t) t r F
      (ruleLbl-sat M Γ (CEr t) (¬· ◇↓◆ r F) (lift tt) , lift tt) ,
     rule-thin1-sat M Γ (¬· ◇↓◆ r F) (□↓■ r (¬· F)) (CEr t) (CEr t) (CEr R) C
      (hyp1 , lift tt) ,
     lift tt)

--    Γ ⊢[R] t₁ ⊑ t    Γ ⊢[R] t₂ ⊑ t    Γ, t₁ ⊑ t₂ ⊢[R] A     Γ, t₂ ⊏ t₁ ⊢[R] A
-- -------------------------------------------------------------------------------
--                                Γ ⊢[R] A

⊑∨⊏ : (Γ : ℂ₀) (t t₁ t₂ R : ℂRes Γ) (A : ℂForm Γ) → Rule
⊑∨⊏ Γ t t₁ t₂ R A =
  rule (rseq Γ R (t₁ ⊑ t) ∷ rseq Γ R (t₂ ⊑ t) ∷ rseq (ℂu Γ (t₁ ⊑ t₂)) R A ∷ rseq (ℂu Γ (t₂ ⊏ t₁)) R A ∷ [])
       (rseq Γ R A)

abstract
  ⊑∨⊏-sat : (M : Model₀) (Γ : ℂ₀) (t t₁ t₂ R : ℂRes Γ) (A : ℂForm Γ)
          → sat-rule M (⊑∨⊏ Γ t t₁ t₂ R A)
  ⊑∨⊏-sat M Γ t t₁ t₂ R A (sat1 , sat2 , sat3 , sat4 , _) s satΓ
    with ≼⊎≺ (lower (sat1 s satΓ)) (lower (sat2 s satΓ))
  ... | inj₁ p = sat3 s (satΓ , lift p)
  ... | inj₂ p = sat4 s (satΓ , lift p)

\end{code}
