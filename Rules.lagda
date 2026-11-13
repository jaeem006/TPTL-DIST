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

module Rules(𝔻 : Set)
            (W : World)
            (EM : ExcludedMiddle (lsuc(0ℓ)))
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open import RulesMisc(𝔻)(W)
open import RulesProp(𝔻)(W)
open import RulesPred(𝔻)(W)
open import RulesTemp(𝔻)(W)
open import RulesClassical(𝔻)(W)(EM)

open World.World W

{--
-- Predicate logic

--      Γ, u ⊢ᵣ A
--  ------------------
--     Γ ⊢ᵣ ∀ u A

rule∀I : (Γ : ℂ₀) (r : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ u)) → Rule
rule∀I Γ r u A =
  rule [ seq (ℂv Γ u) (↑ᵣ₀ r) A ]
       (seq Γ r (∀· u A))

rule∀I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ u))
           → sat-rule M (rule∀I Γ r u A)
rule∀I-sat M Γ r u A (satA , _) s satΓ v =
  subst (λ x → x ⊨ A) (≔-≔ₜ (M ≔ₛ s) v (⟦ r ⟧ᵣ s)) c
  where
  c′ : ((M ≔ₛ (s ⹁ u ∶ v)) ≔ₜ (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ u ∶ v))) ⊨ A
  c′ = satA (s ⹁ u ∶ v) satΓ

  c : (((M ≔ₛ s) ≔ v) ≔ₜ (⟦ r ⟧ᵣ s)) ⊨ A
  c = subst (λ x → (((M ≔ₛ s) ≔ v) ≔ₜ x) ⊨ A) (⟦⊆⟧ᵣ s ⊆₀ (s ⹁ u ∶ v) Sub⊆-⊆₀ r) c′

--}


-- ADDITIONAL RULES


{--
--
-- ----------------
--    Γ, A ⊢ᵣ A

ruleUnlbl : (Γ : ℂ₀) ( r : ℂRes Γ) (A : ℂForm Γ) → Rule
ruleUnlbl Γ r A =
  rule []
  (seq (ℂu Γ A) r A)
--}

--     Γ ⊢ ₜ r₁ ⟨c⟩ r₂
-- -----------------------
--    Γ ⊢ᵣ (r₁ ⟨c⟩ r₂)ˡ

ruleResSwap :  (Γ : ℂ₀) ( r r′ r₁ r₂ : ℂRes Γ) (c : Comparison) → Rule
ruleResSwap  Γ r r′ r₁ r₂ c =
  rule (rseq Γ r′ (r₁ ⟨ c ⟩ r₂) ∷ [])
       (rseq Γ r (r₁ ⟨ c ⟩ r₂))


-- Examples


{--
rule-thin-ℂi : (Γ : ℂ₀) (T : ℂRes Γ) (i : ℂInterval Γ) (A C : ℂForm Γ) → Rule
rule-thin-ℂi Γ T i A C =
  rule (seq Γ T C ∷ [])
       (seq (ℂi Γ A i) T C)

rule-thin-ℂi-sat : (M : Model₀) (Γ : ℂ₀) (T : ℂRes Γ) (i : ℂInterval Γ) (A C : ℂForm Γ)
                 → sat-rule M (rule-thin-ℂi Γ T i A C)
rule-thin-ℂi-sat M Γ T i A C (sat1 , _) s (satΓ , satA) =
  sat1 s satΓ
--}

rule-◇↓-density : (Γ : ℂ₀) (R r r₁ r₂ : ℂRes Γ) (A : ℂForm Γ) → Rule
rule-◇↓-density Γ R r r₁ r₂ A =
  rule (rseq Γ R (◇↓ r₁ (◇↓ r₂ A)) ∷ rseq Γ R ((r₁ ⋆ r₂) ⊑ r) ∷ [])
       (rseq Γ R (◇↓ r A))

-- We prove the validity of this rule using existing rules.
-- 1. We first cut in the 1st hyp
-- 2. We eliminate that hypothesis twice to "unfold" the ◇↓s using rule◇↓L-sat
-- 3. We then introduce the ◇↓ in the conclusion using rule◇↓R-sat
-- 4. We finally have to prove that the conditions coming from rule◇↓R-sat hold, one of which is the 2nd hyp
rule-◇↓-density-sat : (M : Model₀) (Γ : ℂ₀) (R r r₁ r₂ : ℂRes Γ) (A : ℂForm Γ)
                    → sat-rule M (rule-◇↓-density Γ R r r₁ r₂ A)
rule-◇↓-density-sat M Γ R r r₁ r₂ A (sat1 , sat2 , _) =
  rule-cut-sat M Γ (CEr R) (CEr R) (◇↓ r A) (◇↓ r₁ (◇↓ r₂ A)) (sat1 , 𝟙 , lift tt)
  where
  Γ₅ : ℂ₀
  Γ₅ = ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)
  --                  {--H1--}

  Γ₄ : ℂ₀
  Γ₄ = ℂu Γ₅ (𝕣₀ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁)
  --              {--H2--}

  Γ₃ : ℂ₀
  Γ₃ = ℂv Γ₄ 𝕍ℝ
  --

  Γ₂ : ℂ₀
  Γ₂ = ℂu Γ₃ (𝕣₁ ⊑ 𝕣₀)
  --         {--H3--}

  Γ₁ : ℂ₀
  Γ₁ = ℂu Γ₂ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r₂)
  --             {--H4--}

  Γ₀ : ℂ₀
  Γ₀ = ℂe Γ₁ (↑₁ A) 𝕣₀

  𝟙𝟞 : sat-sequent M (rseq Γ₄ (↑ᵣ₀ R) (↑ᵣ₀ ((R ⋆ r₁) ⋆ r₂) ⊑ ↑ᵣ₀ (R ⋆ r)))
  𝟙𝟞 = rule＝-⊑-trans-sat M Γ₄ (↑ᵣ₀ ((R ⋆ r₁) ⋆ r₂)) (↑ᵣ₀ (R ⋆ (r₁ ⋆ r₂))) (↑ᵣ₀ (R ⋆ r)) (↑ᵣ₀ R)
         (rule＝-sym-sat M Γ₄ (↑ᵣ₀ (R ⋆ r₁ ⋆ r₂)) (↑ᵣ₀ (R ⋆ (r₁ ⋆ r₂))) (↑ᵣ₀ R)
            (rule＝-⋆-assoc-sat M Γ₄ (↑ᵣ₀ R) (↑ᵣ₀ r₁) (↑ᵣ₀ r₂) (↑ᵣ₀ R) (lift tt) , lift tt) ,
          rule⊑-⋆-cong-sat M Γ₄ (↑ᵣ₀ R) (↑ᵣ₀ (r₁ ⋆ r₂)) (↑ᵣ₀ R) (↑ᵣ₀ r) (↑ᵣ₀ R)
            (rule⊑-refl-sat M Γ₄ (↑ᵣ₀ R) (↑ᵣ₀ R) (lift tt) ,
            rule-thin-sat M Γ₅ (𝕣₀ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁) CEu (CEr (↑ᵣ₀ R)) (↑₀ (r₁ ⋆ r₂ ⊑ r))
              ((rule-thin-sat M (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ R)) ((↑₀ (r₁ ⋆ r₂ ⊑ r)))
                  ((rule-thin-v-sat M Γ 𝕍ℝ R (r₁ ⋆ r₂ ⊑ r) (sat2 , lift tt)) , lift tt)) , lift tt) ,
            lift tt) ,
          lift tt)

  𝟙𝟝 : sat-sequent M (rseq Γ₄ (↑ᵣ₀ R) (𝕣₀ ⋆ ↑ᵣ₀ r₂ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁ ⋆ ↑ᵣ₀ r₂))
  𝟙𝟝 = rule⊑-⋆-cong-sat M Γ₄ 𝕣₀ (↑ᵣ₀ r₂) (↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁) (↑ᵣ₀ r₂) (↑ᵣ₀ R)
         (rule-id-comp-u-sat M Γ₅ (CEr (↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁) LE (lift tt) ,
          rule⊑-refl-sat M Γ₄ (↑ᵣ₀ r₂) (↑ᵣ₀ R) (lift tt) ,
          lift tt)

  𝟙𝟜 : sat-sequent M (rseq Γ₄ (↑ᵣ₀ R) (𝕣₀ ⋆ ↑ᵣ₀ r₂ ⊑ ↑ᵣ₀ (R ⋆ r)))
  𝟙𝟜 = rule⊑-trans-sat M Γ₄ (𝕣₀ ⋆ ↑ᵣ₀ r₂) (↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁ ⋆ ↑ᵣ₀ r₂) (↑ᵣ₀ (R ⋆ r)) (↑ᵣ₀ R)
         (𝟙𝟝 , 𝟙𝟞 , lift tt)

  𝟙𝟛 : sat-sequent M (rseq Γ₁ (↑ᵣ₁ R) (𝕣₁ ⋆ ↑ᵣ₁ r₂ ⊑ ↑ᵣ₁ R ⋆ ↑ᵣ₁ r)) -- from sat2 & H2
  𝟙𝟛 = rule-thin-sat M Γ₂ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r₂) CEu (CEr (↑ᵣ₁ R)) (𝕣₁ ⋆ ↑ᵣ₁ r₂ ⊑ ↑ᵣ₁ R ⋆ ↑ᵣ₁ r)
         (rule-thin-sat M Γ₃ (𝕣₁ ⊑ 𝕣₀) CEu (CEr (↑ᵣ₁ R)) (𝕣₁ ⋆ ↑ᵣ₁ r₂ ⊑ ↑ᵣ₁ R ⋆ ↑ᵣ₁ r)
            ((subst₃ (λ x y z → sat-sequent M (rseq Γ₃ x (𝕣₁ ⋆ y ⊑ z))) (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ R)) (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r₂)) (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ (R ⋆ r)))
                     (rule-thin-v-sat M Γ₄ 𝕍ℝ (↑ᵣ₀ R) (𝕣₀ ⋆ ↑ᵣ₀ r₂ ⊑ ↑ᵣ₀ (R ⋆ r)) (𝟙𝟜 , lift tt))) , lift tt), lift tt)

  𝟙𝟚 : sat-sequent M (rseq Γ₁ (↑ᵣ₁ R) (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r₂))
  𝟙𝟚 = rule-id-comp-u-sat M Γ₂ (CEr (↑ᵣ₁ R)) 𝕣₀ (𝕣₁ ⋆ ↑ᵣ₁ r₂) LE (lift tt)

  𝟙𝟙 : sat-sequent M (rseq Γ₀ (↑ᵣ₁ R) (𝕣₁ ⊑ 𝕣₀))
  𝟙𝟙 = rule-thin-sat
         M Γ₁ (↑₁ A) (CEr 𝕣₀) (CEr (↑ᵣ₁ R)) (𝕣₁ ⊑ 𝕣₀)
         (rule-thin-sat M Γ₂ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r₂) CEu (CEr (↑ᵣ₁ R)) (𝕣₁ ⊑ 𝕣₀)
            (rule-id-comp-u-sat M Γ₃ (CEr (↑ᵣ₁ R)) 𝕣₁ 𝕣₀ LE (lift tt) , lift tt) ,
          lift tt)

  𝟙𝟘 : sat-sequent M (rseq Γ₀ (↑ᵣ₁ R) (↑ᵣ₁ R ⊑ 𝕣₁)) -- from H1
  𝟙𝟘 = rule-thin-sat M Γ₁ (↑₁ A) (CEr 𝕣₀) (CEr (↑ᵣ₁ R)) (↑ᵣ₁ R ⊑ 𝕣₁)
         (rule-thin-sat  M Γ₂ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r₂) CEu (CEr (↑ᵣ₁ R)) (↑ᵣ₁ R ⊑ 𝕣₁)
            (rule-thin-sat M Γ₃ (𝕣₁ ⊑ 𝕣₀) CEu (CEr (↑ᵣ₁ R)) (↑ᵣ₁ R ⊑ 𝕣₁)
               (subst₂ (λ x y → sat-sequent M (rseq Γ₃ x (y ⊑ 𝕣₁))) (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ R)) (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ R))
                       (rule-thin-v-sat M Γ₄ 𝕍ℝ (↑ᵣ₀ R) (↑ᵣ₀ R ⊑ 𝕣₀)
                          (rule-thin-sat M Γ₅ (𝕣₀ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁) CEu (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R ⊑ 𝕣₀)
                             (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R) 𝕣₀ LE (lift tt) , lift tt) ,
                           lift tt)) , lift tt) , lift tt) , lift tt)

  𝟡 : sat-sequent M (rseq Γ₀ 𝕣₀ (↑₁ A))
  𝟡 = ruleLbl-sat M Γ₁ (CEr 𝕣₀) (↑₁ A) (lift tt)

  𝟠 : sat-sequent M (rseq Γ₀ (↑ᵣ₁ R) (𝕣₀ ⊑ ↑ᵣ₁ R ⋆ ↑ᵣ₁ r))  -- from H4 + sat2
  𝟠 = rule-thin-sat M Γ₁ (↑₁ A) (CEr 𝕣₀) (CEr (↑ᵣ₁ R)) (𝕣₀ ⊑ ↑ᵣ₁ R ⋆ ↑ᵣ₁ r)
        (rule⊑-trans-sat M Γ₁ 𝕣₀ (𝕣₁ ⋆ ↑ᵣ₁ r₂) (↑ᵣ₁ R ⋆ ↑ᵣ₁ r) (↑ᵣ₁ R) (𝟙𝟚 , 𝟙𝟛 , lift tt) , lift tt)

  𝟟 : sat-sequent M (rseq Γ₀ (↑ᵣ₁ R) (↑ᵣ₁ R ⊑ 𝕣₀)) -- from H1 + H3
  𝟟 = rule⊑-trans-sat M Γ₀ (↑ᵣ₁ R) 𝕣₁ 𝕣₀ (↑ᵣ₁ R) (𝟙𝟘 , 𝟙𝟙 , lift tt)

  𝟞 : sat-sequent M (rseq Γ₀ (↑ᵣ₁ R) (◇↓ (↑ᵣ₁ r) (↑₁ A)))
  𝟞 = rule◇↓R-sat M Γ₀ (↑ᵣ₁ r) (↑ᵣ₁ R) 𝕣₀ (↑₁ A) (𝟟 , 𝟠 , 𝟡 , lift tt)

  𝟝 : sat-sequent M (rseq Γ₀ (↑ᵣ₁ R) (◇↓ (↑ᵣ₀ (↑ᵣ₀ r)) (↑₀ (↑₀ A))))
  𝟝 = subst₂ (λ x y → sat-sequent M (rseq Γ₀ (↑ᵣ₁ R) (◇↓ x y)))
             (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r) (↑₁≡↑₀↑₀ A) 𝟞

  𝟜 : sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁)) 𝕍ℝ) (𝕣₁ ⊑ 𝕣₀)) (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂)))
                             (↑₀ (↑₀ A))
                             𝕣₀)
                         (↑ᵣ₀ (↑ᵣ₀ R))
                         (↑₀ (◇↓ (↑ᵣ₀ r) (↑₀ A))))
  𝟜 = subst₄ (λ x y z w → sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ r₁)) 𝕍ℝ) (𝕣₁ ⊑ 𝕣₀)) (𝕣₀ ⊑ 𝕣₁ ⋆ x)) y 𝕣₀) z w))
             (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r₂) (↑₁≡↑₀↑₀ A) (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ R) (sym (↑₀-◇↓ (↑ᵣ₀ r) (↑₀ A))) 𝟝

  𝟛 : sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) (◇↓ (↑ᵣ₀ r₂) (↑₀ A)) 𝕣₀) (↑ᵣ₀ R) (◇↓ (↑ᵣ₀ r) (↑₀ A)))
  𝟛 = rule◇↓L-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) (↑ᵣ₀ r₂) 𝕣₀ (↑ᵣ₀ R) (↑₀ A) (◇↓ (↑ᵣ₀ r) (↑₀ A)) (𝟜 , lift tt)

  𝟚 : sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) (↑₀ (◇↓ r₂ A)) 𝕣₀) (↑ᵣ₀ R) (↑₀ (◇↓ r A)))
  𝟚 = subst₂ (λ x y → sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) x 𝕣₀) (↑ᵣ₀ R) y))
             (sym (↑₀-◇↓ r₂ A)) (sym (↑₀-◇↓ r A)) 𝟛

  𝟙 : sat-sequent M (rseq (ℂe Γ (◇↓ r₁ (◇↓ r₂ A)) R) R (◇↓ r A))
  𝟙 = rule◇↓L-sat M Γ r₁ R R (◇↓ r₂ A) (◇↓ r A) (𝟚 , lift tt)


↑₀◇↓ : {Γ : Ctxt} {v : 𝕍} (r : Res Γ) (A : Form Γ)
     → ↑₀ {_} {v} (◇↓ r A) ≡ ◇↓ (↑ᵣ₀ r) (↑₀ A)
↑₀◇↓ {Γ} {v} r A =
  cong₂ (λ x y → Ｆ ◇ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ x ∧· y)))
        (sym (↑ᵣ₁-↑ᵣ₀≡↑⊆،＋ _ _ _ _ r))
        (sym (↑₁-↑₀≡↑⊆،＋ _ _ _ _ A))

{--
◇↓-dist : {Γ : Ctxt} {m : Model Γ} {P Q : Form Γ} {t : Res Γ}
        → m ⊨ □ (P →· Q)
        → m ⊨ ◇↓ t P
        → m ⊨ ◇↓ t Q
◇↓-dist {Γ} {m} {P} {Q} {t} ⊨PQ ⊨P = {!!}
--}

rule-◇↓-dist : (Γ : ℂ₀) (R r : ℂRes Γ) (P Q : ℂForm Γ) → Rule
rule-◇↓-dist Γ R r P Q =
  rule (rseq Γ R (□ (P →· Q)) ∷ rseq Γ R (◇↓ r P) ∷ [])
       (rseq Γ R (◇↓ r Q))

-- This could be proved using the existing rules, in particular: rule□L-sat & rule◇↓L-sat
rule-◇↓-dist-sat : (M : Model₀) (Γ : ℂ₀) (R r : ℂRes Γ) (P Q : ℂForm Γ)
                 → sat-rule M (rule-◇↓-dist Γ R r P Q)
rule-◇↓-dist-sat M Γ R r P Q (sat1 , sat2 , _) =
  rule-cut-sat M Γ (CEr R) (CEr R) (◇↓ r Q) (◇↓ r P)
    (sat2 ,
     rule◇↓L-sat M Γ r R R P (◇↓ r Q)
       (𝟙 , lift tt) ,
     lift tt)
  where
  Γ₂ : ℂ₀
  Γ₂ = ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)
  --                     H3

  Γ₁ : ℂ₀
  Γ₁ = ℂu Γ₂ (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r))
  --               H2

  Γ₀ : ℂ₀
  Γ₀ = ℂe Γ₁ (↑₀ P) 𝕣₀
  --           H1

  𝟜 : sat-sequent M (rseq (ℂe Γ₀ (□ ((↑₀ P) →· (↑₀ Q))) (↑ᵣ₀ R)) 𝕣₀ (↑₀ Q))
  𝟜 = rule□L-sat M Γ₀ (↑ᵣ₀ R) 𝕣₀ 𝕣₀ (↑₀ P →· ↑₀ Q) (↑₀ Q)
        (rule→L-sat M (ℂe Γ₀ (□ (↑₀ P →· ↑₀ Q)) (↑ᵣ₀ R)) (CEr 𝕣₀) 𝕣₀ (↑₀ P) (↑₀ Q) (↑₀ Q)
          (rule-thin-sat M Γ₀ (□ (↑₀ P →· ↑₀ Q)) (CEr (↑ᵣ₀ R)) (CEr 𝕣₀) (↑₀ P)  -- need to thin to get (↑₀ P) inside Γ₀
            (ruleLbl-sat M Γ₁ (CEr 𝕣₀) (↑₀ P) (lift tt) , lift tt) ,
           ruleLbl-sat M (ℂe Γ₀ (□ (↑₀ P →· ↑₀ Q)) (↑ᵣ₀ R)) (CEr 𝕣₀) (↑₀ Q) (lift tt) ,
           lift tt) ,
         rule-thin-sat M Γ₁ (↑₀ P) (CEr 𝕣₀) (CEr 𝕣₀) (↑ᵣ₀ R ⊑ 𝕣₀)
           (rule-thin-sat M Γ₂ (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)) CEu (CEr 𝕣₀) (↑ᵣ₀ R ⊑ 𝕣₀)
             (ruleLbl-sat M (ℂv Γ 𝕍ℝ) (CEr 𝕣₀) (↑ᵣ₀ R ⊑ 𝕣₀) (lift tt) , lift tt) , lift tt) ,
         lift tt)

  𝟛 : sat-sequent M (rseq Γ₀ 𝕣₀ (↑₀ Q))
  𝟛 = rule-cut-sat M Γ₀ (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (↑₀ Q) (↑₀ (□ (P →· Q)))  -- from sat1
        (rule-thin-sat M Γ₁ (↑₀ P) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (↑₀ (□ (P →· Q)))
          (rule-thin-sat M Γ₂ (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)) CEu (CEr (↑ᵣ₀ R)) (↑₀ (□ (P →· Q)))
            (rule-thin-sat M (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ R)) (↑₀ (□ (P →· Q)))
              (rule-thin-v-sat M Γ 𝕍ℝ R (□ (P →· Q)) (sat1 , lift tt) , lift tt) , lift tt) , lift tt) ,
         𝟜 , -- eliminate the □ using rule□L-sat
         lift tt)

  𝟚 : sat-sequent M (rseq Γ₀ (↑ᵣ₀ R) (◇↓ (↑ᵣ₀ r) (↑₀ Q)))
  𝟚 = rule◇↓R-sat M Γ₀ (↑ᵣ₀ r) (↑ᵣ₀ R) 𝕣₀ (↑₀ Q)
        (rule-thin-sat M Γ₁ (↑₀ P) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R ⊑ 𝕣₀)       -- from H3
          (rule-thin-sat M Γ₂ (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)) CEu (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R ⊑ 𝕣₀)
            (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R) 𝕣₀ LE (lift tt) , lift tt) ,
           lift tt) ,
         rule-thin-sat M Γ₁ (↑₀ P) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r)) -- from H2
           (rule-id-comp-u-sat M Γ₂ (CEr (↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ (R ⋆ r)) LE (lift tt) , lift tt)  ,
         𝟛 , -- from H1
         lift tt)

  𝟙 : sat-sequent M (rseq Γ₀ (↑ᵣ₀ R) (↑₀ (◇↓ r Q)))
  𝟙 = subst (λ x → sat-sequent M (rseq Γ₀ (↑ᵣ₀ R) x)) (sym (↑₀◇↓ r Q)) 𝟚


-- Derived rule:
--   Γ ⊢[R] ◇↓ r₁ (◇↓ r₂ A)
-- --------------------------
--   Γ ⊢[R] ◇↓ (r₁ ⋆ r₂) A

rule-◇↓-dense : (Γ : ℂ₀) (R r₁ r₂ : ℂRes Γ) (A : ℂForm Γ) → Rule
rule-◇↓-dense Γ R r₁ r₂ A =
  rule (rseq Γ R (◇↓ r₁ (◇↓ r₂ A)) ∷ [])
       (rseq Γ R (◇↓ (r₁ ⋆ r₂) A))

-- This could be proved using the existing rules, in particular: rule□L-sat & rule◇↓L-sat
rule-◇↓-dense-sat : (M : Model₀) (Γ : ℂ₀) (R r₁ r₂ : ℂRes Γ) (A : ℂForm Γ)
                  → sat-rule M (rule-◇↓-dense Γ R r₁ r₂ A)
rule-◇↓-dense-sat M Γ R r₁ r₂ A (sat1 , _) =
  rule-cut-sat M Γ (CEr R) (CEr R) (◇↓ (r₁ ⋆ r₂) A) (◇↓ r₁ (◇↓ r₂ A))
    (sat1 , rule◇↓L-sat M Γ r₁ R R (◇↓ r₂ A) (◇↓ (r₁ ⋆ r₂) A) (𝟙 , lift tt) , lift tt)
  where
  𝟟 : sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) 𝕍ℝ)
                                     (𝕣₁ ⊑ 𝕣₀))
                                 (𝕣₀ ⊑ ↑ᵣ₀ (𝕣₀ ⋆ ↑ᵣ₀ r₂)))
                             (↑₀ (↑₀ A)) 𝕣₀)
                         𝕣₀
                         (↑₀ (↑₀ A)))
  𝟟 = ruleLbl-sat M (ℂu (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) 𝕍ℝ)
                                     (𝕣₁ ⊑ 𝕣₀))
                                 (𝕣₀ ⊑ ↑ᵣ₀ (𝕣₀ ⋆ ↑ᵣ₀ r₂))) (CEr 𝕣₀) (↑₀ (↑₀ A)) (lift tt)



  --             H1         H2               H3        H4        H5
  -- Γ , [𝕣₁], R ⊑ 𝕣₁, 𝕣₁ ⊑ R ⋆ r₁, [𝕣₀], 𝕣₁ ⊑ 𝕣₀, 𝕣₀ ⊑ 𝕣₁ ⋆ r₂, A


  Γ₆ : ℂ₀
  Γ₆ = ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)

  Γ₅ : ℂ₀
  Γ₅ = ℂu Γ₆ (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))

  Γ₄ : ℂ₀
  Γ₄ = ℂv Γ₅ 𝕍ℝ

  Γ₃ : ℂ₀
  Γ₃ = ℂu Γ₄ (𝕣₁ ⊑ 𝕣₀)

  Γ₂ : ℂ₀
  Γ₂ = ℂu Γ₃ (𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂)))

  Γ₁ : ℂ₀
  Γ₁ = ℂe Γ₂ (↑₀ (↑₀ A)) 𝕣₀

  𝟞𝕒 : sat-sequent M (rseq Γ₁ (↑ᵣ₀ (↑ᵣ₀ R)) (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂))) -- H4
  𝟞𝕒 = rule-thin-sat M Γ₂ (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂)))
                     (ruleLbl-sat M Γ₃ (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂))) (lift tt) , lift tt)

  -- 1. associativity: R ⋆ (r₁ ⋆ r₂) → (R ⋆ r₁) ⋆ r₂ X
  -- 2. congruence (⋆ r₂) X
  -- 3. left to prove: 𝕣₁ ⊑ R ⋆ r₁ -- H2X
  𝟞𝕓 : sat-sequent M (rseq Γ₁ (↑ᵣ₀ (↑ᵣ₀ R)) (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂) ⊑ ↑ᵣ₀ (↑ᵣ₀ R) ⋆ ↑ᵣ₀ (↑ᵣ₀ (r₁ ⋆ r₂))))
  𝟞𝕓 = rule＝-⊑-transR-sat M
                          Γ₁
                          (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂))
                          ((↑ᵣ₀ (↑ᵣ₀ R) ⋆ (↑ᵣ₀ (↑ᵣ₀ r₁))) ⋆ (↑ᵣ₀ (↑ᵣ₀ r₂)))
                          (↑ᵣ₀ (↑ᵣ₀ R) ⋆ (↑ᵣ₀ (↑ᵣ₀ r₁) ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂)))
                          (↑ᵣ₀ (↑ᵣ₀ R))
                           (rule＝-⋆-assoc-sat M Γ₁ (↑ᵣ₀ (↑ᵣ₀ R)) (↑ᵣ₀ (↑ᵣ₀ r₁)) (↑ᵣ₀ (↑ᵣ₀ r₂)) (↑ᵣ₀ (↑ᵣ₀ R)) (lift tt)
                          , (rule⊑-⋆-cong2-sat M Γ₁ 𝕣₁ (↑ᵣ₀ (↑ᵣ₀ r₂))  (↑ᵣ₀ (↑ᵣ₀ R) ⋆ ↑ᵣ₀ (↑ᵣ₀ r₁)) (↑ᵣ₀ (↑ᵣ₀ R))
                                               ((rule-thin-sat M Γ₂ (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₁ ⊑ ↑ᵣ₀ ( ↑ᵣ₀  (R ⋆ r₁)))
                                                   (rule-thin-sat M Γ₃ (𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂))) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₁ ⊑ ↑ᵣ₀ ( ↑ᵣ₀  (R ⋆ r₁)))
                                                       ((rule-thin-sat M Γ₄ (𝕣₁ ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₁ ⊑ ↑ᵣ₀ ( ↑ᵣ₀  (R ⋆ r₁)))
                                                          (rule-thin-v-sat M Γ₅ 𝕍ℝ (↑ᵣ₀ R) ( 𝕣₀ ⊑  ↑ᵣ₀  (R ⋆ r₁))
                                                              (ruleLbl-sat M Γ₆ (CEr (↑ᵣ₀ R)) ( 𝕣₀ ⊑  ↑ᵣ₀  (R ⋆ r₁)) (lift tt)
                                                              , (lift tt))
                                                          , (lift tt)))
                                                       , (lift tt))
                                                   , (lift tt)))
                                               , (lift tt))
                            , lift tt))

--  (↑ᵣ₀ (↑ᵣ₀ R) ⋆ (↑ᵣ₀ (↑ᵣ₀ r₁) ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂)) ＝  ↑ᵣ₀ (↑ᵣ₀ R) ⋆ ↑ᵣ₀ (↑ᵣ₀ r₁) ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂)))

  𝟞 : sat-sequent M (rseq Γ₁
                         (↑ᵣ₀ (↑ᵣ₀ R))
                         (𝕣₀ ⊑ ↑ᵣ₀ (↑ᵣ₀ R) ⋆ ↑ᵣ₀ (↑ᵣ₀ (r₁ ⋆ r₂))))
  𝟞 = rule⊑-trans-sat M Γ₁
        𝕣₀
        (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂))
        (↑ᵣ₀ (↑ᵣ₀ R) ⋆ ↑ᵣ₀ (↑ᵣ₀ (r₁ ⋆ r₂)))
        (↑ᵣ₀ (↑ᵣ₀ R))
        (𝟞𝕒 , 𝟞𝕓 , lift tt) -- Javier

  𝟝𝕒 : sat-sequent M (rseq Γ₁ (↑ᵣ₀ (↑ᵣ₀ R)) (↑ᵣ₀ (↑ᵣ₀ R) ⊑ 𝕣₁)) -- H1
  𝟝𝕒 = rule-thin-sat M Γ₂ (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (↑ᵣ₀ (↑ᵣ₀ R) ⊑ 𝕣₁)
                     ((rule-thin-sat M Γ₃ (𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂))) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (↑ᵣ₀ (↑ᵣ₀ R) ⊑ 𝕣₁)
                       ((rule-thin-sat M Γ₄ (𝕣₁ ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (↑ᵣ₀ (↑ᵣ₀ R) ⊑ 𝕣₁)
                         ((rule-thin-v-sat M Γ₅ 𝕍ℝ (↑ᵣ₀ R) ((↑ᵣ₀ R) ⊑ 𝕣₀)
                           ((rule-thin-sat M Γ₆ (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁)) CEu (CEr (↑ᵣ₀ R)) ((↑ᵣ₀ R) ⊑ 𝕣₀)
                             ((ruleLbl-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R ⊑ 𝕣₀) (lift tt))
                             , (lift tt)))
                           , (lift tt)))
                         , (lift tt)))
                       , (lift tt)))
                     , (lift tt))

  𝟝𝕓 : sat-sequent M (rseq Γ₁ (↑ᵣ₀ (↑ᵣ₀ R)) (𝕣₁ ⊑ 𝕣₀)) -- H3
  𝟝𝕓 = rule-thin-sat M (ℂu (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) 𝕍ℝ)
                                     (𝕣₁ ⊑ 𝕣₀))
                                 (𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂)))) (↑₀ (↑₀ A)) (CEr 𝕣₀) (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₁ ⊑ 𝕣₀)
        (rule-thin-sat M (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) 𝕍ℝ)
                                     (𝕣₁ ⊑ 𝕣₀)) (𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₀ (↑ᵣ₀ r₂))) CEu (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₁ ⊑ 𝕣₀)
           (ruleLbl-sat M (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) 𝕍ℝ) (CEr (↑ᵣ₀ (↑ᵣ₀ R))) (𝕣₁ ⊑ 𝕣₀) (lift tt) , lift tt) , lift tt)

  𝟝 : sat-sequent M (rseq Γ₁
                         (↑ᵣ₀ (↑ᵣ₀ R))
                         (↑ᵣ₀ (↑ᵣ₀ R) ⊑ 𝕣₀))
  𝟝 = rule⊑-trans-sat M Γ₁ (↑ᵣ₀ (↑ᵣ₀ R)) 𝕣₁ 𝕣₀ (↑ᵣ₀ (↑ᵣ₀ R)) (𝟝𝕒 , 𝟝𝕓 , lift tt) -- Javier

  𝟜 : sat-sequent M (rseq Γ₁
                         (↑ᵣ₀ (↑ᵣ₀ R))
                         (◇↓ (↑ᵣ₀ (↑ᵣ₀ (r₁ ⋆ r₂))) (↑₀ (↑₀ A))))
  𝟜 = rule◇↓R-sat M
       Γ₁
       (↑ᵣ₀ (↑ᵣ₀ (r₁ ⋆ r₂))) (↑ᵣ₀ (↑ᵣ₀ R)) 𝕣₀ (↑₀ (↑₀ A))
       (𝟝 , 𝟞 , 𝟟 , lift tt)

  𝟛 : sat-sequent M (rseq Γ₁
                         (↑ᵣ₀ (↑ᵣ₀ R))
                         (↑₀ (◇↓ (↑ᵣ₀ (r₁ ⋆ r₂)) (↑₀ A))))
  𝟛 = subst (λ x → sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) 𝕍ℝ)
                                                  (𝕣₁ ⊑ 𝕣₀))
                                              (𝕣₀ ⊑ ↑ᵣ₀ (𝕣₀ ⋆ ↑ᵣ₀ r₂)))
                                          (↑₀ (↑₀ A)) 𝕣₀)
                                      (↑ᵣ₀ (↑ᵣ₀ R)) x))
            (sym (↑₀◇↓ (↑ᵣ₀ (r₁ ⋆ r₂)) (↑₀ A)))
            𝟜

  𝟚 : sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) (◇↓ (↑ᵣ₀ r₂) (↑₀ A)) 𝕣₀)
                         (↑ᵣ₀ R)
                         (◇↓ (↑ᵣ₀ (r₁ ⋆ r₂)) (↑₀ A)))
  𝟚 = rule◇↓L-sat M (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁)))
       (↑ᵣ₀ r₂) 𝕣₀ (↑ᵣ₀ R) (↑₀ A) (◇↓ (↑ᵣ₀ (r₁ ⋆ r₂)) (↑₀ A))
       (𝟛 , lift tt)

  𝟙 : sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) (↑₀ (◇↓ r₂ A)) 𝕣₀)
                         (↑ᵣ₀ R)
                         (↑₀ (◇↓ (r₁ ⋆ r₂) A)))
  𝟙 = subst₂ (λ x y → sat-sequent M (rseq (ℂe (ℂu (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ R ⊑ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ r₁))) x 𝕣₀) (↑ᵣ₀ R) y))
             (sym (↑₀◇↓ r₂ A)) (sym (↑₀◇↓ (r₁ ⋆ r₂) A)) 𝟚


-- if 'a' is sent by 'i' to 'A' now then by 'Δ' it will be receiced by all the agents in 'A'
synchrony-assumption-body : {Γ : Ctxt} (Δ : Res Γ) → Form (Γ ، 𝕍Agent ، 𝕍Agents ، 𝕍Data ، 𝕍Agent)
synchrony-assumption-body Δ = (𝔸 (𝕒0 ∈ₐ 𝔸2)) →· □ (send[ 𝕒3 ⇒ 𝕕1 ⇒ 𝔸2 ] →· ◇↓ (↑ᵣ₃ Δ) recv[ 𝕒0 ⇐ 𝕕1 ⇐ 𝕒3 ])

synchrony-assumption : {Γ : Ctxt} (Δ : Res Γ) → Form Γ
synchrony-assumption Δ =
  ∀ₐ (∀ₛ (∀ᵢ (∀ₐ (synchrony-assumption-body Δ))))
-- 𝕒3  𝔸2  𝕕1  a0

synchrony-assumption-body₁ : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) → Form (Γ ، 𝕍Agents ، 𝕍Data ، 𝕍Agent)
synchrony-assumption-body₁ Δ a = (𝔸 (𝕒0 ∈ₐ 𝔸2)) →· □ (send[ ↑ᵢ₂ a ⇒ 𝕕1 ⇒ 𝔸2 ] →· ◇↓ (↑ᵣ₂ Δ) recv[ 𝕒0 ⇐ 𝕕1 ⇐ ↑ᵢ₂ a ])

synchrony-assumption₁ : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) → Form Γ
synchrony-assumption₁ Δ a =
  ∀ₛ (∀ᵢ (∀ₐ (synchrony-assumption-body₁ Δ a)))
-- 𝔸2  𝕕1  a0

synchrony-assumption-sub : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ)
                         → sub (∀ₛ (∀ᵢ (∀ₐ (synchrony-assumption-body Δ)))) (CSub،ₗ a)
                         ≡ synchrony-assumption₁ Δ a
synchrony-assumption-sub {Γ} Δ a =
  cong₂ (λ x y → ∀ₛ (∀ᵢ (∀ₐ ((𝔸 (𝕒0 ∈ₐ 𝔸2)) →· □ (send[ x ⇒ 𝕕1 ⇒ 𝔸2 ] →· y)))))
        (sym (↑ᵢ₂≡↑ᵢ₀↑ᵢ₀↑ᵢ₀ a))
        (cong₂ (λ x y → Ｆ ◇ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ x ∧· y)))
               (trans (trans (cong (λ x → sub-Res x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub، 𝕍Agent (CSub، 𝕍Data (CSub، 𝕍Agents (CSub،ₗ a)))))))
                                   (↑ᵣ₁-↑ᵣ₃≡↑⊆،＋ Γ 𝕍Agent 𝕍Agents 𝕍Data 𝕍Agent 𝕍ℝ 𝕍ℝ Δ))
                             (sub-Res-↑ᵣ،＋ Γ (⟨⟩ ، 𝕍Agents ، 𝕍Data ، 𝕍Agent ، 𝕍ℝ ، 𝕍ℝ) 𝕍Agent a (↑ᵣ₄ Δ)))
                      (sym (↑ᵣ₁-↑ᵣ₂≡↑ᵣ₄ Γ 𝕍Agents 𝕍Data 𝕍Agent 𝕍ℝ 𝕍ℝ Δ)))
               (cong₃ (recv[_⇐_⇐_]) refl refl (trans (sym (↑ᵢ₁≡↑ᵢ₀↑ᵢ₀ _)) (cong ↑ᵢ₁ (sym (↑ᵢ₂≡↑ᵢ₀↑ᵢ₀↑ᵢ₀ _))))))

synchrony-assumption-body₂ : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ) → Form (Γ ، 𝕍Data ، 𝕍Agent)
synchrony-assumption-body₂ Δ a A = (𝔸 (𝕒0 ∈ₐ ↑ₛ₁ A)) →· □ (send[ ↑ᵢ₁ a ⇒ 𝕕1 ⇒ ↑ₛ₁ A ] →· ◇↓ (↑ᵣ₁ Δ) recv[ 𝕒0 ⇐ 𝕕1 ⇐ ↑ᵢ₁ a ])

synchrony-assumption₂ : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ) → Form Γ
synchrony-assumption₂ Δ a A =
  ∀ᵢ (∀ₐ (synchrony-assumption-body₂ Δ a A))
-- 𝕕1  a0

synchrony-assumption₁-sub : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ)
                          → sub (∀ᵢ (∀ₐ (synchrony-assumption-body₁ Δ a))) (CSub،ₗ A)
                          ≡ synchrony-assumption₂ Δ a A
synchrony-assumption₁-sub {Γ} Δ a A =
  cong₃ (λ x y z → ∀ᵢ (∀ₐ ((𝔸 (𝕒0 ∈ₐ z)) →· □ (send[ x ⇒ 𝕕1 ⇒ z ] →· y))))
        (subst (λ x → sub-Agent x (CSub، 𝕍Agent (CSub، 𝕍Data (CSub،ₗ A))) ≡ ↑ᵢ₁ a)
               (sym (↑ᵢ₂≡↑⊆،＋ Γ 𝕍Agents 𝕍Data 𝕍Agent a))
               (sub-Agent-↑ᵢ،＋ Γ (⟨⟩ ، 𝕍Data ، 𝕍Agent) 𝕍Agents A (↑ᵢ₁ a)))
        (cong₂ (λ x y → Ｆ ◇ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ x ∧· y)))
               (trans (trans (cong (λ x → sub-Res x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub، 𝕍Agent (CSub، 𝕍Data (CSub،ₗ A))))))
                                   (↑ᵣ₁-↑ᵣ₂≡↑⊆،＋ Γ 𝕍Agents 𝕍Data 𝕍Agent 𝕍ℝ 𝕍ℝ Δ))
                             (sub-Res-↑ᵣ،＋ Γ (⟨⟩ ، 𝕍Data ، 𝕍Agent ، 𝕍ℝ ، 𝕍ℝ) 𝕍Agents A (↑ᵣ₃ Δ)))
                      (sym (↑ᵣ₁-↑ᵣ₁≡↑ᵣ₃ Γ 𝕍Data 𝕍Agent 𝕍ℝ 𝕍ℝ Δ)))
               (cong₃ recv[_⇐_⇐_] refl refl
                      (trans (trans (cong (λ x → sub-Agent x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub، 𝕍Agent (CSub، 𝕍Data (CSub،ₗ A))))))
                                          (↑ᵢ₁-↑ᵢ₂≡↑⊆،＋ Γ _ _ _ _ _ a))
                                    (sub-Agent-↑ᵢ،＋ Γ (⟨⟩ ، 𝕍Data ، 𝕍Agent ، 𝕍ℝ ، 𝕍ℝ) 𝕍Agents A (↑ᵢ₃ a)))
                             (↑ᵢ₃≡↑ᵢ₁↑ᵢ₁ _))))
        (sym (↑ₛ₁≡↑ₛ₀↑ₛ₀ A))

synchrony-assumption-body₃ : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ) (p : Data Γ) → Form (Γ ، 𝕍Agent)
synchrony-assumption-body₃ Δ a A p = (𝔸 (𝕒0 ∈ₐ ↑ₛ₀ A)) →· □ (send[ ↑ᵢ₀ a ⇒ ↑d₀ p ⇒ ↑ₛ₀ A ] →· ◇↓ (↑ᵣ₀ Δ) recv[ 𝕒0 ⇐ ↑d₀ p ⇐ ↑ᵢ₀ a ])

synchrony-assumption₃ : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ) (p : Data Γ) → Form Γ
synchrony-assumption₃ Δ a A p =
  ∀ₐ (synchrony-assumption-body₃ Δ a A p)
-- a0

synchrony-assumption₂-sub : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ) (p : Data Γ)
                          → sub (∀ₐ (synchrony-assumption-body₂ Δ a A)) (CSub،ₗ p)
                          ≡ synchrony-assumption₃ Δ a A p
synchrony-assumption₂-sub {Γ} Δ a A p =
  cong₃ (λ x y z → ∀ₐ ((𝔸 (𝕒0 ∈ₐ z)) →· □ (send[ x ⇒ ↑d₀ p ⇒ z ] →· y)))
        (subst (λ x → sub-Agent x (CSub، 𝕍Agent (CSub،ₗ p)) ≡ ↑ᵢ₀ a)
               (sym (↑ᵢ₁≡↑⊆،＋ _ _ _ a))
               (sub-Agent-↑ᵢ،＋ Γ (⟨⟩ ، 𝕍Agent) 𝕍Data p (↑ᵢ₀ a)))
        (cong₂ (λ x y → Ｆ ◇ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ x ∧· y)))
               (trans (trans (cong (λ x → sub-Res x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub، 𝕍Agent (CSub،ₗ p)))))
                                   (↑ᵣ₁-↑ᵣ₁≡↑⊆،＋ Γ 𝕍Data 𝕍Agent 𝕍ℝ 𝕍ℝ Δ))
                             (sub-Res-↑ᵣ،＋ Γ (⟨⟩ ، 𝕍Agent ، 𝕍ℝ ، 𝕍ℝ) 𝕍Data p (↑ᵣ₂ Δ)))
                      (sym (↑ᵣ₁-↑ᵣ₀≡↑ᵣ₂ Γ 𝕍Agent 𝕍ℝ 𝕍ℝ Δ)))
               (cong₃ recv[_⇐_⇐_] refl
                      (trans (sym (↑d₂≡↑d₀↑d₀↑d₀ p)) (↑d₂≡↑d₁↑d₀ p))
                      (trans (trans (cong (λ x → sub-Agent x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub، 𝕍Agent (CSub،ₗ p)))))
                                          (↑ᵢ₁-↑ᵢ₁≡↑⊆،＋ Γ _ _ _ _ a))
                                    (sub-Agent-↑ᵢ،＋ Γ (⟨⟩ ، 𝕍Agent ، 𝕍ℝ ، 𝕍ℝ) 𝕍Data p (↑ᵢ₂ a)))
                             (↑ᵢ₂≡↑ᵢ₁↑ᵢ₀ a))))
        (subst (λ x → sub-Agents x (CSub، 𝕍Agent (CSub،ₗ p)) ≡ ↑ₛ₀ A)
               (sym (↑ₛ₁≡↑⊆،＋ _ _ _ A))
               (sub-Agents-↑ₛ،＋ Γ (⟨⟩ ، 𝕍Agent) 𝕍Data p (↑ₛ₀ A)))

synchrony-assumption₄ : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ) (p : Data Γ) (b : Agent Γ) → Form Γ
synchrony-assumption₄ Δ a A p b = (𝔸 (b ∈ₐ A)) →· □ (send[ a ⇒ p ⇒ A ] →· ◇↓ Δ recv[ b ⇐ p ⇐ a ])

synchrony-assumption₃-sub : {Γ : Ctxt} (Δ : Res Γ) (a : Agent Γ) (A : Agents Γ) (p : Data Γ) (b : Agent Γ)
                          → sub (synchrony-assumption-body₃ Δ a A p) (CSub،ₗ b)
                          ≡ synchrony-assumption₄ Δ a A p b
synchrony-assumption₃-sub {Γ} Δ a A p b =
  cong₄ (λ x y z w → (𝔸 (b ∈ₐ x)) →· □ (send[ y ⇒ z ⇒ x ] →· w))
        (sub-Agents-↑ₛ،＋ Γ ⟨⟩ 𝕍Agent b A)
        (sub-Agent-↑ᵢ،＋ Γ ⟨⟩ 𝕍Agent b a)
        (sub-Data-↑d،＋ Γ ⟨⟩ 𝕍Agent b p)
        (cong₂ (λ x y → Ｆ ◇ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ x ∧· y)))
               (subst (λ x → sub-Res x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub،ₗ b))) ≡ ↑ᵣ₁ Δ)
                      (sym (↑ᵣ₁-↑ᵣ₀≡↑⊆،＋ _ _ _ _ Δ))
                      (sub-Res-↑ᵣ،＋ Γ (⟨⟩ ، 𝕍ℝ ، 𝕍ℝ) 𝕍Agent b (↑ᵣ₁ Δ)))
               (cong₃ recv[_⇐_⇐_]
                      (sym (↑ᵢ₁≡↑ᵢ₀↑ᵢ₀ b))
                      (trans (cong (λ x → sub-Data x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub،ₗ b))))
                                   (↑d₁-↑d₀≡↑⊆،＋ _ 𝕍Agent 𝕍ℝ 𝕍ℝ p))
                             (sub-Data-↑d،＋ Γ (⟨⟩ ، 𝕍ℝ ، 𝕍ℝ) 𝕍Agent b (↑d₁ p)))
                      (trans (cong (λ x → sub-Agent x (CSub، 𝕍ℝ (CSub، 𝕍ℝ (CSub،ₗ b))))
                                   (↑ᵢ₁-↑ᵢ₀≡↑⊆،＋ _ 𝕍Agent 𝕍ℝ 𝕍ℝ a))
                             (sub-Agent-↑ᵢ،＋ Γ (⟨⟩ ، 𝕍ℝ ، 𝕍ℝ) 𝕍Agent b (↑ᵢ₁ a)))))

relay-body : {Γ : Ctxt} → Agent Γ → Agent Γ → Agent Γ → Form (Γ ، 𝕍Data)
relay-body a b c = □ (recv[ ↑ᵢ₀ b ⇐ 𝕕0 ⇐ ↑ᵢ₀ a ] →· send[ ↑ᵢ₀ b ⇒ 𝕕0 ⇒ [ ↑ᵢ₀ c ]ₐ ])

-- if b receives a prop. p from a, then it relays it to c
relay : {Γ : Ctxt} → Agent Γ → Agent Γ → Agent Γ → Form Γ
relay a b c = ∀ᵢ (relay-body a b c)

relay₁ : {Γ : Ctxt} → Agent Γ → Agent Γ → Agent Γ → Data Γ → Form Γ
relay₁ {Γ} a b c p = □ (recv[ b ⇐ p ⇐ a ] →· send[ b ⇒ p ⇒ [ c ]ₐ ])

relay-sub : {Γ : Ctxt} (a b c : Agent Γ) (p : Data Γ)
          → sub (relay-body a b c) (CSub،ₗ p)
          ≡ relay₁ a b c p
relay-sub {Γ} a b c p =
  cong₃ (λ a b c → □ (recv[ b ⇐ p ⇐ a ] →· send[ b ⇒ p ⇒ [ c ]ₐ ]))
        (sub-Agent-↑ᵢ،＋ Γ ⟨⟩ 𝕍Data p a)
        (sub-Agent-↑ᵢ،＋ Γ ⟨⟩ 𝕍Data p b)
        (sub-Agent-↑ᵢ،＋ Γ ⟨⟩ 𝕍Data p c)

example1 : (Γ : ℂ₀) (a b c : ℂAgent Γ) (Δ r : ℂRes Γ) (p : ℂData Γ) → Rule
example1 Γ a b c Δ r p =
  rule (rseq Γ r (synchrony-assumption Δ)
        ∷ rseq Γ r (relay a b c)
        -- 'a' sends 'p' to 'b' at time 'r'
        ∷ rseq Γ r send[ a ⇒ p ⇒ [ b ]ₐ ]
        ∷ [])
       -- 'c' receives 'p' from 'b' by 'Δ ⋆ Δ'
       (rseq Γ r (◇↓ (Δ ⋆ Δ) recv[ c ⇐ p ⇐ b ]))

example1-true : (M : Model₀)
                {Γ : ℂ₀} (a b c : ℂAgent Γ) (Δ r : ℂRes Γ) (p : ℂData Γ)
              → sat-rule M (example1 Γ a b c Δ r p)
example1-true M {Γ} a b c Δ r p (hyp1 , hyp2 , hyp3 , _) = concl
  where
  a𝟙𝟙 : sat-sequent M (rseq (ℂe Γ (□ (send[ a ⇒ p ⇒ [ b ]ₐ ] →· ◇↓ Δ recv[ b ⇐ p ⇐ a ])) r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟙𝟙 = rule□L-now-sat M Γ r r (send[ a ⇒ p ⇒ [ b ]ₐ ] →· ◇↓ Δ recv[ b ⇐ p ⇐ a ]) (◇↓ Δ recv[ b ⇐ p ⇐ a ])
          (rule→L-sat M Γ (CEr r) r send[ a ⇒ p ⇒ [ b ]ₐ ] (◇↓ Δ recv[ b ⇐ p ⇐ a ]) (◇↓ Δ recv[ b ⇐ p ⇐ a ])
             (hyp3  , ruleLbl-sat M Γ (CEr r) (◇↓ Δ recv[ b ⇐ p ⇐ a ]) (lift tt) , lift tt) , lift tt)

  a𝟙𝟘 : sat-sequent M (rseq Γ r (𝔸 (b ∈ₐ [ b ]ₐ)))
  a𝟙𝟘 = λ s satΓ → lift (here refl) -- introduce a rule

  a𝟡 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₄ Δ a [ b ]ₐ p b) r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟡 = rule→L-sat M Γ (CEr r) r (𝔸 (b ∈ₐ [ b ]ₐ)) (□ (send[ a ⇒ p ⇒ [ b ]ₐ ] →· ◇↓ Δ recv[ b ⇐ p ⇐ a ])) (◇↓ Δ recv[ b ⇐ p ⇐ a ])
                 (a𝟙𝟘 , a𝟙𝟙 , lift tt)

  a𝟠 : sat-sequent M (rseq (ℂe Γ (sub (synchrony-assumption-body₃ Δ a [ b ]ₐ p) (CSub،ₗ b)) r)
                          r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟠 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ])))
             (sym (synchrony-assumption₃-sub Δ a [ b ]ₐ p b)) a𝟡

  a𝟟 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₃ Δ a [ b ]ₐ p) r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟟 = rule∀L′-sat M Γ r r 𝕌Agent (synchrony-assumption-body₃ Δ a [ b ]ₐ p)
                   (◇↓ Δ recv[ b ⇐ p ⇐ a ]) b (a𝟠 , lift tt)

  a𝟞 : sat-sequent M (rseq (ℂe Γ (sub (∀ₐ (synchrony-assumption-body₂ Δ a [ b ]ₐ)) (CSub،ₗ p)) r)
                          r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟞 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ])))
             (sym (synchrony-assumption₂-sub Δ a [ b ]ₐ p)) a𝟟

  a𝟝 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₂ Δ a [ b ]ₐ) r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟝 = rule∀L′-sat M Γ r r 𝕌Data
         (∀ₐ (synchrony-assumption-body₂ Δ a [ b ]ₐ)) (◇↓ Δ recv[ b ⇐ p ⇐ a ])
         p (a𝟞 , lift tt)

  a𝟜 : sat-sequent M (rseq (ℂe Γ (sub (∀ᵢ (∀ₐ (synchrony-assumption-body₁ Δ a))) (CSub،ₗ [ b ]ₐ)) r)
                          r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟜 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ])))
            (sym (synchrony-assumption₁-sub Δ a [ b ]ₐ)) a𝟝

  a𝟛 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₁ Δ a) r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟛 = rule∀L′-sat M Γ r r 𝕌Agents
         (∀ᵢ (∀ₐ (synchrony-assumption-body₁ Δ a))) (◇↓ Δ recv[ b ⇐ p ⇐ a ])
         [ b ]ₐ (a𝟜 , lift tt)

  a𝟚 : sat-sequent M (rseq (ℂe Γ (sub (∀ₛ (∀ᵢ (∀ₐ (synchrony-assumption-body Δ)))) (CSub،ₗ a)) r)
                          r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟚 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ recv[ b ⇐ p ⇐ a ])))
             (sym (synchrony-assumption-sub Δ a)) a𝟛

  -- from 3rd hyp by synchrony
  a𝟙 : sat-sequent M (rseq Γ r (◇↓ Δ recv[ b ⇐ p ⇐ a ]))
  a𝟙 = rule-cut-sat M Γ (CEr r) (CEr r) (◇↓ Δ recv[ b ⇐ p ⇐ a ]) (synchrony-assumption Δ)
         (hyp1 ,
          rule∀L′-sat M Γ r r 𝕌Agent (∀ₛ (∀ᵢ (∀ₐ (synchrony-assumption-body Δ)))) (◇↓ Δ recv[ b ⇐ p ⇐ a ]) a (a𝟚 , lift tt) ,
          lift tt)

  ----

  -- Now use hyp2 on 𝟙, using rule-◇↓-dist-sat to derive
  b𝟚 : sat-sequent M (rseq Γ r (relay₁ a b c p))
  b𝟚 = rule-cut-sat M Γ (CEr r) (CEr r) (relay₁ a b c p) (relay a b c)  --instantiate hyp2
         (hyp2 ,
          rule∀L′-sat M Γ r r 𝕌Data (relay-body a b c)
            (relay₁ a b c p) p
            (subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (relay₁ a b c p)))
                   (sym (relay-sub a b c p))
                   (ruleLbl-sat M Γ (CEr r) (relay₁ a b c p) (lift tt)) , lift tt) ,
          lift tt)

  b𝟙 : sat-sequent M (rseq Γ r (◇↓ Δ send[ b ⇒ p ⇒ [ c ]ₐ ]))
  b𝟙 = rule-◇↓-dist-sat M Γ r Δ recv[ b ⇐ p ⇐ a ] send[ b ⇒ p ⇒ [ c ]ₐ ] (b𝟚 , a𝟙 , lift tt)

  ----

  -- from b𝟙
  c𝟙𝟙 : sat-sequent M (rseq (ℂe Γ (□ (send[ b ⇒ p ⇒ [ c ]ₐ ] →· ◇↓ Δ recv[ c ⇐ p ⇐ b ])) r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟙𝟙 = rule-◇↓-dist-sat M (ℂe Γ (□ (send[ b ⇒ p ⇒ [ c ]ₐ ] →· ◇↓ Δ recv[ c ⇐ p ⇐ b ])) r)
         r Δ (send[ b ⇒ p ⇒ [ c ]ₐ ]) (◇↓ Δ recv[ c ⇐ p ⇐ b ])
         (ruleLbl-sat M Γ (CEr r) (□ (send[ b ⇒ p ⇒ [ c ]ₐ ] →· ◇↓ Δ recv[ c ⇐ p ⇐ b ])) (lift tt) ,
          rule-thin-sat M Γ (□ (send[ b ⇒ p ⇒ [ c ]ₐ ] →· ◇↓ Δ recv[ c ⇐ p ⇐ b ])) (CEr r) (CEr r) (◇↓ Δ send[ b ⇒ p ⇒ [ c ]ₐ ])
            (b𝟙 , lift tt) ,
          lift tt)

  c𝟙𝟘 : sat-sequent M (rseq Γ r (𝔸 (c ∈ₐ [ c ]ₐ)))
  c𝟙𝟘 = λ s satΓ → lift (here refl) -- introduce a rule

  c𝟡 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₄ Δ b [ c ]ₐ p c) r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟡 = rule→L-sat M Γ (CEr r) r (𝔸 (c ∈ₐ [ c ]ₐ)) (□ (send[ b ⇒ p ⇒ [ c ]ₐ ] →· ◇↓ Δ recv[ c ⇐ p ⇐ b ])) (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))
                 (c𝟙𝟘 , c𝟙𝟙 , lift tt)

  c𝟠 : sat-sequent M (rseq (ℂe Γ (sub (synchrony-assumption-body₃ Δ b [ c ]ₐ p) (CSub،ₗ c)) r)
                          r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟠 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))))
             (sym (synchrony-assumption₃-sub Δ b [ c ]ₐ p c)) c𝟡

  c𝟟 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₃ Δ b [ c ]ₐ p) r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟟 = rule∀L′-sat M Γ r r 𝕌Agent (synchrony-assumption-body₃ Δ b [ c ]ₐ p)
                   (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])) c (c𝟠 , lift tt)

  c𝟞 : sat-sequent M (rseq (ℂe Γ (sub (∀ₐ (synchrony-assumption-body₂ Δ b [ c ]ₐ)) (CSub،ₗ p)) r)
                          r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟞 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))))
             (sym (synchrony-assumption₂-sub Δ b [ c ]ₐ p)) c𝟟

  c𝟝 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₂ Δ b [ c ]ₐ) r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟝 = rule∀L′-sat M Γ r r 𝕌Data
         (∀ₐ (synchrony-assumption-body₂ Δ b [ c ]ₐ)) (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))
         p (c𝟞 , lift tt)

  c𝟜 : sat-sequent M (rseq (ℂe Γ (sub (∀ᵢ (∀ₐ (synchrony-assumption-body₁ Δ b))) (CSub،ₗ [ c ]ₐ)) r)
                          r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟜 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))))
            (sym (synchrony-assumption₁-sub Δ b [ c ]ₐ)) c𝟝

  c𝟛 : sat-sequent M (rseq (ℂe Γ (synchrony-assumption₁ Δ b) r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟛 = rule∀L′-sat M Γ r r 𝕌Agents
         (∀ᵢ (∀ₐ (synchrony-assumption-body₁ Δ b))) (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))
         [ c ]ₐ (c𝟜 , lift tt)

  c𝟚 : sat-sequent M (rseq (ℂe Γ (sub (∀ₛ (∀ᵢ (∀ₐ (synchrony-assumption-body Δ)))) (CSub،ₗ b)) r)
                          r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟚 = subst (λ x → sat-sequent M (rseq (ℂe Γ x r) r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))))
             (sym (synchrony-assumption-sub Δ b)) c𝟛

  -- instantiate hyp1 using b [ c ]ₐ p c and use it in combination of b₁ to derive (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ]))
  c𝟙 : sat-sequent M (rseq Γ r (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])))
  c𝟙 = rule-cut-sat M Γ (CEr r) (CEr r) (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])) (synchrony-assumption Δ)
         (hyp1 ,
          rule∀L′-sat M Γ r r 𝕌Agent (∀ₛ (∀ᵢ (∀ₐ (synchrony-assumption-body Δ)))) (◇↓ Δ (◇↓ Δ recv[ c ⇐ p ⇐ b ])) b (c𝟚 , lift tt) ,
          lift tt)

  ----

  concl : sat-sequent M (rseq Γ r (◇↓ (Δ ⋆ Δ) recv[ c ⇐ p ⇐ b ]))  -- from c𝟙
  concl = rule-◇↓-dense-sat M Γ r Δ Δ recv[ c ⇐ p ⇐ b ] (c𝟙 , lift tt)

{--
         → m ⊨ synchrony-assumption Δ
         → m ⊨ relay a b c
         → m ⊨ ↑[ p , a ⇒ [ b ]ₐ ]        -- at t
         → m ⊨ ◇↓ (Δ ⋆ Δ) ↓[ p , b ⇒ c ]  -- by t + 2Δ
example1 {Γ} m a b c Δ p ⊨s ⊨r ⊨p = 𝕀𝕍
--}

\end{code}

{--
⊨-↑-⊆₀→ {Γ} {m} {𝕒 x} {u} v h =
  λ a → subst (Model.interp m (Model.run m (Model.w m) a))
              (⟦⊆₀⟧ₐ m v x)
              (h a)
⊨-↑-⊆₀→ {Γ} {m} {F ∧· F₁} {u} v (h , q) =
  ⊨-↑-⊆₀→ {Γ} {m} {F} v h , ⊨-↑-⊆₀→ {Γ} {m} {F₁} v q
⊨-↑-⊆₀→ {Γ} {m} {F ∨· F₁} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {F →· F₁} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {¬· F} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {∀· u₁ F} {u} v h =
  λ w → {!!} --⊨-↑-⊆₀→ {Γ ، u₁} {m ≔ w} {F} v {!!}
⊨-↑-⊆₀→ {Γ} {m} {∃· u₁ F} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {x ∈ₐ x₁} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {x ∈ᵢ x₁} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {⟨ x ، x₁ ⟩∈ᵣ x₂} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {𝕂 x F} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {𝐊 x F} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {⟨ x ⟩ x₁ x₂} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {≪ x ≫ x₁ x₂ F} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {▩ x F} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {x ⊑ x₁} {u} v h = {!!}
⊨-↑-⊆₀→ {Γ} {m} {x ⊒ x₁} {u} v h = {!!}
--}

{--
→+𝕥₀≤ : {a b : Res} → a ≤ b → a + 𝕥₀ ≤ b
→+𝕥₀≤ {a} {b} h rewrite +-identityʳ a = h
--}

·-right-id : (w : 𝕎) → w · 𝟘 ≡ w
·-right-id w
  rewrite ·-sym w 𝟘
        | ·-left-id w
  = refl

·𝟘≼→ : {a b : 𝕎} → a · 𝟘 ≼ b → a ≼ b
·𝟘≼→ {a} {b} h rewrite ·-right-id a = h

→·𝟘≼ : {a b : 𝕎} → a ≼ b → a · 𝟘 ≼ b
→·𝟘≼ {a} {b} h rewrite ·-right-id a = h

·𝟘≼ : {a : 𝕎} → a · 𝟘 ≼ a
·𝟘≼ {a} rewrite ·-right-id a = ≼-refl {a}

≼·𝟘 : {a : 𝕎} → a ≼ a · 𝟘
≼·𝟘 {a} rewrite ·-right-id a = ≼-refl {a}

⊨◇ : {Γ : Ctxt} (m : Model Γ) (F : Form Γ)
   → m ⊨ ◇ F
   → ∃ (λ t' → (Model.w m) ≼ t' × ((m ≔ₜ t') ⊨ F))
⊨◇ {Γ} M F (lift t' , lift h₁ , h₂) =
  t' , (𝕀 , ⊨⊨ₜ-↑₀→ {Γ} {M} {F} (lift t') t' h₂)
  where
    𝕀𝕀 : (t t' : 𝕎) → (t · 𝟘 ≼ t') → t ≼ t'
    𝕀𝕀 t t' pₜ = ·𝟘≼→ pₜ

    𝕀 : (Model.w M) ≼ t'
    𝕀 = 𝕀𝕀 (Model.w M) t' h₁

·-s-0≡ : (w : 𝕎) → w · 𝕤 𝟘 ≡ 𝕤 w
·-s-0≡ w
  rewrite ·-sym w (𝕤 𝟘)
        | s-· 𝟘 w
        | ·-left-id (𝕤 w)
  = refl

·-s-0≼ : (w : 𝕎) → w · 𝕤 𝟘 ≼ 𝕤 w
·-s-0≼ w
  rewrite ·-s-0≡ w
  = ≼-refl {𝕤 w}

≼·-s-0 : (w : 𝕎) → 𝕤 w ≼ w · 𝕤 𝟘
≼·-s-0 w
  rewrite ·-s-0≡ w
  = ≼-refl {𝕤 w}

⊨Ｏ : {Γ : Ctxt} (m : Model Γ) (F : Form Γ)
   → m ⊨ Ｏ F
   → (m ≔ₜ (𝕤 (Model.w m))) ⊨ F
⊨Ｏ {Γ} m F h =
  ⊨⊨ₜ-↑₀→ {Γ} {m} {F} (lift (𝕤 (Model.w m))) (𝕤 (Model.w m))
    (h (lift (𝕤 (Model.w m))) (lift (·-s-0≼ (Model.w m)) , lift (≼·-s-0 (Model.w m))))

→⊨Ｏ : {Γ : Ctxt} (m : Model Γ) (F : Form Γ)
    → (m ≔ₜ (𝕤 (Model.w m))) ⊨ F
    → m ⊨ Ｏ F
→⊨Ｏ {Γ} m F h t (lift ct₁ , lift ct₂) =
  →⊨⊨ₜ-↑₀ {Γ} {m} {F} t (lower t)
    (subst (λ x → (m ≔ₜ x) ⊨ F)
           (trans (sym (·-s-0≡ (Model.w m))) (≼→≡ {(Model.w m) · 𝕤 𝟘} {lower t} ct₁ ct₂))
           h)

-- → works because the restriction is stronger in the ◇↓ operator but
-- ← can't be proved
→⊨𝐛 : {Γ : Ctxt} (m : Model Γ) (F : Form Γ)
    → m ⊨ 𝐛 F
    → ∃ (λ t' → t' ≼ Model.w m × ((m ≔ₜ t') ⊨ F))
→⊨𝐛 {Γ} M F (lift t , lift h₁ , h₂) =
  t ,
  subst (λ x → t ≼ x) (·-right-id (Model.w M)) h₁ ,
  ⊨⊨ₜ-↑₀→ {Γ} {M} {F} (lift t) t h₂

←⊨𝐛 : {Γ : Ctxt} (m : Model Γ) (F : Form Γ)
    → ∃ (λ t' → t' ≼ Model.w m × ((m ≔ₜ t') ⊨ F))
    → m ⊨ 𝐛 F
←⊨𝐛 {Γ} M F (t , h₁ , h₂) =
  lift t ,
  lift (subst (λ x → t ≼ x) (sym (·-right-id (Model.w M))) h₁) ,
  →⊨⊨ₜ-↑₀ {Γ} {M} {F} (lift t) t h₂

{--
⊨synchrony-assumption : {Γ : Ctxt} (m : Model Γ) (Δ : Res Γ)
                      → m ⊨ synchrony-assumption Δ
                      → (t : Res Γ)
                      → ⊥ -- to fix by unrolling the semantics of synchrony-assumption
⊨synchrony-assumption {Γ} m Δ ⊨s t = {!!}
--}

-- builds a set containing 1 agent
[_]ₐ : {Γ : Ctxt} → Agent Γ → Agents Γ
[ a ]ₐ = agentsL [ a ]

-- builds a set containing 2 agents
[_,_]ₐ : {Γ : Ctxt} → Agent Γ → Agent Γ → Agents Γ
[ a , b ]ₐ = agentsL (a ∷ b ∷ [])

-- if b receives a prop. p from a, then it relays it to c
relay : {Γ : Ctxt} → Agent Γ → Agent Γ → Agent Γ → Form Γ
relay a b c =
  ∀ₚ (□ (↓[ 𝕡0 , ↑ᵢ₀ a ⇒ ↑ᵢ₀ b ] →· ↑[ 𝕡0 , ↑ᵢ₀ b ⇒ [ ↑ᵢ₀ c ]ₐ ]))

use-synchrony-later : {Γ : Ctxt} (m : Model Γ) (a b : Agent Γ) (A : Agents Γ) (Δ : Res Γ)
                      (p : AtomProp Γ) (t : 𝕎)
                    → Model.w m ≼ t
                    → (⟦ A ⟧ₛ· m) (⟦ b ⟧ᵢ· m)
                    → m ⊨ synchrony-assumption Δ
                    → (m ≔ₜ t) ⊨ ↑[ p , a ⇒ A ]
                    → (m ≔ₜ t) ⊨ ◇↓ Δ ↓[ p , a ⇒ b ]
use-synchrony-later m@(model runs interp r w sub) a b A Δ p t ≼t b∈A ⊨s ⊨p
  with ⊨s (lift (⟦ a ⟧ᵢ· m)) (⟦ A ⟧ₛ· m) (lift (⟦ p ⟧ₚ· m)) (lift t) (lift (→·𝟘≼ ≼t)) ⊨p
... | t′ , ct₁ , ct₂ , C =
  t′ , ct₁ ,
  subst (λ x → Lift (lsuc 0ℓ) (lower t′ ≼ t · x))
        (sym (⟦⊆⟧ᵣ sub ⊆₀ (sub ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ Δ))
        (subst (λ x → Lift (lsuc 0ℓ) (lower t′ ≼ t · x))
               (trans (⟦⊆⟧ᵣ ((((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ t′)
                            (⊆، 𝕌Res ⊆₀)
                            (((((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ lift t) ⹁ 𝕌Res ∶ t′)
                            Sub⊆-⊆،-⊆₀
                            (↑ᵣ ⊆₀ (↑ᵣ ⊆₂ Δ)))
                      (trans (⟦⊆⟧ᵣ (((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub))
                                   ⊆₀
                                   ((((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ t′)
                                   Sub⊆-⊆₀
                                   (↑ᵣ ⊆₂ Δ))
                             (⟦⊆⟧ᵣ sub
                                   ⊆₂
                                   (((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub))
                                   Sub⊆-⊆₂
                                   Δ)))
               ct₂) ,
  λ a₀ → subst₃ (λ x y z → interp (r (lower t′) a₀) (atEvent (EvtReceive (atomPropC x) (agentC y) (agentC z))))
                (sym (⟦⊆⟧ₚ sub (λ {x} → ∈CtxtS 𝕌Res) (sub ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ p))
                (sym (⟦⊆⟧ᵢ sub (λ {x} → ∈CtxtS 𝕌Res) (sub ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ a))
                (sym (⟦⊆⟧ᵢ sub (λ {x} → ∈CtxtS 𝕌Res) (sub ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ b))
                (C (lift ((⟦ b ⟧ᵢ sub))) (lift b∈A) a₀)

-- TODO: should be derivable from use-synchrony-later
use-synchrony : {Γ : Ctxt} (m : Model Γ) (a b : Agent Γ) (A : Agents Γ) (Δ : Res Γ) (p : AtomProp Γ)
              → (⟦ A ⟧ₛ· m) (⟦ b ⟧ᵢ· m)
              → m ⊨ synchrony-assumption Δ
              → m ⊨ ↑[ p , a ⇒ A ]
              → m ⊨ ◇↓ Δ ↓[ p , a ⇒ b ]
use-synchrony m@(model runs interp r w sub) a b A Δ p b∈A ⊨s ⊨p
  with ⊨s (lift (⟦ a ⟧ᵢ· m)) (⟦ A ⟧ₛ· m) (lift (⟦ p ⟧ₚ· m)) (lift (Model.w m)) (lift ·𝟘≼) ⊨p
... | t′ , ct₁ , ct₂ , C =
  t′ , ct₁ ,
  subst (λ x → Lift (lsuc 0ℓ) (lower t′ ≼ (Model.w m) · x))
        (sym (⟦⊆⟧ᵣ (Model.subΓ m) ⊆₀ ((Model.subΓ m) ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ Δ))
        (subst (λ x → Lift (lsuc 0ℓ) (lower t′ ≼ (Model.w m) · x))
               (trans (⟦⊆⟧ᵣ ((((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ t′)
                            (⊆، 𝕌Res ⊆₀)
                            (((((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ lift w) ⹁ 𝕌Res ∶ t′)
                            Sub⊆-⊆،-⊆₀
                            (↑ᵣ ⊆₀ (↑ᵣ ⊆₂ Δ)))
                      (trans (⟦⊆⟧ᵣ (((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub))
                                   ⊆₀
                                   ((((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ t′)
                                   Sub⊆-⊆₀
                                   (↑ᵣ ⊆₂ Δ))
                             (⟦⊆⟧ᵣ (Model.subΓ m)
                                   ⊆₂
                                   (((sub ⹁ 𝕌Agent ∶ lift (⟦ a ⟧ᵢ sub)) ⹁ 𝕌Agents ∶ (⟦ A ⟧ₛ sub)) ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub))
                                   Sub⊆-⊆₂
                                   Δ)))
               ct₂) ,
  λ a₀ → subst₃ (λ x y z → interp (r (lower t′) a₀) (atEvent (EvtReceive (atomPropC x) (agentC y) (agentC z))))
                (sym (⟦⊆⟧ₚ sub ⊆₀ (sub ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ p))
                (sym (⟦⊆⟧ᵢ sub ⊆₀ (sub ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ a))
                (sym (⟦⊆⟧ᵢ sub ⊆₀ (sub ⹁ 𝕌Res ∶ t′) Sub⊆-⊆₀ b))
                (C (lift ((⟦ b ⟧ᵢ sub))) (lift b∈A) a₀)

use-relay-later : {Γ : Ctxt} (m : Model Γ) (a b c : Agent Γ) (p : AtomProp Γ) (t : 𝕎)
                → Model.w m ≼ t
                → m ⊨ relay a b c
                → (m ≔ₜ t) ⊨ ↓[ p , a ⇒ b ]
                → (m ≔ₜ t) ⊨ ↑[ p , b ⇒ [ c ]ₐ ]
use-relay-later m@(model runs interp r w sub) a b c p t ≼t ⊨r rcv =
  λ a₀ → subst₃ (λ x y z → interp (r t a₀) (atAction (ActSend (atomPropC x) (agentC y) (agentsS z))))
                refl
                (trans (⟦⊆⟧ᵢ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⊆₀ ((sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ lift t) Sub⊆-⊆₀ (↑ᵢ₀ b))
                       (⟦⊆⟧ᵢ sub ⊆₀ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) Sub⊆-⊆₀ b))
                (funExt (λ x → cong (λ z → x ∈ z ∷ [])
                                    (trans (⟦⊆⟧ᵢ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⊆₀ ((sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ lift t) Sub⊆-⊆₀ (↑ᵢ₀ c))
                                           (⟦⊆⟧ᵢ sub ⊆₀ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) Sub⊆-⊆₀ c))))
                (⊨r (lift (⟦ p ⟧ₚ· m)) (lift t) (lift (→·𝟘≼ ≼t))
                    (λ a₁ → subst₃ (λ x y z → interp (r t a₁) (atEvent (EvtReceive (atomPropC x) (agentC y) (agentC z))))
                                   refl
                                   (sym (trans (⟦⊆⟧ᵢ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⊆₀ ((sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ lift t) Sub⊆-⊆₀ (↑ᵢ₀ a))
                                               (⟦⊆⟧ᵢ sub ⊆₀ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) Sub⊆-⊆₀ a)))
                                   (sym (trans (⟦⊆⟧ᵢ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⊆₀ ((sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) ⹁ 𝕌Res ∶ lift t) Sub⊆-⊆₀ (↑ᵢ₀ b))
                                               (⟦⊆⟧ᵢ sub ⊆₀ (sub ⹁ 𝕌Prop ∶ lift (⟦ p ⟧ₚ sub)) Sub⊆-⊆₀ b)))
                                   (rcv a₁))
                    a₀)

◇↓-dist : {Γ : Ctxt} {m : Model Γ} {P Q : Form Γ} {t : Res Γ}
        → ((w : 𝕎) → Model.w m ≼ w
                   → w ≼ Model.w m · (⟦ t ⟧ᵣ· m)
                   → (m ≔ₜ w) ⊨ P → (m ≔ₜ w) ⊨ Q)
        → m ⊨ ◇↓ t P
        → m ⊨ ◇↓ t Q
◇↓-dist {Γ} {m@(model runs interp r w sub)} {P} {Q} {t} imp (lift t′ , ct₁ , ct₂ , ⊨P) =
  lift t′ , ct₁ , ct₂ ,
  →⊨⊨ₜ-↑₀ {Γ} {m} {Q} {𝕌Res} (lift t′) t′
          (imp t′
               (≼-trans ≼·𝟘 (lower ct₁))
               (≼-trans (lower ct₂)
                        (·-cong-≼ ≼-refl (subst (λ x → x ≼ (⟦ t ⟧ᵣ· m))
                                                (sym (⟦⊆⟧ᵣ sub ⊆₀ (sub ⹁ 𝕌Res ∶ lift t′) Sub⊆-⊆₀ t)) ≼-refl)))
               (⊨⊨ₜ-↑₀→ {Γ} {m} {P} {𝕌Res} (lift t′) t′ ⊨P))
 --imp t′ ? {--(+𝕥₀≤→ (lower ct₁))--} (lower ct₂) ⊨P

≔ₜ≔ₜ : {Γ : Ctxt} (m : Model Γ) (t′ t″ : 𝕎)
     → ((m ≔ₜ t′) ≔ₜ t″) ≡ (m ≔ₜ t″)
≔ₜ≔ₜ (model runs interp run w sub) t′ t″ = refl

change-model : {Γ : Ctxt} {m₁ m₂ : Model Γ} (F : Form Γ)
             → m₁ ≡ m₂
             → m₁ ⊨ F
             → m₂ ⊨ F
change-model {m₁} {m₂} F refl h = h

◇↓-density : {Γ : Ctxt} (m : Model Γ) (t t₁ t₂ : Res Γ) (P : Form Γ)
           → (⟦ t₁ ⟧ᵣ· m) · (⟦ t₂ ⟧ᵣ· m) ≼ (⟦ t ⟧ᵣ· m)
           → m ⊨ ◇↓ t₁ (◇↓ t₂ P)
           → m ⊨ ◇↓ t P
◇↓-density {Γ} m@(model runs interp r w sub) t t₁ t₂ P ≤t (lift t′ , lift ct₁ , lift ct₂ , (lift t″ , lift ct₃ , lift ct₄ , ⊨P)) =
  lift t″ ,
  lift (≼-trans ct₁ (≼-trans ≼·𝟘 ct₃)) ,
  lift (≼-trans ct₄ (≼-trans (·-cong-≼ ct₂ (subst (λ x → x ≼ (⟦ t₂ ⟧ᵣ· m)) (sym 𝕀𝕍) ≼-refl)) 𝕀)) ,
  ⊨-↑⊆→ {Γ ، 𝕌Res} {Γ ، 𝕌Res ، 𝕌Res}
        {model runs interp r t″ (sub ⹁ 𝕌Res ∶ lift t″)}
        {↑₀ P}
        ((sub ⹁ 𝕌Res ∶ lift t′) ⹁ 𝕌Res ∶ lift t″)
        (⊆، 𝕌Res ⊆₀) Sub⊆-⊆،-⊆₀ ⊨P
  where
  𝕀𝕍 : ⟦ ↑ᵣ (⊆، 𝕌Res ⊆₀) (↑ᵣ₀ t₂) ⟧ᵣ ((sub ⹁ 𝕌Res ∶ lift t′) ⹁ 𝕌Res ∶ lift t″ ) ≡ (⟦ t₂ ⟧ᵣ sub)
  𝕀𝕍 = trans (⟦⊆⟧ᵣ (sub ⹁ 𝕌Res ∶ lift t″) (⊆، 𝕌Res ⊆₀) ((sub ⹁ 𝕌Res ∶ lift t′) ⹁ 𝕌Res ∶ lift t″) Sub⊆-⊆،-⊆₀ (↑ᵣ₀ t₂))
             (⟦⊆⟧ᵣ sub ⊆₀ (sub ⹁ 𝕌Res ∶ lift t″) Sub⊆-⊆₀ t₂)

  𝕀𝕀𝕀 : ((Model.w m) · (⟦ t₁ ⟧ᵣ· m)) · (⟦ t₂ ⟧ᵣ· m) ≼ (Model.w m) · ((⟦ t₁ ⟧ᵣ· m) · (⟦ t₂ ⟧ᵣ· m))
  𝕀𝕀𝕀 = subst (λ x → x ≼ (Model.w m) · ((⟦ t₁ ⟧ᵣ· m) · (⟦ t₂ ⟧ᵣ· m)))
              (·-assoc (Model.w m) (⟦ t₁ ⟧ᵣ· m) (⟦ t₂ ⟧ᵣ· m))
              ≼-refl

  𝕀𝕀 : ((Model.w m) · (⟦ t₁ ⟧ᵣ· m)) · (⟦ t₂ ⟧ᵣ· m) ≼ (Model.w m) · (⟦ t ⟧ᵣ· m)
  𝕀𝕀 = ≼-trans 𝕀𝕀𝕀 (·-cong-≼ ≼-refl ≤t)

  𝕀 : ((Model.w m) · (⟦ ↑ᵣ₀ t₁ ⟧ᵣ· (m ≔ lift t′))) · (⟦ t₂ ⟧ᵣ· m) ≼ (Model.w m) · (⟦ ↑ᵣ₀ t ⟧ᵣ· (m ≔ lift t″))
  𝕀 = subst₂ (λ x y → (Model.w m · x) · (⟦ t₂ ⟧ᵣ· m) ≼ Model.w m · y)
             (sym (⟦⊆⟧ᵣ sub ⊆₀ (sub ⹁ 𝕌Res ∶ lift t′) Sub⊆-⊆₀ t₁))
             (sym (⟦⊆⟧ᵣ sub ⊆₀ (sub ⹁ 𝕌Res ∶ lift t″) Sub⊆-⊆₀ t))
             𝕀𝕀

⟦[]ₛ⟧ₛ : {Γ : Ctxt} (m : Model Γ) (a : Agent Γ) → (⟦ [ a ]ₐ ⟧ₛ· m) (⟦ a ⟧ᵢ· m)
⟦[]ₛ⟧ₛ {Γ} m a = here refl

example1 : {Γ : Ctxt} (m : Model Γ) (a b c : Agent Γ) (Δ : Res Γ) (p : AtomProp Γ)
         → m ⊨ synchrony-assumption Δ
         → m ⊨ relay a b c
         → m ⊨ ↑[ p , a ⇒ [ b ]ₐ ]        -- at t
         → m ⊨ ◇↓ (Δ ⋆ Δ) ↓[ p , b ⇒ c ]  -- by t + 2Δ
example1 {Γ} m a b c Δ p ⊨s ⊨r ⊨p = 𝕀𝕍
  where
  𝕀 : m ⊨ ◇↓ Δ ↓[ p , a ⇒ b ]
  𝕀 = use-synchrony m a b [ b ]ₐ Δ p (⟦[]ₛ⟧ₛ m b) ⊨s ⊨p

  𝕀𝕀 : m ⊨ ◇↓ Δ ↑[ p , b ⇒ [ c ]ₐ ]
  𝕀𝕀 = ◇↓-dist {Γ} {m} {↓[ p , a ⇒ b ]} {↑[ p , b ⇒ [ c ]ₐ ]} {Δ}
               (λ t′ ct₁ ct₂ → use-relay-later m a b c p t′ ct₁ ⊨r) 𝕀

  𝕀𝕀𝕀 : m ⊨ ◇↓ Δ (◇↓ Δ ↓[ p , b ⇒ c ])
  𝕀𝕀𝕀 = ◇↓-dist {Γ} {m} {↑[ p , b ⇒ [ c ]ₐ ]} {◇↓ Δ ↓[ p , b ⇒ c ]} {Δ}
                (λ t′ ct₁ ct₂ → use-synchrony-later m b c [ c ]ₐ Δ p t′ ct₁ (⟦[]ₛ⟧ₛ m c) ⊨s)
                𝕀𝕀

  𝕀𝕍 : m ⊨ ◇↓ (Δ ⋆ Δ) ↓[ p , b ⇒ c ]
  𝕀𝕍 = ◇↓-density m (Δ ⋆ Δ) Δ Δ ↓[ p , b ⇒ c ] ≼-refl 𝕀𝕀𝕀

-- Byzantine Reliable Broadcast

validity : {Γ : Ctxt} → Agent Γ → Agents Γ  → Form Γ
validity a A  =
  ∀ₚ (Correct (↑ᵢ₀ a) →· ↑[ 𝕡0 , (↑ᵢ₀ a) ⇒ (↑ₛ₀ A) ] →· (∃ₐ (Correct 𝕒0 →· ↓[ 𝕡1 , (↑ᵢ₁ a) ⇒ 𝕒0 ])))

validity₂ : {Γ : Ctxt} → (isBCast : DataProp) (isDel : DataProp) → Form Γ
validity₂ isBCast isDel =
  ∀ₐ (∀ᵢ (
    Correct 𝕒1
    →· (𝕕0 ∈ᵢ isBCast)
    →· ●[ 𝕒1 , 𝕕0 ]
    →· ◇ (∃ᵢ (∃ₐ (Correct 𝕒0 ∧· (𝕕1 ∈ᵢ isDel) ∧· ●[ 𝕒0 , 𝕕1 ])))))

no-duplication : {Γ : Ctxt} → Agent Γ → Agent Γ → Form Γ
no-duplication a b =
  ∀ₚ (↓[ 𝕡0 , (↑ᵢ₀ a) ⇒ (↑ᵢ₀ b) ] →· Correct (↑ᵢ₀ a) →· □ (¬· ↓[ 𝕡0 , (↑ᵢ₀ a) ⇒ (↑ᵢ₀ b) ]))

no-duplication₂ : {Γ : Ctxt} → Form Γ
no-duplication₂ =  ∀ₐ (∀ᵢ (●[ 𝕒1 , 𝕕0 ] →· Correct 𝕒1 →· Ｏ (□ (¬· ●[ 𝕒1 , 𝕕0 ]))))

integrity : {Γ : Ctxt} → Agent Γ → Agent Γ → Form Γ
integrity a b =
  ∀ₚ (Correct (↑ᵢ₀ b)
      →· ↓[ 𝕡0 , (↑ᵢ₀ a) ⇒ (↑ᵢ₀ b) ]
      →· Correct (↑ᵢ₀ a)
      →· ◇ (∃ₛ (((↑ᵢ₁ b) ∈ₐ 𝔸0) →· ↑[ 𝕡1 , (↑ᵢ₁ a) ⇒ 𝔸0 ])))

-- how to say that the sender is agent a?
integrity₂ : {Γ : Ctxt} → DataProp → DataProp → DataProp → Form Γ
integrity₂ isDel isSend isBCast =
  ∀ₐ (∀ᵢ (∀ᵢ (
     (∃ₐ (Correct 𝕒0
          ∧· ((𝕕2 ∈ᵢ isDel) →· ●[ 𝕒0 , 𝕕2 ])
          ∧· ((𝕕1 ∈ᵢ isSend) →· ●[ 𝕒3 , 𝕕1 ])
          ∧· Correct 𝕒3))
     →· ∃ᵢ (𝕕0 ∈ᵢ isBCast →· ●[ 𝕒3 , 𝕕0 ]))))

-- isDel   caputures the fact that the corresponding data is a deliver event
-- isSend  caputures the fact that the corresponding data is a send event
-- isBCast caputures the fact that the corresponding data is a broadcast event
-- sentBcast caputures the fact that the corresponding send and bcast pieces of data are for the same message
-- delBcast  caputures the fact that the corresponding deliver and bast pieces of data are for the same message
integrity₃ : {Γ : Ctxt} → DataProp → DataProp → DataProp → DataRel → DataRel → Form Γ
integrity₃ isDel isSend isBCast sentBcast delBcast =
  -- b delivers
  -- a is the sender
  ∀ₐ (∀ₐ (∀ᵢ (∀ᵢ (
    Correct 𝕒3
    →· Correct 𝕒2
    →· ⟨ 𝕕0 ، 𝕕1 ⟩∈ᵣ sentBcast
    →· 𝕕0 ∈ᵢ isSend
    →· ●[ 𝕒3 , 𝕕0 ]
    →· 𝕕1 ∈ᵢ isDel
    →· ●[ 𝕒2 , 𝕕1 ]
    →· 𝐛 (∃ᵢ ((𝕕0 ∈ᵢ isBCast)
              →· ⟨ 𝕕0 ، 𝕕2 ⟩∈ᵣ delBcast
              →· ●[ 𝕒4 , 𝕕0 ]))))))

agreement : {Γ : Ctxt} → Agent Γ → Agent Γ → Form Γ
agreement a b =
  ∀ₚ (
    ↓[ 𝕡0 , (↑ᵢ₀ a) ⇒ (↑ᵢ₀ b) ]
    →· Correct (↑ᵢ₀ b)
    →· ∀ₐ (
          Correct 𝕒0
          →· □ ↓[ 𝕡1 , (↑ᵢ₁ a) ⇒ 𝕒0 ]))

agreement₂ : {Γ : Ctxt} → DataProp → Form Γ
agreement₂ isDel =
  ∀ₐ (∀ᵢ (
    Correct 𝕒1
    →· (𝕕0 ∈ᵢ isDel)
    →· ●[ 𝕒1 , 𝕕0 ]
    →· ∀ₐ (Correct 𝕒0 →· ◇ ●[ 𝕒0 , 𝕕1 ])))

timeliness : {Γ : Ctxt} → Agent Γ → Agents Γ → Form Γ
timeliness a A =
  ∀ₚ (∃ₜ (
    ↑[ 𝕡1 , (↑ᵢ₁ a) ⇒ (↑ₛ₁ A) ]
    →· Correct (↑ᵢ₁ a)
    →· ∀ₐ ((𝕒0 ∈ₐ (↑ₛ₂ A)) →· (Correct 𝕒0 →· ◇↓ 𝕣1 (𝕒0 ∈ₐ (↑ₛ₂ A))))))

timeliness₂ : {Γ : Ctxt} → DataProp → DataProp → Form Γ
timeliness₂ isBCast isDel =
  ∃ₜ (∀ₐ (∀ᵢ (∀ᵢ (
    Correct 𝕒2
    →· (𝕕1 ∈ᵢ isBCast)
    →· (𝕕1 ∈ᵢ isDel)
    →· ●[ 𝕒2 , 𝕕1 ]
    →· (¬· ∃ₐ (Correct 𝕒0 ∧· ◇↑ 𝕣4 ●[ 𝕒0 , 𝕕1 ]))))))

-- Proof of Connectivity

-- Semantics

-- Contexts
data ℂ : Set₂
ℂtxt : ℂ → Ctxt

data ℂ where
  ℂ⟨⟩ : ℂ
  ℂe  : (c : ℂ₀) → Form (ℂtxt c) → Res (ℂtxt c) → ℂ
  ℂv  : (c : ℂ₀) → 𝕌 → ℂ

ℂtxt ℂ⟨⟩ = ⟨⟩
ℂtxt (ℂe c f t) = ℂtxt c
ℂtxt (ℂv c u) = ℂtxt c ، u

ℂRes : ℂ → Set
ℂRes c = Res (ℂtxt c)

ℂForm : ℂ → Set₂
ℂForm c = Form (ℂtxt c)

ℂModel : ℂ → Set₂
ℂModel c = Model (ℂtxt c)

ℂSub : ℂ → Set₂
ℂSub c = Sub (ℂtxt c)

ℂ⟦𝕌⟧ : ℂ → 𝕌 → Set₁
ℂ⟦𝕌⟧ c u = C⟦𝕌⟧ (ℂtxt c) u

Model₀ : Set₂
Model₀ = Model ⟨⟩

record Sequent : Set₂ where
  constructor seq
  field
    Δ : ℂ
    T : ℂRes Δ
    C : ℂForm Δ

record Rule : Set₂ where
  constructor rule
  field
    Premises   : List Sequent
    -- Premises : List (Form × Res)
    Conclusion : Sequent

sat-ctxt : (c : ℂ₀) (M : Model (ℂtxt c)) → Set₂
sat-ctxt ℂ⟨⟩ M = Lift _ ⊤
sat-ctxt (ℂe c f t) M = sat-ctxt c M × (M ≔ₜ (⟦ t ⟧ᵣ· M)) ⊨ f
sat-ctxt (ℂv c u) M = sat-ctxt c (Model،→ M)

sat-sequent : (M : Model₀) (s : Sequent) → Set₂
sat-sequent M (seq Δ 𝕋 C) =
    (s : ℂSub Δ)
  → (sat-ctxt Δ (M ≔ₛ s))
  → ((M ≔ₛ s) ≔ₜ (⟦ 𝕋 ⟧ᵣ s)) ⊨ C

sat-sequents : (M : Model₀) (l : List Sequent) → Set₂
sat-sequents M [] = Lift _ ⊤
sat-sequents M (s ∷ l) = sat-sequent M s × sat-sequents M l

sat-rule : (M : Model₀) (r : Rule) → Set₂
sat-rule M (rule Premises Conclusion) = sat-sequents M Premises → sat-sequent M Conclusion

-- Propositional logic
rule∧I : (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ) → Rule
rule∧I Γ r A B =
  rule (seq Γ r A ∷ seq Γ r B ∷ [])
       (seq Γ r (A ∧· B))

rule∧I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ)
           → sat-rule M (rule∧I Γ r A B)
rule∧I-sat M Γ r A B (satA , satB , _) s satΓ = (satA s satΓ) , (satB s satΓ)
--  satA s satΓ , satB s satΓ

rule∨Iₗ : (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ) → Rule
rule∨Iₗ Γ r A B =
  rule [ seq Γ r A ]
       (seq Γ r (A ∨· B))

rule∨Iₗ-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ)
            → sat-rule M (rule∨Iₗ Γ r A B)
rule∨Iₗ-sat M Γ r A B (satA , _) s satΓ = inj₁ (satA s satΓ)

rule∨Iᵣ : (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ) → Rule
rule∨Iᵣ Γ r A B =
  rule [ seq Γ r B ]
       (seq Γ r (A ∨· B))

rule∨Iᵣ-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ)
            → sat-rule M (rule∨Iᵣ Γ r A B)
rule∨Iᵣ-sat M Γ r A B (satB , _) s satΓ = inj₂ (satB s satΓ)

rule→I : (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ) → Rule
rule→I Γ r A B =
  rule [ seq (ℂe Γ A r) r B ]
       (seq Γ r (A →· B))

rule→I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ)
           → sat-rule M (rule→I Γ r A B)
rule→I-sat M Γ r A B (satB , _) s satΓ a =
  satB s (satΓ , a)

rule¬I : (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ) → Rule
rule¬I Γ r A =
  rule [ seq (ℂe Γ A r) r ⊥· ]
       (seq Γ r (¬· A))

rule¬I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ)
           → sat-rule M (rule¬I Γ r A)
rule¬I-sat M Γ r A (sat⊥ , _) s satΓ a =
  lower (sat⊥ s (satΓ , a))

-- Predicate logic

--      Γ, u ⊢[R] A
--  ------------------
--     Γ ⊢[R] ∀ u A 

rule∀I : (Γ : ℂ₀) (r : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ u)) → Rule
rule∀I Γ r u A =
  rule [ seq (ℂv Γ u) (↑ᵣ₀ r) A ]
       (seq Γ r (∀· u A))

rule∀I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ u))
           → sat-rule M (rule∀I Γ r u A)
rule∀I-sat M Γ r u A (satA , _) s satΓ v =
  subst (λ x → x ⊨ A) (≔-≔ₜ (M ≔ₛ s) v (⟦ r ⟧ᵣ s)) c
  where
  c′ : ((M ≔ₛ (s ⹁ u ∶ v)) ≔ₜ (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ u ∶ v))) ⊨ A
  c′ = satA (s ⹁ u ∶ v) satΓ

  c : (((M ≔ₛ s) ≔ v) ≔ₜ (⟦ r ⟧ᵣ s)) ⊨ A
  c = subst (λ x → (((M ≔ₛ s) ≔ v) ≔ₜ x) ⊨ A) (⟦⊆⟧ᵣ s ⊆₀ (s ⹁ u ∶ v) Sub⊆-⊆₀ r) c′

-- Temporal logic

--   Γ ⊢[t] A
-- ------------
-- Γ ⊢[T] ▩[t]A
rule▩ : (Γ : ℂ₀) (T t : ℂRes Γ) (A : ℂForm Γ) → Rule
rule▩ Γ T t A =
  rule (seq Γ t A ∷ [])
       (seq Γ T (▩ t A ))

rule▩-sat : (M : Model₀) (Γ : ℂ₀) (T t : ℂRes Γ) (A : ℂForm Γ)
          → sat-rule M (rule▩ Γ T t A)
rule▩-sat M Γ T t A (satA , _) s satΓ = satA s satΓ

rule⊑ : (Γ : ℂ₀) (T t₁ t₂ : ℂRes Γ) → Rule
rule⊑ Γ T t₁ t₂ =
  rule []
       (seq Γ T (t₁ ⊑ t₂))

{--
-- Question: could we add such side conditions to the rules directly?
--
-- -------------- (T + t₁ ≤ t₂)
-- Γ ⊢[T] t₁ ⊑ t₂
rule⊑-sat : (M : Model₀) (Γ : ℂ₀) (T t₁ t₂ : ℂRes Γ)
-- TO FIX
--          → (⟦ T ⟧ᵣ· M) · (⟦ t₁ ⟧ᵣ· M) ≼ (⟦ t₂ ⟧ᵣ· M) -- side-condition
          → sat-rule M (rule⊑ Γ T t₁ t₂)
rule⊑-sat M Γ T t₁ t₂ hyps = {!!}
--}

--
-- -----------------
-- Γ ⊢[T] 𝟎 ⊑ T · t
rule⊑₀ : (Γ : ℂ₀) (T t : ℂRes Γ) → Rule
rule⊑₀ Γ T t =
  rule []
       (seq Γ T (𝟎 ⊑ (T ⋆ t)))

rule⊑₀-sat : (M : Model₀) (Γ : ℂ₀) (T t : ℂRes Γ)
          → sat-rule M (rule⊑₀ Γ T t)
rule⊑₀-sat M Γ T t _ s satΓ =
  lift c
  where
  c : (⟦ T ⟧ᵣ s) · 𝟘 ≼ (⟦ T ⟧ᵣ s) · (⟦ t ⟧ᵣ s)
  c = ·-cong-≼ ≼-refl {!!}

--   Γ ⊢[T] t₁ ⊑ T · t    Γ ⊢[T] t ⊑ t₂
-- --------------------------------------
--           Γ ⊢[T] t₁ ⊑ t₂
rule⊑ₜ : (Γ : ℂ₀) (T t₁ t₂ t : ℂRes Γ) → Rule
rule⊑ₜ Γ T t₁ t₂ t =
  rule (seq Γ T (t₁ ⊑ (T ⋆ t)) ∷ seq Γ T (t ⊑ t₂) ∷ [])
       (seq Γ T (t₁ ⊑  t₂))

rule⊑ₜ-sat : (M : Model₀) (Γ : ℂ₀) (T t₁ t₂ t : ℂRes Γ)
          → sat-rule M (rule⊑ₜ Γ T t₁ t₂ t)
rule⊑ₜ-sat M Γ T t₁ t₂ t (satL , (satR , _ )) s satΓ =
  lift c
  where
  c : (⟦ T ⟧ᵣ s) · (⟦ t₁ ⟧ᵣ s) ≼ (⟦ t₂ ⟧ᵣ s)
  c = ≼-trans (lower (satL s satΓ)) (lower (satR s satΓ))

-- LEFT RULES

-- Propositional

--       Γ,Aᴿ,Bᴿ ⊢[T] C
-- ------------------------
--    Γ,(A ∧· B)ᴿ ⊢[T] C

rule∧-L : (Γ : ℂ₀) (T R : ℂRes Γ) (A B C : ℂForm Γ) → Rule
rule∧-L Γ T R A B C =
  rule (seq (ℂe (ℂe Γ A R) B R) T C ∷ [])
       (seq (ℂe Γ (A ∧· B) R) T C)

rule∧L-sat : (M : Model₀) (Γ : ℂ₀) (t r : ℂRes Γ) (A B C : ℂForm Γ)
             → sat-rule M (rule∧-L Γ t r A B C)
rule∧L-sat M Γ t r A B C (satC , _ ) s (satΓ , satA , satB) = satC s ((satΓ , satA) , satB)

--   Γ,Aᴿ ⊢[T] C     Γ,Bᴿ ⊢[T] C
-- --------------------------------
--       Γ,(A ∨ B)ᴿ ⊢[T] C

rule∨-L :  (Γ : ℂ₀) (T R : ℂRes Γ) (A B C : ℂForm Γ) → Rule
rule∨-L Γ T R A B C =
  rule (seq (ℂe Γ A R) T C ∷ (seq (ℂe Γ B R) T C ∷ []))
       (seq (ℂe Γ (A ∨· B) R) T C)

rule∨L-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (A B C : ℂForm Γ)
           → sat-rule M (rule∨-L Γ T R A B C)
rule∨L-sat M Γ T R A B C (satwA , satwB , _) s (satΓ , inj₁ satA) = satwA s (satΓ , satA)
rule∨L-sat M Γ T R A B C (satwA , satwB , _) s (satΓ , inj₂ satB) = satwB s (satΓ , satB)

--   Γ,(¬A)ᴿ ⊢[R] A
-- ------------------
--   Γ,(¬A)ᴿ ⊢[T] B

rule¬-L : (Γ : ℂ₀) (T R : ℂRes Γ) (A B : ℂForm Γ) → Rule
rule¬-L Γ T R A B =
  rule (seq (ℂe Γ (¬· A) R) R A ∷ [])
       (seq (ℂe Γ (¬· A) R) T B)

rule¬L-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (A B : ℂForm Γ)
             → sat-rule M (rule¬-L Γ T R A B)
rule¬L-sat M Γ T R A B (satA , _) s (satΓ , sat¬) = ⊥-elim (sat¬ (satA s (satΓ , sat¬)))

-- Temporal

--   Γ,A ᵗ ⊢[T] B
-- -----------------
--  Γ,(■t A) ᴿ ⊢[T] B

rule■-L : (Γ : ℂ₀) (T t R : ℂRes Γ) (A B : ℂForm Γ) → Rule
rule■-L Γ T t R A B =
  rule (seq (ℂe Γ A t) T B ∷ [] )
       (seq (ℂe Γ (▩ t A) R) T B)

rule■L-sat : (M : Model₀) (Γ : ℂ₀) (T t R : ℂRes Γ) (A B : ℂForm Γ)
             → sat-rule M (rule■-L Γ T t R A B)
rule■L-sat M Γ  T t R A B (satB , _) s (satΓ , satA) = satB s (satΓ , satA)

--   Γ,(t₁ ⊑ (R ⋆ t))ᴿ,(t ⊑ t₂)ᴿ ⊢[T] A
-- --------------------------------------
--          Γ,(t₁ ⊑ t₂)ᴿ ⊢[T] A


--   Γ,(𝕥₀ ⊑ (R ⋆ t))ᴿ ⊢[T] A
-- ----------------------------
--         Γ ⊢[T] A

-- Predicate

{--
close : {u : 𝕌} {Γ : Ctxt} (v : C⟦𝕌⟧ Γ u) (s : Sub Γ) → ⟦𝕌⟧ u
close v s = {!!}

sat∀A-σA₁ : (Γ : Ctxt) {m : Model Γ} {u : 𝕌}
            (A : Form (Γ ، u))
            (v : C⟦𝕌⟧ Γ u)
--            {σ : CSub Δ Γ}
--          → ((v : C⟦𝕌⟧ Γ u) → (m ≔ v) ⊨ A)
          → (m ≔ (close v (Model.subΓ m))) ⊨ A
          → m ⊨ sub A (CSub،ₗ v) --σ
--          → (m ≔ σ) ⊨ A
--          → m ⊨ sub A σ
sat∀A-σA₁ = {!!}
--}

{--
wk : {u : 𝕌} {Γ : Ctxt} (v : ⟦𝕌⟧ u) → C⟦𝕌⟧ Γ u
wk {𝕌Agent}  {Γ} (lift v) = lift (agentC v)
wk {𝕌Agents} {Γ} v        = agentsS v
wk {𝕌Res}    {Γ} (lift v) = lift {!!}
wk {𝕌Prop}   {Γ} (lift v) = lift (atomPropC v)
wk {𝕌Data}   {Γ} (lift v) = lift (dataC v)
--}

{--
-- Δ ⊆ Γ
-- GSuc : Δ → Δ + [t₁ : u₁, t₂ : u₂] = Γ
-- CSub:
--   x : Δ  → Δ - return x
--   x : u₁ → Δ - return t₁ (closed so its variables are in Δ)
--   x : u₂ → Δ - return t₂ (closed so its variables are in Δ)
G→C : {Δ Γ : Ctxt} → GSub Δ Γ → CSub Γ Δ
G→C {Δ} {.Δ} ● {u} i = CSub-var i
G→C {Δ} {.(_ ، u₁)} (s ⹁ u₁ ∶ v) {.u₁} (∈Ctxt0 _) = {!!} --v
G→C {Δ} {.(_ ، u₁)} (s ⹁ u₁ ∶ v) {u} (∈CtxtS .u₁ i) = G→C s i
--}

{--
-- Δ ⊆ Γ
sat∀A-σA₂ : (Γ Δ : Ctxt) {m : Model Δ}
            (A : Form Γ)
            (σ : GSub Δ Γ)
          → (m ≔= σ) ⊨ A
          → m ⊨ sub A (G→C σ)
sat∀A-σA₂ Γ Δ {m} (𝕒 x) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} ⊤· σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (A ∧· A₁) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (A ∨· A₁) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (A →· A₁) σ h =
  λ x → sat∀A-σA₂ Γ Δ {m} A₁ σ {!!}
sat∀A-σA₂ Γ Δ {m} (¬· A) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (∀· u₁ A) σ h v =
  {!!} -- from h₃
  where
  h₁ : ((m ≔= σ) ≔ v) ⊨ A
  h₁ = h v

  h₂ : (m ≔= (σ ⹁ u₁ ∶ v)) ⊨ A
  h₂ = {!!} -- from h₁

  h₃ : m ⊨ sub A (G→C (σ ⹁ u₁ ∶ v))
  h₃ = sat∀A-σA₂ (Γ ، u₁) Δ A (σ ⹁ u₁ ∶ v) h₂
sat∀A-σA₂ Γ Δ {m} (∃· u₁ A) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (x ∈ₐ x₁) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (x ∈ᵢ x₁) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (⟨ x ، x₁ ⟩∈ᵣ x₂) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (𝕂 x A) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (𝐊 x A) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (⟨ x ⟩ x₁ x₂) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (≪ x ≫ x₁ x₂ A) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (▩ x A) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (x ⊑ x₁) σ h = {!!}
sat∀A-σA₂ Γ Δ {m} (x ⊒ x₁) σ h = {!!}
--}

{--
sat∀A-σA : (Γ : ℂ₀) {M : Model(ℂtxt Γ)} {u : 𝕌} (A : ℂForm (ℂv Γ u)) {σ : CSub (ℂtxt (ℂv Γ u)) (ℂtxt Γ)}
           → M ⊨ ∀· u A
           → M ⊨ sub A σ
sat∀A-σA Γ {M} {u} (𝕒 x) {σ} sat∀ a = {!!}
sat∀A-σA Γ {M} {u} ⊤· {σ} sat∀ = sat∀ {!!}
sat∀A-σA Γ {M} {u} ⊥· {σ} sat∀ = sat∀ {!!}
sat∀A-σA Γ {M} {u} (A ∧· A₁) {σ} sat∀ =
                          (sat∀A-σA Γ A λ v → let a , b = sat∀ v in a) ,
                          sat∀A-σA Γ A₁ λ v → let a , b = sat∀ v in b
sat∀A-σA Γ {M} {u} (A ∨· A₁) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (A →· A₁) {σ} sat∀ satA = sat∀A-σA Γ A₁ λ v → sat∀ v {!satA!}
sat∀A-σA Γ {M} {u} (¬· A) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (∀· u₁ A) {σ} sat∀ v = sat∀A-σA Γ (sub {!A!} {!σ!}) (λ v₁ → {!!})
sat∀A-σA Γ {M} {u} (∃· u₁ A) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (x ∈ₐ x₁) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (x ∈ᵢ x₁) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (⟨ x ، x₁ ⟩∈ᵣ x₂) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (𝕂 x A) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (𝐊 x A) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (⟨ x ⟩ x₁ x₂) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (≪ x ≫ x₁ x₂ A) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (▩ x A) {σ} sat∀ = sat∀A-σA Γ A {!sat∀!}
sat∀A-σA Γ {M} {u} (x ⊑ x₁) {σ} sat∀ = {!!}
sat∀A-σA Γ {M} {u} (x ⊒ x₁) {σ} sat∀ = lift {!sat∀!}
--}

{--
G→C : {Γ Δ : Ctxt} {u : 𝕌}
      (s : GSub (Γ ، u) Δ)
      (v : C⟦𝕌⟧ Γ u)
    → CSub Δ Γ
G→C {Γ} {.(Γ ، u)} {u} ● v {.u} (∈Ctxt0 .Γ) = v
G→C {Γ} {.(Γ ، u)} {u} ● v {w} (∈CtxtS .u i) = CSub-var i
G→C {Γ} {.(_ ، u₁)} {u} (s ⹁ u₁ ∶ v₁) v {.u₁} (∈Ctxt0 _) = {!!}
G→C {Γ} {.(_ ، u₁)} {u} (s ⹁ u₁ ∶ v₁) v {w} (∈CtxtS .u₁ i) = G→C s v i
--}

{--
  sat∀A-σA Γ {m} {u} (𝕒 x) v h = {!!}
  sat∀A-σA Γ {m} {u} ⊤· v h = {!!}
  sat∀A-σA Γ {m} {u} (A ∧· A₁) v h = {!!}
  sat∀A-σA Γ {m} {u} (A ∨· A₁) v h = {!!}
  sat∀A-σA Γ {m} {u} (A →· A₁) v h q =
    sat∀A-σA Γ A₁ v (h (sat∀A-σA-rev Γ A v q))
  sat∀A-σA Γ {m} {u} (¬· A) v h = {!!}
  sat∀A-σA Γ {m} {u} (∀· u₁ A) v h w =
    {!!} -- from h₄
    where
    h₁ : ((m ≔ ⟦ v ⟧c· m) ≔ w) ⊨ A
    h₁ = h w

    h₂ : ((m ≔ w) ≔ ⟦ v ⟧c· m) ⊨ ↑swap A
    h₂ = {!!} -- from h₂

    h₃ : ((m ≔ w) ≔ ⟦ C⟦𝕌⟧⊆ ⊆₀ v ⟧c· (m ≔ w)) ⊨ ↑swap A
    h₃ = {!!} -- from h₃

    h₄ : (m ≔ w) ⊨ sub (↑swap A) (CSub،ₗ (C⟦𝕌⟧⊆ ⊆₀ v))
    h₄ = {!!}
  sat∀A-σA Γ {m} {u} (∃· u₁ A) v h = {!!}
  sat∀A-σA Γ {m} {u} (x ∈ₐ x₁) v h = {!!}
  sat∀A-σA Γ {m} {u} (x ∈ᵢ x₁) v h = {!!}
  sat∀A-σA Γ {m} {u} (⟨ x ، x₁ ⟩∈ᵣ x₂) v h = {!!}
  sat∀A-σA Γ {m} {u} (𝕂 x A) v h = {!!}
  sat∀A-σA Γ {m} {u} (𝐊 x A) v h = {!!}
  sat∀A-σA Γ {m} {u} (⟨ x ⟩ x₁ x₂) v h = {!!}
  sat∀A-σA Γ {m} {u} (≪ x ≫ x₁ x₂ A) v h = {!!}
  sat∀A-σA Γ {m} {u} (▩ x A) v h = {!!}
  sat∀A-σA Γ {m} {u} (x ⊑ x₁) v h = {!!}
  sat∀A-σA Γ {m} {u} (x ⊒ x₁) v h = {!!}

  sat∀A-σA-rev : (Γ : Ctxt) {m : Model Γ} {u : 𝕌}
                 (A : Form (Γ ، u))
                 (v : C⟦𝕌⟧ Γ u)
               → m ⊨ sub A (CSub،ₗ v)
               → (m ≔ ⟦ v ⟧c· m) ⊨ A
  sat∀A-σA-rev Γ {m} {u} A v h = {!!}
--}

rule∀L-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ u)) (B : ℂForm Γ) (v : ℂ⟦𝕌⟧ Γ u)
           → sat-rule M (rule∀-L Γ T R u A B v)
rule∀L-sat M Γ T R u A B v (satB , _) s (satΓ , sat∀A) =
  satB s ((satΓ , sat∀A) , ≔→sub (ℂtxt Γ) A v h) --sat∀A-σA Γ A sat∀A)
  where
  h : (((M ≔ₛ s) ≔ₜ (⟦ R ⟧ᵣ· (M ≔ₛ s))) ≔ (⟦ v ⟧c s)) ⊨ A
  h = sat∀A (⟦ v ⟧c s)

--    ???
-- -------------------------
--    Γ,(∃ u A)ᴿ ⊢[T] B

rule∃-L : (Γ : ℂ₀) (T R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ u)) (B : ℂForm Γ) (σ : CSub (ℂtxt (ℂv Γ u)) (ℂtxt Γ)) → Rule
rule∃-L Γ T R u A B σ =
  rule (seq (ℂe (ℂv Γ  u) A (↑ᵣ₀ R)) (↑ᵣ₀ T) (↑₀ B) ∷ [])
       (seq (ℂe Γ (∃· u A) R) T B)

rule∃L-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ u)) (B : ℂForm Γ) (σ : CSub (ℂtxt (ℂv Γ u)) (ℂtxt Γ))
             → sat-rule M (rule∃-L Γ T R u A B σ)
rule∃L-sat M Γ T R u A B σ (satB , _) s (satΓ , sat∃) = {!!}
--satB s (satΓ , {!!})

\end{code}
