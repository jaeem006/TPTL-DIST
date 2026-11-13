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

module RulesClassical(𝔻 : Set)
                     (W : World)
                     (EM : ExcludedMiddle (lsuc(0ℓ)))
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open import RulesMisc(𝔻)(W)
open import RulesProp(𝔻)(W)
open import RulesTemp(𝔻)(W)

open World.World W


LEM : {Γ : Ctxt} (A : Form Γ) → Form Γ
LEM {Γ} A = A ∨· (¬· A)

--
-- -------------------
--   Γ ⊢[R] A ∨ ¬ A

rule-classical : (Γ : ℂ₀) (R : ℂRes Γ) (A : ℂForm Γ) → Rule
rule-classical Γ R A =
  rule []
       (rseq Γ R (LEM A))

abstract
  rule-classical-sat : (M : Model₀) (Γ : ℂ₀) (R : ℂRes Γ) (A : ℂForm Γ)
                     → sat-rule M (rule-classical Γ R A)
  rule-classical-sat M Γ R A _ s satΓ with EM {((M ≔ₛ s) ≔ₜ (⟦ R ⟧ᵣ s)) ⊨ A}
  ... | yes p = inj₁ p
  ... | no p = inj₂ λ k → lift (p k)

--    Γ, □ A @ r, A @ r₁ ⊢[T] C    Γ ⊢[T] r ⊑ r₁
-- ------------------------------------------------
--               Γ, □ A @ r ⊢[T] C

rule□L : (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule□L Γ r r₁ T A C =
  rule (rseq (ℂe (ℂe Γ (□ A) r) A r₁) T C
        ∷ rseq Γ T (r ⊑ r₁)
        ∷ [])
       (rseq (ℂe Γ (□ A) r) T C)

abstract
  rule□L-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ)
             → sat-rule M (rule□L Γ r r₁ T A C)
  rule□L-sat M Γ r r₁ T A C (sat1 , sat2 , _) =
    rule-cut-sat M (ℂe Γ (□ A) r) (CEr T) (CEr r₁) C A                      -- we cut in A@r₁ and so are left with having to prove that formula
      (rule-cut-sat M (ℂe Γ (□ A) r) (CEr r₁) (CEr r₁) A (A ∨· (¬· A))      -- we go by cases on whether A@r₁ is true or not using classical logic
        (rule-classical-sat M (ℂe Γ (□ A) r) r₁ A (lift tt) ,
         rule∨E-sat M (ℂe Γ (□ A) r) r₁ (CEr r₁) A (¬· A) A
           (ruleLbl-sat M (ℂe Γ (□ A) r) (CEr r₁) A (lift tt) ,       -- if A@r₁ is true we can directly conclude
            𝕀 ,                                                 -- if A@r₁ is false, we have to work harder
            lift tt) ,
         lift tt) ,
       sat1 ,
       lift tt)
    where
    𝕀𝕀𝕀 : sat-sequent M (rseq (ℂe Γ (¬· A) r₁) r (◇ (¬· A)))
    𝕀𝕀𝕀 = rule◇R-sat M (ℂe Γ (¬· A) r₁) r r₁ (¬· A)
            (rule-thin-sat M Γ (¬· A) (CEr r₁) (CEr r) (r ⊑ r₁) (sat2 , (lift tt)) ,
             (ruleLbl-sat M Γ (CEr r₁) (¬· A) (lift tt)) ,
             lift tt)

    𝕀𝕀 : sat-sequent M (rseq (ℂe Γ (¬· A) r₁) (↑ᵣ ⊆-refl r) (◇ (¬· (↑ ⊆-refl A))))
    𝕀𝕀 = subst₂ (λ x y → sat-sequent M (rseq (ℂe Γ (¬· A) r₁) x (◇ (¬· y)))) (sym (↑ᵣ⊆-refl r)) (sym (↑⊆-refl A)) 𝕀𝕀𝕀

    𝕀 : sat-sequent M (rseq (ℂe (ℂe Γ (□ A) r) (¬· A) r₁) r₁ A)
    𝕀 = rule¬E-sat M Γ (ℂe ℂ⟨⟩ (¬· A) r₁) r (◇ (¬· A)) (CEr r₁) A (𝕀𝕀 , lift tt)

--    Γ, A @ r ⊢[T] C
-- -----------------------
--    Γ, □ A @ r ⊢[T] C

rule□L-now : (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule□L-now Γ r T A C =
  rule (rseq (ℂe Γ A r) T C
        ∷ [])
       (rseq (ℂe Γ (□ A) r) T C)

rule□L-now-sat : (M : Model₀) (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ)
               → sat-rule M (rule□L-now Γ r T A C)
rule□L-now-sat M Γ r T A C (sat1 , _) =
  rule□L-sat M Γ r r T A C
    (rule-thin1-sat M Γ (□ A) A (CEr r) (CEr r) (CEr T) C (sat1 , lift tt) ,
     rule⊑-refl-sat M Γ r T (lift tt) ,
     lift tt)

-- Similar to rule□L but thins the □ A hyp:
--
--    Γ, A @ r₁ ⊢[T] C    Γ ⊢[T] r ⊑ r₁
-- ---------------------------------------
--           Γ, □ A @ r ⊢[T] C

rule□L′ : (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule□L′ Γ r r₁ T A C =
  rule (rseq (ℂe Γ A r₁) T C
        ∷ rseq Γ T (r ⊑ r₁)
        ∷ [])
       (rseq (ℂe Γ (□ A) r) T C)

rule□L′-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ)
            → sat-rule M (rule□L′ Γ r r₁ T A C)
rule□L′-sat M Γ r r₁ T A C (sat1 , sat2 , _) =
  rule□L-sat M Γ r r₁ T A C
    (rule-thin1-sat M Γ (□ A) A (CEr r) (CEr r₁) (CEr T) C (sat1 , lift tt) ,
     sat2 ,
     lift tt)


-- Derivable:
--    Γ, A , ¬· B ⊢[T] C
-- ---------------------------
--    Γ, ¬· (A →· B) ⊢[T] C

rule¬→L : (Γ : ℂ₀) (T R : ℂRes Γ) (A B C : ℂForm Γ) → Rule
rule¬→L Γ T R A B C =
  rule (rseq (ℂe (ℂe Γ A R) (¬· B) R) T C ∷ [])
       (rseq (ℂe Γ (¬· (A →· B)) R) T C)

rule¬→L-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (A B C : ℂForm Γ)
            → sat-rule M (rule¬→L Γ T R A B C)
rule¬→L-sat M Γ T R A B C (satB , _) =
  rule-cut-sat M (ℂe Γ (¬· (A →· B)) R) (CEr T) (CEr R) C (A ∨· (¬· A))
    (rule-classical-sat M (ℂe Γ (¬· (A →· B)) R) R A (lift tt) ,
     rule∨E-sat M (ℂe Γ (¬· (A →· B)) R) R (CEr T) A (¬· A) C
       (rule-cut-sat M (ℂe (ℂe Γ (¬· (A →· B)) R) A R) (CEr T) (CEr R) C (¬· B)
         (rule¬I-sat M (ℂe (ℂe Γ (¬· (A →· B)) R) A R) R B
           (rule¬E-sat M Γ (ℂe (ℂe ℂ⟨⟩ A R) B R) R (A →· B) (CEr R) ⊥·
             (subst₂ (λ x y → sat-sequent M (rseq (ℂe (ℂe Γ A R) B R) x y))
                     (sym (↑ᵣ⊆-refl R))
                     (sym (↑⊆-refl (A →· B)))
                     (rule→I-sat M (ℂe (ℂe Γ A R) B R) R A B
                       (rule-thin-sat M (ℂe (ℂe Γ A R) B R) A (CEr R) (CEr R) B (ruleLbl-sat M (ℂe Γ A R) (CEr R) B (lift tt) , lift tt) ,
                        lift tt)) ,
              lift tt) ,
            lift tt) ,
          rule-thin-gen-sat M Γ (ℂe (ℂe ℂ⟨⟩ A R) (¬· B) R) (¬· (A →· B)) (CEr R) (CEr T) C (satB , lift tt) ,
          lift tt) ,
        rule¬E-sat M Γ (ℂe ℂ⟨⟩ (¬· A) R) R (A →· B) (CEr T) C
          (subst₂ (λ x y → sat-sequent M (rseq (ℂe Γ (¬· A) R) x y))
                  (sym (↑ᵣ⊆-refl R))
                  (sym (↑⊆-refl (A →· B)))
                  (rule→I-sat M (ℂe Γ (¬· A) R) R A B
                    (rule¬E-sat M Γ (ℂe ℂ⟨⟩ A R) R A (CEr R) B
                      (subst₂ (λ x y → sat-sequent M (rseq (ℂe Γ A R) x y)) (sym (↑ᵣ⊆-refl R)) (sym (↑⊆-refl A))
                              (ruleLbl-sat M Γ (CEr R) A (lift tt)) ,
                       lift tt) ,
                     lift tt)) ,
           lift tt) ,
        lift tt) ,
     lift tt)

--    Γ, A @ t ⊢[R] C
-- -----------------------
--    Γ, □↓ r A @ t ⊢[R] C

□↓L-now : (Γ : ℂ₀) (t R r : ℂRes Γ) (A C : ℂForm Γ) → Rule
□↓L-now Γ t R r A C =
  rule [ rseq (ℂe Γ A t) R C ]
       (rseq (ℂe Γ (□↓ r A) t) R C)

□↓L-now-sat : (M : Model₀) (Γ : ℂ₀) (t R r : ℂRes Γ) (A C : ℂForm Γ)
            → sat-rule M (□↓L-now Γ t R r A C)
□↓L-now-sat M Γ t R r A C (sat1 , _) =
  ruleＦL-sat M Γ t (CEr R) (□ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r →· ↑₁ A))) C (𝕀 , lift tt)
  where
  s′ : CSub (ℂtxt Γ ، 𝕍ℝ) (ℂtxt Γ)
  s′ = CSub،ₗ t

  s : CSub ((ℂtxt Γ ، 𝕍ℝ) ، 𝕍ℝ) (ℂtxt Γ ، 𝕍ℝ)
  s = CSub، 𝕍ℝ (CSub،ₗ t)

  𝕀𝕍 : sat-sequent M (rseq (ℂe Γ (t ⊑ t ⋆ r →· A) t) R C)
  𝕀𝕍 = rule→L-sat M Γ (CEr R) t (t ⊑ t ⋆ r) A C
         (rule＝-⊑-trans-sat M Γ t (t ⋆ 𝟎) (t ⋆ r) t
           (rule＝-trans-sat M Γ t (𝟎 ⋆ t) (t ⋆ 𝟎) t
             (rule＝-sym-sat M Γ t (𝟎 ⋆ t) t (rule-left-id-sat M Γ t t (lift tt) , lift tt) ,
              rule＝-⋆-sym-sat M Γ 𝟎 t (CEr t) (lift tt) ,
              lift tt) ,
            rule⊑-⋆-cong-sat M Γ t 𝟎 t r t
              (rule⊑-refl-sat M Γ t t (lift tt) ,
               rule𝟎min-sat M Γ t r (lift tt) ,
               lift tt) ,
            lift tt) ,
          sat1 , lift tt)

  𝕀𝕀𝕀 : sat-sequent M (rseq (ℂe Γ (t ⊑ sub-Res (↑ᵣ₀ t) s′ ⋆ sub-Res (sub-Res (↑ᵣ₁ r) s) s′ →· sub (sub (↑₁ A) s) s′) t) R C)
  𝕀𝕀𝕀 = subst₃ (λ x y z → sat-sequent M (rseq (ℂe Γ (t ⊑ x ⋆ sub-Res y s′ →· sub z s′) t) R C))
               (sym (sub-Res-↑ᵣ₀ (ℂtxt Γ) 𝕍ℝ t t))
               (sym (sub-Res-↑ᵣ₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ t r))
               (sym (sub-↑₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ t A))
               (subst₂ (λ x y → sat-sequent M (rseq (ℂe Γ (t ⊑ t ⋆ x →· y) t) R C))
                       (sym (sub-Res-↑ᵣ₀ (ℂtxt Γ) 𝕍ℝ t r))
                       (sym (sub-↑₀ (ℂtxt Γ) 𝕍ℝ t A))
                       𝕀𝕍)

  𝕀𝕀 : sat-sequent M (rseq (ℂe Γ (Ｆ (sub (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r →· ↑₁ A) s)) t) R C)
  𝕀𝕀 = ruleＦL-sat M Γ t (CEr R) (sub (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r →· ↑₁ A) s) C (𝕀𝕀𝕀 , lift tt)

  𝕀 : sat-sequent M (rseq (ℂe Γ (□ (subℝ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r →· ↑₁ A)) t)) t) R C)
  𝕀 = rule□L-now-sat M Γ t R (subℝ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r →· ↑₁ A)) t) C (𝕀𝕀 , lift tt)

--    Γ, ■ A @ r, A @ r₁ ⊢[T] C    Γ ⊢[T] r₁ ⊑ r
-- ------------------------------------------------
--               Γ, ■ A @ r ⊢[T] C

rule■L : (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule■L Γ r r₁ T A C =
  rule (rseq (ℂe (ℂe Γ (■ A) r) A r₁) T C
        ∷ rseq Γ T (r₁ ⊑ r)
        ∷ [])
       (rseq (ℂe Γ (■ A) r) T C)

abstract
  rule■L-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ)
             → sat-rule M (rule■L Γ r r₁ T A C)
  rule■L-sat M Γ r r₁ T A C (sat1 , sat2 , _) =
    rule-cut-sat M (ℂe Γ (■ A) r) (CEr T) (CEr r₁) C A
      (rule-cut-sat M (ℂe Γ (■ A) r) (CEr r₁) (CEr r₁) A (A ∨· (¬· A))
        (rule-classical-sat M (ℂe Γ (■ A) r) r₁ A (lift tt) ,
         rule∨E-sat M (ℂe Γ (■ A) r) r₁ (CEr r₁) A (¬· A) A
           (ruleLbl-sat M (ℂe Γ (■ A) r) (CEr r₁) A (lift tt) ,
            𝕀 ,
            lift tt) ,
         lift tt) ,
       sat1 ,
       lift tt)
    where
    𝕀𝕀𝕀 : sat-sequent M (rseq (ℂe Γ (¬· A) r₁) r (◆ (¬· A)))
    𝕀𝕀𝕀 = rule◆R-sat M (ℂe Γ (¬· A) r₁) r r₁ (¬· A)
            (rule-thin-sat M Γ (¬· A) (CEr r₁) (CEr r) (r₁ ⊑ r) (sat2 , (lift tt)) ,
             (ruleLbl-sat M Γ (CEr r₁) (¬· A) (lift tt)) ,
             lift tt)

    𝕀𝕀 : sat-sequent M (rseq (ℂe Γ (¬· A) r₁) (↑ᵣ ⊆-refl r) (◆ (¬· (↑ ⊆-refl A))))
    𝕀𝕀 = subst₂ (λ x y → sat-sequent M (rseq (ℂe Γ (¬· A) r₁) x (◆ (¬· y)))) (sym (↑ᵣ⊆-refl r)) (sym (↑⊆-refl A)) 𝕀𝕀𝕀

    𝕀 : sat-sequent M (rseq (ℂe (ℂe Γ (■ A) r) (¬· A) r₁) r₁ A)
    𝕀 = rule¬E-sat M Γ (ℂe ℂ⟨⟩ (¬· A) r₁) r (◆ (¬· A)) (CEr r₁) A (𝕀𝕀 , lift tt)

--    Γ, A @ r ⊢[T] C
-- -----------------------
--    Γ, ■ A @ r ⊢[T] C

rule■L-now : (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule■L-now Γ r T A C =
  rule (rseq (ℂe Γ A r) T C
        ∷ [])
       (rseq (ℂe Γ (■ A) r) T C)

rule■L-now-sat : (M : Model₀) (Γ : ℂ₀) (r T : ℂRes Γ) (A C : ℂForm Γ)
               → sat-rule M (rule■L-now Γ r T A C)
rule■L-now-sat M Γ r T A C (sat1 , _) =
  rule■L-sat M Γ r r T A C
    (rule-thin1-sat M Γ (■ A) A (CEr r) (CEr r) (CEr T) C (sat1 , lift tt) ,
     rule⊑-refl-sat M Γ r T (lift tt) ,
     lift tt)

-- Similar to rule■L but thins the ■ A hyp:
--
--    Γ, A @ r₁ ⊢[T] C    Γ ⊢[T] r₁ ⊑ r
-- ---------------------------------------
--           Γ, ■ A @ r ⊢[T] C

rule■L′ : (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule■L′ Γ r r₁ T A C =
  rule (rseq (ℂe Γ A r₁) T C
        ∷ rseq Γ T (r₁ ⊑ r)
        ∷ [])
       (rseq (ℂe Γ (■ A) r) T C)

rule■L′-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ T : ℂRes Γ) (A C : ℂForm Γ)
            → sat-rule M (rule■L′ Γ r r₁ T A C)
rule■L′-sat M Γ r r₁ T A C (sat1 , sat2 , _) =
  rule■L-sat M Γ r r₁ T A C
    (rule-thin1-sat M Γ (■ A) A (CEr r) (CEr r₁) (CEr T) C (sat1 , lift tt) ,
     sat2 ,
     lift tt)

-- Derived:
--
--    Γ, A ⊢ᵣ C     Γ , ¬ A ⊢ᵣ C
-- ------------------------------
--         Γ ⊢ᵣ C

by-cases : (Γ : ℂ₀) (r R : ℂRes Γ) (A C : ℂForm Γ) → Rule
by-cases Γ r R A C =
  rule (rseq (ℂe Γ A r) R C ∷ rseq (ℂe Γ (¬· A) r) R C ∷ [])
       (rseq Γ R C)

abstract
  by-cases-sat : (M : Model₀) (Γ : ℂ₀) (r R : ℂRes Γ) (A C : ℂForm Γ)
               → sat-rule M (by-cases Γ r R A C)
  by-cases-sat M Γ r R A C (satA , sat¬A , _) =
    rule-cut-sat M Γ (CEr R) (CEr r) C (A ∨· (¬· A))
      (rule-classical-sat M Γ r A (lift tt) ,
       rule∨E-sat M Γ r (CEr R) A (¬· A) C (satA , sat¬A , lift tt) ,
       lift tt)

--    Γ, A @ r₁ ⊢[T] C    Γ ⊢[T] r ⊑ r₁    Γ ⊢[T] r₂ ⊑ r ⋆ t
-- -----------------------------------------------------------------------
--                      Γ, □↓ t A @ r ⊢[T] C

rule□↓L : (Γ : ℂ₀) (r r₁ T t : ℂRes Γ) (A C : ℂForm Γ) → Rule
rule□↓L Γ r r₁ T t A C =
  rule (rseq (ℂe Γ A r₁) T C
        ∷ rseq Γ T (r ⊑ r₁)
        ∷ rseq Γ T (r₁ ⊑ (r ⋆ t))
        ∷ [])
       (rseq (ℂe Γ (□↓ t A) r) T C)

abstract
  rule□↓L-sat : (M : Model₀) (Γ : ℂ₀) (r r₁ T t : ℂRes Γ) (A C : ℂForm Γ)
              → sat-rule M (rule□↓L Γ r r₁ T t A C)
  rule□↓L-sat M Γ r r₁ T t A C (sat1 , sat2 , sat3 , _) =
    ruleＦL-sat
      M Γ r (CEr T) (□ (Ｆ ((𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₁ t)) →· ↑₁ A))) C
      (𝕀 , lift tt)
    where
    𝕀′ : sat-sequent M (rseq (ℂe Γ (□ (Ｆ ((𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) →· ↑₀ A))) r) T C)
    𝕀′ = rule□L′-sat M Γ r r₁ T (Ｆ (𝕣₀ ⊑ ↑ᵣ₀ r ⋆ ↑ᵣ₀ t →· ↑₀ A)) C
          (ruleＦL-sat M Γ r₁ (CEr T) (𝕣₀ ⊑ ↑ᵣ₀ r ⋆ ↑ᵣ₀ t →· ↑₀ A) C
            (subst₂ (λ x y → sat-sequent M (rseq (ℂe Γ (r₁ ⊑ x →· y) r₁) T C))
                    (sym (sub-Res-↑ᵣ₀ (ℂtxt Γ) 𝕍ℝ r₁ (r ⋆ t)))
                    (sym (sub-↑₀ (ℂtxt Γ) 𝕍ℝ r₁ A))
                    (rule→L-sat M Γ (CEr T) r₁ (r₁ ⊑ r ⋆ t) A C
                      (rule-comp-change-resources-sat M Γ r₁ T r₁ (r ⋆ t) LE
                        (sat3 , lift tt) , sat1 , lift tt)) , lift tt) , sat2 , lift tt)

    s₁ : CSub ((ℂtxt Γ ، 𝕍ℝ) ، 𝕍ℝ) (ℂtxt Γ ، 𝕍ℝ)
    s₁ = CSub، 𝕍ℝ (CSub،ₗ r)

    helper₁ : ((sub-Res 𝕣₀ s₁) ⊑ ((sub-Res 𝕣₁ s₁) ⋆ (sub-Res (↑ᵣ₁ t) s₁))) →· sub (↑₁ A) s₁
            ≡ (𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) →· ↑₀ A
    helper₁ = cong₂ _→·_ (cong₂ _⊑_ refl (cong₂ _⋆_ refl (sub-Res-↑ᵣ₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r t))) (sub-↑₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r A)

    𝕀 : sat-sequent M (rseq (ℂe Γ (subℝ (□ (Ｆ ((𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₁ t)) →· ↑₁ A))) r) r) T C)
    𝕀 = subst (λ x → sat-sequent M (rseq (ℂe Γ (□ (Ｆ x)) r) T C)) (sym helper₁) 𝕀′

-- Derived:
--
--    Γ ⊢[R] □↓ t (¬· A)     Γ ⊢[R] ◇↓◆ t A
-- ------------------------------------------
--                Γ ⊢[R] ◆· A

□↓¬∧◇↓◆⇒◆· : (Γ : ℂ₀) (t R : ℂRes Γ) (A : ℂForm Γ) → Rule
□↓¬∧◇↓◆⇒◆· Γ t R A =
  rule (rseq Γ R (□↓ t (¬· A)) ∷ rseq Γ R (◇↓◆ t A) ∷ [])
       (rseq Γ R (◆· A))

abstract
  □↓¬∧◇↓◆⇒◆·-sat : (M : Model₀) (Γ : ℂ₀) (t R : ℂRes Γ) (A : ℂForm Γ)
                 → sat-rule M (□↓¬∧◇↓◆⇒◆· Γ t R A)
  □↓¬∧◇↓◆⇒◆·-sat M Γ t R A (sat1 , sat2 , _) =
    rule-cut-sat M Γ (CEr R) (CEr R) (◆· A) (◇↓◆ t A)
      (sat2 ,
      rule◇↓◆L-sat M Γ t R R A (◆· A)
        (⊑∨⊏-sat M Γ₁ (↑ᵣ₀ (R ⋆ t)) (↑ᵣ₀ R) 𝕣₀ (↑ᵣ₀ R) (↑₀ (◆· A))
           (derived-rule-⊑⋆ₗ-sat M Γ₁ (↑ᵣ₀ t) (↑ᵣ₀ R) (↑ᵣ₀ R) (rule⊑-refl-sat M Γ₁ (↑ᵣ₀ R) (↑ᵣ₀ R) (lift tt) , lift tt) ,
            rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) (↑₀ A) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))
              (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ (R ⋆ t)) LE (lift tt) , lift tt) ,
            -- prove ⊥· because it contradict sat1
            prove⊥-sat M (ℂu Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀)) (CEr (↑ᵣ₀ R)) (↑₀ (◆· A))
              (rule-cut-sat M (ℂu Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀)) (CEr (↑ᵣ₀ R)) (CEr (↑ᵣ₀ R)) ⊥· (↑₀ (□↓ t (¬· A)))
                (rule-thin-sat M Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ R)) (↑₀ (□↓ t (¬· A)))
                  (rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) (↑₀ A) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (↑₀ (□↓ t (¬· A)))
                    (rule-thin-sat M (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t)) CEu (CEr (↑ᵣ₀ R)) (↑₀ (□↓ t (¬· A)))
                      (rule-thin-v-sat M Γ 𝕍ℝ R (□↓ t (¬· A)) (sat1 , lift tt) , lift tt) , lift tt) , lift tt) ,
                 move-to-concl-ext-sat M {ℂu Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀)} (↑ᵣ₀ R) (↑₀ (□↓ t (¬· A))) ⊥·
                   (subst (λ x → sat-sequent M (rseq (ℂu Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀)) (↑ᵣ₀ R) (x →· ⊥·)))
                          (sym (↑□↓ ⊆₀ t (¬· A)))
                          (rule→I-sat M (ℂu Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀)) (↑ᵣ₀ R) (□↓ (↑ᵣ₀ t) (¬· ↑₀ A)) ⊥·
                            (rule□↓L-sat M (ℂu Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀)) (↑ᵣ₀ R) 𝕣₀ (↑ᵣ₀ R) (↑ᵣ₀ t) (¬· ↑₀ A) ⊥·
                              (rule¬E-last-sat M (ℂu Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀)) 𝕣₀ (↑₀ A) (↑ᵣ₀ R) ⊥·
                                (rule-thin-sat M Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀) CEu (CEr 𝕣₀) (↑₀ A)
                                  (ruleLbl-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) (CEr 𝕣₀) (↑₀ A) (lift tt) , lift tt) , lift tt) ,
                               rule-id-comp-u-sat M Γ₁ (CEr (↑ᵣ₀ R)) (↑ᵣ₀ R) 𝕣₀ LE (lift tt) ,
                               rule-thin-sat M Γ₁ (↑ᵣ₀ R ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ R)) (𝕣₀ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ t)
                                 (rule-thin-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) (↑₀ A) (CEr 𝕣₀) (CEr (↑ᵣ₀ R)) (𝕣₀ ⊑ ↑ᵣ₀ R ⋆ ↑ᵣ₀ t)
                                   (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr (↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ (R ⋆ t)) LE (lift tt) , lift tt) , lift tt) ,
                               lift tt) , lift tt)) , lift tt) ,
                 lift tt) , lift tt) ,
            -- instantiate the conclusion using 𝕣₀ using ◆·R
            ◆·R-sat M (ℂu Γ₁ (𝕣₀ ⊏ ↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ R) (↑₀ A)
              (rule-thin-sat M Γ₁ (𝕣₀ ⊏ ↑ᵣ₀ R) CEu (CEr 𝕣₀) (↑₀ A)
                ((ruleLbl-sat M (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) (CEr 𝕣₀) (↑₀ A) (lift tt)) , lift tt) ,
               rule-id-comp-u-sat M Γ₁ (CEr (↑ᵣ₀ R)) 𝕣₀ (↑ᵣ₀ R) LT (lift tt) , lift tt) ,
            lift tt) ,
          lift tt) ,
      lift tt)
    where
    Γ₁ : ℂ₀
    Γ₁ = ℂe (ℂu (ℂv Γ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ (R ⋆ t))) (↑₀ A) 𝕣₀

\end{code}
