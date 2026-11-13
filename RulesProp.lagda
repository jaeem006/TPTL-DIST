Propositional logic rules

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

module RulesProp(𝔻 : Set)
                (W : World)
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open import RulesMisc(𝔻)(W)

open World.World W

--     Γ ⊢ᵣ A     Γ ⊢ᵣ B
-- ---------------------------
--       Γ ⊢ᵣ A ∧ B

rule∧I : (Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ) → Rule
rule∧I Γ r A B =
  rule (seq Γ r A ∷ seq Γ r B ∷ [])
       (seq Γ r (A ∧· B))

abstract
  rule∧I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ)
             → sat-rule M (rule∧I Γ r A B)
  rule∧I-sat M Γ r A B (satA , satB , _) s satΓ =
    sat-ctxt-annot∧ A B r (M ≔ₛ s) (satA s satΓ) (satB s satΓ)

--    Γ, A^x, B^x ⊢ᵣ C
-- ------------------
--    Γ, (A ∧ B)^x ⊢ᵣ C

rule∧E : (Γ : ℂ₀) (r : ℂCE Γ) (x : ℂCE Γ) (A B C : ℂForm Γ) → Rule
rule∧E Γ r x A B C =
  rule [ seq (ℂx (ℂx Γ A x) B x) r C ]
       (seq (ℂx Γ (A ∧· B) x) r C)

abstract
  rule∧E-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ) (x : ℂCE Γ) (A B C : ℂForm Γ)
             → sat-rule M (rule∧E Γ r x A B C)
  rule∧E-sat M Γ r x A B C (satC , _) s (satΓ , satA) =
    satC s ((satΓ , sat-ctxt-annot∧·ₗ A B x (M ≔ₛ s) satA) ,
           sat-ctxt-annot∧·ᵣ A B x (M ≔ₛ s) satA)

--    Γ, A^x, B^x, Δ ⊢ᵣ C
-- ------------------
--    Γ, (A ∧ B)^x, Δ ⊢ᵣ C

rule∧E′ : (Γ : ℂ₀) (Δ : ℂℂ Γ) (x : ℂCE Γ) (A B : ℂForm Γ)
          (r : ℂRes (ℂx Γ (A ∧· B) x ⨾ Δ))
          (C : ℂForm (ℂx Γ (A ∧· B) x ⨾ Δ)) → Rule
rule∧E′ Γ Δ x A B r C =
  rule [ rseq (ℂx (ℂx Γ A x) B x ⨾ Δ) (⋆Res e r) (⋆Form e C) ]
       (rseq (ℂx Γ (A ∧· B) x ⨾ Δ) r C)
  where
  e : ℂtxt (ℂx Γ (A ∧· B) x ⨾ Δ) ≡ ℂtxt (ℂx (ℂx Γ A x) B x ⨾ Δ)
  e = ≡ℂtxt⨾⨾ (ℂx Γ (A ∧· B) x) (ℂx (ℂx Γ A x) B x) Δ Δ refl

rule∧E′-sat-ctxt : (c : ℂ₀) (d : ℂℂ c)
                   (x : ℂCE c) (A B : ℂForm c)
                   (e : ℂtxt (ℂx c (A ∧· B) x ⨾ d) ≡ ℂtxt (ℂx (ℂx c A x) B x ⨾ d))
                   (M : Model₀)
                   (s : ℂSub (ℂx c (A ∧· B) x ⨾ d))
                 → sat-ctxt (ℂx c (A ∧· B) x ⨾ d) (M ≔ₛ s)
                 → sat-ctxt (ℂx (ℂx c A x) B x ⨾ d) (M ≔ₛ ⋆Sub e s)
rule∧E′-sat-ctxt c ℂ⟨⟩ x A B refl M s (h , q) =
  (h , sat-ctxt-annot∧·ₗ A B x (M ≔ₛ s) q) , (sat-ctxt-annot∧·ᵣ A B x (M ≔ₛ s) q)
rule∧E′-sat-ctxt c (ℂx d f a) x A B e M s (h , q) =
  (rule∧E′-sat-ctxt c d x A B e M s h) ,
  sat-ctxt-annot-*subst
    M (ℂtxt d)
    (ℂtxt (ℂx c (A ∧· B) x ⨾ d))
    (ℂtxt (ℂx (ℂx c A x) B x ⨾ d))
    e (≡ℂtxt⨾ (ℂx c (A ∧· B) x) d) (≡ℂtxt⨾ (ℂx (ℂx c A x) B x) d) s f a q
rule∧E′-sat-ctxt c (ℂv d v) x A B e M s h =
  subst (λ z → sat-ctxt (ℂx (ℂx c A x) B x ⨾ d) (M ≔ₛ z))
        (sym (Sub،→-⋆Sub e s))
        (rule∧E′-sat-ctxt c d x A B (،-inj e) M (Sub،→ s) h)

abstract
  rule∧E′-sat : (M : Model₀) (Γ : ℂ₀) (Δ : ℂℂ Γ) (x : ℂCE Γ) (A B : ℂForm Γ)
                (r : ℂRes (ℂx Γ (A ∧· B) x ⨾ Δ))
                (C : ℂForm (ℂx Γ (A ∧· B) x ⨾ Δ))
              → sat-rule M (rule∧E′ Γ Δ x A B r C)
  rule∧E′-sat M Γ Δ x A B r C (satC , _) s satΓ =
    sat-⋆Sub M e s r C (satC (⋆Sub e s) (rule∧E′-sat-ctxt Γ Δ x A B e M s satΓ))
    where
    e : ℂtxt (ℂx Γ (A ∧· B) x ⨾ Δ) ≡ ℂtxt (ℂx (ℂx Γ A x) B x ⨾ Δ)
    e = ≡ℂtxt⨾⨾ (ℂx Γ (A ∧· B) x) (ℂx (ℂx Γ A x) B x) Δ Δ refl


--         Γ ⊢ᵣ A
-- ----------------------
--       Γ ⊢ᵣ A ∨ B

rule∨Iₗ : (Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ) → Rule
rule∨Iₗ Γ r A B =
  rule [ seq Γ r A ]
       (seq Γ r (A ∨· B))

abstract
  rule∨Iₗ-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ)
              → sat-rule M (rule∨Iₗ Γ r A B)
  rule∨Iₗ-sat M Γ r A B (satA , _) s satΓ = sat-ctxt-annot∨ₗ A B r (M ≔ₛ s) (satA s satΓ)

--    Γ, A ⊢ᵣ C     Γ , B ⊢ᵣ C
-- ------------------------------
--         Γ, A ∨ B ⊢ᵣ C

rule∨E : (Γ : ℂ₀) (r : ℂRes Γ) (R : ℂCE Γ) (A B C : ℂForm Γ) → Rule
rule∨E Γ r R A B C =
  rule (seq (ℂe Γ A r) R C ∷ seq (ℂe Γ B r) R C ∷ [])
       (seq (ℂe Γ (A ∨· B) r) R C)

abstract
  rule∨E-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (R : ℂCE Γ) (A B C : ℂForm Γ)
             → sat-rule M (rule∨E Γ r R A B C)
  rule∨E-sat M Γ r R A B C (satA , satB , _) s (satΓ , inj₁ sata) = satA s (satΓ , sata)
  rule∨E-sat M Γ r R A B C (satA , satB , _) s (satΓ , inj₂ satb) = satB s (satΓ , satb)

--         Γ ⊢ᵣ B
-- ----------------------
--       Γ ⊢ᵣ A ∨ B

rule∨Iᵣ : (Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ) → Rule
rule∨Iᵣ Γ r A B =
  rule [ seq Γ r B ]
       (seq Γ r (A ∨· B))

abstract
  rule∨Iᵣ-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ)
              → sat-rule M (rule∨Iᵣ Γ r A B)
  rule∨Iᵣ-sat M Γ r A B (satB , _) s satΓ = sat-ctxt-annot∨ᵣ A B r (M ≔ₛ s) (satB s satΓ)


--         Γ, A ⊢ᵣ B
-- ------------------------
--        Γ ⊢ᵣ A → B

rule→I : (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ) → Rule
rule→I Γ r A B =
  rule [ rseq (ℂe Γ A r) r B ]
       (rseq Γ r (A →· B))

abstract
  rule→I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ)
             → sat-rule M (rule→I Γ r A B)
  rule→I-sat M Γ r A B (satB , _) s satΓ a = satB s (satΓ , a)

--     Γ ⊢[R] A      Γ,Bᴿ ⊢[T] C
-- -------------------------------
--        Γ,(A → B)ᴿ ⊢[T] C

rule→L : (Γ : ℂ₀) (T : ℂCE Γ) (R : ℂRes Γ) (A B C : ℂForm Γ) → Rule
rule→L Γ T R A B C =
  rule (rseq Γ R A ∷ seq (ℂe Γ B R) T C ∷ [])
       (seq (ℂe Γ (A →· B) R) T C)

abstract
  rule→L-sat : (M : Model₀) (Γ : ℂ₀) (T : ℂCE Γ) (R : ℂRes Γ) (A B C : ℂForm Γ)
             → sat-rule M (rule→L Γ T R A B C)
  rule→L-sat M Γ T R A B C (satA , (satwB , _)) s (satΓ , sat→) = satwB s (satΓ , sat→ (satA s satΓ))


--      Γ , A@r ⊢ᵣ ⊥
-- --------------------
--       Γ ⊢ᵣ ¬ A

rule¬I : (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ) → Rule
rule¬I Γ r A =
  rule [ rseq (ℂe Γ A r) r ⊥· ]
       (rseq Γ r (¬· A))

abstract
  rule¬I-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (rule¬I Γ r A)
  rule¬I-sat M Γ r A (sat⊥ , _) s satΓ a = sat⊥ s (satΓ , a)

--       Γ, Δ ⊢ᵣ A
-- --------------------
--    Γ, ¬ A, Δ ⊢ᵣ B

rule¬E : (Γ : ℂ₀) (Δ : ℂℂ Γ) (r : ℂRes Γ) (A : ℂForm Γ) (R : ℂCE (ℂe Γ (¬· A) r ⨾ Δ)) (B : ℂForm (ℂe Γ (¬· A) r ⨾ Δ)) → Rule
rule¬E Γ Δ r A R B =
  rule [ rseq (Γ ⨾ Δ) (↑ᵣ e r) (↑ e A) ]
       (seq (ℂe Γ (¬· A) r ⨾ Δ) R B)
  where
  e : ℂtxt Γ ⊆ ℂtxt (Γ ⨾ Δ)
  e = ⊆⨾ Γ Δ

rule¬E-sat-ctxt₁ : (c : ℂ₀) (d : ℂℂ c)
                   (r : ℂRes c) (A : ℂForm c)
                   (e : ℂtxt (ℂe c (¬· A) r ⨾ d) ≡ ℂtxt (c ⨾ d))
                   (M : Model₀)
                   (s : ℂSub (ℂe c (¬· A) r ⨾ d))
                 → sat-ctxt (ℂe c (¬· A) r ⨾ d) (M ≔ₛ s)
                 → ¬ ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub e s)) ⊨ ↑ (⊆⨾ c d) A
rule¬E-sat-ctxt₁ c ℂ⟨⟩ r A refl M s (h , q) z =
  lower (q (subst₂ (λ x y → ((M ≔ₛ s) ≔ₜ (⟦ x ⟧ᵣ s)) ⊨ y) (↑ᵣ⊆-refl r) (↑⊆-refl A) z))
rule¬E-sat-ctxt₁ c (ℂx d f a) r A e M s (h , q) z =
  rule¬E-sat-ctxt₁ c d r A e M s h z
rule¬E-sat-ctxt₁ c (ℂv d v) r A e M (s ⹁ .v ∶ u) h z =
  rule¬E-sat-ctxt₁ c d r A (،-inj e) M s h
    (⊨-↑₀→ {_} {(M ≔ₛ ⋆Sub (،-inj e) s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub (،-inj e) s)} {↑ (⊆⨾ c d) A} {v} u 𝕀𝕀)
  where
  e₁ : ↑ᵣ (⊆⨾ c (ℂv d v)) r ≡ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r)
  e₁ = ↑ᵣ-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ r (λ x i → refl)

  e₂ : ↑ (⊆⨾ c (ℂv d v)) A ≡ ↑₀ (↑ (⊆⨾ c d) A)
  e₂ = ↑-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ A (λ x i → refl)

  e₃ : ⟦ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r) ⟧ᵣ (⋆Sub (،-inj e) s ⹁ v ∶ u) ≡ ⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub (،-inj e) s
  e₃ = ⟦↑ᵣ₀⟧ᵣ (↑ᵣ (⊆⨾ c d) r) (⋆Sub (،-inj e) s) v u

  𝕀 : ((M ≔ₛ (⋆Sub (،-inj e) s ⹁ v ∶ u)) ≔ₜ (⟦ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r) ⟧ᵣ (⋆Sub (،-inj e) s ⹁ v ∶ u))) ⊨ ↑₀ (↑ (⊆⨾ c d) A)
  𝕀 = subst₃ (λ x y z → ((M ≔ₛ x) ≔ₜ (⟦ y ⟧ᵣ x)) ⊨ z) (⋆Sub⹁∶ e s u) e₁ e₂ z

  𝕀𝕀 : ((M ≔ₛ (⋆Sub (،-inj e) s ⹁ v ∶ u)) ≔ₜ (⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub (،-inj e) s)) ⊨ ↑₀ (↑ (⊆⨾ c d) A)
  𝕀𝕀 = subst (λ x → ((M ≔ₛ (⋆Sub (،-inj e) s ⹁ v ∶ u)) ≔ₜ x) ⊨ ↑₀ (↑ (⊆⨾ c d) A)) e₃ 𝕀

rule¬E-sat-ctxt₂ : (c : ℂ₀) (d : ℂℂ c)
                   (r : ℂRes c) (A : ℂForm c)
                   (e : ℂtxt (ℂe c (¬· A) r ⨾ d) ≡ ℂtxt (c ⨾ d))
                   (M : Model₀)
                   (s : ℂSub (ℂe c (¬· A) r ⨾ d))
                 → sat-ctxt (ℂe c (¬· A) r ⨾ d) (M ≔ₛ s)
                 → sat-ctxt (c ⨾ d) (M ≔ₛ ⋆Sub e s)
rule¬E-sat-ctxt₂ c ℂ⟨⟩ r A refl M s (h , q) = h
rule¬E-sat-ctxt₂ c (ℂx d f a) r A e M s (h , q) =
  rule¬E-sat-ctxt₂ c d r A e M s h ,
  sat-ctxt-annot-*subst M (ℂtxt d) (ℂtxt (ℂe c (¬· A) r ⨾ d)) (ℂtxt (c ⨾ d)) e (≡ℂtxt⨾ (ℂe c (¬· A) r) d) (≡ℂtxt⨾ c d) s f a q
rule¬E-sat-ctxt₂ c (ℂv d v) r A e M s h =
  subst (λ z → sat-ctxt (c ⨾ d) (M ≔ₛ z)) (sym (Sub،→-⋆Sub e s)) (rule¬E-sat-ctxt₂ c d r A (،-inj e) M (Sub،→ s) h)

abstract
  rule¬E-sat : (M : Model₀) (Γ : ℂ₀) (Δ : ℂℂ Γ) (r : ℂRes Γ) (A : ℂForm Γ) (R : ℂCE (ℂe Γ (¬· A) r ⨾ Δ)) (B : ℂForm (ℂe Γ (¬· A) r ⨾ Δ))
             → sat-rule M (rule¬E Γ Δ r A R B)
  rule¬E-sat M Γ Δ r A R B (satA , _) s satΓ =
    ⊥-elim (𝕀 𝕀𝕀)
    where
    e : ℂtxt (ℂe Γ (¬· A) r ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ)
    e = ≡ℂtxt⨾⨾ (ℂe Γ (¬· A) r) Γ Δ Δ refl

    𝕀𝕀 : ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ Γ Δ) r ⟧ᵣ ⋆Sub e s)) ⊨ ↑ (⊆⨾ Γ Δ) A
    𝕀𝕀 = satA (⋆Sub e s) (rule¬E-sat-ctxt₂ Γ Δ r A e M s satΓ)

    𝕀 : ¬ ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ Γ Δ) r ⟧ᵣ ⋆Sub e s)) ⊨ ↑ (⊆⨾ Γ Δ) A
    𝕀 = rule¬E-sat-ctxt₁ Γ Δ r A e M s satΓ

-- Derived:
--       Γ ⊢ᵣ A
-- ----------------
--    Γ, ¬ A ⊢ᵣ B

rule¬E-last : (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ) (R : ℂRes Γ) (B : ℂForm Γ) → Rule
rule¬E-last Γ r A R B =
  rule [ rseq Γ r A ]
       (rseq (ℂe Γ (¬· A) r) R B)

abstract
  rule¬E-last-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ) (R : ℂRes Γ) (B : ℂForm Γ)
                  → sat-rule M (rule¬E-last Γ r A R B)
  rule¬E-last-sat M Γ r A R B (satA , _) =
    rule¬E-sat M Γ ℂ⟨⟩ r A (CEr R) B
      (subst₂ (λ x y → sat-sequent M (rseq Γ x y)) (sym (↑ᵣ⊆-refl r)) (sym (↑⊆-refl A)) satA , lift tt)

-- Derivable:
--    Γ, ¬· A , ¬· B ⊢[T] C
-- ---------------------------
--    Γ, ¬· (A ∨· B) ⊢[T] C

rule¬∨L : (Γ : ℂ₀) (T R : ℂRes Γ) (A B C : ℂForm Γ) → Rule
rule¬∨L Γ T R A B C =
  rule (rseq (ℂe (ℂe Γ (¬· A) R) (¬· B) R) T C ∷ [])
       (rseq (ℂe Γ (¬· (A ∨· B)) R) T C)

rule¬∨L-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (A B C : ℂForm Γ)
            → sat-rule M (rule¬∨L Γ T R A B C)
rule¬∨L-sat M Γ T R A B C (satB , _) =
  rule-cut-sat M (ℂe Γ (¬· (A ∨· B)) R) (CEr T) (CEr R) C (¬· A)
    (rule¬I-sat M (ℂe Γ (¬· (A ∨· B)) R) R A
      (rule¬E-sat M Γ (ℂe ℂ⟨⟩ A R) R (A ∨· B) (CEr R) ⊥·
        (subst₂ (λ x y → sat-sequent M (rseq (ℂe Γ A R) x y)) (sym (↑ᵣ⊆-refl R)) (sym (↑⊆-refl (A ∨· B))) 𝕀 , lift tt) ,
       lift tt) ,
     𝕀𝕀 ,
     lift tt)
  where
  𝕀 : sat-sequent M (rseq (ℂe Γ A R) R (A ∨· B))
  𝕀 = rule∨Iₗ-sat M (ℂe Γ A R) (CEr R) A B (ruleLbl-sat M Γ (CEr R) A (lift tt) , lift tt)

  𝕀𝕀 : sat-sequent M (rseq (ℂe (ℂe Γ (¬· (A ∨· B)) R) (¬· A) R) T C)
  𝕀𝕀 = rule-cut-sat M (ℂe (ℂe Γ (¬· (A ∨· B)) R) (¬· A) R) (CEr T) (CEr R) C (¬· B)
         (rule¬I-sat M (ℂe (ℂe Γ (¬· (A ∨· B)) R) (¬· A) R) R B
           (rule¬E-sat M Γ (ℂe (ℂe ℂ⟨⟩ (¬· A) R) B R) R (A ∨· B) (CEr R) ⊥·
             (subst₂ (λ x y → sat-sequent M (rseq (ℂe (ℂe Γ (¬· A) R) B R) x y))
                     (sym (↑ᵣ⊆-refl R))
                     (sym (↑⊆-refl (A ∨· B)))
                     (rule∨Iᵣ-sat M (ℂe (ℂe Γ (¬· A) R) B R) (CEr R) A B (ruleLbl-sat M (ℂe Γ (¬· A) R) (CEr R) B (lift tt) , lift tt)) , lift tt) ,
            lift tt) ,
          rule-thin-gen-sat M Γ (ℂe (ℂe ℂ⟨⟩ (¬· A) R) (¬· B) R) (¬· (A ∨· B)) (CEr R) (CEr T) C
            (satB , lift tt) ,
          lift tt)

--
-- -------------
--   Γ ⊢[r] ⊤·

rule⊤R : (Γ : ℂ₀) (r : ℂCE Γ) → Rule
rule⊤R Γ r =
  rule [] (seq Γ r ⊤·)

abstract
  rule⊤R-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ)
             → sat-rule M (rule⊤R Γ r)
  rule⊤R-sat M Γ r _ s satΓ = sat-ctxt-annot⊤ r (M ≔ₛ s)

--    Γ ⊢[R] ⊥·
-- -------------
--    Γ ⊢[R] A

prove⊥ : (Γ : ℂ₀) (R : ℂCE Γ) (A : ℂForm Γ) → Rule
prove⊥ Γ R A =
  rule [ seq Γ R ⊥· ]
       (seq Γ R A)

abstract
  prove⊥-sat : (M : Model₀) (Γ : ℂ₀) (R : ℂCE Γ) (A : ℂForm Γ)
             → sat-rule M (prove⊥ Γ R A)
  prove⊥-sat M Γ (CEr x) A (sat1 , _) s satΓ = ⊥-elim (lower (sat1 s satΓ))
  prove⊥-sat M Γ CEu A (sat1 , _) s satΓ = ⊥-elim (lower (sat1 s satΓ))
  prove⊥-sat M Γ (CEi x) A (sat1 , _) s satΓ = λ w z → ⊥-elim (lower (sat1 s satΓ w z))

--    Γ ⊢[r₂] ⊥·    Γ ⊢ r₂
-- -------------------------
--         Γ ⊢[r₁] A

prove⊥′ : (Γ : ℂ₀) (r₁ r₂ : ℂCE Γ) (A : ℂForm Γ) → Rule
prove⊥′ Γ r₁ r₂ A =
  rule (seq Γ r₂ ⊥· ∷ nonEmpty Γ r₂ ∷ [])
       (seq Γ r₁ A)

abstract
  prove⊥′-sat : (M : Model₀) (Γ : ℂ₀) (r₁ r₂ : ℂCE Γ) (A : ℂForm Γ)
              → sat-rule M (prove⊥′ Γ r₁ r₂ A)
  prove⊥′-sat M Γ (CEr x) r A (sat1 , sat2 , _) s satΓ = ⊥-elim (sat-ctxt-annot⊥ r (M ≔ₛ s) (sat1 s satΓ) (sat2 s satΓ))
  prove⊥′-sat M Γ CEu r A (sat1 , sat2 , _) s satΓ = ⊥-elim (sat-ctxt-annot⊥ r (M ≔ₛ s) (sat1 s satΓ) (sat2 s satΓ))
  prove⊥′-sat M Γ (CEi x) r A (sat1 , sat2 , _) s satΓ = λ w z → ⊥-elim (sat-ctxt-annot⊥ r (M ≔ₛ s) (sat1 s satΓ) (sat2 s satΓ))

\end{code}
