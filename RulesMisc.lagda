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

module RulesMisc(𝔻 : Set)
                (W : World)
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open World.World W


--
-- ----------------
--    Γ, Aʳ ⊢ᵣ A

ruleLbl : (Γ : ℂ₀) (r : ℂCE Γ) (A : ℂForm Γ) → Rule
ruleLbl Γ r A =
  rule []
       (seq (ℂx Γ A r) r A)

abstract
  ruleLbl-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ) (A : ℂForm Γ)
              → sat-rule M (ruleLbl Γ r A)
  ruleLbl-sat M Γ r A _ s (satΓ , satA) = satA

--
-- ----------------
--    Γ, A ⊢ᵣ A

rule-id-comp-u : (Γ : ℂ₀) (r : ℂCE Γ) (r₁ r₂ : ℂRes Γ) (c : Comparison) → Rule
rule-id-comp-u Γ r r₁ r₂ c =
  rule []
       (seq (ℂu Γ (r₁ ⟨ c ⟩ r₂)) r (r₁ ⟨ c ⟩ r₂))

abstract
  rule-id-comp-u-sat : (M : Model₀) (Γ : ℂ₀) (r : ℂCE Γ) (r₁ r₂ : ℂRes Γ) (c : Comparison)
                     → sat-rule M (rule-id-comp-u Γ r r₁ r₂ c)
  rule-id-comp-u-sat M Γ (CEr x) r₁ r₂ c _ s (satΓ , satA) = satA
  rule-id-comp-u-sat M Γ CEu r₁ r₂ c _ s (satΓ , satA) = satA
  rule-id-comp-u-sat M Γ (CEi x) r₁ r₂ c _ s (satΓ , satA) = λ _ _ → satA

--
-- ----------------
--   Γ, Aʳ, Δ ⊢ᵣ A

ruleLbl′ : (Γ : ℂ₀) (Δ : ℂℂ Γ) (r : ℂRes Γ) (A : ℂForm Γ) → Rule
ruleLbl′ Γ Δ r A =
  rule []
       (rseq (ℂe Γ A r ⨾ Δ) (↑ᵣ (⊆⨾ (ℂe Γ A r) Δ) r) (↑ (⊆⨾ (ℂe Γ A r) Δ) A))

rule-var-sat-ctxt₁ : (c : ℂ₀) (d : ℂℂ c)
                     (r : ℂRes c) (A : ℂForm c)
                     (e : ℂtxt (ℂe c A r ⨾ d) ≡ ℂtxt (c ⨾ d))
                     (M : Model₀)
                     (s : ℂSub (ℂe c A r ⨾ d))
                   → sat-ctxt (ℂe c A r ⨾ d) (M ≔ₛ s)
                   → ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub e s)) ⊨ ↑ (⊆⨾ c d) A
rule-var-sat-ctxt₁ c ℂ⟨⟩ r A refl M s (h , q) =
  subst₂ (λ x y → ((M ≔ₛ s) ≔ₜ (⟦ x ⟧ᵣ s)) ⊨ y) (sym (↑ᵣ⊆-refl r)) (sym (↑⊆-refl A)) q
rule-var-sat-ctxt₁ c (ℂx d f a) r A e M s (h , q) =
  rule-var-sat-ctxt₁ c d r A e M s h
rule-var-sat-ctxt₁ c (ℂv d v) r A e M (s ⹁ .v ∶ u) h =
  subst₃ (λ x y z → ((M ≔ₛ x) ≔ₜ (⟦ y ⟧ᵣ x)) ⊨ z) (sym (⋆Sub⹁∶ e s u)) (sym e₁) (sym e₂)
         (subst (λ x → ((M ≔ₛ (⋆Sub (،-inj e) s ⹁ v ∶ u)) ≔ₜ x) ⊨ ↑₀ (↑ (⊆⨾ c d) A)) (sym e₃)
                (→⊨-↑₀ {_} {(M ≔ₛ ⋆Sub (،-inj e) s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub (،-inj e) s)} {↑ (⊆⨾ c d) A} {v} u
                       (rule-var-sat-ctxt₁ c d r A (،-inj e) M s h)))
  where
  e₁ : ↑ᵣ (⊆⨾ c (ℂv d v)) r ≡ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r)
  e₁ = ↑ᵣ-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ r (λ x i → refl)

  e₂ : ↑ (⊆⨾ c (ℂv d v)) A ≡ ↑₀ (↑ (⊆⨾ c d) A)
  e₂ = ↑-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ A (λ x i → refl)

  e₃ : ⟦ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r) ⟧ᵣ (⋆Sub (،-inj e) s ⹁ v ∶ u) ≡ ⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub (،-inj e) s
  e₃ = ⟦↑ᵣ₀⟧ᵣ (↑ᵣ (⊆⨾ c d) r) (⋆Sub (،-inj e) s) v u

abstract
  ruleLbl′-sat : (M : Model₀) (Γ : ℂ₀) (Δ : ℂℂ Γ) (r : ℂRes Γ) (A : ℂForm Γ)
               → sat-rule M (ruleLbl′ Γ Δ r A)
  ruleLbl′-sat M Γ Δ r A _ s satΓ = concl
    where
    e : ℂtxt (ℂe Γ A r ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ)
    e = ≡ℂtxt⨾⨾ (ℂe Γ A r) Γ Δ Δ refl

    e₁ : ⋆Res e (↑ᵣ (⊆⨾ (ℂe Γ A r) Δ) r) ≡ ↑ᵣ (⊆⨾ Γ Δ) r
    e₁ = ⋆Res-↑ᵣ⨾ Γ Δ A r e

    e₂ : ⋆Form e (↑ (⊆⨾ (ℂe Γ A r) Δ) A) ≡ ↑ (⊆⨾ Γ Δ) A
    e₂ = ⋆Form-↑⨾ Γ Δ A r A e

    𝕀 : ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ Γ Δ) r ⟧ᵣ ⋆Sub e s)) ⊨ ↑ (⊆⨾ Γ Δ) A
    𝕀 = rule-var-sat-ctxt₁ Γ Δ r A e M s satΓ

    concl : ((M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ (⊆⨾ (ℂe Γ A r) Δ) r ⟧ᵣ s)) ⊨ ↑ (⊆⨾ (ℂe Γ A r) Δ) A
    concl = sat-⋆Sub M e s (↑ᵣ (⊆⨾ (ℂe Γ A r) Δ) r) (↑ (⊆⨾ (ℂe Γ A r) Δ) A)
                     (subst₂ (λ x y → ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ x ⟧ᵣ ⋆Sub e s)) ⊨ y) (sym e₁) (sym e₂) 𝕀)

{--
--
-- ----------------
--   Γ, A, Δ ⊢ᵣ A

ruleLbl″ : (Γ : ℂ₀) (Δ : ℂℂ Γ) (r : ℂRes Γ) (A : ℂForm Γ) → Rule
ruleLbl″ Γ Δ r A =
  rule []
       (rseq (ℂu Γ A ⨾ Δ) (↑ᵣ (⊆⨾ (ℂu Γ A) Δ) r) (↑ (⊆⨾ (ℂu Γ A) Δ) A))

ruleLbl″-sat : (M : Model₀) (Γ : ℂ₀) (Δ : ℂℂ Γ) (r : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (ruleLbl″ Γ Δ r A)
ruleLbl″-sat M Γ Δ r A _ s satΓ = {!!}
--}

--     Γ , Δ ⊢ᵣ A
-- ----------------
--    Γ, B , Δ ⊢ᵣ A

rule-thin-gen : (Γ : ℂ₀) (Δ : ℂℂ Γ) (B : ℂForm Γ) (x : ℂCE Γ)
                (r : ℂCE (ℂx Γ B x ⨾ Δ))
                (A : ℂForm (ℂx Γ B x ⨾ Δ)) → Rule
rule-thin-gen Γ Δ B x r A =
  rule [ seq (Γ ⨾ Δ) (⋆CE e r) (⋆Form e A) ]
       (seq (ℂx Γ B x ⨾ Δ) r A)
  where
  e : ℂtxt (ℂx Γ B x ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ)
  e = ≡ℂtxt⨾⨾ (ℂx Γ B x) Γ Δ Δ refl

rule-thin-gen-sat-ctxt : (c : ℂ₀) (d : ℂℂ c)
                         (x : ℂCE c) (B : ℂForm c)
                         (e : ℂtxt (ℂx c B x ⨾ d) ≡ ℂtxt (c ⨾ d))
                         (M : Model₀)
                         (s : ℂSub (ℂx c B x ⨾ d))
                       → sat-ctxt (ℂx c B x ⨾ d) (M ≔ₛ s)
                       → sat-ctxt (c ⨾ d) (M ≔ₛ ⋆Sub e s)
rule-thin-gen-sat-ctxt c ℂ⟨⟩ x B refl M s (h , q) = h
rule-thin-gen-sat-ctxt c (ℂx d f a) x B e M s (h , q) =
  rule-thin-gen-sat-ctxt c d x B e M s h ,
  sat-ctxt-annot-*subst M (ℂtxt d) (ℂtxt (ℂx c B x ⨾ d)) (ℂtxt (c ⨾ d)) e (≡ℂtxt⨾ (ℂx c B x) d) (≡ℂtxt⨾ c d) s f a q
rule-thin-gen-sat-ctxt c (ℂv d v) x B e M s h =
  subst (λ z → sat-ctxt (c ⨾ d) (M ≔ₛ z))
        (sym (Sub،→-⋆Sub e s))
        (rule-thin-gen-sat-ctxt c d x B (،-inj e) M (Sub،→ s) h)

abstract
  rule-thin-gen-sat : (M : Model₀) (Γ : ℂ₀) (Δ : ℂℂ Γ) (B : ℂForm Γ) (x : ℂCE Γ)
                      (r : ℂCE (ℂx Γ B x ⨾ Δ))
                      (A : ℂForm (ℂx Γ B x ⨾ Δ))
                    → sat-rule M (rule-thin-gen Γ Δ B x r A)
  rule-thin-gen-sat M Γ Δ B x r A (satA , _) s satΓ =
    sat-ctxt-annot-⋆Sub M e s r A (satA (⋆Sub e s) (rule-thin-gen-sat-ctxt Γ Δ x B e M s satΓ))
    where
    e : ℂtxt (ℂx Γ B x ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ)
    e = ≡ℂtxt⨾⨾ (ℂx Γ B x) Γ Δ Δ refl

-- Derived from rule-thin-gen:
--     Γ ⊢ᵣ A
-- ----------------
--    Γ, B ⊢ᵣ A

rule-thin : (Γ : ℂ₀) (B : ℂForm Γ) (x : ℂCE Γ) (r : ℂCE Γ) (A : ℂForm Γ) → Rule
rule-thin Γ B x r A =
  rule [ seq Γ r A ]
       (seq (ℂx Γ B x) r A)

abstract
  rule-thin-sat : (M : Model₀) (Γ : ℂ₀) (B : ℂForm Γ) (x : ℂCE Γ) (r : ℂCE Γ) (A : ℂForm Γ)
                → sat-rule M (rule-thin Γ B x r A)
  rule-thin-sat M Γ B x r A (satA , _) =
    rule-thin-gen-sat M Γ ℂ⟨⟩ B x r A (satA , lift tt)

-- Derived from rule-thin-gen:
--     Γ, C ⊢ᵣ A
-- ----------------
--    Γ, B, C ⊢ᵣ A

rule-thin1 : (Γ : ℂ₀) (B C : ℂForm Γ) (x y : ℂCE Γ) (r : ℂCE Γ) (A : ℂForm Γ) → Rule
rule-thin1 Γ B C x y r A =
  rule [ seq (ℂx Γ C y) r A ]
       (seq (ℂx (ℂx Γ B x) C y) r A)

abstract
  rule-thin1-sat : (M : Model₀) (Γ : ℂ₀) (B C : ℂForm Γ) (x y : ℂCE Γ) (r : ℂCE Γ) (A : ℂForm Γ)
                 → sat-rule M (rule-thin1 Γ B C x y r A)
  rule-thin1-sat M Γ B C x y r A (satA , _) =
    rule-thin-gen-sat M Γ (ℂx ℂ⟨⟩ C y) B x r A (satA , lift tt)

-- Derived from rule-thin-gen:
--     Γ, v, C ⊢ᵣ A
-- --------------------
--    Γ, B, v, C ⊢ᵣ A

rule-thin1v : (Γ : ℂ₀) (v : 𝕍) (B : ℂForm Γ) (C : ℂForm (ℂv Γ v))
              (x : ℂCE Γ) (y : ℂCE (ℂv Γ v)) (r : ℂCE (ℂv Γ v)) (A : ℂForm (ℂv Γ v)) → Rule
rule-thin1v Γ v B C x y r A =
  rule [ seq (ℂx (ℂv Γ v) C y) r A ]
       (seq (ℂx (ℂv (ℂx Γ B x) v) C y) r A)

abstract
  rule-thin1v-sat : (M : Model₀) (Γ : ℂ₀) (v : 𝕍) (B : ℂForm Γ) (C : ℂForm (ℂv Γ v))
                    (x : ℂCE Γ) (y : ℂCE (ℂv Γ v)) (r : ℂCE (ℂv Γ v)) (A : ℂForm (ℂv Γ v))
                  → sat-rule M (rule-thin1v Γ v B C x y r A)
  rule-thin1v-sat M Γ v B C x y r A (satA , _) =
    rule-thin-gen-sat M Γ (ℂx (ℂv ℂ⟨⟩ v) C y) B x r A (satA , lift tt)

-- Derived from rule-thin-gen:
--     Γ, u, v, C ⊢ᵣ A
-- --------------------
--    Γ, B, u, v, C ⊢ᵣ A

rule-thin1vv : (Γ : ℂ₀) (u v : 𝕍) (B : ℂForm Γ) (C : ℂForm (ℂv (ℂv Γ u) v))
               (x : ℂCE Γ) (y : ℂCE (ℂv (ℂv Γ u) v)) (r : ℂCE (ℂv (ℂv Γ u) v))
               (A : ℂForm (ℂv (ℂv Γ u) v)) → Rule
rule-thin1vv Γ u v B C x y r A =
  rule [ seq (ℂx (ℂv (ℂv Γ u) v) C y) r A ]
       (seq (ℂx (ℂv (ℂv (ℂx Γ B x) u) v) C y) r A)

abstract
  rule-thin1vv-sat : (M : Model₀) (Γ : ℂ₀) (u v : 𝕍) (B : ℂForm Γ) (C : ℂForm (ℂv (ℂv Γ u) v))
                     (x : ℂCE Γ) (y : ℂCE (ℂv (ℂv Γ u) v)) (r : ℂCE (ℂv (ℂv Γ u) v)) (A : ℂForm (ℂv (ℂv Γ u) v))
                   → sat-rule M (rule-thin1vv Γ u v B C x y r A)
  rule-thin1vv-sat M Γ u v B C x y r A (satA , _) =
    rule-thin-gen-sat M Γ (ℂx (ℂv (ℂv ℂ⟨⟩ u) v) C y) B x r A (satA , lift tt)

--     Γ ⊢ᵣ A
-- ----------------
--    Γ, v ⊢ᵣ A

rule-thin-v : (Γ : ℂ₀) (v : 𝕍) (r : ℂRes Γ) (A : ℂForm Γ) → Rule
rule-thin-v Γ v r A =
  rule [ rseq Γ r A ]
       (rseq (ℂv Γ v) (↑ᵣ₀ r) (↑₀ A))

abstract
  rule-thin-v-sat : (M : Model₀) (Γ : ℂ₀) (v : 𝕍) (r : ℂRes Γ) (A : ℂForm Γ)
                  → sat-rule M (rule-thin-v Γ v r A)
  rule-thin-v-sat M Γ v r A (satA , _) (s ⹁ .v ∶ u) satΓ = 𝕀
    where
    𝕀 : ((M ≔ₛ (s ⹁ v ∶ u)) ≔ₜ (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ v ∶ u))) ⊨ ↑₀ A
    𝕀 = →⊨-↑₀ {ℂtxt Γ} {(M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ v ∶ u))} {A} {v} u
              (subst (λ x → ((M ≔ₛ s) ≔ₜ x) ⊨ A) (sym (⟦↑ᵣ₀⟧ᵣ r s v u)) (satA s satΓ))

--     Γ ⊢[r] B   Γ, B^r ⊢[R] A
-- --------------------------
--          Γ ⊢[R] A

rule-cut : (Γ : ℂ₀) (R r : ℂCE Γ) (A B : ℂForm Γ) → Rule
rule-cut Γ R r A B =
  rule (seq Γ r B ∷ seq (ℂx Γ B r) R A ∷ [])
       (seq Γ R A)

abstract
  rule-cut-sat : (M : Model₀) (Γ : ℂ₀) (R r : ℂCE Γ) (A B : ℂForm Γ)
               → sat-rule M (rule-cut Γ R r A B)
  rule-cut-sat M Γ R r A B (satB , satA , _) s satΓ =
    satA s (satΓ , (satB s satΓ))

--     Γ ⊢[r] r₁ ⟨ c ⟩ r₂   Γ, r₁ ⟨ c ⟩ r₂ ⊢[R] A
-- ------------------------------------------------
--                    Γ ⊢[R] A

rule-cut-u : (Γ : ℂ₀) (R r : ℂRes Γ) (A : ℂForm Γ) (r₁ r₁ : ℂRes Γ) (c : Comparison) → Rule
rule-cut-u Γ R r A r₁ r₂ c =
  rule (rseq Γ r (r₁ ⟨ c ⟩ r₂) ∷ rseq (ℂu Γ (r₁ ⟨ c ⟩ r₂)) R A ∷ [])
       (rseq Γ R A)

abstract
  rule-cut-u-sat : (M : Model₀) (Γ : ℂ₀) (R r : ℂRes Γ) (A : ℂForm Γ) (r₁ r₂ : ℂRes Γ) (c : Comparison)
                 → sat-rule M (rule-cut-u Γ R r A r₁ r₂ c)
  rule-cut-u-sat M Γ R r A r₁ r₂ c (satB , satA , _) s satΓ =
    satA s (satΓ , (satB s satΓ))

--   Γ , Δ , B ⊢ᵣ A
-- ------------------
--   Γ , B , Δ ⊢ᵣ A

rule-move : (Γ : ℂ₀) (Δ : ℂℂ Γ) (B : ℂForm Γ) (x : ℂCE Γ)
            (r : ℂCE (ℂx Γ B x ⨾ Δ))
            (A : ℂForm (ℂx Γ B x ⨾ Δ)) → Rule
rule-move Γ Δ B x r A =
  rule [ seq (Γ ⨾ ℂx Δ (↑ (ℂ⊆ Γ Δ) B) (↑CE (ℂ⊆ Γ Δ) x)) (⋆CE e r) (⋆Form e A) ]
       (seq (ℂx Γ B x ⨾ Δ) r A)
  where
  e : ℂtxt (ℂx Γ B x ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ)
  e = ≡ℂtxt⨾⨾ (ℂx Γ B x) Γ Δ Δ refl

rule-sat-ctxt⨾ : (c : ℂ₀) (d : ℂℂ c)
                 (x : ℂCE c) (A : ℂForm c)
                 (e : ℂtxt (ℂx c A x ⨾ d) ≡ ℂtxt (c ⨾ d))
                 (M : Model₀)
                 (s : ℂSub (ℂx c A x ⨾ d))
               → sat-ctxt (ℂx c A x ⨾ d) (M ≔ₛ s)
               → sat-ctxt-annot (⋆Form (≡ℂtxt⨾ c d) (↑ (ℂ⊆ c d) A)) (⋆CE (≡ℂtxt⨾ c d) (↑CE (ℂ⊆ c d) x)) (M ≔ₛ ⋆Sub e s)
rule-sat-ctxt⨾ c ℂ⟨⟩ x A refl M s (h , q) = 𝕀
  where
  𝕀 : sat-ctxt-annot (↑ ⊆-refl A) (↑CE ⊆-refl x) (M ≔ₛ s)
  𝕀 = subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ s)) (sym (↑⊆-refl A)) (sym (↑CE⊆-refl x)) q
rule-sat-ctxt⨾ c (ℂx d f₁ a) x A e M s (h , q) = rule-sat-ctxt⨾ c d x A e M s h
rule-sat-ctxt⨾ c (ℂv d v) (CEr r) A e M (s ⹁ .v ∶ u) h =
  subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ ⋆Sub e (s ⹁ v ∶ u)))
         (sym (⋆Form-ℂ⊆ c (ℂv d v) A))
         (sym (⋆CE-ℂ⊆ c (ℂv d v) (CEr r)))
         (subst₃ (λ x y z → ((M ≔ₛ z) ≔ₜ (⟦ x ⟧ᵣ z)) ⊨ y)
                 (sym e₁) (sym e₂) (sym (⋆Sub، (ℂtxt (ℂx c A (CEr r) ⨾ d)) (ℂtxt (c ⨾ d)) v u e s))
                 (→⊨-↑₀ {_} {(M ≔ₛ ⋆Sub (،-inj e) s) ≔ₜ (⟦ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r) ⟧ᵣ (⋆Sub (،-inj e) s ⹁ v ∶ u))}
                        {↑ (⊆⨾ c d) A} {v} u
                        (subst (λ x → ((M ≔ₛ ⋆Sub (،-inj e) s) ≔ₜ x) ⊨ ↑ (⊆⨾ c d) A) (sym e₃)
                               (subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ ⋆Sub (،-inj e) s))
                                       (⋆Form-ℂ⊆ c d A)
                                       (⋆CE-ℂ⊆ c d (CEr r))
                                       (rule-sat-ctxt⨾ c d (CEr r) A (،-inj e) M s h)))))
  where
  e₁ : ↑ᵣ (⊆⨾ c (ℂv d v)) r ≡ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r)
  e₁ = ↑ᵣ-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ r (λ x i → refl)

  e₂ : ↑ (⊆⨾ c (ℂv d v)) A ≡ ↑₀ (↑ (⊆⨾ c d) A)
  e₂ = ↑-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ A (λ x i → refl)

  e₃ : ⟦ ↑ᵣ₀ (↑ᵣ (⊆⨾ c d) r) ⟧ᵣ (⋆Sub (،-inj e) s ⹁ v ∶ u) ≡ ⟦ ↑ᵣ (⊆⨾ c d) r ⟧ᵣ ⋆Sub (،-inj e) s
  e₃ = ⟦↑ᵣ₀⟧ᵣ (↑ᵣ (⊆⨾ c d) r) (⋆Sub (،-inj e) s) v u
rule-sat-ctxt⨾ c (ℂv d v) CEu A e M (s ⹁ .v ∶ u) h =
  subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ ⋆Sub e (s ⹁ v ∶ u)))
         (sym (⋆Form-ℂ⊆ c (ℂv d v) A))
         (sym (⋆CE-ℂ⊆ c (ℂv d v) CEu))
         (subst₂ (λ x y → (M ≔ₛ y) ⊨ x)
                 (sym e₁)
                 (sym (⋆Sub، (ℂtxt (ℂx c A CEu ⨾ d)) (ℂtxt (c ⨾ d)) v u e s))
                 (→⊨-↑₀ {_} {M ≔ₛ ⋆Sub (،-inj e) s} {↑ (⊆⨾ c d) A} {v} u
                        (subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ ⋆Sub (،-inj e) s))
                                (⋆Form-ℂ⊆ c d A)
                                (⋆CE-ℂ⊆ c d CEu)
                                (rule-sat-ctxt⨾ c d CEu A (،-inj e) M s h))))
  where
  e₁ : ↑ (⊆⨾ c (ℂv d v)) A ≡ ↑₀ (↑ (⊆⨾ c d) A)
  e₁ = ↑-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ A (λ x i → refl)
rule-sat-ctxt⨾ c (ℂv d v) (CEi i) A e M (s ⹁ .v ∶ u) h =
  subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ ⋆Sub e (s ⹁ v ∶ u)))
         (sym (⋆Form-ℂ⊆ c (ℂv d v) A))
         (sym (⋆CE-ℂ⊆ c (ℂv d v) (CEi i)))
         𝕀𝕀
  where
  e₁ : ↑ (⊆⨾ c (ℂv d v)) A ≡ ↑₀ (↑ (⊆⨾ c d) A)
  e₁ = ↑-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ A (λ x i → refl)

  e₂ : ↑I (⊆⨾ c (ℂv d v)) i ≡ ↑I₀ (↑I (⊆⨾ c d) i)
  e₂ = ↑I-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ i (λ x i → refl)

  𝕀 : (w : 𝕎)
    → inter-cond (M ≔ₛ ⋆Sub (،-inj e) s) w (↑I (⊆⨾ c d) i)
    → ((M ≔ₛ ⋆Sub (،-inj e) s) ≔ₜ w) ⊨ (↑ (⊆⨾ c d) A)
  𝕀 = subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ ⋆Sub (،-inj e) s))
             (⋆Form-ℂ⊆ c d A)
             (⋆CE-ℂ⊆ c d (CEi i))
             (rule-sat-ctxt⨾ c d (CEi i) A (،-inj e) M s h)

  𝕀𝕀 : (w : 𝕎)
     → inter-cond (M ≔ₛ ⋆Sub e (s ⹁ v ∶ u)) w (↑I (⊆⨾ c (ℂv d v)) i)
     → ((M ≔ₛ ⋆Sub e (s ⹁ v ∶ u)) ≔ₜ w) ⊨ ↑ (⊆⨾ c (ℂv d v)) A
  𝕀𝕀 w z = subst₂ (λ x y → ((M ≔ₛ y) ≔ₜ w) ⊨ x)
                  (sym e₁)
                  (sym (⋆Sub، (ℂtxt (ℂx c A (CEi i) ⨾ d)) (ℂtxt (c ⨾ d)) v u e s))
                  (→⊨-↑₀ {_} {(M ≔ₛ ⋆Sub (،-inj e) s) ≔ₜ w}
                         {↑ (⊆⨾ c d) A} {v} u
                         (𝕀 w (inter-cond↑I₀ M v u w (↑I (⊆⨾ c d) i) _
                            (subst₂ (λ x y → inter-cond (M ≔ₛ x) w y) (⋆Sub، _ _ v u e s) e₂ z))))

rule-move-sat-ctxt : (c : ℂ₀) (d : ℂℂ c)
                     (x : ℂCE c) (B : ℂForm c)
                     (e : ℂtxt (ℂx c B x ⨾ d) ≡ ℂtxt (c ⨾ d))
                     (M : Model₀)
                     (s : ℂSub (ℂx c B x ⨾ d))
                   → sat-ctxt (ℂx c B x ⨾ d) (M ≔ₛ s)
                   → sat-ctxt (c ⨾ ℂx d (↑ (ℂ⊆ c d) B) (↑CE (ℂ⊆ c d) x)) (M ≔ₛ ⋆Sub e s)
rule-move-sat-ctxt c d x B e M s h =
  𝕀 , rule-sat-ctxt⨾ c d x B e M s h
  where
  𝕀 : sat-ctxt (c ⨾ d) (M ≔ₛ ⋆Sub e s)
  𝕀 = rule-thin-gen-sat-ctxt c d x B e M s h

abstract
  rule-move-sat : (M : Model₀) (Γ : ℂ₀) (Δ : ℂℂ Γ) (B : ℂForm Γ) (x : ℂCE Γ)
                  (r : ℂCE (ℂx Γ B x ⨾ Δ))
                  (A : ℂForm (ℂx Γ B x ⨾ Δ))
                → sat-rule M (rule-move Γ Δ B x r A)
  rule-move-sat M Γ Δ B x r A (satA , _) s satΓ =
    sat-ctxt-annot-⋆Sub M e s r A (satA (⋆Sub e s) (rule-move-sat-ctxt Γ Δ x B e M s satΓ))
    where
    e : ℂtxt (ℂx Γ B x ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ)
    e = ≡ℂtxt⨾⨾ (ℂx Γ B x) Γ Δ Δ refl

-- Move to conclusion:
--
--    Γ ⊢[T] A → B
-- ------------------
--    Γ, A ⊢[T] B

move-to-concl : (Γ : ℂ₀) (T : ℂRes Γ) (r₁ r₂ : ℂRes Γ) (c : Comparison) (B : ℂForm Γ) → Rule
move-to-concl Γ T r₁ r₂ c B =
  rule [ rseq Γ T ((r₁ ⟨ c ⟩ r₂) →· B) ]
       (rseq (ℂu Γ (r₁ ⟨ c ⟩ r₂)) T B)

abstract
  move-to-concl-sat : (M : Model₀)
                      {Γ : ℂ₀} (T : ℂRes Γ) (r₁ r₂ : ℂRes Γ) (c : Comparison) (B : ℂForm Γ)
                    → sat-rule M (move-to-concl Γ T r₁ r₂ c B)
  move-to-concl-sat M {Γ} T r₁ r₂ c B (hyp , _) s (satΓ , satA) =
    hyp s satΓ satA

-- Move variable to conclusion:
--
--    Γ ⊢[T] ∀ v. B
-- ------------------
--    Γ, v ⊢[T] B

move-to-concl-v : (Γ : ℂ₀) (u : 𝕌) (T : ℂRes Γ) (B : ℂForm (ℂv Γ (𝕍𝕌 u))) → Rule
move-to-concl-v Γ u T B =
  rule [ rseq Γ T (∀· u B) ]
       (rseq (ℂv Γ (𝕍𝕌 u)) (↑ᵣ₀ T) B)

abstract
  move-to-concl-v-sat : (M : Model₀)
                        (Γ : ℂ₀) (u : 𝕌) (T : ℂRes Γ) (B : ℂForm (ℂv Γ (𝕍𝕌 u)))
                      → sat-rule M (move-to-concl-v Γ u T B)
  move-to-concl-v-sat M Γ u T B (hyp , _) (s ⹁ .(𝕍𝕌 u) ∶ v) satΓ =
    subst (λ x → ((M ≔ₛ (s ⹁ 𝕍𝕌 u ∶ v)) ≔ₜ x) ⊨ B) (sym (⟦↑ᵣ₀⟧ᵣ T s (𝕍𝕌 u) v))
          (hyp s satΓ v)

-- Move to conclusion:
--    Γ ⊢[T] A → B
-- ------------------
--    Γ, A ⊢[T] B

move-to-concl-ext : (Γ : ℂ₀) (T : ℂRes Γ) (A B : ℂForm Γ) → Rule
move-to-concl-ext Γ T A B =
  rule [ rseq Γ T (A →· B) ]
       (rseq (ℂe Γ A T) T B)

abstract
  move-to-concl-ext-sat : (M : Model₀)
                          {Γ : ℂ₀} (T : ℂRes Γ) (A B : ℂForm Γ)
                        → sat-rule M (move-to-concl-ext Γ T A B)
  move-to-concl-ext-sat M {Γ} T A B (hyp , _) s (satΓ , satA) =
    hyp s satΓ satA


-- Derived:
--
--   Γ , C , B ⊢ᵣ A
-- ------------------
--   Γ , B , C ⊢ᵣ A

rule-swap : (Γ : ℂ₀) (B C : ℂForm Γ) (x y : ℂCE Γ)
            (r : ℂCE (ℂx (ℂx Γ B x) C y))
            (A : ℂForm (ℂx (ℂx Γ B x) C y)) → Rule
rule-swap Γ B C x y r A =
  rule [ seq (ℂx (ℂx Γ C y) B x) r A ]
       (seq (ℂx (ℂx Γ B x) C y) r A)

abstract
  rule-swap-sat : (M : Model₀)
                  (Γ : ℂ₀) (B C : ℂForm Γ) (x y : ℂCE Γ)
                  (r : ℂCE (ℂx (ℂx Γ B x) C y))
                  (A : ℂForm (ℂx (ℂx Γ B x) C y))
                → sat-rule M (rule-swap Γ B C x y r A)
  rule-swap-sat M Γ B C x y r A (hyp , _) =
    rule-move-sat M Γ (ℂx ℂ⟨⟩ C y) B x r A (h₁ , lift tt)
    where
    h₁ : sat-sequent M (seq (ℂx (ℂx Γ C y) (↑ ⊆-refl B) (↑CE ⊆-refl x)) r A)
    h₁ = subst₂ (λ a b → sat-sequent M (seq (ℂx (ℂx Γ C y) a b) r A)) (sym (↑⊆-refl B)) (sym (↑CE⊆-refl x)) hyp

-- TODO: we need a general rule instead
--     Γ, u, B, C ⊢ᵣ A
-- -----------------------
--    Γ, v, u, B, C ⊢ᵣ A

rule-thin-v-v11 : (Γ : ℂ₀) (v u : 𝕍) (r : Res (ℂtxt Γ ، u)) (A B C : Form (ℂtxt Γ ، u)) (x y : CE (ℂtxt Γ ، u)) → Rule
rule-thin-v-v11 Γ v u r A B C x y =
  rule [ rseq (ℂx (ℂx (ℂv Γ u) B x) C y) r A ]
       (rseq (ℂx (ℂx (ℂv (ℂv Γ v) u) (↑₀، B) (↑CE₀، x)) (↑₀، C) (↑CE₀، y)) (↑ᵣ₀، r) (↑₀، A))

abstract
  rule-thin-v-v11-sat : (M : Model₀)
                        (Γ : ℂ₀) (v u : 𝕍) (r : Res (ℂtxt Γ ، u)) (A B C : Form (ℂtxt Γ ، u)) (x y : CE (ℂtxt Γ ، u))
                      → sat-rule M (rule-thin-v-v11 Γ v u r A B C x y)
  rule-thin-v-v11-sat M Γ v u r A B C x y (satA , _) ((s ⹁ .v ∶ v₂) ⹁ .u ∶ v₁) ((h₁ , h₂) , h₃) = ℍ₁
    where
    ℍ₁ : ((M ≔ₛ ((s ⹁ v ∶ v₂) ⹁ u ∶ v₁)) ≔ₜ (⟦ ↑ᵣ₀، r ⟧ᵣ ((s ⹁ v ∶ v₂) ⹁ u ∶ v₁))) ⊨ ↑₀، A
    ℍ₁ = →⊨-↑₀، {_} {(M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ₀، r ⟧ᵣ ((s ⹁ v ∶ v₂) ⹁ u ∶ v₁))} {v} v₂ {u} v₁ A
                (subst (λ x → (((M ≔ₛ s) ≔ₜ x) ≔ v₁) ⊨ A)
                       (sym (⟦↑ᵣ₀،⟧ᵣ s v v₂ u v₁ r))
                       (satA (s ⹁ u ∶ v₁)
                             ((h₁ , sat-ctxt-annot↑⊆→ {_} {_} {M ≔ₛ (s ⹁ u ∶ v₁)} B x _ ⊆₀، Sub⊆-⊆₀، h₂) ,
                              sat-ctxt-annot↑⊆→ {_} {_} {M ≔ₛ (s ⹁ u ∶ v₁)} C y _ ⊆₀، Sub⊆-⊆₀، h₃)))

-- TODO: we need a general rule instead
--     Γ, u, B ⊢ᵣ A
-- -----------------------
--    Γ, v, u, B ⊢ᵣ A

rule-thin-v-v1 : (Γ : ℂ₀) (v u : 𝕍) (r : Res (ℂtxt Γ ، u)) (A B : Form (ℂtxt Γ ، u)) (x : CE (ℂtxt Γ ، u)) → Rule
rule-thin-v-v1 Γ v u r A B x =
  rule [ rseq (ℂx (ℂv Γ u) B x) r A ]
       (rseq (ℂx (ℂv (ℂv Γ v) u) (↑₀، B) (↑CE₀، x)) (↑ᵣ₀، r) (↑₀، A))

abstract
  rule-thin-v-v1-sat : (M : Model₀)
                       (Γ : ℂ₀) (v u : 𝕍) (r : Res (ℂtxt Γ ، u)) (A B : Form (ℂtxt Γ ، u)) (x : CE (ℂtxt Γ ، u))
                     → sat-rule M (rule-thin-v-v1 Γ v u r A B x)
  rule-thin-v-v1-sat M Γ v u r A B x (satA , _) ((s ⹁ .v ∶ v₂) ⹁ .u ∶ v₁) (h₁ , h₂) = ℍ₁
    where
    ℍ₁ : ((M ≔ₛ ((s ⹁ v ∶ v₂) ⹁ u ∶ v₁)) ≔ₜ (⟦ ↑ᵣ₀، r ⟧ᵣ ((s ⹁ v ∶ v₂) ⹁ u ∶ v₁))) ⊨ ↑₀، A
    ℍ₁ = →⊨-↑₀، {_} {(M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ₀، r ⟧ᵣ ((s ⹁ v ∶ v₂) ⹁ u ∶ v₁))} {v} v₂ {u} v₁ A
                (subst (λ x → (((M ≔ₛ s) ≔ₜ x) ≔ v₁) ⊨ A)
                       (sym (⟦↑ᵣ₀،⟧ᵣ s v v₂ u v₁ r))
                       (satA (s ⹁ u ∶ v₁)
                             (h₁ , sat-ctxt-annot↑⊆→ {_} {_} {M ≔ₛ (s ⹁ u ∶ v₁)} B x _ ⊆₀، Sub⊆-⊆₀، h₂)))

\end{code}
