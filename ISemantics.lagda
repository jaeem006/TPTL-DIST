EXPERIMENT: indexed sequents and rules

\begin{code}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open import Data.Nat
open import Data.Nat.Properties
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

module ISemantics(W : World)
       where

𝔻 : Set
𝔻 = ℕ

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import WorldUtil(W)
open import Semantics(𝔻)(W)
open import Decidable(W)

open World.World W

data 𝕀ℂ (Γ : Ctxt) : Ctxt → Set₁ where
  -- empty context
  𝕀ℂ⟨⟩ : 𝕀ℂ Γ Γ
  -- context extension with an annotated hypothesis
  𝕀ℂx  : {Δ : Ctxt} (c : 𝕀ℂ Γ Δ)
         {Φ Ψ : Ctxt}
         (f : Form Φ)
         (a : CE Ψ)
         (i : Φ ⊆ Δ) (j : Ψ ⊆ Δ) → 𝕀ℂ Γ Δ
  -- context extension with a variable
  𝕀ℂv  : {Δ : Ctxt} (c : 𝕀ℂ Γ Δ) (v : 𝕍) → 𝕀ℂ Γ (Δ ، v)

𝕀ℂe : {Γ Δ : Ctxt} (c : 𝕀ℂ Γ Δ)
      {Φ Ψ : Ctxt}
      (f : Form Φ)
      (a : Res Ψ)
      (i : Φ ⊆ Δ) (j : Ψ ⊆ Δ) → 𝕀ℂ Γ Δ
𝕀ℂe {Γ} {Δ} c {Φ} {Ψ} f a i j = 𝕀ℂx c f (CEr a) i j

_⨟_ : {Γ Δ Ω : Ctxt} (c : 𝕀ℂ Γ Δ) (d : 𝕀ℂ Δ Ω) → 𝕀ℂ Γ Ω
c ⨟ 𝕀ℂ⟨⟩ = c
c ⨟ 𝕀ℂx d f a i j = 𝕀ℂx (c ⨟ d) f a i j
c ⨟ 𝕀ℂv d v = 𝕀ℂv (c ⨟ d) v

𝕀ℂ⊆ : {Γ Δ : Ctxt} (c : 𝕀ℂ Γ Δ) → Γ ⊆ Δ
𝕀ℂ⊆ {Γ} {Δ} 𝕀ℂ⟨⟩ = ⊆r
𝕀ℂ⊆ {Γ} {Δ} (𝕀ℂx c f a i j) = 𝕀ℂ⊆ c
𝕀ℂ⊆ {Γ} {Δ} (𝕀ℂv c v) = ⊆-trans (𝕀ℂ⊆ c) ⊆₀

data ISequent : Set₁ where
  iseq : ({Γ} : Ctxt)
         (Δ   : 𝕀ℂ ⟨⟩ Γ)
         ({Φ} : Ctxt)
         ({Ψ} : Ctxt)
         (T   : CE Φ)
         (C   : Form Ψ)
         (I   : Φ ⊆ Γ)
         (J   : Ψ ⊆ Γ)
       → ISequent
  inonEmpty : ({Γ} : Ctxt)
              (Δ   : 𝕀ℂ ⟨⟩ Γ)
              ({Φ} : Ctxt)
              (T   : CE Φ)
              (I   : Φ ⊆ Γ)
            → ISequent

record IRule : Set₁ where
  constructor irule
  field
    Premises   : List ISequent
    Conclusion : ISequent


-- Semantics of contexts, sequents, and rules

sat-ictxt : {Γ Δ : Ctxt} (c : 𝕀ℂ Γ Δ) (M : Model Δ) → Set₁
sat-ictxt {Γ} {.Γ} 𝕀ℂ⟨⟩ M = Lift _ ⊤
sat-ictxt {Γ} {Δ} (𝕀ℂx c f a i j) M = sat-ictxt c M × sat-ctxt-annot (↑ i f) (↑CE j a) M
sat-ictxt {Γ} {Δ} (𝕀ℂv c v) M = sat-ictxt c (Model،→ M)

sat-isequent : (M : Model₀) (s : ISequent) → Set₁
sat-isequent M (iseq {c} Δ {Φ} {Ψ} T C I J) =
    (s : Sub c)
  → sat-ictxt Δ (M ≔ₛ s)
  → sat-ctxt-annot (↑ J C) (↑CE I T) (M ≔ₛ s)
sat-isequent M (inonEmpty {c} Δ {Φ} T I) =
    (s : Sub c)
  → sat-ictxt Δ (M ≔ₛ s)
  → isNonEmpty (M ≔ₛ s) (↑CE I T)

sat-isequents : (M : Model₀) (l : List ISequent) → Set₁
sat-isequents M [] = Lift _ ⊤
sat-isequents M (s ∷ l) = sat-isequent M s × sat-isequents M l

sat-irule : (M : Model₀) (r : IRule) → Set₁
sat-irule M (irule Premises Conclusion) =
  sat-isequents M Premises → sat-isequent M Conclusion


-- Properties of sequents

sat-isequents++ₗ : (M : Model₀) (l k : List ISequent)
                 → sat-isequents M (l ++ k)
                 → sat-isequents M l
sat-isequents++ₗ M [] k h = lift tt
sat-isequents++ₗ M (x ∷ l) k (h , q) = h , sat-isequents++ₗ M l k q

sat-isequents++ᵣ : (M : Model₀) (l k : List ISequent)
                 → sat-isequents M (l ++ k)
                 → sat-isequents M k
sat-isequents++ᵣ M [] k h = h
sat-isequents++ᵣ M (x ∷ l) k (h , q) = sat-isequents++ᵣ M l k q

sat-isequents++ : (M : Model₀) (l k : List ISequent)
                → sat-isequents M l
                → sat-isequents M k
                → sat-isequents M (l ++ k)
sat-isequents++ M [] k h q = q
sat-isequents++ M (x ∷ l) k (h₁ , h₂) q = h₁ , (sat-isequents++ M l k h₂ q)


-- Correspondence between both kinds of contexts

mutual
  𝕀ℂ⇒ℂ : {Γ Δ : Ctxt} (c : 𝕀ℂ Γ Δ) → ℂ Γ
  ℂtxt-𝕀ℂ⇒ℂ : {Γ Δ : Ctxt} (c : 𝕀ℂ Γ Δ) → ℂtxt (𝕀ℂ⇒ℂ c) ≡ Δ

  𝕀ℂ⇒ℂ {Γ} {Δ} 𝕀ℂ⟨⟩ = ℂ⟨⟩
  𝕀ℂ⇒ℂ {Γ} {Δ} (𝕀ℂx c f a i j) = ℂx (𝕀ℂ⇒ℂ c) (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ c)) (↑ i f)) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ c)) (↑CE j a))
  𝕀ℂ⇒ℂ {Γ} {Δ} (𝕀ℂv c v) = ℂv (𝕀ℂ⇒ℂ c) v

  ℂtxt-𝕀ℂ⇒ℂ {Γ} {Δ} 𝕀ℂ⟨⟩ = refl
  ℂtxt-𝕀ℂ⇒ℂ {Γ} {Δ} (𝕀ℂx c f a i j) = ℂtxt-𝕀ℂ⇒ℂ c
  ℂtxt-𝕀ℂ⇒ℂ {Γ} {Δ} (𝕀ℂv c v) = cong (_، v) (ℂtxt-𝕀ℂ⇒ℂ c)

ℂ⇒𝕀ℂ : {Γ : Ctxt} (c : ℂ Γ) → 𝕀ℂ Γ (ℂtxt c)
ℂ⇒𝕀ℂ {Γ} ℂ⟨⟩ = 𝕀ℂ⟨⟩
ℂ⇒𝕀ℂ {Γ} (ℂx c f a) = 𝕀ℂx (ℂ⇒𝕀ℂ c) f a ⊆r ⊆r
ℂ⇒𝕀ℂ {Γ} (ℂv c v) = 𝕀ℂv (ℂ⇒𝕀ℂ c) v

ISequent⇒Sequent : ISequent → Sequent
ISequent⇒Sequent (iseq Δ T C I J) =
  seq (𝕀ℂ⇒ℂ Δ)
      (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T))
      (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑ J C))
ISequent⇒Sequent (inonEmpty Δ T I) =
  nonEmpty (𝕀ℂ⇒ℂ Δ)
           (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T))

Sequent⇒ISequent : Sequent → ISequent
Sequent⇒ISequent (seq Δ T C) =
  iseq (ℂ⇒𝕀ℂ Δ) T C ⊆r ⊆r
Sequent⇒ISequent (nonEmpty Δ T) =
  inonEmpty (ℂ⇒𝕀ℂ Δ) T ⊆r

-- Note that given (s : ISequent), then (Sequent⇒ISequent (ISequent⇒Sequent s)) is not equal to s
-- because ISequent⇒Sequent applies the liftings to the conclusion, and Sequent⇒ISequent leaves them there.
-- ... and similarly for the other syntactic forms ...

ISequents⇒Sequents : List ISequent → List Sequent
ISequents⇒Sequents [] = []
ISequents⇒Sequents (x ∷ l) = ISequent⇒Sequent x ∷ ISequents⇒Sequents l

Sequents⇒ISequents : List Sequent → List ISequent
Sequents⇒ISequents [] = []
Sequents⇒ISequents (x ∷ l) = Sequent⇒ISequent x ∷ Sequents⇒ISequents l

IRule⇒Rule : IRule → Rule
IRule⇒Rule (irule Premises Conclusion) =
  rule (ISequents⇒Sequents Premises) (ISequent⇒Sequent Conclusion)

Rule⇒IRule : Rule → IRule
Rule⇒IRule (rule Premises Conclusion) =
  irule (Sequents⇒ISequents Premises) (Sequent⇒ISequent Conclusion)

sat-ictxt-ℂ⇒𝕀ℂ→ : {Γ : Ctxt} (c : ℂ Γ) (M : ℂModel c)
                → sat-ictxt (ℂ⇒𝕀ℂ c) M
                → sat-ctxt c M
sat-ictxt-ℂ⇒𝕀ℂ→ {Γ} ℂ⟨⟩ M h = lift tt
sat-ictxt-ℂ⇒𝕀ℂ→ {Γ} (ℂx c f a) M (h , q) =
  sat-ictxt-ℂ⇒𝕀ℂ→ c M h ,
  subst₂ (λ x y → sat-ctxt-annot x y M) (↑⊆-refl f) (↑CE⊆-refl a) q
sat-ictxt-ℂ⇒𝕀ℂ→ {Γ} (ℂv c v) M h =
  sat-ictxt-ℂ⇒𝕀ℂ→ c (Model،→ M) h

sat-ictxt-ℂ⇒𝕀ℂ : {Γ : Ctxt} (c : ℂ Γ) (M : ℂModel c)
               → sat-ctxt c M
               → sat-ictxt (ℂ⇒𝕀ℂ c) M
sat-ictxt-ℂ⇒𝕀ℂ {Γ} ℂ⟨⟩ M h = lift tt
sat-ictxt-ℂ⇒𝕀ℂ {Γ} (ℂx c f a) M (h , q) =
  sat-ictxt-ℂ⇒𝕀ℂ c M h ,
  subst₂ (λ x y → sat-ctxt-annot x y M) (sym (↑⊆-refl f)) (sym (↑CE⊆-refl a)) q
sat-ictxt-ℂ⇒𝕀ℂ {Γ} (ℂv c v) M h =
  sat-ictxt-ℂ⇒𝕀ℂ c (Model،→ M) h

sat-isequent-Sequent⇒ISequent : (M : Model₀) (s : Sequent)
                              → sat-sequent M s
                              → sat-isequent M (Sequent⇒ISequent s)
sat-isequent-Sequent⇒ISequent M (seq Δ T C) h s satΓ =
  subst₂ (λ x y → sat-ctxt-annot y x (M ≔ₛ s))
         (sym (↑CE⊆-refl T))
         (sym (↑⊆-refl C))
         (h s (sat-ictxt-ℂ⇒𝕀ℂ→ Δ (M ≔ₛ s) satΓ))
sat-isequent-Sequent⇒ISequent M (nonEmpty Δ T) h s satΓ =
  subst (isNonEmpty (M ≔ₛ s))
        (sym (↑CE⊆-refl T))
        (h s (sat-ictxt-ℂ⇒𝕀ℂ→ Δ (M ≔ₛ s) satΓ))

sat-isequent-Sequent⇒ISequent→ : (M : Model₀) (s : Sequent)
                               → sat-isequent M (Sequent⇒ISequent s)
                               → sat-sequent M s
sat-isequent-Sequent⇒ISequent→ M (seq Δ T C) h s satΓ =
  subst₂ (λ x y → sat-ctxt-annot y x (M ≔ₛ s))
         (↑CE⊆-refl T)
         (↑⊆-refl C)
         (h s (sat-ictxt-ℂ⇒𝕀ℂ Δ (M ≔ₛ s) satΓ))
sat-isequent-Sequent⇒ISequent→ M (nonEmpty Δ T) h s satΓ =
  subst (isNonEmpty (M ≔ₛ s))
        (↑CE⊆-refl T)
        (h s (sat-ictxt-ℂ⇒𝕀ℂ Δ (M ≔ₛ s) satΓ))

sat-isequents-Sequents⇒ISequents→ : (M : Model₀) (l : List Sequent)
                                  → sat-isequents M (Sequents⇒ISequents l)
                                  → sat-sequents M l
sat-isequents-Sequents⇒ISequents→ M [] h = lift tt
sat-isequents-Sequents⇒ISequents→ M (x ∷ l) (h , q) =
  (sat-isequent-Sequent⇒ISequent→ M x h) ,
  (sat-isequents-Sequents⇒ISequents→ M l q)

sat-irule-Rule⇒IRule : (M : Model₀) (r : Rule)
                     → sat-rule M r
                     → sat-irule M (Rule⇒IRule r)
sat-irule-Rule⇒IRule M (rule H S) h hyps =
  sat-isequent-Sequent⇒ISequent M S (h (sat-isequents-Sequents⇒ISequents→ M H hyps))

Model،→≔ₛ : {Γ : Ctxt} {u : 𝕍} {Ω : Ctxt} (M : Model Ω) (s : Sub (Γ ، u))
          → Model،→ (M ≔ₛ s) ≡ M ≔ₛ (Sub،→ s)
Model،→≔ₛ {Γ} {u} {Ω} M s = refl

⋆Sub-cong، : {Γ Δ : Ctxt} (s : Sub Γ) (v : 𝕍) (u : ⟦𝕍⟧ v)
            (e : Γ ≡ Δ)
          → ⋆Sub (cong (_، v) e) (s ⹁ v ∶ u) ≡ (⋆Sub e s ⹁ v ∶ u)
⋆Sub-cong، {Γ} {Δ} s v u refl = refl

⋆Sub-sym-cong، : {Γ Δ : Ctxt} (s : Sub Δ) (v : 𝕍) (u : ⟦𝕍⟧ v)
                 (e : Γ ≡ Δ)
               → ⋆Sub (sym (cong (_، v) e)) (s ⹁ v ∶ u) ≡ (⋆Sub (sym e) s ⹁ v ∶ u)
⋆Sub-sym-cong، {Γ} {Δ} s v u refl = refl

⋆Res⋆Res : {Γ Δ : Ctxt} (r : Res Δ) (e : Γ ≡ Δ)
         → ⋆Res e (⋆Res (sym e) r) ≡ r
⋆Res⋆Res {Γ} {Δ} r refl = refl

⋆CE⋆CE : {Γ Δ : Ctxt} (r : CE Δ) (e : Γ ≡ Δ)
         → ⋆CE e (⋆CE (sym e) r) ≡ r
⋆CE⋆CE {Γ} {Δ} r refl = refl

⋆Sub⋆Sub : {Γ Δ : Ctxt} (s : Sub Δ) (e : Γ ≡ Δ)
         → ⋆Sub e (⋆Sub (sym e) s) ≡ s
⋆Sub⋆Sub {Γ} {Δ} s refl = refl

⋆Sub⋆Sub′ : {Γ Δ : Ctxt} (s : Sub Γ) (e : Γ ≡ Δ)
          → ⋆Sub (sym e) (⋆Sub e s) ≡ s
⋆Sub⋆Sub′ {Γ} {Δ} s refl = refl

⋆Form⋆Form : {Γ Δ : Ctxt} (f : Form Δ) (e : Γ ≡ Δ)
           → ⋆Form e (⋆Form (sym e) f) ≡ f
⋆Form⋆Form {Γ} {Δ} f refl = refl

⋆Interval⋆Interval : {Γ Δ : Ctxt} (i : Interval Δ) (e : Γ ≡ Δ)
                   → ⋆Interval e (⋆Interval (sym e) i) ≡ i
⋆Interval⋆Interval {Γ} {Δ} i refl = refl

≔ₛ≔ₜ⊨-⋆Form : {Γ Δ Ω : Ctxt} (M : Model Δ) (s : Sub Γ) (f : Form Γ) (r : Res Γ)
              (e : Γ ≡ Ω)
            → ((M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)) ⊨ f
            → ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ ⋆Res e r ⟧ᵣ (⋆Sub e s))) ⊨ ⋆Form e f
≔ₛ≔ₜ⊨-⋆Form {Γ} {Δ} {Ω} M s f r refl h = h

sat-ctxt-annot-⋆Form : {Γ Δ Ω : Ctxt} (M : Model Δ) (s : Sub Γ) (f : Form Γ) (c : CE Γ)
                       (e : Γ ≡ Ω)
                     → sat-ctxt-annot f c (M ≔ₛ s)
                     → sat-ctxt-annot (⋆Form e f) (⋆CE e c) (M ≔ₛ ⋆Sub e s)
sat-ctxt-annot-⋆Form {Γ} {Δ} {Ω} M s f c refl h = h

isNonEmpty-⋆CE : {Γ Δ Ω : Ctxt} (M : Model Δ) (s : Sub Γ)  (c : CE Γ)
                 (e : Γ ≡ Ω)
               → isNonEmpty (M ≔ₛ s) c
               → isNonEmpty (M ≔ₛ ⋆Sub e s) (⋆CE e c)
isNonEmpty-⋆CE {Γ} {Δ} {Ω} M s c refl h = h

sat-ctxt-annot-ℂtxt-𝕀ℂ⇒ℂ : {Γ Δ Ω : Ctxt} (M : Model Ω) (s : Sub Γ) (e : Γ ≡ Δ)
                           {Φ Ψ : Ctxt} (f : Form Φ) (a : CE Ψ) (i : Φ ⊆ Δ) (j : Ψ ⊆ Δ)
                         → sat-ctxt-annot (⋆Form (sym e) (↑ i f)) (⋆CE (sym e) (↑CE j a)) (M ≔ₛ s)
                         → sat-ctxt-annot (↑ i f) (↑CE j a) (M ≔ₛ ⋆Sub e s)
sat-ctxt-annot-ℂtxt-𝕀ℂ⇒ℂ {Γ} {Δ} {Ω} M s refl {Φ} {Ψ} f a i j h = h

sat-ctxt-annot-ℂtxt-𝕀ℂ⇒ℂ′ : {Γ Δ Ω : Ctxt} (M : Model Ω) (s : Sub Δ) (e : Δ ≡ Γ)
                            {Φ Ψ : Ctxt} (f : Form Φ) (a : CE Ψ) (i : Φ ⊆ Δ) (j : Ψ ⊆ Δ)
                          → sat-ctxt-annot (↑ i f) (↑CE j a) (M ≔ₛ s)
                          → sat-ctxt-annot (⋆Form e (↑ i f)) (⋆CE e (↑CE j a)) (M ≔ₛ ⋆Sub e s)
sat-ctxt-annot-ℂtxt-𝕀ℂ⇒ℂ′ {Γ} {Δ} {Ω} M s refl {Φ} {Ψ} f a i j h = h

sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ : {Γ Δ Ω : Ctxt} (c : 𝕀ℂ Γ Δ) (M : Model Ω) (s : ℂSub (𝕀ℂ⇒ℂ c))
                    → sat-ictxt (ℂ⇒𝕀ℂ (𝕀ℂ⇒ℂ c)) (M ≔ₛ s)
                    → sat-ictxt c (M ≔ₛ ⋆Sub (ℂtxt-𝕀ℂ⇒ℂ c) s)
sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ {Γ} {Δ} {Ω} 𝕀ℂ⟨⟩ M s h = lift tt
sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ {Γ} {Δ} {Ω} (𝕀ℂx c f a i j) M s (h , q) =
  sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ c M s h ,
  sat-ctxt-annot-ℂtxt-𝕀ℂ⇒ℂ M s (ℂtxt-𝕀ℂ⇒ℂ c) f a i j
    (subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ s))
            (↑⊆-refl (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ c)) (↑ i f)))
            (↑CE⊆-refl (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ c)) (↑CE j a))) q)
sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ {Γ} {Δ} {Ω} (𝕀ℂv c v) M (s ⹁ .v ∶ v₁) h =
  subst (λ x → sat-ictxt c (M ≔ₛ Sub،→ x))
        (sym (⋆Sub-cong، s v v₁ (ℂtxt-𝕀ℂ⇒ℂ c)))
        (sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ c M s h)

sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ : {Γ Δ Ω : Ctxt} (c : 𝕀ℂ Γ Δ) (M : Model Ω) (s : Sub Δ)
                     → sat-ictxt c (M ≔ₛ s)
                     → sat-ictxt (ℂ⇒𝕀ℂ (𝕀ℂ⇒ℂ c)) (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ c)) s)
sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ {Γ} {Δ} {Ω} 𝕀ℂ⟨⟩ M s h = lift tt
sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ {Γ} {Δ} {Ω} (𝕀ℂx c f a i j) M s (h , q) =
  sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ c M s h ,
  subst₂ (λ x y → sat-ctxt-annot x y (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ c)) s))
         (sym (↑⊆-refl (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ c)) (↑ i f))))
         (sym (↑CE⊆-refl (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ c)) (↑CE j a))))
         (sat-ctxt-annot-ℂtxt-𝕀ℂ⇒ℂ′ M s (sym (ℂtxt-𝕀ℂ⇒ℂ c)) f a i j q)
sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ {Γ} {Δ} {Ω} (𝕀ℂv c v) M (s ⹁ .v ∶ v₁) h =
  subst (λ x → sat-ictxt (ℂ⇒𝕀ℂ (𝕀ℂ⇒ℂ c)) (M ≔ₛ Sub،→ x))
        (sym (⋆Sub-sym-cong، s v v₁ (ℂtxt-𝕀ℂ⇒ℂ c)))
        (sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ c M s h)

sat-sequent-ISequent⇒Sequent : (M : Model₀) (s : ISequent)
                             → sat-isequent M s
                             → sat-sequent M (ISequent⇒Sequent s)
sat-sequent-ISequent⇒Sequent M (iseq {Γ} Δ {Φ} {Ψ} T C I J) h s satΓ = h₁
  where
  satΓ₀ : sat-ictxt (ℂ⇒𝕀ℂ (𝕀ℂ⇒ℂ Δ)) (M ≔ₛ s)
  satΓ₀ = sat-ictxt-ℂ⇒𝕀ℂ (𝕀ℂ⇒ℂ Δ) (M ≔ₛ s) satΓ

  h₀ : sat-ctxt-annot (↑ J C) (↑CE I T) (M ≔ₛ ⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s)
  h₀ = h (⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s) (sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ Δ M s satΓ₀)

  q₀ : sat-ctxt-annot (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑ J C)) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)) (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s))
  q₀ = sat-ctxt-annot-⋆Form M (⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s) (↑ J C) (↑CE I T) (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) h₀

  h₁ : sat-ctxt-annot (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑ J C)) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)) (M ≔ₛ s)
  h₁ = subst (λ x → sat-ctxt-annot (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑ J C)) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)) (M ≔ₛ x))
             (⋆Sub⋆Sub′ s (ℂtxt-𝕀ℂ⇒ℂ Δ))
             q₀
sat-sequent-ISequent⇒Sequent M (inonEmpty {Γ} Δ {Φ} T I) h s satΓ = h₁
  where
  satΓ₀ : sat-ictxt (ℂ⇒𝕀ℂ (𝕀ℂ⇒ℂ Δ)) (M ≔ₛ s)
  satΓ₀ = sat-ictxt-ℂ⇒𝕀ℂ (𝕀ℂ⇒ℂ Δ) (M ≔ₛ s) satΓ

  h₀ : isNonEmpty (M ≔ₛ ⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s) (↑CE I T)
  h₀ = h (⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s) (sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ Δ M s satΓ₀)

  q₀ : isNonEmpty (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s)) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T))
  q₀ = isNonEmpty-⋆CE M (⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) s) (↑CE I T) (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) h₀

  h₁ : isNonEmpty (M ≔ₛ s) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T))
  h₁ = subst (λ x → isNonEmpty (M ≔ₛ x) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)))
             (⋆Sub⋆Sub′ s (ℂtxt-𝕀ℂ⇒ℂ Δ))
             q₀

sat-sequent-ISequent⇒Sequent→ : (M : Model₀) (s : ISequent)
                              → sat-sequent M (ISequent⇒Sequent s)
                              → sat-isequent M s
sat-sequent-ISequent⇒Sequent→ M (iseq {Γ} Δ {Φ} {Ψ} T C I J) h s satΓ = h₁
  where
  h₀ : sat-ctxt-annot (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑ J C)) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)) (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s)
  h₀ = h (⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s)
         (sat-ictxt-ℂ⇒𝕀ℂ→ (𝕀ℂ⇒ℂ Δ) (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s) (sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ Δ M s satΓ))

  q₀ : sat-ctxt-annot (⋆Form (ℂtxt-𝕀ℂ⇒ℂ Δ) (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑ J C))) (⋆CE (ℂtxt-𝕀ℂ⇒ℂ Δ) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T))) (M ≔ₛ ⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) (⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s))
  q₀ = sat-ctxt-annot-⋆Form M (⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s) (⋆Form (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑ J C)) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)) (ℂtxt-𝕀ℂ⇒ℂ Δ) h₀

  h₁ : sat-ctxt-annot (↑ J C) (↑CE I T) (M ≔ₛ s)
  h₁ = subst₃ (λ x y z → sat-ctxt-annot z y (M ≔ₛ x))
              (⋆Sub⋆Sub s (ℂtxt-𝕀ℂ⇒ℂ Δ))
              (⋆CE⋆CE (↑CE I T) (ℂtxt-𝕀ℂ⇒ℂ Δ))
              (⋆Form⋆Form (↑ J C) (ℂtxt-𝕀ℂ⇒ℂ Δ))
              q₀
sat-sequent-ISequent⇒Sequent→ M (inonEmpty {Γ} Δ {Φ} T I) h s satΓ = h₁
  where
  h₀ : isNonEmpty (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T))
  h₀ = h (⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s)
         (sat-ictxt-ℂ⇒𝕀ℂ→ (𝕀ℂ⇒ℂ Δ) (M ≔ₛ ⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s) (sat-ictxt-ℂ⇒𝕀ℂ-𝕀ℂ⇒ℂ→ Δ M s satΓ))

  q₀ : isNonEmpty (M ≔ₛ ⋆Sub (ℂtxt-𝕀ℂ⇒ℂ Δ) (⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s)) (⋆CE (ℂtxt-𝕀ℂ⇒ℂ Δ) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)))
  q₀ = isNonEmpty-⋆CE M (⋆Sub (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) s) (⋆CE (sym (ℂtxt-𝕀ℂ⇒ℂ Δ)) (↑CE I T)) (ℂtxt-𝕀ℂ⇒ℂ Δ) h₀

  h₁ : isNonEmpty (M ≔ₛ s) (↑CE I T)
  h₁ = subst₂ (λ x y → isNonEmpty (M ≔ₛ x) y)
              (⋆Sub⋆Sub s (ℂtxt-𝕀ℂ⇒ℂ Δ))
              (⋆CE⋆CE (↑CE I T) (ℂtxt-𝕀ℂ⇒ℂ Δ))
              q₀

sat-sequents-ISequents⇒Sequents→ : (M : Model₀) (s : List ISequent)
                                 → sat-sequents M (ISequents⇒Sequents s)
                                 → sat-isequents M s
sat-sequents-ISequents⇒Sequents→ M [] h = lift tt
sat-sequents-ISequents⇒Sequents→ M (x ∷ s) (h , q) =
  sat-sequent-ISequent⇒Sequent→ M x h ,
  sat-sequents-ISequents⇒Sequents→ M s q

sat-rule-IRule⇒Rule : (M : Model₀) (r : IRule)
                    → sat-irule M r
                    → sat-rule M (IRule⇒Rule r)
sat-rule-IRule⇒Rule M (irule H S) h hyps =
  sat-sequent-ISequent⇒Sequent M S (h (sat-sequents-ISequents⇒Sequents→ M H hyps))

-- Given (r : IRule) such that (sat-irule M r)
--   1. sat-rule M (IRule⇒Rule r)                 using sat-rule-IRule⇒Rule
--   2. sat-irule M (Rule⇒IRule (IRule⇒Rule r))   using sat-irule-Rule⇒IRule


-- Examples of rules

--       Γ, Δ ⊢ᵣ A
-- --------------------
--    Γ, ¬ A, Δ ⊢ᵣ B

irule¬E : {c d : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (Δ : 𝕀ℂ c d)
          {e f : Ctxt}
          (r : Res e) (A : Form f)
          (Φ : Ctxt)
          (Ψ : Ctxt)
          (𝟙 : f ⊆ c)
          (𝟚 : e ⊆ c)
          (𝟛 : Φ ⊆ d)
          (𝟜 : Ψ ⊆ d)
          (R : Res Φ) (B : Form Ψ) → IRule
irule¬E {c} {d} Γ Δ r A Φ Ψ 𝟙 𝟚 𝟛 𝟜 R B =
  irule [ iseq (Γ ⨟ Δ) (CEr r) A (⊆-trans 𝟚 (𝕀ℂ⊆ Δ)) (⊆-trans 𝟙 (𝕀ℂ⊆ Δ)) ]
        (iseq (𝕀ℂe Γ (¬· A) r 𝟙 𝟚 ⨟ Δ) (CEr R) B 𝟛 𝟜)

rule¬E-sat-ictxt₁ : {Γ Δ Φ Ψ : Ctxt} (c : 𝕀ℂ ⟨⟩ Γ) (d : 𝕀ℂ Γ Δ)
                    (r : Res Ψ) (A : Form Φ)
                    (M : Model₀)
                    (s : Sub Δ)
                    (i : Φ ⊆ Γ)
                    (j : Ψ ⊆ Γ)
                  → sat-ictxt (𝕀ℂe c (¬· A) r i j ⨟ d) (M ≔ₛ s)
                  → ¬ ((M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ (⊆-trans j (𝕀ℂ⊆ d)) r ⟧ᵣ s)) ⊨ ↑ (⊆-trans i (𝕀ℂ⊆ d)) A
rule¬E-sat-ictxt₁ {Γ} {Δ} {Φ} {Ψ} c 𝕀ℂ⟨⟩ r A M s i j (h , q) = q
rule¬E-sat-ictxt₁ {Γ} {Δ} {Φ} {Ψ} c (𝕀ℂx d f a i₁ j₁) r A M s i j (h , q) z =
  rule¬E-sat-ictxt₁ c d r A M s i j h z
rule¬E-sat-ictxt₁ {Γ} {Δ} {Φ} {Ψ} c (𝕀ℂv d v) r A M (s ⹁ .v ∶ v₁) i j h z =
  rule¬E-sat-ictxt₁ c d r A M s i j h
    (⊨-↑₀→ {_} {(M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ (⊆-trans j (𝕀ℂ⊆ d)) r ⟧ᵣ s)} {↑ (⊆-trans i (𝕀ℂ⊆ d)) A} {v} v₁
      (subst (λ x → (((M ≔ₛ s) ≔ₜ x) ≔ v₁) ⊨ ↑₀ (↑ (⊆-trans i (𝕀ℂ⊆ d)) A))
             (⟦↑ᵣ₀⟧ᵣ (↑ᵣ (⊆-trans j (𝕀ℂ⊆ d)) r) s v v₁)
             (subst₂ (λ x y → (((M ≔ₛ s) ≔ₜ (⟦ x ⟧ᵣ (s ⹁ v ∶ v₁))) ≔ v₁) ⊨ y)
                     (↑ᵣ-trans (λ x → ∈CtxtS v (𝕀ℂ⊆ d (j x))) (λ x → 𝕀ℂ⊆ d (j x)) ⊆₀ r (λ _ _ → refl))
                     (↑-trans (λ x → ∈CtxtS v (𝕀ℂ⊆ d (i x))) (λ x → 𝕀ℂ⊆ d (i x)) ⊆₀ A (λ _ _ → refl))
                     z)))

rule¬E-sat-ictxt₂ : {Γ Δ Φ Ψ : Ctxt} (c : 𝕀ℂ ⟨⟩ Γ) (d : 𝕀ℂ Γ Δ)
                    (r : Res Ψ) (A : Form Φ)
                    (M : Model₀)
                    (s : Sub Δ)
                    (i : Φ ⊆ Γ)
                    (j : Ψ ⊆ Γ)
                  → sat-ictxt (𝕀ℂe c (¬· A) r i j ⨟ d) (M ≔ₛ s)
                  → sat-ictxt (c ⨟ d) (M ≔ₛ s)
rule¬E-sat-ictxt₂ {Γ} {Δ} {Φ} {Ψ} c 𝕀ℂ⟨⟩ r A M s i j (h , q) = h
rule¬E-sat-ictxt₂ {Γ} {Δ} {Φ} {Ψ} c (𝕀ℂx d f a i₁ j₁) r A M s i j (h , q) =
  rule¬E-sat-ictxt₂ c d r A M s i j h , q
rule¬E-sat-ictxt₂ {Γ} {Δ} {Φ} {Ψ} c (𝕀ℂv d v) r A M s i j h =
  rule¬E-sat-ictxt₂ c d r A M (Sub،→ s) i j h

abstract
  irule¬E-sat : (M : Model₀) {c d : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (Δ : 𝕀ℂ c d)
                {e f : Ctxt}
                (r : Res e) (A : Form f)
                (Φ : Ctxt)
                (Ψ : Ctxt)
                (𝟙 : f ⊆ c)
                (𝟚 : e ⊆ c)
                (𝟛 : Φ ⊆ d)
                (𝟜 : Ψ ⊆ d)
                (R : Res Φ) (B : Form Ψ)
              → sat-irule M (irule¬E Γ Δ r A Φ Ψ 𝟙 𝟚 𝟛 𝟜 R B)
  irule¬E-sat M {c} {d} Γ Δ {e} {f} r A Φ Ψ 𝟙 𝟚 𝟛 𝟜 R B (hyp , _) s satΓ =
    ⊥-elim (𝕀 𝕀𝕀)
    where
    𝕀𝕀 : ((M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ (⊆-trans 𝟚 (𝕀ℂ⊆ Δ)) r ⟧ᵣ s)) ⊨ ↑ (⊆-trans 𝟙 (𝕀ℂ⊆ Δ)) A
    𝕀𝕀 = hyp s (rule¬E-sat-ictxt₂ Γ Δ r A M s 𝟙 𝟚 satΓ)

    𝕀 : ¬ ((M ≔ₛ s) ≔ₜ (⟦ ↑ᵣ (⊆-trans 𝟚 (𝕀ℂ⊆ Δ)) r ⟧ᵣ s)) ⊨ ↑ (⊆-trans 𝟙 (𝕀ℂ⊆ Δ)) A
    𝕀 = rule¬E-sat-ictxt₁ Γ Δ r A M s 𝟙 𝟚 satΓ

--       Γ, Δ ⊢ᵣ A
-- --------------------
--    Γ, ⊥, Δ ⊢ᵣ B

irule⊥E : {c d : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (Δ : 𝕀ℂ c d)
          {e f : Ctxt}
          (r : Res e)
          (Φ : Ctxt)
          (Ψ : Ctxt)
          (𝟙 : f ⊆ c)
          (𝟚 : e ⊆ c)
          (𝟛 : Φ ⊆ d)
          (𝟜 : Ψ ⊆ d)
          (R : Res Φ) (B : Form Ψ) → IRule
irule⊥E {c} {d} Γ Δ r Φ Ψ 𝟙 𝟚 𝟛 𝟜 R B =
  irule [] (iseq (𝕀ℂe Γ ⊥· r 𝟙 𝟚 ⨟ Δ) (CEr R) B 𝟛 𝟜)

rule⊥E-sat-ictxt₁ : {Γ Δ Φ Ψ : Ctxt} (c : 𝕀ℂ ⟨⟩ Γ) (d : 𝕀ℂ Γ Δ)
                    (r : Res Ψ)
                    (M : Model₀)
                    (s : Sub Δ)
                    (i : Φ ⊆ Γ)
                    (j : Ψ ⊆ Γ)
                  → sat-ictxt (𝕀ℂe c ⊥· r i j ⨟ d) (M ≔ₛ s)
                  → ⊥
rule⊥E-sat-ictxt₁ {Γ} {Δ} {Φ} {Ψ} c 𝕀ℂ⟨⟩ r M s i j (h , lift q) = q
rule⊥E-sat-ictxt₁ {Γ} {Δ} {Φ} {Ψ} c (𝕀ℂx d f a i₁ j₁) r M s i j (h , q) =
  rule⊥E-sat-ictxt₁ c d r M s i j h
rule⊥E-sat-ictxt₁ {Γ} {Δ} {Φ} {Ψ} c (𝕀ℂv d v) r M (s ⹁ .v ∶ v₁) i j h =
  rule⊥E-sat-ictxt₁ c d r M s i j h

abstract
  irule⊥E-sat : (M : Model₀) {c d : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (Δ : 𝕀ℂ c d)
                {e f : Ctxt}
                (r : Res e)
                (Φ : Ctxt)
                (Ψ : Ctxt)
                (𝟙 : f ⊆ c)
                (𝟚 : e ⊆ c)
                (𝟛 : Φ ⊆ d)
                (𝟜 : Ψ ⊆ d)
                (R : Res Φ) (B : Form Ψ)
              → sat-irule M (irule⊥E Γ Δ r Φ Ψ 𝟙 𝟚 𝟛 𝟜 R B)
  irule⊥E-sat M {c} {d} Γ Δ {e} {f} r Φ Ψ 𝟙 𝟚 𝟛 𝟜 R B _ s satΓ =
    ⊥-elim (rule⊥E-sat-ictxt₁ Γ Δ r M s 𝟙 𝟚 satΓ)

--     Γ ⊢ᵣ A
-- --------------
--    Γ, v ⊢ᵣ A

irule-thin-v : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (v : 𝕍)
               (Φ : Ctxt)
               (Ψ : Ctxt)
               (i : Φ ⊆ (c ، v))
               (j : Ψ ⊆ (c ، v))
               (r : CE Φ) (A : Form Ψ)
               (i′ : Φ ⊆ c)
               (j′ : Ψ ⊆ c) → IRule
irule-thin-v Γ v Φ Ψ i j r A i′ j′ =
  irule [ iseq Γ r A i′ j′ ]
        (iseq (𝕀ℂv Γ v) r A i j)

--     Γ, Δ ⊢ᵣ A
-- -----------------
--    Γ, v, Δ ⊢ᵣ A

irule-thin-v′ : {c d : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (v : 𝕍) (Δ : 𝕀ℂ (c ، v) d)
                (Φ : Ctxt)
                (Ψ : Ctxt)
                (i : Φ ⊆ d)
                (j : Ψ ⊆ d)
                (r : CE Φ) (A : Form Ψ)
                (i′ : Φ ⊆ c)
                (j′ : Ψ ⊆ c) → IRule
irule-thin-v′ Γ v Δ Φ Ψ i j r A i′ j′ =
  irule [ iseq (Γ ⨟ 𝕀ℂ⟨⟩) r A i′ j′ ]
        (iseq (𝕀ℂv Γ v ⨟ Δ) r A i j)

--   Γ, A ⊢ᵣ B
-- --------------
--   Γ ⊢ᵣ A → B

irule→I : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
          (Φ Ψ : Ctxt)
          (r : Res Φ) (A B : Form Ψ)
          (i : Φ ⊆ c)
          (j : Ψ ⊆ c) → IRule
irule→I Γ Φ Ψ r A B i j =
  irule [ iseq (𝕀ℂe Γ A r j i) (CEr r) B i j ]
        (iseq Γ (CEr r) (A →· B) i j)

abstract
  irule→I-sat : (M : Model₀) {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
                (Φ Ψ : Ctxt)
                (r : Res Φ) (A B : Form Ψ)
                (i : Φ ⊆ c)
                (j : Ψ ⊆ c)
              → sat-irule M (irule→I Γ Φ Ψ r A B i j)
  irule→I-sat M Γ Φ Ψ r A B i j = λ z s z₁ z₂ → z .proj₁ s (z₁ , z₂)

--   Γ,(∀u.A)ᴿ,σ(A)ᴿ ⊢[T] B
-- --------------------------
--      Γ,(∀u.A)ᴿ ⊢[T] B

irule∀L : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
          (Φ Ψ Ω Δ : Ctxt)
          (T : Res Φ)
          (R : Res Ω)
          (u : 𝕌)
          (A : Form (Δ ، (𝕍𝕌 u)))
          (B : Form Ψ) (v : C⟦𝕌⟧ Δ u)
          (i : Φ ⊆ c)
          (j : Ψ ⊆ c)
          (k : Ω ⊆ c)
          (l : Δ ⊆ c) → IRule
irule∀L Γ Φ Ψ Ω Δ T R u A B v i j k l =
  irule [ iseq (𝕀ℂe (𝕀ℂe Γ (∀· u A) R l k) (sub A (CSub،ₗ v)) R l k) (CEr T) B i j ]
        (iseq (𝕀ℂe Γ (∀· u A) R l k) (CEr T) B i j)

--
-- --------------
--   Γ, Aʳ ⊢ᵣ A

iruleLbl : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
           (Φ Ψ : Ctxt)
           (r : Res Ψ)
           (A : Form Φ)
           (i : Φ ⊆ c)
           (j : Ψ ⊆ c)
           (k : Φ ⊆ c)
           (l : Ψ ⊆ c) → IRule
iruleLbl Γ Φ Ψ r A i j k l =
  irule []
       (iseq (𝕀ℂe Γ A r i j) (CEr r) A l k)

abstract
  iruleLbl-sat : (M : Model₀) {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
                 (Φ Ψ : Ctxt)
                 (r : Res Ψ)
                 (A : Form Φ)
                 (i : Φ ⊆ c)
                 (j : Ψ ⊆ c)
                 (k : Φ ⊆ c)
                 (l : Ψ ⊆ c)
               → ≡⊆ i k
               → ≡⊆ j l
               → sat-irule M (iruleLbl Γ Φ Ψ r A i j k l)
  iruleLbl-sat M Γ Φ Ψ r A i j k l e f _ s (satΓ , satA) =
    subst₂ (λ x y → (((M ≔ₛ s) ≔ₜ (⟦ x ⟧ᵣ s)) ⊨ y)) (≡↑ᵣ r j l f) (≡↑ A i k e) satA

--     Γ ⊢[r] B   Γ, B^r ⊢[R] A
-- --------------------------
--          Γ ⊢[R] A

irule-cut : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
            (Φ Ψ Ω Δ : Ctxt)
            (R : Res Φ) (r : Res Ψ) (A : Form Ω) (B : Form Δ)
            (i : Φ ⊆ c)
            (j : Ψ ⊆ c)
            (k : Ω ⊆ c)
            (l : Δ ⊆ c) → IRule
irule-cut Γ Φ Ψ Ω Δ R r A B i j k l =
  irule (iseq Γ (CEr r) B j l ∷ iseq (𝕀ℂe Γ B r l j) (CEr R) A i k ∷ [])
        (iseq Γ (CEr R) A i k)

abstract
  irule-cut-sat : (M : Model₀) {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
                  (Φ Ψ Ω Δ : Ctxt)
                  (R : Res Φ) (r : Res Ψ) (A : Form Ω) (B : Form Δ)
                  (i : Φ ⊆ c)
                  (j : Ψ ⊆ c)
                  (k : Ω ⊆ c)
                  (l : Δ ⊆ c)
                → sat-irule M (irule-cut Γ Φ Ψ Ω Δ R r A B i j k l)
  irule-cut-sat M Γ Φ Ψ Ω Δ R r A B i j k l (satB , satA , _) s satΓ =
    satA s (satΓ , (satB s satΓ))

--       Γ.A ⊢ᵣ ⊥
-- --------------------
--       Γ ⊢ᵣ ¬ A

irule¬I : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
          (Φ Ψ : Ctxt)
          (r : Res Ψ) (A : Form Φ)
          (i : Ψ ⊆ c)
          (j : Φ ⊆ c)
        → IRule
irule¬I Γ Φ Ψ r A i j =
  irule [ iseq (𝕀ℂe Γ A r j i) (CEr r) ⊥· i ⟨⟩⊆ ]
        (iseq Γ (CEr r) (¬· A) i j)

abstract
  irule¬I-sat : {c : Ctxt} (M : Model₀) (Γ : 𝕀ℂ ⟨⟩ c)
                (Φ Ψ : Ctxt)
                (r : Res Ψ) (A : Form Φ)
                (i : Ψ ⊆ c)
                (j : Φ ⊆ c)
              → sat-irule M (irule¬I Γ Φ Ψ r A i j)
  irule¬I-sat M Γ Φ Ψ r A i j (sat⊥ , _) s satΓ a =
    lower (sat⊥ s (satΓ , a))

--         Γ ⊢ᵣ A
-- ----------------------
--       Γ ⊢ᵣ A ∨ B

irule∨Iₗ : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
           (Φ Ψ : Ctxt)
           (r : Res Φ) (A B : Form Ψ)
           (i : Φ ⊆ c)
           (j : Ψ ⊆ c)
         → IRule
irule∨Iₗ Γ Φ Ψ r A B i j =
  irule [ iseq Γ (CEr r) A i j ]
        (iseq Γ (CEr r) (A ∨· B) i j)

abstract
  irule∨Iₗ-sat : {c : Ctxt} (M : Model₀) (Γ : 𝕀ℂ ⟨⟩ c)
                 (Φ Ψ : Ctxt)
                 (r : Res Φ) (A B : Form Ψ)
                 (i : Φ ⊆ c)
                 (j : Ψ ⊆ c)
               → sat-irule M (irule∨Iₗ Γ Φ Ψ r A B i j)
  irule∨Iₗ-sat M Γ Φ Ψ r A B i j (satA , _) s satΓ = inj₁ (satA s satΓ)

--         Γ ⊢ᵣ B
-- ----------------------
--       Γ ⊢ᵣ A ∨ B

irule∨Iᵣ : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c)
           (Φ Ψ : Ctxt)
           (r : Res Φ) (A B : Form Ψ)
           (i : Φ ⊆ c)
           (j : Ψ ⊆ c)
         → IRule
irule∨Iᵣ Γ Φ Ψ r A B i j =
  irule [ iseq Γ (CEr r) B i j ]
        (iseq Γ (CEr r) (A ∨· B) i j)

abstract
  irule∨Iᵣ-sat : {c : Ctxt} (M : Model₀) (Γ : 𝕀ℂ ⟨⟩ c)
                 (Φ Ψ : Ctxt)
                 (r : Res Φ) (A B : Form Ψ)
                 (i : Φ ⊆ c)
                 (j : Ψ ⊆ c)
               → sat-irule M (irule∨Iᵣ Γ Φ Ψ r A B i j)
  irule∨Iᵣ-sat M Γ Φ Ψ r A B i j (satA , _) s satΓ = inj₂ (satA s satΓ)

--     Γ , Δ ⊢ᵣ A
-- ----------------
--    Γ, B , Δ ⊢ᵣ A

irule-thin : {c d : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (Δ : 𝕀ℂ c d)
             (Φ Ψ θ δ : Ctxt)
             (B : Form Φ) (x : CE Ψ)
             (r : Res θ)
             (A : Form δ)
             (i : Φ ⊆ c)
             (j : Ψ ⊆ c)
             (k : θ ⊆ d)
             (l : δ ⊆ d)
           → IRule
irule-thin Γ Δ Φ Ψ θ δ B x r A i j k l =
  irule [ iseq (Γ ⨟ Δ) (CEr r) A k l ]
        (iseq (𝕀ℂx Γ B x i j ⨟ Δ) (CEr r) A k l)

irule-thin-sat-ctxt : {c d : Ctxt} (M : Model₀) (Γ : 𝕀ℂ ⟨⟩ c) (Δ : 𝕀ℂ c d)
                      (Φ Ψ : Ctxt)
                      (B : Form Φ) (x : CE Ψ)
                      (i : Φ ⊆ c)
                      (j : Ψ ⊆ c)
                      (s : Sub d)
                    → sat-ictxt (𝕀ℂx Γ B x i j ⨟ Δ) (M ≔ₛ s)
                    → sat-ictxt (Γ ⨟ Δ) (M ≔ₛ s)
irule-thin-sat-ctxt {c} {.c} M Γ 𝕀ℂ⟨⟩ Φ Ψ B x i j s (h , q) = h
irule-thin-sat-ctxt {c} {d} M Γ (𝕀ℂx Δ f a i₁ j₁) Φ Ψ B x i j s (h , q) =
  irule-thin-sat-ctxt M Γ Δ Φ Ψ B x i j s h , q
irule-thin-sat-ctxt {c} {d} M Γ (𝕀ℂv Δ v) Φ Ψ B x i j s h =
  irule-thin-sat-ctxt M Γ Δ Φ Ψ B x i j (Sub،→ s) h

abstract
  irule-thin-sat : {c d : Ctxt} (M : Model₀) (Γ : 𝕀ℂ ⟨⟩ c) (Δ : 𝕀ℂ c d)
                   (Φ Ψ θ δ : Ctxt)
                   (B : Form Φ) (x : CE Ψ)
                   (r : Res θ)
                   (A : Form δ)
                   (i : Φ ⊆ c)
                   (j : Ψ ⊆ c)
                   (k : θ ⊆ d)
                   (l : δ ⊆ d)
                 → sat-irule M (irule-thin Γ Δ Φ Ψ θ δ B x r A i j k l)
  irule-thin-sat M Γ Δ Φ Ψ θ δ B x r A i j k l (satA , _) s satΓ =
    satA s (irule-thin-sat-ctxt M Γ Δ Φ Ψ B x i j s satΓ)


-- Proof checker

split :  {Γ Δ : Ctxt} (c : 𝕀ℂ Γ Δ) (n : ℕ)
        → Maybe (Σ Ctxt (λ Ω →
                 Σ Ctxt (λ Φ →
                 Σ Ctxt (λ Ψ →
                 Σ (Form Φ) (λ A →
                 Σ (CE Ψ) (λ a →
                 Σ (Φ ⊆ Ω) (λ i →
                 Σ (Ψ ⊆ Ω) (λ j →
                 Σ (𝕀ℂ Γ Ω) (λ left →
                 Σ (𝕀ℂ Ω Δ) (λ right →
                   c ≡ 𝕀ℂx left A a i j ⨟ right))))))))))
split {Γ} {Δ} 𝕀ℂ⟨⟩ n = nothing
split {Γ} {Δ} (𝕀ℂx {.Δ} c {Φ} {Ψ} f a i j) 0 =
  just (Δ , Φ , Ψ , f , a , i , j , c , 𝕀ℂ⟨⟩ , refl)
split {Γ} {Δ} (𝕀ℂx {K} c {Φ} {Ψ} f a i j) (suc n) with split c n
... | nothing = nothing
... | just (Ω , Φ′ , Ψ′ , f′ , a′ , i′ , j′ , left , right , refl) =
  just (Ω , Φ′ , Ψ′ , f′ , a′ , i′ , j′ , left ,
        𝕀ℂx {Ω} right {Φ} {Ψ} f a i j ,
        refl)
split {Γ} {Δ} (𝕀ℂv c v) n with split c n
... | nothing = nothing
... | just (Ω , Φ , Ψ , f , a , i , j , left , right , refl) =
  just (Ω , Φ , Ψ , f , a , i , j , left , 𝕀ℂv right v , refl)

data Command : Set₁ where
  Com→I   : Command
  Com¬E   : ℕ → Command
  Com¬I   : Command
  Com⊥E   : ℕ → Command
  Com∨Iₗ  : Command
  Com∨Iᵣ  : Command
  ComThin : ℕ → Command
  ComId   : Command
  ComIdd  : Command -- tries and decide
  ComCut  : {b : Ctxt} (r : Res b) {c : Ctxt} (A : Form c) → Command

data Script : Set₁ where
  Node : Command → (List Script) → Script

data Constraint : Set₁ where
  Cs≡Ctxt : Ctxt → Ctxt → Constraint
  Cs⊆Ctxt : Ctxt → Ctxt → Constraint
  Cs≡Form : {Φ : Ctxt} (A : Form Φ) {Ψ : Ctxt} (B : Form Ψ) → Constraint
  Cs≡Res  : {Φ : Ctxt} (r : Res  Φ) {Ψ : Ctxt} (s : Res Ψ)  → Constraint
  Cs≡⊆    : {Φ Ψ : Ctxt} (i : Φ ⊆ Ψ) {Γ Δ : Ctxt} (j : Γ ⊆ Δ) → Constraint

sat-constraint : Constraint → Set₁
sat-constraint (Cs≡Ctxt Φ Ψ) = Lift _ (Φ ≡ Ψ)
sat-constraint (Cs⊆Ctxt Φ Ψ) = Lift _ (Φ ⊆ Ψ)
sat-constraint (Cs≡Form {Φ} A {Ψ} B) = Σ (Φ ≡ Ψ) (λ e → subst Form e A ≡ B)
sat-constraint (Cs≡Res  {Φ} r {Ψ} s) = Σ (Φ ≡ Ψ) (λ e → Lift _ (subst Res e r ≡ s))
sat-constraint (Cs≡⊆ {Φ} {Ψ} i {Γ} {Δ} j) = Σ (Φ ≡ Γ) (λ e₁ → Σ (Ψ ≡ Δ) (λ e₂ → Lift _ (≡⊆ (subst₂ _⊆_ e₁ e₂ i) j)))

sat-constraints : List Constraint → Set₁
sat-constraints [] = Lift _ ⊤
sat-constraints (x ∷ l) = sat-constraint x × sat-constraints l

sat-constraints++ₗ : (l k : List Constraint)
                   → sat-constraints (l ++ k)
                   → sat-constraints l
sat-constraints++ₗ [] k h = lift tt
sat-constraints++ₗ (x ∷ l) k (h₁ , h₂) = h₁ , sat-constraints++ₗ l k h₂

sat-constraints++ᵣ : (l k : List Constraint)
                   → sat-constraints (l ++ k)
                   → sat-constraints k
sat-constraints++ᵣ [] k h = h
sat-constraints++ᵣ (x ∷ l) k (h₁ , h₂) = sat-constraints++ᵣ l k h₂

sat-constraints++ : (l k : List Constraint)
                  → sat-constraints l
                  → sat-constraints k
                  → sat-constraints (l ++ k)
sat-constraints++ [] k h q = q
sat-constraints++ (x ∷ l) k (h₁ , h₂) q = h₁ , sat-constraints++ l k h₂ q

execute : (M : Model₀)
          (c : Command)
          (s : ISequent)
        → Σ (List ISequent) (λ l →
          Σ (List Constraint) (λ C →
          sat-constraints C →
          sat-irule M (irule l s)))
execute M c s@(inonEmpty {Γ} Δ {Φ} r I) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- →I
execute M Com→I (iseq {Γ} Δ {Φ} {Ψ} (CEr T) (A →· B) I J) =
  [ iseq (𝕀ℂe Δ A T J I) (CEr T) B I J ] ,
  [] ,
  λ _ → irule→I-sat M Δ Φ Ψ T A B I J
execute M Com→I s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- ¬E
execute M (Com¬E n) s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) C I J)
  with split Δ n
... | nothing = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | just (Ω , ϕ , ψ , ¬· A , CEr r , i , j , left , right , refl) =
  [ iseq (left ⨟ right) (CEr r) A (⊆-trans j (𝕀ℂ⊆ right)) (⊆-trans i (𝕀ℂ⊆ right)) ] ,
  [] ,
  λ _ → irule¬E-sat M left right r A Φ Ψ i j I J T C
... | just (Ω , ϕ , ψ , A , a , i , j , left , right , e) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
execute M (Com¬E n) s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- ¬I
execute M Com¬I s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) (¬· C) I J) =
  [ iseq (𝕀ℂe Δ C T J I) (CEr T) ⊥· I ⟨⟩⊆ ] ,
  [] ,
  λ _ → irule¬I-sat M Δ Ψ Φ T C I J
execute M Com¬I s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- ⊥E
execute M (Com⊥E n) s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) C I J)
  with split Δ n
... | nothing = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | just (Ω , ϕ , ψ , ⊥· , CEr r , i , j , left , right , refl) =
  [] ,
  [] ,
  λ _ → irule⊥E-sat M left right r Φ Ψ i j I J T C
... | just (Ω , ϕ , ψ , A , a , i , j , left , right , e) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
execute M (Com⊥E n) s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- ∨Iₗ
execute M Com∨Iₗ s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) (A ∨· B) I J) =
  [ iseq Δ (CEr T) A I J ] ,
  [] ,
  λ _ → irule∨Iₗ-sat M Δ Φ Ψ T A B I J
execute M Com∨Iₗ s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- ∨Iᵣ
execute M Com∨Iᵣ s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) (A ∨· B) I J) =
  [ iseq Δ (CEr T) B I J ] ,
  [] ,
  λ _ → irule∨Iᵣ-sat M Δ Φ Ψ T A B I J
execute M Com∨Iᵣ s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- thin
execute M (ComThin n) s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) C I J)
  with split Δ n
... | nothing = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | just (Ω , θ , δ , B , x , i , j , left , right , refl) =
  [ iseq (left ⨟ right) (CEr T) C I J ] ,
  [] ,
  λ _ → irule-thin-sat M left right θ δ Φ Ψ B x T C i j I J
execute M (ComThin n) s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- Id
execute M ComId s@(iseq {Γ} (𝕀ℂx {Γ₁} Δ {Φ₁} {Ψ₁} A (CEr r) i j) {Ψ} {Φ} (CEr T) C J I) =
  [] ,
  Cs≡Ctxt Φ Φ₁ ∷ Cs≡Ctxt Ψ Ψ₁ ∷ Cs≡Form A C ∷ Cs≡Res r T ∷ Cs≡⊆ i I ∷ Cs≡⊆ j J ∷ [] ,
  sat
  where
  sat : sat-constraints (Cs≡Ctxt Φ Φ₁ ∷ Cs≡Ctxt Ψ Ψ₁ ∷ Cs≡Form A C ∷ Cs≡Res r T ∷ Cs≡⊆ i I ∷ Cs≡⊆ j J ∷ [])
      → sat-irule M (irule [] (iseq (𝕀ℂx Δ A (CEr r) i j) (CEr T) C J I))
  sat (lift refl , lift refl , (refl , refl) , (refl , lift refl) , (refl , refl , lift c₁) , (refl , refl , lift c₂) , _) h =
    iruleLbl-sat M Δ Φ₁ Ψ₁ r A i j I J c₁ c₂ (lift tt)
execute M ComId s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- Idd
execute M ComIdd s@(iseq {Γ} (𝕀ℂx {Γ₁} Δ {Φ₁} {Ψ₁} A (CEr r) i j) {Ψ} {Φ} (CEr T) C J I)
  with Ctxt-dec Φ Φ₁
... | inj₂ p = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | inj₁ refl
  with Ctxt-dec Ψ Ψ₁
... | inj₂ p = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | inj₁ refl
  with Form-dec A C
... | inj₂ p = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | inj₁ refl
  with Res-dec r T
... | inj₂ p = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | inj₁ refl
  with ≡⊆-dec i I
... | inj₂ p = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | inj₁ p₁
  with ≡⊆-dec j J
... | inj₂ p = [ s ] , [] , (λ _ (z , _) → z) -- do nothing
... | inj₁ q₁ = [] , [] , λ _ → iruleLbl-sat M Δ Φ₁ Ψ₁ T A i j I J p₁ q₁
execute M ComIdd s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
-- Cut
execute M (ComCut {b} r {c} B) s@(iseq {d} Γ {Ω} {Φ} R A i k) =
  [ s ] , [] , (λ _ (z , _) → z) -- do nothing
  -- not clear what to do
{--
  iseq {d} Γ {b} {c} r B {!!} {!!} ∷ iseq (𝕀ℂe Γ B r {!!} {!!}) R A i k ∷ [] ,
  {!!} ,
  {!!}
--}

-- as opposed to execute, this version allows using the constraints in the sub-goals
execute′ : (M : Model₀)
           (c : Command)
           (s : ISequent)
         → Σ (List Constraint) (λ C →
           sat-constraints C →
           Σ (List ISequent) (λ l →
           sat-irule M (irule l s)))
execute′ M c s@(inonEmpty {Γ} Δ {Φ} T I) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- →I
execute′ M Com→I (iseq {Γ} Δ {Φ} {Ψ} (CEr T) (A →· B) I J) =
  [] , λ _ → [ iseq (𝕀ℂe Δ A T J I) (CEr T) B I J ] , irule→I-sat M Δ Φ Ψ T A B I J
execute′ M Com→I s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- ¬E
execute′ M (Com¬E n) s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) C I J)
  with split Δ n
... | nothing = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | just (Ω , ϕ , ψ , ¬· A , CEr r , i , j , left , right , refl) =
  [] ,
  λ _ →
    [ iseq (left ⨟ right) (CEr r) A (⊆-trans j (𝕀ℂ⊆ right)) (⊆-trans i (𝕀ℂ⊆ right)) ] ,
    irule¬E-sat M left right r A Φ Ψ i j I J T C
... | just (Ω , ϕ , ψ , A , a , i , j , left , right , e) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
execute′ M (Com¬E n) s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- ¬I
execute′ M Com¬I s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) (¬· C) I J) =
  [] , λ _ → [ iseq (𝕀ℂe Δ C T J I) (CEr T) ⊥· I ⟨⟩⊆ ] , irule¬I-sat M Δ Ψ Φ T C I J
execute′ M Com¬I s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- ⊥E
execute′ M (Com⊥E n) s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) C I J)
  with split Δ n
... | nothing = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | just (Ω , ϕ , ψ , ⊥· , CEr r , i , j , left , right , refl) =
  [] , λ _ → [] , irule⊥E-sat M left right r Φ Ψ i j I J T C
... | just (Ω , ϕ , ψ , A , a , i , j , left , right , e) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
execute′ M (Com⊥E n) s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- ∨Iₗ
execute′ M Com∨Iₗ s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) (A ∨· B) I J) =
  [] , λ _ → [ iseq Δ (CEr T) A I J ] , irule∨Iₗ-sat M Δ Φ Ψ T A B I J
execute′ M Com∨Iₗ s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- ∨Iᵣ
execute′ M Com∨Iᵣ s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) (A ∨· B) I J) =
  [] , λ _ → [ iseq Δ (CEr T) B I J ] , irule∨Iᵣ-sat M Δ Φ Ψ T A B I J
execute′ M Com∨Iᵣ s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- thin
execute′ M (ComThin n) s@(iseq {Γ} Δ {Φ} {Ψ} (CEr T) C I J)
  with split Δ n
... | nothing = [] , (λ _ → [ s ] , λ (z , _) → z) -- do nothing
... | just (Ω , θ , δ , B , x , i , j , left , right , refl) =
  [] , λ _ → [ iseq (left ⨟ right) (CEr T) C I J ] , irule-thin-sat M left right θ δ Φ Ψ B x T C i j I J
execute′ M (ComThin n) s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- Id
execute′ M ComId s@(iseq {Γ} (𝕀ℂx {Γ₁} Δ {Φ₁} {Ψ₁} A (CEr r) i j) {Ψ} {Φ} (CEr T) C J I) =
  Cs≡Ctxt Φ Φ₁ ∷ Cs≡Ctxt Ψ Ψ₁ ∷ Cs≡Form A C ∷ Cs≡Res r T ∷ Cs≡⊆ i I ∷ Cs≡⊆ j J ∷ [] ,
  sat
  where
  sat : sat-constraints (Cs≡Ctxt Φ Φ₁ ∷ Cs≡Ctxt Ψ Ψ₁ ∷ Cs≡Form A C ∷ Cs≡Res r T ∷ Cs≡⊆ i I ∷ Cs≡⊆ j J ∷ [])
      → Σ (List ISequent) (λ l → sat-irule M (irule l (iseq (𝕀ℂx Δ A (CEr r) i j) (CEr T) C J I)))
  sat (lift refl , lift refl , (refl , refl) , (refl , lift refl) , (refl , refl , lift c₁) , (refl , refl , lift c₂) , _) =
    [] , iruleLbl-sat M Δ Φ₁ Ψ₁ r A i j I J c₁ c₂
execute′ M ComId s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- Idd
execute′ M ComIdd s@(iseq {Γ} (𝕀ℂx {Γ₁} Δ {Φ₁} {Ψ₁} A (CEr r) i j) {Ψ} {Φ} (CEr T) C J I)
  with Ctxt-dec Φ Φ₁
... | inj₂ p = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | inj₁ refl
  with Ctxt-dec Ψ Ψ₁
... | inj₂ p = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | inj₁ refl
  with Form-dec A C
... | inj₂ p = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | inj₁ refl
  with Res-dec r T
... | inj₂ p = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | inj₁ refl
  with ≡⊆-dec i I
... | inj₂ p = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | inj₁ p₁
  with ≡⊆-dec j J
... | inj₂ p = [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
... | inj₁ q₁ = [] , λ _ → [] , iruleLbl-sat M Δ Φ₁ Ψ₁ T A i j I J p₁ q₁
execute′ M ComIdd s@(iseq {Γ} Δ {Φ} {Ψ} T C I J) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing
-- Cut
execute′ M (ComCut {b} r {c} B) s@(iseq {d} Γ {Ω} {Φ} (CEr R) A i k) =
  Cs⊆Ctxt b d ∷ Cs⊆Ctxt c d ∷ [] , sat
  where
  sat : sat-constraints (Cs⊆Ctxt b d ∷ Cs⊆Ctxt c d ∷ [])
      → Σ (List ISequent) (λ l → sat-irule M (irule l (iseq Γ (CEr R) A i k)))
  sat (lift c₁ , lift c₂ , lift tt) =
    iseq {d} Γ {b} {c} (CEr r) B c₁ c₂ ∷ iseq (𝕀ℂe Γ B r c₂ c₁) (CEr R) A i k ∷ [] ,
    irule-cut-sat M Γ Ω b Φ c R r A B i c₁ k c₂
execute′ M (ComCut {b} r {c} B) s@(iseq {d} Γ {Ω} {Φ} R A i k) =
  [] , λ _ → [ s ] , (λ (z , _) → z) -- do nothing

executeScript : (M : Model₀)
                (S : Script)
                (s : ISequent)
              → Σ (List ISequent) (λ l →
                Σ (List Constraint) (λ C →
                sat-constraints C →
                sat-irule M (irule l s)))
executeScript M (Node c L) s with execute M c s
... | S , C , P = aux L S [] C [] P
  where
  aux : (S₀ : List Script)     -- L
        (L₀ : List ISequent)   -- S
        (K  : List ISequent)   -- []
        (C₀ : List Constraint) -- C
        (J  : List Constraint) -- []
      → (sat-constraints (J ++ C₀) → sat-irule M (irule (K ++ L₀) s))
      → Σ (List ISequent) (λ l →
        Σ (List Constraint) (λ c →
        sat-constraints (J ++ c) →
        sat-irule M (irule (K ++ l) s)))
  aux S₀ [] K C₀ J P₀ = [] , C₀ , P₀
  aux [] L₀ K C₀ J P₀ = L₀ , C₀ , P₀
  aux (c₁ ∷ S₀) (s₁ ∷ L₀) K C₀ J P₀
    with executeScript M c₁ s₁
  ... | S₁ , C₁ , P₁
    with aux S₀ L₀ (S₁ ++ K) C₀ (C₁ ++ J)
             (λ j k → P₀ (sat-constraints++ J C₀
                                            (sat-constraints++ᵣ C₁ J (sat-constraints++ₗ (C₁ ++ J) C₀ j))
                                            (sat-constraints++ᵣ (C₁ ++ J) C₀ j))
                         (sat-isequents++
                           M K (s₁ ∷ L₀)
                           (sat-isequents++ᵣ M S₁ K (sat-isequents++ₗ M (S₁ ++ K) L₀ k))
                           (P₁ (sat-constraints++ₗ _ _ (sat-constraints++ₗ _ _ j))
                               (sat-isequents++ₗ M S₁ K (sat-isequents++ₗ M (S₁ ++ K) L₀ k)) ,
                            sat-isequents++ᵣ M (S₁ ++ K) L₀ k)))
  ... | S₂ , C₂ , P₂ =
    S₁ ++ S₂ ,
    C₁ ++ C₂ ,
    (λ j k → P₂ (sat-constraints++ (C₁ ++ J) C₂
                                   (sat-constraints++ C₁ J
                                                      (sat-constraints++ₗ C₁ C₂ (sat-constraints++ᵣ J (C₁ ++ C₂) j))
                                                      (sat-constraints++ₗ J (C₁ ++ C₂) j))
                                   (sat-constraints++ᵣ C₁ C₂ (sat-constraints++ᵣ J (C₁ ++ C₂) j)))
                (sat-isequents++ M (S₁ ++ K) S₂
                                 (sat-isequents++ M S₁ K
                                                  (sat-isequents++ₗ M S₁ S₂ (sat-isequents++ᵣ M K (S₁ ++ S₂) k))
                                                  (sat-isequents++ₗ M K (S₁ ++ S₂) k))
                                 (sat-isequents++ᵣ M S₁ S₂ (sat-isequents++ᵣ M K (S₁ ++ S₂) k))))

{--
executeScript′ : (M : Model₀)
                 (S : Script)
                 (s : ISequent)
               → Σ (List Constraint) (λ C →
                 sat-constraints C →
                 Σ (List ISequent) (λ l →
                 sat-irule M (irule l s)))
executeScript′ M (Node c L) s with execute′ M c s
... | C , P = {!!} --aux L S [] C [] P
  where
  aux : (S₀ : List Script)     -- L
        (L₀ : List ISequent)   -- S
        (K  : List ISequent)   -- []
        (C₀ : List Constraint) -- C
        (J  : List Constraint) -- []
      → (sat-constraints (J ++ C₀) → sat-irule M (irule (K ++ L₀) s))
      → Σ (List ISequent) (λ l →
        Σ (List Constraint) (λ c →
        sat-constraints (J ++ c) →
        sat-irule M (irule (K ++ l) s)))
  aux S₀ [] K C₀ J P₀ = [] , C₀ , P₀
  aux [] L₀ K C₀ J P₀ = L₀ , C₀ , P₀
  aux (c₁ ∷ S₀) (s₁ ∷ L₀) K C₀ J P₀
    with executeScript M c₁ s₁
  ... | S₁ , C₁ , P₁
    with aux S₀ L₀ (S₁ ++ K) C₀ (C₁ ++ J)
             (λ j k → P₀ (sat-constraints++ J C₀
                                            (sat-constraints++ᵣ C₁ J (sat-constraints++ₗ (C₁ ++ J) C₀ j))
                                            (sat-constraints++ᵣ (C₁ ++ J) C₀ j))
                         (sat-isequents++
                           M K (s₁ ∷ L₀)
                           (sat-isequents++ᵣ M S₁ K (sat-isequents++ₗ M (S₁ ++ K) L₀ k))
                           (P₁ (sat-constraints++ₗ _ _ (sat-constraints++ₗ _ _ j))
                               (sat-isequents++ₗ M S₁ K (sat-isequents++ₗ M (S₁ ++ K) L₀ k)) ,
                            sat-isequents++ᵣ M (S₁ ++ K) L₀ k)))
  ... | S₂ , C₂ , P₂ =
    S₁ ++ S₂ ,
    C₁ ++ C₂ ,
    (λ j k → P₂ (sat-constraints++ (C₁ ++ J) C₂
                                   (sat-constraints++ C₁ J
                                                      (sat-constraints++ₗ C₁ C₂ (sat-constraints++ᵣ J (C₁ ++ C₂) j))
                                                      (sat-constraints++ₗ J (C₁ ++ C₂) j))
                                   (sat-constraints++ᵣ C₁ C₂ (sat-constraints++ᵣ J (C₁ ++ C₂) j)))
                (sat-isequents++ M (S₁ ++ K) S₂
                                 (sat-isequents++ M S₁ K
                                                  (sat-isequents++ₗ M S₁ S₂ (sat-isequents++ᵣ M K (S₁ ++ S₂) k))
                                                  (sat-isequents++ₗ M K (S₁ ++ S₂) k))
                                 (sat-isequents++ᵣ M S₁ S₂ (sat-isequents++ᵣ M K (S₁ ++ S₂) k))))
--}

abstract
  cs₁ : (c : Ctxt) (A : Form c) (r : Res c)
      → Lift (lsuc Level.zero) (c ≡ c) ×
        Lift (lsuc Level.zero) (c ≡ c) ×
        Σ (c ≡ c) (λ e → subst Form e A ≡ A) ×
        Σ (c ≡ c) (λ e → Lift (lsuc Level.zero) (subst Res e r ≡ r)) ×
        Σ (c ≡ c) (λ e₁ → Σ (c ≡ c) (λ e₂ → Lift (lsuc Level.zero) (≡⊆ (subst₂ _⊆_ e₁ e₂ ⊆r) ⊆r))) ×
        Σ (c ≡ c) (λ e₁ → Σ (c ≡ c) (λ e₂ → Lift (lsuc Level.zero) (≡⊆ (subst₂ _⊆_ e₁ e₂ ⊆r) ⊆r))) ×
        Lift (lsuc Level.zero) ⊤
  cs₁ c A r =
    lift refl , lift refl , (refl , refl) , (refl , lift refl) , (refl , refl , lift ≡⊆-refl) , (refl , refl , lift ≡⊆-refl) , lift tt

-- Example
--   1. Consider this sequent 's': iseq 𝕀ℂ⟨⟩ 𝟎 (⊥· →· ⊤· →· ⊥·) ⊆r ⊆r
--   2. Use the scrit 'C': Node Com→I [ Node Com→I [ Node (Com¬E 1) [] ] ]
--   3. Prove sat-irule M (irule [] S) by running: executeScript M C s
--           → we get [] , P, where P is of type sat-irule M (irule [] S)

example1 : (M : Model₀)
         → sat-irule M (irule [] (iseq 𝕀ℂ⟨⟩ (CEr 𝟎) (⊥· →· ⊤· →· ⊥·) ⊆r ⊆r))
example1 M =
  let l , c , p = executeScript M (Node Com→I [ Node Com→I [ Node (Com⊥E 1) [] ] ]) (iseq 𝕀ℂ⟨⟩ (CEr 𝟎) (⊥· →· ⊤· →· ⊥·) ⊆r ⊆r)
  in p (lift tt)

example2 : (M : Model₀) {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (A : Form c)
         → sat-irule M (irule [] (iseq Γ (CEr 𝟎) (A →· A) ⊆r ⊆r))
example2 M {c} Γ A =
  let l₁ , c₁ , p₁ = executeScript M (Node Com→I [ Node ComId [] ]) (iseq Γ (CEr 𝟎) (A →· A) ⊆r ⊆r)
  in p₁ (cs₁ c A 𝟎)


-- To prove this derived rule, we use a mixture of execute′ which we only use for ComCut
-- and execute, which we use for the other rules

--    Γ , ¬ A@R , ¬ B@R , Δ ⊢[T] C
-- ----------------------------------
--     Γ, ¬ (A ∨ B)@R , Δ ⊢[T] C

irule¬∨L : {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (T R : Res c) (A B C : Form c) → IRule
irule¬∨L Γ T R A B C =
  irule (iseq (𝕀ℂe (𝕀ℂe Γ (¬· A) R ⊆r ⊆r) (¬· B) R ⊆r ⊆r) (CEr T) C ⊆r ⊆r ∷ [])
        (iseq (𝕀ℂe Γ (¬· (A ∨· B)) R ⊆r ⊆r) (CEr T) C ⊆r ⊆r)

irule¬∨L-sat : (M : Model₀) {c : Ctxt} (Γ : 𝕀ℂ ⟨⟩ c) (T R : Res c) (A B C : Form c)
             → sat-irule M (irule¬∨L Γ T R A B C)
irule¬∨L-sat M {c} Γ T R A B C (satB , _) =
  let c₁ , p₁ = execute′ M (ComCut R (¬· A)) (iseq (𝕀ℂe Γ (¬· (A ∨· B)) R ⊆r ⊆r) (CEr T) C ⊆r ⊆r) in
  let s₂ , p₂ = p₁ (lift ⊆r , lift ⊆r , lift tt) in
  p₂ ((let l₃ , c₃ , p₃ = executeScript M (Node Com¬I [ Node (Com¬E 1) [ Node Com∨Iₗ [ Node ComId [] ] ] ]) (iseq (𝕀ℂe Γ (¬· (A ∨· B)) R ⊆r ⊆r) (CEr R) (¬· A) ⊆r ⊆r)
       in p₃ (cs₁ c A R) (lift tt)) ,
      (let c₃ , p₃ = execute′ M (ComCut R (¬· B)) (iseq (𝕀ℂe (𝕀ℂe Γ (¬· (A ∨· B)) R ⊆r ⊆r) (¬· A) R ⊆r ⊆r) (CEr T) C ⊆r ⊆r)
       in let s₄ , p₄ = p₃ (lift ⊆r , lift ⊆r , lift tt)
       in p₄ ((let l₅ , c₅ , p₅ = executeScript M (Node Com¬I [ Node (Com¬E 2) [ Node Com∨Iᵣ [ Node ComId [] ] ] ]) (iseq (𝕀ℂe (𝕀ℂe Γ (¬· (A ∨· B)) R ⊆r ⊆r) (¬· A) R ⊆r ⊆r) (CEr R) (¬· B) ⊆r ⊆r)
               in p₅ (cs₁ c B R) (lift tt)) ,
              (let l₅ , c₅ , p₅ = executeScript M (Node (ComThin 2) []) (iseq (𝕀ℂe (𝕀ℂe (𝕀ℂe Γ (¬· (A ∨· B)) R ⊆r ⊆r) (¬· A) R ⊆r ⊆r) (¬· B) R ⊆r ⊆r) (CEr T) C ⊆r ⊆r)
               in p₅ (lift tt) (satB , lift tt)) ,
              lift tt)) ,
      lift tt)

\end{code}
