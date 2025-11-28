\begin{code}
{-# OPTIONS --without-K --safe #-}

open import Level using (Level ; 0ℓ) renaming (suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Nat using (ℕ ; _≤_ ; _<_ ; pred ; suc ; _+_ ; z≤n)
open import Data.Nat.Properties
  using (m≤n⇒m<n∨m≡n ; ≤-refl ; ≤-trans ; ≤-<-trans ; <⇒≤ ; +-comm ; +-assoc ; +-suc ; ≤-antisym ; +-mono-≤ ;
         m<1+n⇒m<n∨m≡n ; ≤-pred ; ≤-total)
open import Data.Sum
open import Data.Product
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary

module World where

-- TODO: generalize the universe levels
-- TODO: what structure is that? A: The structure (𝕎,≼,𝟘,·) is a (strict) symmetric monoidal poset thanks to axioms sym, assoc, left-id, ≼-refl, ≼→≡, ≼-trans and ·-cong-≼. 
record World : Set₁ where
  constructor world
  infixr 40 _·_
  infixr 30 _≼_
  field
    𝕎   : Set
    𝟘  : 𝕎
--    𝕤  : 𝕎 → 𝕎
--    𝕡  : 𝕎 → 𝕎
    _·_ : 𝕎 → 𝕎 → 𝕎
    _≼_ : 𝕎 → 𝕎 → Set -- w₁ ≼ w₂ means that w₁ is less than or equal to w₂
    _◃_ : 𝕎 → 𝕎 → Set -- w₁ ◃ w₂ means that w₁ comes right before w₂

    -- axioms
    ·-sym     : (w₁ w₂ : 𝕎) → w₁ · w₂ ≡ w₂ · w₁
    ·-assoc   : (w₁ w₂ w₃ : 𝕎) → w₁ · (w₂ · w₃) ≡ (w₁ · w₂) · w₃
    ·-left-id : {w : 𝕎} → 𝟘 · w ≡ w
    𝟘≼        : {w : 𝕎} → 𝟘 ≼ w
    ≼-refl    : {w : 𝕎} → w ≼ w
    ≼-trans   : {w₁ w₂ w₃ : 𝕎} → w₁ ≼ w₂ → w₂ ≼ w₃ → w₁ ≼ w₃
    ·-cong-≼  : {w₁ w₂ w₃ w₄ : 𝕎} → w₁ ≼ w₃ → w₂ ≼ w₄ → w₁ · w₂ ≼ w₃ · w₄
    --
    ◃→≼       : {w₁ w₂ : 𝕎} → w₁ ◃ w₂ → w₁ ≼ w₂
    --
    ≼→≡⊎◃ᵣ    : {w₁ w₂ : 𝕎} → w₁ ≼ w₂ → w₁ ≡ w₂ ⊎ Σ 𝕎 (λ w → w₁ ≼ w × (w ◃ w₂))
    ≼→≡⊎◃ₗ    : {w₁ w₂ : 𝕎} → w₁ ≼ w₂ → w₁ ≡ w₂ ⊎ Σ 𝕎 (λ w → w₁ ◃ w × (w ≼ w₂))
    ≼⊎≼       : {w₁ w₂ w : 𝕎} → w₁ ≼ w → w₂ ≼ w → w₁ ≼ w₂ ⊎ w₂ ≼ w₁

--    ◃injₗ     : {w₁ w₂ w : 𝕎} → w₁ ◃ w → w₂ ◃ w → w₁ ≡ w₂
    --¬◃𝟘       : {w : 𝕎} → ¬ (w ◃ 𝟘)
    --≼𝟘        : {w : 𝕎} → w ≼ 𝟘 → w ≡ 𝟘
    --◃injᵣ     : {w₁ w₂ w : 𝕎} → w ◃ w₁ → w ◃ w₂ → w₁ ≡ w₂
--    ≼→≡       : {w₁ w₂ : 𝕎} → w₁ ≼ w₂ → w₂ ≼ w₁ → w₁ ≡ w₂
    -- s-·       : (w₁ w₂ : 𝕎) → 𝕤 w₁ · w₂ ≡ w₁ · 𝕤 w₂
    --◃→𝕤≼      : {w₁ w₂ : 𝕎} → w₁ ◃ w₂ → 𝕤 w₁ ≼ w₂ -- we can actually have (𝕤 w₁ ≡ w₂). why not use this as the definition of ◃
    --◃𝕤→≡       : {w₁ w₂ : 𝕎} → w₁ ◃ 𝕤 w₂ → w₁ ≡ w₂
    --◃𝕤        : {w : 𝕎} → w ◃ 𝕤 w
    --≼𝕤        : {w : 𝕎} → w ≼ 𝕤 w
    --𝕤≼𝕤       : {w₁ w₂ : 𝕎} → w₁ ≼ w₂ → 𝕤 w₁ ≼ 𝕤 w₂

record Induction {l : Level} (W : World) : Set(lsuc l) where
  constructor induction
  open World W
  field
    ind : (P : 𝕎 → Set(l))
          → ((w : 𝕎) → ((v u : 𝕎) → u ≼ v → v ◃ w → P u) → P w)
          → (w : 𝕎) → P w

-- Proof that ℕ is an instance of the above records

_◂_ : ℕ → ℕ → Set
a ◂ 0 = ⊥
a ◂ suc b = a ≡ b

◂injₗ : {a b c : ℕ} → a ◂ c → b ◂ c → a ≡ b
◂injₗ {a} {b} {suc a} refl refl = refl

◂injᵣ : {a b c : ℕ} → a ◂ b → a ◂ c → b ≡ c
◂injᵣ {a} {suc a} {suc c} refl refl = refl

◂suc⇒≡ : (u v : ℕ) → u ◂ (suc v) → u ≡ v
◂suc⇒≡ u v h = h

◂⇒< : {u v : ℕ} → u ◂ v → suc u ≤ v
◂⇒< {u} {suc v} refl = ≤-refl

◂⇒≤ : {u v : ℕ} → u ◂ v → u ≤ v
◂⇒≤ {u} {suc v} refl = <⇒≤ ≤-refl

≤⇒≺⇒< : (u v n : ℕ) → u ≤ v → v ◂ n → u < n
≤⇒≺⇒< u v n c d = ≤-<-trans c (◂⇒< d)

comp-ind-ℕ-aux : {l : Level} (P : ℕ → Set(l))
                 → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                 → (n m : ℕ) → m < n → P m
comp-ind-ℕ-aux P ind (suc n) m (_≤_.s≤s z) with m≤n⇒m<n∨m≡n z
... | inj₁ q = comp-ind-ℕ-aux P ind n m q
... | inj₂ q rewrite q = ind n (comp-ind-ℕ-aux P ind n)

<ℕind : {l : Level} (P : ℕ → Set(l))
      → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
      → (n : ℕ) → P n
<ℕind P ind n = comp-ind-ℕ-aux P ind (suc n) n (_≤_.s≤s ≤-refl)

gen : {l : Level} (P : ℕ → Set(l))
    → ((w : ℕ) → ((v u : ℕ) → u ≤ v → v ◂ w → P u) → P w)
    → (w : ℕ) → P w
gen P ind w =
  <ℕind P (λ n I → ind n (λ v u c d → I u (≤⇒≺⇒< u v n c d))) w

≼→≡⊎◃ℕₗ : {n₁ n₂ : ℕ} → n₁ ≤ n₂ → n₁ ≡ n₂ ⊎ Σ ℕ (λ n → n₁ ≤ n × (n ◂ n₂))
≼→≡⊎◃ℕₗ {n₁} {n₂} h with m<1+n⇒m<n∨m≡n {n₁} {n₂} (_≤_.s≤s h)
≼→≡⊎◃ℕₗ {n₁} {suc n₂} h | inj₁ p = inj₂ (n₂ , ≤-pred p , refl)
≼→≡⊎◃ℕₗ {n₁} {n₂} h | inj₂ p = inj₁ p

≼→≡⊎◃ℕᵣ : {n₁ n₂ : ℕ} → n₁ ≤ n₂ → n₁ ≡ n₂ ⊎ Σ ℕ (λ n → n₁ ◂ n × (n ≤ n₂))
≼→≡⊎◃ℕᵣ {n₁} {n₂} h with m<1+n⇒m<n∨m≡n {n₁} {n₂} (_≤_.s≤s h)
≼→≡⊎◃ℕᵣ {n₁} {suc n₂} h | inj₁ p = inj₂ (suc n₁ , refl , p)
≼→≡⊎◃ℕᵣ {n₁} {n₂} h | inj₂ p = inj₁ p

≤0 : {w : ℕ} → w ≤ 0 → w ≡ 0
≤0 {0} h = refl

≤⊎≤ : {n₁ n₂ n : ℕ} → n₁ ≤ n → n₂ ≤ n → n₁ ≤ n₂ ⊎ n₂ ≤ n₁
≤⊎≤ {n₁} {n₂} {n} _ _ = ≤-total n₁ n₂

ℕWorld : World
ℕWorld =
  world ℕ 0
--        suc
        --pred
        _+_ _≤_ _◂_ +-comm
        (λ a b c → sym (+-assoc a b c))
        (λ {w} → refl)
        (λ {w} → z≤n)
        ≤-refl
        ≤-trans
        +-mono-≤
        ◂⇒≤
        ≼→≡⊎◃ℕₗ
        ≼→≡⊎◃ℕᵣ
        ≤⊎≤
--        ◂injₗ
--        (λ ())
--        ≤0
        --◂injᵣ
--        ≤-antisym
        --(λ a b → sym (+-suc a b))
        -- ◂⇒<
        --≼→≡⊎◃ℕᵣ
        --(λ {w} → refl)
        --(λ {w} → <⇒≤ ≤-refl)
        --_≤_.s≤s

ℕInduction : Induction {0ℓ} ℕWorld
ℕInduction =
  induction gen

\end{code}
