\begin{code}

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

open import World

module WorldUtil (W : World)
       where

open World.World W

_≺_ : 𝕎 → 𝕎 → Set
w₁ ≺ w₂ = Σ 𝕎 (λ w → Σ 𝕎 (λ w′ → w₁ ≼ w × (w ◃ w′) × w′ ≼ w₂))

≺→≼ : {w₁ w₂ : 𝕎} → w₁ ≺ w₂ → w₁ ≼ w₂
≺→≼ {w₁} {w₂} (w , w′ , c₁ , c₂ , c₃) = ≼-trans c₁ (≼-trans (◃→≼ c₂) c₃)

◃→≺ : {w₁ w₂ : 𝕎} → w₁ ◃ w₂ → w₁ ≺ w₂
◃→≺ {w₁} {w₂} h = w₁ , w₂ , ≼-refl , h , ≼-refl

≺-≼-trans : {w₁ w₂ w₃ : 𝕎} → w₁ ≺ w₂ → w₂ ≼ w₃ → w₁ ≺ w₃
≺-≼-trans {w₁} {w₂} {w₃} (w , w′ , c₁ , c₂ , c₃) q = w , w′ , c₁ , c₂ , ≼-trans c₃ q

≼-≺-trans : {w₁ w₂ w₃ : 𝕎} → w₁ ≼ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃
≼-≺-trans {w₁} {w₂} {w₃} h (w , w′ , c₁ , c₂ , c₃) = w , w′ , ≼-trans h c₁ , c₂ , c₃

≺-trans : {w₁ w₂ w₃ : 𝕎} → w₁ ≺ w₂ → w₂ ≺ w₃ → w₁ ≺ w₃
≺-trans {w₁} {w₂} {w₃} (w , w′ , c₁ , c₂ , c₃) q =
  w , w′ , c₁ , c₂ , ≼-trans c₃ (≺→≼ q)

≺⇒◃ᵣ : (w₁ w₂ : 𝕎) → w₁ ≺ w₂ → Σ 𝕎 (λ w → w₁ ≼ w × (w ◃ w₂))
≺⇒◃ᵣ w₁ w₂ (w , w′ , c₁ , c₂ , c₃) with ≼→≡⊎◃ᵣ c₃
... | inj₁ refl = w , c₁ , c₂
... | inj₂ (w″ , d₁ , d₂) = w″ , ≼-trans c₁ (≼-trans (◃→≼ c₂) d₁) , d₂

{--
≺⇒◃ₗ : (w₁ w₂ : 𝕎) → w₁ ≺ w₂ → Σ 𝕎 (λ w → w₁ ◃ w × (w ≼ w₂))
≺⇒◃ₗ w₁ w₂ (w , w′ , c₁ , c₂ , c₃) with ≼→≡⊎◃ₗ c₁
... | inj₁ refl = w′ , c₂ , c₃
... | inj₂ (w″ , d₁ , d₂) = w″ , d₁ , ≼-trans d₂ (≼-trans (◃→≼ c₂) c₃)
--}

·-right-id : (w : 𝕎) → w · 𝟘 ≡ w
·-right-id w = subst (λ x → x ≡ w) (·-sym 𝟘 w) ·-left-id

·-cong-≼-r₁ : (w₁ w₂ w₃ : 𝕎) → w₁ ≼ w₂ → w₁ ≼ w₂ · w₃
·-cong-≼-r₁ w₁ w₂ w₃ ≼₁ = subst (λ x → x ≼ w₂ · w₃) (·-right-id w₁) (·-cong-≼ ≼₁ 𝟘≼)

·-cong-≼-r₂ : (w₁ w₂ w₃ : 𝕎) → w₁ ≼ w₂ → w₁ ≼ w₃ · w₂
·-cong-≼-r₂ w₁ w₂ w₃ ≼₁ = subst (λ x → w₁ ≼ x) (·-sym w₂ w₃) (·-cong-≼-r₁ w₁ w₂ w₃ ≼₁)

𝟘⊎◃ : (w : 𝕎) → w ≡ 𝟘 ⊎ Σ 𝕎 (λ w′ → w′ ◃ w)
𝟘⊎◃ w with ≼→≡⊎◃ᵣ {𝟘} {w} 𝟘≼
... | inj₁ refl = inj₁ refl
... | inj₂ (w′ , c₁ , c₂) = inj₂ (w′ , c₂)

{--
◃∧≺→≼ : {w₁ w₂ w₃ : 𝕎} → w₁ ◃ w₂ → w₁ ≺ w₃ → w₂ ≼ w₃
◃∧≺→≼ {w₁} {w₂} {w₃} h q with ≺⇒◃ₗ w₁ w₃ q
... | w , d₁ , d₂ with ◃injᵣ h d₁
... | refl = d₂
--}

≼⊎≺ : {w₁ w₂ w : 𝕎} → w₁ ≼ w → w₂ ≼ w → w₁ ≼ w₂ ⊎ w₂ ≺ w₁
≼⊎≺ {w₁} {w₂} {w} h q with ≼⊎≼ h q
... | inj₁ p = inj₁ p
... | inj₂ p with ≼→≡⊎◃ᵣ p
... |   inj₁ refl = inj₁ ≼-refl
... |   inj₂ (w′ , c₁ , c₂) = inj₂ (w′ , w₁ , c₁ , c₂ , ≼-refl)

{--
≼𝟘 : {w : 𝕎} → w ≼ 𝟘 → w ≡ 𝟘
≼𝟘 {w} h with ≼→≡⊎◃ᵣ {w} {𝟘} h
... | inj₁ p = p
... | inj₂ (x , c₁ , c₂) = ⊥-elim (¬◃𝟘 c₂)
--}

totality : {w₁ w₂ : 𝕎} → w₁ ≼ w₂ ⊎ w₂ ≼ w₁
totality {w₁} {w₂} =
  ≼⊎≼ {w₁} {w₂} {w₁ · w₂}
      (·-cong-≼-r₁ w₁ w₁ w₂ ≼-refl)
      (·-cong-≼-r₂ w₂ w₂ w₁ ≼-refl)

\end{code}
