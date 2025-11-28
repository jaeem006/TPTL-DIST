\begin{code}
{-# OPTIONS --without-K --safe #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)

open import Agda.Builtin.Equality

open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤ ; tt)
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

module Misc where

cong : ∀ {a b : Level} {A : Set a} {B : Set b}
       (f : A → B) {x y}
     → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y u v}
      → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

cong₃ : ∀ {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v m n}
      → x ≡ y → u ≡ v → m ≡ n → f x u m ≡ f y v n
cong₃ f refl refl refl = refl

cong₄ : ∀ {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
        (f : A → B → C → D → E) {x y u v m n p q}
      → x ≡ y → u ≡ v → m ≡ n → p ≡ q → f x u m p ≡ f y v n q
cong₄ f refl refl refl refl = refl

subst₂ : ∀ {a b c : Level} {A : Set a} {B : Set b}
         (f : A → B → Set(c)) {x y u v}
       → x ≡ y → u ≡ v → f x u → f y v
subst₂ f refl refl h = h

subst₃ : ∀ {a b c d : Level} {A : Set a} {B : Set b} {C : Set c}
         (f : A → B → C → Set(d)) {x y u v m n}
       → x ≡ y → u ≡ v → m ≡ n → f x u m → f y v n
subst₃ f refl refl refl h = h

subst₄ : ∀ {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         (f : A → B → C → D → Set(e)) {x y u v m n p q}
       → x ≡ y → u ≡ v → m ≡ n → p ≡ q → f x u m p → f y v n q
subst₄ f refl refl refl refl h = h

_⇔_ : {l : Level} → Set(l) → Set(l) → Set(l)
a ⇔ b = (a → b) × (b → a)

-- increments x if c ≤ x
sucIf≤ : (c x : ℕ) → ℕ
sucIf≤ zero x = suc x
sucIf≤ (suc c) zero = zero
sucIf≤ (suc c) (suc x) = suc (sucIf≤ c x)

+-zero : ∀ m → m + 0 ≡ m
+-zero zero = refl
+-zero (suc m) = cong suc (+-zero m)

zero-≤ : {n : ℕ} → 0 ≤ n
zero-≤ {n} = z≤n

suc-≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
suc-≤-suc = _≤_.s≤s

¬m<m : {m : ℕ} → ¬ m < m
¬m<m {m} = <-irrefl refl

¬-<-zero : {m : ℕ} → ¬ m < 0
¬-<-zero ()

pred-≤-pred : {m n : ℕ} → suc m ≤ suc n → m ≤ n
pred-≤-pred = ≤-pred

≤→< : {m n : ℕ} → m ≤ n → ¬ m ≡ n → m < n
≤→< = ≤∧≢⇒<

sucIf≤-prop : (c x : ℕ)
            → ((c ≤ x) × (sucIf≤ c x ≡ suc x))
            ⊎ ((x < c) × (sucIf≤ c x ≡ x))
sucIf≤-prop zero x = inj₁ (zero-≤ , refl)
sucIf≤-prop (suc c) zero = inj₂ (suc-≤-suc zero-≤ , refl)
sucIf≤-prop (suc c) (suc x) with sucIf≤-prop c x
... | inj₁ (p , q) = inj₁ (suc-≤-suc p , cong suc q)
... | inj₂ (p , q) = inj₂ (suc-≤-suc p , cong suc q)

sucIf≤-≤ : (c x : ℕ)
         → c ≤ x
         → sucIf≤ c x ≡ suc x
sucIf≤-≤ c x c≤x with sucIf≤-prop c x
... | inj₁ (c≤x , p) = p
... | inj₂ (x<c , p) = ⊥-elim (¬m<m (≤-trans x<c c≤x))

sucIf≤-< : (c x : ℕ)
         → x < c
         → sucIf≤ c x ≡ x
sucIf≤-< c x x<c with sucIf≤-prop c x
... | inj₁ (c≤x , p) = ⊥-elim (¬m<m (≤-trans x<c c≤x))
... | inj₂ (x<c , p) = p

-- decrements x if c < x
predIf≤ : (c x : ℕ) → ℕ
predIf≤ c zero = zero
predIf≤ zero (suc x) = x
predIf≤ (suc c) (suc x) = suc (predIf≤ c x)

predIf≤-suc-prop : (c x : ℕ)
                 → ((c ≤ x) × (predIf≤ c (suc x) ≡ x))
                 ⊎ ((x < c) × (predIf≤ c (suc x) ≡ suc x))
predIf≤-suc-prop zero x = inj₁ (zero-≤ , refl)
predIf≤-suc-prop (suc c) zero = inj₂ (suc-≤-suc zero-≤ , refl)
predIf≤-suc-prop (suc c) (suc x) with predIf≤-suc-prop c x
predIf≤-suc-prop (suc c) (suc x) | inj₁ (c≤x , p) = inj₁ (suc-≤-suc c≤x , cong suc p)
predIf≤-suc-prop (suc c) (suc x) | inj₂ (x<c , p) = inj₂ (suc-≤-suc x<c , cong suc p)

predIf≤-suc-≤ : (c x : ℕ)
              → c ≤ x
              → predIf≤ c (suc x) ≡ x
predIf≤-suc-≤ c x c≤x with predIf≤-suc-prop c x
predIf≤-suc-≤ c x c≤x | inj₁ (c≤x₁ , p) = p
predIf≤-suc-≤ c x c≤x | inj₂ (x<c₁ , p) =
  ⊥-elim (¬m<m (≤-trans x<c₁ c≤x))

sucIf≤-predIf≤-< : (v c x : ℕ)
                 → c < x
                 → v < x
                 → sucIf≤ v (predIf≤ c x) ≡ x
sucIf≤-predIf≤-< v c 0 c<x v<x = ⊥-elim (¬-<-zero c<x)
sucIf≤-predIf≤-< v c (suc x) c<sx v<sx =
  trans (cong (sucIf≤ v) (predIf≤-suc-≤ c x (pred-≤-pred c<sx)))
        (sucIf≤-≤ v x (pred-≤-pred v<sx))

sucIf≤-predIf≤≡predIf≤ : (v n x : ℕ)
                       → ¬ x ≡ n
                       → n ≤ v
                       → x ≤ v
                       → sucIf≤ v (predIf≤ n x) ≡ predIf≤ n x
sucIf≤-predIf≤≡predIf≤ v 0 0 x≢n n≤v x≤v = sucIf≤-< v zero (≤-trans (⊥-elim (x≢n refl)) n≤v)
sucIf≤-predIf≤≡predIf≤ v (suc n) 0 x≢sn sn≤v x≤v = sucIf≤-< v zero (≤-trans (suc-≤-suc zero-≤) sn≤v)
sucIf≤-predIf≤≡predIf≤ v n (suc x) sx≢n n≤v sx≤v with predIf≤-suc-prop n x
sucIf≤-predIf≤≡predIf≤ v n (suc x) sx≢n n≤v sx≤v | inj₁ (n≤x , p) =
  trans (trans (cong (sucIf≤ v) p) (sucIf≤-< v x sx≤v)) (sym p)
sucIf≤-predIf≤≡predIf≤ v n (suc x) sx≢n n≤v sx≤v | inj₂ (x<n , p) =
  trans (trans (cong (sucIf≤ v) p) (sucIf≤-< v (suc x) (≤-trans (≤→< x<n sx≢n) n≤v))) (sym p)


if≡ : {T : Set} (a b : ℕ) (c d : T) → T
if≡ zero zero c d = c
if≡ zero (suc _) c d = d
if≡ (suc _) zero c d = d
if≡ (suc a) (suc b) c d = if≡ a b c d

caseNat : ∀ {ℓ} → {A : Set ℓ} → (a0 aS : A) → ℕ → A
caseNat a0 aS zero    = a0
caseNat a0 aS (suc n) = aS

znots : {n : ℕ} → ¬ (0 ≡ suc n)
znots eq = subst (caseNat ℕ ⊥) eq 0

snotz : {n : ℕ} → ¬ (suc n ≡ 0)
snotz eq = subst (caseNat ⊥ ℕ) eq 0

predℕ : ℕ → ℕ
predℕ zero = zero
predℕ (suc n) = n

injSuc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
injSuc p = cong predℕ p

if≡-prop : (a b : ℕ)
         → ((a ≡ b) × ({T : Set} (c d : T) → if≡ a b c d ≡ c))
         ⊎ ((¬ a ≡ b) × ({T : Set} (c d : T) → if≡ a b c d ≡ d))
if≡-prop zero zero = inj₁ (refl , λ c d → refl)
if≡-prop zero (suc b) = inj₂ (znots , λ c d → refl)
if≡-prop (suc a) zero = inj₂ (snotz , λ c d → refl)
if≡-prop (suc a) (suc b) with if≡-prop a b
... | inj₁ (p , q) = inj₁ (cong suc p , q)
... | inj₂ (p , q) = inj₂ ((λ z → p (injSuc z)) , q)

if≡-prop-≢ : {T : Set} (a b : ℕ) (c d : T)
           → ¬ a ≡ b
           → if≡ a b c d ≡ d
if≡-prop-≢ a b c d a≢b with if≡-prop a b
... | inj₁ (p , q) = ⊥-elim (a≢b p)
... | inj₂ (p , q) = q c d

decidable : {ℓ : Level} (A : Set(ℓ)) → Set(ℓ)
decidable {ℓ} A = (a b : A) → a ≡ b ⊎ ¬ (a ≡ b)

\end{code}
