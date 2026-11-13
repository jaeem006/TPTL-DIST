\begin{code}

{-# OPTIONS --safe #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)

open import Agda.Builtin.Equality

open import Data.Product
open import Data.List using (List; _∷_; [])
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ ; zero ; suc)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst ; dcong₂ ; _≡_ ; module ≡-Reasoning)
open ≡-Reasoning

--open import Axiom.Extensionality.Propositional using (Extensionality)

open import Induction.WellFounded
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_≟_)
open import Function using (_∘_ ; id)
import Relation.Binary.HeterogeneousEquality as H

open import Misc
open import World

module Automation(W : World)
       where

open import Decidable(W)
open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open import RulesMisc(𝔻)(W)
open import RulesProp(𝔻)(W)
open import RulesTemp(𝔻)(W)

Interval-dec : {Γ : Ctxt} → decidable (Interval Γ)
Interval-dec ［ a , b ］ ［ c , d ］ with Res-dec a c
... | inj₂ p = inj₂ (λ { refl → p refl })
... | inj₁ refl with Res-dec b d
... | inj₂ q = inj₂ (λ { refl → q refl })
... | inj₁ refl = inj₁ refl
Interval-dec ［ a , b ］ ［ c , d ） = inj₂ (λ ())
Interval-dec ［ a , b ］ （ c , d ］ = inj₂ (λ ())
Interval-dec ［ a , b ］ （ c , d ） = inj₂ (λ ())
Interval-dec ［ a , b ） ［ c , d ］ = inj₂ (λ ())
Interval-dec ［ a , b ） ［ c , d ） with Res-dec a c
... | inj₂ p = inj₂ (λ { refl → p refl })
... | inj₁ refl with Res-dec b d
... | inj₂ q = inj₂ (λ { refl → q refl })
... | inj₁ refl = inj₁ refl
Interval-dec ［ a , b ） （ c , d ］ = inj₂ (λ ())
Interval-dec ［ a , b ） （ c , d ） = inj₂ (λ ())
Interval-dec （ a , b ］ ［ c , d ］ = inj₂ (λ ())
Interval-dec （ a , b ］ ［ c , d ） = inj₂ (λ ())
Interval-dec （ a , b ］ （ c , d ］ with Res-dec a c
... | inj₂ p = inj₂ (λ { refl → p refl })
... | inj₁ refl with Res-dec b d
... | inj₂ q = inj₂ (λ { refl → q refl })
... | inj₁ refl = inj₁ refl
Interval-dec （ a , b ］ （ c , d ） = inj₂ (λ ())
Interval-dec （ a , b ） ［ c , d ］ = inj₂ (λ ())
Interval-dec （ a , b ） ［ c , d ） = inj₂ (λ ())
Interval-dec （ a , b ） （ c , d ］ = inj₂ (λ ())
Interval-dec （ a , b ） （ c , d ） with Res-dec a c
... | inj₂ p = inj₂ (λ { refl → p refl })
... | inj₁ refl with Res-dec b d
... | inj₂ q = inj₂ (λ { refl → q refl })
... | inj₁ refl = inj₁ refl

CE-dec : {Γ : Ctxt} → decidable (CE Γ)
CE-dec (CEr r) (CEr r₁) with Res-dec r r₁
... | inj₁ refl = inj₁ refl
... | inj₂ p    = inj₂ (λ { refl → p refl })
CE-dec CEu CEu = inj₁ refl
CE-dec (CEi i) (CEi j) with Interval-dec i j
... | inj₁ refl = inj₁ refl
... | inj₂ p    = inj₂ (λ { refl → p refl })
CE-dec (CEr _) CEu     = inj₂ (λ ())
CE-dec (CEr _) (CEi _) = inj₂ (λ ())
CE-dec CEu (CEr _)     = inj₂ (λ ())
CE-dec CEu (CEi _)     = inj₂ (λ ())
CE-dec (CEi _) (CEr _) = inj₂ (λ ())
CE-dec (CEi _) CEu     = inj₂ (λ ())

↑I-dec : {Γ Δ : Ctxt}
         (e : Γ ⊆ Δ)
         (c : Interval Δ)
       → (Σ (Interval Γ) (λ d → c ≡ ↑I e d)) ⊎ ((d : Interval Γ) → ¬ c ≡ ↑I e d)
↑I-dec {Γ} {Δ} e ［ x , x₁ ］
  with ↑ᵣ-dec e x | ↑ᵣ-dec e x₁
... | inj₁ (y , refl) | inj₁ (y₁ , refl) = inj₁ (［ y , y₁ ］ , refl)
... | inj₂ p | _ = inj₂ (λ { (［ y , y₁ ］) refl → p y refl })
... | _ | inj₂ p = inj₂ (λ { (［ y , y₁ ］) refl → p y₁ refl })
↑I-dec {Γ} {Δ} e ［ x , x₁ ）
  with ↑ᵣ-dec e x | ↑ᵣ-dec e x₁
... | inj₁ (y , refl) | inj₁ (y₁ , refl) = inj₁ (［ y , y₁ ） , refl)
... | inj₂ p | _ = inj₂ (λ { (［ y , y₁ ）) refl → p y refl })
... | _ | inj₂ p = inj₂ (λ { (［ y , y₁ ）) refl → p y₁ refl })
↑I-dec {Γ} {Δ} e （ x , x₁ ］
  with ↑ᵣ-dec e x | ↑ᵣ-dec e x₁
... | inj₁ (y , refl) | inj₁ (y₁ , refl) = inj₁ (（ y , y₁ ］ , refl)
... | inj₂ p | _ = inj₂ (λ { (（ y , y₁ ］) refl → p y refl })
... | _ | inj₂ p = inj₂ (λ { (（ y , y₁ ］) refl → p y₁ refl })
↑I-dec {Γ} {Δ} e （ x , x₁ ）
  with ↑ᵣ-dec e x | ↑ᵣ-dec e x₁
... | inj₁ (y , refl) | inj₁ (y₁ , refl) = inj₁ (（ y , y₁ ） , refl)
... | inj₂ p | _ = inj₂ (λ { (（ y , y₁ ）) refl → p y refl })
... | _ | inj₂ p = inj₂ (λ { (（ y , y₁ ）) refl → p y₁ refl })

↑CE-dec : {Γ Δ : Ctxt}
          (e : Γ ⊆ Δ)
          (c : CE Δ)
        → (Σ (CE Γ) (λ d → c ≡ ↑CE e d)) ⊎ ((d : CE Γ) → ¬ c ≡ ↑CE e d)
↑CE-dec {Γ} {Δ} e (CEr x)
  with ↑ᵣ-dec e x
... | inj₁ (y , refl) = inj₁ (CEr y , refl)
... | inj₂ p = inj₂ (λ { (CEr y) refl → p y refl })
↑CE-dec {Γ} {Δ} e CEu = inj₁ (CEu , refl)
↑CE-dec {Γ} {Δ} e (CEi x)
  with ↑I-dec e x
... | inj₁ (y , refl) = inj₁ (CEi y , refl)
... | inj₂ p = inj₂ λ { (CEi x) refl → p x refl }

CEr-inj : {Γ : Ctxt}
        → {a b : Res Γ}
        → CEr a ≡ CEr b
        → a ≡ b
CEr-inj {Γ} {a} {b} refl = refl

CEi-inj : {Γ : Ctxt}
        → {a b : Interval Γ}
        → CEi a ≡ CEi b
        → a ≡ b
CEi-inj {Γ} {a} {b} refl = refl

［］-inj₁ : {Γ : Ctxt} {a b c d : Res Γ}
          → ［ a , b ］ ≡ ［ c , d ］
          → a ≡ c
［］-inj₁ {Γ} {a} {b} {c} {d} refl = refl

［］-inj₂ : {Γ : Ctxt} {a b c d : Res Γ}
          → ［ a , b ］ ≡ ［ c , d ］
          → b ≡ d
［］-inj₂ {Γ} {a} {b} {c} {d} refl = refl

［）-inj₁ : {Γ : Ctxt} {a b c d : Res Γ}
          → ［ a , b ） ≡ ［ c , d ）
          → a ≡ c
［）-inj₁ {Γ} {a} {b} {c} {d} refl = refl

［）-inj₂ : {Γ : Ctxt} {a b c d : Res Γ}
          → ［ a , b ） ≡ ［ c , d ）
          → b ≡ d
［）-inj₂ {Γ} {a} {b} {c} {d} refl = refl

（］-inj₁ : {Γ : Ctxt} {a b c d : Res Γ}
          → （ a , b ］ ≡ （ c , d ］
          → a ≡ c
（］-inj₁ {Γ} {a} {b} {c} {d} refl = refl

（］-inj₂ : {Γ : Ctxt} {a b c d : Res Γ}
          → （ a , b ］ ≡ （ c , d ］
          → b ≡ d
（］-inj₂ {Γ} {a} {b} {c} {d} refl = refl

（）-inj₁ : {Γ : Ctxt} {a b c d : Res Γ}
          → （ a , b ） ≡ （ c , d ）
          → a ≡ c
（）-inj₁ {Γ} {a} {b} {c} {d} refl = refl

（）-inj₂ : {Γ : Ctxt} {a b c d : Res Γ}
          → （ a , b ） ≡ （ c , d ）
          → b ≡ d
（）-inj₂ {Γ} {a} {b} {c} {d} refl = refl

↑I-inj : {Γ Δ : Ctxt}
         (e   : Γ ⊆ Δ)
         (ei  : ⊆-inj e)
         (a b : Interval Γ)
       → ↑I e a ≡ ↑I e b
       → a ≡ b
↑I-inj {Γ} {Δ} e ei ［ x , x₁ ］ ［ y , y₁ ］ h = cong₂ ［_,_］ (↑ᵣ-inj e ei x y (［］-inj₁ h)) (↑ᵣ-inj e ei x₁ y₁ (［］-inj₂ h))
↑I-inj {Γ} {Δ} e ei ［ x , x₁ ） ［ y , y₁ ） h = cong₂ ［_,_） (↑ᵣ-inj e ei x y (［）-inj₁ h)) (↑ᵣ-inj e ei x₁ y₁ (［）-inj₂ h))
↑I-inj {Γ} {Δ} e ei （ x , x₁ ］ （ y , y₁ ］ h = cong₂ （_,_］ (↑ᵣ-inj e ei x y (（］-inj₁ h)) (↑ᵣ-inj e ei x₁ y₁ (（］-inj₂ h))
↑I-inj {Γ} {Δ} e ei （ x , x₁ ） （ y , y₁ ） h = cong₂ （_,_） (↑ᵣ-inj e ei x y (（）-inj₁ h)) (↑ᵣ-inj e ei x₁ y₁ (（）-inj₂ h))

↑CE-inj : {Γ Δ : Ctxt}
          (e   : Γ ⊆ Δ)
          (ei  : ⊆-inj e)
          (a b : CE Γ)
        → ↑CE e a ≡ ↑CE e b
        → a ≡ b
↑CE-inj {Γ} {Δ} e ei (CEr x) (CEr y) h = cong CEr (↑ᵣ-inj e ei x y (CEr-inj h))
↑CE-inj {Γ} {Δ} e ei CEu CEu h = refl
↑CE-inj {Γ} {Δ} e ei (CEi x) (CEi y) h = cong CEi (↑I-inj e ei x y (CEi-inj h))

data Ax : (c : ℂ₀) (r : ℂCE c) (A : ℂForm c) → Set₂ where
  found : (c : ℂ₀) (f : ℂForm c) (a : ℂCE c)
        → Ax (ℂx c f a) a f
  skip  : {c : ℂ₀} {r : ℂCE c} {A : ℂForm c} (f : ℂForm c) (a : ℂCE c)
        → Ax c r A
        → Ax (ℂx c f a) r A
  down  : {c : ℂ₀} {v : 𝕍} {r : ℂCE c} {A : ℂForm c}
        → Ax c r A
        → Ax (ℂv c v) (↑CE₀ {_} {v} r) (↑₀ A)

Ax-sat : {Δ : ℂ₀} {r : ℂCE Δ} {A : ℂForm Δ} (M : ℂModel Δ)
       → Ax Δ r A → sat-ctxt Δ M → sat-ctxt-annot A r M
Ax-sat {Δ} {r} {A} M (found c .A .r) (sat₁ , sat₂) = sat₂
Ax-sat {Δ} {r} {A} M (skip f a h) (sat₁ , sat₂) = Ax-sat M h sat₁
Ax-sat {Δ} {r} {A} M (down {c} {v} {R} {a} h) s =
  →sat-ctxt-annot-↑₀ M a R (Ax-sat {c} {R} {a} (Model،→ M) h s)

Ax-ℂv→₀ : (c : ℂ₀) (v : 𝕍) (r : ℂCE c) (a : ℂForm c) (R : ℂCE (ℂv c v)) (A : ℂForm (ℂv c v))
        → Ax (ℂv c v) R A
        → R ≡ (↑CE₀ r)
        → A ≡ (↑₀ a)
        → Ax c r a
Ax-ℂv→₀ c v r a R A (down {d} {w} {s} {b} h) e f
  with ↑-inj ⊆₀ ⊆₀-inj b a f | ↑CE-inj ⊆₀ ⊆₀-inj s r e
... | refl | refl = h

Ax-ℂv→ : (c : ℂ₀) (v : 𝕍) (r : ℂCE c) (a : ℂForm c)
       → Ax (ℂv c v) (↑CE₀ r) (↑₀ a)
       → Ax c r a
Ax-ℂv→ c v r a h = Ax-ℂv→₀ c v r a (↑CE₀ r) (↑₀ a) h refl refl

decAx : (c : ℂ₀) (r : ℂCE c) (A : ℂForm c)
      → Ax c r A ⊎ ¬ Ax c r A
decAx ℂ⟨⟩ r A = inj₂ (λ ())

decAx (ℂx c f a) r A
  with Form-dec f A | CE-dec a r
... | inj₁ refl | inj₁ refl = inj₁ (found c f a)
... | inj₁ refl | inj₂ p
  with decAx c r f
...    | inj₁ q = inj₁ (skip f a q)
...    | inj₂ ¬q = inj₂ concl
  where
  concl : Ax (ℂx c f a) r f → ⊥
  concl (found .c .f .a) = p refl
  concl (skip .f .a x) = ¬q x
decAx (ℂx c f a) r A | inj₂ p    | inj₁ refl
  with decAx c r A
...    | inj₁ q = inj₁ (skip f a q)
...    | inj₂ ¬q = inj₂ concl
  where
  concl : Ax (ℂx c f a) a A → ⊥
  concl (found .c .f .a) = p refl
  concl (skip .f .a x) = ¬q x
decAx (ℂx c f a) r A | inj₂ p    | inj₂ q
  with decAx c r A
...    | inj₁ q = inj₁ (skip f a q)
...    | inj₂ ¬q = inj₂ concl
  where
  concl : Ax (ℂx c f a) r A → ⊥
  concl (found .c .f .a) = q refl
  concl (skip .f .a x) = ¬q x

decAx (ℂv c v) r A
  with ↑dec {ℂtxt c} {ℂtxt c ، v} ⊆₀ A | ↑CE-dec {ℂtxt c} {ℂtxt c ، v} ⊆₀ r
... | inj₁ (a , refl) | inj₁ (s , refl)
  with decAx c s a
... | inj₁ p = inj₁ (down p)
... | inj₂ ¬p = inj₂ concl
  where
  concl : ¬ Ax (ℂv c v) (↑CE₀ s) (↑₀ a)
  concl x = ¬p (Ax-ℂv→ c v s a x)
decAx (ℂv c v) r A | inj₂ ¬p         | _ = inj₂ concl
  where
  concl : ¬ Ax (ℂv c v) r A
  concl (down {d} {w} {s} {a} x) = ¬p a refl
decAx (ℂv c v) r A | _               | inj₂ ¬p = inj₂ concl
  where
  concl : ¬ Ax (ℂv c v) r A
  concl (down {d} {w} {s} {a} x) = ¬p s refl

data pointCE {Γ : Ctxt} : CE Γ → Set where
  ptR : (r : Res Γ) → pointCE (CEr r)
  ptU : pointCE CEu

decPointCE : {Γ : Ctxt} (a : CE Γ) → pointCE a ⊎ ¬ pointCE a
decPointCE (CEr r) = inj₁ (ptR r)
decPointCE CEu     = inj₁ ptU
decPointCE (CEi i) = inj₂ (λ ())

pointCE-↑CE : {Γ Δ : Ctxt} (e : Γ ⊆ Δ) {a : CE Γ}
            → pointCE a → pointCE (↑CE e a)
pointCE-↑CE e (ptR r) = ptR (↑ᵣ e r)
pointCE-↑CE e ptU     = ptU

pointCE-↑⋆CE : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) {a : CE Γ}
             → pointCE a → pointCE (↑⋆CE s a)
pointCE-↑⋆CE s (ptR r) = ptR (↑⋆ᵣ s r)
pointCE-↑⋆CE s ptU     = ptU


sat-ctxt-annot⊥pt : {Γ : Ctxt} (a : CE Γ) (M : Model Γ)
                  → pointCE a
                  → sat-ctxt-annot {Γ} ⊥· a M
                  → ⊥
sat-ctxt-annot⊥pt (CEr r) M (ptR .r) h = lower h
sat-ctxt-annot⊥pt CEu     M ptU      h = lower h

sat-ctxt-annot→ : {Γ : Ctxt} (A B : Form Γ) (a : CE Γ) (M : Model Γ)
                → sat-ctxt-annot {Γ} (A →· B) a M
                → sat-ctxt-annot {Γ} A a M
                → sat-ctxt-annot {Γ} B a M
sat-ctxt-annot→ A B (CEr r) M h q = h q
sat-ctxt-annot→ A B CEu     M h q = h q
sat-ctxt-annot→ A B (CEi i) M h q = λ w c → h w c (q w c)

sat-ctxt-annot∨pt : {Γ : Ctxt} (A B : Form Γ) (a : CE Γ) (M : Model Γ)
                  → pointCE a
                  → sat-ctxt-annot {Γ} (A ∨· B) a M
                  → sat-ctxt-annot {Γ} A a M ⊎ sat-ctxt-annot {Γ} B a M
sat-ctxt-annot∨pt A B (CEr r) M (ptR .r) h = h
sat-ctxt-annot∨pt A B CEu     M ptU      h = h


-- A comparison's truth does not depend on the current time point.
sat-ctxt-annot-cmp : {Γ : Ctxt} (a b : Res Γ) (c : Comparison) (T T′ : CE Γ) (M : Model Γ)
                   → pointCE T
                   → sat-ctxt-annot {Γ} (a ⟨ c ⟩ b) T M
                   → sat-ctxt-annot {Γ} (a ⟨ c ⟩ b) T′ M
sat-ctxt-annot-cmp a b c (CEr r) (CEr x) M (ptR .r) h = h
sat-ctxt-annot-cmp a b c (CEr r) CEu     M (ptR .r) h = h
sat-ctxt-annot-cmp a b c (CEr r) (CEi i) M (ptR .r) h = λ w _ → h
sat-ctxt-annot-cmp a b c CEu     (CEr x) M ptU      h = h
sat-ctxt-annot-cmp a b c CEu     CEu     M ptU      h = h
sat-ctxt-annot-cmp a b c CEu     (CEi i) M ptU      h = λ w _ → h

data ⊢ : Sequent → Set₂ where
  -- hyppothesis
  ax  : {Δ : ℂ₀} {r : ℂCE Δ} {A : ℂForm Δ}
      → Ax Δ r A → ⊢ (seq Δ r A)
  -- introduction rules
  ⊤I  : {Δ : ℂ₀} {r : ℂCE Δ}
      → ⊢ (seq Δ r ⊤·)
  ∧I  : {Δ : ℂ₀} {r : ℂCE Δ} {A B : ℂForm Δ}
      → ⊢ (seq Δ r A) → ⊢ (seq Δ r B) → ⊢ (seq Δ r (A ∧· B))
  ∨Iₗ : {Δ : ℂ₀} {r : ℂCE Δ} {A B : ℂForm Δ}
      → ⊢ (seq Δ r A) → ⊢ (seq Δ r (A ∨· B))
  ∨Iᵣ : {Δ : ℂ₀} {r : ℂCE Δ} {A B : ℂForm Δ}
      → ⊢ (seq Δ r B) → ⊢ (seq Δ r (A ∨· B))
  →I  : {Δ : ℂ₀} {r : ℂRes Δ} {A B : ℂForm Δ}
      → ⊢ (rseq (ℂe Δ A r) r B) → ⊢ (rseq Δ r (A →· B))
  ＯI : {Δ : ℂ₀} {r r₁ : ℂRes Δ} {A : ℂForm Δ}
      → ⊢ (useq Δ (r ◁ r₁)) → ⊢ (rseq Δ r₁ A) → ⊢ (rseq Δ r (Ｏ A))
  ＵI : {Δ : ℂ₀} {r r₁ : ℂRes Δ} {A B : ℂForm Δ}
      → ⊢ (useq Δ (r ⊑ r₁))
      → ⊢ (rseq Δ r₁ B)
      → ⊢ (rseq (ℂu (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊏ ↑ᵣ₀ r₁)) 𝕣₀ (↑₀ A))
      → ⊢ (rseq Δ r (A Ｕ B))
  -- elimination rules
  ⊥L  : {Δ : ℂ₀} {R T : ℂCE Δ} {C : ℂForm Δ}
      → pointCE R
      → Ax Δ R ⊥·
      → ⊢ (seq Δ T C)
  ∧L  : {Δ : ℂ₀} {R T : ℂCE Δ} {A B C : ℂForm Δ}
      → Ax Δ R (A ∧· B)
      → ⊢ (seq (ℂx (ℂx Δ A R) B R) T C)
      → ⊢ (seq Δ T C)
  →L  : {Δ : ℂ₀} {R T : ℂCE Δ} {A B C : ℂForm Δ}
      → Ax Δ R (A →· B)
      → ⊢ (seq Δ R A)
      → ⊢ (seq (ℂx Δ B R) T C)
      → ⊢ (seq Δ T C)
  ∨L  : {Δ : ℂ₀} {R T : ℂCE Δ} {A B C : ℂForm Δ}
      → pointCE R
      → Ax Δ R (A ∨· B)
      → ⊢ (seq (ℂx Δ A R) T C)
      → ⊢ (seq (ℂx Δ B R) T C)
      → ⊢ (seq Δ T C)
  -- next-time-point binder: Ｆ A holds at r if A[x/r] does
  ＦI  : {Δ : ℂ₀} {r : ℂRes Δ} {A : ℂForm (ℂv Δ 𝕍ℝ)}
      → ⊢ (rseq Δ r (subℝ A r)) → ⊢ (rseq Δ r (Ｆ A))
  -- comparisons do not depend on the time point, so they can be moved from
  -- a point label (resource or unlabelled) to any label
  cmpR : {Δ : ℂ₀} {T T′ : ℂCE Δ} {a b : ℂRes Δ} {c : Comparison}
       → pointCE T
       → ⊢ (seq Δ T (a ⟨ c ⟩ b)) → ⊢ (seq Δ T′ (a ⟨ c ⟩ b))

sound : (M : Model₀) {s : Sequent} → ⊢ s → sat-sequent M s
sound M (ax p)                                  = λ s satΔ → Ax-sat (M ≔ₛ s) p satΔ
sound M (⊤I {Δ} {r})                            = rule⊤R-sat  M Δ r (lift tt)
sound M (∧I {Δ} {r} d₁ d₂)                      = rule∧I-sat  M Δ r _ _ (sound M d₁ , sound M d₂ , lift tt)
sound M (∨Iₗ {Δ} {r} d)                         = rule∨Iₗ-sat M Δ r _ _ (sound M d , lift tt)
sound M (∨Iᵣ {Δ} {r} d)                         = rule∨Iᵣ-sat M Δ r _ _ (sound M d , lift tt)
sound M (→I {Δ} {r} {A} {B} d)                  = rule→I-sat  M Δ r A B (sound M d , lift tt)
sound M (ＯI {Δ} {r} {r₁} {A} d₁ d₂)            = ruleＯR-sat M Δ r r₁ A (sound M d₁ , sound M d₂ , lift tt)
sound M (ＵI {Δ} {r} {r₁} {A} {B} d₁ d₂ d₃)     = ruleＵR-sat M Δ r r₁ A B (sound M d₁ , sound M d₂ , sound M d₃ , lift tt)
sound M (⊥L {Δ} {R} {T} {C} pt p) = λ s satΔ →
  ⊥-elim (sat-ctxt-annot⊥pt R (M ≔ₛ s) pt (Ax-sat (M ≔ₛ s) p satΔ))
sound M (∧L {Δ} {R} {T} {A} {B} {C} p d) = λ s satΔ →
  sound M d s ( (satΔ , sat-ctxt-annot∧·ₗ A B R (M ≔ₛ s) (Ax-sat (M ≔ₛ s) p satΔ))
              ,           sat-ctxt-annot∧·ᵣ A B R (M ≔ₛ s) (Ax-sat (M ≔ₛ s) p satΔ) )
sound M (→L {Δ} {R} {T} {A} {B} {C} p d₁ d₂) = λ s satΔ →
  sound M d₂ s ( satΔ
               , sat-ctxt-annot→ A B R (M ≔ₛ s)
                                 (Ax-sat (M ≔ₛ s) p satΔ)
                                 (sound M d₁ s satΔ) )
sound M (∨L {Δ} {R} {T} {A} {B} {C} pt p d₁ d₂) = λ s satΔ →
  [ (λ hA → sound M d₁ s (satΔ , hA))
  , (λ hB → sound M d₂ s (satΔ , hB)) ]
  (sat-ctxt-annot∨pt A B R (M ≔ₛ s) pt (Ax-sat (M ≔ₛ s) p satΔ))
sound M (ＦI {Δ} {r} {A} d) = ruleＦR-sat M Δ r A (sound M d , lift tt)
sound M (cmpR {Δ} {T} {T′} {a} {b} {c} pt d) = λ s satΔ →
  sat-ctxt-annot-cmp a b c T T′ (M ≔ₛ s) pt (sound M d s satΔ)


-- ===========================================================================
-- PROOF SEARCH: search⊢ and Prove
--
-- Shared by both approaches to Agda-level formulas (A : Form Γ):
--   * SUBST APPROACH (this file, below): search on object variables
--     (var 0 →· var 0) and instantiate with subst-⊢⋆ / subst-⊢⋆₀ (uses plug⊢ now).
--   * REFLECTION APPROACH (ProveTactic.lagda): the `prove` macro abstracts A to
--     a fresh var k, runs search⊢, and puts A back into the derivation.
-- Side-by-side examples of both: Examples.lagda.
-- ===========================================================================

ℂhyp : (Δ : ℂ₀) → Set₂
ℂhyp Δ = Σ (ℂCE Δ) (λ R → Σ (ℂForm Δ) (λ A → Ax Δ R A))

ℂhyps : (Δ : ℂ₀) → List (ℂhyp Δ)
ℂhyps ℂ⟨⟩        = []
ℂhyps (ℂx c f a) = (a , f , found c f a) ∷ mapskip (ℂhyps c)
  where
  mapskip : List (ℂhyp c) → List (ℂhyp (ℂx c f a))
  mapskip []                = []
  mapskip ((R , A , p) ∷ l) = (R , A , skip f a p) ∷ mapskip l
ℂhyps (ℂv c v)   = mapdown (ℂhyps c)
  where
  mapdown : List (ℂhyp c) → List (ℂhyp (ℂv c v))
  mapdown []                = []
  mapdown ((R , A , p) ∷ l) = (↑CE₀ R , ↑₀ A , down p) ∷ mapdown l

mmap : {A B : Set₂} → (A → B) → Maybe A → Maybe B
mmap f (just x) = just (f x)
mmap f nothing  = nothing

_orelse_ : {A : Set₂} → Maybe A → Maybe A → Maybe A
just x  orelse _ = just x
nothing orelse y = y

{--
search⊢       : (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
search⊢-intro : (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
search⊢-left  : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ)
                 → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T C))

search⊢ Δ T C with decAx Δ T C
... | inj₁ p  = just (ax p)
... | inj₂ ¬p = search⊢-intro Δ T C

search⊢-intro Δ T ⊤· = just ⊤I

search⊢-intro Δ T (A ∧· B)
  with search⊢ Δ T A
... | nothing = nothing
... | just pa
    with search⊢ Δ T B
...   | nothing = nothing
...   | just pb = just (∧I pa pb)

search⊢-intro Δ T (A ∨· B)
  with search⊢ Δ T A
... | just pa = just (∨Iₗ pa)
... | nothing
    with search⊢ Δ T B
...   | just pb = just (∨Iᵣ pb)
...   | nothing = nothing

search⊢-intro Δ T (A →· B) with T
... | CEr R
      with search⊢ (ℂe Δ A R) (CEr R) B
...     | just p  = just (→I p)
...     | nothing = nothing
search⊢-intro Δ T (A →· B) | CEu   = nothing
search⊢-intro Δ T (A →· B) | CEi _ = nothing

search⊢-intro Δ T C = nothing   -- ⊥·, atoms, quantifiers, temporal operators, comparisons
--}


search⊢       : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
search⊢-intro : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
search⊢-left  : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ)
                 → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T C))
-- ＯI and ＵI need a witness r₁.  Their first premise (r ◁ r₁, resp. r ⊑ r₁,
-- unlabelled) is closed by ax, possibly via cmpR, so the witnesses are
-- taken from the comparison hypotheses of the context at a point label.
search⊢-Ｏ    : (n : ℕ) (Δ : ℂ₀) (r : ℂRes Δ) (A : ℂForm Δ)
                 → List (ℂhyp Δ) → Maybe (⊢ (rseq Δ r (Ｏ A)))
search⊢-Ｕ    : (n : ℕ) (Δ : ℂ₀) (r : ℂRes Δ) (A B : ℂForm Δ)
                 → List (ℂhyp Δ) → Maybe (⊢ (rseq Δ r (A Ｕ B)))
search⊢-cmp : (Δ : ℂ₀) (T : ℂCE Δ) (a b : ℂRes Δ) (c : Comparison)
               → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T (a ⟨ c ⟩ b)))

search⊢ 0 Δ T C with decAx Δ T C
... | inj₁ p  = just (ax p)
... | inj₂ ¬p = nothing
search⊢ (suc n) Δ T C with decAx Δ T C
... | inj₁ p  = just (ax p)
... | inj₂ ¬p = search⊢-intro n Δ T C
                orelse search⊢-left n Δ T C (ℂhyps Δ)

-- unchanged apart from threading n
search⊢-intro n Δ T ⊤· = just ⊤I

search⊢-intro n Δ T (A ∧· B)
  with search⊢ n Δ T A
... | nothing = nothing
... | just pa
    with search⊢ n Δ T B
...   | nothing = nothing
...   | just pb = just (∧I pa pb)

search⊢-intro n Δ T (A ∨· B)
  with search⊢ n Δ T A
... | just pa = just (∨Iₗ pa)
... | nothing
    with search⊢ n Δ T B
...   | just pb = just (∨Iᵣ pb)
...   | nothing = nothing

search⊢-intro n Δ T (A →· B) with T
... | CEr R
      with search⊢ n (ℂe Δ A R) (CEr R) B
...     | just p  = just (→I p)
...     | nothing = nothing
search⊢-intro n Δ T (A →· B) | CEu   = nothing
search⊢-intro n Δ T (A →· B) | CEi _ = nothing

search⊢-intro n Δ (CEr r) (Ｏ A)   = search⊢-Ｏ n Δ r A (ℂhyps Δ)
search⊢-intro n Δ (CEr r) (A Ｕ B) = search⊢-Ｕ n Δ r A B (ℂhyps Δ)

search⊢-intro n Δ (CEr r) (Ｆ A)   = mmap ＦI (search⊢ n Δ (CEr r) (subℝ A r))
search⊢-intro n Δ T (a ⟨ c ⟩ b)  = search⊢-cmp Δ T a b c (ℂhyps Δ)

search⊢-intro n Δ T C = nothing

-- a comparison hypothesis at any point label can be used unlabelled (cmpR)
cmpAx : {Δ : ℂ₀} {R : ℂCE Δ} {a b : ℂRes Δ} {c : Comparison}
      → pointCE R → Ax Δ R (a ⟨ c ⟩ b) → ⊢ (useq Δ (a ⟨ c ⟩ b))
cmpAx ptU     p = ax p
cmpAx (ptR r) p = cmpR (ptR r) (ax p)

-- a comparison goal at any label, from the same comparison at a point label
search⊢-cmp Δ T a b c [] = nothing
search⊢-cmp Δ T a b c ((R , _ , _) ∷ l) with decPointCE R
... | inj₂ _ = search⊢-cmp Δ T a b c l
... | inj₁ pt with decAx Δ R (a ⟨ c ⟩ b)
...   | inj₁ q = just (cmpR pt (ax q))
...   | inj₂ _ = search⊢-cmp Δ T a b c l

search⊢-Ｏ n Δ r A [] = nothing
search⊢-Ｏ n Δ r A ((R , (x ⟨ PR ⟩ r₁) , p) ∷ l) with decPointCE R | Res-dec x r
... | inj₁ pt | inj₁ refl = mmap (ＯI (cmpAx pt p)) (search⊢ n Δ (CEr r₁) A)
                            orelse search⊢-Ｏ n Δ r A l
... | _       | _         = search⊢-Ｏ n Δ r A l
search⊢-Ｏ n Δ r A (_ ∷ l) = search⊢-Ｏ n Δ r A l

search⊢-Ｕ n Δ r A B [] = nothing
search⊢-Ｕ n Δ r A B ((R , (x ⟨ LE ⟩ r₁) , p) ∷ l) with decPointCE R | Res-dec x r
... | inj₁ pt | inj₁ refl
    with search⊢ n Δ (CEr r₁) B
...   | nothing = search⊢-Ｕ n Δ r A B l
...   | just dB =
        mmap (ＵI (cmpAx pt p) dB)
             (search⊢ n (ℂu (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊏ ↑ᵣ₀ r₁)) (CEr 𝕣₀) (↑₀ A))
        orelse search⊢-Ｕ n Δ r A B l
search⊢-Ｕ n Δ r A B ((R , (x ⟨ LE ⟩ r₁) , p) ∷ l) | _ | _ = search⊢-Ｕ n Δ r A B l
search⊢-Ｕ n Δ r A B (_ ∷ l) = search⊢-Ｕ n Δ r A B l

search⊢-left n Δ T C [] = nothing

-- ⊥L : a contradictory hypothesis closes the goal outright.
search⊢-left n Δ T C ((R , ⊥· , p) ∷ l)
  with decPointCE R
... | inj₁ pt = just (⊥L pt p)
... | inj₂ _  = search⊢-left n Δ T C l

-- ∧L : unrestricted, non-branching.  Skipped if both conjuncts are present.
search⊢-left n Δ T C ((R , A ∧· B , p) ∷ l)
  with decAx Δ R A | decAx Δ R B
... | inj₁ _ | inj₁ _ = search⊢-left n Δ T C l
... | _      | _      =
      mmap (∧L p) (search⊢ n (ℂx (ℂx Δ A R) B R) T C)
      orelse search⊢-left n Δ T C l

-- →L : unrestricted.  Fires only if the antecedent is provable.
search⊢-left n Δ T C ((R , A →· B , p) ∷ l)
  with decAx Δ R B
... | inj₁ _ = search⊢-left n Δ T C l
... | inj₂ _
    with search⊢ n Δ R A
...   | nothing = search⊢-left n Δ T C l
...   | just dA =
        mmap (→L p dA) (search⊢ n (ℂx Δ B R) T C)
        orelse search⊢-left n Δ T C l

-- ∨L : branching, and pointCE-restricted.
search⊢-left n Δ T C ((R , A ∨· B , p) ∷ l)
  with decPointCE R
... | inj₂ _  = search⊢-left n Δ T C l
... | inj₁ pt
    with decAx Δ R A | decAx Δ R B
...   | inj₁ _ | _     = search⊢-left n Δ T C l
...   | _      | inj₁ _ = search⊢-left n Δ T C l
...   | inj₂ _ | inj₂ _
      with search⊢ n (ℂx Δ A R) T C
...     | nothing = search⊢-left n Δ T C l
...     | just d₁ =
          mmap (∨L pt p d₁) (search⊢ n (ℂx Δ B R) T C)
          orelse search⊢-left n Δ T C l

-- atoms, quantifiers, temporal operators, comparisons: no left rule yet.
-- MUST remain the last clause.
search⊢-left n Δ T C (_ ∷ l) = search⊢-left n Δ T C l

Prove : (n : ℕ) (M : Model₀) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ)
      → Maybe (sat-sequent M (seq Δ T C))
Prove n M Δ T C with search⊢ n Δ T C
... | just p  = just (sound M p)
... | nothing = nothing

{--
Prove : (M : Model₀) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (sat-sequent M (seq Δ T C))
Prove M Δ T C with search⊢ Δ T C
... | just p  = just (sound M p)
... | nothing = nothing
--}

-- ===========================================================================
-- SUBST APPROACH: substitution lemmas for ⊢
--
-- subst-⊢  : semantic-style substitutions (FormSub = FormVar → Form Γ);
--            retired (commented out), superseded by subst-⊢⋆
-- subst-⊢⋆ : syntactic substitutions (FormSub⋆), any context Δ
-- subst-⊢⋆₀: corollary of subst-⊢⋆ for Δ = ℂ⟨⟩, whose conclusion is just
--            substF⋆ σ C (no ↑⋆ wrappers).
-- subst-⊢⋆ₕ: same, for closed contexts with hypotheses (no ℂv), given as a
--            list ⌜ l ⌝; hypotheses become substF⋆ σ of the originals.
-- ===========================================================================

↑FormSub₀ : {Γ : Ctxt} {u : 𝕍} → FormSub Γ → FormSub (Γ ، u)
↑FormSub₀ σ n = ↑₀ (σ n)

liftFormSub : {Γ : Ctxt} (σ : FormSub Γ) (c : ℂ Γ) → FormSub (ℂtxt (substCtxt σ c))
liftFormSub σ ℂ⟨⟩        = σ
liftFormSub σ (ℂx c f a) = liftFormSub σ c
liftFormSub σ (ℂv c v)   = ↑FormSub₀ (liftFormSub σ c)

liftCE : {Γ : Ctxt} (σ : FormSub Γ) (c : ℂ Γ) → CE (ℂtxt c) → CE (ℂtxt (substCtxt σ c))
liftCE σ ℂ⟨⟩        r = r
liftCE σ (ℂx c f a) r = liftCE σ c r
liftCE σ (ℂv c v)   r = ⋆CE (sym (ℂtxt-substCtxt σ (ℂv c v))) r

⋆Form-↑ : (Γ Δ Ψ : Ctxt) (B : Form Γ)
          (e : Δ ≡ Ψ)
          (s : Γ ⊆ Δ)
        → ⋆Form e (↑ s B)
        ≡ ↑ (subst (λ x → Γ ⊆ x) e s) B
⋆Form-↑ Γ Δ Ψ B refl s = refl

{--
-- We need ⋆Form and ↑₀ to commute in the 'down' case below.
⋆Form-↑₀ : (Γ Δ : Ctxt) (B : Form Γ) (v : 𝕍)
         → (e : Γ ، v ≡ Δ)
         → ⋆Form e (↑₀ {Γ} {v} B)
         ≡ {!!}
⋆Form-↑₀ Γ Δ B v e = {!!}
--}

{--
FormSub،-↑FormSub : (Δ Γ : Ctxt) (v : 𝕍) (g : Δ ⊆ Γ) (σ : FormSub Δ)
                 → FormSub، Γ v (↑FormSub g σ)
                 ≡ ↑FormSub (⊆-trans g ⊆₀) σ
FormSub،-↑FormSub Δ Γ v g σ =
  -- use function extentionality
  ext (λ x → sym (↑-trans (⊆-trans g ⊆₀) g (∈CtxtS v) (σ x) λ z i → refl))
--}

{--
substF↑ : {Γ Δ Φ : Ctxt} (σ : FormSub Φ) (f : Form Γ) (e : Γ ⊆ Δ) (g : Φ ⊆ Δ) (h : Φ ⊆ Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Φ) → g i ≡ e (h i))
        → substF (↑FormSub g σ) (↑ e f)
        ≡ ↑ e (substF (↑FormSub h σ) f)
substF↑ {Γ} {Δ} {Φ} σ (𝕒 x) e g h k = refl
substF↑ {Γ} {Δ} {Φ} σ (var x) e g h k = ↑-trans g h e (σ x) k
substF↑ {Γ} {Δ} {Φ} σ ⊤· e g h k = refl
substF↑ {Γ} {Δ} {Φ} σ ⊥· e g h k = refl
substF↑ {Γ} {Δ} {Φ} σ (f ∧· f₁) e g h k = cong₂ _∧·_ (substF↑ σ f e g h k) (substF↑ σ f₁ e g h k)
substF↑ {Γ} {Δ} {Φ} σ (f ∨· f₁) e g h k = cong₂ _∨·_ (substF↑ σ f e g h k) (substF↑ σ f₁ e g h k)
substF↑ {Γ} {Δ} {Φ} σ (f →· f₁) e g h k = cong₂ _→·_ (substF↑ σ f e g h k) (substF↑ σ f₁ e g h k)
substF↑ {Γ} {Δ} {Φ} σ (∀· u f) e g h k =
  cong (∀· u)
       (trans (cong (λ z → substF z (↑ (⊆، (𝕍𝕌 u) e) f))
                    (FormSub،-↑FormSub Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF↑ σ f (⊆، (𝕍𝕌 u) e) (⊆-trans g ⊆₀) (⊆-trans h ⊆₀) (λ v i → cong (∈CtxtS (𝕍𝕌 u)) (k v i)))
                     (cong (λ z → ↑ (⊆، (𝕍𝕌 u) e) (substF z f))
                           (sym (FormSub،-↑FormSub Φ Γ (𝕍𝕌 u) h σ)))))
substF↑ {Γ} {Δ} {Φ} σ (∃· u f) e g h k =
  cong (∃· u)
       (trans (cong (λ z → substF z (↑ (⊆، (𝕍𝕌 u) e) f))
                    (FormSub،-↑FormSub Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF↑ σ f (⊆، (𝕍𝕌 u) e) (⊆-trans g ⊆₀) (⊆-trans h ⊆₀) (λ v i → cong (∈CtxtS (𝕍𝕌 u)) (k v i)))
                     (cong (λ z → ↑ (⊆، (𝕍𝕌 u) e) (substF z f))
                           (sym (FormSub،-↑FormSub Φ Γ (𝕍𝕌 u) h σ)))))
substF↑ {Γ} {Δ} {Φ} σ (𝔸 x) e g h k = refl
substF↑ {Γ} {Δ} {Φ} σ (f Ｕ f₁) e g h k = cong₂ _Ｕ_ (substF↑ σ f e g h k) (substF↑ σ f₁ e g h k)
substF↑ {Γ} {Δ} {Φ} σ (Ｏ f) e g h k = cong Ｏ (substF↑ σ f e g h k)
substF↑ {Γ} {Δ} {Φ} σ (f Ｓ f₁) e g h k = cong₂ _Ｓ_ (substF↑ σ f e g h k) (substF↑ σ f₁ e g h k)
substF↑ {Γ} {Δ} {Φ} σ (Ｙ f) e g h k = cong Ｙ (substF↑ σ f e g h k)
substF↑ {Γ} {Δ} {Φ} σ (Ｂ f) e g h k = cong Ｂ (substF↑ σ f e g h k)
substF↑ {Γ} {Δ} {Φ} σ (Ｆ f) e g h k =
  cong Ｆ_
       (trans (cong (λ z → substF z (↑ (⊆، 𝕍ℝ e) f))
                    (FormSub،-↑FormSub Φ Δ 𝕍ℝ g σ))
              (trans (substF↑ σ f (⊆، 𝕍ℝ e) (⊆-trans g ⊆₀) (⊆-trans h ⊆₀) (λ v i → cong (∈CtxtS 𝕍ℝ) (k v i)))
                     (cong (λ z → ↑ (⊆، 𝕍ℝ e) (substF z f))
                           (sym (FormSub،-↑FormSub Φ Γ 𝕍ℝ h σ)))))
substF↑ {Γ} {Δ} {Φ} σ (t₁ ⟨ x ⟩ t₂) e g h k = refl
--}

-- Weakening by ⊆₀ commutes with the ≡-induced coercion, for context elements.
-- Proved by generalising the equation and matching on refl: then
--   sym refl ↝ refl,  cong f refl ↝ refl,  ≡-to-⊆ refl ↝ ⊆-refl
-- and all that is left is ↑CE⊆-refl.
↑CE₀-↑CE≡ : (Γ Δ : Ctxt) (v : 𝕍) (e : Δ ≡ Γ) (x : CE Γ)
          → ↑CE₀ {Δ} {v} (↑CE≡ (sym e) x)
          ≡ ↑CE≡ (sym (cong (λ z → z ، v) e)) (↑CE₀ {Γ} {v} x)
↑CE₀-↑CE≡ Γ .Γ v refl x =
  trans (cong (↑CE₀ {Γ} {v}) (↑CE⊆-refl x))
        (sym (↑CE⊆-refl (↑CE₀ {Γ} {v} x)))

-- Same, for formulas.
↑₀-↑≡ : (Γ Δ : Ctxt) (v : 𝕍) (e : Δ ≡ Γ) (f : Form Γ)
      → ↑₀ {Δ} {v} (↑≡ (sym e) f)
      ≡ ↑≡ (sym (cong (λ z → z ، v) e)) (↑₀ {Γ} {v} f)
↑₀-↑≡ Γ .Γ v refl f =
  trans (cong (↑₀ {Γ} {v}) (↑⊆-refl f))
        (sym (↑⊆-refl (↑₀ {Γ} {v} f)))

{--
subst-Ax : (σ : FormSub₀) {Δ : ℂ₀} {r : ℂCE Δ} {A : ℂForm Δ}
         → Ax Δ r A
         → Ax (substCtxt σ Δ)
              (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) r)
              (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) A))
subst-Ax σ {Δ} {r} {A} (found c .A .r) =
  found (substCtxt σ c)
        (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) A))
        (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) r)
subst-Ax σ {Δ} {r} {A} (skip {c} {.r} {.A} f a h) =
  skip (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) f))
       (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) a)
       (subst-Ax σ h)
subst-Ax σ {Δ} {r} {A} (down {c} {v} {x} {C} h) =
  subst (λ z → Ax (substCtxt σ (ℂv c v))
                  (↑CE≡ (sym (ℂtxt-substCtxt σ (ℂv c v))) (↑CE₀ x))
                  (↑≡ (sym (ℂtxt-substCtxt σ (ℂv c v))) z))
        (sym (substF↑ σ C (∈CtxtS v) (ℂtxt⊆ (ℂv c v)) (⟨⟩⊆ {ℂtxt c}) (λ z ())))
        (subst (Ax (substCtxt σ (ℂv c v))
               (↑CE≡ (sym (ℂtxt-substCtxt σ (ℂv c v))) (↑CE₀ x)))
               (sym (sym (↑-trans (⊆-trans (≡-to-⊆ (sym (ℂtxt-substCtxt σ c))) ⊆₀)
                                  (∈CtxtS v)
                                  (≡-to-⊆ (sym (cong (λ z → z ، v) (ℂtxt-substCtxt σ c))))
                                  (substF (↑FormSub ⟨⟩⊆ σ) C)
                                  (λ z i → {!!}))))
               {!(λ i → ∈CtxtS v (≡-to-⊆ (sym (ℂtxt-substCtxt σ c)) i))!})
--}

{--
subst-Ax : (σ : FormSub₀) {Δ : ℂ₀} {r : ℂCE Δ} {A : ℂForm Δ}
         → Ax Δ r A
         → Ax (substCtxt σ Δ)
              (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) r)
              (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) A))
subst-Ax σ {Δ} {r} {A} (found c .A .r) =
  found (substCtxt σ c)
        (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) A))
        (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) r)
subst-Ax σ {Δ} {r} {A} (skip {c} {.r} {.A} f a h) =
  skip (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) f))
       (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) a)
       (subst-Ax σ h)
subst-Ax σ {Δ} {r} {A} (down {c} {v} {x} {C} h) =
  subst₂ (Ax (ℂv (substCtxt σ c) v))
         eqCE
         eqF
         (down {substCtxt σ c} {v} (subst-Ax σ h))
  where
  -- the substituted body, as produced by the induction hypothesis
  D : Form (ℂtxt c)
  D = substF (↑FormSub (ℂtxt⊆ c) σ) C

  e : ℂtxt (substCtxt σ c) ≡ ℂtxt c
  e = ℂtxt-substCtxt σ c

  eqCE : ↑CE₀ {ℂtxt (substCtxt σ c)} {v} (↑CE≡ (sym e) x)
       ≡ ↑CE≡ (sym (ℂtxt-substCtxt σ (ℂv c v))) (↑CE₀ {ℂtxt c} {v} x)
  eqCE = ↑CE₀-↑CE≡ (ℂtxt c) (ℂtxt (substCtxt σ c)) v e x

  -- substF commutes with ↑₀ : this is exactly substF↑, with h := ℂtxt⊆ c
  -- (NOT ⟨⟩⊆ -- that gives a merely pointwise-equal renaming, which will not
  --  match the shape produced by the induction hypothesis).
  eqSub : ↑₀ {ℂtxt c} {v} D
        ≡ substF (↑FormSub (ℂtxt⊆ (ℂv c v)) σ) (↑₀ {ℂtxt c} {v} C)
  eqSub = sym (substF↑ σ C ⊆₀ (ℂtxt⊆ (ℂv c v)) (ℂtxt⊆ c) (λ z ()))

  eqF : ↑₀ {ℂtxt (substCtxt σ c)} {v} (↑≡ (sym e) D)
      ≡ ↑≡ (sym (ℂtxt-substCtxt σ (ℂv c v)))
           (substF (↑FormSub (ℂtxt⊆ (ℂv c v)) σ) (↑₀ {ℂtxt c} {v} C))
  eqF =
    trans (↑₀-↑≡ (ℂtxt c) (ℂtxt (substCtxt σ c)) v e D)
          (cong (↑≡ (sym (ℂtxt-substCtxt σ (ℂv c v)))) eqSub)
--}

⊆⋆→⊆ : {Γ Δ : Ctxt} → Γ ⊆⋆ Δ → Γ ⊆ Δ
⊆⋆→⊆ {Γ} {Δ} s {u} i = app-⊆⋆ s u i

-- app-⊆⋆ of ⊆⋆-refl is the identity.
app-⊆⋆-refl : {Γ : Ctxt} (v : 𝕍) (i : ∈Ctxt v Γ)
            → app-⊆⋆ (⊆⋆-refl {Γ}) v i ≡ i
app-⊆⋆-refl v (∈Ctxt0 Γ)   = refl
app-⊆⋆-refl v (∈CtxtS u i) = cong (∈CtxtS u) (app-⊆⋆-refl v i)

app-⊆⋆-trans : {Γ Δ Ψ : Ctxt} (s : Γ ⊆⋆ Δ) (t : Δ ⊆⋆ Ψ) (v : 𝕍) (i : ∈Ctxt v Γ)
             → app-⊆⋆ (⊆⋆-trans s t) v i ≡ app-⊆⋆ t v (app-⊆⋆ s v i)
--app-⊆⋆-trans = ?
app-⊆⋆-trans (⊆⋆-init _)   t              v ()
app-⊆⋆-trans (⊆⋆-add u s)  (⊆⋆-add .u t)  v (∈Ctxt0 _)    = refl
app-⊆⋆-trans (⊆⋆-add u s)  (⊆⋆-add .u t)  v (∈CtxtS .u i) =
  cong (∈CtxtS u) (app-⊆⋆-trans s t v i)
app-⊆⋆-trans (⊆⋆-skip u s) (⊆⋆-add .u t)  v i =
  cong (∈CtxtS u) (app-⊆⋆-trans s t v i)
app-⊆⋆-trans (⊆⋆-add u s)  (⊆⋆-skip w t)  v i =
  cong (∈CtxtS w) (app-⊆⋆-trans (⊆⋆-add u s) t v i)
app-⊆⋆-trans (⊆⋆-skip u s) (⊆⋆-skip w t)  v i =
  cong (∈CtxtS w) (app-⊆⋆-trans (⊆⋆-skip u s) t v i)

-- Specialisation used in the quantifier cases of substF⋆↑.
app-⊆⋆-⊆⋆₀ : {Γ Δ : Ctxt} {u : 𝕍} (s : Γ ⊆⋆ Δ) (v : 𝕍) (i : ∈Ctxt v Γ)
            → app-⊆⋆ (⊆⋆-trans s (⊆⋆₀ {Δ} {u})) v i ≡ ∈CtxtS u (app-⊆⋆ s v i)
app-⊆⋆-⊆⋆₀ {Γ} {Δ} {u} s v i =
  trans (app-⊆⋆-trans s ⊆⋆₀ v i)
        (cong (∈CtxtS u) (app-⊆⋆-refl v (app-⊆⋆ s v i)))

-- ⊆⋆-add commutes with ⊆، under the translation.  Needed for the binder cases
-- of ↑-⊆⋆ below.  Both clauses are refl; only the indices differ.
⊆⋆→⊆-add : {Γ Δ : Ctxt} (u : 𝕍) (s : Γ ⊆⋆ Δ)
         → ≡⊆ (⊆⋆→⊆ (⊆⋆-add u s)) (⊆، u (⊆⋆→⊆ s))
⊆⋆→⊆-add u s (∈Ctxt0 _)    = refl
⊆⋆→⊆-add u s (∈CtxtS .u i) = refl

↑ᵢ-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : Agent Γ)
      → ↑⋆ᵢ s a ≡ ↑ᵢ (⊆⋆→⊆ s) a
↑ᵢ-⊆⋆ s (agentV i) = refl
↑ᵢ-⊆⋆ s (agentC x) = refl

↑ₛ-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : Agents Γ)
      → ↑⋆ₛ s a ≡ ↑ₛ (⊆⋆→⊆ s) a
↑ₛ-⊆⋆ {Γ} {Δ} s (agentsV i) = refl
↑ₛ-⊆⋆ {Γ} {Δ} s (agentsL l) = cong agentsL (mapl l)
  where
  mapl : (l : List (Agent Γ))
       → Data.List.map (↑⋆ᵢ s) l ≡ Data.List.map (↑ᵢ (⊆⋆→⊆ s)) l
  mapl []       = refl
  mapl (x ∷ xs) = cong₂ _∷_ (↑ᵢ-⊆⋆ s x) (mapl xs)

↑ₚ-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : AtomProp Γ)
      → ↑⋆ₚ s a ≡ ↑ₚ (⊆⋆→⊆ s) a
↑ₚ-⊆⋆ s (atomPropV i) = refl
↑ₚ-⊆⋆ s (atomPropC x) = refl

↑d-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : Data Γ)
      → ↑⋆d s a ≡ ↑d (⊆⋆→⊆ s) a
↑d-⊆⋆ s (dataV i) = refl
↑d-⊆⋆ s (dataC x) = refl

↑ₜ-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : Action Γ)
      → ↑⋆ₜ s a ≡ ↑ₜ (⊆⋆→⊆ s) a
↑ₜ-⊆⋆ s (ActSend p a A) =
  cong₃ ActSend (↑d-⊆⋆ s p) (↑ᵢ-⊆⋆ s a) (↑ₛ-⊆⋆ s A)

↑ₑ-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : Event Γ)
      → ↑⋆ₑ s a ≡ ↑ₑ (⊆⋆→⊆ s) a
↑ₑ-⊆⋆ s (EvtReceive p a b) =
  cong₃ EvtReceive (↑d-⊆⋆ s p) (↑ᵢ-⊆⋆ s a) (↑ᵢ-⊆⋆ s b)
↑ₑ-⊆⋆ s (EvtInternal a d) =
  cong₂ EvtInternal (↑ᵢ-⊆⋆ s a) (↑d-⊆⋆ s d)

↑f-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : Fault Γ)
      → ↑⋆f s a ≡ ↑f (⊆⋆→⊆ s) a
↑f-⊆⋆ s (FaultCorrect a b) =
  cong₂ FaultCorrect (↑ᵢ-⊆⋆ s a) (↑ᵢ-⊆⋆ s b)

↑ₐ-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (a : Atom Γ)
      → ↑⋆ₐ s a ≡ ↑ₐ (⊆⋆→⊆ s) a
↑ₐ-⊆⋆ s (atProp    x) = cong atProp    (↑ₚ-⊆⋆ s x)
↑ₐ-⊆⋆ s (atAction  x) = cong atAction  (↑ₜ-⊆⋆ s x)
↑ₐ-⊆⋆ s (atEvent   x) = cong atEvent   (↑ₑ-⊆⋆ s x)
↑ₐ-⊆⋆ s (atCorrect x) = cong atCorrect (↑f-⊆⋆ s x)

↑ᵣ-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (r : Res Γ)
      → ↑⋆ᵣ s r ≡ ↑ᵣ (⊆⋆→⊆ s) r
↑ᵣ-⊆⋆ s (𝐯 i)     = refl
↑ᵣ-⊆⋆ s 𝟎         = refl
↑ᵣ-⊆⋆ s (rvar ρ)         = refl
↑ᵣ-⊆⋆ s (r ⋆ r₁)  = cong₂ _⋆_ (↑ᵣ-⊆⋆ s r) (↑ᵣ-⊆⋆ s r₁)

↑A-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (A : SetAtom Γ)
      → ↑⋆A s A ≡ ↑A (⊆⋆→⊆ s) A
↑A-⊆⋆ s (a ∈ₐ A)     = cong₂ _∈ₐ_ (↑ᵢ-⊆⋆ s a) (↑ₛ-⊆⋆ s A)
↑A-⊆⋆ s (∣ A ∣ₛ＝ n) = cong (∣_∣ₛ＝ n) (↑ₛ-⊆⋆ s A)

-- The Form case.  Under a binder, ↑⋆ pushes ⊆⋆-add while ↑ pushes ⊆، ; the two
-- are only *pointwise* equal, so we fix up with ≡↑ (already in Subst.lagda).
↑-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (f : Form Γ)
     → ↑⋆ s f ≡ ↑ (⊆⋆→⊆ s) f
--↑-⊆⋆ {⟨⟩} {⟨⟩} (⊆⋆-init ⟨⟩) f = ?
↑-⊆⋆ s (𝕒 x)     = cong 𝕒 (↑ₐ-⊆⋆ s x)
↑-⊆⋆ s (var x)   = refl
↑-⊆⋆ s ⊤·        = refl
↑-⊆⋆ s ⊥·        = refl
↑-⊆⋆ s (f ∧· g)  = cong₂ _∧·_ (↑-⊆⋆ s f) (↑-⊆⋆ s g)
↑-⊆⋆ s (f ∨· g)  = cong₂ _∨·_ (↑-⊆⋆ s f) (↑-⊆⋆ s g)
↑-⊆⋆ s (f →· g)  = cong₂ _→·_ (↑-⊆⋆ s f) (↑-⊆⋆ s g)
↑-⊆⋆ s (∀· u f)  =
  cong (∀· u)
       (trans (↑-⊆⋆ (⊆⋆-add (𝕍𝕌 u) s) f)
              (≡↑ f (⊆⋆→⊆ (⊆⋆-add (𝕍𝕌 u) s)) (⊆، (𝕍𝕌 u) (⊆⋆→⊆ s))
                    (⊆⋆→⊆-add (𝕍𝕌 u) s)))
↑-⊆⋆ s (∃· u f)  =
  cong (∃· u)
       (trans (↑-⊆⋆ (⊆⋆-add (𝕍𝕌 u) s) f)
              (≡↑ f (⊆⋆→⊆ (⊆⋆-add (𝕍𝕌 u) s)) (⊆، (𝕍𝕌 u) (⊆⋆→⊆ s))
                    (⊆⋆→⊆-add (𝕍𝕌 u) s)))
↑-⊆⋆ s (𝔸 A)     = cong 𝔸 (↑A-⊆⋆ s A)
↑-⊆⋆ s (f Ｕ g)  = cong₂ _Ｕ_ (↑-⊆⋆ s f) (↑-⊆⋆ s g)
↑-⊆⋆ s (Ｏ f)    = cong Ｏ (↑-⊆⋆ s f)
↑-⊆⋆ s (f Ｓ g)  = cong₂ _Ｓ_ (↑-⊆⋆ s f) (↑-⊆⋆ s g)
↑-⊆⋆ s (Ｙ f)    = cong Ｙ (↑-⊆⋆ s f)
↑-⊆⋆ s (Ｂ f)    = cong Ｂ (↑-⊆⋆ s f)
↑-⊆⋆ s (Ｆ f)    =
  cong Ｆ_
       (trans (↑-⊆⋆ (⊆⋆-add 𝕍ℝ s) f)
              (≡↑ f (⊆⋆→⊆ (⊆⋆-add 𝕍ℝ s)) (⊆، 𝕍ℝ (⊆⋆→⊆ s))
                    (⊆⋆→⊆-add 𝕍ℝ s)))
↑-⊆⋆ s (t₁ ⟨ c ⟩ t₂) = cong₂ (_⟨ c ⟩_) (↑ᵣ-⊆⋆ s t₁) (↑ᵣ-⊆⋆ s t₂)

↑I-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (I : Interval Γ)
      → ↑⋆I s I ≡ ↑I (⊆⋆→⊆ s) I
↑I-⊆⋆ s ［ a , b ］ = cong₂ ［_,_］ (↑ᵣ-⊆⋆ s a) (↑ᵣ-⊆⋆ s b)
↑I-⊆⋆ s ［ a , b ） = cong₂ ［_,_） (↑ᵣ-⊆⋆ s a) (↑ᵣ-⊆⋆ s b)
↑I-⊆⋆ s （ a , b ］ = cong₂ （_,_］ (↑ᵣ-⊆⋆ s a) (↑ᵣ-⊆⋆ s b)
↑I-⊆⋆ s （ a , b ） = cong₂ （_,_） (↑ᵣ-⊆⋆ s a) (↑ᵣ-⊆⋆ s b)

↑CE-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (x : CE Γ)
       → ↑⋆CE s x ≡ ↑CE (⊆⋆→⊆ s) x
↑CE-⊆⋆ s (CEr r) = cong CEr (↑ᵣ-⊆⋆ s r)
↑CE-⊆⋆ s CEu     = refl
↑CE-⊆⋆ s (CEi I) = cong CEi (↑I-⊆⋆ s I)

-- ↑⋆ followed by a *semantic* lift.  This is the ⋆-analogue of ↑-trans and is
-- what the `var` case of substF⋆↑ needs.
↑⋆-trans↑ : {Γ Ψ Δ : Ctxt} (g : Γ ⊆⋆ Δ) (h : Γ ⊆⋆ Ψ) (e : Ψ ⊆ Δ) (f : Form Γ)
          → ((v : 𝕍) (i : ∈Ctxt v Γ) → app-⊆⋆ g v i ≡ e (app-⊆⋆ h v i))
          → ↑⋆ g f ≡ ↑ e (↑⋆ h f)
↑⋆-trans↑ g h e f k =
  trans (↑-⊆⋆ g f)
        (trans (↑-trans (⊆⋆→⊆ g) (⊆⋆→⊆ h) e f k)
               (cong (↑ e) (sym (↑-⊆⋆ h f))))

↑⋆-trans↑⋆ : {Γ Ψ Δ : Ctxt} (g : Γ ⊆⋆ Δ) (h : Γ ⊆⋆ Ψ) (e : Ψ ⊆⋆ Δ) (f : Form Γ)
           → ((v : 𝕍) (i : ∈Ctxt v Γ) → app-⊆⋆ g v i ≡ app-⊆⋆ e _ (app-⊆⋆ h v i))
           → ↑⋆ g f ≡ ↑⋆ e (↑⋆ h f)
↑⋆-trans↑⋆ g h e f k =
  trans (↑⋆-trans↑ g h (⊆⋆→⊆ e) f k) (sym (↑-⊆⋆ e (↑⋆ h f)))

-- Purely syntactic version.
↑⋆-trans⋆ : {Γ Δ Ψ : Ctxt} (s : Γ ⊆⋆ Δ) (t : Δ ⊆⋆ Ψ) (f : Form Γ)
          → ↑⋆ (⊆⋆-trans s t) f ≡ ↑⋆ t (↑⋆ s f)
↑⋆-trans⋆ s t f =
  trans (↑⋆-trans↑ (⊆⋆-trans s t) s (⊆⋆→⊆ t) f (app-⊆⋆-trans s t))
        (sym (↑-⊆⋆ t (↑⋆ s f)))


-- ⋆-analogue of FormSub،-↑FormSub.  Note: no function extensionality needed
-- here, because FormSub⋆ is an inductive list rather than a function.
FormSub⋆،-↑FormSub⋆ : (Δ Γ : Ctxt) (v : 𝕍) (g : Δ ⊆⋆ Γ) (σ : FormSub⋆ Δ)
                    → FormSub⋆، Γ v (↑FormSub⋆ g σ)
                    ≡ ↑FormSub⋆ (⊆⋆-trans g ⊆⋆₀) σ
FormSub⋆،-↑FormSub⋆ Δ Γ v g ●             = refl
FormSub⋆،-↑FormSub⋆ Δ Γ v g (x ↦ f ⨾ σ) =
  cong₂ (λ a b → x ↦ a ⨾ b)
        (sym (↑⋆-trans⋆ g ⊆⋆₀ f))
        (FormSub⋆،-↑FormSub⋆ Δ Γ v g σ)

-- The `var` case.  The `with x ≟ y` below abstracts over exactly the scrutinee
-- that app-FormSub⋆ itself matches on, so both sides of the goal reduce
-- simultaneously.
app-FormSub⋆-↑ : {Γ Δ Φ : Ctxt} (σ : FormSub⋆ Φ) (x : FormVar)
                 (e : Γ ⊆ Δ) (g : Φ ⊆⋆ Δ) (h : Φ ⊆⋆ Γ)
               → ((v : 𝕍) (i : ∈Ctxt v Φ) → app-⊆⋆ g v i ≡ e (app-⊆⋆ h v i))
               → app-FormSub⋆ x (↑FormSub⋆ g σ)
               ≡ ↑ e (app-FormSub⋆ x (↑FormSub⋆ h σ))
app-FormSub⋆-↑ ● x e g h k = refl
app-FormSub⋆-↑ (y ↦ f ⨾ σ) x e g h k with x ≟ y
... | yes refl = ↑⋆-trans↑ g h e f k
... | no  p    = app-FormSub⋆-↑ σ x e g h k

substF⋆↑ : {Γ Δ Φ : Ctxt} (σ : FormSub⋆ Φ) (f : Form Γ)
           (e : Γ ⊆ Δ) (g : Φ ⊆⋆ Δ) (h : Φ ⊆⋆ Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Φ) → app-⊆⋆ g v i ≡ e (app-⊆⋆ h v i))
         → substF⋆ (↑FormSub⋆ g σ) (↑ e f)
         ≡ ↑ e (substF⋆ (↑FormSub⋆ h σ) f)
substF⋆↑ {Γ} {Δ} {Φ} σ (𝕒 x)    e g h k = refl
substF⋆↑ {Γ} {Δ} {Φ} σ (var x)  e g h k = app-FormSub⋆-↑ σ x e g h k
substF⋆↑ {Γ} {Δ} {Φ} σ ⊤·       e g h k = refl
substF⋆↑ {Γ} {Δ} {Φ} σ ⊥·       e g h k = refl
substF⋆↑ {Γ} {Δ} {Φ} σ (f ∧· f₁) e g h k =
  cong₂ _∧·_ (substF⋆↑ σ f e g h k) (substF⋆↑ σ f₁ e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (f ∨· f₁) e g h k =
  cong₂ _∨·_ (substF⋆↑ σ f e g h k) (substF⋆↑ σ f₁ e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (f →· f₁) e g h k =
  cong₂ _→·_ (substF⋆↑ σ f e g h k) (substF⋆↑ σ f₁ e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (∀· u f) e g h k =
  cong (∀· u)
       (trans (cong (λ z → substF⋆ z (↑ (⊆، (𝕍𝕌 u) e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF⋆↑ σ f (⊆، (𝕍𝕌 u) e)
                               (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀)
                               (cond (𝕍𝕌 u)))
                     (cong (λ z → ↑ (⊆، (𝕍𝕌 u) e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ (𝕍𝕌 u) h σ)))))
  where
  cond : (w : 𝕍) (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {w})) v i
       ≡ ⊆، w e (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {w})) v i)
  cond w v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS w) (k v i))
                 (cong (λ z → ⊆، w e z) (sym (app-⊆⋆-⊆⋆₀ h v i))))
substF⋆↑ {Γ} {Δ} {Φ} σ (∃· u f) e g h k =
  cong (∃· u)
       (trans (cong (λ z → substF⋆ z (↑ (⊆، (𝕍𝕌 u) e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF⋆↑ σ f (⊆، (𝕍𝕌 u) e)
                               (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀)
                               (cond (𝕍𝕌 u)))
                     (cong (λ z → ↑ (⊆، (𝕍𝕌 u) e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ (𝕍𝕌 u) h σ)))))
  where
  cond : (w : 𝕍) (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {w})) v i
       ≡ ⊆، w e (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {w})) v i)
  cond w v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS w) (k v i))
                 (cong (λ z → ⊆، w e z) (sym (app-⊆⋆-⊆⋆₀ h v i))))
substF⋆↑ {Γ} {Δ} {Φ} σ (𝔸 x)     e g h k = refl
substF⋆↑ {Γ} {Δ} {Φ} σ (f Ｕ f₁) e g h k =
  cong₂ _Ｕ_ (substF⋆↑ σ f e g h k) (substF⋆↑ σ f₁ e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (Ｏ f)    e g h k = cong Ｏ (substF⋆↑ σ f e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (f Ｓ f₁) e g h k =
  cong₂ _Ｓ_ (substF⋆↑ σ f e g h k) (substF⋆↑ σ f₁ e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (Ｙ f)    e g h k = cong Ｙ (substF⋆↑ σ f e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (Ｂ f)    e g h k = cong Ｂ (substF⋆↑ σ f e g h k)
substF⋆↑ {Γ} {Δ} {Φ} σ (Ｆ f)    e g h k =
  cong Ｆ_
       (trans (cong (λ z → substF⋆ z (↑ (⊆، 𝕍ℝ e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ 𝕍ℝ g σ))
              (trans (substF⋆↑ σ f (⊆، 𝕍ℝ e)
                               (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀) cond)
                     (cong (λ z → ↑ (⊆، 𝕍ℝ e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ 𝕍ℝ h σ)))))
  where
  cond : (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {𝕍ℝ})) v i
       ≡ ⊆، 𝕍ℝ e (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {𝕍ℝ})) v i)
  cond v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS 𝕍ℝ) (k v i))
                 (cong (λ z → ⊆، 𝕍ℝ e z) (sym (app-⊆⋆-⊆⋆₀ h v i))))
substF⋆↑ {Γ} {Δ} {Φ} σ (t₁ ⟨ x ⟩ t₂) e g h k = refl

{--
FormSub⋆،-↑FormSub⋆ : (Δ Γ : Ctxt) (v : 𝕍) (g : Δ ⊆⋆ Γ) (σ : FormSub⋆ Δ)
                    → FormSub⋆، Γ v (↑FormSub⋆ g σ)
                    ≡ ↑FormSub⋆ (⊆⋆-trans g (⊆⋆₀ {Γ} {v})) σ
FormSub⋆،-↑FormSub⋆ Δ Γ v g ● = refl
FormSub⋆،-↑FormSub⋆ Δ Γ v g (x ↦ f ⨾ σ) =
  cong₂ (λ a b → x ↦ a ⨾ b)
        -- ↑⋆ ⊆⋆₀ (↑⋆ g f) ≡ ↑⋆ (⊆⋆-trans g ⊆⋆₀) f
        (sym (↑⋆-trans⋆ (⊆⋆-trans g (⊆⋆₀ {Γ} {v})) g (⊆⋆₀ {Γ} {v}) f
                        (app-⊆⋆-trans g (⊆⋆₀ {Γ} {v}))))
        (FormSub⋆،-↑FormSub⋆ Δ Γ v g σ)
--}

app-FormSub⋆-↑⋆ : {Γ Δ Φ : Ctxt} (σ : FormSub⋆ Φ) (x : FormVar)
                  (e : Γ ⊆⋆ Δ) (g : Φ ⊆⋆ Δ) (h : Φ ⊆⋆ Γ)
                → ((v : 𝕍) (i : ∈Ctxt v Φ)
                      → app-⊆⋆ g v i ≡ app-⊆⋆ e v (app-⊆⋆ h v i))
                → app-FormSub⋆ x (↑FormSub⋆ g σ)
                ≡ ↑⋆ e (app-FormSub⋆ x (↑FormSub⋆ h σ))
app-FormSub⋆-↑⋆ ●             x e g h k = refl        -- var x ≡ ↑⋆ e (var x)
app-FormSub⋆-↑⋆ (y ↦ f ⨾ σ)   x e g h k with x ≟ y
... | yes refl = ↑⋆-trans↑⋆ g h e f k
... | no  p    = app-FormSub⋆-↑⋆ σ x e g h k

substF⋆↑⋆ : {Γ Δ Φ : Ctxt} (σ : FormSub⋆ Φ) (f : Form Γ)
            (e : Γ ⊆⋆ Δ) (g : Φ ⊆⋆ Δ) (h : Φ ⊆⋆ Γ)
          → ((v : 𝕍) (i : ∈Ctxt v Φ)
               → app-⊆⋆ g v i ≡ app-⊆⋆ e v (app-⊆⋆ h v i))
          → substF⋆ (↑FormSub⋆ g σ) (↑⋆ e f)
          ≡ ↑⋆ e (substF⋆ (↑FormSub⋆ h σ) f)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (𝕒 x)     e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (var x)   e g h k = app-FormSub⋆-↑⋆ σ x e g h k
substF⋆↑⋆ {Γ} {Δ} {Φ} σ ⊤·        e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ ⊥·        e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f ∧· f₁) e g h k =
  cong₂ _∧·_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f ∨· f₁) e g h k =
  cong₂ _∨·_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f →· f₁) e g h k =
  cong₂ _→·_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (∀· u f) e g h k =
  cong (∀· u)
       (trans (cong (λ z → substF⋆ z (↑⋆ (⊆⋆، (𝕍𝕌 u) e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF⋆↑⋆ σ f (⊆⋆، (𝕍𝕌 u) e)
                                (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀)
                                (cond (𝕍𝕌 u)))
                     (cong (λ z → ↑⋆ (⊆⋆، (𝕍𝕌 u) e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ (𝕍𝕌 u) h σ)))))
  where
  cond : (w : 𝕍) (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {w})) v i
       ≡ app-⊆⋆ (⊆⋆، w e) v (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {w})) v i)
  cond w v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS w) (k v i))
                 (sym (cong (app-⊆⋆ (⊆⋆، w e) v) (app-⊆⋆-⊆⋆₀ h v i))))
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (∃· u f) e g h k =
  cong (∃· u)
       (trans (cong (λ z → substF⋆ z (↑⋆ (⊆⋆، (𝕍𝕌 u) e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF⋆↑⋆ σ f (⊆⋆، (𝕍𝕌 u) e)
                                (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀)
                                (cond (𝕍𝕌 u)))
                     (cong (λ z → ↑⋆ (⊆⋆، (𝕍𝕌 u) e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ (𝕍𝕌 u) h σ)))))
  where
  cond : (w : 𝕍) (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {w})) v i
       ≡ app-⊆⋆ (⊆⋆، w e) v (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {w})) v i)
  cond w v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS w) (k v i))
                 (sym (cong (app-⊆⋆ (⊆⋆، w e) v) (app-⊆⋆-⊆⋆₀ h v i))))
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (𝔸 x)     e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f Ｕ f₁) e g h k =
  cong₂ _Ｕ_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｏ f)    e g h k = cong Ｏ (substF⋆↑⋆ σ f e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f Ｓ f₁) e g h k =
  cong₂ _Ｓ_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｙ f)    e g h k = cong Ｙ (substF⋆↑⋆ σ f e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｂ f)    e g h k = cong Ｂ (substF⋆↑⋆ σ f e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｆ f)    e g h k =
  cong Ｆ_
       (trans (cong (λ z → substF⋆ z (↑⋆ (⊆⋆، 𝕍ℝ e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ 𝕍ℝ g σ))
              (trans (substF⋆↑⋆ σ f (⊆⋆، 𝕍ℝ e)
                                (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀) cond)
                     (cong (λ z → ↑⋆ (⊆⋆، 𝕍ℝ e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ 𝕍ℝ h σ)))))
  where
  cond : (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {𝕍ℝ})) v i
       ≡ app-⊆⋆ (⊆⋆، 𝕍ℝ e) v (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {𝕍ℝ})) v i)
  cond v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS 𝕍ℝ) (k v i))
                 (sym (cong (app-⊆⋆ (⊆⋆، 𝕍ℝ e) v) (app-⊆⋆-⊆⋆₀ h v i))))
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (t₁ ⟨ x ⟩ t₂) e g h k = refl

{--
substF⋆↑⋆ : {Γ Δ Φ : Ctxt} (σ : FormSub⋆ Φ) (f : Form Γ)
            (e : Γ ⊆⋆ Δ) (g : Φ ⊆⋆ Δ) (h : Φ ⊆⋆ Γ)
          → ((v : 𝕍) (i : ∈Ctxt v Φ) → app-⊆⋆ g v i ≡ app-⊆⋆ e v (app-⊆⋆ h v i))
          → substF⋆ (↑FormSub⋆ g σ) (↑⋆ e f)
          ≡ ↑⋆ e (substF⋆ (↑FormSub⋆ h σ) f)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (𝕒 x)    e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (var x)  e g h k = {!!} --app-FormSub⋆-↑ σ x e g h k
substF⋆↑⋆ {Γ} {Δ} {Φ} σ ⊤·       e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ ⊥·       e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f ∧· f₁) e g h k =
  cong₂ _∧·_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f ∨· f₁) e g h k =
  cong₂ _∨·_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f →· f₁) e g h k =
  cong₂ _→·_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (∀· u f) e g h k =
  cong (∀· u)
       {!!} {--(trans (cong (λ z → substF⋆ z (↑ (⊆، (𝕍𝕌 u) e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF⋆↑⋆ σ f (⊆، (𝕍𝕌 u) e)
                               (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀)
                               (cond (𝕍𝕌 u)))
                     (cong (λ z → ↑ (⊆، (𝕍𝕌 u) e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ (𝕍𝕌 u) h σ)))))--}
  where
  cond : (w : 𝕍) (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {w})) v i
       ≡ app-⊆⋆ (⊆⋆، w e) _ (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {w})) v i)
  cond w v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS w) (k v i))
                 {!!} {--(cong (λ z → ⊆⋆، w e z) (sym (app-⊆⋆-⊆⋆₀ h v i)))--})
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (∃· u f) e g h k =
  cong (∃· u)
       {!!} {--(trans (cong (λ z → substF⋆ z (↑ (⊆، (𝕍𝕌 u) e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ (𝕍𝕌 u) g σ))
              (trans (substF⋆↑⋆ σ f (⊆، (𝕍𝕌 u) e)
                               (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀)
                               (cond (𝕍𝕌 u)))
                     (cong (λ z → ↑ (⊆، (𝕍𝕌 u) e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ (𝕍𝕌 u) h σ)))))--}
  where
  cond : (w : 𝕍) (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {w})) v i
       ≡ app-⊆⋆ (⊆⋆، w e) _ (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {w})) v i)
  cond w v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS w) (k v i))
                 {!!} {--(cong (λ z → ⊆⋆، w e z) (sym (app-⊆⋆-⊆⋆₀ h v i)))--})
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (𝔸 x)     e g h k = refl
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f Ｕ f₁) e g h k =
  cong₂ _Ｕ_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｏ f)    e g h k = cong Ｏ (substF⋆↑⋆ σ f e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (f Ｓ f₁) e g h k =
  cong₂ _Ｓ_ (substF⋆↑⋆ σ f e g h k) (substF⋆↑⋆ σ f₁ e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｙ f)    e g h k = cong Ｙ (substF⋆↑⋆ σ f e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｂ f)    e g h k = cong Ｂ (substF⋆↑⋆ σ f e g h k)
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (Ｆ f)    e g h k =
  cong Ｆ_
       {!!} {--(trans (cong (λ z → substF⋆ z (↑ (⊆، 𝕍ℝ e) f))
                    (FormSub⋆،-↑FormSub⋆ Φ Δ 𝕍ℝ g σ))
              (trans (substF⋆↑⋆ σ f (⊆، 𝕍ℝ e)
                               (⊆⋆-trans g ⊆⋆₀) (⊆⋆-trans h ⊆⋆₀) cond)
                     (cong (λ z → ↑ (⊆، 𝕍ℝ e) (substF⋆ z f))
                           (sym (FormSub⋆،-↑FormSub⋆ Φ Γ 𝕍ℝ h σ)))))--}
  where
  cond : (v : 𝕍) (i : ∈Ctxt v Φ)
       → app-⊆⋆ (⊆⋆-trans g (⊆⋆₀ {Δ} {𝕍ℝ})) v i
       ≡ app-⊆⋆ (⊆⋆، 𝕍ℝ e) _ (app-⊆⋆ (⊆⋆-trans h (⊆⋆₀ {Γ} {𝕍ℝ})) v i)
  cond v i =
    trans (app-⊆⋆-⊆⋆₀ g v i)
          (trans (cong (∈CtxtS 𝕍ℝ) (k v i))
                 {!!} {--(cong (λ z → ⊆⋆، 𝕍ℝ e z) (sym (app-⊆⋆-⊆⋆₀ h v i)))--})
substF⋆↑⋆ {Γ} {Δ} {Φ} σ (t₁ ⟨ x ⟩ t₂) e g h k = refl
--}

↑CE₀-↑⋆CE : {Γ Δ : Ctxt} (v : 𝕍) (s : Γ ⊆⋆ Δ) (x : CE Γ)
          → ↑CE₀ {Δ} {v} (↑⋆CE s x)
          ≡ ↑⋆CE (⊆⋆-add v s) (↑CE₀ {Γ} {v} x)
↑CE₀-↑⋆CE {Γ} {Δ} v s x =
  trans (sym (trans (↑CE-trans t (⊆⋆→⊆ s) ⊆₀ x (λ u i → refl))
                    (cong (↑CE ⊆₀) (sym (↑CE-⊆⋆ s x)))))
        (trans (↑CE-trans t ⊆₀ (⊆⋆→⊆ (⊆⋆-add v s)) x (λ u i → refl))
               (sym (↑CE-⊆⋆ (⊆⋆-add v s) (↑CE₀ {Γ} {v} x))))
  where
  t : Γ ⊆ (Δ ، v)
  t = ⊆-trans (⊆⋆→⊆ s) ⊆₀

↑₀-↑⋆ : {Γ Δ : Ctxt} (v : 𝕍) (s : Γ ⊆⋆ Δ) (f : Form Γ)
      → ↑₀ {Δ} {v} (↑⋆ s f)
      ≡ ↑⋆ (⊆⋆-add v s) (↑₀ {Γ} {v} f)
↑₀-↑⋆ {Γ} {Δ} v s f =
  trans (sym (trans (↑-trans t (⊆⋆→⊆ s) ⊆₀ f (λ u i → refl))
                    (cong (↑ ⊆₀) (sym (↑-⊆⋆ s f)))))
        (trans (↑-trans t ⊆₀ (⊆⋆→⊆ (⊆⋆-add v s)) f (λ u i → refl))
               (sym (↑-⊆⋆ (⊆⋆-add v s) (↑₀ {Γ} {v} f))))
  where
  t : Γ ⊆ (Δ ، v)
  t = ⊆-trans (⊆⋆→⊆ s) ⊆₀

subst-Ax⋆ : (σ : FormSub⋆₀) {Δ : ℂ₀} {r : ℂCE Δ} {A : ℂForm Δ}
          → Ax Δ r A
          → Ax (substCtxt⋆ σ Δ)
               (↑⋆CE (ℂtxt-substCtxt⋆ σ Δ) r)
               (↑⋆ (ℂtxt-substCtxt⋆ σ Δ) (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Δ) σ) A))
subst-Ax⋆ σ {Δ} {r} {A} (found c .A .r) =
  found (substCtxt⋆ σ c)
        (↑⋆ (ℂtxt-substCtxt⋆ σ Δ) (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Δ) σ) A))
        (↑⋆CE (ℂtxt-substCtxt⋆ σ Δ) r)
subst-Ax⋆ σ {Δ} {r} {A} (skip {c} {.r} {.A} f a h) =
  skip (↑⋆ (ℂtxt-substCtxt⋆ σ Δ) (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Δ) σ) f))
       (↑⋆CE (ℂtxt-substCtxt⋆ σ Δ) a)
       (subst-Ax⋆ σ h)
subst-Ax⋆ σ {Δ} {r} {A} (down {c} {v} {x} {C} a) =
  subst₂ (Ax (ℂv (substCtxt⋆ σ c) v))
         eqCE
         eqF
         (down {substCtxt⋆ σ c} {v} (subst-Ax⋆ σ a))
  where
  -- the syntactic sub-context witness produced at `c`
  s : ℂtxt c ⊆⋆ ℂtxt (substCtxt⋆ σ c)
  s = ℂtxt-substCtxt⋆ σ c

  -- the substituted body, as produced by the induction hypothesis.  Note that
  -- ℂtxt-substCtxt⋆ σ (ℂv c v) is *definitionally* ⊆⋆-add v s, so the two
  -- lemmas above apply on the nose with no massaging.
  D : Form (ℂtxt c)
  D = substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ c) σ) C

  eqCE : ↑CE₀ {ℂtxt (substCtxt⋆ σ c)} {v} (↑⋆CE s x)
       ≡ ↑⋆CE (ℂtxt-substCtxt⋆ σ (ℂv c v)) (↑CE₀ {ℂtxt c} {v} x)
  eqCE = ↑CE₀-↑⋆CE v s x

  -- substF⋆ commutes with ↑₀.  Use h := ℂtxt⊆⋆ c (NOT some pointwise-equal
  -- renaming), so that the result matches the shape the IH produces; and
  -- g := ℂtxt⊆⋆ (ℂv c v), which is by definition ⊆⋆-trans (ℂtxt⊆⋆ c) ⊆⋆₀.
  -- Since Φ = ⟨⟩ the compatibility side condition is vacuous.
  eqSub : ↑₀ {ℂtxt c} {v} D
        ≡ substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ (ℂv c v)) σ) (↑₀ {ℂtxt c} {v} C)
  eqSub = sym (substF⋆↑ σ C ⊆₀ (ℂtxt⊆⋆ (ℂv c v)) (ℂtxt⊆⋆ c) (λ z ()))

  eqF : ↑₀ {ℂtxt (substCtxt⋆ σ c)} {v} (↑⋆ s D)
      ≡ ↑⋆ (ℂtxt-substCtxt⋆ σ (ℂv c v))
           (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ (ℂv c v)) σ) (↑₀ {ℂtxt c} {v} C))
  eqF = trans (↑₀-↑⋆ v s D)
              (cong (↑⋆ (ℂtxt-substCtxt⋆ σ (ℂv c v))) eqSub)

{--
subst-Ax⋆ σ {Δ} {r} {A} (down {c} {v} {x} {C} a) =
  {!!}
--}

{--
subst⊨ : {Γ : Ctxt} (m : Model Γ) (f : Form Γ) (σ : FormSub Γ)
       → ((n : ℕ) → Model.vars m n ⇔ (m ⊨ σ n))
       → (m ⊨ f) ⇔ (m ⊨ substF σ f)
subst⊨ m (var n)   σ agree = agree n
subst⊨ m ⊤·        σ agree = id , id
subst⊨ m ⊥·        σ agree = id , id
subst⊨ m (A ∧· B)  σ agree =
  (λ (ha , hb) → to (subst⊨ m A σ agree) ha , to (subst⊨ m B σ agree) hb) ,
  (λ (ha , hb) → from (subst⊨ m A σ agree) ha , from (subst⊨ m B σ agree) hb)
subst⊨ m (A ∨· B)  σ agree =
  Data.Sum.map (to (subst⊨ m A σ agree)) (to (subst⊨ m B σ agree)) ,
  Data.Sum.map (from (subst⊨ m A σ agree)) (from (subst⊨ m B σ agree))
subst⊨ m (A →· B)  σ agree =
  (λ h h' → to (subst⊨ m B σ agree) (h (from (subst⊨ m A σ agree) h'))) ,
  (λ h h' → from (subst⊨ m B σ agree) (h (to (subst⊨ m A σ agree) h')))
--}

↑ᵣ₀-↑ᵣ≡ : (Γ Δ : Ctxt) (v : 𝕍) (e : Δ ≡ Γ) (r : Res Γ)
        → ↑ᵣ₀ {Δ} {v} (↑ᵣ (≡-to-⊆ (sym e)) r)
        ≡ ↑ᵣ (≡-to-⊆ (sym (cong (λ z → z ، v) e))) (↑ᵣ₀ {Γ} {v} r)
↑ᵣ₀-↑ᵣ≡ Γ .Γ v refl r =
  trans (cong (↑ᵣ₀ {Γ} {v}) (↑ᵣ⊆-refl r))
        (sym (↑ᵣ⊆-refl (↑ᵣ₀ {Γ} {v} r)))

-- The de Bruijn-zero resource variable is fixed by the coercion.
𝕣₀-↑ᵣ≡ : (Γ Δ : Ctxt) (e : Δ ≡ Γ)
       → ↑ᵣ (≡-to-⊆ (sym (cong (λ z → z ، 𝕍ℝ) e))) (𝕣₀ {Γ}) ≡ 𝕣₀ {Δ}
𝕣₀-↑ᵣ≡ Γ .Γ refl = ↑ᵣ⊆-refl (𝕣₀ {Γ})

{-- Retired: subst-⊢ (function substitutions) is superseded by subst-⊢⋆ and
-- has no case for ＦI.
subst-⊢ : (σ : FormSub₀) {Δ : ℂ₀} {r : ℂCE Δ} {C : ℂForm Δ}
        → ⊢ (seq Δ r C)
        → ⊢ (seq (substCtxt σ Δ)
                 (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) r)
                 (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) C)))
subst-⊢ σ {Δ} {r} {C} (ax x)          = ax (subst-Ax σ x)
subst-⊢ σ {Δ} {r} {C} ⊤I              = ⊤I
subst-⊢ σ {Δ} {r} {C} (∧I h h₁)       = ∧I (subst-⊢ σ h) (subst-⊢ σ h₁)
subst-⊢ σ {Δ} {r} {C} (∨Iₗ h)         = ∨Iₗ (subst-⊢ σ h)
subst-⊢ σ {Δ} {r} {C} (∨Iᵣ h)         = ∨Iᵣ (subst-⊢ σ h)
subst-⊢ σ {Δ} {CEr r} {C} (→I h)      = →I (subst-⊢ σ h)
subst-⊢ σ {Δ} {CEr r} {C} (ＯI h₁ h₂) = ＯI (subst-⊢ σ h₁) (subst-⊢ σ h₂)
subst-⊢ σ {Δ} {CEr r} {C} (ＵI {.Δ} {.r} {r₁} {A} {B} h₁ h₂ h₃) =
  ＵI (subst-⊢ σ h₁) (subst-⊢ σ h₂) q
  where
  -- ------------------------------------------------------------------ names
  G : Ctxt                       -- the ambient variable context
  G = ℂtxt Δ

  Δ′ : ℂ₀                        -- the substituted ℂ-context
  Δ′ = substCtxt σ Δ

  G′ : Ctxt
  G′ = ℂtxt Δ′

  E : G′ ≡ G
  E = ℂtxt-substCtxt σ Δ

  ρ : G ⊆ G′                     -- the coercion used by subst-⊢'s conclusion
  ρ = ≡-to-⊆ (sym E)

  ρ₁ : (G ، 𝕍ℝ) ⊆ (G′ ، 𝕍ℝ)     -- its shift under the ℂv binder.  This is
  ρ₁ = ≡-to-⊆ (sym (cong (λ z → z ، 𝕍ℝ) E))
                                 -- *definitionally* the coercion arising from
                                 -- ℂtxt-substCtxt σ (ℂv Δ 𝕍ℝ).

  σA : Form G
  σA = substF (↑FormSub (ℂtxt⊆ Δ) σ) A

  -- The third premise's context.  Note ℂtxt Θ = G ، 𝕍ℝ, and
  -- ℂtxt-substCtxt σ Θ reduces to cong (λ z → z ، 𝕍ℝ) E, because the two
  -- ℂx-clauses of ℂtxt-substCtxt are identities.
  Θ : ℂ₀
  Θ = ℂu (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊏ ↑ᵣ₀ r₁)

  -- --------------------------------------------------------- induction step
  p : ⊢ (seq (substCtxt σ Θ)
             (↑CE≡ (sym (ℂtxt-substCtxt σ Θ)) (CEr 𝕣₀))
             (↑≡ (sym (ℂtxt-substCtxt σ Θ))
                 (substF (↑FormSub (ℂtxt⊆ Θ) σ) (↑₀ A))))
  p = subst-⊢ σ h₃

  -- --------------------------------------------------------- the family
  -- ℂtxt (ℂx c f a) = ℂtxt c, so H does NOT depend on f₁ f₂ : the whole thing
  -- is a plain four-argument non-dependent family and subst₄ suffices.
  -- (This is why dsubst₃ / dcong₂ ℂu is not needed.)
  H : Form (G′ ، 𝕍ℝ) → Form (G′ ، 𝕍ℝ) → CE (G′ ، 𝕍ℝ) → Form (G′ ، 𝕍ℝ) → Set₂
  H f₁ f₂ t D = ⊢ (seq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) f₁) f₂) t D)

  -- --------------------------------------------------------- obligations
  b : ↑ᵣ ρ₁ (𝕣₀ {G}) ≡ 𝕣₀ {G′}
  b = 𝕣₀-↑ᵣ≡ G G′ E

  -- substF is the identity on _⟨ x ⟩_ (and _⊑_ = _⟨ LE ⟩_, _⊏_ = _⟨ LT ⟩_),
  -- so the two decorating formulas are pure Res-arithmetic.
  e₁ : (↑ᵣ ρ₁ (↑ᵣ₀ r) ⊑ ↑ᵣ ρ₁ (𝕣₀ {G}))
     ≡ (↑ᵣ₀ (↑ᵣ ρ r) ⊑ 𝕣₀)
  e₁ = cong₂ _⊑_ (sym (↑ᵣ₀-↑ᵣ≡ G G′ 𝕍ℝ E r)) b

  e₂ : (↑ᵣ ρ₁ (𝕣₀ {G}) ⊏ ↑ᵣ ρ₁ (↑ᵣ₀ r₁))
     ≡ (𝕣₀ ⊏ ↑ᵣ₀ (↑ᵣ ρ r₁))
  e₂ = cong₂ _⊏_ b (sym (↑ᵣ₀-↑ᵣ≡ G G′ 𝕍ℝ E r₁))

  e₃ : CEr (↑ᵣ ρ₁ (𝕣₀ {G})) ≡ CEr (𝕣₀ {G′})
  e₃ = cong CEr b

  -- substF commutes with ↑₀.  Φ = ⟨⟩, so the side condition is vacuous.
  -- g must be `ℂtxt⊆ Θ` (definitionally ⊆-trans (ℂtxt⊆ Δ) ⊆₀) and h must be
  -- `ℂtxt⊆ Δ`, so that the result matches the shape produced by p.
  eqSub : substF (↑FormSub (ℂtxt⊆ Θ) σ) (↑₀ A) ≡ ↑₀ σA
  eqSub = substF↑ σ A ⊆₀ (ℂtxt⊆ Θ) (ℂtxt⊆ Δ) (λ z ())

  e₄ : ↑ ρ₁ (substF (↑FormSub (ℂtxt⊆ Θ) σ) (↑₀ A)) ≡ ↑₀ (↑ ρ σA)
  e₄ = trans (cong (↑ ρ₁) eqSub)
             (sym (↑₀-↑≡ G G′ 𝕍ℝ E σA))

  -- --------------------------------------------------------- conclusion
  q : ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) (↑ᵣ₀ (↑ᵣ ρ r) ⊑ 𝕣₀))
                  (𝕣₀ ⊏ ↑ᵣ₀ (↑ᵣ ρ r₁)))
              𝕣₀
              (↑₀ (↑ ρ σA)))
  q = subst₄ H e₁ e₂ e₃ e₄ p

subst-⊢ σ {Δ} {r} {C} (⊥L pt p) =
  ⊥L (pointCE-↑CE _ pt) (subst-Ax σ p)
subst-⊢ σ {Δ} {r} {C} (∧L p h) =
  ∧L (subst-Ax σ p) (subst-⊢ σ h)
subst-⊢ σ {Δ} {r} {C} (→L p h₁ h₂) =
  →L (subst-Ax σ p) (subst-⊢ σ h₁) (subst-⊢ σ h₂)
subst-⊢ σ {Δ} {r} {C} (∨L pt p h₁ h₂) =
  ∨L (pointCE-↑CE _ pt) (subst-Ax σ p) (subst-⊢ σ h₁) (subst-⊢ σ h₂)
subst-⊢ σ {Δ} {r} {C} (cmpR pt h) =
  cmpR (pointCE-↑CE _ pt) (subst-⊢ σ h)
--}


{--
subst-⊢ σ {Δ} {CEr r} {C} (ＵI {.Δ} {.r} {r₁} {A} {B} h₁ h₂ h₃) =
  ＵI (subst-⊢ σ h₁) (subst-⊢ σ h₂) q
  where
  p : ⊢ (seq (substCtxt σ (ℂx (ℂx (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀) CEu) (𝕣₀ ⊏ ↑ᵣ₀ r₁) CEu))
             (↑CE≡ (sym (ℂtxt-substCtxt σ (ℂx (ℂx (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀) CEu) (𝕣₀ ⊏ ↑ᵣ₀ r₁) CEu))) (CEr 𝕣₀))
             (↑≡ (sym (ℂtxt-substCtxt σ (ℂx (ℂx (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀) CEu) (𝕣₀ ⊏ ↑ᵣ₀ r₁) CEu)))
                 (substF (↑FormSub (ℂtxt⊆ (ℂx (ℂx (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀) CEu) (𝕣₀ ⊏ ↑ᵣ₀ r₁) CEu)) σ) (↑₀ A))))
  p = subst-⊢ σ h₃

  q : ⊢ (rseq (ℂu (ℂu (ℂv (substCtxt σ Δ) 𝕍ℝ) (↑ᵣ₀ (↑ᵣ (subst (_⊆_ (ℂtxt Δ)) (sym (ℂtxt-substCtxt σ Δ)) (λ {u} i → i)) r) ⊑ 𝕣₀))
                  (𝕣₀ ⊏ ↑ᵣ₀ (↑ᵣ (≡-to-⊆ (sym (ℂtxt-substCtxt σ Δ))) r₁)))
              𝕣₀
              (↑₀ (↑ (≡-to-⊆ (sym (ℂtxt-substCtxt σ Δ))) (substF (↑FormSub (ℂtxt⊆ Δ) σ) A))))
  q = dsubst₃ (λ x y z → ⊢ (seq x y z))
              (dcong₂ ℂu (dcong₂ ℂu refl {!!}) {!!})
              {!!}
              {!!}
              p
--}

-- ⊆⋆-add fixes the de Bruijn-zero resource variable.  Definitionally true --
-- app-⊆⋆ (⊆⋆-add v₁ s) v (∈Ctxt0 _) = ∈Ctxt0 _ -- so this is only stated for
-- readability; it is never needed as a rewrite.
⋆𝕣₀-add : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ)
        → ↑⋆ᵣ (⊆⋆-add 𝕍ℝ s) (𝕣₀ {Γ}) ≡ 𝕣₀ {Δ}
⋆𝕣₀-add s = refl

-- Weakening-by-⊆₀ commutes with ↑⋆ᵣ under a ⊆⋆-add binder.
-- 𝐯-leaf: both sides are 𝐯 (∈CtxtS v (app-⊆⋆ s _ i)).
⋆↑ᵣ₀-add : {Γ Δ : Ctxt} (v : 𝕍) (s : Γ ⊆⋆ Δ) (r : Res Γ)
         → ↑⋆ᵣ (⊆⋆-add v s) (↑ᵣ₀ {Γ} {v} r) ≡ ↑ᵣ₀ {Δ} {v} (↑⋆ᵣ s r)
⋆↑ᵣ₀-add v s (𝐯 i)    = refl
⋆↑ᵣ₀-add v s 𝟎        = refl
⋆↑ᵣ₀-add v s (rvar ρ)        = refl
⋆↑ᵣ₀-add v s (r ⋆ r₁) = cong₂ _⋆_ (⋆↑ᵣ₀-add v s r) (⋆↑ᵣ₀-add v s r₁)

-- The syntactic ⊆⋆₀ and the semantic ⊆₀ agree on formulas.  NOT refl:
-- ⊆⋆₀ = ⊆⋆-skip _ ⊆⋆-refl, so ⊆⋆→⊆ ⊆⋆₀ i = ∈CtxtS v (app-⊆⋆ ⊆⋆-refl _ i),
-- and the inner app-⊆⋆ has to be peeled off by app-⊆⋆-refl.
↑⋆₀-↑₀ : {Γ : Ctxt} {v : 𝕍} (f : Form Γ)
       → ↑⋆ (⊆⋆₀ {Γ} {v}) f ≡ ↑₀ {Γ} {v} f
↑⋆₀-↑₀ {Γ} {v} f =
  trans (↑-⊆⋆ ⊆⋆₀ f)
        (≡↑ f (⊆⋆→⊆ (⊆⋆₀ {Γ} {v})) (⊆₀ {Γ} {v})
             (λ {u} i → cong (∈CtxtS v) (app-⊆⋆-refl u i)))

-- Same statement one level up: ↑⋆ under a ⊆⋆-add binder commutes with ↑₀.
-- Routed through ⊆⋆→⊆ and the existing ↑-trans; both side conditions are refl
-- because app-⊆⋆ (⊆⋆-add v s) u (∈CtxtS v i) and ⊆₀ (app-⊆⋆ s u i) are both
-- ∈CtxtS v (app-⊆⋆ s u i).
⋆↑₀-add : {Γ Δ : Ctxt} (v : 𝕍) (s : Γ ⊆⋆ Δ) (f : Form Γ)
        → ↑⋆ (⊆⋆-add v s) (↑₀ {Γ} {v} f) ≡ ↑₀ {Δ} {v} (↑⋆ s f)
⋆↑₀-add {Γ} {Δ} v s f =
  trans (↑-⊆⋆ (⊆⋆-add v s) (↑₀ {Γ} {v} f))
        (trans (sym (↑-trans t (⊆₀ {Γ} {v}) (⊆⋆→⊆ (⊆⋆-add v s)) f (λ _ _ → refl)))
               (trans (↑-trans t (⊆⋆→⊆ s) (⊆₀ {Δ} {v}) f (λ _ _ → refl))
                      (cong (↑₀ {Δ} {v}) (sym (↑-⊆⋆ s f)))))
  where
  -- the common composite Γ ⊆ (Δ ، v)
  t : Γ ⊆ (Δ ، v)
  t {u} i = ∈CtxtS v (app-⊆⋆ s u i)

-- ---------------------------------------------------------------------------
-- Commutation lemmas for the ＦI case of subst-⊢⋆: syntactic lifting ↑⋆ and
-- syntactic formula substitution substF⋆ both commute with resource/term
-- substitution sub (used by subℝ).  CSubs are compared pointwise.

↑⋆u : {Γ Δ : Ctxt} (e : Γ ⊆⋆ Δ) {u : 𝕌} → C⟦𝕌⟧ Γ u → C⟦𝕌⟧ Δ u
↑⋆u e {𝕌Agent}  x = ↑⋆ᵢ e x
↑⋆u e {𝕌Agents} x = ↑⋆ₛ e x
↑⋆u e {𝕌Prop}   x = ↑⋆ₚ e x
↑⋆u e {𝕌Data}   x = ↑⋆d e x

↑⋆v : {Γ Δ : Ctxt} (e : Γ ⊆⋆ Δ) {v : 𝕍} → C⟦𝕍⟧ Γ v → C⟦𝕍⟧ Δ v
↑⋆v e {𝕍𝕌 u} x = ↑⋆u e {u} x
↑⋆v e {𝕍ℝ}   x = ↑⋆ᵣ e x

↑⋆v-CSub-var : {Γ Δ : Ctxt} (e : Γ ⊆⋆ Δ) {v : 𝕍} (i : ∈Ctxt v Γ)
             → ↑⋆v e {v} (CSub-var {Γ} {v} i) ≡ CSub-var {Δ} {v} (app-⊆⋆ e v i)
↑⋆v-CSub-var e {𝕍𝕌 𝕌Agent}  i = refl
↑⋆v-CSub-var e {𝕍𝕌 𝕌Agents} i = refl
↑⋆v-CSub-var e {𝕍𝕌 𝕌Prop}   i = refl
↑⋆v-CSub-var e {𝕍𝕌 𝕌Data}   i = refl
↑⋆v-CSub-var e {𝕍ℝ}         i = refl

-- Weakening by ⊆₀ commutes with ↑⋆ (pushed under the new binder).
↑ᵢ₀-↑⋆ᵢ : {Γ Δ : Ctxt} (u : 𝕍) (e : Γ ⊆⋆ Δ) (a : Agent Γ)
        → ↑ᵢ (⊆₀ {Δ} {u}) (↑⋆ᵢ e a) ≡ ↑⋆ᵢ (⊆⋆-add u e) (↑ᵢ ⊆₀ a)
↑ᵢ₀-↑⋆ᵢ u e (agentV i) = refl
↑ᵢ₀-↑⋆ᵢ u e (agentC x) = refl

↑ᵢₛ₀-↑⋆ᵢₛ : {Γ Δ : Ctxt} (u : 𝕍) (e : Γ ⊆⋆ Δ) (l : List (Agent Γ))
          → Data.List.map (↑ᵢ (⊆₀ {Δ} {u})) (Data.List.map (↑⋆ᵢ e) l)
          ≡ Data.List.map (↑⋆ᵢ (⊆⋆-add u e)) (Data.List.map (↑ᵢ ⊆₀) l)
↑ᵢₛ₀-↑⋆ᵢₛ u e []      = refl
↑ᵢₛ₀-↑⋆ᵢₛ u e (a ∷ l) = cong₂ _∷_ (↑ᵢ₀-↑⋆ᵢ u e a) (↑ᵢₛ₀-↑⋆ᵢₛ u e l)

↑v₀-↑⋆v : {Γ Δ : Ctxt} (u : 𝕍) (e : Γ ⊆⋆ Δ) {v : 𝕍} (x : C⟦𝕍⟧ Γ v)
        → ↑v (⊆₀ {Δ} {u}) {v} (↑⋆v e {v} x) ≡ ↑⋆v (⊆⋆-add u e) {v} (↑v (⊆₀ {Γ} {u}) {v} x)
↑v₀-↑⋆v u e {𝕍𝕌 𝕌Agent}  x = ↑ᵢ₀-↑⋆ᵢ u e x
↑v₀-↑⋆v u e {𝕍𝕌 𝕌Agents} (agentsV i) = refl
↑v₀-↑⋆v u e {𝕍𝕌 𝕌Agents} (agentsL l) = cong agentsL (↑ᵢₛ₀-↑⋆ᵢₛ u e l)
↑v₀-↑⋆v u e {𝕍𝕌 𝕌Prop}   (atomPropV i) = refl
↑v₀-↑⋆v u e {𝕍𝕌 𝕌Prop}   (atomPropC x) = refl
↑v₀-↑⋆v u e {𝕍𝕌 𝕌Data}   (dataV i) = refl
↑v₀-↑⋆v u e {𝕍𝕌 𝕌Data}   (dataC x) = refl
↑v₀-↑⋆v {Γ} {Δ} u e {𝕍ℝ} x = ↑ᵣ₀-↑⋆ᵣ x
  where
  ↑ᵣ₀-↑⋆ᵣ : (r : Res Γ) → ↑ᵣ (⊆₀ {Δ} {u}) (↑⋆ᵣ e r) ≡ ↑⋆ᵣ (⊆⋆-add u e) (↑ᵣ ⊆₀ r)
  ↑ᵣ₀-↑⋆ᵣ (𝐯 i)   = refl
  ↑ᵣ₀-↑⋆ᵣ 𝟎       = refl
  ↑ᵣ₀-↑⋆ᵣ (rvar ρ)       = refl
  ↑ᵣ₀-↑⋆ᵣ (r ⋆ s) = cong₂ _⋆_ (↑ᵣ₀-↑⋆ᵣ r) (↑ᵣ₀-↑⋆ᵣ s)

-- The ⊆₀ weakening and its syntactic counterpart ⊆⋆₀ agree on values.
↑v₀-↑⋆v₀ : {Γ : Ctxt} (u : 𝕍) {v : 𝕍} (x : C⟦𝕍⟧ Γ v)
         → ↑v (⊆₀ {Γ} {u}) {v} x ≡ ↑⋆v (⊆⋆₀ {Γ} {u}) {v} x
↑v₀-↑⋆v₀ u {𝕍𝕌 𝕌Agent} (agentV i) = cong (λ z → agentV (∈CtxtS u z)) (sym (app-⊆⋆-refl _ i))
↑v₀-↑⋆v₀ u {𝕍𝕌 𝕌Agent} (agentC x) = refl
↑v₀-↑⋆v₀ {Γ} u {𝕍𝕌 𝕌Agents} (agentsV i) = cong (λ z → agentsV (∈CtxtS u z)) (sym (app-⊆⋆-refl _ i))
↑v₀-↑⋆v₀ {Γ} u {𝕍𝕌 𝕌Agents} (agentsL l) = cong agentsL (go l)
  where
  go : (l : List (Agent Γ)) → Data.List.map (↑ᵢ ⊆₀) l ≡ Data.List.map (↑⋆ᵢ (⊆⋆₀ {Γ} {u})) l
  go []      = refl
  go (agentV i ∷ l) = cong₂ _∷_ (cong (λ z → agentV (∈CtxtS u z)) (sym (app-⊆⋆-refl _ i))) (go l)
  go (agentC x ∷ l) = cong₂ _∷_ refl (go l)
↑v₀-↑⋆v₀ u {𝕍𝕌 𝕌Prop} (atomPropV i) = cong (λ z → atomPropV (∈CtxtS u z)) (sym (app-⊆⋆-refl _ i))
↑v₀-↑⋆v₀ u {𝕍𝕌 𝕌Prop} (atomPropC x) = refl
↑v₀-↑⋆v₀ u {𝕍𝕌 𝕌Data} (dataV i) = cong (λ z → dataV (∈CtxtS u z)) (sym (app-⊆⋆-refl _ i))
↑v₀-↑⋆v₀ u {𝕍𝕌 𝕌Data} (dataC x) = refl
↑v₀-↑⋆v₀ {Γ} u {𝕍ℝ} x = go x
  where
  go : (r : Res Γ) → ↑ᵣ ⊆₀ r ≡ ↑⋆ᵣ ⊆⋆₀ r
  go (𝐯 i)   = cong (λ z → 𝐯 (∈CtxtS u z)) (sym (app-⊆⋆-refl _ i))
  go 𝟎       = refl
  go (rvar ρ)       = refl
  go (r ⋆ s) = cong₂ _⋆_ (go r) (go s)

-- ↑⋆ commutes with sub, given compatible substitutions.
module _ {Γ Γ′ Δ Δ′ : Ctxt} (e′ : Γ ⊆⋆ Γ′) (e : Δ ⊆⋆ Δ′)
         (c : CSub Γ Δ) (c′ : CSub Γ′ Δ′)
         (H : {v : 𝕍} (i : ∈Ctxt v Γ) → c′ {v} (app-⊆⋆ e′ v i) ≡ ↑⋆v e {v} (c {v} i)) where

  ↑⋆-subAgent : (a : Agent Γ) → ↑⋆ᵢ e (sub-Agent a c) ≡ sub-Agent (↑⋆ᵢ e′ a) c′
  ↑⋆-subAgent (agentV i) = sym (H i)
  ↑⋆-subAgent (agentC x) = refl

  ↑⋆-subAgentL : (l : List (Agent Γ))
               → Data.List.map (↑⋆ᵢ e) (Data.List.map (λ x → sub-Agent x c) l)
               ≡ Data.List.map (λ x → sub-Agent x c′) (Data.List.map (↑⋆ᵢ e′) l)
  ↑⋆-subAgentL []      = refl
  ↑⋆-subAgentL (a ∷ l) = cong₂ _∷_ (↑⋆-subAgent a) (↑⋆-subAgentL l)

  ↑⋆-subAgents : (a : Agents Γ) → ↑⋆ₛ e (sub-Agents a c) ≡ sub-Agents (↑⋆ₛ e′ a) c′
  ↑⋆-subAgents (agentsV i) = sym (H i)
  ↑⋆-subAgents (agentsL l) = cong agentsL (↑⋆-subAgentL l)

  ↑⋆-subAtomProp : (a : AtomProp Γ) → ↑⋆ₚ e (sub-AtomProp a c) ≡ sub-AtomProp (↑⋆ₚ e′ a) c′
  ↑⋆-subAtomProp (atomPropV i) = sym (H i)
  ↑⋆-subAtomProp (atomPropC x) = refl

  ↑⋆-subData : (a : Data Γ) → ↑⋆d e (sub-Data a c) ≡ sub-Data (↑⋆d e′ a) c′
  ↑⋆-subData (dataV i) = sym (H i)
  ↑⋆-subData (dataC x) = refl

  ↑⋆-subAtom : (a : Atom Γ) → ↑⋆ₐ e (sub-Atom a c) ≡ sub-Atom (↑⋆ₐ e′ a) c′
  ↑⋆-subAtom (atProp x) = cong atProp (↑⋆-subAtomProp x)
  ↑⋆-subAtom (atAction (ActSend p a A)) =
    cong atAction (cong₃ ActSend (↑⋆-subData p) (↑⋆-subAgent a) (↑⋆-subAgents A))
  ↑⋆-subAtom (atEvent (EvtReceive p a b)) =
    cong atEvent (cong₃ EvtReceive (↑⋆-subData p) (↑⋆-subAgent a) (↑⋆-subAgent b))
  ↑⋆-subAtom (atEvent (EvtInternal a d)) =
    cong atEvent (cong₂ EvtInternal (↑⋆-subAgent a) (↑⋆-subData d))
  ↑⋆-subAtom (atCorrect (FaultCorrect a b)) =
    cong atCorrect (cong₂ FaultCorrect (↑⋆-subAgent a) (↑⋆-subAgent b))

  ↑⋆-subRes : (r : Res Γ) → ↑⋆ᵣ e (sub-Res r c) ≡ sub-Res (↑⋆ᵣ e′ r) c′
  ↑⋆-subRes (𝐯 i)   = sym (H i)
  ↑⋆-subRes 𝟎       = refl
  ↑⋆-subRes (rvar ρ)       = refl
  ↑⋆-subRes (r ⋆ s) = cong₂ _⋆_ (↑⋆-subRes r) (↑⋆-subRes s)

  ↑⋆-subSetAtom : (A : SetAtom Γ) → ↑⋆A e (sub-SetAtom A c) ≡ sub-SetAtom (↑⋆A e′ A) c′
  ↑⋆-subSetAtom (a ∈ₐ A)     = cong₂ _∈ₐ_ (↑⋆-subAgent a) (↑⋆-subAgents A)
  ↑⋆-subSetAtom (∣ A ∣ₛ＝ n) = cong (λ z → ∣ z ∣ₛ＝ n) (↑⋆-subAgents A)

-- H is preserved when going under a binder.
H-add : {Γ Γ′ Δ Δ′ : Ctxt} (e′ : Γ ⊆⋆ Γ′) (e : Δ ⊆⋆ Δ′)
        (c : CSub Γ Δ) (c′ : CSub Γ′ Δ′)
        (H : {v : 𝕍} (i : ∈Ctxt v Γ) → c′ {v} (app-⊆⋆ e′ v i) ≡ ↑⋆v e {v} (c {v} i))
        (u : 𝕍) {v : 𝕍} (i : ∈Ctxt v (Γ ، u))
      → CSub، u c′ {v} (app-⊆⋆ (⊆⋆-add u e′) v i) ≡ ↑⋆v (⊆⋆-add u e) {v} (CSub، u c {v} i)
H-add e′ e c c′ H u {.u} (∈Ctxt0 _)   = sym (↑⋆v-CSub-var (⊆⋆-add u e) {u} (∈Ctxt0 _))
H-add e′ e c c′ H u {v}  (∈CtxtS .u i) =
  trans (cong (↑v ⊆₀ {v}) (H {v} i)) (↑v₀-↑⋆v u e {v} (c {v} i))

↑⋆-sub : {Γ Γ′ Δ Δ′ : Ctxt} (e′ : Γ ⊆⋆ Γ′) (e : Δ ⊆⋆ Δ′)
         (c : CSub Γ Δ) (c′ : CSub Γ′ Δ′)
         (H : {v : 𝕍} (i : ∈Ctxt v Γ) → c′ {v} (app-⊆⋆ e′ v i) ≡ ↑⋆v e {v} (c {v} i))
         (f : Form Γ)
       → ↑⋆ e (sub f c) ≡ sub (↑⋆ e′ f) c′
↑⋆-sub e′ e c c′ H (𝕒 x)         = cong 𝕒 (↑⋆-subAtom e′ e c c′ H x)
↑⋆-sub e′ e c c′ H (var x)       = refl
↑⋆-sub e′ e c c′ H ⊤·            = refl
↑⋆-sub e′ e c c′ H ⊥·            = refl
↑⋆-sub e′ e c c′ H (f ∧· g)      = cong₂ _∧·_ (↑⋆-sub e′ e c c′ H f) (↑⋆-sub e′ e c c′ H g)
↑⋆-sub e′ e c c′ H (f ∨· g)      = cong₂ _∨·_ (↑⋆-sub e′ e c c′ H f) (↑⋆-sub e′ e c c′ H g)
↑⋆-sub e′ e c c′ H (f →· g)      = cong₂ _→·_ (↑⋆-sub e′ e c c′ H f) (↑⋆-sub e′ e c c′ H g)
↑⋆-sub e′ e c c′ H (∀· u f)      =
  cong (∀· u) (↑⋆-sub (⊆⋆-add _ e′) (⊆⋆-add _ e) (CSub، _ c) (CSub، _ c′) (H-add e′ e c c′ H _) f)
↑⋆-sub e′ e c c′ H (∃· u f)      =
  cong (∃· u) (↑⋆-sub (⊆⋆-add _ e′) (⊆⋆-add _ e) (CSub، _ c) (CSub، _ c′) (H-add e′ e c c′ H _) f)
↑⋆-sub e′ e c c′ H (𝔸 A)         = cong 𝔸 (↑⋆-subSetAtom e′ e c c′ H A)
↑⋆-sub e′ e c c′ H (f Ｕ g)      = cong₂ _Ｕ_ (↑⋆-sub e′ e c c′ H f) (↑⋆-sub e′ e c c′ H g)
↑⋆-sub e′ e c c′ H (Ｏ f)        = cong Ｏ (↑⋆-sub e′ e c c′ H f)
↑⋆-sub e′ e c c′ H (f Ｓ g)      = cong₂ _Ｓ_ (↑⋆-sub e′ e c c′ H f) (↑⋆-sub e′ e c c′ H g)
↑⋆-sub e′ e c c′ H (Ｙ f)        = cong Ｙ (↑⋆-sub e′ e c c′ H f)
↑⋆-sub e′ e c c′ H (Ｂ f)        = cong Ｂ (↑⋆-sub e′ e c c′ H f)
↑⋆-sub e′ e c c′ H (Ｆ f)        =
  cong Ｆ_ (↑⋆-sub (⊆⋆-add _ e′) (⊆⋆-add _ e) (CSub، _ c) (CSub، _ c′) (H-add e′ e c c′ H _) f)
↑⋆-sub e′ e c c′ H (t₁ ⟨ k ⟩ t₂) =
  cong₂ (λ a b → a ⟨ k ⟩ b) (↑⋆-subRes e′ e c c′ H t₁) (↑⋆-subRes e′ e c c′ H t₂)

-- sub after a ⊆⋆₀ weakening, under a matching CSub، .
sub-↑⋆₀ : {Γ Δ : Ctxt} (u : 𝕍) (c : CSub Γ Δ) (X : Form Γ)
        → sub (↑⋆ (⊆⋆₀ {Γ} {u}) X) (CSub، u c) ≡ ↑⋆ (⊆⋆₀ {Δ} {u}) (sub X c)
sub-↑⋆₀ {Γ} {Δ} u c X =
  sym (↑⋆-sub ⊆⋆₀ ⊆⋆₀ c (CSub، u c)
              (λ {v} i → trans (cong (λ z → ↑v ⊆₀ {v} (c {v} z)) (app-⊆⋆-refl v i))
                               (↑v₀-↑⋆v₀ u {v} (c {v} i)))
              X)

app-FormSub⋆، : {Γ : Ctxt} (u : 𝕍) (x : FormVar) (σ : FormSub⋆ Γ)
              → app-FormSub⋆ x (FormSub⋆، Γ u σ) ≡ ↑⋆ ⊆⋆₀ (app-FormSub⋆ x σ)
app-FormSub⋆، u x ● = refl
app-FormSub⋆، u x (y ↦ f ⨾ σ) with x ≟ y
... | yes refl = refl
... | no _     = app-FormSub⋆، u x σ

-- substF⋆ commutes with sub, given compatible formula substitutions.
-- The compatibility hypothesis of substF⋆-sub is preserved under a binder.
K-add : {Γ Δ : Ctxt} (τ′ : FormSub⋆ Γ) (τ : FormSub⋆ Δ) (c : CSub Γ Δ)
        (K : (x : FormVar) → sub (app-FormSub⋆ x τ′) c ≡ app-FormSub⋆ x τ)
        (u : 𝕍) (x : FormVar)
      → sub (app-FormSub⋆ x (FormSub⋆، Γ u τ′)) (CSub، u c) ≡ app-FormSub⋆ x (FormSub⋆، Δ u τ)
K-add τ′ τ c K u x =
  trans (cong (λ z → sub z (CSub، u c)) (app-FormSub⋆، u x τ′))
        (trans (sub-↑⋆₀ u c (app-FormSub⋆ x τ′))
               (trans (cong (↑⋆ ⊆⋆₀) (K x)) (sym (app-FormSub⋆، u x τ))))

substF⋆-sub : {Γ Δ : Ctxt} (τ′ : FormSub⋆ Γ) (τ : FormSub⋆ Δ) (c : CSub Γ Δ)
              (K : (x : FormVar) → sub (app-FormSub⋆ x τ′) c ≡ app-FormSub⋆ x τ)
              (f : Form Γ)
            → substF⋆ τ (sub f c) ≡ sub (substF⋆ τ′ f) c
substF⋆-sub τ′ τ c K (𝕒 x)    = refl
substF⋆-sub τ′ τ c K (var x)  = sym (K x)
substF⋆-sub τ′ τ c K ⊤·       = refl
substF⋆-sub τ′ τ c K ⊥·       = refl
substF⋆-sub τ′ τ c K (f ∧· g) = cong₂ _∧·_ (substF⋆-sub τ′ τ c K f) (substF⋆-sub τ′ τ c K g)
substF⋆-sub τ′ τ c K (f ∨· g) = cong₂ _∨·_ (substF⋆-sub τ′ τ c K f) (substF⋆-sub τ′ τ c K g)
substF⋆-sub τ′ τ c K (f →· g) = cong₂ _→·_ (substF⋆-sub τ′ τ c K f) (substF⋆-sub τ′ τ c K g)
substF⋆-sub τ′ τ c K (∀· u f) = cong (∀· u) (substF⋆-sub _ _ (CSub، _ c) (K-add τ′ τ c K _) f)
substF⋆-sub τ′ τ c K (∃· u f) = cong (∃· u) (substF⋆-sub _ _ (CSub، _ c) (K-add τ′ τ c K _) f)
substF⋆-sub τ′ τ c K (𝔸 A)    = refl
substF⋆-sub τ′ τ c K (f Ｕ g) = cong₂ _Ｕ_ (substF⋆-sub τ′ τ c K f) (substF⋆-sub τ′ τ c K g)
substF⋆-sub τ′ τ c K (Ｏ f)   = cong Ｏ (substF⋆-sub τ′ τ c K f)
substF⋆-sub τ′ τ c K (f Ｓ g) = cong₂ _Ｓ_ (substF⋆-sub τ′ τ c K f) (substF⋆-sub τ′ τ c K g)
substF⋆-sub τ′ τ c K (Ｙ f)   = cong Ｙ (substF⋆-sub τ′ τ c K f)
substF⋆-sub τ′ τ c K (Ｂ f)   = cong Ｂ (substF⋆-sub τ′ τ c K f)
substF⋆-sub τ′ τ c K (Ｆ f)   = cong Ｆ_ (substF⋆-sub _ _ (CSub، _ c) (K-add τ′ τ c K _) f)
substF⋆-sub τ′ τ c K (t₁ ⟨ k ⟩ t₂) = refl

subst-⊢⋆ : (σ : FormSub⋆₀) {Δ : ℂ₀} {r : ℂCE Δ} {C : ℂForm Δ}
         → ⊢ (seq Δ r C)
         → ⊢ (seq (substCtxt⋆ σ Δ)
                  (↑⋆CE (ℂtxt-substCtxt⋆ σ Δ) r)
                  (↑⋆ (ℂtxt-substCtxt⋆ σ Δ) (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Δ) σ) C)))
subst-⊢⋆ σ {Δ} {r} {C} (ax x) = ax (subst-Ax⋆ σ x)
subst-⊢⋆ σ {Δ} {r} {C} ⊤I = ⊤I
subst-⊢⋆ σ {Δ} {r} {C} (∧I h h₁) = ∧I (subst-⊢⋆ σ h) (subst-⊢⋆ σ h₁)
subst-⊢⋆ σ {Δ} {r} {C} (∨Iₗ h) = ∨Iₗ (subst-⊢⋆ σ h)
subst-⊢⋆ σ {Δ} {r} {C} (∨Iᵣ h) = ∨Iᵣ (subst-⊢⋆ σ h)
subst-⊢⋆ σ {Δ} {r} {C} (→I h) = →I (subst-⊢⋆ σ h)
subst-⊢⋆ σ {Δ} {r} {C} (ＯI h₁ h₂) = ＯI (subst-⊢⋆ σ h₁) (subst-⊢⋆ σ h₂)
subst-⊢⋆ σ {Δ} {CEr r} {C} (ＵI {.Δ} {.r} {r₁} {A} {B} h₁ h₂ h₃) =
  ＵI (subst-⊢⋆ σ h₁) (subst-⊢⋆ σ h₂) q
  where
  -- ------------------------------------------------------------------ names
  G : Ctxt                          -- ambient variable context
  G = ℂtxt Δ

  Δ′ : ℂ₀                           -- the substituted ℂ-context
  Δ′ = substCtxt⋆ σ Δ

  G′ : Ctxt
  G′ = ℂtxt Δ′

  s : G ⊆⋆ G′                       -- the witness used by subst-⊢⋆'s conclusion
  s = ℂtxt-substCtxt⋆ σ Δ

  s₁ : (G ، 𝕍ℝ) ⊆⋆ (G′ ، 𝕍ℝ)       -- its shift under the ℂv binder.  This is
  s₁ = ⊆⋆-add 𝕍ℝ s
       -- *definitionally* ℂtxt-substCtxt⋆ σ Θ, because the two ℂx-clauses of
       -- ℂtxt-substCtxt⋆ are identities and the ℂv-clause is ⊆⋆-add.

  σA : Form G
  σA = substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Δ) σ) A

  -- The third premise's context.  ℂtxt Θ = G ، 𝕍ℝ.
  Θ : ℂ₀
  Θ = ℂu (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊏ ↑ᵣ₀ r₁)

  -- --------------------------------------------------------- induction step
  -- substCtxt⋆ σ Θ reduces to ℂu (ℂu (ℂv Δ′ 𝕍ℝ) _) _, and ↑⋆CE s₁ (CEr 𝕣₀)
  -- reduces to CEr 𝕣₀, so p is already at the shape H wants.
  p : ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) (↑⋆ᵣ s₁ (↑ᵣ₀ r) ⊑ 𝕣₀))
                  (𝕣₀ ⊏ ↑⋆ᵣ s₁ (↑ᵣ₀ r₁)))
              𝕣₀
              (↑⋆ s₁ (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Θ) σ) (↑₀ A))))
  p = subst-⊢⋆ σ h₃

  -- --------------------------------------------------------- the family
  -- ℂtxt (ℂx c f a) = ℂtxt c, so H does not depend on f₁ f₂ : this is a plain
  -- three-argument non-dependent family and subst₃ suffices.  (No dsubst₃.)
  H : Form (G′ ، 𝕍ℝ) → Form (G′ ، 𝕍ℝ) → Form (G′ ، 𝕍ℝ) → Set₂
  H f₁ f₂ D = ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) f₁) f₂) 𝕣₀ D)

  -- --------------------------------------------------------- obligations
  -- substF⋆ is the identity on _⟨ x ⟩_ (and _⊑_ = _⟨ LE ⟩_, _⊏_ = _⟨ LT ⟩_),
  -- so the two decorating formulas are pure Res-arithmetic.  The 𝕣₀ halves
  -- need no rewriting at all (⋆𝕣₀-add is refl), hence the bare cong.
  e₁ : (↑⋆ᵣ s₁ (↑ᵣ₀ r) ⊑ 𝕣₀) ≡ (↑ᵣ₀ (↑⋆ᵣ s r) ⊑ 𝕣₀)
  e₁ = cong (λ z → z ⊑ 𝕣₀) (⋆↑ᵣ₀-add 𝕍ℝ s r)

  e₂ : (𝕣₀ ⊏ ↑⋆ᵣ s₁ (↑ᵣ₀ r₁)) ≡ (𝕣₀ ⊏ ↑ᵣ₀ (↑⋆ᵣ s r₁))
  e₂ = cong (λ z → 𝕣₀ ⊏ z) (⋆↑ᵣ₀-add 𝕍ℝ s r₁)

  -- substF⋆ commutes with ↑₀.  Φ = ⟨⟩, so the side condition is vacuous.
  -- The two ↑⋆₀-↑₀ rewrites convert between the ⊆⋆₀ that substF⋆↑ is phrased
  -- with and the semantic ⊆₀ that ＵI's third premise actually uses.
  eqSub : substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Θ) σ) (↑₀ A) ≡ ↑₀ σA
  eqSub =
    trans (sym (cong (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Θ) σ)) (↑⋆₀-↑₀ A)))
          (trans (substF⋆↑⋆ σ A ⊆⋆₀ (ℂtxt⊆⋆ Θ) (ℂtxt⊆⋆ Δ) (λ z ()))
                 (↑⋆₀-↑₀ σA))

  e₃ : ↑⋆ s₁ (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Θ) σ) (↑₀ A)) ≡ ↑₀ (↑⋆ s σA)
  e₃ = trans (cong (↑⋆ s₁) eqSub)
             (⋆↑₀-add 𝕍ℝ s σA)

  -- --------------------------------------------------------- conclusion
  q : ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) (↑ᵣ₀ (↑⋆ᵣ s r) ⊑ 𝕣₀))
                  (𝕣₀ ⊏ ↑ᵣ₀ (↑⋆ᵣ s r₁)))
              𝕣₀
              (↑₀ (↑⋆ s σA)))
  q = subst₃ H e₁ e₂ e₃ p

subst-⊢⋆ σ {Δ} {r} {C} (⊥L pt p) =
  ⊥L (pointCE-↑⋆CE _ pt) (subst-Ax⋆ σ p)
subst-⊢⋆ σ {Δ} {r} {C} (∧L p h) =
  ∧L (subst-Ax⋆ σ p) (subst-⊢⋆ σ h)
subst-⊢⋆ σ {Δ} {r} {C} (→L p h₁ h₂) =
  →L (subst-Ax⋆ σ p) (subst-⊢⋆ σ h₁) (subst-⊢⋆ σ h₂)
subst-⊢⋆ σ {Δ} {r} {C} (∨L pt p h₁ h₂) =
  ∨L (pointCE-↑⋆CE _ pt) (subst-Ax⋆ σ p) (subst-⊢⋆ σ h₁) (subst-⊢⋆ σ h₂)
subst-⊢⋆ σ {Δ} {r} {C} (cmpR pt h) =
  cmpR (pointCE-↑⋆CE _ pt) (subst-⊢⋆ σ h)
subst-⊢⋆ σ {Δ} {CEr r} {C} (ＦI {.Δ} {.r} {A} h) =
  ＦI (subst (λ X → ⊢ (rseq (substCtxt⋆ σ Δ) (↑⋆ᵣ s r) X)) eq (subst-⊢⋆ σ h))
  where
  s : ℂtxt Δ ⊆⋆ ℂtxt (substCtxt⋆ σ Δ)
  s = ℂtxt-substCtxt⋆ σ Δ

  σΔ : FormSub⋆ (ℂtxt Δ)
  σΔ = ↑FormSub⋆ (ℂtxt⊆⋆ Δ) σ

  K : (x : FormVar) → sub (app-FormSub⋆ x (FormSub⋆، _ 𝕍ℝ σΔ)) (CSub،ₗ r) ≡ app-FormSub⋆ x σΔ
  K x = trans (cong (λ z → sub z (CSub،ₗ r)) (app-FormSub⋆، 𝕍ℝ x σΔ))
              (trans (cong (λ z → sub z (CSub،ₗ r)) (↑⋆₀-↑₀ (app-FormSub⋆ x σΔ)))
                     (sub-↑₀ (ℂtxt Δ) 𝕍ℝ r (app-FormSub⋆ x σΔ)))

  H : {v : 𝕍} (i : ∈Ctxt v (ℂtxt Δ ، 𝕍ℝ))
    → CSub،ₗ {_} {𝕍ℝ} (↑⋆ᵣ s r) {v} (app-⊆⋆ (⊆⋆-add 𝕍ℝ s) v i)
    ≡ ↑⋆v s {v} (CSub،ₗ {_} {𝕍ℝ} r {v} i)
  H {.𝕍ℝ} (∈Ctxt0 _)       = refl
  H {v}   (∈CtxtS .𝕍ℝ i) = sym (↑⋆v-CSub-var s {v} i)

  eq : ↑⋆ s (substF⋆ σΔ (subℝ A r))
     ≡ subℝ (↑⋆ (⊆⋆-add 𝕍ℝ s) (substF⋆ (FormSub⋆، _ 𝕍ℝ σΔ) A)) (↑⋆ᵣ s r)
  eq = trans (cong (↑⋆ s) (substF⋆-sub (FormSub⋆، _ 𝕍ℝ σΔ) σΔ (CSub،ₗ r) K A))
             (↑⋆-sub (⊆⋆-add 𝕍ℝ s) s (CSub،ₗ r) (CSub،ₗ (↑⋆ᵣ s r)) H
                     (substF⋆ (FormSub⋆، _ 𝕍ℝ σΔ) A))

-- ---------------------------------------------------------------------------
-- subst-⊢⋆ for closed sequents, with a clean conclusion.
--
-- At Δ = ℂ⟨⟩ every lift in subst-⊢⋆'s conclusion is by ⊆⋆-refl, which is an
-- identity that does not compute on a variable formula A.  The lemmas below
-- show it is propositionally the identity.  Note that ⊆⋆، u ⊆⋆-refl is
-- definitionally ⊆⋆-refl, so the binder cases are plain induction.

↑⋆ᵢ-refl : {Γ : Ctxt} (a : Agent Γ) → ↑⋆ᵢ ⊆⋆-refl a ≡ a
↑⋆ᵢ-refl (agentV i) = cong agentV (app-⊆⋆-refl _ i)
↑⋆ᵢ-refl (agentC x) = refl

↑⋆ᵢₛ-refl : {Γ : Ctxt} (l : List (Agent Γ)) → Data.List.map (↑⋆ᵢ ⊆⋆-refl) l ≡ l
↑⋆ᵢₛ-refl []      = refl
↑⋆ᵢₛ-refl (a ∷ l) = cong₂ _∷_ (↑⋆ᵢ-refl a) (↑⋆ᵢₛ-refl l)

↑⋆ₛ-refl : {Γ : Ctxt} (a : Agents Γ) → ↑⋆ₛ ⊆⋆-refl a ≡ a
↑⋆ₛ-refl (agentsV i) = cong agentsV (app-⊆⋆-refl _ i)
↑⋆ₛ-refl (agentsL l) = cong agentsL (↑⋆ᵢₛ-refl l)

↑⋆ₚ-refl : {Γ : Ctxt} (a : AtomProp Γ) → ↑⋆ₚ ⊆⋆-refl a ≡ a
↑⋆ₚ-refl (atomPropV i) = cong atomPropV (app-⊆⋆-refl _ i)
↑⋆ₚ-refl (atomPropC x) = refl

↑⋆d-refl : {Γ : Ctxt} (a : Data Γ) → ↑⋆d ⊆⋆-refl a ≡ a
↑⋆d-refl (dataV i) = cong dataV (app-⊆⋆-refl _ i)
↑⋆d-refl (dataC x) = refl

↑⋆ₜ-refl : {Γ : Ctxt} (a : Action Γ) → ↑⋆ₜ ⊆⋆-refl a ≡ a
↑⋆ₜ-refl (ActSend p a A) = cong₃ ActSend (↑⋆d-refl p) (↑⋆ᵢ-refl a) (↑⋆ₛ-refl A)

↑⋆ₑ-refl : {Γ : Ctxt} (a : Event Γ) → ↑⋆ₑ ⊆⋆-refl a ≡ a
↑⋆ₑ-refl (EvtReceive p a b) = cong₃ EvtReceive (↑⋆d-refl p) (↑⋆ᵢ-refl a) (↑⋆ᵢ-refl b)
↑⋆ₑ-refl (EvtInternal a d)  = cong₂ EvtInternal (↑⋆ᵢ-refl a) (↑⋆d-refl d)

↑⋆f-refl : {Γ : Ctxt} (a : Fault Γ) → ↑⋆f ⊆⋆-refl a ≡ a
↑⋆f-refl (FaultCorrect a b) = cong₂ FaultCorrect (↑⋆ᵢ-refl a) (↑⋆ᵢ-refl b)

↑⋆ₐ-refl : {Γ : Ctxt} (a : Atom Γ) → ↑⋆ₐ ⊆⋆-refl a ≡ a
↑⋆ₐ-refl (atProp    x) = cong atProp    (↑⋆ₚ-refl x)
↑⋆ₐ-refl (atAction  x) = cong atAction  (↑⋆ₜ-refl x)
↑⋆ₐ-refl (atEvent   x) = cong atEvent   (↑⋆ₑ-refl x)
↑⋆ₐ-refl (atCorrect x) = cong atCorrect (↑⋆f-refl x)

↑⋆ᵣ-refl : {Γ : Ctxt} (r : Res Γ) → ↑⋆ᵣ ⊆⋆-refl r ≡ r
↑⋆ᵣ-refl (𝐯 i)   = cong 𝐯 (app-⊆⋆-refl _ i)
↑⋆ᵣ-refl 𝟎       = refl
↑⋆ᵣ-refl (rvar ρ)       = refl
↑⋆ᵣ-refl (r ⋆ s) = cong₂ _⋆_ (↑⋆ᵣ-refl r) (↑⋆ᵣ-refl s)

↑⋆A-refl : {Γ : Ctxt} (A : SetAtom Γ) → ↑⋆A ⊆⋆-refl A ≡ A
↑⋆A-refl (a ∈ₐ A)     = cong₂ _∈ₐ_ (↑⋆ᵢ-refl a) (↑⋆ₛ-refl A)
↑⋆A-refl (∣ A ∣ₛ＝ n) = cong (λ z → ∣ z ∣ₛ＝ n) (↑⋆ₛ-refl A)

↑⋆-refl : {Γ : Ctxt} (f : Form Γ) → ↑⋆ ⊆⋆-refl f ≡ f
↑⋆-refl (𝕒 x)         = cong 𝕒 (↑⋆ₐ-refl x)
↑⋆-refl (var x)       = refl
↑⋆-refl ⊤·            = refl
↑⋆-refl ⊥·            = refl
↑⋆-refl (f ∧· g)      = cong₂ _∧·_ (↑⋆-refl f) (↑⋆-refl g)
↑⋆-refl (f ∨· g)      = cong₂ _∨·_ (↑⋆-refl f) (↑⋆-refl g)
↑⋆-refl (f →· g)      = cong₂ _→·_ (↑⋆-refl f) (↑⋆-refl g)
↑⋆-refl (∀· u f)      = cong (∀· u) (↑⋆-refl f)
↑⋆-refl (∃· u f)      = cong (∃· u) (↑⋆-refl f)
↑⋆-refl (𝔸 A)         = cong 𝔸 (↑⋆A-refl A)
↑⋆-refl (f Ｕ g)      = cong₂ _Ｕ_ (↑⋆-refl f) (↑⋆-refl g)
↑⋆-refl (Ｏ f)        = cong Ｏ (↑⋆-refl f)
↑⋆-refl (f Ｓ g)      = cong₂ _Ｓ_ (↑⋆-refl f) (↑⋆-refl g)
↑⋆-refl (Ｙ f)        = cong Ｙ (↑⋆-refl f)
↑⋆-refl (Ｂ f)        = cong Ｂ (↑⋆-refl f)
↑⋆-refl (Ｆ f)        = cong Ｆ_ (↑⋆-refl f)
↑⋆-refl (t₁ ⟨ c ⟩ t₂) = cong₂ (λ a b → a ⟨ c ⟩ b) (↑⋆ᵣ-refl t₁) (↑⋆ᵣ-refl t₂)

↑⋆I-refl : {Γ : Ctxt} (I : Interval Γ) → ↑⋆I ⊆⋆-refl I ≡ I
↑⋆I-refl ［ a , b ］ = cong₂ ［_,_］ (↑⋆ᵣ-refl a) (↑⋆ᵣ-refl b)
↑⋆I-refl ［ a , b ） = cong₂ ［_,_） (↑⋆ᵣ-refl a) (↑⋆ᵣ-refl b)
↑⋆I-refl （ a , b ］ = cong₂ （_,_］ (↑⋆ᵣ-refl a) (↑⋆ᵣ-refl b)
↑⋆I-refl （ a , b ） = cong₂ （_,_） (↑⋆ᵣ-refl a) (↑⋆ᵣ-refl b)

↑⋆CE-refl : {Γ : Ctxt} (x : CE Γ) → ↑⋆CE ⊆⋆-refl x ≡ x
↑⋆CE-refl (CEr r) = cong CEr (↑⋆ᵣ-refl r)
↑⋆CE-refl CEu     = refl
↑⋆CE-refl (CEi I) = cong CEi (↑⋆I-refl I)

↑FormSub⋆-refl : {Γ : Ctxt} (σ : FormSub⋆ Γ) → ↑FormSub⋆ ⊆⋆-refl σ ≡ σ
↑FormSub⋆-refl ●           = refl
↑FormSub⋆-refl (x ↦ f ⨾ σ) = cong₂ (x ↦_⨾_) (↑⋆-refl f) (↑FormSub⋆-refl σ)

-- The corollary: on closed sequents, substitution is just substF⋆ on the
-- conclusion.  E.g. substF⋆ (0 ↦ A ⨾ ●) (var 0 →· var 0) reduces to A →· A.
-- The only transport is this one subst₂ around the whole derivation.
subst-⊢⋆₀ : (σ : FormSub⋆₀) {r : CE ⟨⟩} {C : Form ⟨⟩}
          → ⊢ (seq ℂ⟨⟩ r C)
          → ⊢ (seq ℂ⟨⟩ r (substF⋆ σ C))
subst-⊢⋆₀ σ {r} {C} d =
  subst₂ (λ r′ C′ → ⊢ (seq ℂ⟨⟩ r′ C′))
         (↑⋆CE-refl r)
         (trans (↑⋆-refl _) (cong (λ τ → substF⋆ τ C) (↑FormSub⋆-refl σ)))
         (subst-⊢⋆ σ d)

-- Inverting →I in the empty context, where no left rule or ax can apply.
-- Lets subst-⊢⋆₀ (stated for ℂ⟨⟩) produce sequents with hypotheses: prove
-- H →· C in ℂ⟨⟩, then move H into the context.
→I-inv₀ : {r : Res ⟨⟩} {A B : Form ⟨⟩}
        → ⊢ (rseq ℂ⟨⟩ r (A →· B))
        → ⊢ (rseq (ℂe ℂ⟨⟩ A r) r B)
→I-inv₀ (→I d)     = d
→I-inv₀ (ax ())
→I-inv₀ (⊥L _ ())
→I-inv₀ (∧L () _)
→I-inv₀ (→L () _ _)
→I-inv₀ (∨L _ () _ _)

-- subst-⊢⋆₀ generalised to closed contexts with hypotheses (any labels, but
-- no ℂv).  Such a context is given as a list of closed hypotheses, the head
-- being the last (innermost) one:
--   ⌜ (A , CEr t) ∷ (B , CEu) ∷ [] ⌝  =  ℂe (ℂu ℂ⟨⟩ B) A t.
-- The hypotheses are cast along ⟨⟩ ≡ ℂtxt ⌜ l ⌝, which is refl for any
-- concrete list, so for concrete l both ⌜ l ⌝ and the casts compute away.

Hyps : Set₁
Hyps = List (Form ⟨⟩ × CE ⟨⟩)

⌜_⌝    : Hyps → ℂ₀
ℂtxt⌜⌝ : (l : Hyps) → ⟨⟩ ≡ ℂtxt ⌜ l ⌝

⌜ []          ⌝ = ℂ⟨⟩
⌜ (f , a) ∷ l ⌝ = ℂx ⌜ l ⌝ (subst Form (ℂtxt⌜⌝ l) f) (subst CE (ℂtxt⌜⌝ l) a)

ℂtxt⌜⌝ []      = refl
ℂtxt⌜⌝ (_ ∷ l) = ℂtxt⌜⌝ l

castF : (l : Hyps) → Form ⟨⟩ → ℂForm ⌜ l ⌝
castF l = subst Form (ℂtxt⌜⌝ l)

castCE : (l : Hyps) → CE ⟨⟩ → ℂCE ⌜ l ⌝
castCE l = subst CE (ℂtxt⌜⌝ l)

substHyps : FormSub⋆₀ → Hyps → Hyps
substHyps σ []            = []
substHyps σ ((f , a) ∷ l) = (substF⋆ σ f , a) ∷ substHyps σ l

module _ (σ : FormSub⋆₀) where

  ℂtxt-subst⌜⌝ : (l : Hyps) → ⟨⟩ ≡ ℂtxt (substCtxt⋆ σ ⌜ l ⌝)
  ℂtxt-subst⌜⌝ []      = refl
  ℂtxt-subst⌜⌝ (_ ∷ l) = ℂtxt-subst⌜⌝ l

  -- Once both contexts are ⟨⟩, the lifts are by the only inclusion
  -- ⟨⟩ ⊆⋆ ⟨⟩, which is ⊆⋆-refl.
  clean-F : {Γ Γ′ : Ctxt} (e : ⟨⟩ ≡ Γ) (e′ : ⟨⟩ ≡ Γ′)
            (s : Γ ⊆⋆ Γ′) (t : ⟨⟩ ⊆⋆ Γ) (f : Form ⟨⟩)
          → ↑⋆ s (substF⋆ (↑FormSub⋆ t σ) (subst Form e f)) H.≅ substF⋆ σ f
  clean-F refl refl (⊆⋆-init .⟨⟩) (⊆⋆-init .⟨⟩) f =
    H.≡-to-≅ (trans (↑⋆-refl _) (cong (λ τ → substF⋆ τ f) (↑FormSub⋆-refl σ)))

  clean-CE : {Γ Γ′ : Ctxt} (e : ⟨⟩ ≡ Γ) (e′ : ⟨⟩ ≡ Γ′)
             (s : Γ ⊆⋆ Γ′) (a : CE ⟨⟩)
           → ↑⋆CE s (subst CE e a) H.≅ a
  clean-CE refl refl (⊆⋆-init .⟨⟩) a = H.≡-to-≅ (↑⋆CE-refl a)

  key-F : (l : Hyps) (f : Form ⟨⟩)
        → ↑⋆ (ℂtxt-substCtxt⋆ σ ⌜ l ⌝) (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ ⌜ l ⌝) σ) (castF l f))
          H.≅ castF (substHyps σ l) (substF⋆ σ f)
  key-F l f =
    H.trans (clean-F (ℂtxt⌜⌝ l) (ℂtxt-subst⌜⌝ l) _ _ f)
            (H.sym (H.≡-subst-removable Form (ℂtxt⌜⌝ (substHyps σ l)) (substF⋆ σ f)))

  key-CE : (l : Hyps) (a : CE ⟨⟩)
         → ↑⋆CE (ℂtxt-substCtxt⋆ σ ⌜ l ⌝) (castCE l a) H.≅ castCE (substHyps σ l) a
  key-CE l a =
    H.trans (clean-CE (ℂtxt⌜⌝ l) (ℂtxt-subst⌜⌝ l) _ a)
            (H.sym (H.≡-subst-removable CE (ℂtxt⌜⌝ (substHyps σ l)) a))

  ℂx-cong : {c c′ : ℂ₀} {f : ℂForm c} {f′ : ℂForm c′} {a : ℂCE c} {a′ : ℂCE c′}
          → c ≡ c′ → f H.≅ f′ → a H.≅ a′ → ℂx c f a ≡ ℂx c′ f′ a′
  ℂx-cong refl H.refl H.refl = refl

  seq-cong : {c c′ : ℂ₀} {T : ℂCE c} {T′ : ℂCE c′} {C : ℂForm c} {C′ : ℂForm c′}
           → c ≡ c′ → T H.≅ T′ → C H.≅ C′ → seq c T C ≡ seq c′ T′ C′
  seq-cong refl H.refl H.refl = refl

  ctx-eq : (l : Hyps) → substCtxt⋆ σ ⌜ l ⌝ ≡ ⌜ substHyps σ l ⌝
  ctx-eq []            = refl
  ctx-eq ((f , a) ∷ l) = ℂx-cong (ctx-eq l) (key-F l f) (key-CE l a)

  -- The generalised corollary.  For a concrete l, the conclusion computes to
  -- the expected sequent: hypotheses and goal are substF⋆ σ of the originals.
  subst-⊢⋆ₕ : (l : Hyps) {r : CE ⟨⟩} {C : Form ⟨⟩}
            → ⊢ (seq ⌜ l ⌝ (castCE l r) (castF l C))
            → ⊢ (seq ⌜ substHyps σ l ⌝ (castCE (substHyps σ l) r)
                     (castF (substHyps σ l) (substF⋆ σ C)))
  subst-⊢⋆ₕ l {r} {C} d =
    subst ⊢ (seq-cong (ctx-eq l) (key-CE l r) (key-F l C)) (subst-⊢⋆ σ d)

-- ===========================================================================
-- RULES FROM SEQUENTS
--
-- A rule whose premises and conclusion share the context Γ,
--     Γ ⊢[R₁] H₁   …   Γ ⊢[Rₙ] Hₙ
--     ---------------------------
--            Γ ⊢[T] D
-- follows from the single sequent  Γ, H₁@R₁, …, Hₙ@Rₙ ⊢[T] D:  cut each
-- premise into the context with hyp-cut, after weakening the later premises
-- past the hypotheses already added with hyp-wk.
-- ===========================================================================

hyp-cut : (M : Model₀) (Γ : ℂ₀) (H : ℂForm Γ) (R T : ℂCE Γ) (D : ℂForm Γ)
        → sat-sequent M (seq (ℂx Γ H R) T D)
        → sat-sequent M (seq Γ R H)
        → sat-sequent M (seq Γ T D)
hyp-cut M Γ H R T D h p s satΓ = h s (satΓ , p s satΓ)

hyp-wk : (M : Model₀) (Γ : ℂ₀) (H : ℂForm Γ) (R T : ℂCE Γ) (D : ℂForm Γ)
       → sat-sequent M (seq Γ T D)
       → sat-sequent M (seq (ℂx Γ H R) T D)
hyp-wk M Γ H R T D p s (satΓ , _) = p s satΓ

-- Example: rule◇↓R from RulesTemp.lagda, through ⊢ instead of the semantics.
--
--   Γ ⊢[r] r ⊑ r₁    Γ ⊢[r] r₁ ⊑ r ⋆ t    Γ ⊢[r₁] A
--   ----------------------------------------------------
--                    Γ ⊢[r] ◇↓ t A
module _ (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ) where

  private
    Γ₁ Γ₂ Γ₃ : ℂ₀
    Γ₁ = ℂe Γ  (r ⊑ r₁)     r
    Γ₂ = ℂe Γ₁ (r₁ ⊑ r ⋆ t) r
    Γ₃ = ℂe Γ₂ A            r₁

    -- The inner Ｆ body after substituting r for its bound variable, and
    -- the conjunction after substituting r₁.  Both are only propositional
    -- equalities because A and t are opaque (cf. helper₀/helper₁ in RulesTemp).
    Y : Form (ℂtxt Γ ، 𝕍ℝ)
    Y = (𝕣₀ ⊑ (↑ᵣ₀ r ⋆ ↑ᵣ₀ t)) ∧· ↑₀ A

    eq-outer : subℝ (◇ (Ｆ ((𝕣₀ ⊑ (𝕣₁ ⋆ ↑ᵣ₁ t)) ∧· ↑₁ A))) r ≡ ◇ (Ｆ Y)
    eq-outer = cong (λ x → ◇ (Ｆ x))
                    (cong₂ _∧·_ (cong₂ _⊑_ refl (cong₂ _⋆_ refl (sub-Res-↑ᵣ₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r t)))
                                (sub-↑₁₀ (ℂtxt Γ) 𝕍ℝ 𝕍ℝ r A))

    eq-inner : subℝ Y r₁ ≡ (r₁ ⊑ (r ⋆ t)) ∧· A
    eq-inner = cong₂ _∧·_ (cong₂ _⊑_ refl (cong₂ _⋆_ (sub-Res-↑ᵣ₀ (ℂtxt Γ) 𝕍ℝ r₁ r)
                                                    (sub-Res-↑ᵣ₀ (ℂtxt Γ) 𝕍ℝ r₁ t)))
                          (sub-↑₀ (ℂtxt Γ) 𝕍ℝ r₁ A)

    hyp-r⊑r₁ : Ax Γ₃ (CEr r) (r ⊑ r₁)
    hyp-r⊑r₁ = skip A (CEr r₁) (skip (r₁ ⊑ r ⋆ t) (CEr r) (found Γ (r ⊑ r₁) (CEr r)))

    hyp-r₁⊑rt : Ax Γ₃ (CEr r) (r₁ ⊑ r ⋆ t)
    hyp-r₁⊑rt = skip A (CEr r₁) (found Γ₁ (r₁ ⊑ r ⋆ t) (CEr r))

    hyp-A : Ax Γ₃ (CEr r₁) A
    hyp-A = found Γ₂ A (CEr r₁)

  -- Γ, (r ⊑ r₁)@r, (r₁ ⊑ r ⋆ t)@r, A@r₁ ⊢[r] ◇↓ t A
  ◇↓R-⊢ : ⊢ (rseq Γ₃ r (◇↓ t A))
  ◇↓R-⊢ =
    ＦI (subst (λ X → ⊢ (rseq Γ₃ r X)) (sym eq-outer)
          (ＵI (cmpR (ptR r) (ax hyp-r⊑r₁))
               (ＦI (subst (λ X → ⊢ (rseq Γ₃ r₁ X)) (sym eq-inner)
                      (∧I (cmpR (ptR r) (ax hyp-r₁⊑rt)) (ax hyp-A))))
               ⊤I))

  rule◇↓R-sat′ : (M : Model₀) → sat-rule M (rule◇↓R Γ t r r₁ A)
  rule◇↓R-sat′ M (sat1 , sat2 , sat3 , _) =
    hyp-cut M Γ (r ⊑ r₁) (CEr r) (CEr r) (◇↓ t A)
      (hyp-cut M Γ₁ (r₁ ⊑ r ⋆ t) (CEr r) (CEr r) (◇↓ t A)
        (hyp-cut M Γ₂ A (CEr r₁) (CEr r) (◇↓ t A)
          (sound M ◇↓R-⊢)
          (hyp-wk M Γ₁ (r₁ ⊑ r ⋆ t) (CEr r) (CEr r₁) A
            (hyp-wk M Γ (r ⊑ r₁) (CEr r) (CEr r₁) A sat3)))
        (hyp-wk M Γ (r ⊑ r₁) (CEr r) (CEr r) (r₁ ⊑ r ⋆ t) sat2))
      sat1

-- ===========================================================================
-- SUBST APPROACH: examples (see also Examples.lagda)
-- ===========================================================================

--subst-⊢⋆ σ {Δ} {r} {C} (ＵI h₁ h₂ h₃) = ＵI (subst-⊢⋆ σ h₁) (subst-⊢⋆ σ h₂) {!!} --(subst-⊢⋆ σ h₃)

{--
subst-⊢′ : (σ : FormSub₀) {Δ : ℂ₀} {r : ℂCE Δ} {C : ℂForm Δ}
        → ⊢ (seq Δ r C)
        → ⊢ (seq (substCtxt σ Δ)
                 (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) r)
                 {!substF!})
--                 (subst Form (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) C)))
subst-⊢′ = {!!}
--}

FormSub-𝐯0 : (Γ : Ctxt) (A : Form Γ) → FormSub Γ
FormSub-𝐯0 Γ A v with v ≟ 0
... | yes p = A
... | no q = ⊥· -- Could as well return A everywhere

{-- Commented out: subst-⊢ (function substitutions) does not give a clean type.
example0′ : (M : Model₀)
           (A : Form₀)
         → ⊢ (seq ℂ⟨⟩ (CEr 𝟎) (𝐯0 →· 𝐯0))
         → ⊢ (seq ℂ⟨⟩ (CEr 𝟎) (A →· A))
example0′ M A s = {!subst-⊢ (λ _ → A) s !}
--}

example0 : (M : Model₀)
           (A : Form₀)
         → ⊢ (seq ℂ⟨⟩ (CEr 𝟎) (𝐯0 →· 𝐯0))
         → ⊢ (seq ℂ⟨⟩ (CEr 𝟎) (A →· A))
example0 M A s = subst-⊢⋆₀ (0 ↦ A ⨾ ●) s

{-- Commented out: Prove M ℂ⟨⟩ (CEr 𝟎) (A →· A) gets stuck because Form-dec
-- cannot compare the Agda variable A with itself.  See example1′ (subst
-- approach) and Examples.lagda (both approaches) for what works instead.
example1 : (M : Model₀)
           (A : Form₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (A →· A)))
example1 M A p s h = {!Prove M ℂ⟨⟩ (CEr 𝟎) (A →· A)!}
--}

example2 : (M : Model₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (𝐯0 →· 𝐯0)))
example2 M p s h = sound M (→I (ax (found ℂ⟨⟩ (var 0) (CEr 𝟎)))) s (lift tt)
-- Prove 10 M ℂ⟨⟩ (CEr 𝟎) (𝐯0 →· 𝐯0) gives us (when typing C-u C-u C-u C-c C-n):
-- just (sound M (→I (ax (found ℂ⟨⟩ (var 0) (CEr 𝟎)))))

-- Fully automatic: search on the object-variable instance, then substitute.
-- from-just only typechecks because search⊢ evaluates to just _ here.
example1′ : (M : Model₀)
            (A : Form₀)
          → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (A →· A)))
example1′ M A p =
  sound M (subst-⊢⋆₀ (0 ↦ A ⨾ ●) (from-just (search⊢ 10 ℂ⟨⟩ (CEr 𝟎) (𝐯0 →· 𝐯0))))

-- Same, with the derivation written by hand.
example3 : (M : Model₀)
           (A : Form₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (A →· A)))
example3 M A p s h = sound M (subst-⊢⋆₀ (0 ↦ A ⨾ ●) (→I (ax (found ℂ⟨⟩ (var 0) (CEr 𝟎))))) s (lift tt)

-- Example that makes use of an elimination
example4 : (M : Model₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) ((𝐯0 ∧· 𝐯1) →· 𝐯0)))
example4 M p s h = sound M (→I (∧L (found ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (ax (skip (var 1) (CEr 𝟎) (found (ℂx ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (var 0) (CEr 𝟎)))))) s (lift tt)
-- Prove 10 M ℂ⟨⟩ (CEr 𝟎) ((𝐯0 ∧· 𝐯1) →· 𝐯0) gives us (when typing C-u C-u C-u C-c C-n):
-- just (sound M (→I (∧L (found ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (ax (skip (var 1) (CEr 𝟎) (found (ℂx ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (var 0) (CEr 𝟎)))))))

\end{code}
