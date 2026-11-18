A simpler version compared to Experiment.lagda, without elimination rules for now for simplicity.

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
open import Data.Nat using (ℕ ; zero ; suc ; _≡ᵇ_ ; _⊔_)
open import Data.Bool using (Bool ; true ; false) renaming (_∨_ to _∨ᵇ_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst ; dcong₂ ; _≡_ ; module ≡-Reasoning)
open ≡-Reasoning


open import Induction.WellFounded
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_≟_)
open import Function using (_∘_ ; id)
open import Axiom.ExcludedMiddle using (ExcludedMiddle)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.Any using (here ; there)
import RulesClassical
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
open import RulesTemp(𝔻)(W) hiding (ＹL ; ＹL-sat)
open import RulesPred(𝔻)(W) using (rule∀I-sat ; rule∃L-sat ; rule∃R-sat)

open World.World W using (_◃_ ; _≼_ ; ≼-trans ; ≼-refl)
open import WorldUtil W using (≺-≼-trans ; ≺→≼)

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

-- ---------------------------------------------------------------------------
-- Soundness of the temporal left rules that introduce a fresh time point x.
-- The eliminated hypothesis stays in Δ (as in ∧L), so these are the rules
-- ruleＵL and ruleＳL of RulesTemp.lagda with the hypothesis anywhere in the
-- context and an arbitrary label T, plus the analogous rules for Ｏ and Ｙ:
--
--   Γ, x, r ◁ x, A^x ⊢[T] C      Γ, x, x ◁ r, A^x ⊢[T] C
--   ----------------------      ----------------------
--     Γ, (Ｏ A)^r ⊢[T] C           Γ, (Ｙ A)^r ⊢[T] C
-- ---------------------------------------------------------------------------

ＯL-sat : (M : Model₀) (Δ : ℂ₀) (r : ℂRes Δ) (T : ℂCE Δ) (A C : ℂForm Δ)
        → sat-sequent M (seq (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ◁ 𝕣₀)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
        → (s : ℂSub Δ) → sat-ctxt Δ (M ≔ₛ s)
        → sat-ctxt-annot (Ｏ A) (CEr r) (M ≔ₛ s)
        → sat-ctxt-annot C T (M ≔ₛ s)
ＯL-sat M Δ r T A C d s satΔ (t , c₁ , c₂) =
  sat-ctxt-annot-↑₀ (M ≔ₛ (s ⹁ 𝕍ℝ ∶ t)) C T
    (d (s ⹁ 𝕍ℝ ∶ t)
       ((satΔ , lift (subst (λ x → x ◃ t) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) c₁)) ,
        →⊨⊨ₜ-↑₀ {ℂtxt Δ} {M ≔ₛ s} {A} {𝕍ℝ} t t c₂))

ＹL-sat : (M : Model₀) (Δ : ℂ₀) (r : ℂRes Δ) (T : ℂCE Δ) (A C : ℂForm Δ)
        → sat-sequent M (seq (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
        → (s : ℂSub Δ) → sat-ctxt Δ (M ≔ₛ s)
        → sat-ctxt-annot (Ｙ A) (CEr r) (M ≔ₛ s)
        → sat-ctxt-annot C T (M ≔ₛ s)
ＹL-sat M Δ r T A C d s satΔ (t , c₁ , c₂) =
  sat-ctxt-annot-↑₀ (M ≔ₛ (s ⹁ 𝕍ℝ ∶ t)) C T
    (d (s ⹁ 𝕍ℝ ∶ t)
       ((satΔ , lift (subst (λ x → t ◃ x) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) c₁)) ,
        →⊨⊨ₜ-↑₀ {ℂtxt Δ} {M ≔ₛ s} {A} {𝕍ℝ} t t c₂))

-- as ruleＵL-sat
ＵL-sat : (M : Model₀) (Δ : ℂ₀) (r : ℂRes Δ) (T : ℂCE Δ) (A B C : ℂForm Δ)
        → sat-sequent M (seq (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ B) 𝕣₀) (↑₀ A) ［ ↑ᵣ₀ r , 𝕣₀ ）)
                             (↑CE₀ T) (↑₀ C))
        → (s : ℂSub Δ) → sat-ctxt Δ (M ≔ₛ s)
        → sat-ctxt-annot (A Ｕ B) (CEr r) (M ≔ₛ s)
        → sat-ctxt-annot C T (M ≔ₛ s)
ＵL-sat M Δ r T A B C d s satΔ (t , c₁ , c₂ , c₃) =
  sat-ctxt-annot-↑₀ (M ≔ₛ (s ⹁ 𝕍ℝ ∶ t)) C T
    (d (s ⹁ 𝕍ℝ ∶ t)
       (((satΔ , lift (subst (λ x → x ≼ t) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) c₁)) ,
         →⊨⊨ₜ-↑₀ {ℂtxt Δ} {M ≔ₛ s} {B} {𝕍ℝ} t t c₂) ,
        λ w (d₁ , d₂) →
          →⊨⊨ₜ-↑₀ {ℂtxt Δ} {M ≔ₛ s} {A} {𝕍ℝ} t w
                  (c₃ w (≼-trans (subst (λ x → (⟦ r ⟧ᵣ s) ≼ x) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) ≼-refl) d₁) d₂)))

-- as ruleＳL-sat
ＳL-sat : (M : Model₀) (Δ : ℂ₀) (r : ℂRes Δ) (T : ℂCE Δ) (A B C : ℂForm Δ)
        → sat-sequent M (seq (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ r)) (↑₀ B) 𝕣₀) (↑₀ A) （ 𝕣₀ , ↑ᵣ₀ r ］)
                             (↑CE₀ T) (↑₀ C))
        → (s : ℂSub Δ) → sat-ctxt Δ (M ≔ₛ s)
        → sat-ctxt-annot (A Ｓ B) (CEr r) (M ≔ₛ s)
        → sat-ctxt-annot C T (M ≔ₛ s)
ＳL-sat M Δ r T A B C d s satΔ (t , c₁ , c₂ , c₃) =
  sat-ctxt-annot-↑₀ (M ≔ₛ (s ⹁ 𝕍ℝ ∶ t)) C T
    (d (s ⹁ 𝕍ℝ ∶ t)
       (((satΔ , lift (subst (λ x → t ≼ x) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) c₁)) ,
         →⊨⊨ₜ-↑₀ {ℂtxt Δ} {M ≔ₛ s} {B} {𝕍ℝ} t t c₂) ,
        λ w (d₁ , d₂) →
          →⊨⊨ₜ-↑₀ {ℂtxt Δ} {M ≔ₛ s} {A} {𝕍ℝ} t w
                  (c₃ w d₁ (≼-trans d₂ (subst (λ x → x ≼ (⟦ r ⟧ᵣ s)) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) ≼-refl)))))

--   Γ, x, x ◁ r ⊢[x] A
--   ------------------
--     Γ ⊢[r] Ｂ A
ＢR-sat : (M : Model₀) (Δ : ℂ₀) (r : ℂRes Δ) (A : ℂForm Δ)
        → sat-sequent M (rseq (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕣₀ (↑₀ A))
        → sat-sequent M (rseq Δ r (Ｂ A))
ＢR-sat M Δ r A d s satΔ t c =
  ⊨⊨ₜ-↑₀→ {ℂtxt Δ} {M ≔ₛ s} {A} {𝕍ℝ} t t
    (d (s ⹁ 𝕍ℝ ∶ t) (satΔ , lift (subst (λ x → t ◃ x) (sym (⟦↑ᵣ₀⟧ᵣ𝕎 r s t)) c)))

-- excluded middle, as RulesClassical takes it; only □L uses it
EMT : Set₂
EMT = ExcludedMiddle (lsuc 0ℓ)

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
  -- past operators: introduction rules
  ＹI  : {Δ : ℂ₀} {r r₁ : ℂRes Δ} {A : ℂForm Δ}
      → ⊢ (useq Δ (r₁ ◁ r)) → ⊢ (rseq Δ r₁ A) → ⊢ (rseq Δ r (Ｙ A))
  ＳI  : {Δ : ℂ₀} {r r₁ : ℂRes Δ} {A B : ℂForm Δ}
      → ⊢ (useq Δ (r₁ ⊑ r))
      → ⊢ (rseq Δ r₁ B)
      → ⊢ (rseq (ℂu (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r₁ ⊏ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ r)) 𝕣₀ (↑₀ A))
      → ⊢ (rseq Δ r (A Ｓ B))
  ＢI  : {Δ : ℂ₀} {r : ℂRes Δ} {A : ℂForm Δ}
      → ⊢ (rseq (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) 𝕣₀ (↑₀ A))
      → ⊢ (rseq Δ r (Ｂ A))
  -- temporal elimination rules; the hypothesis stays in the context
  ＯL  : {Δ : ℂ₀} {r : ℂRes Δ} {T : ℂCE Δ} {A C : ℂForm Δ}
      → Ax Δ (CEr r) (Ｏ A)
      → ⊢ (seq (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ◁ 𝕣₀)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
      → ⊢ (seq Δ T C)
  ＹL  : {Δ : ℂ₀} {r : ℂRes Δ} {T : ℂCE Δ} {A C : ℂForm Δ}
      → Ax Δ (CEr r) (Ｙ A)
      → ⊢ (seq (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
      → ⊢ (seq Δ T C)
  ＵL  : {Δ : ℂ₀} {r : ℂRes Δ} {T : ℂCE Δ} {A B C : ℂForm Δ}
      → Ax Δ (CEr r) (A Ｕ B)
      → ⊢ (seq (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ B) 𝕣₀) (↑₀ A) ［ ↑ᵣ₀ r , 𝕣₀ ）)
               (↑CE₀ T) (↑₀ C))
      → ⊢ (seq Δ T C)
  ＳL  : {Δ : ℂ₀} {r : ℂRes Δ} {T : ℂCE Δ} {A B C : ℂForm Δ}
      → Ax Δ (CEr r) (A Ｓ B)
      → ⊢ (seq (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ r)) (↑₀ B) 𝕣₀) (↑₀ A) （ 𝕣₀ , ↑ᵣ₀ r ］)
               (↑CE₀ T) (↑₀ C))
      → ⊢ (seq Δ T C)
  -- Ｂ A at r holds at every r₁ with r₁ ◁ r
  ＢL  : {Δ : ℂ₀} {r r₁ : ℂRes Δ} {T : ℂCE Δ} {A C : ℂForm Δ}
      → Ax Δ (CEr r) (Ｂ A)
      → ⊢ (useq Δ (r₁ ◁ r))
      → ⊢ (seq (ℂe Δ A r₁) T C)
      → ⊢ (seq Δ T C)
  -- freeze: Ｆ A at r gives A[x/r] at r
  ＦL  : {Δ : ℂ₀} {r : ℂRes Δ} {T : ℂCE Δ} {A : ℂForm (ℂv Δ 𝕍ℝ)} {C : ℂForm Δ}
      → Ax Δ (CEr r) (Ｆ A)
      → ⊢ (seq (ℂe Δ (subℝ A r) r) T C)
      → ⊢ (seq Δ T C)
  -- reasoning about comparisons.  Comparisons do not depend on the time
  -- point, so these rules are stated unlabelled; cmpR moves the result to
  -- any label.
  ⊑refl   : {Δ : ℂ₀} {a : ℂRes Δ} → ⊢ (useq Δ (a ⊑ a))
  ⊑𝟎      : {Δ : ℂ₀} {a : ℂRes Δ} → ⊢ (useq Δ (𝟎 ⊑ a))
  ⊑trans  : {Δ : ℂ₀} {a b c : ℂRes Δ}
          → ⊢ (useq Δ (a ⊑ b)) → ⊢ (useq Δ (b ⊑ c)) → ⊢ (useq Δ (a ⊑ c))
  ⊑⊏trans : {Δ : ℂ₀} {a b c : ℂRes Δ}
          → ⊢ (useq Δ (a ⊑ b)) → ⊢ (useq Δ (b ⊏ c)) → ⊢ (useq Δ (a ⊏ c))
  ⊏⊑trans : {Δ : ℂ₀} {a b c : ℂRes Δ}
          → ⊢ (useq Δ (a ⊏ b)) → ⊢ (useq Δ (b ⊑ c)) → ⊢ (useq Δ (a ⊏ c))
  ◁⊑      : {Δ : ℂ₀} {a b : ℂRes Δ} → ⊢ (useq Δ (a ◁ b)) → ⊢ (useq Δ (a ⊑ b))
  ◁⊏      : {Δ : ℂ₀} {a b : ℂRes Δ} → ⊢ (useq Δ (a ◁ b)) → ⊢ (useq Δ (a ⊏ b))
  ⊏⊑      : {Δ : ℂ₀} {a b : ℂRes Δ} → ⊢ (useq Δ (a ⊏ b)) → ⊢ (useq Δ (a ⊑ b))
  ＝⊑      : {Δ : ℂ₀} {a b : ℂRes Δ} → ⊢ (useq Δ (a ＝ b)) → ⊢ (useq Δ (a ⊑ b))
  ⊑⋆      : {Δ : ℂ₀} {a₁ a₂ b₁ b₂ : ℂRes Δ}
          → ⊢ (useq Δ (a₁ ⊑ b₁)) → ⊢ (useq Δ (a₂ ⊑ b₂)) → ⊢ (useq Δ (a₁ ⋆ a₂ ⊑ b₁ ⋆ b₂))
  ⊑⋆ₗ     : {Δ : ℂ₀} {a b t : ℂRes Δ} → ⊢ (useq Δ (a ⊑ b)) → ⊢ (useq Δ (a ⊑ b ⋆ t))
  ⊑⋆ᵣ     : {Δ : ℂ₀} {a b t : ℂRes Δ} → ⊢ (useq Δ (a ⊑ t)) → ⊢ (useq Δ (a ⊑ b ⋆ t))
  ＝refl   : {Δ : ℂ₀} {a : ℂRes Δ} → ⊢ (useq Δ (a ＝ a))
  ＝sym    : {Δ : ℂ₀} {a b : ℂRes Δ} → ⊢ (useq Δ (b ＝ a)) → ⊢ (useq Δ (a ＝ b))
  ＝trans  : {Δ : ℂ₀} {a b c : ℂRes Δ}
          → ⊢ (useq Δ (a ＝ b)) → ⊢ (useq Δ (b ＝ c)) → ⊢ (useq Δ (a ＝ c))
  ＝⋆      : {Δ : ℂ₀} {a₁ a₂ b₁ b₂ : ℂRes Δ}
          → ⊢ (useq Δ (a₁ ＝ b₁)) → ⊢ (useq Δ (a₂ ＝ b₂)) → ⊢ (useq Δ (a₁ ⋆ a₂ ＝ b₁ ⋆ b₂))
  ＝assoc  : {Δ : ℂ₀} {a b c : ℂRes Δ} → ⊢ (useq Δ (a ⋆ (b ⋆ c) ＝ (a ⋆ b) ⋆ c))
  ＝comm   : {Δ : ℂ₀} {a b : ℂRes Δ} → ⊢ (useq Δ (a ⋆ b ＝ b ⋆ a))
  ＝lid    : {Δ : ℂ₀} {a : ℂRes Δ} → ⊢ (useq Δ (𝟎 ⋆ a ＝ a))
  -- quantifiers over agents, sets of agents, propositions and data
  ∀I  : {Δ : ℂ₀} {T : ℂCE Δ} {u : 𝕌} {A : ℂForm (ℂv Δ (𝕍𝕌 u))}
      → ⊢ (seq (ℂv Δ (𝕍𝕌 u)) (↑CE₀ T) A)
      → ⊢ (seq Δ T (∀· u A))
  ∀L  : {Δ : ℂ₀} {R T : ℂCE Δ} {u : 𝕌} {A : ℂForm (ℂv Δ (𝕍𝕌 u))} {C : ℂForm Δ}
      → Ax Δ R (∀· u A)
      → (v : ℂ⟦𝕌⟧ Δ u)
      → ⊢ (seq (ℂx Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) R) T C)
      → ⊢ (seq Δ T C)
  ∃R  : {Δ : ℂ₀} {T : ℂCE Δ} {u : 𝕌} {A : ℂForm (ℂv Δ (𝕍𝕌 u))}
      → (v : ℂ⟦𝕌⟧ Δ u)
      → ⊢ (seq Δ T (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)))
      → ⊢ (seq Δ T (∃· u A))
  ∃L  : {Δ : ℂ₀} {R : ℂRes Δ} {T : ℂCE Δ} {u : 𝕌} {A : ℂForm (ℂv Δ (𝕍𝕌 u))} {C : ℂForm Δ}
      → Ax Δ (CEr R) (∃· u A)
      → ⊢ (seq (ℂe (ℂv Δ (𝕍𝕌 u)) A (↑ᵣ₀ R)) (↑CE₀ T) (↑₀ C))
      → ⊢ (seq Δ T C)
  -- ruleIn: a hypothesis over an interval i holds at each point r of i
  InL : {Δ : ℂ₀} {i : ℂInterval Δ} {r : ℂRes Δ} {T : ℂCE Δ} {A C : ℂForm Δ}
      → Ax Δ (CEi i) A
      → ⊢ (useq Δ (interval r i))
      → ⊢ (seq (ℂe Δ A r) T C)
      → ⊢ (seq Δ T C)
  -- membership in an explicit list of agents
  ∈I  : {Δ : ℂ₀} {r : ℂRes Δ} {a : Agent (ℂtxt Δ)} {l : List (Agent (ℂtxt Δ))}
      → a ∈ l → ⊢ (rseq Δ r (𝔸 (a ∈ₐ agentsL l)))
  -- □ (always), as rule□R and rule□L; □L is classical and carries EM
  □I  : {Δ : ℂ₀} {r : ℂRes Δ} {A : ℂForm Δ}
      → ⊢ (rseq (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕣₀ (↑₀ A))
      → ⊢ (rseq Δ r (□ A))
  □L  : {Δ : ℂ₀} {r t T : ℂRes Δ} {A C : ℂForm Δ}
      → EMT
      → Ax Δ (CEr r) (□ A)
      → ⊢ (useq Δ (r ⊑ t))
      → ⊢ (rseq (ℂe Δ A t) T C)
      → ⊢ (rseq Δ T C)

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
sound M (ＹI {Δ} {r} {r₁} {A} d₁ d₂)        = ruleＹR-sat M Δ r r₁ A (sound M d₁ , sound M d₂ , lift tt)
sound M (ＳI {Δ} {r} {r₁} {A} {B} d₁ d₂ d₃) = ruleＳR-sat M Δ r r₁ A B (sound M d₁ , sound M d₂ , sound M d₃ , lift tt)
sound M (ＢI {Δ} {r} {A} d)                 = ＢR-sat M Δ r A (sound M d)
sound M (ＯL {Δ} {r} {T} {A} {C} p d) = λ s satΔ →
  ＯL-sat M Δ r T A C (sound M d) s satΔ (Ax-sat (M ≔ₛ s) p satΔ)
sound M (ＹL {Δ} {r} {T} {A} {C} p d) = λ s satΔ →
  ＹL-sat M Δ r T A C (sound M d) s satΔ (Ax-sat (M ≔ₛ s) p satΔ)
sound M (ＵL {Δ} {r} {T} {A} {B} {C} p d) = λ s satΔ →
  ＵL-sat M Δ r T A B C (sound M d) s satΔ (Ax-sat (M ≔ₛ s) p satΔ)
sound M (ＳL {Δ} {r} {T} {A} {B} {C} p d) = λ s satΔ →
  ＳL-sat M Δ r T A B C (sound M d) s satΔ (Ax-sat (M ≔ₛ s) p satΔ)
sound M (ＢL {Δ} {r} {r₁} {T} {A} {C} p d₁ d₂) = λ s satΔ →
  sound M d₂ s (satΔ , Ax-sat (M ≔ₛ s) p satΔ (⟦ r₁ ⟧ᵣ s) (lower (sound M d₁ s satΔ)))
-- The comparison rules reuse the lemmas of RulesTemp, stated there at a
-- resource label R: an unlabelled comparison has the same meaning, so we
-- take R = 𝟎.
sound M (⊑refl {Δ} {a})               = rule⊑-refl-sat M Δ a 𝟎 (lift tt)
sound M (⊑𝟎 {Δ} {a})                  = rule𝟎min-sat M Δ 𝟎 a (lift tt)
sound M (⊑trans {Δ} {a} {b} {c} d e)  = rule⊑-trans-sat M Δ a b c 𝟎 (sound M d , sound M e , lift tt)
sound M (⊑⊏trans {Δ} {a} {b} {c} d e) = rule⊏-transᵣ-sat M Δ a b c 𝟎 (sound M d , sound M e , lift tt)
sound M (⊏⊑trans {Δ} {a} {b} {c} d e) = λ s satΔ →
  lift (≺-≼-trans (lower (sound M d s satΔ)) (lower (sound M e s satΔ)))
sound M (◁⊑ {Δ} {a} {b} d)            = ◁⇒⊑-sat M Δ 𝟎 a b (sound M d , lift tt)
sound M (◁⊏ {Δ} {a} {b} d)            = ◁⇒⊏-sat M Δ 𝟎 a b (sound M d , lift tt)
sound M (⊏⊑ {Δ} {a} {b} d)            = λ s satΔ → lift (≺→≼ (lower (sound M d s satΔ)))
sound M (＝⊑ {Δ} {a} {b} d)            = rule＝→⊑-sat M Δ a b 𝟎 (sound M d , lift tt)
sound M (⊑⋆ {Δ} {a₁} {a₂} {b₁} {b₂} d e) =
  rule⊑-⋆-cong-sat M Δ a₁ a₂ b₁ b₂ 𝟎 (sound M d , sound M e , lift tt)
sound M (⊑⋆ₗ {Δ} {a} {b} {t} d)       = derived-rule-⊑⋆ₗ-sat M Δ t b a (sound M d , lift tt)
sound M (⊑⋆ᵣ {Δ} {a} {b} {t} d)       = derived-rule-⊑⋆ᵣ-sat M Δ t b a (sound M d , lift tt)
sound M (＝refl {Δ} {a})               = rule＝-refl-sat M Δ a CEu (lift tt)
sound M (＝sym {Δ} {a} {b} d)          = rule＝-sym-sat M Δ a b 𝟎 (sound M d , lift tt)
sound M (＝trans {Δ} {a} {b} {c} d e)  = rule＝-trans-sat M Δ a b c 𝟎 (sound M d , sound M e , lift tt)
sound M (＝⋆ {Δ} {a₁} {a₂} {b₁} {b₂} d e) =
  rule＝-⋆-cong-sat M Δ a₁ a₂ b₁ b₂ 𝟎 (sound M d , sound M e , lift tt)
sound M (＝assoc {Δ} {a} {b} {c})      = rule＝-⋆-assoc-sat M Δ a b c 𝟎 (lift tt)
sound M (＝comm {Δ} {a} {b})           = rule＝-⋆-sym-sat M Δ a b CEu (lift tt)
sound M (＝lid {Δ} {a})                = rule-left-id-sat M Δ 𝟎 a (lift tt)
sound M (∀I {Δ} {T} {u} {A} d) = rule∀I-sat M Δ T u A (sound M d , lift tt)
-- as rule∀L-sat, with the hypothesis anywhere in Δ
sound M (∀L {Δ} {R} {T} {u} {A} {C} p v d) = λ s satΔ →
  sound M d s (satΔ , sat-ctxt-annot→sub A R v
                        (sat-ctxt-annot∀→ u A R (M ≔ₛ s) (Ax-sat (M ≔ₛ s) p satΔ)
                                          (⟦ 𝕍𝕌 u ، v ⟧c· (M ≔ₛ s))))
sound M (∃R {Δ} {T} {u} {A} v d) = rule∃R-sat M Δ T u A v (sound M d , lift tt)
sound M (∃L {Δ} {R} {T} {u} {A} {C} p d) = λ s satΔ →
  rule∃L-sat M Δ T R u A C (sound M d , lift tt) s (satΔ , Ax-sat (M ≔ₛ s) p satΔ)
-- as ruleIn-sat, with the hypothesis anywhere in Δ and any label T
sound M (InL {Δ} {i} {r} {T} {A} {C} p d₁ d₂) = λ s satΔ →
  sound M d₂ s (satΔ , Ax-sat (M ≔ₛ s) p satΔ (⟦ r ⟧ᵣ s)
                         (⊨interval→inter-cond M Δ s (Model.w M) r i (sound M d₁ s satΔ)))
sound M (∈I {Δ} {r} {a} {l} p) = λ s satΔ → lift (∈-map⁺ (λ j → ⟦ j ⟧ᵢ _) p)
sound M (□I {Δ} {r} {A} d) = rule□R-sat M Δ r A (sound M d , lift tt)
sound M (□L {Δ} {r} {t} {T} {A} {C} em p dc d) = λ s satΔ →
  RulesClassical.rule□L-sat 𝔻 W em M Δ r t T A C
    ((λ s′ sat′ → sound M d s′ (proj₁ (proj₁ sat′) , proj₂ sat′)) ,
     sound M dc , lift tt)
    s (satΔ , Ax-sat (M ≔ₛ s) p satΔ)
-- ruleＦL with the hypothesis anywhere in Δ
sound M (ＦL {Δ} {r} {T} {A} {C} p d) = λ s satΔ →
  ruleＦL-sat M Δ r T A C (sound M d , lift tt) s (satΔ , Ax-sat (M ≔ₛ s) p satΔ)


-- ===========================================================================
-- PROOF SEARCH: search⊢ and Prove
--
-- Shared by both approaches to Agda-level formulas (A : Form Γ):
--   * SUBST APPROACH (Plug.lagda): search on object variables
--     (var 0 →· var 0) and instantiate with plug-⊢.
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

infixr 1 _orelse_

-- ---------------------------------------------------------------------------
-- Witnesses for the temporal left rules.  ＯL, ＹL, ＵL and ＳL keep their
-- hypothesis, so they are skipped when the context already contains, at a
-- point label, a comparison giving a time point w for the hypothesis together
-- with its body at w (r ◁ w and A^w for (Ｏ A)^r, r ⊑ w and B^w for
-- (A Ｕ B)^r, ...).  This keeps them from firing again on the copy of the
-- hypothesis under the new binder.

isAx : (Δ : ℂ₀) (R : ℂCE Δ) (A : ℂForm Δ) → Bool
isAx Δ R A with decAx Δ R A
... | inj₁ _ = true
... | inj₂ _ = false

-- the time point a comparison provides for r: r ◁ w (selＯ), w ◁ r (selＹ),
-- r ⊑ w (selＵ), w ⊑ r (selＳ)
selＯ selＹ selＵ selＳ : {Δ : ℂ₀} → ℂRes Δ → ℂForm Δ → Maybe (ℂRes Δ)
selＯ r (x ⟨ PR ⟩ w) with Res-dec x r
... | inj₁ _ = just w
... | inj₂ _ = nothing
selＯ r _ = nothing
selＹ r (w ⟨ PR ⟩ x) with Res-dec x r
... | inj₁ _ = just w
... | inj₂ _ = nothing
selＹ r _ = nothing
selＵ r (x ⟨ LE ⟩ w) with Res-dec x r
... | inj₁ _ = just w
... | inj₂ _ = nothing
selＵ r _ = nothing
selＳ r (w ⟨ LE ⟩ x) with Res-dec x r
... | inj₁ _ = just w
... | inj₂ _ = nothing
selＳ r _ = nothing

witnessed : (Δ : ℂ₀) (sel : ℂForm Δ → Maybe (ℂRes Δ)) (A : ℂForm Δ) → List (ℂhyp Δ) → Bool
witnessed Δ sel A [] = false
witnessed Δ sel A ((R , F , _) ∷ l) with decPointCE R | sel F
... | inj₁ _ | just w = isAx Δ (CEr w) A ∨ᵇ witnessed Δ sel A l
... | _      | _      = witnessed Δ sel A l

-- The terms tried for ∀L and ∃R: the variables of sort u in scope.
idxs : (Γ : Ctxt) (w : 𝕍) → List (∈Ctxt w Γ)
idxs ⟨⟩      w = []
idxs (Γ ، v) w with 𝕍-dec v w
... | inj₁ refl = ∈Ctxt0 Γ ∷ Data.List.map (∈CtxtS v) (idxs Γ w)
... | inj₂ _    = Data.List.map (∈CtxtS v) (idxs Γ w)

terms : (Δ : ℂ₀) (u : 𝕌) → List (ℂ⟦𝕌⟧ Δ u)
terms Δ u = Data.List.map (CSub-var {ℂtxt Δ} {𝕍𝕌 u}) (idxs (ℂtxt Δ) (𝕍𝕌 u))

-- ∃L keeps its hypothesis: skip it if some term already witnesses it
∃witnessed : (Δ : ℂ₀) (R : ℂCE Δ) (u : 𝕌) (A : ℂForm (ℂv Δ (𝕍𝕌 u))) → List (ℂ⟦𝕌⟧ Δ u) → Bool
∃witnessed Δ R u A []      = false
∃witnessed Δ R u A (v ∷ l) = isAx Δ R (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) ∨ᵇ ∃witnessed Δ R u A l

-- a comparison hypothesis at any point label can be used unlabelled (cmpR)
cmpAx : {Δ : ℂ₀} {R : ℂCE Δ} {a b : ℂRes Δ} {c : Comparison}
      → pointCE R → Ax Δ R (a ⟨ c ⟩ b) → ⊢ (useq Δ (a ⟨ c ⟩ b))
cmpAx ptU     p = ax p
cmpAx (ptR r) p = cmpR (ptR r) (ax p)

-- ---------------------------------------------------------------------------
-- Comparison prover.
--
-- Proves unlabelled comparisons a ⊑ b, a ⊏ b and a ＝ b from the comparison
-- hypotheses of the context (at point labels), with ⊑refl, ⊑𝟎, transitivity
-- (chaining forward from a through the hypotheses), ◁ ⇒ ⊏ ⇒ ⊑, ＝ ⇒ ⊑,
-- congruence of ⋆, a ⊑ b ⋆ t / a ⊑ t ⋆ b, and the monoid equations
-- (associativity, commutativity, left identity) at the top of a term.
-- Bounded by cmp-fuel, independently of the search's fuel.
-- ---------------------------------------------------------------------------

cmp-fuel : ℕ
cmp-fuel = 4

-- a known comparison a ⟨ c ⟩ b with its derivation
Fact : (Δ : ℂ₀) → Comparison → Set₂
Fact Δ c = Σ (ℂRes Δ) (λ a → Σ (ℂRes Δ) (λ b → ⊢ (useq Δ (a ⟨ c ⟩ b))))

-- the hypotheses, as ⊑ facts (from ⊑, ⊏, ◁ and both directions of ＝),
-- ⊏ facts (from ⊏ and ◁) and ＝ facts (both directions)
record Facts (Δ : ℂ₀) : Set₂ where
  constructor facts
  field
    le : List (Fact Δ LE)
    lt : List (Fact Δ LT)
    eq : List (Fact Δ EQ)
open Facts

addFact : {Δ : ℂ₀} {a b : ℂRes Δ} (c : Comparison) → ⊢ (useq Δ (a ⟨ c ⟩ b)) → Facts Δ → Facts Δ
addFact {Δ} {a} {b} LE d (facts l₁ l₂ l₃) = facts ((a , b , d) ∷ l₁) l₂ l₃
addFact {Δ} {a} {b} LT d (facts l₁ l₂ l₃) = facts ((a , b , ⊏⊑ d) ∷ l₁) ((a , b , d) ∷ l₂) l₃
addFact {Δ} {a} {b} PR d (facts l₁ l₂ l₃) = facts ((a , b , ◁⊑ d) ∷ l₁) ((a , b , ◁⊏ d) ∷ l₂) l₃
addFact {Δ} {a} {b} EQ d (facts l₁ l₂ l₃) =
  facts ((a , b , ＝⊑ d) ∷ (b , a , ＝⊑ (＝sym d)) ∷ l₁) l₂ ((a , b , d) ∷ (b , a , ＝sym d) ∷ l₃)

factsOf : (Δ : ℂ₀) → List (ℂhyp Δ) → Facts Δ
factsOf Δ [] = facts [] [] []
factsOf Δ ((R , (a ⟨ c ⟩ b) , p) ∷ l) with decPointCE R
... | inj₁ pt = addFact c (cmpAx pt p) (factsOf Δ l)
... | inj₂ _  = factsOf Δ l
factsOf Δ (_ ∷ l) = factsOf Δ l

ctxFacts : (Δ : ℂ₀) → Facts Δ
ctxFacts Δ = factsOf Δ (ℂhyps Δ)

findFact : {Δ : ℂ₀} {c : Comparison} → List (Fact Δ c) → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⟨ c ⟩ b)))
findFact [] a b = nothing
findFact ((x , y , d) ∷ l) a b with Res-dec x a | Res-dec y b
... | inj₁ refl | inj₁ refl = just d
... | _         | _         = findFact l a b

leZero : {Δ : ℂ₀} (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊑ b)))
leZero 𝟎 b = just ⊑𝟎
leZero _ _ = nothing

-- 𝟎 ⋆ a ＝ a, a ⋆ b ＝ b ⋆ a, a ⋆ (b ⋆ c) ＝ (a ⋆ b) ⋆ c
eqAx : {Δ : ℂ₀} (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ＝ b)))
eqAx (𝟎 ⋆ x) b with Res-dec x b
... | inj₁ refl = just ＝lid
... | inj₂ _    = nothing
eqAx (x ⋆ (y ⋆ z)) b with Res-dec b ((x ⋆ y) ⋆ z)
... | inj₁ refl = just ＝assoc
... | inj₂ _ with Res-dec b ((y ⋆ z) ⋆ x)
...   | inj₁ refl = just ＝comm
...   | inj₂ _    = nothing
eqAx (x ⋆ y) b with Res-dec b (y ⋆ x)
... | inj₁ refl = just ＝comm
... | inj₂ _    = nothing
eqAx _ _ = nothing

proveLE  : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊑ b)))
proveLE′ : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊑ b)))
proveLT  : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊏ b)))
proveLT′ : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊏ b)))
proveEQ  : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ＝ b)))
proveEQ′ : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ＝ b)))
leR      : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊑ b)))
leCong   : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊑ b)))
-- a ⊑ x ⋆ (y ⋆ z) from a ⊑ (x ⋆ y) ⋆ z
leAssoc  : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊑ b)))
eqCong   : (k : ℕ) (Δ : ℂ₀) → Facts Δ → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ＝ b)))
-- chain through a fact a ⟨c⟩ m (m ≠ a), then prove m ⟨c′⟩ b
transLE  : (k : ℕ) (Δ : ℂ₀) → Facts Δ → List (Fact Δ LE) → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊑ b)))
transLT₁ : (k : ℕ) (Δ : ℂ₀) → Facts Δ → List (Fact Δ LE) → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊏ b)))
transLT₂ : (k : ℕ) (Δ : ℂ₀) → Facts Δ → List (Fact Δ LT) → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ⊏ b)))
transEQ  : (k : ℕ) (Δ : ℂ₀) → Facts Δ → List (Fact Δ EQ) → (a b : ℂRes Δ) → Maybe (⊢ (useq Δ (a ＝ b)))

proveLE k Δ F a b with Res-dec a b
... | inj₁ refl = just ⊑refl
... | inj₂ _    = leZero a b orelse findFact (le F) a b orelse proveLE′ k Δ F a b

proveLE′ zero    Δ F a b = nothing
proveLE′ (suc k) Δ F a b =
  leR k Δ F a b orelse leCong k Δ F a b orelse transLE k Δ F (le F) a b
  orelse mmap ＝⊑ (proveEQ k Δ F a b) orelse leAssoc k Δ F a b

leR k Δ F a (b₁ ⋆ b₂) = mmap ⊑⋆ₗ (proveLE k Δ F a b₁) orelse mmap ⊑⋆ᵣ (proveLE k Δ F a b₂)
leR k Δ F a _         = nothing

leCong k Δ F (a₁ ⋆ a₂) (b₁ ⋆ b₂) with proveLE k Δ F a₁ b₁
... | nothing = nothing
... | just d₁ = mmap (⊑⋆ d₁) (proveLE k Δ F a₂ b₂)
leCong k Δ F _ _ = nothing

leAssoc k Δ F a (x ⋆ (y ⋆ z)) = mmap (λ d → ⊑trans d (＝⊑ (＝sym ＝assoc))) (proveLE k Δ F a ((x ⋆ y) ⋆ z))
leAssoc k Δ F a _             = nothing

transLE k Δ F [] a b = nothing
transLE k Δ F ((x , m , d) ∷ l) a b with Res-dec x a | Res-dec m a
... | inj₁ refl | inj₂ _ = mmap (⊑trans d) (proveLE k Δ F m b) orelse transLE k Δ F l a b
... | _         | _      = transLE k Δ F l a b

proveLT k Δ F a b = findFact (lt F) a b orelse proveLT′ k Δ F a b

proveLT′ zero    Δ F a b = nothing
proveLT′ (suc k) Δ F a b = transLT₁ k Δ F (le F) a b orelse transLT₂ k Δ F (lt F) a b

transLT₁ k Δ F [] a b = nothing
transLT₁ k Δ F ((x , m , d) ∷ l) a b with Res-dec x a | Res-dec m a
... | inj₁ refl | inj₂ _ = mmap (⊑⊏trans d) (proveLT k Δ F m b) orelse transLT₁ k Δ F l a b
... | _         | _      = transLT₁ k Δ F l a b

transLT₂ k Δ F [] a b = nothing
transLT₂ k Δ F ((x , m , d) ∷ l) a b with Res-dec x a
... | inj₁ refl = mmap (⊏⊑trans d) (proveLE k Δ F m b) orelse transLT₂ k Δ F l a b
... | inj₂ _    = transLT₂ k Δ F l a b

proveEQ k Δ F a b with Res-dec a b
... | inj₁ refl = just ＝refl
... | inj₂ _    = findFact (eq F) a b orelse eqAx a b orelse mmap ＝sym (eqAx b a)
                  orelse proveEQ′ k Δ F a b

proveEQ′ zero    Δ F a b = nothing
proveEQ′ (suc k) Δ F a b = eqCong k Δ F a b orelse transEQ k Δ F (eq F) a b

eqCong k Δ F (a₁ ⋆ a₂) (b₁ ⋆ b₂) with proveEQ k Δ F a₁ b₁
... | nothing = nothing
... | just d₁ = mmap (＝⋆ d₁) (proveEQ k Δ F a₂ b₂)
eqCong k Δ F _ _ = nothing

transEQ k Δ F [] a b = nothing
transEQ k Δ F ((x , m , d) ∷ l) a b with Res-dec x a | Res-dec m a
... | inj₁ refl | inj₂ _ = mmap (＝trans d) (proveEQ k Δ F m b) orelse transEQ k Δ F l a b
... | _         | _      = transEQ k Δ F l a b

-- ◁ is only taken from the hypotheses (search⊢-cmp)
proveCmp : (Δ : ℂ₀) (a b : ℂRes Δ) (c : Comparison) → Maybe (⊢ (useq Δ (a ⟨ c ⟩ b)))
proveCmp Δ a b LE = proveLE cmp-fuel Δ (ctxFacts Δ) a b
proveCmp Δ a b LT = proveLT cmp-fuel Δ (ctxFacts Δ) a b
proveCmp Δ a b EQ = proveEQ cmp-fuel Δ (ctxFacts Δ) a b
proveCmp Δ a b PR = nothing

-- an unlabelled comparison holds at any label
cmpAt : {Δ : ℂ₀} (T : ℂCE Δ) {a b : ℂRes Δ} {c : Comparison}
      → ⊢ (useq Δ (a ⟨ c ⟩ b)) → ⊢ (seq Δ T (a ⟨ c ⟩ b))
cmpAt CEu d = d
cmpAt T   d = cmpR ptU d

-- r ∈ i, with the comparison prover
proveIn : (Δ : ℂ₀) (r : ℂRes Δ) (i : ℂInterval Δ) → Maybe (⊢ (useq Δ (interval r i)))
proveIn Δ r i = go i
  where
  both : {F G : ℂForm Δ} → Maybe (⊢ (useq Δ F)) → Maybe (⊢ (useq Δ G)) → Maybe (⊢ (useq Δ (F ∧· G)))
  both (just d) (just e) = just (∧I d e)
  both _        _        = nothing

  go : (i : ℂInterval Δ) → Maybe (⊢ (useq Δ (interval r i)))
  go ［ a , b ］ = both (proveCmp Δ a r LE) (proveCmp Δ r b LE)
  go ［ a , b ） = both (proveCmp Δ a r LE) (proveCmp Δ r b LT)
  go （ a , b ］ = both (proveCmp Δ a r LT) (proveCmp Δ r b LE)
  go （ a , b ） = both (proveCmp Δ a r LT) (proveCmp Δ r b LT)

memRes : {Γ : Ctxt} → Res Γ → List (Res Γ) → Bool
memRes r []      = false
memRes r (x ∷ l) with Res-dec r x
... | inj₁ _ = true
... | inj₂ _ = memRes r l

nubRes : {Γ : Ctxt} → List (Res Γ) → List (Res Γ)
nubRes []      = []
nubRes (x ∷ l) with memRes x l
... | true  = nubRes l
... | false = x ∷ nubRes l

-- points tried for InL on a hypothesis over i: the goal's label, the
-- endpoints of i, and the time points of the comparison hypotheses
inCands : (Δ : ℂ₀) (T : ℂCE Δ) (i : ℂInterval Δ) → List (ℂRes Δ)
inCands Δ T i = nubRes (lbl T (ends i (pts (le (ctxFacts Δ)))))
  where
  lbl : ℂCE Δ → List (ℂRes Δ) → List (ℂRes Δ)
  lbl (CEr t) l = t ∷ l
  lbl _       l = l

  ends : ℂInterval Δ → List (ℂRes Δ) → List (ℂRes Δ)
  ends ［ a , b ］ l = a ∷ b ∷ l
  ends ［ a , b ） l = a ∷ b ∷ l
  ends （ a , b ］ l = a ∷ b ∷ l
  ends （ a , b ） l = a ∷ b ∷ l

  pts : List (Fact Δ LE) → List (ℂRes Δ)
  pts []                = []
  pts ((a , b , _) ∷ l) = a ∷ b ∷ pts l

-- the left/right ends of ⊑ facts, and the resource labels of hypotheses,
-- each put in front of a given list
lhsF rhsF : {Δ : ℂ₀} → List (Fact Δ LE) → List (ℂRes Δ) → List (ℂRes Δ)
lhsF []                k = k
lhsF ((m , _ , _) ∷ l) k = m ∷ lhsF l k
rhsF []                k = k
rhsF ((_ , m , _) ∷ l) k = m ∷ rhsF l k

hypLbls : {Δ : ℂ₀} → List (ℂhyp Δ) → List (ℂRes Δ) → List (ℂRes Δ)
hypLbls []                    k = k
hypLbls ((CEr t , _ , _) ∷ l) k = t ∷ hypLbls l k
hypLbls (_ ∷ l)               k = hypLbls l k

-- removes duplicates, keeping first occurrences (so the order is kept)
nubFst : {Γ : Ctxt} → List (Res Γ) → List (Res Γ) → List (Res Γ)
nubFst seen []      = []
nubFst seen (x ∷ l) with memRes x seen
... | true  = nubFst seen l
... | false = x ∷ nubFst (x ∷ seen) l

-- witnesses for ＵI (r ⊑ w) and ＳI (w ⊑ r): first the time points the
-- comparison hypotheses lead to and r itself (as before), then the labels
-- of the hypotheses and the other ends of the comparison hypotheses
Ｕcands Ｓcands : (Δ : ℂ₀) (r : ℂRes Δ) → List (ℂRes Δ)
Ｕcands Δ r = nubFst [] (rhsF (le (ctxFacts Δ)) (r ∷ hypLbls (ℂhyps Δ) (lhsF (le (ctxFacts Δ)) [])))
Ｓcands Δ r = nubFst [] (lhsF (le (ctxFacts Δ)) (r ∷ hypLbls (ℂhyps Δ) (rhsF (le (ctxFacts Δ)) [])))

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


-- membership of an agent in an explicit list
findAg : {Γ : Ctxt} (a : Agent Γ) (l : List (Agent Γ)) → Maybe (a ∈ l)
findAg a []      = nothing
findAg a (x ∷ l) with Agent-dec a x
... | inj₁ refl = just (here refl)
... | inj₂ _    = mapM there (findAg a l)
  where
  mapM : {A B : Set} → (A → B) → Maybe A → Maybe B
  mapM f (just x) = just (f x)
  mapM f nothing  = nothing

-- constants occurring in formulas (agents, data, closed lists of agents)
nubℕ : List ℕ → List ℕ → List ℕ
nubℕ seen []      = []
nubℕ seen (x ∷ l) with memℕ x seen
  where
  memℕ : ℕ → List ℕ → Bool
  memℕ x []      = false
  memℕ x (y ∷ l) with x ≟ y
  ... | yes _ = true
  ... | no  _ = memℕ x l
... | true  = nubℕ seen l
... | false = x ∷ nubℕ (x ∷ seen) l

record Consts : Set where
  constructor mkConsts
  field
    cAg  : List agent
    cDa  : List 𝔻
    cAgs : List (List agent)

module _ where
  open Consts
  agC : {Γ : Ctxt} → Agent Γ → Consts → Consts
  agC (agentC k) c = record c { cAg = k ∷ cAg c }
  agC (agentV _) c = c

  closedL : {Γ : Ctxt} → List (Agent Γ) → Maybe (List agent)
  closedL []             = just []
  closedL (agentC k ∷ l) with closedL l
  ... | just l′ = just (k ∷ l′)
  ... | nothing = nothing
  closedL (agentV _ ∷ l) = nothing

  agLC : {Γ : Ctxt} → List (Agent Γ) → Consts → Consts
  agLC []      c = c
  agLC (a ∷ l) c = agC a (agLC l c)

  agsC : {Γ : Ctxt} → Agents Γ → Consts → Consts
  agsC (agentsV _) c = c
  agsC (agentsL l) c with closedL l
  ... | just l′ = agLC l (record c { cAgs = l′ ∷ cAgs c })
  ... | nothing = agLC l c

  daC : {Γ : Ctxt} → Data Γ → Consts → Consts
  daC (dataC d) c = record c { cDa = d ∷ cDa c }
  daC (dataV _) c = c

  atC : {Γ : Ctxt} → Atom Γ → Consts → Consts
  atC (atProp _)                    c = c
  atC (atAction (ActSend p a A))    c = daC p (agC a (agsC A c))
  atC (atEvent (EvtReceive p a b))  c = daC p (agC a (agC b c))
  atC (atEvent (EvtInternal a d))   c = agC a (daC d c)
  atC (atCorrect (FaultCorrect a b)) c = agC a (agC b c)

  setC : {Γ : Ctxt} → SetAtom Γ → Consts → Consts
  setC (a ∈ₐ A)     c = agC a (agsC A c)
  setC (∣ A ∣ₛ＝ n) c = agsC A c

  formC : {Γ : Ctxt} → Form Γ → Consts → Consts
  formC (𝕒 x)       c = atC x c
  formC (var x)     c = c
  formC ⊤·          c = c
  formC ⊥·          c = c
  formC (f ∧· g)    c = formC f (formC g c)
  formC (f ∨· g)    c = formC f (formC g c)
  formC (f →· g)    c = formC f (formC g c)
  formC (∀· u f)    c = formC f c
  formC (∃· u f)    c = formC f c
  formC (𝔸 A)       c = setC A c
  formC (f Ｕ g)    c = formC f (formC g c)
  formC (Ｏ f)      c = formC f c
  formC (f Ｓ g)    c = formC f (formC g c)
  formC (Ｙ f)      c = formC f c
  formC (Ｂ f)      c = formC f c
  formC (Ｆ f)      c = formC f c
  formC (_ ⟨ _ ⟩ _) c = c

  hypsC : {Δ : ℂ₀} → List (ℂhyp Δ) → Consts → Consts
  hypsC []                  c = c
  hypsC ((_ , f , _) ∷ l)   c = formC f (hypsC l c)

-- the terms tried for ∀L and ∃R: the variables of sort u in scope, then the
-- constants occurring in the goal and the hypotheses, and for agent sets the
-- singletons of the agents tried
termsC : (Δ : ℂ₀) (C : ℂForm Δ) (u : 𝕌) → List (ℂ⟦𝕌⟧ Δ u)
termsC Δ C u = terms Δ u Data.List.++ more u
  where
  K : Consts
  K = formC C (hypsC (ℂhyps Δ) (mkConsts [] [] []))
  ags : List agent
  ags = nubℕ [] (Consts.cAg K)
  more : (u : 𝕌) → List (ℂ⟦𝕌⟧ Δ u)
  more 𝕌Agent  = Data.List.map agentC ags
  more 𝕌Data   = Data.List.map dataC (nubℕ [] (Consts.cDa K))
  more 𝕌Agents = Data.List.map (λ v → agentsL (v ∷ [])) (terms Δ 𝕌Agent Data.List.++ Data.List.map agentC ags)
                 Data.List.++ Data.List.map (λ l → agentsL (Data.List.map agentC l)) (Consts.cAgs K)
  more 𝕌Prop   = []

-- ∀L by matching.  For a hypothesis ∀x₁…∀xₖ.B, the atoms of B are matched
-- against the atoms of the goal and of the hypotheses, and the consistent
-- assignments of x₁…xₖ that cover the most variables are used to instantiate
-- all of the ∀s at once.  Terms are compared in a flat form, with variables
-- as de Bruijn positions, and converted back with toTerm.  The matcher only
-- proposes terms: each ∀L step is still a ⊢ step.
module Match where
  data FA : Set where
    fav : ℕ → FA  -- variable of the context of the sequent
    fac : ℕ → FA  -- constant
    fap : ℕ → FA  -- pattern variable (0 = innermost ∀ of the prefix)
    fax : FA      -- bound inside the formula (wildcard in patterns)

  data FL : Set where
    flv : ℕ → FL
    fll : List FA → FL
    flp : ℕ → FL
    flx : FL

  data FD : Set where
    fdv : ℕ → FD
    fdc : ℕ → FD
    fdp : ℕ → FD
    fdx : FD

  data FT : Set where
    ftA : FA → FT
    ftL : FL → FT
    ftD : FD → FT
    ftP : FD → FT   -- atomic propositions, same shape as data

  data FAt : Set where
    fprop : FD → FAt
    fsend : FD → FA → FL → FAt
    frecv : FD → FA → FA → FAt
    fint  : FA → FD → FAt
    fcorr : FA → FA → FAt
    fmem  : FA → FL → FAt
    fcard : FL → ℕ → FAt

  data VK : Set where
    vkO : ℕ → VK
    vkP : ℕ → VK
    vkX : VK

  -- a variable at position j, under m binders of the formula and k binders
  -- of the prefix
  classify : (m k j : ℕ) → VK
  classify (suc m) k       zero    = vkX
  classify (suc m) k       (suc j) = classify m k j
  classify zero    zero    j       = vkO j
  classify zero    (suc k) zero    = vkP 0
  classify zero    (suc k) (suc j) with classify zero k j
  ... | vkP i = vkP (suc i)
  ... | x     = x

  idx : {v : 𝕍} {Γ : Ctxt} → ∈Ctxt v Γ → ℕ
  idx (∈Ctxt0 _)   = 0
  idx (∈CtxtS _ i) = suc (idx i)

  flA : {Γ : Ctxt} (m k : ℕ) → Agent Γ → FA
  flA m k (agentC c) = fac c
  flA m k (agentV i) with classify m k (idx i)
  ... | vkO j = fav j
  ... | vkP j = fap j
  ... | vkX   = fax

  flAs : {Γ : Ctxt} (m k : ℕ) → List (Agent Γ) → List FA
  flAs m k []      = []
  flAs m k (a ∷ l) = flA m k a ∷ flAs m k l

  flL : {Γ : Ctxt} (m k : ℕ) → Agents Γ → FL
  flL m k (agentsL l) = fll (flAs m k l)
  flL m k (agentsV i) with classify m k (idx i)
  ... | vkO j = flv j
  ... | vkP j = flp j
  ... | vkX   = flx

  flD : {Γ : Ctxt} (m k : ℕ) → Data Γ → FD
  flD m k (dataC c) = fdc c
  flD m k (dataV i) with classify m k (idx i)
  ... | vkO j = fdv j
  ... | vkP j = fdp j
  ... | vkX   = fdx

  flP : {Γ : Ctxt} (m k : ℕ) → AtomProp Γ → FD
  flP m k (atomPropC c) = fdc c
  flP m k (atomPropV i) with classify m k (idx i)
  ... | vkO j = fdv j
  ... | vkP j = fdp j
  ... | vkX   = fdx

  flAt : {Γ : Ctxt} (m k : ℕ) → Atom Γ → FAt
  flAt m k (atProp x)                    = fprop (flP m k x)
  flAt m k (atAction (ActSend p a A))    = fsend (flD m k p) (flA m k a) (flL m k A)
  flAt m k (atEvent (EvtReceive p a b))  = frecv (flD m k p) (flA m k a) (flA m k b)
  flAt m k (atEvent (EvtInternal a d))   = fint (flA m k a) (flD m k d)
  flAt m k (atCorrect (FaultCorrect a b)) = fcorr (flA m k a) (flA m k b)

  flSet : {Γ : Ctxt} (m k : ℕ) → SetAtom Γ → FAt
  flSet m k (a ∈ₐ A)     = fmem (flA m k a) (flL m k A)
  flSet m k (∣ A ∣ₛ＝ n) = fcard (flL m k A) n

  atomsF : {Γ : Ctxt} (m k : ℕ) → Form Γ → List FAt → List FAt
  atomsF m k (𝕒 x)       ac₀ = flAt m k x ∷ ac₀
  atomsF m k (𝔸 s)       ac₀ = flSet m k s ∷ ac₀
  atomsF m k (f ∧· g)    ac₀ = atomsF m k f (atomsF m k g ac₀)
  atomsF m k (f ∨· g)    ac₀ = atomsF m k f (atomsF m k g ac₀)
  atomsF m k (f →· g)    ac₀ = atomsF m k f (atomsF m k g ac₀)
  atomsF m k (f Ｕ g)    ac₀ = atomsF m k f (atomsF m k g ac₀)
  atomsF m k (f Ｓ g)    ac₀ = atomsF m k f (atomsF m k g ac₀)
  atomsF m k (∀· u f)    ac₀ = atomsF (suc m) k f ac₀
  atomsF m k (∃· u f)    ac₀ = atomsF (suc m) k f ac₀
  atomsF m k (Ｆ f)      ac₀ = atomsF (suc m) k f ac₀
  atomsF m k (Ｏ f)      ac₀ = atomsF m k f ac₀
  atomsF m k (Ｙ f)      ac₀ = atomsF m k f ac₀
  atomsF m k (Ｂ f)      ac₀ = atomsF m k f ac₀
  atomsF m k _           ac₀ = ac₀

  -- the number of leading ∀s, and the atoms of the body
  prefixLen : {Γ : Ctxt} → Form Γ → ℕ
  prefixLen (∀· u f) = suc (prefixLen f)
  prefixLen _        = 0

  patterns : {Γ : Ctxt} (k : ℕ) → Form Γ → List FAt
  patterns k (∀· u f) = patterns (suc k) f
  patterns k f        = atomsF 0 k f []

  -- equality
  eqA : FA → FA → Bool
  eqA (fav i) (fav j) = i ≡ᵇ j
  eqA (fac i) (fac j) = i ≡ᵇ j
  eqA _       _       = false

  eqAs : List FA → List FA → Bool
  eqAs []      []      = true
  eqAs (a ∷ l) (b ∷ k) with eqA a b
  ... | true  = eqAs l k
  ... | false = false
  eqAs _       _       = false

  eqL : FL → FL → Bool
  eqL (flv i) (flv j) = i ≡ᵇ j
  eqL (fll l) (fll k) = eqAs l k
  eqL _       _       = false

  eqD : FD → FD → Bool
  eqD (fdv i) (fdv j) = i ≡ᵇ j
  eqD (fdc i) (fdc j) = i ≡ᵇ j
  eqD _       _       = false

  eqT : FT → FT → Bool
  eqT (ftA a) (ftA b) = eqA a b
  eqT (ftL a) (ftL b) = eqL a b
  eqT (ftD a) (ftD b) = eqD a b
  eqT (ftP a) (ftP b) = eqD a b
  eqT _       _       = false

  -- usable target terms: closed, or variables of the sequent's context
  okA : FA → Bool
  okA (fav _) = true
  okA (fac _) = true
  okA _       = false

  okAs : List FA → Bool
  okAs []      = true
  okAs (a ∷ l) with okA a
  ... | true  = okAs l
  ... | false = false

  okL : FL → Bool
  okL (flv _) = true
  okL (fll l) = okAs l
  okL _       = false

  okD : FD → Bool
  okD (fdv _) = true
  okD (fdc _) = true
  okD _       = false

  -- assignments: one slot per variable of the prefix, innermost first
  Θ : Set
  Θ = List (Maybe FT)

  bind : ℕ → FT → Θ → Maybe Θ
  bind i       t []             = nothing
  bind zero    t (nothing ∷ θ)  = just (just t ∷ θ)
  bind zero    t (just t′ ∷ θ) with eqT t t′
  ... | true  = just (just t′ ∷ θ)
  ... | false = nothing
  bind (suc i) t (s ∷ θ) with bind i t θ
  ... | just θ′ = just (s ∷ θ′)
  ... | nothing = nothing

  _>>=ₘ_ : Maybe Θ → (Θ → Maybe Θ) → Maybe Θ
  just θ  >>=ₘ f = f θ
  nothing >>=ₘ f = nothing

  -- pattern against target
  uA : FA → FA → Θ → Maybe Θ
  uA fax     t       θ = just θ
  uA (fap i) t       θ with okA t
  ... | true  = bind i (ftA t) θ
  ... | false = nothing
  uA p       t       θ with eqA p t
  ... | true  = just θ
  ... | false = nothing

  uAs : List FA → List FA → Θ → Maybe Θ
  uAs []      []      θ = just θ
  uAs (p ∷ l) (t ∷ k) θ = uA p t θ >>=ₘ uAs l k
  uAs _       _       θ = nothing

  uL : FL → FL → Θ → Maybe Θ
  uL flx     t       θ = just θ
  uL (flp i) t       θ with okL t
  ... | true  = bind i (ftL t) θ
  ... | false = nothing
  uL (fll l) (fll k) θ = uAs l k θ
  uL p       t       θ with eqL p t
  ... | true  = just θ
  ... | false = nothing

  uD : (FD → FT) → FD → FD → Θ → Maybe Θ
  uD c fdx     t θ = just θ
  uD c (fdp i) t θ with okD t
  ... | true  = bind i (c t) θ
  ... | false = nothing
  uD c p       t θ with eqD p t
  ... | true  = just θ
  ... | false = nothing

  uAt : FAt → FAt → Θ → Maybe Θ
  uAt (fprop p)     (fprop q)     θ = uD ftP p q θ
  uAt (fsend p a A) (fsend q b B) θ = uD ftD p q θ >>=ₘ (λ θ → uA a b θ >>=ₘ uL A B)
  uAt (frecv p a b) (frecv q c d) θ = uD ftD p q θ >>=ₘ (λ θ → uA a c θ >>=ₘ uA b d)
  uAt (fint a p)    (fint b q)    θ = uA a b θ >>=ₘ uD ftD p q
  uAt (fcorr a b)   (fcorr c d)   θ = uA a c θ >>=ₘ uA b d
  uAt (fmem a A)    (fmem b B)    θ = uA a b θ >>=ₘ uL A B
  uAt (fcard A n)   (fcard B k)   θ with n ≡ᵇ k
  ... | true  = uL A B θ
  ... | false = nothing
  uAt _             _             θ = nothing

  eqS : Maybe FT → Maybe FT → Bool
  eqS nothing  nothing  = true
  eqS (just a) (just b) = eqT a b
  eqS _        _        = false

  eqΘ : Θ → Θ → Bool
  eqΘ []      []      = true
  eqΘ (a ∷ l) (b ∷ k) with eqS a b
  ... | true  = eqΘ l k
  ... | false = false
  eqΘ _       _       = false

  memΘ : Θ → List Θ → Bool
  memΘ θ []      = false
  memΘ θ (x ∷ l) with eqΘ θ x
  ... | true  = true
  ... | false = memΘ θ l

  nubΘ : List Θ → List Θ → List Θ
  nubΘ seen []      = []
  nubΘ seen (θ ∷ l) with memΘ θ seen
  ... | true  = nubΘ seen l
  ... | false = θ ∷ nubΘ (θ ∷ seen) l

  mapMaybe′ : (FAt → Maybe Θ) → List FAt → List Θ
  mapMaybe′ f []      = []
  mapMaybe′ f (t ∷ l) with f t
  ... | just θ  = θ ∷ mapMaybe′ f l
  ... | nothing = mapMaybe′ f l

  concatMap′ : (Θ → List Θ) → List Θ → List Θ
  concatMap′ f []      = []
  concatMap′ f (θ ∷ l) = f θ Data.List.++ concatMap′ f l

  -- each pattern atom is either matched against a target atom or skipped
  step : List FAt → FAt → List Θ → List Θ
  step ts p θs = nubΘ [] (concatMap′ (λ θ → θ ∷ mapMaybe′ (λ t → uAt p t θ) ts) θs)

  empties : ℕ → Θ
  empties zero    = []
  empties (suc k) = nothing ∷ empties k

  bound : Θ → ℕ
  bound []             = 0
  bound (just _ ∷ θ)   = suc (bound θ)
  bound (nothing ∷ θ)  = bound θ

  maxBound : List Θ → ℕ
  maxBound []      = 0
  maxBound (θ ∷ l) = bound θ ⊔ maxBound l

  withBound : ℕ → List Θ → List Θ
  withBound b []      = []
  withBound b (θ ∷ l) with bound θ ≡ᵇ b
  ... | true  = θ ∷ withBound b l
  ... | false = withBound b l

  -- the assignments for ∀· u A against the targets, outermost first;
  -- [] when nothing matches
  slot : ℕ → Θ → Maybe FT
  slot i       []      = nothing
  slot zero    (s ∷ θ) = s
  slot (suc i) (s ∷ θ) = slot i θ

  resolveL : Θ → FL → Maybe (List FA)
  resolveL θ (fll ts) with okAs ts
  ... | true  = just ts
  ... | false = nothing
  resolveL θ (flp i) with slot i θ
  ... | just (ftL (fll ts)) = just ts
  ... | _                   = nothing
  resolveL θ _       = nothing

  bindAll : ℕ → List FA → Θ → List Θ
  bindAll i []      θ = []
  bindAll i (t ∷ l) θ with bind i (ftA t) θ
  ... | just θ′ = θ′ ∷ bindAll i l θ
  ... | nothing = bindAll i l θ

  -- a pattern x ∈ₐ L with x unassigned and L a known list: x is taken
  -- from L (so that the antecedent x ∈ₐ L of the instance holds)
  expand1 : FAt → Θ → List Θ
  expand1 (fmem (fap i) A) θ with slot i θ | resolveL θ A
  ... | nothing | just ts with bindAll i ts θ
  ...   | []      = θ ∷ []
  ...   | θ′ ∷ θs = θ′ ∷ θs
  expand1 (fmem (fap i) A) θ | _ | _ = θ ∷ []
  expand1 _ θ = θ ∷ []

  expand : List FAt → Θ → List Θ
  expand []       θ = θ ∷ []
  expand (p ∷ ps) θ = concatMap′ (expand ps) (expand1 p θ)

  total : Θ → Bool
  total []            = true
  total (just _ ∷ θ)  = total θ
  total (nothing ∷ θ) = false

  totals : List Θ → List Θ
  totals []      = []
  totals (θ ∷ l) with total θ
  ... | true  = θ ∷ totals l
  ... | false = totals l

  best : List Θ → List Θ
  best θs with maxBound θs
  ... | zero  = []
  ... | suc b = Data.List.map Data.List.reverse (withBound (suc b) θs)

  assignments : {Γ : Ctxt} (A : Form Γ) → List FAt → List Θ
  assignments A ts =
    best (concatMap′ (expand (patterns 1 A))
           (Data.List.foldr (step ts) (empties (suc (prefixLen A)) ∷ []) (patterns 1 A)))

  -- the target atoms: the goal's and the hypotheses'
  targetsH : {Δ : ℂ₀} → List (ℂhyp Δ) → List FAt → List FAt
  targetsH []                  ac₀ = ac₀
  targetsH ((_ , f , _) ∷ l)   ac₀ = atomsF 0 0 f (targetsH l ac₀)

  targets : (Δ : ℂ₀) (C : ℂForm Δ) → List FAt
  targets Δ C = atomsF 0 0 C (targetsH (ℂhyps Δ) [])

  -- back to typed terms
  toVar : (Γ : Ctxt) (v : 𝕍) → ℕ → Maybe (∈Ctxt v Γ)
  toVar ⟨⟩      v j       = nothing
  toVar (Γ ، w) v zero    with 𝕍-dec w v
  ... | inj₁ refl = just (∈Ctxt0 Γ)
  ... | inj₂ _    = nothing
  toVar (Γ ، w) v (suc j) with toVar Γ v j
  ... | just i  = just (∈CtxtS w i)
  ... | nothing = nothing

  toAg : (Γ : Ctxt) → FA → Maybe (Agent Γ)
  toAg Γ (fac c) = just (agentC c)
  toAg Γ (fav j) with toVar Γ 𝕍Agent j
  ... | just i  = just (agentV i)
  ... | nothing = nothing
  toAg Γ _       = nothing

  toAgs : (Γ : Ctxt) → List FA → Maybe (List (Agent Γ))
  toAgs Γ []      = just []
  toAgs Γ (a ∷ l) with toAg Γ a | toAgs Γ l
  ... | just b | just k = just (b ∷ k)
  ... | _      | _      = nothing

  toTerm : (Γ : Ctxt) (u : 𝕌) → FT → Maybe (C⟦𝕌⟧ Γ u)
  toTerm Γ 𝕌Agent  (ftA a)       = toAg Γ a
  toTerm Γ 𝕌Agents (ftL (fll l)) with toAgs Γ l
  ... | just k  = just (agentsL k)
  ... | nothing = nothing
  toTerm Γ 𝕌Agents (ftL (flv j)) with toVar Γ 𝕍Agents j
  ... | just i  = just (agentsV i)
  ... | nothing = nothing
  toTerm Γ 𝕌Data   (ftD (fdc c)) = just (dataC c)
  toTerm Γ 𝕌Data   (ftD (fdv j)) with toVar Γ 𝕍Data j
  ... | just i  = just (dataV i)
  ... | nothing = nothing
  toTerm Γ 𝕌Prop   (ftP (fdc c)) = just (atomPropC c)
  toTerm Γ 𝕌Prop   (ftP (fdv j)) with toVar Γ 𝕍Prop j
  ... | just i  = just (atomPropV i)
  ... | nothing = nothing
  toTerm Γ _       _             = nothing

open Match using (Θ ; FT ; assignments ; targets ; toTerm ; totals)

-- witnesses are tried first at the points where an atom of the formula to
-- prove there is already a hypothesis
hypAtomsAt : (Δ : ℂ₀) (t : ℂRes Δ) → List (ℂhyp Δ) → List Match.FAt
hypAtomsAt Δ t []                        = []
hypAtomsAt Δ t ((CEr t′ , 𝕒 x , _) ∷ l) with Res-dec t′ t
... | inj₁ _ = Match.flAt 0 0 x ∷ hypAtomsAt Δ t l
... | inj₂ _ = hypAtomsAt Δ t l
hypAtomsAt Δ t (_ ∷ l)                   = hypAtomsAt Δ t l

anyAt : List Match.FAt → List Match.FAt → Bool
anyAt []      ts = false
anyAt (p ∷ ps) ts with anyT p ts
  where
  anyT : Match.FAt → List Match.FAt → Bool
  anyT p []      = false
  anyT p (t ∷ l) with Match.uAt p t []
  ... | just _  = true
  ... | nothing = anyT p l
... | true  = true
... | false = anyAt ps ts

rank : (Δ : ℂ₀) (B : ℂForm Δ) → List (ℂRes Δ) → List (ℂRes Δ)
rank Δ B ts = go ts Data.List.++ notGo ts
  where
  rel : ℂRes Δ → Bool
  rel t = anyAt (Match.atomsF 0 0 B []) (hypAtomsAt Δ t (ℂhyps Δ))
  go notGo : List (ℂRes Δ) → List (ℂRes Δ)
  go []      = []
  go (t ∷ l) with rel t
  ... | true  = t ∷ go l
  ... | false = go l
  notGo []      = []
  notGo (t ∷ l) with rel t
  ... | true  = notGo l
  ... | false = t ∷ notGo l

rankIf : Bool → (Δ : ℂ₀) (B : ℂForm Δ) → List (ℂRes Δ) → List (ℂRes Δ)
rankIf false Δ B ts = ts
rankIf true  Δ B ts = rank Δ B ts

-- the formula obtained by instantiating the ∀s of F with θ (ℂx does not
-- change the variables in scope, so all the instances live in Δ)
instF : (Δ : ℂ₀) (F : ℂForm Δ) → Θ → Maybe (ℂForm Δ)
instF Δ F            []            = just F
instF Δ (∀· u A)     (just t ∷ θ)  with toTerm (ℂtxt Δ) u t
... | just v  = instF Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) θ
... | nothing = nothing
instF Δ _            _             = nothing

-- the first assignment whose instance is not yet a hypothesis
pickθ : (Δ : ℂ₀) (R : ℂCE Δ) (F : ℂForm Δ) → List Θ → Maybe Θ
pickθ Δ R F []      = nothing
pickθ Δ R F (θ ∷ l) with instF Δ F θ
... | nothing = pickθ Δ R F l
... | just F′ with decAx Δ R F′
...   | inj₁ _ = pickθ Δ R F l
...   | inj₂ _ = just θ

-- a point t (among ts) with r ⊑ t where P holds and P →· Q and Q do not
fwd□ : (Δ : ℂ₀) (r : ℂRes Δ) (P Q : ℂForm Δ) → List (ℂRes Δ)
     → Maybe (Σ (ℂRes Δ) (λ t → ⊢ (useq Δ (r ⊑ t))))
fwd□ Δ r P Q []       = nothing
fwd□ Δ r P Q (t ∷ ts) with decAx Δ (CEr t) P | decAx Δ (CEr t) (P →· Q) | decAx Δ (CEr t) Q
... | inj₁ _ | inj₂ _ | inj₂ _ with proveCmp Δ r t LE
...   | just dc = just (t , dc)
...   | nothing = fwd□ Δ r P Q ts
fwd□ Δ r P Q (t ∷ ts) | _ | _ | _ = fwd□ Δ r P Q ts


-- how many invertible left rules search⊢ applies in a row before the others
inv-fuel : ℕ
inv-fuel = 40

module Srch (mem : Maybe EMT) (fwd : Bool) where

  search⊢       : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
  -- the invertible left rules (⊥L, ∧L, ＦL, ＯL, ＹL, ＵL, ＳL, ∃L, with the
  -- same guards as in search⊢-left) are applied first, without using fuel
  -- and without backtracking; k bounds how many are applied in a row
  -- with fwd false, search⊢ is the search of the previous rounds (no
  -- saturation, no forward steps, ∀L on termsC, witnesses in their order)
  search⊢-top   : Bool → (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
  search⊢-∀Lsel : Bool → (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (u : 𝕌) (A : ℂForm (ℂv Δ (𝕍𝕌 u)))
                   → Ax Δ R (∀· u A) → Maybe (⊢ (seq Δ T C))
  search⊢-sat   : (k n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
  search⊢-inv   : (k n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T C))
  -- forward steps, also applied by search⊢-inv: an ∀ whose instance is fully
  -- determined by matching (search⊢-∀Lf), →L when the antecedent is
  -- immediate (cheap), and, with EM, □L on □ (P →· Q) at a point where P holds
  search⊢-∀Lf   : (k n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (F : ℂForm Δ)
                   → Ax Δ R F → Θ → Maybe (⊢ (seq Δ T C))
  search⊢-□F    : (k n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (r : ℂRes Δ) (P Q : ℂForm Δ)
                   → Ax Δ (CEr r) (□ (P →· Q)) → List (ℂhyp Δ) → Maybe EMT → Maybe (⊢ (seq Δ T C))
  cheap         : (Δ : ℂ₀) (R : ℂCE Δ) (A : ℂForm Δ) → Maybe (⊢ (seq Δ R A))
  search⊢-intro : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
  search⊢-left  : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ)
                   → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T C))
  -- ＯI needs a witness r₁.  Its first premise (r ◁ r₁, unlabelled) is
  -- closed by ax, possibly via cmpR, so the witnesses are taken from the
  -- comparison hypotheses of the context at a point label.  ＵI tries the
  -- witnesses of Ｕcands, and proves r ⊑ r₁ with the comparison prover.
  search⊢-Ｏ    : (n : ℕ) (Δ : ℂ₀) (r : ℂRes Δ) (A : ℂForm Δ)
                   → List (ℂhyp Δ) → Maybe (⊢ (rseq Δ r (Ｏ A)))
  search⊢-Ｕ    : (n : ℕ) (Δ : ℂ₀) (r : ℂRes Δ) (A B : ℂForm Δ)
                   → List (ℂRes Δ) → Maybe (⊢ (rseq Δ r (A Ｕ B)))
  search⊢-cmp : (Δ : ℂ₀) (T : ℂCE Δ) (a b : ℂRes Δ) (c : Comparison)
                 → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T (a ⟨ c ⟩ b)))
  -- ＹI takes its witness from the comparison hypotheses, as ＯI; ＳI as ＵI
  search⊢-Ｙ    : (n : ℕ) (Δ : ℂ₀) (r : ℂRes Δ) (A : ℂForm Δ)
                   → List (ℂhyp Δ) → Maybe (⊢ (rseq Δ r (Ｙ A)))
  search⊢-Ｓ    : (n : ℕ) (Δ : ℂ₀) (r : ℂRes Δ) (A B : ℂForm Δ)
                   → List (ℂRes Δ) → Maybe (⊢ (rseq Δ r (A Ｓ B)))
  -- ∃R and ∀L, for each term of terms Δ u
  search⊢-∃R    : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (u : 𝕌) (A : ℂForm (ℂv Δ (𝕍𝕌 u)))
                   → List (ℂ⟦𝕌⟧ Δ u) → Maybe (⊢ (seq Δ T (∃· u A)))
  search⊢-∀L    : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (u : 𝕌) (A : ℂForm (ℂv Δ (𝕍𝕌 u)))
                   → Ax Δ R (∀· u A) → List (ℂ⟦𝕌⟧ Δ u) → Maybe (⊢ (seq Δ T C))
  -- ∀L by matching: each assignment of Match.assignments instantiates all of
  -- the ∀s of the prefix (unassigned ones with each term of termsC); with no
  -- assignment, search⊢-∀L on termsC as before
  search⊢-∀Lθ   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (u : 𝕌) (A : ℂForm (ℂv Δ (𝕍𝕌 u)))
                   → Ax Δ R (∀· u A) → List Θ → Maybe (⊢ (seq Δ T C))
  search⊢-∀Ls   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (F : ℂForm Δ)
                   → Ax Δ R F → List Θ → Maybe (⊢ (seq Δ T C))
  search⊢-∀Lm   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (F : ℂForm Δ)
                   → Ax Δ R F → Θ → Maybe (⊢ (seq Δ T C))
  search⊢-∀Le   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (u : 𝕌) (A : ℂForm (ℂv Δ (𝕍𝕌 u)))
                   → Ax Δ R (∀· u A) → Θ → List (ℂ⟦𝕌⟧ Δ u) → Maybe (⊢ (seq Δ T C))
  search⊢-∀L1   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (u : 𝕌) (A : ℂForm (ℂv Δ (𝕍𝕌 u)))
                   → Ax Δ R (∀· u A) → ℂ⟦𝕌⟧ Δ u → Θ → Maybe (⊢ (seq Δ T C))
  -- InL on A^i, for each point of inCands in i
  search⊢-In    : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (i : ℂInterval Δ) (A : ℂForm Δ)
                   → Ax Δ (CEi i) A → List (ℂRes Δ) → Maybe (⊢ (seq Δ T C))
  -- ＢL on (Ｂ A)^r, for each comparison hypothesis r₁ ◁ r
  search⊢-□L   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (r : ℂRes Δ) (A : ℂForm Δ)
                 → Ax Δ (CEr r) (□ A) → List (ℂRes Δ) → Maybe (⊢ (seq Δ T C))
  search⊢-→L   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (R : ℂCE Δ) (A B : ℂForm Δ)
                 → Ax Δ R (A →· B) → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T C))
  search⊢-ＢL   : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) (r : ℂRes Δ) (A : ℂForm Δ)
                   → Ax Δ (CEr r) (Ｂ A) → List (ℂhyp Δ) → Maybe (⊢ (seq Δ T C))

  search⊢ 0 Δ T C with decAx Δ T C
  ... | inj₁ p  = just (ax p)
  ... | inj₂ ¬p = nothing
  search⊢ (suc n) Δ T C with decAx Δ T C
  ... | inj₁ p  = just (ax p)
  ... | inj₂ ¬p = search⊢-top fwd n Δ T C

  search⊢-top false n Δ T C = search⊢-intro n Δ T C orelse search⊢-left n Δ T C (ℂhyps Δ)
  search⊢-top true  n Δ T C = search⊢-sat inv-fuel n Δ T C

  search⊢-sat k n Δ T C with decAx Δ T C | k
  ... | inj₁ p  | _      = just (ax p)
  ... | inj₂ ¬p | zero   = search⊢-intro n Δ T C orelse search⊢-left n Δ T C (ℂhyps Δ)
  ... | inj₂ ¬p | suc k′ = search⊢-inv k′ n Δ T C (ℂhyps Δ)

  search⊢-inv k n Δ T C [] = search⊢-intro n Δ T C orelse search⊢-left n Δ T C (ℂhyps Δ)
  search⊢-inv k n Δ T C ((R , ⊥· , p) ∷ l)
    with decPointCE R
  ... | inj₁ pt = just (⊥L pt p)
  ... | inj₂ _  = search⊢-inv k n Δ T C l
  search⊢-inv k n Δ T C ((R , A ∧· B , p) ∷ l)
    with decAx Δ R A | decAx Δ R B
  ... | inj₁ _ | inj₁ _ = search⊢-inv k n Δ T C l
  ... | _      | _      = mmap (∧L p) (search⊢-sat k n (ℂx (ℂx Δ A R) B R) T C)
  search⊢-inv k n Δ T C ((CEr r , Ｆ A , p) ∷ l)
    with decAx Δ (CEr r) (subℝ A r)
  ... | inj₁ _ = search⊢-inv k n Δ T C l
  ... | inj₂ _ = mmap (ＦL p) (search⊢-sat k n (ℂe Δ (subℝ A r) r) T C)
  search⊢-inv k n Δ T C ((CEr r , Ｏ A , p) ∷ l)
    with witnessed Δ (selＯ {Δ} r) A (ℂhyps Δ)
  ... | true  = search⊢-inv k n Δ T C l
  ... | false = mmap (ＯL p) (search⊢-sat k n (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ◁ 𝕣₀)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
  search⊢-inv k n Δ T C ((CEr r , Ｙ A , p) ∷ l)
    with witnessed Δ (selＹ {Δ} r) A (ℂhyps Δ)
  ... | true  = search⊢-inv k n Δ T C l
  ... | false = mmap (ＹL p) (search⊢-sat k n (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
  search⊢-inv k n Δ T C ((CEr r , A Ｕ B , p) ∷ l)
    with witnessed Δ (selＵ {Δ} r) B (ℂhyps Δ)
  ... | true  = search⊢-inv k n Δ T C l
  ... | false = mmap (ＵL p) (search⊢-sat k n (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ B) 𝕣₀) (↑₀ A) ［ ↑ᵣ₀ r , 𝕣₀ ）)
                                              (↑CE₀ T) (↑₀ C))
  search⊢-inv k n Δ T C ((CEr r , A Ｓ B , p) ∷ l)
    with witnessed Δ (selＳ {Δ} r) B (ℂhyps Δ)
  ... | true  = search⊢-inv k n Δ T C l
  ... | false = mmap (ＳL p) (search⊢-sat k n (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ r)) (↑₀ B) 𝕣₀) (↑₀ A) （ 𝕣₀ , ↑ᵣ₀ r ］)
                                              (↑CE₀ T) (↑₀ C))
  search⊢-inv k n Δ T C ((CEr R , ∃· u A , p) ∷ l)
    with ∃witnessed Δ (CEr R) u A (terms Δ u)
  ... | true  = search⊢-inv k n Δ T C l
  ... | false = mmap (∃L p) (search⊢-sat k n (ℂe (ℂv Δ (𝕍𝕌 u)) A (↑ᵣ₀ R)) (↑CE₀ T) (↑₀ C))
  search⊢-inv k n Δ T C ((CEr r , ((⊤· Ｕ ((P →· Q) →· ⊥·)) →· ⊥·) , p) ∷ l) =
    search⊢-□F k n Δ T C r P Q p l mem
  search⊢-inv k n Δ T C ((R , A →· B , p) ∷ l)
    with decAx Δ R B
  ... | inj₁ _ = search⊢-inv k n Δ T C l
  ... | inj₂ _ with cheap Δ R A
  ...   | just dA = mmap (→L p dA) (search⊢-sat k n (ℂx Δ B R) T C)
  ...   | nothing = search⊢-inv k n Δ T C l
  search⊢-inv k n Δ T C ((R , ∀· u A , p) ∷ l)
    with pickθ Δ R (∀· u A) (totals (assignments A (targets Δ C)))
  ... | just θ  = search⊢-∀Lf k n Δ T C R (∀· u A) p θ
  ... | nothing = search⊢-inv k n Δ T C l
  search⊢-inv k n Δ T C (_ ∷ l) = search⊢-inv k n Δ T C l

  search⊢-□F k n Δ T C r P Q p l nothing = search⊢-inv k n Δ T C l
  search⊢-□F k n Δ (CEr t₀) C r P Q p l (just em) with fwd□ Δ r P Q (Ｕcands Δ r)
  ... | just (t , dc) = mmap (□L em p dc) (search⊢-sat k n (ℂe Δ (P →· Q) t) (CEr t₀) C)
  ... | nothing       = search⊢-inv k n Δ (CEr t₀) C l
  search⊢-□F k n Δ T C r P Q p l (just em) = search⊢-inv k n Δ T C l

  search⊢-∀Lf k n Δ T C R (∀· u A) p (just t ∷ θ) with toTerm (ℂtxt Δ) u t
  ... | just v  = mmap (∀L p v) (search⊢-∀Lf k n (ℂx Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) R) T C R
                                   (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) (found Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) R) θ)
  ... | nothing = nothing
  search⊢-∀Lf k n Δ T C R F p [] = search⊢-sat k n Δ T C
  search⊢-∀Lf k n Δ T C R F p _  = nothing

  cheap Δ R A with decAx Δ R A
  ... | inj₁ q = just (ax q)
  ... | inj₂ _ = shape R A
    where
    shape : (R : ℂCE Δ) (A : ℂForm Δ) → Maybe (⊢ (seq Δ R A))
    shape R ⊤· = just ⊤I
    shape (CEr r) (𝔸 (a ∈ₐ agentsL l)) with findAg a l
    ... | just m  = just (∈I m)
    ... | nothing = nothing
    shape R (a ⟨ c ⟩ b) = search⊢-cmp Δ R a b c (ℂhyps Δ) orelse mmap (cmpAt R) (proveCmp Δ a b c)
    shape R _ = nothing

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

  -- □I (and, failing that, →I on ¬◇¬A)
  search⊢-intro n Δ (CEr r) ((⊤· Ｕ (A →· ⊥·)) →· ⊥·) =
    mmap □I (search⊢ n (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (CEr 𝕣₀) (↑₀ A))
    orelse mmap →I (search⊢ n (ℂe Δ (⊤· Ｕ (A →· ⊥·)) r) (CEr r) ⊥·)

  search⊢-intro n Δ T (A →· B) with T
  ... | CEr R
        with search⊢ n (ℂe Δ A R) (CEr R) B
  ...     | just p  = just (→I p)
  ...     | nothing = nothing
  search⊢-intro n Δ T (A →· B) | CEu   = nothing
  search⊢-intro n Δ T (A →· B) | CEi _ = nothing

  search⊢-intro n Δ (CEr r) (Ｏ A)   = search⊢-Ｏ n Δ r A (ℂhyps Δ)
  search⊢-intro n Δ (CEr r) (A Ｕ B) = search⊢-Ｕ n Δ r A B (rankIf fwd Δ B (Ｕcands Δ r))

  search⊢-intro n Δ (CEr r) (Ｆ A)   = mmap ＦI (search⊢ n Δ (CEr r) (subℝ A r))
  search⊢-intro n Δ T (a ⟨ c ⟩ b)  =
    search⊢-cmp Δ T a b c (ℂhyps Δ) orelse mmap (cmpAt T) (proveCmp Δ a b c)

  search⊢-intro n Δ (CEr r) (Ｙ A)   = search⊢-Ｙ n Δ r A (ℂhyps Δ)
  search⊢-intro n Δ (CEr r) (A Ｓ B) = search⊢-Ｓ n Δ r A B (rankIf fwd Δ B (Ｓcands Δ r))
  search⊢-intro n Δ (CEr r) (Ｂ A)   = mmap ＢI (search⊢ n (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) (CEr 𝕣₀) (↑₀ A))

  search⊢-intro n Δ (CEr r) (𝔸 (a ∈ₐ agentsL l)) with findAg a l
  ... | just m  = just (∈I m)
  ... | nothing = nothing

  search⊢-intro n Δ T (∀· u A) = mmap ∀I (search⊢ n (ℂv Δ (𝕍𝕌 u)) (↑CE₀ T) A)
  search⊢-intro n Δ T (∃· u A) = search⊢-∃R n Δ T u A (termsC Δ (∃· u A) u)

  search⊢-intro n Δ T C = nothing


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
  search⊢-Ｕ n Δ r A B (r₁ ∷ l) with proveLE cmp-fuel Δ (ctxFacts Δ) r r₁
  ... | nothing = search⊢-Ｕ n Δ r A B l
  ... | just dle
      with search⊢ n Δ (CEr r₁) B
  ...   | nothing = search⊢-Ｕ n Δ r A B l
  ...   | just dB =
          mmap (ＵI dle dB)
               (search⊢ n (ℂu (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (𝕣₀ ⊏ ↑ᵣ₀ r₁)) (CEr 𝕣₀) (↑₀ A))
          orelse search⊢-Ｕ n Δ r A B l

  search⊢-Ｙ n Δ r A [] = nothing
  search⊢-Ｙ n Δ r A ((R , (r₁ ⟨ PR ⟩ x) , p) ∷ l) with decPointCE R | Res-dec x r
  ... | inj₁ pt | inj₁ refl = mmap (ＹI (cmpAx pt p)) (search⊢ n Δ (CEr r₁) A)
                              orelse search⊢-Ｙ n Δ r A l
  ... | _       | _         = search⊢-Ｙ n Δ r A l
  search⊢-Ｙ n Δ r A (_ ∷ l) = search⊢-Ｙ n Δ r A l

  search⊢-Ｓ n Δ r A B [] = nothing
  search⊢-Ｓ n Δ r A B (r₁ ∷ l) with proveLE cmp-fuel Δ (ctxFacts Δ) r₁ r
  ... | nothing = search⊢-Ｓ n Δ r A B l
  ... | just dle
      with search⊢ n Δ (CEr r₁) B
  ...   | nothing = search⊢-Ｓ n Δ r A B l
  ...   | just dB =
          mmap (ＳI dle dB)
               (search⊢ n (ℂu (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r₁ ⊏ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ r)) (CEr 𝕣₀) (↑₀ A))
          orelse search⊢-Ｓ n Δ r A B l

  search⊢-∃R n Δ T u A [] = nothing
  search⊢-∃R n Δ T u A (v ∷ l) =
    mmap (∃R v) (search⊢ n Δ T (sub A (CSub،ₗ {_} {𝕍𝕌 u} v))) orelse search⊢-∃R n Δ T u A l

  search⊢-∀L n Δ T C R u A p [] = nothing
  search⊢-∀L n Δ T C R u A p (v ∷ l) with decAx Δ R (sub A (CSub،ₗ {_} {𝕍𝕌 u} v))
  ... | inj₁ _ = search⊢-∀L n Δ T C R u A p l
  ... | inj₂ _ = mmap (∀L p v) (search⊢ n (ℂx Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) R) T C)
                 orelse search⊢-∀L n Δ T C R u A p l

  search⊢-∀Lsel false n Δ T C R u A p = search⊢-∀L n Δ T C R u A p (termsC Δ C u)
  search⊢-∀Lsel true  n Δ T C R u A p = search⊢-∀Lθ n Δ T C R u A p (assignments A (targets Δ C))

  search⊢-∀Lθ n Δ T C R u A p []         = search⊢-∀L n Δ T C R u A p (termsC Δ C u)
  search⊢-∀Lθ n Δ T C R u A p (θ ∷ θs)   = search⊢-∀Ls n Δ T C R (∀· u A) p (θ ∷ θs)

  search⊢-∀Ls n Δ T C R F p []       = nothing
  search⊢-∀Ls n Δ T C R F p (θ ∷ θs) = search⊢-∀Lm n Δ T C R F p θ orelse search⊢-∀Ls n Δ T C R F p θs

  search⊢-∀Lm n Δ T C R (∀· u A) p (just t ∷ θ) with toTerm (ℂtxt Δ) u t
  ... | just v  = search⊢-∀L1 n Δ T C R u A p v θ
  ... | nothing = nothing
  search⊢-∀Lm n Δ T C R (∀· u A) p (nothing ∷ θ) = search⊢-∀Le n Δ T C R u A p θ (termsC Δ C u)
  search⊢-∀Lm n Δ T C R F p _ = nothing

  search⊢-∀Le n Δ T C R u A p θ []       = nothing
  search⊢-∀Le n Δ T C R u A p θ (v ∷ vs) = search⊢-∀L1 n Δ T C R u A p v θ orelse search⊢-∀Le n Δ T C R u A p θ vs

  search⊢-∀L1 n Δ T C R u A p v [] with decAx Δ R (sub A (CSub،ₗ {_} {𝕍𝕌 u} v))
  ... | inj₁ _ = nothing
  ... | inj₂ _ = mmap (∀L p v) (search⊢ n (ℂx Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) R) T C)
  search⊢-∀L1 n Δ T C R u A p v (s ∷ θ) =
    mmap (∀L p v) (search⊢-∀Lm n (ℂx Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) R) T C R (sub A (CSub،ₗ {_} {𝕍𝕌 u} v))
                                (found Δ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v)) R) (s ∷ θ))

  search⊢-In n Δ T C i A p [] = nothing
  search⊢-In n Δ T C i A p (r ∷ l) with decAx Δ (CEr r) A
  ... | inj₁ _ = search⊢-In n Δ T C i A p l
  ... | inj₂ _ with proveIn Δ r i
  ...   | nothing = search⊢-In n Δ T C i A p l
  ...   | just dI = mmap (InL p dI) (search⊢ n (ℂe Δ A r) T C) orelse search⊢-In n Δ T C i A p l

  search⊢-ＢL n Δ T C r A p [] = nothing
  search⊢-ＢL n Δ T C r A p ((R , (r₁ ⟨ PR ⟩ x) , q) ∷ l) with decPointCE R | Res-dec x r
  ... | inj₁ pt | inj₁ refl
      with decAx Δ (CEr r₁) A
  ...   | inj₁ _ = search⊢-ＢL n Δ T C r A p l
  ...   | inj₂ _ = mmap (ＢL p (cmpAx pt q)) (search⊢ n (ℂe Δ A r₁) T C)
                   orelse search⊢-ＢL n Δ T C r A p l
  search⊢-ＢL n Δ T C r A p ((R , (r₁ ⟨ PR ⟩ x) , q) ∷ l) | _ | _ = search⊢-ＢL n Δ T C r A p l
  search⊢-ＢL n Δ T C r A p (_ ∷ l) = search⊢-ＢL n Δ T C r A p l

  search⊢-→L n Δ T C R A B p l
    with decAx Δ R B
  ... | inj₁ _ = search⊢-left n Δ T C l
  ... | inj₂ _
      with search⊢ n Δ R A
  ...   | nothing = search⊢-left n Δ T C l
  ...   | just dA =
          mmap (→L p dA) (search⊢ n (ℂx Δ B R) T C)
          orelse search⊢-left n Δ T C l

  search⊢-□L n Δ T C r A p ts = withEM mem
    where
    withEM : Maybe EMT → Maybe (⊢ (seq Δ T C))
    withEM nothing   = nothing
    withEM (just em) = go T ts
      where
        go : (T : ℂCE Δ) → List (ℂRes Δ) → Maybe (⊢ (seq Δ T C))
        go (CEr t₀) (t ∷ ts) with decAx Δ (CEr t) A | proveCmp Δ r t LE
        ... | inj₂ _ | just dc = mmap (□L em p dc) (search⊢ n (ℂe Δ A t) (CEr t₀) C) orelse go (CEr t₀) ts
        ... | _      | _       = go (CEr t₀) ts
        go _ _ = nothing

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

  -- InL : a hypothesis over an interval is instantiated at the points of
  -- inCands that the comparison prover places in the interval.  (Conjunctions
  -- over an interval are split by ∧L above first.)
  search⊢-left n Δ T C ((CEi i , A , p) ∷ l) =
    search⊢-In n Δ T C i A p (inCands Δ T i) orelse search⊢-left n Δ T C l

  -- □L (classical: only when the search is given EM) : □ A at r gives A at
  -- the candidate points t with r ⊑ t; the →L step on ¬◇¬A is still tried.
  search⊢-left n Δ T C ((CEr r , ((⊤· Ｕ (A →· ⊥·)) →· ⊥·) , p) ∷ l) =
    search⊢-□L n Δ T C r A p (Ｕcands Δ r)
    orelse search⊢-→L n Δ T C (CEr r) (⊤· Ｕ (A →· ⊥·)) ⊥· p l

  -- →L : unrestricted.  Fires only if the antecedent is provable.
  search⊢-left n Δ T C ((R , A →· B , p) ∷ l) = search⊢-→L n Δ T C R A B p l

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

  -- ＯL, ＹL, ＵL, ＳL : introduce a fresh time point, unless the hypothesis
  -- is already witnessed in the context (see witnessed).
  search⊢-left n Δ T C ((CEr r , Ｏ A , p) ∷ l)
    with witnessed Δ (selＯ {Δ} r) A (ℂhyps Δ)
  ... | true  = search⊢-left n Δ T C l
  ... | false =
        mmap (ＯL p) (search⊢ n (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ◁ 𝕣₀)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
        orelse search⊢-left n Δ T C l

  search⊢-left n Δ T C ((CEr r , Ｙ A , p) ∷ l)
    with witnessed Δ (selＹ {Δ} r) A (ℂhyps Δ)
  ... | true  = search⊢-left n Δ T C l
  ... | false =
        mmap (ＹL p) (search⊢ n (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ◁ ↑ᵣ₀ r)) (↑₀ A) 𝕣₀) (↑CE₀ T) (↑₀ C))
        orelse search⊢-left n Δ T C l

  search⊢-left n Δ T C ((CEr r , A Ｕ B , p) ∷ l)
    with witnessed Δ (selＵ {Δ} r) B (ℂhyps Δ)
  ... | true  = search⊢-left n Δ T C l
  ... | false =
        mmap (ＵL p) (search⊢ n (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) (↑₀ B) 𝕣₀) (↑₀ A) ［ ↑ᵣ₀ r , 𝕣₀ ）)
                                (↑CE₀ T) (↑₀ C))
        orelse search⊢-left n Δ T C l

  search⊢-left n Δ T C ((CEr r , A Ｓ B , p) ∷ l)
    with witnessed Δ (selＳ {Δ} r) B (ℂhyps Δ)
  ... | true  = search⊢-left n Δ T C l
  ... | false =
        mmap (ＳL p) (search⊢ n (ℂi (ℂe (ℂu (ℂv Δ 𝕍ℝ) (𝕣₀ ⊑ ↑ᵣ₀ r)) (↑₀ B) 𝕣₀) (↑₀ A) （ 𝕣₀ , ↑ᵣ₀ r ］)
                                (↑CE₀ T) (↑₀ C))
        orelse search⊢-left n Δ T C l

  -- ＢL : instantiated at the r₁ with r₁ ◁ r in the context.
  search⊢-left n Δ T C ((CEr r , Ｂ A , p) ∷ l) =
    search⊢-ＢL n Δ T C r A p (ℂhyps Δ) orelse search⊢-left n Δ T C l

  -- ＦL : non-branching; skipped if A[x/r]^r is already present.
  search⊢-left n Δ T C ((CEr r , Ｆ A , p) ∷ l)
    with decAx Δ (CEr r) (subℝ A r)
  ... | inj₁ _ = search⊢-left n Δ T C l
  ... | inj₂ _ =
        mmap (ＦL p) (search⊢ n (ℂe Δ (subℝ A r) r) T C)
        orelse search⊢-left n Δ T C l

  -- ∀L : by matching (search⊢-∀Lθ), else with each term of termsC.
  search⊢-left n Δ T C ((R , ∀· u A , p) ∷ l) =
    search⊢-∀Lsel fwd n Δ T C R u A p orelse search⊢-left n Δ T C l

  -- ∃L : fresh variable, unless already witnessed by a variable in scope.
  search⊢-left n Δ T C ((CEr R , ∃· u A , p) ∷ l)
    with ∃witnessed Δ (CEr R) u A (terms Δ u)
  ... | true  = search⊢-left n Δ T C l
  ... | false =
        mmap (∃L p) (search⊢ n (ℂe (ℂv Δ (𝕍𝕌 u)) A (↑ᵣ₀ R)) (↑CE₀ T) (↑₀ C))
        orelse search⊢-left n Δ T C l

  -- atoms, comparisons, temporal and ∃ hypotheses at other labels:
  -- no left rule.  MUST remain the last clause.
  search⊢-left n Δ T C (_ ∷ l) = search⊢-left n Δ T C l

open Srch nothing false public

-- the search with saturation and forward steps: invertible left rules and
-- forward steps first, without fuel or backtracking, then ∀L by matching
-- and witnesses at relevant points first
search⊢⁺ : (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
search⊢⁺ = Srch.search⊢ nothing true

-- the same with the classical rule □L enabled
search⊢ᶜ : EMT → (n : ℕ) (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Maybe (⊢ (seq Δ T C))
search⊢ᶜ em = Srch.search⊢ (just em) true

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
-- Lemmas about weakening used by Plug.lagda
-- ===========================================================================

⊆⋆→⊆ : {Γ Δ : Ctxt} → Γ ⊆⋆ Δ → Γ ⊆ Δ
⊆⋆→⊆ {Γ} {Δ} s {u} i = app-⊆⋆ s u i

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

⋆↑ᵣ₀-add : {Γ Δ : Ctxt} (v : 𝕍) (s : Γ ⊆⋆ Δ) (r : Res Γ)
         → ↑⋆ᵣ (⊆⋆-add v s) (↑ᵣ₀ {Γ} {v} r) ≡ ↑ᵣ₀ {Δ} {v} (↑⋆ᵣ s r)
⋆↑ᵣ₀-add v s (𝐯 i)    = refl
⋆↑ᵣ₀-add v s 𝟎        = refl
⋆↑ᵣ₀-add v s (rvar ρ)        = refl
⋆↑ᵣ₀-add v s (r ⋆ r₁) = cong₂ _⋆_ (⋆↑ᵣ₀-add v s r) (⋆↑ᵣ₀-add v s r₁)

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
-- Examples (see Examples.lagda for examples over arbitrary formulas, using
-- plug-⊢ from Plug.lagda)
-- ===========================================================================

example2 : (M : Model₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (𝐯0 →· 𝐯0)))
example2 M p s h = sound M (→I (ax (found ℂ⟨⟩ (var 0) (CEr 𝟎)))) s (lift tt)
-- Prove 10 M ℂ⟨⟩ (CEr 𝟎) (𝐯0 →· 𝐯0) gives us (when typing C-u C-u C-u C-c C-n):
-- just (sound M (→I (ax (found ℂ⟨⟩ (var 0) (CEr 𝟎)))))

-- Example that makes use of an elimination
example4 : (M : Model₀)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) ((𝐯0 ∧· 𝐯1) →· 𝐯0)))
example4 M p s h = sound M (→I (∧L (found ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (ax (skip (var 1) (CEr 𝟎) (found (ℂx ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (var 0) (CEr 𝟎)))))) s (lift tt)
-- Prove 10 M ℂ⟨⟩ (CEr 𝟎) ((𝐯0 ∧· 𝐯1) →· 𝐯0) gives us (when typing C-u C-u C-u C-c C-n):
-- just (sound M (→I (∧L (found ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (ax (skip (var 1) (CEr 𝟎) (found (ℂx ℂ⟨⟩ (var 0 ∧· var 1) (CEr 𝟎)) (var 0) (CEr 𝟎)))))))

\end{code}
