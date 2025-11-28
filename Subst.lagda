\begin{code}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)

open import Agda.Builtin.Equality

open import Data.Nat
open import Data.Nat.Properties using ()
open import Data.List
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All renaming (tabulate to tab)
open import Data.List.Properties using (map-cong-local)
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤ ; tt)
open import Data.Empty
--open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

open import Axiom.Extensionality.Propositional

open import World
open import Misc

module Subst(𝔻 : Set)
            (W : World)
       where

open import Syntax(𝔻)(W)

open World.World W


_⊆_ : (Γ Δ : Ctxt) → Set
Γ ⊆ Δ = {u : 𝕍} → ∈Ctxt u Γ → ∈Ctxt u Δ

≡⊆ : {Γ Δ : Ctxt} (s₁ s₂ : Γ ⊆ Δ) → Set
≡⊆ {Γ} {Δ} s₁ s₂ = {u : 𝕍} (i : ∈Ctxt u Γ) → s₁ i ≡ s₂ i

≡⊆-refl : {Γ Δ : Ctxt} {s : Γ ⊆ Δ}
        → ≡⊆ s s
≡⊆-refl {Γ} {Δ} {s} {u} i = refl

⊆، : {Γ Δ : Ctxt} (u : 𝕍)
    → Γ ⊆ Δ
    → (Γ ، u) ⊆ (Δ ، u)
⊆، {Γ} {Δ} u s {.u} (∈Ctxt0 .Γ) = ∈Ctxt0 Δ
⊆، {Γ} {Δ} u s {v} (∈CtxtS .u i) = ∈CtxtS u (s i)

≡⊆-⊆، : {Γ Δ : Ctxt} (u : 𝕍)
        (s₁ s₂ : Γ ⊆ Δ)
      → ≡⊆ s₁ s₂
      → ≡⊆ (⊆، u s₁) (⊆، u s₂)
≡⊆-⊆، {Γ} {Δ} u s₁ s₂ ≡s {.u} (∈Ctxt0 .Γ) = refl
≡⊆-⊆، {Γ} {Δ} u s₁ s₂ ≡s {v} (∈CtxtS .u i) = cong (∈CtxtS u) (≡s i)

⊆₀ : {Γ : Ctxt} {u : 𝕍} → Γ ⊆ (Γ ، u)
⊆₀ {Γ} {u} {x} i = ∈CtxtS u i

⊆₁ : {Γ : Ctxt} {u v : 𝕍} → Γ ⊆ (Γ ، u ، v)
⊆₁ {Γ} {u} {v} {x} i = ∈CtxtS v (∈CtxtS u i)

⊆₂ : {Γ : Ctxt} {u v w : 𝕍} → Γ ⊆ (Γ ، u ، v ، w)
⊆₂ {Γ} {u} {v} {w} {x} i = ∈CtxtS w (∈CtxtS v (∈CtxtS u i))

⊆₃ : {Γ : Ctxt} {u v w z : 𝕍} → Γ ⊆ (Γ ، u ، v ، w ، z)
⊆₃ {Γ} {u} {v} {w} {z} {x} i = ∈CtxtS z (∈CtxtS w (∈CtxtS v (∈CtxtS u i)))

⊆₄ : {Γ : Ctxt} {u v w z x : 𝕍} → Γ ⊆ (Γ ، u ، v ، w ، z ، x)
⊆₄ {Γ} {u} {v} {w} {z} {x} {_} i = ∈CtxtS x (∈CtxtS z (∈CtxtS w (∈CtxtS v (∈CtxtS u i))))

⊆₅ : {Γ : Ctxt} {u v w z x y : 𝕍} → Γ ⊆ (Γ ، u ، v ، w ، z ، x ، y)
⊆₅ {Γ} {u} {v} {w} {z} {x} {y} {_} i = ∈CtxtS y (∈CtxtS x (∈CtxtS z (∈CtxtS w (∈CtxtS v (∈CtxtS u i)))))

⊆₀، : {Γ : Ctxt} {u v : 𝕍} → (Γ ، v) ⊆ (Γ ، u ، v)
⊆₀، {Γ} {u} {v} = ⊆، v ⊆₀

⊆₀،، : {Γ : Ctxt} {u v w : 𝕍} → (Γ ، v ، w) ⊆ (Γ ، u ، v ، w)
⊆₀،، {Γ} {u} {v} {w} = ⊆، w (⊆، v ⊆₀)

⊆₀،،، : {Γ : Ctxt} {u v w x : 𝕍} → (Γ ، v ، w ، x) ⊆ (Γ ، u ، v ، w ، x)
⊆₀،،، {Γ} {u} {v} {w} {x} = ⊆، x (⊆، w (⊆، v ⊆₀))

⊆₁، : {Γ : Ctxt} {u v w : 𝕍} → (Γ ، w) ⊆ (Γ ، u ، v ، w)
⊆₁، {Γ} {u} {v} {w} = ⊆، w ⊆₁

⊆₂، : {Γ : Ctxt} {u v w x : 𝕍} → (Γ ، x) ⊆ (Γ ، u ، v ، w ، x)
⊆₂، {Γ} {u} {v} {w} {x} = ⊆، x ⊆₂


-- weakening

↑ᵢ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Agent Γ → Agent Δ
↑ᵢ s (agentV i) = agentV (s i)
↑ᵢ s (agentC x) = agentC x

↑ₛ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Agents Γ → Agents Δ
↑ₛ s (agentsV i) = agentsV (s i)
↑ₛ s (agentsL l) = agentsL (Data.List.map (↑ᵢ s) l)
--↑ₛ s (agentsS A) = agentsS A

↑ₚ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → AtomProp Γ → AtomProp Δ
↑ₚ s (atomPropV i) = atomPropV (s i)
↑ₚ s (atomPropC x) = atomPropC x

↑d : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Data Γ → Data Δ
↑d s (dataV i) = dataV (s i)
↑d s (dataC x) = dataC x

↑ₜ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Action Γ → Action Δ
↑ₜ s (ActSend p a A) = ActSend (↑d s p) (↑ᵢ s a) (↑ₛ s A)

↑ₑ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Event Γ → Event Δ
↑ₑ s (EvtReceive p a b) = EvtReceive (↑d s p) (↑ᵢ s a) (↑ᵢ s b)
↑ₑ s (EvtInternal a d) = EvtInternal (↑ᵢ s a) (↑d s d)

↑f : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Fault Γ → Fault Δ
↑f s (FaultCorrect a b) = FaultCorrect (↑ᵢ s a) (↑ᵢ s b)

↑ₐ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Atom Γ → Atom Δ
↑ₐ s (atProp    x) = atProp (↑ₚ s x)
↑ₐ s (atAction  x) = atAction (↑ₜ s x)
↑ₐ s (atEvent   x) = atEvent (↑ₑ s x)
↑ₐ s (atCorrect x) = atCorrect (↑f s x)

↑ᵣ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Res Γ → Res Δ
↑ᵣ s (var x) = var (s x)
↑ᵣ s 𝟎 = 𝟎
--↑ᵣ s (𝐬 t) = 𝐬 (↑ᵣ s t)
↑ᵣ s (t ⋆ t₁) = ↑ᵣ s t ⋆ ↑ᵣ s t₁

↑ᵣ₀ : {Γ : Ctxt} {u : 𝕍} → Res Γ → Res (Γ ، u)
↑ᵣ₀ {Γ} {u} a = ↑ᵣ ⊆₀ a

↑ᵣ₀، : {Γ : Ctxt} {u v : 𝕍} → Res (Γ ، v) → Res (Γ ، u ، v)
↑ᵣ₀، {Γ} {u} {v} a = ↑ᵣ ⊆₀، a

↑ᵣ₀،، : {Γ : Ctxt} {u v w : 𝕍} → Res (Γ ، v ، w) → Res (Γ ، u ، v ، w)
↑ᵣ₀،، {Γ} {u} {v} {w} a = ↑ᵣ ⊆₀،، a

↑ᵣ₀،،، : {Γ : Ctxt} {u v w x : 𝕍} → Res (Γ ، v ، w ، x) → Res (Γ ، u ، v ، w ، x)
↑ᵣ₀،،، {Γ} {u} {v} {w} {x} a = ↑ᵣ ⊆₀،،، a

↑ᵣ₁ : {Γ : Ctxt} {u v : 𝕍} → Res Γ → Res (Γ ، u ، v)
↑ᵣ₁ {Γ} {u} {v} a = ↑ᵣ ⊆₁ a

↑ᵣ₁، : {Γ : Ctxt} {u v w : 𝕍} → Res (Γ ، w) → Res (Γ ، u ، v ، w)
↑ᵣ₁، {Γ} {u} {v} {w} a = ↑ᵣ ⊆₁، a

↑ᵣ₂ : {Γ : Ctxt} {u v w : 𝕍} → Res Γ → Res (Γ ، u ، v ، w)
↑ᵣ₂ {Γ} {u} {v} {w} a = ↑ᵣ ⊆₂ a

↑ᵣ₂، : {Γ : Ctxt} {u v w x : 𝕍} → Res (Γ ، x) → Res (Γ ، u ، v ، w ، x)
↑ᵣ₂، {Γ} {u} {v} {w} {x} a = ↑ᵣ ⊆₂، a

↑ᵣ₃ : {Γ : Ctxt} {u v w x : 𝕍} → Res Γ → Res (Γ ، u ، v ، w ، x)
↑ᵣ₃ {Γ} {u} {v} {w} {x} a = ↑ᵣ ⊆₃ a

↑ᵣ₄ : {Γ : Ctxt} {u v w x y : 𝕍} → Res Γ → Res (Γ ، u ، v ، w ، x ، y)
↑ᵣ₄ {Γ} {u} {v} {w} {x} {y} a = ↑ᵣ ⊆₄ a

↑ᵣ₅ : {Γ : Ctxt} {u v w x y z : 𝕍} → Res Γ → Res (Γ ، u ، v ، w ، x ، y ، z)
↑ᵣ₅ {Γ} {u} {v} {w} {x} {y} {z} a = ↑ᵣ ⊆₅ a

↑ᵢ₀ : {Γ : Ctxt} {u : 𝕍} → Agent Γ → Agent (Γ ، u)
↑ᵢ₀ {Γ} {u} a = ↑ᵢ ⊆₀ a

↑ᵢ₁ : {Γ : Ctxt} {u v : 𝕍} → Agent Γ → Agent (Γ ، u ، v)
↑ᵢ₁ {Γ} {u} {v} a = ↑ᵢ ⊆₁ a

↑ᵢ₂ : {Γ : Ctxt} {u v w : 𝕍} → Agent Γ → Agent (Γ ، u ، v ، w)
↑ᵢ₂ {Γ} {u} {v} {w} a = ↑ᵢ ⊆₂ a

↑ᵢ₃ : {Γ : Ctxt} {u v w x : 𝕍} → Agent Γ → Agent (Γ ، u ، v ، w ، x)
↑ᵢ₃ {Γ} {u} {v} {w} {x} a = ↑ᵢ ⊆₃ a

↑ₛ₀ : {Γ : Ctxt} {u : 𝕍} → Agents Γ → Agents (Γ ، u)
↑ₛ₀ {Γ} {u} a = ↑ₛ ⊆₀ a

↑ₛ₁ : {Γ : Ctxt} {u v : 𝕍} → Agents Γ → Agents (Γ ، u ، v)
↑ₛ₁ {Γ} {u} {v} a = ↑ₛ ⊆₁ a

↑ₛ₂ : {Γ : Ctxt} {u v w : 𝕍} → Agents Γ → Agents (Γ ، u ، v ، w)
↑ₛ₂ {Γ} {u} {v} {w} a = ↑ₛ ⊆₂ a

↑ₚ₀ : {Γ : Ctxt} {u : 𝕍} → AtomProp Γ → AtomProp (Γ ، u)
↑ₚ₀ {Γ} {u} a = ↑ₚ ⊆₀ a

↑ₚ₁ : {Γ : Ctxt} {u v : 𝕍} → AtomProp Γ → AtomProp (Γ ، u ، v)
↑ₚ₁ {Γ} {u} {v} a = ↑ₚ ⊆₁ a

↑ₚ₂ : {Γ : Ctxt} {u v w : 𝕍} → AtomProp Γ → AtomProp (Γ ، u ، v ، w)
↑ₚ₂ {Γ} {u} {v} {w} a = ↑ₚ ⊆₂ a

↑d₀ : {Γ : Ctxt} {u : 𝕍} → Data Γ → Data (Γ ، u)
↑d₀ {Γ} {u} a = ↑d ⊆₀ a

↑d₀، : {Γ : Ctxt} {u v : 𝕍} → Data (Γ ، v) → Data (Γ ، u ، v)
↑d₀، {Γ} {u} {v} d = ↑d ⊆₀، d

↑d₀،، : {Γ : Ctxt} {u v w : 𝕍} → Data (Γ ، v ، w) → Data (Γ ، u ، v ، w)
↑d₀،، {Γ} {u} {v} {w} d = ↑d ⊆₀،، d

↑d₀،،، : {Γ : Ctxt} {u v w x : 𝕍} → Data (Γ ، v ، w ، x) → Data (Γ ، u ، v ، w ، x)
↑d₀،،، {Γ} {u} {v} {w} {x} d = ↑d ⊆₀،،، d

↑d₂، : {Γ : Ctxt} {u v w x : 𝕍} → Data (Γ ، x) → Data (Γ ، u ، v ، w ، x)
↑d₂، {Γ} {u} {v} {w} {x} d = ↑d ⊆₂، d

↑d₁ : {Γ : Ctxt} {u v : 𝕍} → Data Γ → Data (Γ ، u ، v)
↑d₁ {Γ} {u} {v} a = ↑d ⊆₁ a

↑d₁، : {Γ : Ctxt} {u v w : 𝕍} → Data (Γ ، w) → Data (Γ ، u ، v ، w)
↑d₁، {Γ} {u} {v} {w} a = ↑d ⊆₁، a

↑d₂ : {Γ : Ctxt} {u v w : 𝕍} → Data Γ → Data (Γ ، u ، v ، w)
↑d₂ {Γ} {u} {v} {w} a = ↑d ⊆₂ a

↑d₃ : {Γ : Ctxt} {u v w x : 𝕍} → Data Γ → Data (Γ ، u ، v ، w ، x)
↑d₃ {Γ} {u} {v} {w} {x} a = ↑d ⊆₃ a

↑d₄ : {Γ : Ctxt} {u v w x y : 𝕍} → Data Γ → Data (Γ ، u ، v ، w ، x ، y)
↑d₄ {Γ} {u} {v} {w} {x} {y} a = ↑d ⊆₄ a

↑ₐ₀ : {Γ : Ctxt} {u : 𝕍} → Atom Γ → Atom (Γ ، u)
↑ₐ₀ {Γ} {u} a = ↑ₐ ⊆₀ a

↑ₐ₁ : {Γ : Ctxt} {u v : 𝕍} → Atom Γ → Atom (Γ ، u ، v)
↑ₐ₁ {Γ} {u} {v} a = ↑ₐ ⊆₁ a

↑ₜ₀ : {Γ : Ctxt} {u : 𝕍} → Action Γ → Action (Γ ، u)
↑ₜ₀ {Γ} {u} a = ↑ₜ ⊆₀ a

↑ₜ₁ : {Γ : Ctxt} {u v : 𝕍} → Action Γ → Action (Γ ، u ، v)
↑ₜ₁ {Γ} {u} {v} a = ↑ₜ ⊆₁ a

↑ₑ₀ : {Γ : Ctxt} {u : 𝕍} → Event Γ → Event (Γ ، u)
↑ₑ₀ {Γ} {u} a = ↑ₑ ⊆₀ a

↑ₑ₁ : {Γ : Ctxt} {u v : 𝕍} → Event Γ → Event (Γ ، u ، v)
↑ₑ₁ {Γ} {u} {v} a = ↑ₑ ⊆₁ a

↑f₀ : {Γ : Ctxt} {u : 𝕍} → Fault Γ → Fault (Γ ، u)
↑f₀ {Γ} {u} a = ↑f ⊆₀ a

↑f₁ : {Γ : Ctxt} {u v : 𝕍} → Fault Γ → Fault (Γ ، u ، v)
↑f₁ {Γ} {u} {v} a = ↑f ⊆₁ a

{--
↑D : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → DataProp Γ → DataProp Δ
↑D s p = {!!}
{-- (dataPropV i) = ? --dataPropV (s i)
↑D s (dataPropC p) = ? --dataPropC p
--}

↑R : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → DataRel Γ → DataRel Δ
↑R s r = {!!}
{-- (dataRelV i) = dataRelV (s i)
↑r s (dataRelC r) = dataRelC r
--}
--}

↑ : {Γ Δ : Ctxt}
  → Γ ⊆ Δ
  → Form Γ
  → Form Δ
↑ {Γ} {Δ} s (𝕒 x) = 𝕒 (↑ₐ s x)
↑ {Γ} {Δ} s ⊤· = ⊤·
↑ {Γ} {Δ} s ⊥· = ⊥·
↑ {Γ} {Δ} s (f ∧· f₁) = ↑ s f ∧· ↑ s f₁
↑ {Γ} {Δ} s (f ∨· f₁) = ↑ s f ∨· ↑ s f₁
↑ {Γ} {Δ} s (f →· f₁) = ↑ s f →· ↑ s f₁
↑ {Γ} {Δ} s (¬· f) = ¬· ↑ s f
↑ {Γ} {Δ} s (∀· u f) = ∀· u (↑ (⊆، (𝕍𝕌 u) s) f)
↑ {Γ} {Δ} s (∃· u f) = ∃· u (↑ (⊆، (𝕍𝕌 u) s) f)
↑ {Γ} {Δ} s (a ∈ₐ A) = ↑ᵢ s a ∈ₐ ↑ₛ s A
↑ {Γ} {Δ} s (∣ A ∣ₛ＝ n) = ∣ ↑ₛ s A ∣ₛ＝ n
--↑ {Γ} {Δ} s (d ∈ᵢ D) = ↑d s d ∈ᵢ D
--↑ {Γ} {Δ} s (⟨ d₁ ، d₂ ⟩∈ᵣ R) = ⟨ ↑d s d₁ ، ↑d s d₂ ⟩∈ᵣ R
↑ {Γ} {Δ} s (f Ｕ f₁) = ↑ s f Ｕ ↑ s f₁
↑ {Γ} {Δ} s (Ｏ f) = Ｏ (↑ s f)
↑ {Γ} {Δ} s (f Ｓ f₁) = ↑ s f Ｓ ↑ s f₁
↑ {Γ} {Δ} s (Ｙ f) = Ｙ (↑ s f)
↑ {Γ} {Δ} s (Ｂ f) = Ｂ (↑ s f)
↑ {Γ} {Δ} s (Ｆ f) = Ｆ ↑ (⊆، 𝕍ℝ s) f
↑ {Γ} {Δ} s (t₁ ⟨ c ⟩ t₂) = ↑ᵣ s t₁ ⟨ c ⟩ ↑ᵣ s t₂


--↑⸲ : {Γ : Ctxt} {u : 𝕍} → Form Γ → Form (Γ ، u)
--↑⸲ {Γ} {u} a = ↑ ⊆₀ a

↑₀ : {Γ : Ctxt} {u : 𝕍} → Form Γ → Form (Γ ، u)
↑₀ {Γ} {u} a = ↑ ⊆₀ a

↑₀، : {Γ : Ctxt} {u v : 𝕍} → Form (Γ ، v) → Form (Γ ، u ، v)
↑₀، {Γ} {u} {v} a = ↑ ⊆₀، a

↑₀،، : {Γ : Ctxt} {u v w : 𝕍} → Form (Γ ، v ، w) → Form (Γ ، u ، v ، w)
↑₀،، {Γ} {u} {v} {w} f = ↑ ⊆₀،، f

↑₀،،، : {Γ : Ctxt} {u v w x : 𝕍} → Form (Γ ، v ، w ، x) → Form (Γ ، u ، v ، w ، x)
↑₀،،، {Γ} {u} {v} {w} {x} f = ↑ ⊆₀،،، f

↑₁ : {Γ : Ctxt} {u v : 𝕍} → Form Γ → Form (Γ ، u ، v)
↑₁ {Γ} {u} {v} a = ↑ ⊆₁ a

↑₁، : {Γ : Ctxt} {u v w : 𝕍} → Form (Γ ، w) → Form (Γ ، u ، v ، w)
↑₁، {Γ} {u} {v} {w} a = ↑ ⊆₁، a

↑₂ : {Γ : Ctxt} {u v w : 𝕍} → Form Γ → Form (Γ ، u ، v ، w)
↑₂ {Γ} {u} {v} {w} a = ↑ ⊆₂ a

↑₂، : {Γ : Ctxt} {u v w x : 𝕍} → Form (Γ ، x) → Form (Γ ، u ، v ، w ، x)
↑₂، {Γ} {u} {v} {w} {x} a = ↑ ⊆₂، a

↑₃ : {Γ : Ctxt} {u v w x : 𝕍} → Form Γ → Form (Γ ، u ، v ، w ، x)
↑₃ {Γ} {u} {v} {w} {x} a = ↑ ⊆₃ a

⟨⟩⊆ : {Γ : Ctxt} → ⟨⟩ ⊆ Γ
⟨⟩⊆ {Γ} ()

--↑₀ : {Γ : Ctxt} → Form₀ → Form Γ
--↑₀ {Γ} a = ↑ ⟨⟩⊆ a

≡↑ₚ : {Γ Δ : Ctxt}
      (a : AtomProp Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑ₚ s₁ a ≡ ↑ₚ s₂ a
≡↑ₚ {Γ} {Δ} (atomPropV i) s₁ s₂ ≡s = cong atomPropV (≡s i)
≡↑ₚ {Γ} {Δ} (atomPropC x) s₁ s₂ ≡s = refl

≡↑ᵢ : {Γ Δ : Ctxt}
      (a : Agent Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑ᵢ s₁ a ≡ ↑ᵢ s₂ a
≡↑ᵢ {Γ} {Δ} (agentV i) s₁ s₂ ≡s = cong agentV (≡s i)
≡↑ᵢ {Γ} {Δ} (agentC x) s₁ s₂ ≡s = refl

≡↑ₛ : {Γ Δ : Ctxt}
      (a : Agents Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑ₛ s₁ a ≡ ↑ₛ s₂ a
≡↑ₛ {Γ} {Δ} (agentsV i) s₁ s₂ ≡s = cong agentsV (≡s i)
≡↑ₛ {Γ} {Δ} (agentsL x) s₁ s₂ ≡s =
  cong agentsL (map-cong-local (tab (λ {i} z → ≡↑ᵢ i s₁ s₂ ≡s)))
--≡↑ₛ {Γ} {Δ} (agentsS x) s₁ s₂ ≡s = refl

≡↑d : {Γ Δ : Ctxt}
      (a : Data Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑d s₁ a ≡ ↑d s₂ a
≡↑d {Γ} {Δ} (dataV i) s₁ s₂ ≡s = cong dataV (≡s i)
≡↑d {Γ} {Δ} (dataC x) s₁ s₂ ≡s = refl

≡↑ₜ : {Γ Δ : Ctxt}
      (a : Action Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑ₜ s₁ a ≡ ↑ₜ s₂ a
≡↑ₜ {Γ} {Δ} (ActSend p a A) s₁ s₂ ≡s =
  cong₃ ActSend (≡↑d p s₁ s₂ ≡s) (≡↑ᵢ a s₁ s₂ ≡s) (≡↑ₛ A s₁ s₂ ≡s)

≡↑ₑ : {Γ Δ : Ctxt}
      (a : Event Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑ₑ s₁ a ≡ ↑ₑ s₂ a
≡↑ₑ {Γ} {Δ} (EvtReceive p a b) s₁ s₂ ≡s = cong₃ EvtReceive (≡↑d p s₁ s₂ ≡s) (≡↑ᵢ a s₁ s₂ ≡s) (≡↑ᵢ b s₁ s₂ ≡s)
≡↑ₑ {Γ} {Δ} (EvtInternal a d) s₁ s₂ ≡s = cong₂ EvtInternal (≡↑ᵢ a s₁ s₂ ≡s) (≡↑d d s₁ s₂ ≡s)

≡↑f : {Γ Δ : Ctxt}
      (a : Fault Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑f s₁ a ≡ ↑f s₂ a
≡↑f {Γ} {Δ} (FaultCorrect a b) s₁ s₂ ≡s = cong₂ FaultCorrect (≡↑ᵢ a s₁ s₂ ≡s) (≡↑ᵢ b s₁ s₂ ≡s)

≡↑ₐ : {Γ Δ : Ctxt}
      (a : Atom Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑ₐ s₁ a ≡ ↑ₐ s₂ a
≡↑ₐ {Γ} {Δ} (atProp x) s₁ s₂ ≡s = cong atProp (≡↑ₚ x s₁ s₂ ≡s)
≡↑ₐ {Γ} {Δ} (atAction x) s₁ s₂ ≡s = cong atAction (≡↑ₜ x s₁ s₂ ≡s)
≡↑ₐ {Γ} {Δ} (atEvent x) s₁ s₂ ≡s = cong atEvent (≡↑ₑ x s₁ s₂ ≡s)
≡↑ₐ {Γ} {Δ} (atCorrect x) s₁ s₂ ≡s = cong atCorrect (≡↑f x s₁ s₂ ≡s)


{--
↑ᵣ : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) → Res Γ → Res Δ
↑ᵣ s (var x) = var (s x)
↑ᵣ s 𝟎 = 𝟎
↑ᵣ s (𝐬 t) = 𝐬 (↑ᵣ s t)
↑ᵣ s (t ⋆ t₁) = ↑ᵣ s t ⋆ ↑ᵣ s t₁
--}

≡↑ᵣ : {Γ Δ : Ctxt}
      (r : Res Γ)
      (s₁ s₂ : Γ ⊆ Δ)
    → ≡⊆ s₁ s₂
    → ↑ᵣ s₁ r ≡ ↑ᵣ s₂ r
≡↑ᵣ {Γ} {Δ} (var i) s₁ s₂ ≡s = cong var (≡s i)
≡↑ᵣ {Γ} {Δ} 𝟎 s₁ s₂ ≡s = refl
--≡↑ᵣ {Γ} {Δ} (𝐬 r) s₁ s₂ ≡s = cong 𝐬 (≡↑ᵣ r s₁ s₂ ≡s)
≡↑ᵣ {Γ} {Δ} (r ⋆ r₁) s₁ s₂ ≡s = cong₂ _⋆_ (≡↑ᵣ r s₁ s₂ ≡s) (≡↑ᵣ r₁ s₁ s₂ ≡s)

≡↑ : {Γ Δ : Ctxt}
     (F : Form Γ)
     (s₁ s₂ : Γ ⊆ Δ)
   → ≡⊆ s₁ s₂
   → ↑ s₁ F ≡ ↑ s₂ F
≡↑ {Γ} {Δ} (𝕒 x) s₁ s₂ ≡s = cong 𝕒 ((≡↑ₐ x s₁ s₂ ≡s))
≡↑ {Γ} {Δ} ⊤· s₁ s₂ ≡s = refl
≡↑ {Γ} {Δ} ⊥· s₁ s₂ ≡s = refl
≡↑ {Γ} {Δ} (f ∧· f₁) s₁ s₂ ≡s = cong₂ _∧·_ (≡↑ f s₁ s₂ ≡s) (≡↑ f₁ s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (f ∨· f₁) s₁ s₂ ≡s = cong₂ _∨·_ (≡↑ f s₁ s₂ ≡s) (≡↑ f₁ s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (f →· f₁) s₁ s₂ ≡s = cong₂ _→·_ (≡↑ f s₁ s₂ ≡s) (≡↑ f₁ s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (¬· f) s₁ s₂ ≡s = cong ¬·_ (≡↑ f s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (∀· u f) s₁ s₂ ≡s =  cong (∀· u) (≡↑ f (⊆، (𝕍𝕌 u)  s₁) (⊆، (𝕍𝕌 u) s₂) (≡⊆-⊆، (𝕍𝕌 u) s₁ s₂  ≡s))
≡↑ {Γ} {Δ} (∃· u f) s₁ s₂ ≡s =  cong (∃· u) (≡↑ f (⊆، (𝕍𝕌 u)  s₁) (⊆، (𝕍𝕌 u) s₂) (≡⊆-⊆، (𝕍𝕌 u) s₁ s₂  ≡s))
≡↑ {Γ} {Δ} (x ∈ₐ x₁) s₁ s₂ ≡s = cong₂ _∈ₐ_ (≡↑ᵢ x s₁ s₂ ≡s) (≡↑ₛ x₁ s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (∣ A ∣ₛ＝ n) s₁ s₂ ≡s = cong (∣_∣ₛ＝ n) (≡↑ₛ A s₁ s₂ ≡s)
--≡↑ {Γ} {Δ} (x ∈ᵢ x₁) s₁ s₂ ≡s = cong (_∈ᵢ x₁) (≡↑d x s₁ s₂ ≡s)
--≡↑ {Γ} {Δ} (⟨ x ، x₁ ⟩∈ᵣ x₂) s₁ s₂ ≡s = cong₂ (⟨_،_⟩∈ᵣ x₂) (≡↑d x s₁ s₂ ≡s) (≡↑d x₁ s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (f Ｕ f₁) s₁ s₂ ≡s = cong₂ _Ｕ_ (≡↑ f s₁ s₂ ≡s) (≡↑ f₁ s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (Ｏ f) s₁ s₂ ≡s = cong Ｏ (≡↑ f s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (f Ｓ f₁) s₁ s₂ ≡s =  cong₂ _Ｓ_ (≡↑ f s₁ s₂ ≡s) (≡↑ f₁ s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (Ｙ f) s₁ s₂ ≡s = cong Ｙ (≡↑ f s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (Ｂ f) s₁ s₂ ≡s = cong Ｂ (≡↑ f s₁ s₂ ≡s)
≡↑ {Γ} {Δ} (Ｆ f) s₁ s₂ ≡s = cong (Ｆ_) (≡↑ f (⊆، 𝕍ℝ s₁) (⊆، 𝕍ℝ s₂) ( ≡⊆-⊆، 𝕍ℝ s₁ s₂  ≡s))
≡↑ {Γ} {Δ} (t₁ ⟨ c ⟩ t₂) s₁ s₂ ≡s = cong₂ (_⟨ c ⟩_) (≡↑ᵣ t₁ s₁ s₂ ≡s) (≡↑ᵣ t₂ s₁ s₂ ≡s)

{--
≡↑ {Γ} {Δ} (v ⊑ c) s₁ s₂ ≡s = cong (λ x → x ⊑ c) (≡s v)
≡↑ {Γ} {Δ} (v ⊏ c) s₁ s₂ ≡s = cong (λ x → x ⊏ c) (≡s v)
≡↑ {Γ} {Δ} (v ⊒ c) s₁ s₂ ≡s = cong (λ x → x ⊒ c) (≡s v)
≡↑ {Γ} {Δ} (v ⊐ c) s₁ s₂ ≡s = cong (λ x → x ⊐ c) (≡s v)
≡↑ {Γ} {Δ} (v ＝ c) s₁ s₂ ≡s = cong (λ x → x ＝ c) (≡s v)
--}



-- Semantical substitution

⟦𝕌⟧ : 𝕌 → Set
⟦𝕌⟧ 𝕌Agent  = agent
⟦𝕌⟧ 𝕌Agents = agents
⟦𝕌⟧ 𝕌Prop   = atomProp
⟦𝕌⟧ 𝕌Data   = 𝔻

⟦ℝ⟧ : Set
⟦ℝ⟧ = 𝕎

⟦𝕍⟧ : 𝕍 → Set
⟦𝕍⟧ (𝕍𝕌 x) = ⟦𝕌⟧ x
⟦𝕍⟧ 𝕍ℝ = ⟦ℝ⟧

data Sub : Ctxt → Set₁ where
  ●     : Sub ⟨⟩
  _⹁_∶_ : {Γ : Ctxt} (s : Sub Γ) (u : 𝕍) (v : ⟦𝕍⟧ u) → Sub (Γ ، u)

Sub،→ : {Γ : Ctxt} {u : 𝕍} → Sub (Γ ، u) → Sub Γ
Sub،→ {Γ} {u} (s ⹁ .u ∶ v) = s

app-sub : {u : 𝕍} {Γ : Ctxt} (i : ∈Ctxt u Γ) (s : Sub Γ) → ⟦𝕍⟧ u
app-sub {.U} {Γ ، U} (∈Ctxt0 .Γ) (s ⹁ .U ∶ v) = v
app-sub {u} {Γ ، U} (∈CtxtS .U i) (s ⹁ .U ∶ v) = app-sub i s


data ∈Sub {u : 𝕍} (v : ⟦𝕍⟧ u) : {Γ : Ctxt} (i : ∈Ctxt u Γ) (s : Sub Γ) → Set₂ where
  ∈Sub0 : {Γ : Ctxt} (s : Sub Γ) → ∈Sub v (∈Ctxt0 Γ) (s ⹁ u ∶ v)
  ∈SubS : {Γ : Ctxt} (s : Sub Γ) {w : 𝕍} (z : ⟦𝕍⟧ w) (i : ∈Ctxt u Γ)
        → ∈Sub v i s
        → ∈Sub v (∈CtxtS w i) (s ⹁ w ∶ z)

∈Sub-app-sub : {u : 𝕍} {v : ⟦𝕍⟧ u} {Γ : Ctxt} {i : ∈Ctxt u Γ} {s : Sub Γ}
             → ∈Sub v i s
             → app-sub i s ≡ v
∈Sub-app-sub {u} {v} {.(_ ، u)} {.(∈Ctxt0 _)} {.(s ⹁ u ∶ v)} (∈Sub0 s) = refl
∈Sub-app-sub {u} {v} {.(_ ، _)} {.(∈CtxtS _ i)} {.(s ⹁ _ ∶ z)} (∈SubS s z i j) = ∈Sub-app-sub j

Sub⊆ : {Γ Δ : Ctxt} (e : Γ ⊆ Δ) (s₁ : Sub Γ) (s₂ : Sub Δ) → Set₂
Sub⊆ {Γ} {Δ} e s₁ s₂ = {u : 𝕍} (v : ⟦𝕍⟧ u) (i : ∈Ctxt u Γ) (j : ∈Sub v i s₁) → ∈Sub v (e i) s₂

Sub⊆-⊆₀ : {Γ : Ctxt} {u : 𝕍} {v : ⟦𝕍⟧ u} {s : Sub Γ}
        → Sub⊆ ⊆₀ s (s ⹁ u ∶ v)
Sub⊆-⊆₀ {Γ} {u} {v} {s} {z} w i j = ∈SubS s v i j

Sub⊆-⊆₁ : {Γ : Ctxt} {u : 𝕍} {v : ⟦𝕍⟧ u} {a : 𝕍} {b : ⟦𝕍⟧ a} {s : Sub Γ}
        → Sub⊆ ⊆₁ s ((s ⹁ a ∶ b) ⹁ u ∶ v)
Sub⊆-⊆₁ {Γ} {u} {v} {a} {b} {s} {z} w i j = ∈SubS (s ⹁ a ∶ b) v (∈CtxtS a i) (∈SubS s b i j)

Sub⊆-⊆₂ : {Γ : Ctxt} {u : 𝕍} {v : ⟦𝕍⟧ u} {a : 𝕍} {b : ⟦𝕍⟧ a} {m : 𝕍} {n : ⟦𝕍⟧ m} {s : Sub Γ}
        → Sub⊆ ⊆₂ s (((s ⹁ m ∶ n) ⹁ a ∶ b) ⹁ u ∶ v)
Sub⊆-⊆₂ {Γ} {u} {v} {a} {b} {m} {n} {s} {z} w i j =
  ∈SubS ((s ⹁ m ∶ n) ⹁ a ∶ b) v (∈CtxtS _ (∈CtxtS _ i)) (∈SubS (s ⹁ m ∶ n) b (∈CtxtS _ i) (∈SubS s n i j))

Sub⊆-⊆،-⊆₀ : {Γ : Ctxt} {u : 𝕍} {v : ⟦𝕍⟧ u} {a : 𝕍} {b : ⟦𝕍⟧ a} {s : Sub Γ}
        → Sub⊆ (⊆، u ⊆₀) (s ⹁ u ∶ v) ((s ⹁ a ∶ b) ⹁ u ∶ v)
Sub⊆-⊆،-⊆₀ {Γ} {u} {.w} {a} {b} {s} {.u} w .(∈Ctxt0 Γ) (∈Sub0 .s) = ∈Sub0 (s ⹁ a ∶ b)
Sub⊆-⊆،-⊆₀ {Γ} {u} {v} {a} {b} {s} {z} w .(∈CtxtS u i) (∈SubS .s .v i j) = ∈SubS (s ⹁ a ∶ b) v (∈CtxtS a i) (∈SubS s b i j)

∈Ctxt→∈Sub : {u : 𝕍} {Γ : Ctxt} (i : ∈Ctxt u Γ) (s : Sub Γ)
           → Σ (⟦𝕍⟧ u) (λ v → ∈Sub v i s)
∈Ctxt→∈Sub {u} {.(Γ ، u)} (∈Ctxt0 Γ) (s ⹁ .u ∶ v) = v , ∈Sub0 s
∈Ctxt→∈Sub {u} {.(_ ، v)} (∈CtxtS v i) (s ⹁ .v ∶ v₁) with ∈Ctxt→∈Sub i s
... | w , j = w , ∈SubS s v₁ i j

app-sub-Sub⊆ : {u : 𝕍} {Γ Δ : Ctxt} (i : ∈Ctxt u Γ) (e : Γ ⊆ Δ) (s₁ : Sub Γ) (s₂ : Sub Δ)
             → Sub⊆ e s₁ s₂
             → app-sub i s₁ ≡ app-sub (e i) s₂
app-sub-Sub⊆ {u} {Γ} {Δ} i e s₁ s₂ ⊆s with ∈Ctxt→∈Sub i s₁
... | v , j = trans (∈Sub-app-sub j) (sym (∈Sub-app-sub (⊆s v i j)))

Sub⊆-⊆، : {Γ Δ : Ctxt} {s₁ : Sub Γ} {s₂ : Sub Δ} {e : Γ ⊆ Δ} {u : 𝕍} {w : ⟦𝕍⟧ u}
        → Sub⊆ e s₁ s₂
        → Sub⊆ (⊆، u e) (s₁ ⹁ u ∶ w) (s₂ ⹁ u ∶ w)
Sub⊆-⊆، {Γ} {Δ} {s₁} {s₂} {e} {u} {.v} h {.u} v (∈Ctxt0 .Γ) (∈Sub0 .s₁) = ∈Sub0 s₂
Sub⊆-⊆، {Γ} {Δ} {s₁} {s₂} {e} {u} {w} h {z} v (∈CtxtS .u i) (∈SubS .s₁ .w .i j) =
  ∈SubS s₂ w (e i) (h v i j)

-- Syntactical Substitution

C⟦𝕌⟧ : Ctxt → 𝕌 → Set
C⟦𝕌⟧ Δ 𝕌Agent  = Agent Δ
C⟦𝕌⟧ Δ 𝕌Agents = Agents Δ
C⟦𝕌⟧ Δ 𝕌Prop   = AtomProp Δ
C⟦𝕌⟧ Δ 𝕌Data   = Data Δ

C⟦ℝ⟧ : Ctxt → Set
C⟦ℝ⟧ Δ = Res Δ

C⟦𝕍⟧ : Ctxt → 𝕍 → Set
C⟦𝕍⟧ Δ (𝕍𝕌 x) = C⟦𝕌⟧ Δ x
C⟦𝕍⟧ Δ 𝕍ℝ = C⟦ℝ⟧ Δ

CSub : (Γ Δ : Ctxt) → Set
CSub Γ Δ = {u : 𝕍} (i : ∈Ctxt u Γ) → C⟦𝕍⟧ Δ u

𝕌C⟦𝕍⟧ : Ctxt → 𝕍 → Set
𝕌C⟦𝕍⟧ Δ (𝕍𝕌 x) = C⟦𝕌⟧ Δ x
𝕌C⟦𝕍⟧ Δ 𝕍ℝ = ∈Ctxt 𝕍ℝ Δ

𝕌CSub : (Γ Δ : Ctxt) → Set
𝕌CSub Γ Δ = {u : 𝕍} (i : ∈Ctxt u Γ) → 𝕌C⟦𝕍⟧ Δ u

𝕌CSub-var : {Γ : Ctxt} {u : 𝕌} (i : ∈Ctxt (𝕍𝕌 u) Γ) → C⟦𝕌⟧ Γ u
𝕌CSub-var {Γ} {𝕌Agent}  i = agentV i
𝕌CSub-var {Γ} {𝕌Agents} i = agentsV i
𝕌CSub-var {Γ} {𝕌Prop}   i = atomPropV i
𝕌CSub-var {Γ} {𝕌Data}   i = dataV i

𝕌𝕌CSub-var : {Γ : Ctxt} {u : 𝕍} (i : ∈Ctxt u Γ) → 𝕌C⟦𝕍⟧ Γ u
𝕌𝕌CSub-var {Γ} {𝕍𝕌 x} i = 𝕌CSub-var i
𝕌𝕌CSub-var {Γ} {𝕍ℝ}   i = i

ℝCSub-var : {Γ : Ctxt} (i : ∈Ctxt 𝕍ℝ Γ) → C⟦ℝ⟧ Γ
ℝCSub-var {Γ} i = var i

CSub-var : {Γ : Ctxt} {u : 𝕍} (i : ∈Ctxt u Γ) → C⟦𝕍⟧ Γ u
CSub-var {Γ} {𝕍𝕌 x} i = 𝕌CSub-var i
CSub-var {Γ} {𝕍ℝ} i = ℝCSub-var i

𝕍CSub-var : {Γ : Ctxt} {u : 𝕍} (i : ∈Ctxt u Γ) → 𝕌C⟦𝕍⟧ Γ u
𝕍CSub-var {Γ} {𝕍𝕌 x} i = 𝕌CSub-var i
𝕍CSub-var {Γ} {𝕍ℝ} i = i

↑u : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) {u : 𝕌} → C⟦𝕌⟧ Γ u → C⟦𝕌⟧ Δ u
↑u {Γ} {Δ} s {𝕌Agent}  x = ↑ᵢ s x
↑u {Γ} {Δ} s {𝕌Agents} x = ↑ₛ s x
↑u {Γ} {Δ} s {𝕌Prop}   x = ↑ₚ s x
↑u {Γ} {Δ} s {𝕌Data}   x = ↑d s x

↑ℝ : {Γ Δ : Ctxt} → Γ ⊆ Δ → C⟦ℝ⟧ Γ → C⟦ℝ⟧ Δ
↑ℝ {Γ} {Δ} s v = ↑ᵣ s v

↑v : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) {v : 𝕍} → C⟦𝕍⟧ Γ v → C⟦𝕍⟧ Δ v
↑v {Γ} {Δ} s {𝕍𝕌 u} x = ↑u s {u} x
↑v {Γ} {Δ} s {𝕍ℝ} x = ↑ℝ s x

𝕌↑v : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) {u : 𝕍} → 𝕌C⟦𝕍⟧ Γ u → 𝕌C⟦𝕍⟧ Δ u
𝕌↑v {Γ} {Δ} s {𝕍𝕌 x₁} x = ↑v s x
𝕌↑v {Γ} {Δ} s {𝕍ℝ} x = s x

CSub، : {Γ Δ : Ctxt} (u : 𝕍)
      → CSub Γ Δ
      → CSub (Γ ، u) (Δ ، u)
CSub، {Γ} {Δ} u s (∈Ctxt0 .Γ) = CSub-var {Δ ، u} {u} (∈Ctxt0 Δ)
CSub، {Γ} {Δ} u s {u₁} (∈CtxtS .u i) = ↑v {Δ} {Δ ، u} ⊆₀ {u₁} (s i)

𝕌CSub، : {Γ Δ : Ctxt} (u : 𝕍)
       → 𝕌CSub Γ Δ
       → 𝕌CSub (Γ ، u) (Δ ، u)
𝕌CSub، {Γ} {Δ} u s {.u} (∈Ctxt0 .Γ) = 𝕍CSub-var {Δ ، u} {u} (∈Ctxt0 Δ)
𝕌CSub، {Γ} {Δ} u s {v} (∈CtxtS .u i) = 𝕌↑v {Δ} {Δ ، u} ⊆₀ {v} (s i)

CSub،ₗ : {Γ : Ctxt} {u : 𝕍} (v : C⟦𝕍⟧ Γ u)
      → CSub (Γ ، u) Γ
CSub،ₗ {Γ} {u} v (∈Ctxt0 .Γ) = v
CSub،ₗ {Γ} {u} v (∈CtxtS .u i) = CSub-var i

𝕌CSub،ₗ : {Γ : Ctxt} {u : 𝕍} (v : 𝕌C⟦𝕍⟧ Γ u)
       → 𝕌CSub (Γ ، u) Γ
𝕌CSub،ₗ {Γ} {u} v (∈Ctxt0 .Γ) = v -- v
𝕌CSub،ₗ {Γ} {u} v (∈CtxtS .u i) = 𝕌𝕌CSub-var i

sub-AtomProp : {Γ Δ : Ctxt} (a : AtomProp Γ) (s : CSub Γ Δ) → AtomProp Δ
sub-AtomProp {Γ} {Δ} (atomPropV i) s = s i
sub-AtomProp {Γ} {Δ} (atomPropC x) s = atomPropC x

𝕌sub-AtomProp : {Γ Δ : Ctxt} (a : AtomProp Γ) (s : 𝕌CSub Γ Δ) → AtomProp Δ
𝕌sub-AtomProp {Γ} {Δ} (atomPropV i) s = s i
𝕌sub-AtomProp {Γ} {Δ} (atomPropC x) s = atomPropC x

sub-Agent : {Γ Δ : Ctxt} (a : Agent Γ) (s : CSub Γ Δ) → Agent Δ
sub-Agent {Γ} {Δ} (agentV i) s = s i
sub-Agent {Γ} {Δ} (agentC x) s = agentC x

𝕌sub-Agent : {Γ Δ : Ctxt} (a : Agent Γ) (s : 𝕌CSub Γ Δ) → Agent Δ
𝕌sub-Agent {Γ} {Δ} (agentV i) s = s i
𝕌sub-Agent {Γ} {Δ} (agentC x) s = agentC x

sub-Agents : {Γ Δ : Ctxt} (A : Agents Γ) (s : CSub Γ Δ) → Agents Δ
sub-Agents {Γ} {Δ} (agentsV i) s = s i
sub-Agents {Γ} {Δ} (agentsL l) s = agentsL (Data.List.map (λ x → sub-Agent x s) l)
--sub-Agents {Γ} {Δ} (agentsS x) s = agentsS x

𝕌sub-Agents : {Γ Δ : Ctxt} (A : Agents Γ) (s : 𝕌CSub Γ Δ) → Agents Δ
𝕌sub-Agents {Γ} {Δ} (agentsV i) s = s i
𝕌sub-Agents {Γ} {Δ} (agentsL l) s = agentsL (Data.List.map (λ x → 𝕌sub-Agent x s) l)
--𝕌sub-Agents {Γ} {Δ} (agentsS x) s = agentsS x

sub-Data : {Γ Δ : Ctxt} (d : Data Γ) (s : CSub Γ Δ) → Data Δ
sub-Data {Γ} {Δ} (dataV i) s = s i
sub-Data {Γ} {Δ} (dataC x) s = dataC x

𝕌sub-Data : {Γ Δ : Ctxt} (d : Data Γ) (s : 𝕌CSub Γ Δ) → Data Δ
𝕌sub-Data {Γ} {Δ} (dataV i) s = s i
𝕌sub-Data {Γ} {Δ} (dataC x) s = dataC x

sub-Action : {Γ Δ : Ctxt} (a : Action Γ) (s : CSub Γ Δ) → Action Δ
sub-Action {Γ} {Δ} (ActSend p a A) s = ActSend (sub-Data p s) (sub-Agent a s) (sub-Agents A s)

𝕌sub-Action : {Γ Δ : Ctxt} (a : Action Γ) (s : 𝕌CSub Γ Δ) → Action Δ
𝕌sub-Action {Γ} {Δ} (ActSend p a A) s = ActSend (𝕌sub-Data p s) (𝕌sub-Agent a s) (𝕌sub-Agents A s)

sub-Event : {Γ Δ : Ctxt} (e : Event Γ) (s : CSub Γ Δ) → Event Δ
sub-Event {Γ} {Δ} (EvtReceive p a b) s = EvtReceive (sub-Data p s) (sub-Agent a s) (sub-Agent b s)
sub-Event {Γ} {Δ} (EvtInternal a d) s = EvtInternal (sub-Agent a s) (sub-Data d s)

𝕌sub-Event : {Γ Δ : Ctxt} (e : Event Γ) (s : 𝕌CSub Γ Δ) → Event Δ
𝕌sub-Event {Γ} {Δ} (EvtReceive p a b) s = EvtReceive (𝕌sub-Data p s) (𝕌sub-Agent a s) (𝕌sub-Agent b s)
𝕌sub-Event {Γ} {Δ} (EvtInternal a d) s = EvtInternal (𝕌sub-Agent a s) (𝕌sub-Data d s)

sub-Fault : {Γ Δ : Ctxt} (f : Fault Γ) (s : CSub Γ Δ) → Fault Δ
sub-Fault {Γ} {Δ} (FaultCorrect a b) s = FaultCorrect (sub-Agent a s) (sub-Agent b s)

𝕌sub-Fault : {Γ Δ : Ctxt} (f : Fault Γ) (s : 𝕌CSub Γ Δ) → Fault Δ
𝕌sub-Fault {Γ} {Δ} (FaultCorrect a b) s = FaultCorrect (𝕌sub-Agent a s) (𝕌sub-Agent b s)

sub-Atom : {Γ Δ : Ctxt} (a : Atom Γ) (s : CSub Γ Δ) → Atom Δ
sub-Atom {Γ} {Δ} (atProp    x) s = atProp    (sub-AtomProp x s)
sub-Atom {Γ} {Δ} (atAction  x) s = atAction  (sub-Action   x s)
sub-Atom {Γ} {Δ} (atEvent   x) s = atEvent   (sub-Event    x s)
sub-Atom {Γ} {Δ} (atCorrect x) s = atCorrect (sub-Fault    x s)

𝕌sub-Atom : {Γ Δ : Ctxt} (a : Atom Γ) (s : 𝕌CSub Γ Δ) → Atom Δ
𝕌sub-Atom {Γ} {Δ} (atProp    x) s = atProp    (𝕌sub-AtomProp x s)
𝕌sub-Atom {Γ} {Δ} (atAction  x) s = atAction  (𝕌sub-Action   x s)
𝕌sub-Atom {Γ} {Δ} (atEvent   x) s = atEvent   (𝕌sub-Event    x s)
𝕌sub-Atom {Γ} {Δ} (atCorrect x) s = atCorrect (𝕌sub-Fault    x s)

sub-Res : {Γ Δ : Ctxt} (r : Res Γ) (s : CSub Γ Δ) → Res Δ
sub-Res {Γ} {Δ} (var i) s = s i
sub-Res {Γ} {Δ} 𝟎 s = 𝟎
--sub-Res {Γ} {Δ} (𝐬 r) s = 𝐬 (sub-Res r s)
sub-Res {Γ} {Δ} (r₁ ⋆ r₂) s = sub-Res r₁ s ⋆ sub-Res r₂ s

𝕌sub-Res : {Γ Δ : Ctxt} (r : Res Γ) (s : 𝕌CSub Γ Δ) → Res Δ
𝕌sub-Res {Γ} {Δ} (var i) s = var (s i)
𝕌sub-Res {Γ} {Δ} 𝟎 s = 𝟎
--𝕌sub-Res {Γ} {Δ} (𝐬 r) s = 𝐬 (𝕌sub-Res r s)
𝕌sub-Res {Γ} {Δ} (r₁ ⋆ r₂) s = 𝕌sub-Res r₁ s ⋆ 𝕌sub-Res r₂ s

-- substitution on the quantifiable variables only - resources are left untouched
substitute : {Γ Δ : Ctxt} (f : Form Γ) (s : 𝕌CSub Γ Δ) → Form Δ
substitute {Γ} {Δ} (𝕒 p) s = 𝕒 (𝕌sub-Atom p s)
substitute {Γ} {Δ} ⊤· s = ⊤·
substitute {Γ} {Δ} ⊥· s = ⊥·
substitute {Γ} {Δ} (f ∧· f₁) s = substitute f s ∧· substitute f₁ s
substitute {Γ} {Δ} (f ∨· f₁) s = substitute f s ∨· substitute f₁ s
substitute {Γ} {Δ} (f →· f₁) s = substitute f s →· substitute f₁ s
substitute {Γ} {Δ} (¬· f) s = ¬· (substitute f s)
substitute {Γ} {Δ} (∀· u f) s = ∀· u (substitute f (𝕌CSub، (𝕍𝕌 u) s))
substitute {Γ} {Δ} (∃· u f) s = ∃· u (substitute f (𝕌CSub، (𝕍𝕌 u) s))
substitute {Γ} {Δ} (a ∈ₐ A) s = 𝕌sub-Agent a s ∈ₐ 𝕌sub-Agents A s
substitute {Γ} {Δ} (∣ A ∣ₛ＝ n) s = ∣ 𝕌sub-Agents A s ∣ₛ＝ n
--substitute {Γ} {Δ} (d ∈ᵢ D) s = 𝕌sub-Data d s ∈ᵢ D
--substitute {Γ} {Δ} (⟨ d₁ ، d₂ ⟩∈ᵣ R) s = ⟨ 𝕌sub-Data d₁ s ، 𝕌sub-Data d₂ s ⟩∈ᵣ R
substitute {Γ} {Δ} (f Ｕ f₁) s = substitute f s Ｕ substitute f₁ s
substitute {Γ} {Δ} (Ｏ f) s = Ｏ (substitute f s)
substitute {Γ} {Δ} (f Ｓ f₁) s = substitute f s Ｓ substitute f₁ s
substitute {Γ} {Δ} (Ｙ f) s = Ｙ (substitute f s)
substitute {Γ} {Δ} (Ｂ f) s = Ｂ (substitute f s)
substitute {Γ} {Δ} (Ｆ f) s = Ｆ substitute f (𝕌CSub، 𝕍ℝ s)
substitute {Γ} {Δ} (t₁ ⟨ c ⟩ t₂) s = 𝕌sub-Res t₁ s ⟨ c ⟩ 𝕌sub-Res t₂ s

-- general substitution
sub : {Γ Δ : Ctxt} (f : Form Γ) (s : CSub Γ Δ) → Form Δ
sub {Γ} {Δ} (𝕒 p) s = 𝕒 (sub-Atom p s)
sub {Γ} {Δ} ⊤· s = ⊤·
sub {Γ} {Δ} ⊥· s = ⊥·
sub {Γ} {Δ} (f ∧· f₁) s = sub f s ∧· sub f₁ s
sub {Γ} {Δ} (f ∨· f₁) s = sub f s ∨· sub f₁ s
sub {Γ} {Δ} (f →· f₁) s = sub f s →· sub f₁ s
sub {Γ} {Δ} (¬· f) s = ¬· (sub f s)
sub {Γ} {Δ} (∀· u f) s = ∀· u (sub f (CSub، (𝕍𝕌 u) s))
sub {Γ} {Δ} (∃· u f) s = ∃· u (sub f (CSub، (𝕍𝕌 u) s))
sub {Γ} {Δ} (a ∈ₐ A) s = sub-Agent a s ∈ₐ sub-Agents A s
sub {Γ} {Δ} (∣ A ∣ₛ＝ n) s = ∣ sub-Agents A s ∣ₛ＝ n
--sub {Γ} {Δ} (d ∈ᵢ D) s = sub-Data d s ∈ᵢ D
--sub {Γ} {Δ} (⟨ d₁ ، d₂ ⟩∈ᵣ R) s = ⟨ sub-Data d₁ s ، sub-Data d₂ s ⟩∈ᵣ R
sub {Γ} {Δ} (f Ｕ f₁) s = sub f s Ｕ sub f₁ s
sub {Γ} {Δ} (Ｏ f) s = Ｏ (sub f s)
sub {Γ} {Δ} (f Ｓ f₁) s = sub f s Ｓ sub f₁ s
sub {Γ} {Δ} (Ｙ f) s = Ｙ (sub f s)
sub {Γ} {Δ} (Ｂ f) s = Ｂ (sub f s)
sub {Γ} {Δ} (Ｆ f) s = Ｆ (sub f (CSub، 𝕍ℝ s))
sub {Γ} {Δ} (t₁ ⟨ c ⟩ t₂) s = sub-Res t₁ s ⟨ c ⟩ sub-Res t₂ s

subℝ : {Γ : Ctxt} (f : Form (Γ ، 𝕍ℝ)) (r : Res Γ) → Form Γ
subℝ {Γ} f r = sub f (CSub،ₗ r)

sub-Resℝ : {Γ : Ctxt} (r : Res (Γ ، 𝕍ℝ)) (s : Res Γ) → Res Γ
sub-Resℝ {Γ} r s = sub-Res r (CSub،ₗ s)

sub-Res-↑ᵣ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (r : Res Γ)
            → sub-Res (↑ᵣ₀ r) (CSub،ₗ {Γ} {u} v) ≡ r
sub-Res-↑ᵣ₀ Γ u v (var i) = refl
sub-Res-↑ᵣ₀ Γ u v 𝟎 = refl
--sub-Res-↑ᵣ₀ Γ u v (𝐬 r) = cong 𝐬 (sub-Res-↑ᵣ₀ Γ u v r)
sub-Res-↑ᵣ₀ Γ u v (r ⋆ r₁) = cong₂ _⋆_ (sub-Res-↑ᵣ₀ Γ u v r) (sub-Res-↑ᵣ₀ Γ u v r₁)

sub-Agent-↑ᵢ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Agent Γ)
              → sub-Agent (↑ᵢ₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-Agent-↑ᵢ₀ Γ u v (agentV i) = refl
sub-Agent-↑ᵢ₀ Γ u v (agentC x) = refl

sub-AgentL-↑ᵢ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : List (Agent Γ))
               → Data.List.map (λ z → sub-Agent z (CSub،ₗ {Γ} {u} v)) (Data.List.map ↑ᵢ₀ a) ≡ a
sub-AgentL-↑ᵢ₀ Γ u v [] = refl
sub-AgentL-↑ᵢ₀ Γ u v (x ∷ a) = cong₂ _∷_ (sub-Agent-↑ᵢ₀ Γ u v x) (sub-AgentL-↑ᵢ₀ Γ u v a)

sub-Agents-↑ᵢ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Agents Γ)
               → sub-Agents (↑ₛ₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-Agents-↑ᵢ₀ Γ u v (agentsV i) = refl
sub-Agents-↑ᵢ₀ Γ u v (agentsL x) = cong agentsL (sub-AgentL-↑ᵢ₀ Γ u v x)
--sub-Agents-↑ᵢ₀ Γ u v (agentsS x) = refl

sub-Data-↑d₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Data Γ)
             → sub-Data (↑d₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-Data-↑d₀ Γ u v (dataV i) = refl
sub-Data-↑d₀ Γ u v (dataC x) = refl

sub-AtomProp-↑ₚ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : AtomProp Γ)
                 → sub-AtomProp (↑ₚ₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-AtomProp-↑ₚ₀ Γ u v (atomPropV i) = refl
sub-AtomProp-↑ₚ₀ Γ u v (atomPropC x) = refl

sub-Action-↑ₜ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Action Γ)
               → sub-Action (↑ₜ₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-Action-↑ₜ₀ Γ u v (ActSend p a A) =
  cong₃ ActSend (sub-Data-↑d₀ Γ u v p) (sub-Agent-↑ᵢ₀ Γ u v a) (sub-Agents-↑ᵢ₀ Γ u v A)

sub-Event-↑ₑ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Event Γ)
              → sub-Event (↑ₑ₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-Event-↑ₑ₀ Γ u v (EvtReceive p a b) =
  cong₃ EvtReceive (sub-Data-↑d₀ Γ u v p) (sub-Agent-↑ᵢ₀ Γ u v a) (sub-Agent-↑ᵢ₀ Γ u v b)
sub-Event-↑ₑ₀ Γ u v (EvtInternal a d) =
  cong₂ EvtInternal (sub-Agent-↑ᵢ₀ Γ u v a) (sub-Data-↑d₀ Γ u v d)

sub-Fault-↑f₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Fault Γ)
              → sub-Fault (↑f₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-Fault-↑f₀ Γ u v (FaultCorrect a b) =
  cong₂ FaultCorrect (sub-Agent-↑ᵢ₀ Γ u v a) (sub-Agent-↑ᵢ₀ Γ u v b)

sub-Atom-↑ₐ₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Atom Γ)
             → sub-Atom (↑ₐ₀ a) (CSub،ₗ {Γ} {u} v) ≡ a
sub-Atom-↑ₐ₀ Γ u v (atProp x) = cong atProp (sub-AtomProp-↑ₚ₀ Γ u v x)
sub-Atom-↑ₐ₀ Γ u v (atAction x) = cong atAction (sub-Action-↑ₜ₀ Γ u v x)
sub-Atom-↑ₐ₀ Γ u v (atEvent x) = cong atEvent (sub-Event-↑ₑ₀ Γ u v x)
sub-Atom-↑ₐ₀ Γ u v (atCorrect x) = cong atCorrect (sub-Fault-↑f₀ Γ u v x)

{--
substitute {Γ} {Δ} (v ⊑ c) s = lower (s v) ⊑ c
substitute {Γ} {Δ} (v ⊏ c) s = lower (s v) ⊏ c
substitute {Γ} {Δ} (v ⊒ c) s = lower (s v) ⊒ c
substitute {Γ} {Δ} (v ⊐ c) s = lower (s v) ⊐ c
substitute {Γ} {Δ} (v ＝ c) s = lower (s v) ＝ c
--}

-- Properties

_＋_ : (Γ Δ : Ctxt) → Ctxt
Γ ＋ ⟨⟩ = Γ
Γ ＋ (Δ ، U) = (Γ ＋ Δ) ، U

_＋ₛ_ : {Δ Γ : Ctxt} → Sub Γ → Sub Δ → Sub (Γ ＋ Δ)
_＋ₛ_ {.⟨⟩} {Γ} m ● = m
_＋ₛ_ {.(_ ، u)} {Γ} m (s ⹁ u ∶ v) = (m ＋ₛ s) ⹁ u ∶ v

CSub،＋ : {Γ Δ : Ctxt} {u : 𝕍}
         (v : C⟦𝕍⟧ Γ u)
       → CSub ((Γ ، u) ＋ Δ) (Γ ＋ Δ)
CSub،＋ {Γ} {⟨⟩} {u} v = CSub،ₗ v
CSub،＋ {Γ} {Δ ، U} {u} v = CSub، U (CSub،＋ v)

⊆،＋ : {Γ Δ : Ctxt} {u : 𝕍} → (Γ ＋ Δ) ⊆ ((Γ ، u) ＋ Δ)
⊆،＋ {Γ} {⟨⟩} {u} {x} i = ∈CtxtS u i
⊆،＋ {Γ} {Δ ، U} {u} {x} i = ⊆، U (⊆،＋ {Γ} {Δ} {u}) i

CSub＋ : {Γ₁ Γ₂ Δ : Ctxt}
       → CSub Γ₁ Γ₂
       → CSub (Γ₁ ＋ Δ) (Γ₂ ＋ Δ)
CSub＋ {Γ₁} {Γ₂} {⟨⟩} s = s
CSub＋ {Γ₁} {Γ₂} {Δ ، U} s = CSub، U (CSub＋ s)

⊆،* : {Γ Δ Ψ : Ctxt} → Γ ⊆ Δ → (Γ ＋ Ψ) ⊆ (Δ ＋ Ψ)
⊆،* {Γ} {Δ} {⟨⟩} e = e
⊆،* {Γ} {Δ} {Ψ ، U} e = ⊆، U (⊆،* e)

⊆＋ : {Γ Δ : Ctxt} → Γ ⊆ (Γ ＋ Δ)
⊆＋ {Γ} {⟨⟩} {x} i = i
⊆＋ {Γ} {Δ ، U} {x} i = ∈CtxtS U (⊆＋ {Γ} {Δ} i)

⊆＋،⋆ : {Γ Δ Ψ : Ctxt} → (Γ ＋ Ψ) ⊆ ((Γ ＋ Δ) ＋ Ψ)
⊆＋،⋆ {Γ} {Δ} {Ψ} = ⊆،* {Γ} {Γ ＋ Δ} {Ψ} (⊆＋ {Γ} {Δ})

CSub،＋-var-res : {Γ Δ : Ctxt} {u : 𝕍} (v : C⟦𝕍⟧ Γ u) (i : ∈Ctxt 𝕍World (Γ ＋ Δ))
               → CSub،＋ {Γ} {Δ} {u} v (⊆،＋ i) ≡ var i
CSub،＋-var-res {Γ} {⟨⟩} {u} v i = refl
CSub،＋-var-res {Γ} {Δ ، .𝕍World} {u} v (∈Ctxt0 .(Γ ＋ Δ)) = refl
CSub،＋-var-res {Γ} {Δ ، U} {u} v (∈CtxtS .U i) =
  cong (↑v {Γ ＋ Δ} {Γ ＋ Δ ، U} ⊆₀ {𝕍World}) (CSub،＋-var-res {Γ} {Δ} {u} v i)

sub-Res-↑ᵣ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (r : Res (Γ ＋ Δ))
             → sub-Res (↑ᵣ ⊆،＋ r) (CSub،＋ {Γ} {Δ} {u} v) ≡ r
sub-Res-↑ᵣ،＋ Γ Δ u v (var i) = CSub،＋-var-res {Γ} {Δ} {u} v i
sub-Res-↑ᵣ،＋ Γ Δ u v 𝟎 = refl
--sub-Res-↑ᵣ،＋ Γ Δ u v (𝐬 r) = cong 𝐬 (sub-Res-↑ᵣ،＋ Γ Δ u v r)
sub-Res-↑ᵣ،＋ Γ Δ u v (r ⋆ r₁) = cong₂ _⋆_ (sub-Res-↑ᵣ،＋ Γ Δ u v r) (sub-Res-↑ᵣ،＋ Γ Δ u v r₁)

CSub،＋-var-agent : {Γ Δ : Ctxt} {u : 𝕍} (v : C⟦𝕍⟧ Γ u) (i : ∈Ctxt 𝕍Agent (Γ ＋ Δ))
                 → CSub،＋ {Γ} {Δ} {u} v (⊆،＋ i) ≡ agentV i
CSub،＋-var-agent {Γ} {⟨⟩} {u} v i = refl
CSub،＋-var-agent {Γ} {Δ ، .𝕍Agent} {u} v (∈Ctxt0 .(Γ ＋ Δ)) = refl
CSub،＋-var-agent {Γ} {Δ ، U} {u} v (∈CtxtS .U i) =
  cong (↑v {Γ ＋ Δ} {Γ ＋ Δ ، U} ⊆₀ {𝕍Agent}) (CSub،＋-var-agent {Γ} {Δ} {u} v i)

sub-Agent-↑ᵢ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Agent (Γ ＋ Δ))
              → sub-Agent (↑ᵢ ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-Agent-↑ᵢ،＋ Γ Δ u v (agentV i) = CSub،＋-var-agent {Γ} {Δ} {u} v i
sub-Agent-↑ᵢ،＋ Γ Δ u v (agentC x) = refl

sub-AgentL-↑ᵢ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : List (Agent (Γ ＋ Δ)))
               → Data.List.map (λ z → sub-Agent z (CSub،＋ {Γ} {Δ} {u} v)) (Data.List.map (↑ᵢ ⊆،＋) a) ≡ a
sub-AgentL-↑ᵢ،＋ Γ Δ u v [] = refl
sub-AgentL-↑ᵢ،＋ Γ Δ u v (x ∷ a) = cong₂ _∷_ (sub-Agent-↑ᵢ،＋ Γ Δ u v x) (sub-AgentL-↑ᵢ،＋ Γ Δ u v a)

CSub،＋-var-agents : {Γ Δ : Ctxt} {u : 𝕍} (v : C⟦𝕍⟧ Γ u) (i : ∈Ctxt 𝕍Agents (Γ ＋ Δ))
                  → CSub،＋ {Γ} {Δ} {u} v (⊆،＋ i) ≡ agentsV i
CSub،＋-var-agents {Γ} {⟨⟩} {u} v i = refl
CSub،＋-var-agents {Γ} {Δ ، .𝕍Agents} {u} v (∈Ctxt0 .(Γ ＋ Δ)) = refl
CSub،＋-var-agents {Γ} {Δ ، U} {u} v (∈CtxtS .U i) =
  cong (↑v {Γ ＋ Δ} {Γ ＋ Δ ، U} ⊆₀ {𝕍Agents}) (CSub،＋-var-agents {Γ} {Δ} {u} v i)

sub-Agents-↑ₛ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Agents (Γ ＋ Δ))
                → sub-Agents (↑ₛ ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-Agents-↑ₛ،＋ Γ Δ u v (agentsV i) = CSub،＋-var-agents {Γ} {Δ} {u} v i
sub-Agents-↑ₛ،＋ Γ Δ u v (agentsL x) = cong agentsL (sub-AgentL-↑ᵢ،＋ Γ Δ u v x)
--sub-Agents-↑ₛ،＋ Γ Δ u v (agentsS x) = refl

CSub،＋-var-data : {Γ Δ : Ctxt} {u : 𝕍} (v : C⟦𝕍⟧ Γ u) (i : ∈Ctxt 𝕍Data (Γ ＋ Δ))
                → CSub،＋ {Γ} {Δ} {u} v (⊆،＋ i) ≡ dataV i
CSub،＋-var-data {Γ} {⟨⟩} {u} v i = refl
CSub،＋-var-data {Γ} {Δ ، .𝕍Data} {u} v (∈Ctxt0 .(Γ ＋ Δ)) = refl
CSub،＋-var-data {Γ} {Δ ، U} {u} v (∈CtxtS .U i) =
  cong (↑v {Γ ＋ Δ} {Γ ＋ Δ ، U} ⊆₀ {𝕍Data}) (CSub،＋-var-data {Γ} {Δ} {u} v i)

sub-Data-↑d،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Data (Γ ＋ Δ))
              → sub-Data (↑d  ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-Data-↑d،＋ Γ Δ u v (dataV i) = CSub،＋-var-data {Γ} {Δ} {u} v i
sub-Data-↑d،＋ Γ Δ u v (dataC x) = refl

CSub،＋-var-prop : {Γ Δ : Ctxt} {u : 𝕍} (v : C⟦𝕍⟧ Γ u) (i : ∈Ctxt 𝕍Prop (Γ ＋ Δ))
                → CSub،＋ {Γ} {Δ} {u} v (⊆،＋ i) ≡ atomPropV i
CSub،＋-var-prop {Γ} {⟨⟩} {u} v i = refl
CSub،＋-var-prop {Γ} {Δ ، .𝕍Prop} {u} v (∈Ctxt0 .(Γ ＋ Δ)) = refl
CSub،＋-var-prop {Γ} {Δ ، U} {u} v (∈CtxtS .U i) =
  cong (↑v {Γ ＋ Δ} {Γ ＋ Δ ، U} ⊆₀ {𝕍Prop}) (CSub،＋-var-prop {Γ} {Δ} {u} v i)

sub-AtomProp-↑ₚ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : AtomProp (Γ ＋ Δ))
                 → sub-AtomProp (↑ₚ ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-AtomProp-↑ₚ،＋ Γ Δ u v (atomPropV i) = CSub،＋-var-prop {Γ} {Δ} {u} v i
sub-AtomProp-↑ₚ،＋ Γ Δ u v (atomPropC x) = refl

sub-Action-↑ₜ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Action (Γ ＋ Δ))
                → sub-Action (↑ₜ ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-Action-↑ₜ،＋ Γ Δ u v (ActSend p a A) =
  cong₃ ActSend (sub-Data-↑d،＋ Γ Δ u v p) (sub-Agent-↑ᵢ،＋ Γ Δ u v a) (sub-Agents-↑ₛ،＋ Γ Δ u v A)

sub-Event-↑ₑ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Event (Γ ＋ Δ))
               → sub-Event (↑ₑ ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-Event-↑ₑ،＋ Γ Δ u v (EvtReceive p a b) =
  cong₃ EvtReceive (sub-Data-↑d،＋ Γ Δ u v p) (sub-Agent-↑ᵢ،＋ Γ Δ u v a) (sub-Agent-↑ᵢ،＋ Γ Δ u v b)
sub-Event-↑ₑ،＋ Γ Δ u v (EvtInternal a d) =
  cong₂ EvtInternal (sub-Agent-↑ᵢ،＋ Γ Δ u v a) (sub-Data-↑d،＋ Γ Δ u v d)

sub-Fault-↑f،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Fault (Γ ＋ Δ))
               → sub-Fault (↑f ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-Fault-↑f،＋ Γ Δ u v (FaultCorrect a b) =
  cong₂ FaultCorrect (sub-Agent-↑ᵢ،＋ Γ Δ u v a) (sub-Agent-↑ᵢ،＋ Γ Δ u v b)

sub-Atom-↑ₐ،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (a : Atom (Γ ＋ Δ))
              → sub-Atom (↑ₐ ⊆،＋ a) (CSub،＋ {Γ} {Δ} {u} v) ≡ a
sub-Atom-↑ₐ،＋ Γ Δ u v (atProp x) = cong atProp (sub-AtomProp-↑ₚ،＋ Γ Δ u v x)
sub-Atom-↑ₐ،＋ Γ Δ u v (atAction x) = cong atAction (sub-Action-↑ₜ،＋ Γ Δ u v x)
sub-Atom-↑ₐ،＋ Γ Δ u v (atEvent x) = cong atEvent (sub-Event-↑ₑ،＋ Γ Δ u v x)
sub-Atom-↑ₐ،＋ Γ Δ u v (atCorrect x) = cong atCorrect (sub-Fault-↑f،＋ Γ Δ u v x)

sub-↑،＋ : (Γ Δ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (f : Form (Γ ＋ Δ))
        → sub (↑ ⊆،＋ f) (CSub،＋ {Γ} {Δ} {u} v) ≡ f
sub-↑،＋ Γ Δ u v (𝕒 x) = cong 𝕒 (sub-Atom-↑ₐ،＋ Γ Δ u v x)
sub-↑،＋ Γ Δ u v ⊤· = refl
sub-↑،＋ Γ Δ u v ⊥· = refl
sub-↑،＋ Γ Δ u v (f ∧· f₁) = cong₂ _∧·_ (sub-↑،＋ Γ Δ u v f) (sub-↑،＋ Γ Δ u v f₁)
sub-↑،＋ Γ Δ u v (f ∨· f₁) = cong₂ _∨·_ (sub-↑،＋ Γ Δ u v f) (sub-↑،＋ Γ Δ u v f₁)
sub-↑،＋ Γ Δ u v (f →· f₁) = cong₂ _→·_ (sub-↑،＋ Γ Δ u v f) (sub-↑،＋ Γ Δ u v f₁)
sub-↑،＋ Γ Δ u v (¬· f) = cong ¬·_ (sub-↑،＋ Γ Δ u v f)
sub-↑،＋ Γ Δ u v (∀· u₁ f) = cong (∀· u₁) (sub-↑،＋ Γ (Δ ، 𝕍𝕌 u₁) u v f)
sub-↑،＋ Γ Δ u v (∃· u₁ f) = cong (∃· u₁) (sub-↑،＋ Γ (Δ ، 𝕍𝕌 u₁) u v f)
sub-↑،＋ Γ Δ u v (x ∈ₐ x₁) = cong₂ _∈ₐ_ (sub-Agent-↑ᵢ،＋ Γ Δ u v x) (sub-Agents-↑ₛ،＋ Γ Δ u v x₁)
sub-↑،＋ Γ Δ u v (∣ A ∣ₛ＝ n) = cong (∣_∣ₛ＝ n) (sub-Agents-↑ₛ،＋ Γ Δ u v A)
--sub-↑،＋ Γ Δ u v (x ∈ᵢ x₁) = cong₂ _∈ᵢ_ (sub-Data-↑d،＋ Γ Δ u v x) refl
--sub-↑،＋ Γ Δ u v (⟨ x ، x₁ ⟩∈ᵣ x₂) = cong₃ ⟨_،_⟩∈ᵣ_ (sub-Data-↑d،＋ Γ Δ u v x) (sub-Data-↑d،＋ Γ Δ u v x₁) refl
sub-↑،＋ Γ Δ u v (f Ｕ f₁) = cong₂ _Ｕ_ (sub-↑،＋ Γ Δ u v f) (sub-↑،＋ Γ Δ u v f₁)
sub-↑،＋ Γ Δ u v (Ｏ f) = cong Ｏ (sub-↑،＋ Γ Δ u v f)
sub-↑،＋ Γ Δ u v (f Ｓ f₁) = cong₂ _Ｓ_ (sub-↑،＋ Γ Δ u v f) (sub-↑،＋ Γ Δ u v f₁)
sub-↑،＋ Γ Δ u v (Ｙ f) = cong Ｙ (sub-↑،＋ Γ Δ u v f)
sub-↑،＋ Γ Δ u v (Ｂ f) = cong Ｂ (sub-↑،＋ Γ Δ u v f)
sub-↑،＋ Γ Δ u v (Ｆ f) = cong Ｆ_ (sub-↑،＋ Γ (Δ ، 𝕍ℝ) u v f)
sub-↑،＋ Γ Δ u v (t₁ ⟨ x ⟩ t₂) = cong₂ (_⟨ x ⟩_) (sub-Res-↑ᵣ،＋ Γ Δ u v t₁) (sub-Res-↑ᵣ،＋ Γ Δ u v t₂)

sub-↑₀ : (Γ : Ctxt) (u : 𝕍) (v : C⟦𝕍⟧ Γ u) (f : Form Γ)
       → sub (↑₀ f) (CSub،ₗ {Γ} {u} v) ≡ f
sub-↑₀ Γ u v f = sub-↑،＋ Γ ⟨⟩ u v f

↑ᵣ₁≡↑ᵣ₊₀ : {Γ : Ctxt} {u v : 𝕍} (r : Res Γ)
         → ↑ᵣ₁ {Γ} {u} {v} r ≡ ↑ᵣ (⊆،＋ {Γ} {⟨⟩ ، v} {u}) (↑ᵣ₀ {Γ} {v} r)
↑ᵣ₁≡↑ᵣ₊₀ {Γ} {u} {v} (var i) = refl
↑ᵣ₁≡↑ᵣ₊₀ {Γ} {u} {v} Res.𝟎 = refl
--↑ᵣ₁≡↑ᵣ₊₀ {Γ} {u} {v} (𝐬 r) = cong 𝐬 (↑ᵣ₁≡↑ᵣ₊₀ r)
↑ᵣ₁≡↑ᵣ₊₀ {Γ} {u} {v} (r ⋆ r₁) = cong₂ _⋆_ (↑ᵣ₁≡↑ᵣ₊₀ r) (↑ᵣ₁≡↑ᵣ₊₀ r₁)

sub-Res-↑ᵣ₁₀ : (Γ : Ctxt) (u w : 𝕍) (v : C⟦𝕍⟧ Γ u) (r : Res Γ)
             → sub-Res (↑ᵣ₁ {Γ} {u} {w} r) (CSub، w (CSub،ₗ {Γ} {u} v)) ≡ ↑ᵣ₀ {Γ} {w} r
sub-Res-↑ᵣ₁₀ Γ u w v r =
  trans (cong (λ z → sub-Res z (CSub، w (CSub،ₗ {Γ} {u} v))) (↑ᵣ₁≡↑ᵣ₊₀ {Γ} {u} {w} r))
        (sub-Res-↑ᵣ،＋ Γ (⟨⟩ ، w) u v (↑ᵣ₀ {Γ} {w} r))

↑ᵣ-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (r  : Res Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑ᵣ e r ≡ ↑ᵣ e₂ (↑ᵣ e₁ r)
↑ᵣ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (var i) cond = cong var (cond _ i)
↑ᵣ-trans {Γ} {Ψ} {Δ} e e₁ e₂ 𝟎 cond = refl
--↑ᵣ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (𝐬 r) cond = cong 𝐬 (↑ᵣ-trans e e₁ e₂ r cond)
↑ᵣ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (r ⋆ r₁) cond = cong₂ _⋆_ (↑ᵣ-trans e e₁ e₂ r cond) (↑ᵣ-trans e e₁ e₂ r₁ cond)

↑ₚ-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (p  : AtomProp Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑ₚ e p ≡ ↑ₚ e₂ (↑ₚ e₁ p)
↑ₚ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (atomPropV i) cond = cong atomPropV (cond _ i)
↑ₚ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (atomPropC x) cond = refl

↑ᵢ-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (a  : Agent Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑ᵢ e a ≡ ↑ᵢ e₂ (↑ᵢ e₁ a)
↑ᵢ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (agentV i) cond = cong agentV (cond _ i)
↑ᵢ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (agentC x) cond = refl

↑ᵢ-list-trans : {Γ Ψ Δ : Ctxt}
                (e  : Γ ⊆ Δ)
                (e₁ : Γ ⊆ Ψ)
                (e₂ : Ψ ⊆ Δ)
                (a  : List (Agent Γ))
              → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
              → Data.List.map (↑ᵢ e) a ≡ Data.List.map (↑ᵢ e₂) (Data.List.map (↑ᵢ e₁) a)
↑ᵢ-list-trans {Γ} {Ψ} {Δ} e e₁ e₂ [] cond = refl
↑ᵢ-list-trans {Γ} {Ψ} {Δ} e e₁ e₂ (x ∷ a) cond =
  cong₂ _∷_ (↑ᵢ-trans e e₁ e₂ x cond) (↑ᵢ-list-trans e e₁ e₂ a cond)

↑ₛ-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (a  : Agents Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑ₛ e a ≡ ↑ₛ e₂ (↑ₛ e₁ a)
↑ₛ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (agentsV i) cond = cong agentsV (cond _ i)
↑ₛ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (agentsL x) cond = cong agentsL (↑ᵢ-list-trans e e₁ e₂ x cond)
--↑ₛ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (agentsS x) cond = refl

↑d-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (a  : Data Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑d e a ≡ ↑d e₂ (↑d e₁ a)
↑d-trans {Γ} {Ψ} {Δ} e e₁ e₂ (dataV i) cond = cong dataV (cond _ i)
↑d-trans {Γ} {Ψ} {Δ} e e₁ e₂ (dataC x) cond = refl

↑ₜ-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (a  : Action Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑ₜ e a ≡ ↑ₜ e₂ (↑ₜ e₁ a)
↑ₜ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (ActSend p a A) cond =
  cong₃ ActSend
        (↑d-trans e e₁ e₂ p cond)
        (↑ᵢ-trans e e₁ e₂ a cond)
        (↑ₛ-trans e e₁ e₂ A cond)

↑ₑ-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (a  : Event Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑ₑ e a ≡ ↑ₑ e₂ (↑ₑ e₁ a)
↑ₑ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (EvtReceive p a b) cond =
  cong₃ EvtReceive (↑d-trans e e₁ e₂ p cond) (↑ᵢ-trans e e₁ e₂ a cond) (↑ᵢ-trans e e₁ e₂ b cond)
↑ₑ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (EvtInternal a d) cond =
  cong₂ EvtInternal (↑ᵢ-trans e e₁ e₂ a cond) (↑d-trans e e₁ e₂ d cond)

↑f-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (a  : Fault Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑f e a ≡ ↑f e₂ (↑f e₁ a)
↑f-trans {Γ} {Ψ} {Δ} e e₁ e₂ (FaultCorrect a b) cond =
  cong₂ FaultCorrect (↑ᵢ-trans e e₁ e₂ a cond) (↑ᵢ-trans e e₁ e₂ b cond)

↑ₐ-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (a  : Atom Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑ₐ e a ≡ ↑ₐ e₂ (↑ₐ e₁ a)
↑ₐ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (atProp x) cond = cong atProp (↑ₚ-trans e e₁ e₂ x cond)
↑ₐ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (atAction x) cond = cong atAction (↑ₜ-trans e e₁ e₂ x cond)
↑ₐ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (atEvent x) cond = cong atEvent (↑ₑ-trans e e₁ e₂ x cond)
↑ₐ-trans {Γ} {Ψ} {Δ} e e₁ e₂ (atCorrect x) cond = cong atCorrect (↑f-trans e e₁ e₂ x cond)

↑-trans : {Γ Ψ Δ : Ctxt}
          (e  : Γ ⊆ Δ)
          (e₁ : Γ ⊆ Ψ)
          (e₂ : Ψ ⊆ Δ)
          (f  : Form Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
        → ↑ e f ≡ ↑ e₂ (↑ e₁ f)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (𝕒 x) cond = cong 𝕒 (↑ₐ-trans e e₁ e₂ x cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ ⊤· cond = refl
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ ⊥· cond = refl
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (f ∧· f₁) cond = cong₂ _∧·_ (↑-trans e e₁ e₂ f cond) (↑-trans e e₁ e₂ f₁ cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (f ∨· f₁) cond = cong₂ _∨·_ (↑-trans e e₁ e₂ f cond) (↑-trans e e₁ e₂ f₁ cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (f →· f₁) cond = cong₂ _→·_ (↑-trans e e₁ e₂ f cond) (↑-trans e e₁ e₂ f₁ cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (¬· f) cond = cong ¬·_ (↑-trans e e₁ e₂ f cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (∀· u f) cond = cong (∀· u) (↑-trans (⊆، (𝕍𝕌 u) e) (⊆، (𝕍𝕌 u) e₁) (⊆، (𝕍𝕌 u) e₂) f cond′)
  where
  cond′ : (v : 𝕍) (i : ∈Ctxt v (Γ ، 𝕍𝕌 u)) → ⊆، (𝕍𝕌 u) e i ≡ ⊆، (𝕍𝕌 u) e₂ (⊆، (𝕍𝕌 u) e₁ i)
  cond′ .(𝕍𝕌 u) (∈Ctxt0 .Γ) = refl
  cond′ v (∈CtxtS .(𝕍𝕌 u) i) = cong (∈CtxtS (𝕍𝕌 u)) (cond v i)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (∃· u f) cond = cong (∃· u) (↑-trans (⊆، (𝕍𝕌 u) e) (⊆، (𝕍𝕌 u) e₁) (⊆، (𝕍𝕌 u) e₂) f cond′)
  where
  cond′ : (v : 𝕍) (i : ∈Ctxt v (Γ ، 𝕍𝕌 u)) → ⊆، (𝕍𝕌 u) e i ≡ ⊆، (𝕍𝕌 u) e₂ (⊆، (𝕍𝕌 u) e₁ i)
  cond′ .(𝕍𝕌 u) (∈Ctxt0 .Γ) = refl
  cond′ v (∈CtxtS .(𝕍𝕌 u) i) = cong (∈CtxtS (𝕍𝕌 u)) (cond v i)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (x ∈ₐ x₁) cond = cong₂ _∈ₐ_ (↑ᵢ-trans e e₁ e₂ x cond) (↑ₛ-trans e e₁ e₂ x₁ cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (∣ A ∣ₛ＝ n) cond = cong (∣_∣ₛ＝ n) (↑ₛ-trans e e₁ e₂ A cond)
--↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (x ∈ᵢ x₁) cond = cong₂ _∈ᵢ_ (↑d-trans e e₁ e₂ x cond) refl
--↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (⟨ x ، x₁ ⟩∈ᵣ x₂) cond = cong₃ ⟨_،_⟩∈ᵣ_ (↑d-trans e e₁ e₂ x cond) (↑d-trans e e₁ e₂ x₁ cond) refl
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (f Ｕ f₁) cond = cong₂ _Ｕ_ (↑-trans e e₁ e₂ f cond) (↑-trans e e₁ e₂ f₁ cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (Ｏ f) cond = cong Ｏ (↑-trans e e₁ e₂ f cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (f Ｓ f₁) cond = cong₂ _Ｓ_ (↑-trans e e₁ e₂ f cond) (↑-trans e e₁ e₂ f₁ cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (Ｙ f) cond = cong Ｙ (↑-trans e e₁ e₂ f cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (Ｂ f) cond = cong Ｂ (↑-trans e e₁ e₂ f cond)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (Ｆ f) cond = cong Ｆ_ (↑-trans (⊆، 𝕍ℝ e) (⊆، 𝕍ℝ e₁) (⊆، 𝕍ℝ e₂) f cond′)
  where
  cond′ : (v : 𝕍) (i : ∈Ctxt v (Γ ، 𝕍ℝ)) → ⊆، 𝕍ℝ e i ≡ ⊆، 𝕍ℝ e₂ (⊆، 𝕍ℝ e₁ i)
  cond′ .𝕍ℝ (∈Ctxt0 .Γ) = refl
  cond′ v (∈CtxtS .𝕍ℝ i) = cong (∈CtxtS 𝕍ℝ) (cond v i)
↑-trans {Γ} {Ψ} {Δ} e e₁ e₂ (t₁ ⟨ x ⟩ t₂) cond = cong₂ (_⟨ x ⟩_) (↑ᵣ-trans e e₁ e₂ t₁ cond) (↑ᵣ-trans e e₁ e₂ t₂ cond)

↑₁≡↑₊₀ : {Γ : Ctxt} {u v : 𝕍} (f : Form Γ)
       → ↑₁ {Γ} {u} {v} f ≡ ↑ (⊆،＋ {Γ} {⟨⟩ ، v} {u}) (↑₀ {Γ} {v} f)
↑₁≡↑₊₀ {Γ} {u} {v} f =
  ↑-trans (⊆₁ {Γ} {u} {v})
          (⊆₀ {Γ} {v})
          (⊆،＋ {Γ} {⟨⟩ ، v} {u})
          f
          (λ w i → refl)

sub-↑₁₀ : (Γ : Ctxt) (u w : 𝕍) (v : C⟦𝕍⟧ Γ u) (f : Form Γ)
        → sub (↑₁ {Γ} {u} {w} f) (CSub، w (CSub،ₗ {Γ} {u} v)) ≡ ↑₀ {Γ} {w} f
sub-↑₁₀ Γ u w v f =
  trans (cong (λ z → sub z (CSub، w (CSub،ₗ {Γ} {u} v))) (↑₁≡↑₊₀ {Γ} {u} {w} f))
        (sub-↑،＋ Γ (⟨⟩ ، w) u v (↑₀ {Γ} {w} f))

⊆₀،-⊆₀ : {Γ : Ctxt} {u v : 𝕍}
      → (x : 𝕍) (i : ∈Ctxt x Γ) → ⊆₁ i ≡ ⊆₀، {Γ} {u} {v} (⊆₀ i)
⊆₀،-⊆₀ {Γ} {u} {v} x i = refl

⊆₁،-⊆₁ : {Γ : Ctxt} {u v x y : 𝕍}
      → (z : 𝕍) (i : ∈Ctxt z Γ) → ⊆₃ i ≡ ⊆₁، {Γ ، u} {x} {y} {v} (⊆₁ {Γ} {u} {v} i)
⊆₁،-⊆₁ {Γ} {u} {v} {x} {y} z i = refl

↑ᵣ₀،-↑ᵣ₀ : {Γ : Ctxt} {u v : 𝕍} (t : Res Γ)
        → (↑ᵣ₀، {Γ} {u} {v} (↑ᵣ₀ t)) ≡ ↑ᵣ₁ {Γ} {u} {v} t
↑ᵣ₀،-↑ᵣ₀ {Γ} {u} {v} t =
  sym (↑ᵣ-trans ⊆₁ ⊆₀ ⊆₀، t ⊆₀،-⊆₀)

↑ᵣ₀،-↑ᵣ₁ : {Γ : Ctxt} {u v w : 𝕍} (t : Res Γ)
        → (↑ᵣ₀، {Γ ، u} {v} {w} (↑ᵣ₁ {Γ} {u} {w} t)) ≡ ↑ᵣ₂ {Γ} {u} {v} {w} t
↑ᵣ₀،-↑ᵣ₁ {Γ} {u} {v} {w} t =
  sym (↑ᵣ-trans ⊆₂ ⊆₁ ⊆₀، t (λ _ _ → refl))

↑₀،-↑₀ : {Γ : Ctxt} {u v : 𝕍} (f : Form Γ)
      → (↑₀، {Γ} {u} {v} (↑₀ f)) ≡ ↑₁ {Γ} {u} {v} f
↑₀،-↑₀ {Γ} {u} {v} f =
  sym (↑-trans ⊆₁ ⊆₀ ⊆₀، f ⊆₀،-⊆₀)

↑₁،-↑₁ : {Γ : Ctxt} {u v x y : 𝕍} (f : Form Γ)
      → (↑₁، {Γ ، u} {x} {y} {v} (↑₁ {Γ} {u} {v} f)) ≡ ↑₃ {Γ} {u} {x} {y} {v} f
↑₁،-↑₁ {Γ} {u} {v} {x} {y} f =
  sym (↑-trans ⊆₃ ⊆₁ ⊆₁، f ⊆₁،-⊆₁)

↑₁،-↑₀ : {Γ : Ctxt} {u v w : 𝕍} (f : Form Γ)
      → (↑₁، {Γ} {u} {v} {w} (↑₀ {Γ} {w} f)) ≡ ↑₂ {Γ} {u} {v} {w} f
↑₁،-↑₀ {Γ} {u} {v} {w} f =
  sym (↑-trans ⊆₂ ⊆₀ ⊆₁، f (λ _ _ → refl))

↑d₁،-↑d₀ : {Γ : Ctxt} {u v w : 𝕍} (d : Data Γ)
         → (↑d₁، {Γ} {u} {v} {w} (↑d₀ {Γ} {w} d)) ≡ ↑d₂ {Γ} {u} {v} {w} d
↑d₁،-↑d₀ {Γ} {u} {v} {w} d =
  sym (↑d-trans ⊆₂ ⊆₀ ⊆₁، d (λ _ _ → refl))

↑₀،-as-↑⊆،＋ : {Γ : Ctxt} {u v : 𝕍} (f : Form (Γ ، v))
           → ↑₀، {Γ} {u} {v} f ≡ ↑ (⊆،＋ {Γ} {⟨⟩ ، v} {u}) f
↑₀،-as-↑⊆،＋ {Γ} {u} {v} f = refl

↑₁≡↑₀↑₀ : {Γ : Ctxt} {u v : 𝕍} (f : Form Γ)
       → ↑₁ {Γ} {u} {v} f ≡ ↑₀ {Γ ، u} {v} (↑₀ {Γ} {u} f)
↑₁≡↑₀↑₀ {Γ} {u} {v} f =
  ↑-trans (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ} {u}) (⊆₀ {Γ ، u} {v}) f
          (λ w i → refl)

↑₃≡↑₀↑₂ : {Γ : Ctxt} {u v w x : 𝕍} (f : Form Γ)
       → ↑₃ {Γ} {u} {v} {w} {x} f ≡ ↑₀ {Γ ، u ، v ، w} {x} (↑₂ {Γ} {u} {v} {w} f)
↑₃≡↑₀↑₂ {Γ} {u} {v} {w} {x} f =
  ↑-trans (⊆₃ {Γ} {u} {v} {w} {x}) (⊆₂ {Γ} {u} {v} {w}) (⊆₀ {Γ ، u ، v ، w} {x}) f
          (λ w i → refl)

↑d₃≡↑d₀↑d₂ : {Γ : Ctxt} {u v w x : 𝕍} (d : Data Γ)
           → ↑d₃ {Γ} {u} {v} {w} {x} d ≡ ↑d₀ {Γ ، u ، v ، w} {x} (↑d₂ {Γ} {u} {v} {w} d)
↑d₃≡↑d₀↑d₂ {Γ} {u} {v} {w} {x} d =
  ↑d-trans (⊆₃ {Γ} {u} {v} {w} {x}) (⊆₂ {Γ} {u} {v} {w}) (⊆₀ {Γ ، u ، v ، w} {x}) d
           (λ w i → refl)

↑d₂≡↑d₀↑d₁ : {Γ : Ctxt} {u v w : 𝕍} (d : Data Γ)
           → ↑d₂ {Γ} {u} {v} {w} d ≡ ↑d₀ {Γ ، u ، v} {w} (↑d₁ {Γ} {u} {v} d)
↑d₂≡↑d₀↑d₁ {Γ} {u} {v} {w} d =
  ↑d-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ ، u ، v} {w}) d
           (λ w i → refl)

↑ᵢ₁≡↑ᵢ₀↑ᵢ₀ : {Γ : Ctxt} {u v : 𝕍} (a : Agent Γ)
           → ↑ᵢ₁ {Γ} {u} {v} a ≡ ↑ᵢ₀ {Γ ، u} {v} (↑ᵢ₀ {Γ} {u} a)
↑ᵢ₁≡↑ᵢ₀↑ᵢ₀ {Γ} {u} {v} a =
  ↑ᵢ-trans (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ} {u}) (⊆₀ {Γ ، u} {v}) a
           (λ w i → refl)

↑ᵢ₂≡↑ᵢ₁↑ᵢ₀ : {Γ : Ctxt} {u v w : 𝕍} (a : Agent Γ)
           → ↑ᵢ₂ {Γ} {u} {v} {w} a ≡ ↑ᵢ₁ {Γ ، u} {v} {w} (↑ᵢ₀ {Γ} {u} a)
↑ᵢ₂≡↑ᵢ₁↑ᵢ₀ {Γ} {u} {v} {w} a =
  ↑ᵢ-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₀ {Γ} {u}) (⊆₁ {Γ ، u} {v} {w}) a
           (λ w i → refl)

↑ᵢ₂≡↑ᵢ₀↑ᵢ₀↑ᵢ₀ : {Γ : Ctxt} {u v w : 𝕍} (a : Agent Γ)
              → ↑ᵢ₂ {Γ} {u} {v} {w} a ≡ ↑ᵢ₀ {Γ ، u ، v} {w} (↑ᵢ₀ {Γ ، u} {v} (↑ᵢ₀ {Γ} {u} a))
↑ᵢ₂≡↑ᵢ₀↑ᵢ₀↑ᵢ₀ {Γ} {u} {v} {w} a = trans (↑ᵢ₂≡↑ᵢ₁↑ᵢ₀ a) (↑ᵢ₁≡↑ᵢ₀↑ᵢ₀ (↑ᵢ₀ a))

↑ₚ₁≡↑ₚ₀↑ₚ₀ : {Γ : Ctxt} {u v : 𝕍} (a : AtomProp Γ)
           → ↑ₚ₁ {Γ} {u} {v} a ≡ ↑ₚ₀ {Γ ، u} {v} (↑ₚ₀ {Γ} {u} a)
↑ₚ₁≡↑ₚ₀↑ₚ₀ {Γ} {u} {v} a =
  ↑ₚ-trans (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ} {u}) (⊆₀ {Γ ، u} {v}) a
           (λ w i → refl)

↑ₚ₂≡↑ₚ₁↑ₚ₀ : {Γ : Ctxt} {u v w : 𝕍} (a : AtomProp Γ)
           → ↑ₚ₂ {Γ} {u} {v} {w} a ≡ ↑ₚ₁ {Γ ، u} {v} {w} (↑ₚ₀ {Γ} {u} a)
↑ₚ₂≡↑ₚ₁↑ₚ₀ {Γ} {u} {v} {w} a =
  ↑ₚ-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₀ {Γ} {u}) (⊆₁ {Γ ، u} {v} {w}) a
           (λ w i → refl)

↑ₚ₂≡↑ₚ₀↑ₚ₀↑ₚ₀ : {Γ : Ctxt} {u v w : 𝕍} (a : AtomProp Γ)
              → ↑ₚ₂ {Γ} {u} {v} {w} a ≡ ↑ₚ₀ {Γ ، u ، v} {w} (↑ₚ₀ {Γ ، u} {v} (↑ₚ₀ {Γ} {u} a))
↑ₚ₂≡↑ₚ₀↑ₚ₀↑ₚ₀ {Γ} {u} {v} {w} a = trans (↑ₚ₂≡↑ₚ₁↑ₚ₀ a) (↑ₚ₁≡↑ₚ₀↑ₚ₀ (↑ₚ₀ a))

↑d₁≡↑d₀↑d₀ : {Γ : Ctxt} {u v : 𝕍} (a : Data Γ)
           → ↑d₁ {Γ} {u} {v} a ≡ ↑d₀ {Γ ، u} {v} (↑d₀ {Γ} {u} a)
↑d₁≡↑d₀↑d₀ {Γ} {u} {v} a =
  ↑d-trans (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ} {u}) (⊆₀ {Γ ، u} {v}) a
           (λ w i → refl)

↑d₂≡↑d₁↑d₀ : {Γ : Ctxt} {u v w : 𝕍} (a : Data Γ)
           → ↑d₂ {Γ} {u} {v} {w} a ≡ ↑d₁ {Γ ، u} {v} {w} (↑d₀ {Γ} {u} a)
↑d₂≡↑d₁↑d₀ {Γ} {u} {v} {w} a =
  ↑d-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₀ {Γ} {u}) (⊆₁ {Γ ، u} {v} {w}) a
           (λ w i → refl)

↑d₂≡↑d₀↑d₀↑d₀ : {Γ : Ctxt} {u v w : 𝕍} (a : Data Γ)
              → ↑d₂ {Γ} {u} {v} {w} a ≡ ↑d₀ {Γ ، u ، v} {w} (↑d₀ {Γ ، u} {v} (↑d₀ {Γ} {u} a))
↑d₂≡↑d₀↑d₀↑d₀ {Γ} {u} {v} {w} a = trans (↑d₂≡↑d₁↑d₀ a) (↑d₁≡↑d₀↑d₀ (↑d₀ a))

↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ : {Γ : Ctxt} {u v : 𝕍} (r : Res Γ)
           → ↑ᵣ₁ {Γ} {u} {v} r ≡ ↑ᵣ₀ {Γ ، u} {v} (↑ᵣ₀ {Γ} {u} r)
↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ {Γ} {u} {v} r =
  ↑ᵣ-trans (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ} {u}) (⊆₀ {Γ ، u} {v}) r
           (λ w i → refl)

↑ᵣ₂≡↑ᵣ₁↑ᵣ₀ : {Γ : Ctxt} {u v w : 𝕍} (r : Res Γ)
           → ↑ᵣ₂ {Γ} {u} {v} {w} r ≡ ↑ᵣ₁ {Γ ، u} {v} {w} (↑ᵣ₀ {Γ} {u} r)
↑ᵣ₂≡↑ᵣ₁↑ᵣ₀ {Γ} {u} {v} {w} r =
  ↑ᵣ-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₀ {Γ} {u}) (⊆₁ {Γ ، u} {v} {w}) r
           (λ w i → refl)

↑ᵣ₂≡↑ᵣ₀،،↑ᵣ₁ : {Γ : Ctxt} {u v w : 𝕍} (r : Res Γ)
            → ↑ᵣ₂ {Γ} {u} {v} {w} r ≡ ↑ᵣ₀،، {Γ} {u} {v} {w} (↑ᵣ₁ {Γ} {v} {w} r)
↑ᵣ₂≡↑ᵣ₀،،↑ᵣ₁ {Γ} {u} {v} {w} r =
  ↑ᵣ-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₁ {Γ} {v} {w}) (⊆₀،، {Γ} {u} {v} {w}) r
           (λ w i → refl)

↑d₂≡↑d₀،،↑d₁ : {Γ : Ctxt} {u v w : 𝕍} (d : Data Γ)
            → ↑d₂ {Γ} {u} {v} {w} d ≡ ↑d₀،، {Γ} {u} {v} {w} (↑d₁ {Γ} {v} {w} d)
↑d₂≡↑d₀،،↑d₁ {Γ} {u} {v} {w} d =
  ↑d-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₁ {Γ} {v} {w}) (⊆₀،، {Γ} {u} {v} {w}) d
           (λ w i → refl)

↑₂≡↑₁↑₀ : {Γ : Ctxt} {u v w : 𝕍} (f : Form Γ)
        → ↑₂ {Γ} {u} {v} {w} f ≡ ↑₁ {Γ ، u} {v} {w} (↑₀ {Γ} {u} f)
↑₂≡↑₁↑₀ {Γ} {u} {v} {w} f =
  ↑-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₀ {Γ} {u}) (⊆₁ {Γ ، u} {v} {w}) f
          (λ w i → refl)

↑₂≡↑₀،،↑₁ : {Γ : Ctxt} {u v w : 𝕍} (f : Form Γ)
         → ↑₂ {Γ} {u} {v} {w} f ≡ ↑₀،، {Γ} {u} {v} {w} (↑₁ {Γ} {v} {w} f)
↑₂≡↑₀،،↑₁ {Γ} {u} {v} {w} f =
  ↑-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₁ {Γ} {v} {w}) (⊆₀،، {Γ} {u} {v} {w}) f
          (λ w i → refl)

↑₃≡↑₀،،،↑₂ : {Γ : Ctxt} {u v w x : 𝕍} (f : Form Γ)
         → ↑₃ {Γ} {u} {v} {w} {x} f ≡ ↑₀،،، {Γ} {u} {v} {w} {x} (↑₂ {Γ} {v} {w} {x} f)
↑₃≡↑₀،،،↑₂ {Γ} {u} {v} {w} {x} f =
  ↑-trans (⊆₃ {Γ} {u} {v} {w} {x}) (⊆₂ {Γ} {v} {w} {x}) (⊆₀،،، {Γ} {u} {v} {w} {x}) f
          (λ w i → refl)

↑d₃≡↑d₀،،،↑d₂ : {Γ : Ctxt} {u v w x : 𝕍} (d : Data Γ)
             → ↑d₃ {Γ} {u} {v} {w} {x} d ≡ ↑d₀،،، {Γ} {u} {v} {w} {x} (↑d₂ {Γ} {v} {w} {x} d)
↑d₃≡↑d₀،،،↑d₂ {Γ} {u} {v} {w} {x} d =
  ↑d-trans (⊆₃ {Γ} {u} {v} {w} {x}) (⊆₂ {Γ} {v} {w} {x}) (⊆₀،،، {Γ} {u} {v} {w} {x}) d
           (λ w i → refl)

↑d₃≡↑d₀،↑d₂ : {Γ : Ctxt} {u v w x : 𝕍} (d : Data Γ)
           → ↑d₃ {Γ} {u} {v} {w} {x} d ≡ ↑d₀، {Γ ، u ، v} {w} {x} (↑d₂ {Γ} {u} {v} {x} d)
↑d₃≡↑d₀،↑d₂ {Γ} {u} {v} {w} {x} d =
  ↑d-trans (⊆₃ {Γ} {u} {v} {w} {x}) (⊆₂ {Γ} {u} {v} {x}) (⊆₀، {Γ ، u ، v} {w} {x}) d
           (λ w i → refl)

↑d₂≡↑d₀،↑d₁ : {Γ : Ctxt} {u v w : 𝕍} (d : Data Γ)
           → ↑d₂ {Γ} {u} {v} {w} d ≡ ↑d₀، {Γ ، u} {v} {w} (↑d₁ {Γ} {u} {w} d)
↑d₂≡↑d₀،↑d₁ {Γ} {u} {v} {w} d =
  ↑d-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₁ {Γ} {u} {w}) (⊆₀، {Γ ، u} {v} {w}) d
           (λ w i → refl)

↑d₁≡↑d₀،↑d₀ : {Γ : Ctxt} {u v : 𝕍} (d : Data Γ)
           → ↑d₁ {Γ} {u} {v} d ≡ ↑d₀، {Γ} {u} {v} (↑d₀ {Γ} {v} d)
↑d₁≡↑d₀،↑d₀ {Γ} {u} {v} d =
  ↑d-trans (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ} {v}) (⊆₀، {Γ} {u} {v}) d
           (λ w i → refl)

sub-↑₁ : (Γ : Ctxt) (u w : 𝕍) (v : C⟦𝕍⟧ (Γ ، u) w) (f : Form Γ)
       → sub (↑₁ {Γ} {u} {w} f) (CSub،ₗ {Γ ، u} {w} v) ≡ ↑₀ {Γ} {u} f
sub-↑₁ Γ u w v f =
  trans (cong (λ z → sub z (CSub،ₗ {Γ ، u} {w} v)) (↑₁≡↑₀↑₀ f))
        (sub-↑،＋ (Γ ، u) ⟨⟩ w v (↑₀ {Γ} {u} f))

sub-↑₃ : (Γ : Ctxt) (u w x y : 𝕍) (v : C⟦𝕍⟧ (Γ ، u ، w ، x) y) (f : Form Γ)
       → sub (↑₃ {Γ} {u} {w} {x} {y} f) (CSub،ₗ {Γ ، u ، w ، x} {y} v) ≡ ↑₂ {Γ} {u} {w} {x} f
sub-↑₃ Γ u w x y v f =
  trans (cong (λ z → sub z (CSub،ₗ {Γ ، u ، w ، x} {y} v)) (↑₃≡↑₀↑₂ f))
        (sub-↑،＋ (Γ ، u ، w ، x) ⟨⟩ y v (↑₂ {Γ} {u} {w} {x} f))

sub-Data-↑d₃ : (Γ : Ctxt) (u w x y : 𝕍) (v : C⟦𝕍⟧ (Γ ، u ، w ، x) y) (d : Data Γ)
             → sub-Data (↑d₃ {Γ} {u} {w} {x} {y} d) (CSub،ₗ {Γ ، u ، w ، x} {y} v) ≡ ↑d₂ {Γ} {u} {w} {x} d
sub-Data-↑d₃ Γ u w x y v d =
  trans (cong (λ z → sub-Data z (CSub،ₗ {Γ ، u ، w ، x} {y} v)) (↑d₃≡↑d₀↑d₂ d))
        (sub-Data-↑d،＋ (Γ ، u ، w ، x) ⟨⟩ y v (↑d₂ {Γ} {u} {w} {x} d))

sub-Res-↑ᵣ₁ : (Γ : Ctxt) (u w : 𝕍) (v : C⟦𝕍⟧ (Γ ، u) w) (r : Res Γ)
            → sub-Res (↑ᵣ₁ {Γ} {u} {w} r) (CSub،ₗ {Γ ، u} {w} v) ≡ ↑ᵣ₀ {Γ} {u} r
sub-Res-↑ᵣ₁ Γ u w v r =
  trans (cong (λ z → sub-Res z (CSub،ₗ {Γ ، u} {w} v)) (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r))
        (sub-Res-↑ᵣ،＋ (Γ ، u) ⟨⟩ w v (↑ᵣ₀ {Γ} {u} r))

⊆-refl : {Γ : Ctxt} → Γ ⊆ Γ
⊆-refl {Γ} {u} i = i

⊆r : {Γ : Ctxt} → Γ ⊆ Γ
⊆r = ⊆-refl

⊆-trans : {Γ Δ Ψ : Ctxt}
       → Γ ⊆ Δ
       → Δ ⊆ Ψ
       → Γ ⊆ Ψ
⊆-trans {Γ} {Δ} {Ψ} a b {u} i = b (a i)

⊆-＋ : (Γ Δ : Ctxt)
     → Γ ⊆ (Γ ＋ Δ)
⊆-＋ Γ ⟨⟩ = ⊆-refl
⊆-＋ Γ (Δ ، U) = ⊆-trans (⊆-＋ Γ Δ) ⊆₀

↑Form-＋ : (Γ Δ : Ctxt)
         → Form Γ
         → Form (Γ ＋ Δ)
↑Form-＋ Γ Δ f = ↑ (⊆-＋ Γ Δ) f

↑ᵣ-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (r  : Res Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑ᵣ e r ≡ r
↑ᵣ-refl {Γ} e (var i) cond = cong var (cond _ i)
↑ᵣ-refl {Γ} e 𝟎 cond = refl
--↑ᵣ-refl {Γ} e (𝐬 r) cond = cong 𝐬 (↑ᵣ-refl e r cond)
↑ᵣ-refl {Γ} e (r ⋆ r₁) cond = cong₂ _⋆_ (↑ᵣ-refl e r cond) (↑ᵣ-refl e r₁ cond)

↑ᵢ-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (a  : Agent Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑ᵢ e a ≡ a
↑ᵢ-refl {Γ} e (agentV i) cond = cong agentV (cond _ i)
↑ᵢ-refl {Γ} e (agentC x) cond = refl

↑ᵢ-list-refl : {Γ : Ctxt}
               (e  : Γ ⊆ Γ)
               (a  : List (Agent Γ))
             → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
             → Data.List.map (↑ᵢ e) a ≡ a
↑ᵢ-list-refl {Γ} e [] cond = refl
↑ᵢ-list-refl {Γ} e (x ∷ a) cond = cong₂ _∷_ (↑ᵢ-refl e x cond) (↑ᵢ-list-refl e a cond)

↑ₛ-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (a  : Agents Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑ₛ e a ≡ a
↑ₛ-refl {Γ} e (agentsV i) cond = cong agentsV (cond _ i)
↑ₛ-refl {Γ} e (agentsL x) cond = cong agentsL (↑ᵢ-list-refl e x cond)
--↑ₛ-refl {Γ} e (agentsS x) cond = refl

↑d-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (d  : Data Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑d e d ≡ d
↑d-refl {Γ} e (dataV i) cond = cong dataV (cond _ i)
↑d-refl {Γ} e (dataC x) cond = refl

↑ₚ-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (p  : AtomProp Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑ₚ e p ≡ p
↑ₚ-refl {Γ} e (atomPropV i) cond = cong atomPropV (cond _ i)
↑ₚ-refl {Γ} e (atomPropC x) cond = refl

↑ₜ-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (a  : Action Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑ₜ e a ≡ a
↑ₜ-refl {Γ} e (ActSend p a A) cond = cong₃ ActSend (↑d-refl e p cond) (↑ᵢ-refl e a cond) (↑ₛ-refl e A cond)

↑ₑ-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (a  : Event Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑ₑ e a ≡ a
↑ₑ-refl {Γ} e (EvtReceive p a b) cond = cong₃ EvtReceive (↑d-refl e p cond) (↑ᵢ-refl e a cond) (↑ᵢ-refl e b cond)
↑ₑ-refl {Γ} e (EvtInternal a d) cond = cong₂ EvtInternal (↑ᵢ-refl e a cond) (↑d-refl e d cond)

↑f-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (a  : Fault Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑f e a ≡ a
↑f-refl {Γ} e (FaultCorrect a b) cond = cong₂ FaultCorrect (↑ᵢ-refl e a cond) (↑ᵢ-refl e b cond)

↑ₐ-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (a  : Atom Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑ₐ e a ≡ a
↑ₐ-refl {Γ} e (atProp x) cond = cong atProp (↑ₚ-refl e x cond)
↑ₐ-refl {Γ} e (atAction x) cond = cong atAction (↑ₜ-refl e x cond)
↑ₐ-refl {Γ} e (atEvent x) cond = cong atEvent (↑ₑ-refl e x cond)
↑ₐ-refl {Γ} e (atCorrect x) cond = cong atCorrect (↑f-refl e x cond)

↑-refl : {Γ : Ctxt}
         (e  : Γ ⊆ Γ)
         (f  : Form Γ)
       → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
       → ↑ e f ≡ f
↑-refl {Γ} e (𝕒 x) cond = cong 𝕒 (↑ₐ-refl e x cond)
↑-refl {Γ} e ⊤· cond = refl
↑-refl {Γ} e ⊥· cond = refl
↑-refl {Γ} e (f ∧· f₁) cond = cong₂ _∧·_ (↑-refl e f cond) (↑-refl e f₁ cond)
↑-refl {Γ} e (f ∨· f₁) cond = cong₂ _∨·_ (↑-refl e f cond) (↑-refl e f₁ cond)
↑-refl {Γ} e (f →· f₁) cond = cong₂ _→·_ (↑-refl e f cond) (↑-refl e f₁ cond)
↑-refl {Γ} e (¬· f) cond = cong ¬·_ (↑-refl e f cond)
↑-refl {Γ} e (∀· u f) cond = cong (∀· u) (↑-refl (⊆، (𝕍𝕌 u) e) f cond′)
  where
  cond′ : (v : 𝕍) (i : ∈Ctxt v (Γ ، 𝕍𝕌 u)) → ⊆، (𝕍𝕌 u) e i ≡ i
  cond′ .(𝕍𝕌 u) (∈Ctxt0 .Γ) = refl
  cond′ v (∈CtxtS .(𝕍𝕌 u) i) = cong (∈CtxtS (𝕍𝕌 u)) (cond _ i)
↑-refl {Γ} e (∃· u f) cond = cong (∃· u) (↑-refl (⊆، (𝕍𝕌 u) e) f cond′)
  where
  cond′ : (v : 𝕍) (i : ∈Ctxt v (Γ ، 𝕍𝕌 u)) → ⊆، (𝕍𝕌 u) e i ≡ i
  cond′ .(𝕍𝕌 u) (∈Ctxt0 .Γ) = refl
  cond′ v (∈CtxtS .(𝕍𝕌 u) i) = cong (∈CtxtS (𝕍𝕌 u)) (cond _ i)
↑-refl {Γ} e (x ∈ₐ x₁) cond = cong₂ _∈ₐ_ (↑ᵢ-refl e x cond) (↑ₛ-refl e x₁ cond)
↑-refl {Γ} e (∣ A ∣ₛ＝ n) cond = cong (∣_∣ₛ＝ n) (↑ₛ-refl e A cond)
--↑-refl {Γ} e (x ∈ᵢ x₁) cond = cong (_∈ᵢ x₁) (↑d-refl e x cond)
--↑-refl {Γ} e (⟨ x ، x₁ ⟩∈ᵣ x₂) cond = cong₂ (⟨_،_⟩∈ᵣ x₂) (↑d-refl e x cond) (↑d-refl e x₁ cond)
↑-refl {Γ} e (f Ｕ f₁) cond = cong₂ _Ｕ_ (↑-refl e f cond) (↑-refl e f₁ cond)
↑-refl {Γ} e (Ｏ f) cond = cong Ｏ (↑-refl e f cond)
↑-refl {Γ} e (f Ｓ f₁) cond = cong₂ _Ｓ_ (↑-refl e f cond) (↑-refl e f₁ cond)
↑-refl {Γ} e (Ｙ f) cond = cong Ｙ (↑-refl e f cond)
↑-refl {Γ} e (Ｂ f) cond = cong Ｂ (↑-refl e f cond)
↑-refl {Γ} e (Ｆ f) cond = cong Ｆ_ (↑-refl (⊆، 𝕍ℝ e) f cond′)
  where
  cond′ : (v : 𝕍) (i : ∈Ctxt v (Γ ، 𝕍ℝ)) → ⊆، 𝕍ℝ e i ≡ i
  cond′ .𝕍ℝ (∈Ctxt0 .Γ) = refl
  cond′ v (∈CtxtS .𝕍ℝ i) = cong (∈CtxtS 𝕍ℝ) (cond _ i)
↑-refl {Γ} e (t₁ ⟨ x ⟩ t₂) cond = cong₂ (_⟨ x ⟩_) (↑ᵣ-refl e t₁ cond) (↑ᵣ-refl e t₂ cond)

↑⊆-refl : {Γ : Ctxt}
          (f : Form Γ)
        → ↑ ⊆-refl f ≡ f
↑⊆-refl {Γ} f = ↑-refl ⊆-refl f (λ v i → refl)

↑ᵣ⊆-refl : {Γ : Ctxt}
           (r : Res Γ)
         → ↑ᵣ ⊆-refl r ≡ r
↑ᵣ⊆-refl {Γ} r = ↑ᵣ-refl ⊆-refl r (λ v i → refl)

-- Resource variable 0
𝕣₀ : {Γ : Ctxt} → Res (Γ ، 𝕍ℝ)
𝕣₀ {Γ} = var (∈Ctxt0 Γ)

-- Resource variable 1
𝕣₁ : {Γ : Ctxt} {v : 𝕍} → Res (Γ ، 𝕍ℝ ، v)
𝕣₁ {Γ} {v} = var (∈CtxtS v (∈Ctxt0 Γ))

-- Resource variable 2
𝕣₂ : {Γ : Ctxt} {v w : 𝕍} → Res (Γ ، 𝕍ℝ ، v ، w)
𝕣₂ {Γ} {v} {w} = var (∈CtxtS w (∈CtxtS v (∈Ctxt0 Γ)))

-- Resource variable 3
𝕣₃ : {Γ : Ctxt} {v w x : 𝕍} → Res (Γ ، 𝕍ℝ ، v ، w ، x)
𝕣₃ {Γ} {v} {w} {x} = var (∈CtxtS x (∈CtxtS w (∈CtxtS v (∈Ctxt0 Γ))))

-- Resource variable 4
𝕣₄ : {Γ : Ctxt} {v w x y : 𝕍} → Res (Γ ، 𝕍ℝ ، v ، w ، x ، y)
𝕣₄ {Γ} {v} {w} {x} {y} = var (∈CtxtS y (∈CtxtS x (∈CtxtS w (∈CtxtS v (∈Ctxt0 Γ)))))

-- Eventually ϕ holds "by" r
◇↓ : {Γ : Ctxt} → Res Γ → Form Γ → Form Γ
◇↓ {Γ} r ϕ = Ｆ (◇ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r ∧· ↑₁ ϕ)))

-- ϕ always holds between now and r
□↓ : {Γ : Ctxt} → Res Γ → Form Γ → Form Γ
□↓ {Γ} r ϕ = Ｆ (□ (Ｆ (𝕣₀ ⊑ 𝕣₁ ⋆ ↑ᵣ₁ r →· ↑₁ ϕ)))

-- f is true at some point before the current time + r
◇↓◆ : {Γ : Ctxt} → Res Γ → Form Γ → Form Γ
◇↓◆ {Γ} r f = ◇↓ r (◆ f)

-- f is always true before the current time + r
□↓■ : {Γ : Ctxt} → Res Γ → Form Γ → Form Γ
□↓■ {Γ} r f = □↓ r (■ f)

↑₀-◇↓ : {Γ : Ctxt} {v : 𝕍} (r : Res Γ) (A : Form Γ)
      → ↑₀ {Γ} {v} (◇↓ r A) ≡ ◇↓ (↑ᵣ₀ r) (↑₀ A)
↑₀-◇↓ {Γ} {v} r A =
  cong Ｆ_ (cong ◇ (cong Ｆ_ (cong₂ _∧·_ (cong₂ _⊑_ refl (cong₂ _⋆_ refl 𝕀)) 𝕀𝕀)))
  where
  𝕀 : ↑ᵣ₀،، (↑ᵣ₁ r) ≡ ↑ᵣ₁ (↑ᵣ₀ r)
  𝕀 = trans (sym (↑ᵣ₂≡↑ᵣ₀،،↑ᵣ₁ r)) (↑ᵣ₂≡↑ᵣ₁↑ᵣ₀ r)

  𝕀𝕀 : ↑₀،، (↑₁ A) ≡ ↑₁ (↑₀ A)
  𝕀𝕀 = trans (sym (↑₂≡↑₀،،↑₁ A)) (↑₂≡↑₁↑₀ A)

↑u-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          {u : 𝕌}
          (x : C⟦𝕌⟧ Γ u)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑u e {u} x ≡ x
↑u-refl {Γ} e {𝕌Agent}  x cond = ↑ᵢ-refl e x cond
↑u-refl {Γ} e {𝕌Agents} x cond = ↑ₛ-refl e x cond
↑u-refl {Γ} e {𝕌Prop}   x cond = ↑ₚ-refl e x cond
↑u-refl {Γ} e {𝕌Data}   x cond = ↑d-refl e x cond

↑v-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          {v : 𝕍}
          (x : C⟦𝕍⟧ Γ v)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑v e {v} x ≡ x
↑v-refl {Γ} e {𝕍𝕌 x₁} x cond = ↑u-refl e x cond
↑v-refl {Γ} e {𝕍ℝ} x cond = ↑ᵣ-refl e x cond

↑u-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           {u  : 𝕌}
           (x  : C⟦𝕌⟧ Γ u)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑u e {u} x ≡ ↑u e₂ {u} (↑u e₁ {u} x)
↑u-trans {Γ} {Ψ} {Δ} e e₁ e₂ {𝕌Agent}  x cond = ↑ᵢ-trans e e₁ e₂ x cond
↑u-trans {Γ} {Ψ} {Δ} e e₁ e₂ {𝕌Agents} x cond = ↑ₛ-trans e e₁ e₂ x cond
↑u-trans {Γ} {Ψ} {Δ} e e₁ e₂ {𝕌Prop}   x cond = ↑ₚ-trans e e₁ e₂ x cond
↑u-trans {Γ} {Ψ} {Δ} e e₁ e₂ {𝕌Data}   x cond = ↑d-trans e e₁ e₂ x cond

↑v-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           {v  : 𝕍}
           (x  : C⟦𝕍⟧ Γ v)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑v e {v} x ≡ ↑v e₂ {v} (↑v e₁ {v} x)
↑v-trans {Γ} {Ψ} {Δ} e e₁ e₂ {𝕍𝕌 x₁} x cond = ↑u-trans e e₁ e₂ {x₁} x cond
↑v-trans {Γ} {Ψ} {Δ} e e₁ e₂ {𝕍ℝ} x cond = ↑ᵣ-trans e e₁ e₂ x cond

CSub＋-⊆＋ : {Γ₁ Γ₂ Δ : Ctxt} (s : CSub Γ₁ Γ₂) {v : 𝕍} (i : ∈Ctxt v Γ₁)
           → CSub＋ {Γ₁} {Γ₂} {Δ} s (⊆＋ {Γ₁} {Δ} i)
           ≡ ↑v (⊆＋ {Γ₂} {Δ}) {v} (s i)
CSub＋-⊆＋ {Γ₁} {Γ₂} {⟨⟩} s {v} i = sym (↑v-refl {Γ₂} (λ i → i) {v} (s i) λ v i → refl)
CSub＋-⊆＋ {Γ₁} {Γ₂} {Δ ، U} s {v} i =
  trans (cong (↑v ⊆₀ {v}) (CSub＋-⊆＋ {Γ₁} {Γ₂} {Δ} s {v} i))
        (sym (↑v-trans (λ i → ∈CtxtS U (⊆＋ i)) ⊆＋ (∈CtxtS U) {v} (s i) (λ v i → refl)))

{--
CSub،-⊆، : {Γ Δ Ψ : Ctxt} (u v : 𝕍) (i : ∈Ctxt v (Γ ، u)) (e : Γ ⊆ Δ) (s : CSub Δ Ψ)
        → CSub، u s (⊆، u e i)
        ≡ CSub، u (λ x → s (e x)) i
CSub،-⊆، {Γ} {Δ} {Ψ} u i e s = {!!}
--}

CSub-var-⊆＋،⋆ : {Γ₁ Γ₂ Δ Ψ : Ctxt} {u : 𝕍}
              → CSub-var {(Γ₂ ＋ Δ) ＋ Ψ ، u} {u} (∈Ctxt0 ((Γ₂ ＋ Δ) ＋ Ψ))
              ≡ ↑v (⊆＋،⋆ {Γ₂} {Δ} {Ψ ، u}) {u} (CSub-var {Γ₂ ＋ Ψ ، u} {u} (∈Ctxt0 (Γ₂ ＋ Ψ)))
CSub-var-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ} {𝕍𝕌 𝕌Agent} = refl
CSub-var-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ} {𝕍𝕌 𝕌Agents} = refl
CSub-var-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ} {𝕍𝕌 𝕌Prop} = refl
CSub-var-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ} {𝕍𝕌 𝕌Data} = refl
CSub-var-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ} {𝕍ℝ} = refl

CSub＋-⊆＋،⋆ : {Γ₁ Γ₂ Δ Ψ : Ctxt} (s : CSub Γ₁ Γ₂) {v : 𝕍} (i : ∈Ctxt v (Γ₁ ＋ Ψ))
           → CSub＋ {Γ₁ ＋ Δ} {Γ₂ ＋ Δ} {Ψ} (CSub＋ {Γ₁} {Γ₂} {Δ} s) (⊆＋،⋆ {Γ₁} {Δ} {Ψ} i)
           ≡ ↑v (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) {v} (CSub＋ s i)
CSub＋-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {⟨⟩} s {v} i = CSub＋-⊆＋ s i
CSub＋-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ ، U} s {.U} (∈Ctxt0 .(Γ₁ ＋ Ψ)) = CSub-var-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ} {U}
CSub＋-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ ، U} s {v} (∈CtxtS .U i) =
  trans (cong (↑v ⊆₀ {v}) (CSub＋-⊆＋،⋆ {Γ₁} {Γ₂} {Δ} {Ψ} s {v} i))
        (trans (sym (↑v-trans (λ i → ∈CtxtS U (⊆＋،⋆ {Γ₂} {Δ} {Ψ} i)) (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) ⊆₀ {v} (CSub＋ s i) (λ v i → refl)))
               (↑v-trans (λ i → ∈CtxtS U (⊆＋،⋆ {Γ₂} {Δ} {Ψ} i)) ⊆₀ (⊆＋،⋆ {Γ₂} {Δ} {Ψ ، U}) {v} (CSub＋ s i) (λ v i → refl)))

sub-Res-↑ᵣ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (r : Res (Γ₁ ＋ Ψ))
             → sub-Res (↑ᵣ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) r) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
             ≡ ↑ᵣ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Res r (CSub＋ s))
sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s (var i) = CSub＋-⊆＋،⋆ s {𝕍World} i
sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s 𝟎 = refl
--sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s (𝐬 r) = cong 𝐬 (sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s r)
sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s (r ⋆ r₁) = cong₂ _⋆_ (sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s r) (sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s r₁)

sub-AtomProp-↑ₚ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (p : AtomProp (Γ₁ ＋ Ψ))
                  → sub-AtomProp (↑ₚ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) p) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
                  ≡ ↑ₚ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-AtomProp p (CSub＋ s))
sub-AtomProp-↑ₚ＋ Γ₁ Γ₂ Δ Ψ s (atomPropV i) = CSub＋-⊆＋،⋆ s {𝕍𝕌 𝕌Prop} i
sub-AtomProp-↑ₚ＋ Γ₁ Γ₂ Δ Ψ s (atomPropC x) = refl

sub-Agent-↑ₐ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (a : Agent (Γ₁ ＋ Ψ))
               → sub-Agent (↑ᵢ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) a) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
               ≡ ↑ᵢ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Agent a (CSub＋ s))
sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s (agentV i) = CSub＋-⊆＋،⋆ s {𝕍𝕌 𝕌Agent} i
sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s (agentC x) = refl

sub-AgentL-↑ₐ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (a : List (Agent (Γ₁ ＋ Ψ)))
                → Data.List.map (λ x → sub-Agent x (CSub＋ {_} {_} {Ψ} (CSub＋ s)))
                                (Data.List.map (↑ᵢ (⊆＋،⋆ {Γ₁} {Δ} {Ψ})) a)
                ≡ Data.List.map (↑ᵢ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}))
                                (Data.List.map (λ x → sub-Agent x (CSub＋ s)) a)
sub-AgentL-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s [] = refl
sub-AgentL-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s (x ∷ a) = cong₂ _∷_ (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s x) (sub-AgentL-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s a)

sub-Agents-↑ₛ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (a : Agents (Γ₁ ＋ Ψ))
               → sub-Agents (↑ₛ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) a) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
               ≡ ↑ₛ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Agents a (CSub＋ s))
sub-Agents-↑ₛ＋ Γ₁ Γ₂ Δ Ψ s (agentsV i) = CSub＋-⊆＋،⋆ s {𝕍𝕌 𝕌Agents} i
sub-Agents-↑ₛ＋ Γ₁ Γ₂ Δ Ψ s (agentsL x) = cong agentsL (sub-AgentL-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s x)
--sub-Agents-↑ₛ＋ Γ₁ Γ₂ Δ Ψ s (agentsS x) = refl

sub-Data-↑d＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (d : Data (Γ₁ ＋ Ψ))
              → sub-Data (↑d (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) d) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
              ≡ ↑d (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Data d (CSub＋ s))
sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s (dataV i) = CSub＋-⊆＋،⋆ s {𝕍𝕌 𝕌Data} i
sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s (dataC x) = refl

sub-Action-↑ₜ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (a : Action (Γ₁ ＋ Ψ))
                → sub-Action (↑ₜ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) a) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
                ≡ ↑ₜ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Action a (CSub＋ s))
sub-Action-↑ₜ＋ Γ₁ Γ₂ Δ Ψ s (ActSend p a A) =
  cong₃ ActSend (sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s p)
                (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s a)
                (sub-Agents-↑ₛ＋ Γ₁ Γ₂ Δ Ψ s A)

sub-Event-↑ₑ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (e : Event (Γ₁ ＋ Ψ))
               → sub-Event (↑ₑ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) e) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
               ≡ ↑ₑ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Event e (CSub＋ s))
sub-Event-↑ₑ＋ Γ₁ Γ₂ Δ Ψ s (EvtReceive p a b) =
  cong₃ EvtReceive (sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s p)
                   (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s a)
                   (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s b)
sub-Event-↑ₑ＋ Γ₁ Γ₂ Δ Ψ s (EvtInternal a d) =
  cong₂ EvtInternal (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s a)
                    (sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s d)

sub-Fault-↑f＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (c : Fault (Γ₁ ＋ Ψ))
               → sub-Fault (↑f (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) c) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
               ≡ ↑f (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Fault c (CSub＋ s))
sub-Fault-↑f＋ Γ₁ Γ₂ Δ Ψ s (FaultCorrect a b) =
  cong₂ FaultCorrect (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s a)
                     (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s b)

sub-Atom-↑ₐ＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (a : Atom (Γ₁ ＋ Ψ))
              → sub-Atom (↑ₐ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) a) (CSub＋ {_} {_} {Ψ} (CSub＋ s))
              ≡ ↑ₐ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub-Atom a (CSub＋ s))
sub-Atom-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s (atProp x) = cong atProp (sub-AtomProp-↑ₚ＋ Γ₁ Γ₂ Δ Ψ s x)
sub-Atom-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s (atAction x) = cong atAction (sub-Action-↑ₜ＋ Γ₁ Γ₂ Δ Ψ s x)
sub-Atom-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s (atEvent x) = cong atEvent (sub-Event-↑ₑ＋ Γ₁ Γ₂ Δ Ψ s x)
sub-Atom-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s (atCorrect x) = cong atCorrect (sub-Fault-↑f＋ Γ₁ Γ₂ Δ Ψ s x)

sub-↑＋ : (Γ₁ Γ₂ Δ Ψ : Ctxt) (s : CSub Γ₁ Γ₂) (f : Form (Γ₁ ＋ Ψ))
        → sub (↑ (⊆＋،⋆ {Γ₁} {Δ} {Ψ}) f) (CSub＋ {Γ₁ ＋ Δ} {Γ₂ ＋ Δ} {Ψ} (CSub＋ {Γ₁} {Γ₂} {Δ} s))
        ≡ ↑ (⊆＋،⋆ {Γ₂} {Δ} {Ψ}) (sub f (CSub＋ {Γ₁} {Γ₂} {Ψ} s))
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (𝕒 x) = cong 𝕒 (sub-Atom-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s x)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s ⊤· = refl
sub-↑＋ Γ₁ Γ₂ Δ Ψ s ⊥· = refl
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (f ∧· f₁) = cong₂ _∧·_ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f) (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f₁)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (f ∨· f₁) = cong₂ _∨·_ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f) (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f₁)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (f →· f₁) = cong₂ _→·_ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f) (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f₁)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (¬· f) = cong ¬·_ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (∀· u f) = cong (∀· u) (sub-↑＋ Γ₁ Γ₂ Δ (Ψ ، 𝕍𝕌 u) s f)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (∃· u f) = cong (∃· u) (sub-↑＋ Γ₁ Γ₂ Δ (Ψ ، 𝕍𝕌 u) s f)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (x ∈ₐ x₁) = cong₂ _∈ₐ_ (sub-Agent-↑ₐ＋ Γ₁ Γ₂ Δ Ψ s x) (sub-Agents-↑ₛ＋ Γ₁ Γ₂ Δ Ψ s x₁)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (∣ A ∣ₛ＝ n) = cong (∣_∣ₛ＝ n) (sub-Agents-↑ₛ＋ Γ₁ Γ₂ Δ Ψ s A)
--sub-↑＋ Γ₁ Γ₂ Δ Ψ s (x ∈ᵢ x₁) = cong (_∈ᵢ x₁) (sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s x)
--sub-↑＋ Γ₁ Γ₂ Δ Ψ s (⟨ x ، x₁ ⟩∈ᵣ x₂) = cong₂ (⟨_،_⟩∈ᵣ x₂) (sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s x) (sub-Data-↑d＋ Γ₁ Γ₂ Δ Ψ s x₁)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (f Ｕ f₁) = cong₂ _Ｕ_ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f) (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f₁)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (Ｏ f) = cong Ｏ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (f Ｓ f₁) = cong₂ _Ｓ_ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f) (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f₁)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (Ｙ f) = cong Ｙ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (Ｂ f) = cong Ｂ (sub-↑＋ Γ₁ Γ₂ Δ Ψ s f)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (Ｆ f) = cong Ｆ_ (sub-↑＋ Γ₁ Γ₂ Δ (Ψ ، 𝕍ℝ) s f)
sub-↑＋ Γ₁ Γ₂ Δ Ψ s (t₁ ⟨ x ⟩ t₂) = cong₂ (_⟨ x ⟩_) (sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s t₁) (sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ Ψ s t₂)

sub-↑＋₀ : (Γ₁ Γ₂ Δ : Ctxt) (s : CSub Γ₁ Γ₂) (f : Form Γ₁)
         → sub (↑ (⊆＋ {Γ₁} {Δ}) f) (CSub＋ {Γ₁} {Γ₂} {Δ} s)
         ≡ ↑ (⊆＋ {Γ₂} {Δ}) (sub f s)
sub-↑＋₀ Γ₁ Γ₂ Δ s f = sub-↑＋ Γ₁ Γ₂ Δ ⟨⟩ s f

sub-Res-↑ᵣ＋₀ : (Γ₁ Γ₂ Δ : Ctxt) (s : CSub Γ₁ Γ₂) (r : Res Γ₁)
             → sub-Res (↑ᵣ (⊆＋ {Γ₁} {Δ}) r) (CSub＋ {Γ₁} {Γ₂} {Δ} s)
             ≡ ↑ᵣ (⊆＋ {Γ₂} {Δ}) (sub-Res r s)
sub-Res-↑ᵣ＋₀ Γ₁ Γ₂ Δ s r = sub-Res-↑ᵣ＋ Γ₁ Γ₂ Δ ⟨⟩ s r

sub-↑₁₁ : {Γ Δ : Ctxt} (u w : 𝕍) (s : CSub Γ Δ) (f : Form Γ)
         → sub (↑₁ {Γ} {u} {w} f) (CSub، w (CSub، u s)) ≡ ↑₁ {Δ} {u} {w} (sub f s)
sub-↑₁₁ {Γ} {Δ} u w s f =
  sub-↑＋₀ Γ Δ (⟨⟩ ، u ، w) s f

sub-Res-↑ᵣ₁₁ : {Γ Δ : Ctxt} (u w : 𝕍) (s : CSub Γ Δ) (r : Res Γ)
             → sub-Res (↑ᵣ₁ {Γ} {u} {w} r) (CSub، w (CSub، u s)) ≡ ↑ᵣ₁ {Δ} {u} {w} (sub-Res r s)
sub-Res-↑ᵣ₁₁ {Γ} {Δ} u w s r =
  sub-Res-↑ᵣ＋₀ Γ Δ (⟨⟩ ، u ، w) s r

↑ᵣ₁-↑ᵣ₃≡↑ᵣ₀-↑ᵣ₄ : (Γ : Ctxt) (a b c d e f : 𝕍) (r : Res Γ)
                → ↑ᵣ₁ {_} {e} {f} (↑ᵣ₃ {Γ} {a} {b} {c} {d} r)
                ≡ ↑ᵣ₀ {_} {f} (↑ᵣ₄ {Γ} {a} {b} {c} {d} {e} r)
↑ᵣ₁-↑ᵣ₃≡↑ᵣ₀-↑ᵣ₄ Γ a b c d e f r =
  trans (sym (↑ᵣ-trans ⊆₅ ⊆₃ ⊆₁ r (λ v i → refl))) (↑ᵣ-trans ⊆₅ ⊆₄ ⊆₀ r (λ v i → refl))

↑ᵣ₁-↑ᵣ₃≡↑ᵣ₄-↑ᵣ₀ : (Γ : Ctxt) (a b c d e f : 𝕍) (r : Res Γ)
                → ↑ᵣ₁ {_} {e} {f} (↑ᵣ₃ {Γ} {a} {b} {c} {d} r)
                ≡ ↑ᵣ₄ {_} {b} {c} {d} {e} {f} (↑ᵣ₀ {Γ} {a} r)
↑ᵣ₁-↑ᵣ₃≡↑ᵣ₄-↑ᵣ₀ Γ a b c d e f r =
  trans (sym (↑ᵣ-trans ⊆₅ ⊆₃ ⊆₁ r (λ v i → refl))) (↑ᵣ-trans ⊆₅ ⊆₀ ⊆₄ r (λ v i → refl))

↑ᵣ₁-↑ᵣ₃≡↑⊆،＋ : (Γ : Ctxt) (a b c d e f : 𝕍) (r : Res Γ)
             → ↑ᵣ₁ {_} {e} {f} (↑ᵣ₃ {Γ} {a} {b} {c} {d} r)
             ≡ ↑ᵣ (⊆،＋ {Γ} {_} {a}) (↑ᵣ₄ {Γ} {b} {c} {d} {e} {f} r)
↑ᵣ₁-↑ᵣ₃≡↑⊆،＋ Γ a b c d e f r =
  trans (sym (↑ᵣ-trans ⊆₅ ⊆₃ ⊆₁ r (λ v i → refl)))
        (↑ᵣ-trans ⊆₅ ⊆₄ (⊆،＋ {Γ} {_} {a}) r (λ v i → refl))

↑ᵣ₁-↑ᵣ₂≡↑ᵣ₄ : (Γ : Ctxt) (a b c d e : 𝕍) (r : Res Γ)
            → ↑ᵣ₁ {_} {d} {e} (↑ᵣ₂ {Γ} {a} {b} {c} r)
            ≡ ↑ᵣ₄ {Γ} {a} {b} {c} {d} {e} r
↑ᵣ₁-↑ᵣ₂≡↑ᵣ₄ Γ a b c d e r =
  sym (↑ᵣ-trans ⊆₄ ⊆₂ ⊆₁ r (λ v i → refl))

↑ᵢ₂≡↑⊆،＋ : (Γ : Ctxt) (a b c : 𝕍) (i : Agent Γ)
          → ↑ᵢ₂ {Γ} {a} {b} {c} i
          ≡ ↑ᵢ (⊆،＋ {Γ} {_} {a}) (↑ᵢ₁ {Γ} {b} {c} i)
↑ᵢ₂≡↑⊆،＋ Γ a b c i =
  ↑ᵢ-trans ⊆₂ ⊆₁ (⊆،＋ {Γ} {_} {a}) i (λ v i → refl)

↑ᵢ₁≡↑⊆،＋ : (Γ : Ctxt) (a b : 𝕍) (i : Agent Γ)
          → ↑ᵢ₁ {Γ} {a} {b} i
          ≡ ↑ᵢ (⊆،＋ {Γ} {_} {a}) (↑ᵢ₀ {Γ} {b} i)
↑ᵢ₁≡↑⊆،＋ Γ a b i =
  ↑ᵢ-trans ⊆₁ ⊆₀ (⊆،＋ {Γ} {_} {a}) i (λ v i → refl)

↑ₛ₁≡↑⊆،＋ : (Γ : Ctxt) (a b : 𝕍) (i : Agents Γ)
          → ↑ₛ₁ {Γ} {a} {b} i
          ≡ ↑ₛ (⊆،＋ {Γ} {_} {a}) (↑ₛ₀ {Γ} {b} i)
↑ₛ₁≡↑⊆،＋ Γ a b i =
  ↑ₛ-trans ⊆₁ ⊆₀ (⊆،＋ {Γ} {_} {a}) i (λ v i → refl)

↑ₛ₁≡↑ₛ₀↑ₛ₀ : {Γ : Ctxt} {u v : 𝕍} (a : Agents Γ)
           → ↑ₛ₁ {Γ} {u} {v} a ≡ ↑ₛ₀ {Γ ، u} {v} (↑ₛ₀ {Γ} {u} a)
↑ₛ₁≡↑ₛ₀↑ₛ₀ {Γ} {u} {v} a =
  ↑ₛ-trans (⊆₁ {Γ} {u} {v}) (⊆₀ {Γ} {u}) (⊆₀ {Γ ، u} {v}) a
           (λ w i → refl)

↑ᵣ₁-↑ᵣ₁≡↑ᵣ₃ : (Γ : Ctxt) (a b c d : 𝕍) (r : Res Γ)
            → ↑ᵣ₁ {_} {c} {d} (↑ᵣ₁ {Γ} {a} {b} r)
            ≡ ↑ᵣ₃ {Γ} {a} {b} {c} {d} r
↑ᵣ₁-↑ᵣ₁≡↑ᵣ₃ Γ a b c d r =
  sym (↑ᵣ-trans ⊆₃ ⊆₁ ⊆₁ r (λ v i → refl))

↑ᵣ₁-↑ᵣ₀≡↑ᵣ₂ : (Γ : Ctxt) (a b c : 𝕍) (r : Res Γ)
            → ↑ᵣ₁ {_} {b} {c} (↑ᵣ₀ {Γ} {a} r)
            ≡ ↑ᵣ₂ {Γ} {a} {b} {c} r
↑ᵣ₁-↑ᵣ₀≡↑ᵣ₂ Γ a b c r =
  sym (↑ᵣ-trans ⊆₂ ⊆₀ ⊆₁ r (λ v i → refl))

↑ᵣ₁-↑ᵣ₂≡↑⊆،＋ : (Γ : Ctxt) (a b c d e : 𝕍) (r : Res Γ)
             → ↑ᵣ₁ {_} {d} {e} (↑ᵣ₂ {Γ} {a} {b} {c} r)
             ≡ ↑ᵣ (⊆،＋ {Γ} {_} {a}) (↑ᵣ₃ {Γ} {b} {c} {d} {e} r)
↑ᵣ₁-↑ᵣ₂≡↑⊆،＋ Γ a b c d e r =
  trans (sym (↑ᵣ-trans ⊆₄ ⊆₂ ⊆₁ r (λ v i → refl)))
        (↑ᵣ-trans ⊆₄ ⊆₃ (⊆،＋ {Γ} {_} {a}) r (λ v i → refl))

↑ᵣ₁-↑ᵣ₁≡↑⊆،＋ : (Γ : Ctxt) (a b c d : 𝕍) (r : Res Γ)
             → ↑ᵣ₁ {_} {c} {d} (↑ᵣ₁ {Γ} {a} {b} r)
             ≡ ↑ᵣ (⊆،＋ {Γ} {_} {a}) (↑ᵣ₂ {Γ} {b} {c} {d} r)
↑ᵣ₁-↑ᵣ₁≡↑⊆،＋ Γ a b c d r =
  trans (sym (↑ᵣ-trans ⊆₃ ⊆₁ ⊆₁ r (λ v i → refl)))
        (↑ᵣ-trans ⊆₃ ⊆₂ (⊆،＋ {Γ} {_} {a}) r (λ v i → refl))

↑ᵣ₁-↑ᵣ₀≡↑⊆،＋ : (Γ : Ctxt) (a b c : 𝕍) (r : Res Γ)
             → ↑ᵣ₁ {_} {b} {c} (↑ᵣ₀ {Γ} {a} r)
             ≡ ↑ᵣ (⊆،＋ {Γ} {_} {a}) (↑ᵣ₁ {Γ} {b} {c} r)
↑ᵣ₁-↑ᵣ₀≡↑⊆،＋ Γ a b c r =
  trans (sym (↑ᵣ-trans ⊆₂ ⊆₀ ⊆₁ r (λ v i → refl)))
        (↑ᵣ-trans ⊆₂ ⊆₁ (⊆،＋ {Γ} {_} {a}) r (λ v i → refl))

↑₁-↑₀≡↑⊆،＋ : (Γ : Ctxt) (a b c : 𝕍) (f : Form Γ)
           → ↑₁ {_} {b} {c} (↑₀ {Γ} {a} f)
           ≡ ↑ (⊆،＋ {Γ} {_} {a}) (↑₁ {Γ} {b} {c} f)
↑₁-↑₀≡↑⊆،＋ Γ a b c f =
  trans (sym (↑-trans ⊆₂ ⊆₀ ⊆₁ f (λ v i → refl)))
        (↑-trans ⊆₂ ⊆₁ (⊆،＋ {Γ} {_} {a}) f (λ v i → refl))

↑ᵢ₃≡↑ᵢ₁↑ᵢ₁ : {Γ : Ctxt} {u v w x : 𝕍} (a : Agent Γ)
           → ↑ᵢ₃ {Γ} {u} {v} {w} {x} a ≡ ↑ᵢ₁ {Γ ، u ، v} {w} {x} (↑ᵢ₁ {Γ} {u} {v} a)
↑ᵢ₃≡↑ᵢ₁↑ᵢ₁ {Γ} {u} {v} {w} {x} a =
  ↑ᵢ-trans (⊆₃ {Γ} {u} {v} {w} {x}) (⊆₁ {Γ} {u} {v}) (⊆₁ {Γ ، u ، v} {w} {x}) a
           (λ w i → refl)

↑ᵢ₁-↑ᵢ₂≡↑⊆،＋ : (Γ : Ctxt) (a b c d e : 𝕍) (i : Agent Γ)
             → ↑ᵢ₁ {_} {d} {e} (↑ᵢ₂ {Γ} {a} {b} {c} i)
             ≡ ↑ᵢ (⊆،＋ {Γ} {_} {a}) (↑ᵢ₃ {Γ} {b} {c} {d} {e} i)
↑ᵢ₁-↑ᵢ₂≡↑⊆،＋ Γ a b c d e i =
  trans (sym (↑ᵢ-trans ⊆₄ ⊆₂ ⊆₁ i (λ v i → refl)))
        (↑ᵢ-trans ⊆₄ ⊆₃ (⊆،＋ {Γ} {_} {a}) i (λ v i → refl))

↑ᵢ₁-↑ᵢ₁≡↑⊆،＋ : (Γ : Ctxt) (a b c d : 𝕍) (i : Agent Γ)
             → ↑ᵢ₁ {_} {c} {d} (↑ᵢ₁ {Γ} {a} {b} i)
             ≡ ↑ᵢ (⊆،＋ {Γ} {_} {a}) (↑ᵢ₂ {Γ} {b} {c} {d} i)
↑ᵢ₁-↑ᵢ₁≡↑⊆،＋ Γ a b c d i =
  trans (sym (↑ᵢ-trans ⊆₃ ⊆₁ ⊆₁ i (λ v i → refl)))
        (↑ᵢ-trans ⊆₃ ⊆₂ (⊆،＋ {Γ} {_} {a}) i (λ v i → refl))

↑ₚ₁-↑ₚ₀≡↑⊆،＋ : (Γ : Ctxt) (a b c : 𝕍) (p : AtomProp Γ)
             → ↑ₚ₁ {_} {b} {c} (↑ₚ₀ {Γ} {a} p)
             ≡ ↑ₚ (⊆،＋ {Γ} {_} {a}) (↑ₚ₁ {Γ} {b} {c} p)
↑ₚ₁-↑ₚ₀≡↑⊆،＋ Γ a b c p =
  trans (sym (↑ₚ-trans ⊆₂ ⊆₀ ⊆₁ p (λ v i → refl)))
        (↑ₚ-trans ⊆₂ ⊆₁ (⊆،＋ {Γ} {_} {a}) p (λ v i → refl))

↑d₁-↑d₀≡↑⊆،＋ : (Γ : Ctxt) (a b c : 𝕍) (p : Data Γ)
             → ↑d₁ {_} {b} {c} (↑d₀ {Γ} {a} p)
             ≡ ↑d (⊆،＋ {Γ} {_} {a}) (↑d₁ {Γ} {b} {c} p)
↑d₁-↑d₀≡↑⊆،＋ Γ a b c p =
  trans (sym (↑d-trans ⊆₂ ⊆₀ ⊆₁ p (λ v i → refl)))
        (↑d-trans ⊆₂ ⊆₁ (⊆،＋ {Γ} {_} {a}) p (λ v i → refl))

↑ᵢ₁-↑ᵢ₀≡↑⊆،＋ : (Γ : Ctxt) (a b c : 𝕍) (i : Agent Γ)
             → ↑ᵢ₁ {_} {b} {c} (↑ᵢ₀ {Γ} {a} i)
             ≡ ↑ᵢ (⊆،＋ {Γ} {_} {a}) (↑ᵢ₁ {Γ} {b} {c} i)
↑ᵢ₁-↑ᵢ₀≡↑⊆،＋ Γ a b c i =
  trans (sym (↑ᵢ-trans ⊆₂ ⊆₀ ⊆₁ i (λ v i → refl)))
        (↑ᵢ-trans ⊆₂ ⊆₁ (⊆،＋ {Γ} {_} {a}) i (λ v i → refl))

↑₁-↑₀≡↑₂ : (Γ : Ctxt) (a b c : 𝕍) (f : Form Γ)
         → ↑₁ {_} {b} {c} (↑₀ {Γ} {a} f)
         ≡ ↑₂ {Γ} {a} {b} {c} f
↑₁-↑₀≡↑₂ Γ a b c f =
  sym (↑-trans ⊆₂ ⊆₀ ⊆₁ f (λ v i → refl))

𝕦0 : {Γ : Ctxt} {u : 𝕌} → C⟦𝕌⟧ (Γ ، 𝕍𝕌 u) u
𝕦0 {Γ} {𝕌Agent}  = 𝕒0
𝕦0 {Γ} {𝕌Agents} = 𝔸0
𝕦0 {Γ} {𝕌Prop}   = 𝕡0
𝕦0 {Γ} {𝕌Data}   = 𝕕0

𝕧0 : {Γ : Ctxt} {u : 𝕍} → C⟦𝕍⟧ (Γ ، u) u
𝕧0 {Γ} {𝕍𝕌 x} = 𝕦0
𝕧0 {Γ} {𝕍ℝ} = 𝕣₀

↑v-CSub-var : {Γ Δ : Ctxt} (s : Γ ⊆ Δ) {v : 𝕍} (i : ∈Ctxt v Γ)
            → ↑v {Γ} {Δ} s {v} (CSub-var i) ≡ CSub-var (s i)
↑v-CSub-var {Γ} {Δ} s {𝕍𝕌 𝕌Agent} i = refl
↑v-CSub-var {Γ} {Δ} s {𝕍𝕌 𝕌Agents} i = refl
↑v-CSub-var {Γ} {Δ} s {𝕍𝕌 𝕌Prop} i = refl
↑v-CSub-var {Γ} {Δ} s {𝕍𝕌 𝕌Data} i = refl
↑v-CSub-var {Γ} {Δ} s {𝕍ℝ} i = refl

CSub＋-⊆،* : {Γ₁ Γ₂ Δ : Ctxt} {u : 𝕍} (s : CSub Γ₁ Γ₂) (i : ∈Ctxt u (Γ₂ ＋ Δ)) (e : Γ₂ ⊆ Γ₁)
          → ((i : ∈Ctxt u Γ₂) → s (e i) ≡ CSub-var i)
          → CSub＋ {Γ₁} {Γ₂} {Δ} s (⊆،* {Γ₂} {Γ₁} {Δ} e i)
          ≡ CSub-var i
CSub＋-⊆،* {Γ₁} {Γ₂} {⟨⟩} {u} s i e cond = cond i
CSub＋-⊆،* {Γ₁} {Γ₂} {Δ ، U} {u} s i e cond = c i
  where
  c : (i : ∈Ctxt u (Γ₂ ＋ (Δ ، U))) → CSub، U (CSub＋ {Γ₁} {Γ₂} {Δ} s) (⊆، U (⊆،* {Γ₂} {Γ₁} {Δ} e) i) ≡ CSub-var i
  c (∈Ctxt0 .(Γ₂ ＋ Δ)) = refl
  c (∈CtxtS .U i) =
    trans (cong (↑v {Γ₂ ＋ Δ} {Γ₂ ＋ (Δ ، U)} ⊆₀ {u}) (CSub＋-⊆،* {Γ₁} {Γ₂} {Δ} {u} s i e cond))
          (↑v-CSub-var {Γ₂ ＋ Δ} {Γ₂ ＋ (Δ ، U)} (∈CtxtS U) {u} i)

CSub＋-CSub،ₗ-𝕧0-⊆،*-⊆₀، : (Γ Δ : Ctxt) (u : 𝕍) {w : 𝕍} (i : ∈Ctxt w ((Γ ، u) ＋ Δ))
                        → CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})) (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u}) i)
                        ≡ CSub-var i
CSub＋-CSub،ₗ-𝕧0-⊆،*-⊆₀، Γ Δ u {w} i = CSub＋-⊆،* {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})) i (⊆₀، {_} {u} {u}) c
  where
  c : {w : 𝕍} (i₁ : ∈Ctxt w (Γ ، u)) → CSub،ₗ (𝕧0 {Γ} {u}) (⊆₀، i₁) ≡ CSub-var i₁
  c {𝕍𝕌 𝕌Agent} (∈Ctxt0 .Γ) = refl
  c {𝕍𝕌 𝕌Agents} (∈Ctxt0 .Γ) = refl
  c {𝕍𝕌 𝕌Prop} (∈Ctxt0 .Γ) = refl
  c {𝕍𝕌 𝕌Data} (∈Ctxt0 .Γ) = refl
  c {𝕍ℝ} (∈Ctxt0 .Γ) = refl
  c {w} (∈CtxtS .u j) = refl

sub-Res-var0 : (Γ Δ : Ctxt) (u : 𝕍) (r : Res ((Γ ، u) ＋ Δ))
             → sub-Res (↑ᵣ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) r) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
             ≡ r
sub-Res-var0 Γ Δ u (var i) = CSub＋-CSub،ₗ-𝕧0-⊆،*-⊆₀، Γ Δ u i
sub-Res-var0 Γ Δ u 𝟎 = refl
--sub-Res-var0 Γ Δ u (𝐬 r) = cong 𝐬 (sub-Res-var0 Γ Δ u r)
sub-Res-var0 Γ Δ u (r ⋆ r₁) = cong₂ _⋆_ (sub-Res-var0 Γ Δ u r) (sub-Res-var0 Γ Δ u r₁)

sub-AtomProp-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : AtomProp ((Γ ، u) ＋ Δ))
                  → sub-AtomProp (↑ₚ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
                  ≡ a
sub-AtomProp-var0 Γ Δ u (atomPropV i) = CSub＋-CSub،ₗ-𝕧0-⊆،*-⊆₀، Γ Δ u i
sub-AtomProp-var0 Γ Δ u (atomPropC x) = refl

sub-Agent-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : Agent ((Γ ، u) ＋ Δ))
               → sub-Agent (↑ᵢ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
               ≡ a
sub-Agent-var0 Γ Δ u (agentV i) = CSub＋-CSub،ₗ-𝕧0-⊆،*-⊆₀، Γ Δ u i
sub-Agent-var0 Γ Δ u (agentC x) = refl

sub-AgentList-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : List (Agent ((Γ ، u) ＋ Δ)))
                   → Data.List.map (λ x → sub-Agent x (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u}))))
                                   (Data.List.map (↑ᵢ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u}))) a)
                   ≡ a
sub-AgentList-var0 Γ Δ u [] = refl
sub-AgentList-var0 Γ Δ u (x ∷ a) = cong₂ _∷_ (sub-Agent-var0 Γ Δ u x) (sub-AgentList-var0 Γ Δ u a)

sub-Agents-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : Agents ((Γ ، u) ＋ Δ))
                → sub-Agents (↑ₛ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
                ≡ a
sub-Agents-var0 Γ Δ u (agentsV i) = CSub＋-CSub،ₗ-𝕧0-⊆،*-⊆₀، Γ Δ u i
sub-Agents-var0 Γ Δ u (agentsL x) = cong agentsL (sub-AgentList-var0 Γ Δ u x)
--sub-Agents-var0 Γ Δ u (agentsS x) = refl

sub-Data-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : Data ((Γ ، u) ＋ Δ))
              → sub-Data (↑d (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
              ≡ a
sub-Data-var0 Γ Δ u (dataV i) = CSub＋-CSub،ₗ-𝕧0-⊆،*-⊆₀، Γ Δ u i
sub-Data-var0 Γ Δ u (dataC x) = refl

sub-Action-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : Action ((Γ ، u) ＋ Δ))
                → sub-Action (↑ₜ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
                ≡ a
sub-Action-var0 Γ Δ u (ActSend p a A) =
  cong₃ ActSend (sub-Data-var0 Γ Δ u p) (sub-Agent-var0 Γ Δ u a) (sub-Agents-var0 Γ Δ u A)

sub-Event-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : Event ((Γ ، u) ＋ Δ))
                → sub-Event (↑ₑ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
                ≡ a
sub-Event-var0 Γ Δ u (EvtReceive p a b) =
  cong₃ EvtReceive (sub-Data-var0 Γ Δ u p) (sub-Agent-var0 Γ Δ u a) (sub-Agent-var0 Γ Δ u b)
sub-Event-var0 Γ Δ u (EvtInternal a d) =
  cong₂ EvtInternal (sub-Agent-var0 Γ Δ u a) (sub-Data-var0 Γ Δ u d)

sub-Fault-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : Fault ((Γ ، u) ＋ Δ))
               → sub-Fault (↑f (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
               ≡ a
sub-Fault-var0 Γ Δ u (FaultCorrect a b) = cong₂ FaultCorrect (sub-Agent-var0 Γ Δ u a) (sub-Agent-var0 Γ Δ u b)

sub-Atom-var0 : (Γ Δ : Ctxt) (u : 𝕍) (a : Atom ((Γ ، u) ＋ Δ))
              → sub-Atom (↑ₐ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) a) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
              ≡ a
sub-Atom-var0 Γ Δ u (atProp x) = cong atProp (sub-AtomProp-var0 Γ Δ u x)
sub-Atom-var0 Γ Δ u (atAction x) = cong atAction (sub-Action-var0 Γ Δ u x)
sub-Atom-var0 Γ Δ u (atEvent x) = cong atEvent (sub-Event-var0 Γ Δ u x)
sub-Atom-var0 Γ Δ u (atCorrect x) = cong atCorrect (sub-Fault-var0 Γ Δ u x)

sub-var0 : (Γ Δ : Ctxt) (u : 𝕍) (f : Form ((Γ ، u) ＋ Δ))
         → sub (↑ (⊆،* {Γ ، u} {Γ ، u ، u} {Δ} (⊆₀، {_} {u} {u})) f) (CSub＋ {Γ ، u ، u} {Γ ، u} {Δ} (CSub،ₗ (𝕧0 {Γ} {u})))
         ≡ f
sub-var0 Γ Δ u (𝕒 x) = cong 𝕒 (sub-Atom-var0 Γ Δ u x)
sub-var0 Γ Δ u ⊤· = refl
sub-var0 Γ Δ u ⊥· = refl
sub-var0 Γ Δ u (f ∧· f₁) = cong₂ _∧·_ (sub-var0 Γ Δ u f) (sub-var0 Γ Δ u f₁)
sub-var0 Γ Δ u (f ∨· f₁) = cong₂ _∨·_ (sub-var0 Γ Δ u f) (sub-var0 Γ Δ u f₁)
sub-var0 Γ Δ u (f →· f₁) = cong₂ _→·_ (sub-var0 Γ Δ u f) (sub-var0 Γ Δ u f₁)
sub-var0 Γ Δ u (¬· f) = cong ¬·_ (sub-var0 Γ Δ u f)
sub-var0 Γ Δ u (∀· u₁ f) = cong (λ x → ∀· u₁ x) (sub-var0 Γ (Δ ، 𝕍𝕌 u₁) u f)
sub-var0 Γ Δ u (∃· u₁ f) = cong (λ x → ∃· u₁ x) (sub-var0 Γ (Δ ، 𝕍𝕌 u₁) u f)
sub-var0 Γ Δ u (a ∈ₐ A) = cong₂ _∈ₐ_ (sub-Agent-var0 Γ Δ u a) (sub-Agents-var0 Γ Δ u A)
sub-var0 Γ Δ u (∣ A ∣ₛ＝ n) = cong (∣_∣ₛ＝ n) (sub-Agents-var0 Γ Δ u A)
--sub-var0 Γ Δ u (d ∈ᵢ p) = cong₂ _∈ᵢ_ (sub-Data-var0 Γ Δ u d) refl
--sub-var0 Γ Δ u (⟨ d ، e ⟩∈ᵣ r) = cong₃ ⟨_،_⟩∈ᵣ_ (sub-Data-var0 Γ Δ u d) (sub-Data-var0 Γ Δ u e) refl
sub-var0 Γ Δ u (f Ｕ f₁) = cong₂ _Ｕ_ (sub-var0 Γ Δ u f) (sub-var0 Γ Δ u f₁)
sub-var0 Γ Δ u (Ｏ f) = cong Ｏ (sub-var0 Γ Δ u f)
sub-var0 Γ Δ u (f Ｓ f₁) = cong₂ _Ｓ_ (sub-var0 Γ Δ u f) (sub-var0 Γ Δ u f₁)
sub-var0 Γ Δ u (Ｙ f) = cong Ｙ (sub-var0 Γ Δ u f)
sub-var0 Γ Δ u (Ｂ f) = cong Ｂ (sub-var0 Γ Δ u f)
sub-var0 Γ Δ u (Ｆ f) = cong Ｆ_ (sub-var0 Γ (Δ ، 𝕍ℝ) u f)
sub-var0 Γ Δ u (t₁ ⟨ x ⟩ t₂) = cong₂ (_⟨ x ⟩_) (sub-Res-var0 Γ Δ u t₁) (sub-Res-var0 Γ Δ u t₂)

sub-var0₀ : (Γ : Ctxt) (u : 𝕍) (f : Form (Γ ، u))
          → sub (↑₀، {_} {u} {u} f) (CSub،ₗ (𝕧0 {Γ} {u}))
          ≡ f
sub-var0₀ Γ u f = sub-var0 Γ ⟨⟩ u f

↑◇↓◆ : {Γ Δ : Ctxt}
       (e : Γ ⊆ Δ)
       (r : Res Γ)
       (A : Form Γ)
     → ↑ e (◇↓◆ r A) ≡ ◇↓◆ (↑ᵣ e r) (↑ e A)
↑◇↓◆ {Γ} {Δ} e r A =
  cong₂ (λ x y → Ｆ (◇ (Ｆ ((𝕣₀ ⊑ 𝕣₁ ⋆ x) ∧· ◆ y))))
        (trans (sym (↑ᵣ-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) ⊆₁ (⊆، _ (⊆، _ e)) r (λ _ _ → refl)))
               (↑ᵣ-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) e ⊆₁ r (λ _ _ → refl)))
        (trans (sym (↑-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) ⊆₁ (⊆، _ (⊆، _ e)) A (λ _ _ → refl)))
               (↑-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) e ⊆₁ A (λ _ _ → refl)))

↑◇↓ : {Γ Δ : Ctxt}
      (e : Γ ⊆ Δ)
      (r : Res Γ)
      (A : Form Γ)
    → ↑ e (◇↓ r A) ≡ ◇↓ (↑ᵣ e r) (↑ e A)
↑◇↓ {Γ} {Δ} e r A =
  cong₂ (λ x y → Ｆ (◇ (Ｆ ((𝕣₀ ⊑ 𝕣₁ ⋆ x) ∧· y))))
        (trans (sym (↑ᵣ-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) ⊆₁ (⊆، _ (⊆، _ e)) r (λ _ _ → refl)))
               (↑ᵣ-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) e ⊆₁ r (λ _ _ → refl)))
        (trans (sym (↑-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) ⊆₁ (⊆، _ (⊆، _ e)) A (λ _ _ → refl)))
               (↑-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) e ⊆₁ A (λ _ _ → refl)))

↑□↓ : {Γ Δ : Ctxt}
      (e : Γ ⊆ Δ)
      (r : Res Γ)
      (A : Form Γ)
    → ↑ e (□↓ r A) ≡ □↓ (↑ᵣ e r) (↑ e A)
↑□↓ {Γ} {Δ} e r A =
  cong₂ (λ x y → Ｆ (□ (Ｆ ((𝕣₀ ⊑ 𝕣₁ ⋆ x) →· y))))
        (trans (sym (↑ᵣ-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) ⊆₁ (⊆، _ (⊆، _ e)) r (λ _ _ → refl)))
               (↑ᵣ-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) e ⊆₁ r (λ _ _ → refl)))
        (trans (sym (↑-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) ⊆₁ (⊆، _ (⊆، _ e)) A (λ _ _ → refl)))
               (↑-trans (λ i → ∈CtxtS _ (∈CtxtS _ (e i))) e ⊆₁ A (λ _ _ → refl)))

sub-◇↓ : {Γ Δ : Ctxt}
         (s : CSub Γ Δ)
         (r : Res Γ)
         (A : Form Γ)
       → sub (◇↓ r A) s ≡ ◇↓ (sub-Res r s) (sub A s)
sub-◇↓ {Γ} {Δ} s r A =
  cong₂ (λ x y → Ｆ (◇ (Ｆ ((𝕣₀ ⊑ 𝕣₁ ⋆ x) ∧· y))))
        (sub-Res-↑ᵣ₁₁ 𝕍ℝ 𝕍ℝ s r)
        (sub-↑₁₁ 𝕍ℝ 𝕍ℝ s A)

sub-◇↓◆ : {Γ Δ : Ctxt}
          (s : CSub Γ Δ)
          (r : Res Γ)
          (A : Form Γ)
        → sub (◇↓◆ r A) s ≡ ◇↓◆ (sub-Res r s) (sub A s)
sub-◇↓◆ {Γ} {Δ} s r A =
  cong₂ (λ x y → Ｆ (◇ (Ｆ ((𝕣₀ ⊑ 𝕣₁ ⋆ x) ∧· ◆ y))))
        (sub-Res-↑ᵣ₁₁ 𝕍ℝ 𝕍ℝ s r)
        (sub-↑₁₁ 𝕍ℝ 𝕍ℝ s A)

↑ᵣ₀،↑ᵣ₀ : {Γ : Ctxt} {u v : 𝕍} (t : Res Γ)
       → (↑ᵣ₀، {Γ} {u} {v} (↑ᵣ₀ t)) ≡ ↑ᵣ₀ {Γ ، u} {v} (↑ᵣ₀ {Γ} {u} t)
↑ᵣ₀،↑ᵣ₀ {Γ} {u} {v} t = trans (↑ᵣ₀،-↑ᵣ₀ t) (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ t)

↑₀،↑₀ : {Γ : Ctxt} {u v : 𝕍} (A : Form Γ)
     → (↑₀، {Γ} {u} {v} (↑₀ A)) ≡ ↑₀ {Γ ، u} {v} (↑₀ {Γ} {u} A)
↑₀،↑₀ {Γ} {u} {v} A = trans (↑₀،-↑₀ A) (↑₁≡↑₀↑₀ A)

↑ᵣ₀،،-↑ᵣ₁ : {Γ : Ctxt} {u v w : 𝕍} (t : Res Γ)
        → (↑ᵣ₀،، {Γ} {u} {v} {w} (↑ᵣ₁ {_} {v} {w} t)) ≡ ↑ᵣ₂ {Γ} {u} {v} {w} t
↑ᵣ₀،،-↑ᵣ₁ {Γ} {u} {v} {w} t =
  sym (↑ᵣ-trans ⊆₂ ⊆₁ ⊆₀،، t (λ _ _ → refl))

↑d₀،،-↑d₁ : {Γ : Ctxt} {u v w : 𝕍} (d : Data Γ)
        → (↑d₀،، {Γ} {u} {v} {w} (↑d₁ {_} {v} {w} d)) ≡ ↑d₂ {Γ} {u} {v} {w} d
↑d₀،،-↑d₁ {Γ} {u} {v} {w} d =
  sym (↑d-trans ⊆₂ ⊆₁ ⊆₀،، d (λ _ _ → refl))

↑d₀،-↑d₁ : {Γ : Ctxt} {u v w : 𝕍} (d : Data Γ)
        → (↑d₀، {Γ ، u} {v} {w} (↑d₁ {_} {u} {w} d)) ≡ ↑d₂ {Γ} {u} {v} {w} d
↑d₀،-↑d₁ {Γ} {u} {v} {w} d =
  sym (↑d-trans ⊆₂ ⊆₁ ⊆₀، d (λ _ _ → refl))

↑₀-↑₁≡↑₂ : (Γ : Ctxt) (a b c : 𝕍) (f : Form Γ)
         → ↑₀ {_} {c} (↑₁ {Γ} {a} {b} f)
         ≡ ↑₂ {Γ} {a} {b} {c} f
↑₀-↑₁≡↑₂ Γ a b c f =
  sym (↑-trans ⊆₂ ⊆₁ ⊆₀ f (λ v i → refl))

↑₀↑₀،↑₀ : {Γ : Ctxt} {u v w : 𝕍} (A : Form Γ)
        → ↑₀ {_} {w} (↑₀، {Γ} {u} {v} (↑₀ {_} {v} A)) ≡ ↑₂ {Γ} {u} {v} {w} A
↑₀↑₀،↑₀ {Γ} {u} {v} A = trans (cong ↑₀ (↑₀،-↑₀ A)) (↑₀-↑₁≡↑₂ _ _ _ _ A)

↑₂≡↑₀،↑₁ : {Γ : Ctxt} {u v w : 𝕍} (f : Form Γ)
         → ↑₂ {Γ} {u} {v} {w} f ≡ ↑₀، {Γ ، u} {v} {w} (↑₁ {Γ} {u} {w} f)
↑₂≡↑₀،↑₁ {Γ} {u} {v} {w} f =
  ↑-trans (⊆₂ {Γ} {u} {v} {w}) (⊆₁ {Γ} {u} {w}) (⊆₀، {Γ ، u} {v} {w}) f
          (λ w i → refl)

↑d₂،-↑d₀ : {Γ : Ctxt} {u v x y : 𝕍} (d : Data Γ)
        → (↑d₂، {Γ} {u} {v} {x} {y} (↑d₀ {Γ} {y} d)) ≡ ↑d₃ {Γ} {u} {v} {x} {y} d
↑d₂،-↑d₀ {Γ} {u} {v} {x} {y} d =
  sym (↑d-trans ⊆₃ ⊆₀ ⊆₂، d (λ _ _ → refl))

↑₂،-↑₀ : {Γ : Ctxt} {u v x y : 𝕍} (f : Form Γ)
      → (↑₂، {Γ} {u} {v} {x} {y} (↑₀ {Γ} {y} f)) ≡ ↑₃ {Γ} {u} {v} {x} {y} f
↑₂،-↑₀ {Γ} {u} {v} {x} {y} f =
  sym (↑-trans ⊆₃ ⊆₀ ⊆₂، f (λ _ _ → refl))

\end{code}
