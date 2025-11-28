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

module Decidable(W : World)
       where

𝔻 : Set
𝔻 = ℕ

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)

open World.World W


-- Deciders

𝕍𝕌-inj : {u v : 𝕌} → 𝕍𝕌 u ≡ 𝕍𝕌 v → u ≡ v
𝕍𝕌-inj {u} {v} refl = refl

var-inj : {Γ : Ctxt} {i j : ∈Ctxt 𝕍ℝ Γ} → var i ≡ var j → i ≡ j
var-inj {Γ} {i} {j} refl = refl

𝕒-inj : {Γ : Ctxt} {i j : Atom Γ} → 𝕒 i ≡ 𝕒 j → i ≡ j
𝕒-inj {Γ} {i} {j} refl = refl

،-inj₁ : {Γ Δ : Ctxt} {u v : 𝕍} → Γ ، u ≡ Δ ، v → Γ ≡ Δ
،-inj₁ {Γ} {Δ} {u} {v} refl = refl

،-inj₂ : {Γ Δ : Ctxt} {u v : 𝕍} → Γ ، u ≡ Δ ، v → u ≡ v
،-inj₂ {Γ} {Δ} {u} {v} refl = refl

∧-inj₁ : {Γ : Ctxt} {a b c d : Form Γ} → a ∧· b ≡ c ∧· d → a ≡ c
∧-inj₁ {Γ} {a} {b} {c} {d} refl = refl

∧-inj₂ : {Γ : Ctxt} {a b c d : Form Γ} → a ∧· b ≡ c ∧· d → b ≡ d
∧-inj₂ {Γ} {a} {b} {c} {d} refl = refl

∨-inj₁ : {Γ : Ctxt} {a b c d : Form Γ} → a ∨· b ≡ c ∨· d → a ≡ c
∨-inj₁ {Γ} {a} {b} {c} {d} refl = refl

∨-inj₂ : {Γ : Ctxt} {a b c d : Form Γ} → a ∨· b ≡ c ∨· d → b ≡ d
∨-inj₂ {Γ} {a} {b} {c} {d} refl = refl

→-inj₁ : {Γ : Ctxt} {a b c d : Form Γ} → a →· b ≡ c →· d → a ≡ c
→-inj₁ {Γ} {a} {b} {c} {d} refl = refl

→-inj₂ : {Γ : Ctxt} {a b c d : Form Γ} → a →· b ≡ c →· d → b ≡ d
→-inj₂ {Γ} {a} {b} {c} {d} refl = refl

∀-inj₁ : {Γ : Ctxt} {a b : 𝕌} {c : Form (Γ ، 𝕍𝕌 a)} {d : Form (Γ ، 𝕍𝕌 b)} → ∀· a c ≡ ∀· b d → a ≡ b
∀-inj₁ {Γ} {a} {b} {c} {d} refl = refl

∀-inj₂ : {Γ : Ctxt} {a : 𝕌} {c : Form (Γ ، 𝕍𝕌 a)} {d : Form (Γ ، 𝕍𝕌 a)} → ∀· a c ≡ ∀· a d → c ≡ d
∀-inj₂ {Γ} {a} {c} {d} refl = refl

∈ₐ-inj₁ : {Γ : Ctxt} {a b : Agent Γ} {c d : Agents Γ} → a ∈ₐ c ≡ b ∈ₐ d → a ≡ b
∈ₐ-inj₁ {Γ} {a} {b} {c} {d} refl = refl

∈ₐ-inj₂ : {Γ : Ctxt} {a b : Agent Γ} {c d : Agents Γ} → a ∈ₐ c ≡ b ∈ₐ d → c ≡ d
∈ₐ-inj₂ {Γ} {a} {b} {c} {d} refl = refl

∣∣ₛ-inj₁ : {Γ : Ctxt} {a b : Agents Γ} {c d : ℕ} → ∣ a ∣ₛ＝ c ≡ ∣ b ∣ₛ＝ d → a ≡ b
∣∣ₛ-inj₁ {Γ} {a} {b} {c} {d} refl = refl

∣∣ₛ-inj₂ : {Γ : Ctxt} {a b : Agents Γ} {c d : ℕ} → ∣ a ∣ₛ＝ c ≡ ∣ b ∣ₛ＝ d → c ≡ d
∣∣ₛ-inj₂ {Γ} {a} {b} {c} {d} refl = refl

∃-inj₁ : {Γ : Ctxt} {a b : 𝕌} {c : Form (Γ ، 𝕍𝕌 a)} {d : Form (Γ ، 𝕍𝕌 b)} → ∃· a c ≡ ∃· b d → a ≡ b
∃-inj₁ {Γ} {a} {b} {c} {d} refl = refl

∃-inj₂ : {Γ : Ctxt} {a : 𝕌} {c : Form (Γ ، 𝕍𝕌 a)} {d : Form (Γ ، 𝕍𝕌 a)} → ∃· a c ≡ ∃· a d → c ≡ d
∃-inj₂ {Γ} {a} {c} {d} refl = refl

Ｕ-inj₁ : {Γ : Ctxt} {a b c d : Form Γ} → a Ｕ b ≡ c Ｕ d → a ≡ c
Ｕ-inj₁ {Γ} {a} {b} {c} {d} refl = refl

Ｕ-inj₂ : {Γ : Ctxt} {a b c d : Form Γ} → a Ｕ b ≡ c Ｕ d → b ≡ d
Ｕ-inj₂ {Γ} {a} {b} {c} {d} refl = refl

Ｓ-inj₁ : {Γ : Ctxt} {a b c d : Form Γ} → a Ｓ b ≡ c Ｓ d → a ≡ c
Ｓ-inj₁ {Γ} {a} {b} {c} {d} refl = refl

Ｓ-inj₂ : {Γ : Ctxt} {a b c d : Form Γ} → a Ｓ b ≡ c Ｓ d → b ≡ d
Ｓ-inj₂ {Γ} {a} {b} {c} {d} refl = refl

Ｏ-inj : {Γ : Ctxt} {a b : Form Γ} → Ｏ a ≡ Ｏ b → a ≡ b
Ｏ-inj {Γ} {a} {b} refl = refl

Ｙ-inj : {Γ : Ctxt} {a b : Form Γ} → Ｙ a ≡ Ｙ b → a ≡ b
Ｙ-inj {Γ} {a} {b} refl = refl

Ｂ-inj : {Γ : Ctxt} {a b : Form Γ} → Ｂ a ≡ Ｂ b → a ≡ b
Ｂ-inj {Γ} {a} {b} refl = refl

Ｆ-inj : {Γ : Ctxt} {a b : Form (Γ ، 𝕍ℝ)} → Ｆ a ≡ Ｆ b → a ≡ b
Ｆ-inj {Γ} {a} {b} refl = refl

¬-inj : {Γ : Ctxt} {a b : Form Γ} → ¬· a ≡ ¬· b → a ≡ b
¬-inj {Γ} {a} {b} refl = refl

⋆-inj₁ : {Γ : Ctxt} {a b c d : Res Γ} → a ⋆ b ≡ c ⋆ d → a ≡ c
⋆-inj₁ {Γ} {a} {b} {c} {d} refl = refl

⋆-inj₂ : {Γ : Ctxt} {a b c d : Res Γ} → a ⋆ b ≡ c ⋆ d → b ≡ d
⋆-inj₂ {Γ} {a} {b} {c} {d} refl = refl

comp-inj₁ : {Γ : Ctxt} {r₁ r₂ s₁ s₂ : Res Γ} {c₁ c₂ : Comparison} → r₁ ⟨ c₁ ⟩ s₁ ≡ r₂ ⟨ c₂ ⟩ s₂ → r₁ ≡ r₂
comp-inj₁ {Γ} {r₁} {r₂} {s₁} {s₂} {c₁} {c₂} refl = refl

comp-inj₂ : {Γ : Ctxt} {r₁ r₂ s₁ s₂ : Res Γ} {c₁ c₂ : Comparison} → r₁ ⟨ c₁ ⟩ s₁ ≡ r₂ ⟨ c₂ ⟩ s₂ → c₁ ≡ c₂
comp-inj₂ {Γ} {r₁} {r₂} {s₁} {s₂} {c₁} {c₂} refl = refl

comp-inj₃ : {Γ : Ctxt} {r₁ r₂ s₁ s₂ : Res Γ} {c₁ c₂ : Comparison} → r₁ ⟨ c₁ ⟩ s₁ ≡ r₂ ⟨ c₂ ⟩ s₂ → s₁ ≡ s₂
comp-inj₃ {Γ} {r₁} {r₂} {s₁} {s₂} {c₁} {c₂} refl = refl

∈CtxtS-inj : {Γ : Ctxt} {u v : 𝕍} {i j : ∈Ctxt v Γ}
           → ∈CtxtS u i ≡ ∈CtxtS u j
           → i ≡ j
∈CtxtS-inj {Γ} {u} {v} {i} {j} refl = refl

atProp-inj : {Γ : Ctxt} {a b : AtomProp Γ} → atProp a ≡ atProp b → a ≡ b
atProp-inj {Γ} {a} {b} refl = refl

atomPropV-inj : {Γ : Ctxt} {a b : ∈Ctxt 𝕍Prop Γ} → atomPropV a ≡ atomPropV b → a ≡ b
atomPropV-inj {Γ} {a} {b} refl = refl

dataV-inj : {Γ : Ctxt} {a b : ∈Ctxt 𝕍Data Γ} → dataV a ≡ dataV b → a ≡ b
dataV-inj {Γ} {a} {b} refl = refl

agentV-inj : {Γ : Ctxt} {a b : ∈Ctxt 𝕍Agent Γ} → agentV a ≡ agentV b → a ≡ b
agentV-inj {Γ} {a} {b} refl = refl

agentsV-inj : {Γ : Ctxt} {a b : ∈Ctxt 𝕍Agents Γ} → agentsV a ≡ agentsV b → a ≡ b
agentsV-inj {Γ} {a} {b} refl = refl

agentsL-inj : {Γ : Ctxt} {a b : List (Agent Γ)} → agentsL a ≡ agentsL b → a ≡ b
agentsL-inj {Γ} {a} {b} refl = refl

--agentsS-inj : {Γ : Ctxt} {a b : agents} → agentsS {Γ} a ≡ agentsS b → a ≡ b
--agentsS-inj {Γ} {a} {b} refl = refl

atomPropC-inj : {Γ : Ctxt} {a b : atomProp} → atomPropC {Γ} a ≡ atomPropC b → a ≡ b
atomPropC-inj {Γ} {a} {b} refl = refl

agentC-inj : {Γ : Ctxt} {a b : agent} → agentC {Γ} a ≡ agentC b → a ≡ b
agentC-inj {Γ} {a} {b} refl = refl

dataC-inj : {Γ : Ctxt} {a b : 𝔻} → dataC {Γ} a ≡ dataC b → a ≡ b
dataC-inj {Γ} {a} {b} refl = refl

atAction-inj : {Γ : Ctxt} {a b : Action Γ} → atAction a ≡ atAction b → a ≡ b
atAction-inj {Γ} {a} {b} refl = refl

atEvent-inj : {Γ : Ctxt} {a b : Event Γ} → atEvent a ≡ atEvent b → a ≡ b
atEvent-inj {Γ} {a} {b} refl = refl

atCorrect-inj : {Γ : Ctxt} {a b : Fault Γ} → atCorrect a ≡ atCorrect b → a ≡ b
atCorrect-inj {Γ} {a} {b} refl = refl

ActSend-inj₁ : {Γ : Ctxt} {a b : Data Γ} {c d : Agent Γ} {e f : Agents Γ} → ActSend a c e ≡ ActSend b d f → a ≡ b
ActSend-inj₁ {Γ} {a} {b} {c} {d} {e} {f} refl = refl

ActSend-inj₂ : {Γ : Ctxt} {a b : Data Γ} {c d : Agent Γ} {e f : Agents Γ} → ActSend a c e ≡ ActSend b d f → c ≡ d
ActSend-inj₂ {Γ} {a} {b} {c} {d} {e} {f} refl = refl

ActSend-inj₃ : {Γ : Ctxt} {a b : Data Γ} {c d : Agent Γ} {e f : Agents Γ} → ActSend a c e ≡ ActSend b d f → e ≡ f
ActSend-inj₃ {Γ} {a} {b} {c} {d} {e} {f} refl = refl

EvtReceive-inj₁ : {Γ : Ctxt} {a b : Data Γ} {c d e f : Agent Γ} → EvtReceive a c e ≡ EvtReceive b d f → a ≡ b
EvtReceive-inj₁ {Γ} {a} {b} {c} {d} {e} {f} refl = refl

EvtReceive-inj₂ : {Γ : Ctxt} {a b : Data Γ} {c d e f : Agent Γ} → EvtReceive a c e ≡ EvtReceive b d f → c ≡ d
EvtReceive-inj₂ {Γ} {a} {b} {c} {d} {e} {f} refl = refl

EvtReceive-inj₃ : {Γ : Ctxt} {a b : Data Γ} {c d e f : Agent Γ} → EvtReceive a c e ≡ EvtReceive b d f → e ≡ f
EvtReceive-inj₃ {Γ} {a} {b} {c} {d} {e} {f} refl = refl

EvtInternal-inj₁ : {Γ : Ctxt} {a b : Agent Γ} {c d : Data Γ} → EvtInternal a c ≡ EvtInternal b d → a ≡ b
EvtInternal-inj₁ {Γ} {a} {b} {c} {d} refl = refl

EvtInternal-inj₂ : {Γ : Ctxt} {a b : Agent Γ} {c d : Data Γ} → EvtInternal a c ≡ EvtInternal b d → c ≡ d
EvtInternal-inj₂ {Γ} {a} {b} {c} {d} refl = refl

FaultCorrect-inj₁ : {Γ : Ctxt} {a b c d : Agent Γ} → FaultCorrect a c ≡ FaultCorrect b d → a ≡ b
FaultCorrect-inj₁ {Γ} {a} {b} {c} {d} refl = refl

FaultCorrect-inj₂ : {Γ : Ctxt} {a b c d : Agent Γ} → FaultCorrect a c ≡ FaultCorrect b d → c ≡ d
FaultCorrect-inj₂ {Γ} {a} {b} {c} {d} refl = refl

Comparison-dec : decidable Comparison
Comparison-dec LE LE = inj₁ refl
Comparison-dec LE LT = inj₂ (λ ())
Comparison-dec LE EQ = inj₂ (λ ())
Comparison-dec LE PR = inj₂ (λ ())
Comparison-dec LT LE = inj₂ (λ ())
Comparison-dec LT LT = inj₁ refl
Comparison-dec LT EQ = inj₂ (λ ())
Comparison-dec LT PR = inj₂ (λ ())
Comparison-dec EQ LE = inj₂ (λ ())
Comparison-dec EQ LT = inj₂ (λ ())
Comparison-dec EQ EQ = inj₁ refl
Comparison-dec EQ PR = inj₂ (λ ())
Comparison-dec PR LE = inj₂ (λ ())
Comparison-dec PR LT = inj₂ (λ ())
Comparison-dec PR EQ = inj₂ (λ ())
Comparison-dec PR PR = inj₁ refl

𝕌-dec : decidable 𝕌
𝕌-dec 𝕌Agent  𝕌Agent  = inj₁ refl
𝕌-dec 𝕌Agent  𝕌Agents = inj₂ (λ ())
𝕌-dec 𝕌Agent  𝕌Prop   = inj₂ (λ ())
𝕌-dec 𝕌Agent  𝕌Data   = inj₂ (λ ())
𝕌-dec 𝕌Agents 𝕌Agent  = inj₂ (λ ())
𝕌-dec 𝕌Agents 𝕌Agents = inj₁ refl
𝕌-dec 𝕌Agents 𝕌Prop   = inj₂ (λ ())
𝕌-dec 𝕌Agents 𝕌Data   = inj₂ (λ ())
𝕌-dec 𝕌Prop   𝕌Agent  = inj₂ (λ ())
𝕌-dec 𝕌Prop   𝕌Agents = inj₂ (λ ())
𝕌-dec 𝕌Prop   𝕌Prop   = inj₁ refl
𝕌-dec 𝕌Prop   𝕌Data   = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Agent  = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Agents = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Prop   = inj₂ (λ ())
𝕌-dec 𝕌Data   𝕌Data   = inj₁ refl

𝕍-dec : decidable 𝕍
𝕍-dec (𝕍𝕌 u) (𝕍𝕌 v) with 𝕌-dec u v
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ h → p (𝕍𝕌-inj h))
𝕍-dec (𝕍𝕌 x) 𝕍ℝ = inj₂ (λ ())
𝕍-dec 𝕍ℝ (𝕍𝕌 x) = inj₂ (λ ())
𝕍-dec 𝕍ℝ 𝕍ℝ = inj₁ refl

Ctxt-dec : decidable Ctxt
Ctxt-dec ⟨⟩ ⟨⟩ = inj₁ refl
Ctxt-dec ⟨⟩ (Δ ، u) = inj₂ (λ ())
Ctxt-dec (Γ ، u) ⟨⟩ = inj₂ (λ ())
Ctxt-dec (Γ ، u) (Δ ، v) with Ctxt-dec Γ Δ
... | inj₂ p = inj₂ (λ k → p (،-inj₁ k))
... | inj₁ refl with 𝕍-dec u v
... |   inj₂ p = inj₂ (λ k → p (،-inj₂ k))
... |   inj₁ refl = inj₁ refl

Form-dec-⊥ : {Γ : Ctxt} (A : Form Γ) → A ≡ ⊥· ⊎ ¬ (A ≡ ⊥·)
Form-dec-⊥ {Γ} (𝕒 x) = inj₂ (λ ())
Form-dec-⊥ {Γ} ⊤· = inj₂ (λ ())
Form-dec-⊥ {Γ} ⊥· = inj₁ refl
Form-dec-⊥ {Γ} (A ∧· A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A ∨· A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A →· A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (¬· A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (∀· u A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (∃· u A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (x ∈ₐ x₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ ())
--Form-dec-⊥ {Γ} (x ∈ᵢ x₁) = inj₂ (λ ())
--Form-dec-⊥ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A Ｕ A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｏ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (A Ｓ A₁) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｙ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｂ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (Ｆ A) = inj₂ (λ ())
Form-dec-⊥ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ ())

Form-dec-⊤ : {Γ : Ctxt} (A : Form Γ) → A ≡ ⊤· ⊎ ¬ (A ≡ ⊤·)
Form-dec-⊤ {Γ} (𝕒 x) = inj₂ (λ ())
Form-dec-⊤ {Γ} ⊤· = inj₁ refl
Form-dec-⊤ {Γ} ⊥· = inj₂ (λ ())
Form-dec-⊤ {Γ} (A ∧· A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A ∨· A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A →· A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (¬· A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (∀· u A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (∃· u A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (x ∈ₐ x₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ ())
--Form-dec-⊤ {Γ} (x ∈ᵢ x₁) = inj₂ (λ ())
--Form-dec-⊤ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A Ｕ A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｏ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (A Ｓ A₁) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｙ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｂ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (Ｆ A) = inj₂ (λ ())
Form-dec-⊤ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ ())

Form-dec-∧ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a ∧· b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a ∧· b))
Form-dec-∧ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∧ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∧ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A ∧· A₁) = inj₁ (A , A₁ , refl)
Form-dec-∧ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-∧ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∧ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∧ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∨ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a ∨· b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a ∨· b))
Form-dec-∨ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∨ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∨ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A ∨· A₁) = inj₁ (A , A₁ , refl)
Form-dec-∨ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-∨ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∨ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∨ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-→ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a →· b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a →· b))
Form-dec-→ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-→ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-→ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-→ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A →· A₁) = inj₁ (A , A₁ , refl)
Form-dec-→ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-→ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-→ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-→ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-Ｕ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a Ｕ b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a Ｕ b))
Form-dec-Ｕ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-Ｕ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-Ｕ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A Ｕ A₁) = inj₁ (A , A₁ , refl)
Form-dec-Ｕ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-Ｕ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-Ｓ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → Σ (Form Γ) (λ b → A ≡ a Ｓ b)))
           ⊎ ((a b : Form Γ) → ¬ (A ≡ a Ｓ b))
Form-dec-Ｓ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-Ｓ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-Ｓ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (A Ｓ A₁) = inj₁ (A , A₁ , refl)
Form-dec-Ｓ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-Ｓ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∀ : {Γ : Ctxt} (A : Form Γ)
           → (Σ 𝕌 (λ a → Σ (Form (Γ ، 𝕍𝕌 a)) (λ b → A ≡ ∀· a b)))
           ⊎ ((a : 𝕌) (b : Form (Γ ، 𝕍𝕌 a)) → ¬ (A ≡ ∀· a b))
Form-dec-∀ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∀ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∀ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (∀· u A) = inj₁ (u , A , refl)
Form-dec-∀ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-∀ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∀ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∀ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∃ : {Γ : Ctxt} (A : Form Γ)
           → (Σ 𝕌 (λ a → Σ (Form (Γ ، 𝕍𝕌 a)) (λ b → A ≡ ∃· a b)))
           ⊎ ((a : 𝕌) (b : Form (Γ ، 𝕍𝕌 a)) → ¬ (A ≡ ∃· a b))
Form-dec-∃ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∃ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∃ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (∃· u A) = inj₁ (u , A , refl)
Form-dec-∃ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-∃ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∃ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∃ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∈ₐ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Agent Γ) (λ a → Σ (Agents Γ) (λ b → A ≡ a ∈ₐ b)))
           ⊎ ((a : Agent Γ) (b : Agents Γ) → ¬ (A ≡ a ∈ₐ b))
Form-dec-∈ₐ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (x ∈ₐ x₁) = inj₁ (x , x₁ , refl)
Form-dec-∈ₐ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b ())
--Form-dec-∈ₐ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∈ₐ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∈ₐ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-∣∣ₛ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Agents Γ) (λ a → Σ ℕ (λ b → A ≡ ∣ a ∣ₛ＝ b)))
           ⊎ ((a : Agents Γ) (b : ℕ) → ¬ (A ≡ ∣ a ∣ₛ＝ b))
Form-dec-∣∣ₛ {Γ} (𝕒 x) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} ⊤· = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} ⊥· = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A ∧· A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A ∨· A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A →· A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (¬· A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (∀· u A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (∃· u A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (∣ x ∣ₛ＝ x₁) = inj₁ (x , x₁ , refl)
--Form-dec-∣∣ₛ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b ())
--Form-dec-∣∣ₛ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A Ｕ A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｏ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (A Ｓ A₁) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｙ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｂ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (Ｆ A) = inj₂ (λ a b ())
Form-dec-∣∣ₛ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a b ())

Form-dec-Ｏ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ Ｏ a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ Ｏ a))
Form-dec-Ｏ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｏ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A →· A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (x ∈ₐ x₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a ())
--Form-dec-Ｏ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｏ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｏ A) = inj₁ (A , refl)
Form-dec-Ｏ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-Ｏ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-Ｙ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ Ｙ a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ Ｙ a))
Form-dec-Ｙ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｙ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A →· A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (x ∈ₐ x₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a ())
--Form-dec-Ｙ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｙ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (Ｙ A) = inj₁ (A , refl)
Form-dec-Ｙ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-Ｙ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-Ｂ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ Ｂ a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ Ｂ a))
Form-dec-Ｂ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｂ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A →· A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (x ∈ₐ x₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a ())
--Form-dec-Ｂ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｂ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (Ｂ A) = inj₁ (A , refl)
Form-dec-Ｂ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-Ｂ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-¬ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form Γ) (λ a → A ≡ ¬· a))
           ⊎ ((a : Form Γ) → ¬ (A ≡ ¬· a))
Form-dec-¬ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-¬ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-¬ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-¬ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A →· A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (¬· A) = inj₁ (A , refl)
Form-dec-¬ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (x ∈ₐ x₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a ())
--Form-dec-¬ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-¬ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-¬ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-Ｆ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Form (Γ ، 𝕍ℝ)) (λ a → A ≡ Ｆ a))
           ⊎ ((a : Form (Γ ، 𝕍ℝ)) → ¬ (A ≡ Ｆ a))
Form-dec-Ｆ {Γ} (𝕒 x) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} ⊤· = inj₂ (λ a ())
Form-dec-Ｆ {Γ} ⊥· = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A →· A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (x ∈ₐ x₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a ())
--Form-dec-Ｆ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-Ｆ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-Ｆ {Γ} (Ｆ A) = inj₁ (A , refl)
Form-dec-Ｆ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

Form-dec-⟨⟩ : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Res Γ) (λ a → Σ (Comparison) (λ b → Σ (Res Γ) (λ c → A ≡ a ⟨ b ⟩ c))))
           ⊎ ((a : Res Γ) (b : Comparison) (c : Res Γ) → ¬ (A ≡ a ⟨ b ⟩ c))
Form-dec-⟨⟩ {Γ} (𝕒 x) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} ⊤· = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} ⊥· = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A ∧· A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A ∨· A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A →· A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (¬· A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (∀· u A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (∃· u A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (x ∈ₐ x₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a b c ())
--Form-dec-⟨⟩ {Γ} (x ∈ᵢ x₁) = inj₂ (λ a b c ())
--Form-dec-⟨⟩ {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A Ｕ A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｏ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (A Ｓ A₁) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｙ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｂ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (Ｆ A) = inj₂ (λ a b c ())
Form-dec-⟨⟩ {Γ} (t₁ ⟨ x ⟩ t₂) = inj₁ (t₁ , x , t₂ , refl)

Form-dec-𝕒 : {Γ : Ctxt} (A : Form Γ)
           → (Σ (Atom Γ) (λ a → A ≡ 𝕒 a))
           ⊎ ((a : Atom Γ) → ¬ (A ≡ 𝕒 a))
Form-dec-𝕒 {Γ} (𝕒 x) = inj₁ (x , refl)
Form-dec-𝕒 {Γ} ⊤· = inj₂ (λ a ())
Form-dec-𝕒 {Γ} ⊥· = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A ∧· A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A ∨· A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A →· A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (¬· A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (∀· u A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (∃· u A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (x ∈ₐ x₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (∣ x ∣ₛ＝ x₁) = inj₂ (λ a ())
--Form-dec-𝕒 {Γ} (x ∈ᵢ x₁) = inj₂ (λ a ())
--Form-dec-𝕒 {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A Ｕ A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｏ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (A Ｓ A₁) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｙ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｂ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (Ｆ A) = inj₂ (λ a ())
Form-dec-𝕒 {Γ} (t₁ ⟨ x ⟩ t₂) = inj₂ (λ a ())

var-dec : {Γ : Ctxt} {v : 𝕍} → decidable (∈Ctxt v Γ)
var-dec {Γ} {v} (∈Ctxt0 Γ₁) (∈Ctxt0 .Γ₁) = inj₁ refl
var-dec {Γ} {v} (∈Ctxt0 Γ₁) (∈CtxtS .v j) = inj₂ (λ ())
var-dec {Γ} {v} (∈CtxtS u i) (∈Ctxt0 _) = inj₂ (λ ())
var-dec {Γ} {v} (∈CtxtS u i) (∈CtxtS .u j)
  with var-dec i j
... | inj₂ p = inj₂ (λ k → p (∈CtxtS-inj k))
... | inj₁ refl = inj₁ refl

Res-dec : {Γ : Ctxt} → decidable (Res Γ)
Res-dec {Γ} (var i) (var j) with var-dec i j
... | inj₂ p = inj₂ (λ k → p (var-inj k))
... | inj₁ refl = inj₁ refl
Res-dec {Γ} (var i) 𝟎 = inj₂ (λ ())
Res-dec {Γ} (var i) (s ⋆ s₁) = inj₂ (λ ())
Res-dec {Γ} 𝟎 (var i) = inj₂ (λ ())
Res-dec {Γ} 𝟎 𝟎 = inj₁ refl
Res-dec {Γ} 𝟎 (s ⋆ s₁) = inj₂ (λ ())
Res-dec {Γ} (r ⋆ r₁) (var i) = inj₂ (λ ())
Res-dec {Γ} (r ⋆ r₁) 𝟎 = inj₂ (λ ())
Res-dec {Γ} (r ⋆ r₁) (s ⋆ s₁)
  with Res-dec r s
... | inj₂ p = inj₂ (λ k → p (⋆-inj₁ k))
... | inj₁ refl
  with Res-dec r₁ s₁
... | inj₂ p = inj₂ (λ k → p (⋆-inj₂ k))
... | inj₁ refl = inj₁ refl

ℕ-dec : decidable ℕ
ℕ-dec zero zero = inj₁ refl
ℕ-dec zero (suc b) = inj₂ (λ ())
ℕ-dec (suc a) zero = inj₂ (λ ())
ℕ-dec (suc a) (suc b)
  with ℕ-dec a b
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (suc-injective k))

atomProp-dec : decidable atomProp
atomProp-dec = ℕ-dec

agent-dec : decidable agent
agent-dec = ℕ-dec

AtomProp-dec : {Γ : Ctxt} → decidable (AtomProp Γ)
AtomProp-dec {Γ} (atomPropV i) (atomPropV i₁)
  with var-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atomPropV-inj k))
AtomProp-dec {Γ} (atomPropV i) (atomPropC x) = inj₂ (λ ())
AtomProp-dec {Γ} (atomPropC x) (atomPropV i) = inj₂ (λ ())
AtomProp-dec {Γ} (atomPropC x) (atomPropC x₁)
  with atomProp-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atomPropC-inj k))

Data-dec : {Γ : Ctxt} → decidable (Data Γ)
Data-dec {Γ} (dataV i) (dataV i₁)
  with var-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (dataV-inj k))
Data-dec {Γ} (dataV i) (dataC x) = inj₂ (λ ())
Data-dec {Γ} (dataC x) (dataV i) = inj₂ (λ ())
Data-dec {Γ} (dataC x) (dataC x₁)
  with ℕ-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (dataC-inj k))

Agent-dec : {Γ : Ctxt} → decidable (Agent Γ)
Agent-dec {Γ} (agentV i) (agentV i₁)
  with var-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (agentV-inj k))
Agent-dec {Γ} (agentV i) (agentC x) = inj₂ (λ ())
Agent-dec {Γ} (agentC x) (agentV i) = inj₂ (λ ())
Agent-dec {Γ} (agentC x) (agentC x₁)
  with agent-dec x x₁
... | inj₂ p = inj₂ (λ k → p (agentC-inj k))
... | inj₁ refl = inj₁ refl

AgentL-dec : {Γ : Ctxt} → decidable (List (Agent Γ))
AgentL-dec {Γ} [] [] = inj₁ refl
AgentL-dec {Γ} [] (x ∷ b) = inj₂ (λ ())
AgentL-dec {Γ} (x ∷ a) [] = inj₂ (λ ())
AgentL-dec {Γ} (x ∷ a) (x₁ ∷ b)
  with Agent-dec x x₁
... | inj₂ p = inj₂ (λ k → p (∷-injectiveˡ k))
... | inj₁ refl
  with AgentL-dec a b
... | inj₂ p = inj₂ (λ k → p (∷-injectiveʳ k))
... | inj₁ refl = inj₁ refl

agents-dec : decidable agents
agents-dec [] [] = inj₁ refl
agents-dec [] (x ∷ b) = inj₂ (λ ())
agents-dec (x ∷ a) [] = inj₂ (λ ())
agents-dec (x ∷ a) (x₁ ∷ b)
  with agent-dec x x₁
... | inj₂ p = inj₂ (λ k → p (∷-injectiveˡ k))
... | inj₁ refl
  with agents-dec a b
... | inj₂ p = inj₂ (λ k → p (∷-injectiveʳ k))
... | inj₁ refl = inj₁ refl

Agents-dec : {Γ : Ctxt} → decidable (Agents Γ)
Agents-dec {Γ} (agentsV i) (agentsV i₁)
  with var-dec i i₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (agentsV-inj k))
Agents-dec {Γ} (agentsV i) (agentsL x) = inj₂ (λ ())
--Agents-dec {Γ} (agentsV i) (agentsS x) = inj₂ (λ ())
Agents-dec {Γ} (agentsL x) (agentsV i) = inj₂ (λ ())
Agents-dec {Γ} (agentsL x) (agentsL x₁)
  with AgentL-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (agentsL-inj k))
--Agents-dec {Γ} (agentsL x) (agentsS x₁) = inj₂ (λ ())
--Agents-dec {Γ} (agentsS x) (agentsV i) = inj₂ (λ ())
--Agents-dec {Γ} (agentsS x) (agentsL x₁) = inj₂ (λ ())
--Agents-dec {Γ} (agentsS x) (agentsS x₁)
--  with agents-dec x x₁
--... | inj₁ refl = inj₁ refl
--... | inj₂ p = inj₂ (λ k → p (agentsS-inj k))

Action-dec : {Γ : Ctxt} → decidable (Action Γ)
Action-dec {Γ} (ActSend p a A) (ActSend p₁ a₁ A₁)
  with Data-dec p p₁
... | inj₂ q = inj₂ (λ k → q (ActSend-inj₁ k))
... | inj₁ refl
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (ActSend-inj₂ k))
... | inj₁ refl
  with Agents-dec A A₁
... | inj₂ q = inj₂ (λ k → q (ActSend-inj₃ k))
... | inj₁ refl = inj₁ refl

Event-dec : {Γ : Ctxt} → decidable (Event Γ)
Event-dec {Γ} (EvtReceive p a b) (EvtReceive p₁ a₁ b₁)
  with Data-dec p p₁
... | inj₂ q = inj₂ (λ k → q (EvtReceive-inj₁ k))
... | inj₁ refl
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (EvtReceive-inj₂ k))
... | inj₁ refl
  with Agent-dec b b₁
... | inj₂ q = inj₂ (λ k → q (EvtReceive-inj₃ k))
... | inj₁ refl = inj₁ refl
Event-dec {Γ} (EvtReceive p a b₁) (EvtInternal a₁ d) = inj₂ (λ ())
Event-dec {Γ} (EvtInternal a d) (EvtReceive p a₁ b) = inj₂ (λ ())
Event-dec {Γ} (EvtInternal a d) (EvtInternal a₁ d₁)
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (EvtInternal-inj₁ k))
... | inj₁ refl
  with Data-dec d d₁
... | inj₂ q = inj₂ (λ k → q (EvtInternal-inj₂ k))
... | inj₁ refl = inj₁ refl

Fault-dec : {Γ : Ctxt} → decidable (Fault Γ)
Fault-dec {Γ} (FaultCorrect a b) (FaultCorrect a₁ b₁)
  with Agent-dec a a₁
... | inj₂ q = inj₂ (λ k → q (FaultCorrect-inj₁ k))
... | inj₁ refl
  with Agent-dec b b₁
... | inj₂ q = inj₂ (λ k → q (FaultCorrect-inj₂ k))
... | inj₁ refl = inj₁ refl

Atom-dec : {Γ : Ctxt} → decidable (Atom Γ)
Atom-dec {Γ} (atProp x) (atProp x₁)
  with AtomProp-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atProp-inj k))
Atom-dec {Γ} (atProp x) (atAction x₁) = inj₂ (λ ())
Atom-dec {Γ} (atProp x) (atEvent x₁) = inj₂ (λ ())
Atom-dec {Γ} (atProp x) (atCorrect x₁) = inj₂ (λ ())
Atom-dec {Γ} (atAction x) (atProp x₁) = inj₂ (λ ())
Atom-dec {Γ} (atAction x) (atAction x₁)
  with Action-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atAction-inj k))
Atom-dec {Γ} (atAction x) (atEvent x₁) = inj₂ (λ ())
Atom-dec {Γ} (atAction x) (atCorrect x₁) = inj₂ (λ ())
Atom-dec {Γ} (atEvent x) (atProp x₁) = inj₂ (λ ())
Atom-dec {Γ} (atEvent x) (atAction x₁) = inj₂ (λ ())
Atom-dec {Γ} (atEvent x) (atEvent x₁)
  with Event-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atEvent-inj k))
Atom-dec {Γ} (atEvent x) (atCorrect x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atProp x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atAction x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atEvent x₁) = inj₂ (λ ())
Atom-dec {Γ} (atCorrect x) (atCorrect x₁)
  with Fault-dec x x₁
... | inj₁ refl = inj₁ refl
... | inj₂ p = inj₂ (λ k → p (atCorrect-inj k))

Form-dec : {Γ : Ctxt} → decidable (Form Γ)
Form-dec {Γ} (𝕒 x) B with Form-dec-𝕒 B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Atom-dec x a
... | inj₂ p = inj₂ (λ k → p (𝕒-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} ⊤· B with Form-dec-⊤ B
... | inj₂ p = inj₂ (λ k → p (sym k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} ⊥· B with Form-dec-⊥ B
... | inj₂ p = inj₂ (λ k → p (sym k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A ∧· A₁) B with Form-dec-∧ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (∧-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (∧-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A ∨· A₁) B with Form-dec-∨ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (∨-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (∨-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A →· A₁) B with Form-dec-→ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (→-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (→-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (¬· A) B with Form-dec-¬ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (¬-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (∀· u A) B with Form-dec-∀ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with 𝕌-dec u a
... | inj₂ p = inj₂ (λ k → p (∀-inj₁ k))
... | inj₁ refl with Form-dec A b
... | inj₂ p = inj₂ (λ k → p (∀-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (∃· u A) B with Form-dec-∃ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with 𝕌-dec u a
... | inj₂ p = inj₂ (λ k → p (∃-inj₁ k))
... | inj₁ refl with Form-dec A b
... | inj₂ p = inj₂ (λ k → p (∃-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (x ∈ₐ x₁) B with Form-dec-∈ₐ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Agent-dec x a
... | inj₂ p = inj₂ (λ k → p (∈ₐ-inj₁ k))
... | inj₁ refl with Agents-dec x₁ b
... | inj₂ p = inj₂ (λ k → p (∈ₐ-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (∣ x ∣ₛ＝ x₁) B with Form-dec-∣∣ₛ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Agents-dec x a
... | inj₂ p = inj₂ (λ k → p (∣∣ₛ-inj₁ k))
... | inj₁ refl with ℕ-dec x₁ b
... | inj₂ p = inj₂ (λ k → p (∣∣ₛ-inj₂ k))
... | inj₁ refl = inj₁ refl
--Form-dec {Γ} (x ∈ᵢ x₁) B = {!!}
--Form-dec {Γ} (⟨ x ، x₁ ⟩∈ᵣ x₂) B = {!!}
Form-dec {Γ} (A Ｕ A₁) B with Form-dec-Ｕ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｕ-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (Ｕ-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｏ A) B with Form-dec-Ｏ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｏ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (A Ｓ A₁) B with Form-dec-Ｓ B
... | inj₂ p = inj₂ (λ k → p _ _ (sym k))
... | inj₁ (a , b , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｓ-inj₁ k))
... | inj₁ refl with Form-dec A₁ b
... | inj₂ p = inj₂ (λ k → p (Ｓ-inj₂ k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｙ A) B with Form-dec-Ｙ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｙ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｂ A) B with Form-dec-Ｂ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｂ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (Ｆ A) B with Form-dec-Ｆ B
... | inj₂ p = inj₂ (λ k → p _ (sym k))
... | inj₁ (a , refl) with Form-dec A a
... | inj₂ p = inj₂ (λ k → p (Ｆ-inj k))
... | inj₁ refl = inj₁ refl
Form-dec {Γ} (t₁ ⟨ x ⟩ t₂) B with Form-dec-⟨⟩ B
... | inj₂ p = inj₂ (λ k → p _ _ _ (sym k))
... | inj₁ (a , b , c , refl) with Res-dec t₁ a
... | inj₂ p = inj₂ (λ k → p (comp-inj₁ k))
... | inj₁ refl with Comparison-dec x b
... | inj₂ p = inj₂ (λ k → p (comp-inj₂ k))
... | inj₁ refl with Res-dec t₂ c
... | inj₂ p = inj₂ (λ k → p (comp-inj₃ k))
... | inj₁ refl = inj₁ refl

≡⊆-dec : {Γ Δ : Ctxt} (i j : Γ ⊆ Δ) → ≡⊆ i j ⊎ ¬ (≡⊆ i j)
≡⊆-dec {⟨⟩} {Δ} i j = inj₁ (λ ())
≡⊆-dec {Γ ، U} {Δ} i j with var-dec (i (∈Ctxt0 Γ)) (j (∈Ctxt0 Γ))
... | inj₂ p = inj₂ (λ z → p (z (∈Ctxt0 Γ)))
... | inj₁ p with ≡⊆-dec {Γ} {Δ} (λ z → i (∈CtxtS _ z)) (λ z → j (∈CtxtS _ z))
... |   inj₂ q = inj₂ (λ z → q (λ {u} k → z (∈CtxtS U k)))
... |   inj₁ q = inj₁ h
  where
  h : {u : 𝕍} (z : ∈Ctxt u (Γ ، U)) → i z ≡ j z
  h {u} (∈Ctxt0 .Γ) = p
  h {u} (∈CtxtS .U z) = q z

\end{code}
