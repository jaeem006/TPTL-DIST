\begin{code}
{-# OPTIONS --without-K --safe #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)

open import Agda.Builtin.Equality

open import Data.Nat
open import Data.Nat.Properties using ()
open import Data.List
open import Data.List.Properties using (map-cong-local)
open import Data.List.Relation.Unary.All
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤ ; tt)
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

open import World
open import Misc

-- 𝔻 is a "data" set
module Syntax (𝔻 : Set) (W : World) where

open World.World W

data 𝕌 : Set where
  𝕌Agent  : 𝕌
  𝕌Agents : 𝕌
  𝕌Prop   : 𝕌
  𝕌Data   : 𝕌

data 𝕍 : Set where
  𝕍𝕌 : 𝕌 → 𝕍
  𝕍ℝ : 𝕍

𝕍Agent : 𝕍
𝕍Agent = 𝕍𝕌 𝕌Agent

𝕍Agents : 𝕍
𝕍Agents = 𝕍𝕌 𝕌Agents

𝕍Prop : 𝕍
𝕍Prop = 𝕍𝕌 𝕌Prop

𝕍Data : 𝕍
𝕍Data = 𝕍𝕌 𝕌Data

𝕍World : 𝕍
𝕍World = 𝕍ℝ

data Ctxt : Set where
  ⟨⟩  : Ctxt
  -- extension of the context with a variable
  _،_ : (c : Ctxt) (U : 𝕍) → Ctxt

infixl 60 _،_

-- A variable of type u
data ∈Ctxt (v : 𝕍) : Ctxt → Set where
 ∈Ctxt0 : (Γ : Ctxt) → ∈Ctxt v (Γ ، v)
 ∈CtxtS : {Γ : Ctxt} (u : 𝕍) → ∈Ctxt v Γ → ∈Ctxt v (Γ ، u)

agent : Set
agent = ℕ

-- Agent (a)
data Agent (Γ : Ctxt) : Set where
  agentV : (i : ∈Ctxt 𝕍Agent Γ) → Agent Γ -- variable
  agentC : agent → Agent Γ  -- constant

agents : Set
agents = List agent -- agent → Set

-- Group of agents (A)
data Agents (Γ : Ctxt) : Set where
  agentsV : (i : ∈Ctxt 𝕍Agents Γ) → Agents Γ -- variable
  agentsL : List (Agent Γ) → Agents Γ        -- list
--  agentsS : agents → Agents Γ                -- set

agentsS : {Γ : Ctxt} → agents → Agents Γ
agentsS {Γ} l = agentsL (Data.List.map agentC l)

data Data (Γ : Ctxt) : Set where
  dataV : (i : ∈Ctxt 𝕍Data Γ) → Data Γ
  dataC : 𝔻 → Data Γ

DataProp : Set₁
DataProp = 𝔻 → Set

DataRel : Set₁
DataRel = 𝔻 → 𝔻 → Set

-- Atomic propositions (p)
atomProp : Set
atomProp = ℕ -- fix

data AtomProp (Γ : Ctxt) : Set where
  atomPropV : (i : ∈Ctxt 𝕍Prop Γ) → AtomProp Γ -- variable
  atomPropC : atomProp → AtomProp Γ            -- constant

-- Action (σ)
data Action (Γ : Ctxt) : Set₁ where
  -- Agent a sends some atom p to the set of Agents A
  ActSend : (p : Data Γ) (a : Agent Γ) (A : Agents Γ) → Action Γ

-- Event (ϵ)
data Event (Γ : Ctxt) : Set₁ where
  -- Agent b receives some atom p from a
  EvtReceive  : (p : Data Γ) (a b : Agent Γ) → Event Γ
  -- An internal event with some "data" associated with it
  EvtInternal : (a : Agent Γ) (d : Data Γ) → Event Γ

data Fault (Γ : Ctxt) : Set₁ where
  -- The link from agent a to agent b is correct
  FaultCorrect : (a b : Agent Γ) → Fault Γ

-- Atom (τ)
data Atom (Γ : Ctxt) : Set₁ where
  atProp    : AtomProp Γ → Atom Γ
  atAction  : Action Γ   → Atom Γ
  atEvent   : Event Γ    → Atom Γ
  atCorrect : Fault Γ    → Atom Γ

atom : Set₁
atom = Atom ⟨⟩

ResVar : Set
ResVar = ℕ

-- Res (resource)
data Res (Γ : Ctxt) : Set where
  𝐯   : (i : ∈Ctxt  𝕍World Γ) → Res Γ
  𝟎   : Res Γ
--  𝐬   : Res Γ → Res Γ
  _⋆_ : Res Γ → Res Γ → Res Γ
  rvar : ResVar → Res Γ

infixl 50 _⋆_

Res₀ : Set
Res₀ = Res ⟨⟩


data Comparison : Set where
  LE : Comparison
  LT : Comparison
  EQ : Comparison
  PR : Comparison

data SetAtom : (Γ : Ctxt) → Set where
  _∈ₐ_    : {Γ : Ctxt} → Agent Γ → Agents Γ → SetAtom Γ
  ∣_∣ₛ＝_ : {Γ : Ctxt} → Agents Γ → ℕ → SetAtom Γ

FormVar : Set
FormVar = ℕ

data Form : (Γ : Ctxt) → Set₁ where
  𝕒     : {Γ : Ctxt} → Atom Γ → Form Γ
  var   : {Γ : Ctxt} → FormVar → Form Γ
  -- Propositional logic
  ⊤·    : {Γ : Ctxt} → Form Γ
  ⊥·    : {Γ : Ctxt} → Form Γ
  _∧·_  : {Γ : Ctxt} → Form Γ → Form Γ → Form Γ
  _∨·_  : {Γ : Ctxt} → Form Γ → Form Γ → Form Γ
  _→·_  : {Γ : Ctxt} → Form Γ → Form Γ → Form Γ
  -- Predicate logic
  ∀·    : {Γ : Ctxt} → (u : 𝕌) → Form (Γ ، 𝕍𝕌 u) → Form Γ
  ∃·    : {Γ : Ctxt} → (u : 𝕌) → Form (Γ ، 𝕍𝕌 u) → Form Γ
  𝔸     : {Γ : Ctxt} → SetAtom Γ → Form Γ
--
--  _∈ₐ_    : {Γ : Ctxt} → Agent Γ → Agents Γ → Form Γ
--  ∣_∣ₛ＝_ : {Γ : Ctxt} → Agents Γ → ℕ → Form Γ
--
--  _∈ᵢ_  : {Γ : Ctxt} → Data Γ → DataProp → Form Γ
--  ⟨_،_⟩∈ᵣ_  : {Γ : Ctxt} → Data Γ → Data Γ → DataRel → Form Γ
  -- Temporal logic
  _Ｕ_  : {Γ : Ctxt} → Form Γ → Form Γ → Form Γ
  Ｏ    : {Γ : Ctxt} → Form Γ → Form Γ
  _Ｓ_  : {Γ : Ctxt} → Form Γ → Form Γ → Form Γ
  Ｙ    : {Γ : Ctxt} → Form Γ → Form Γ
  Ｂ    : {Γ : Ctxt} → Form Γ → Form Γ -- Similar to Ｙ but holds if no previous point exist
  Ｆ_  : {Γ : Ctxt} → Form (Γ ، 𝕍ℝ) → Form Γ
  -- clocks comparations (Maybe theres a beteer way of doing it)
  {--
  _⊑_   : {Γ : Ctxt} {x : ℝ} → (v : ∈Ctxt (𝕍ℝ x) Γ) → (c : 𝕎) → Form Γ
  _⊏_   : {Γ : Ctxt} {x : ℝ} → (v : ∈Ctxt (𝕍ℝ x) Γ) → (c : 𝕎) → Form Γ
  _⊒_   : {Γ : Ctxt} {x : ℝ} → (v : ∈Ctxt (𝕍ℝ x) Γ) → (c : 𝕎) → Form Γ
  _⊐_   : {Γ : Ctxt} {x : ℝ} → (v : ∈Ctxt (𝕍ℝ x) Γ) → (c : 𝕎) → Form Γ
  _＝_  : {Γ : Ctxt} {x : ℝ} → (v : ∈Ctxt (𝕍ℝ x) Γ) → (c : 𝕎) → Form Γ
  --}
  _⟨_⟩_   : {Γ : Ctxt} → (t₁ : Res Γ) → Comparison → (t₂ : Res Γ) → Form Γ

¬·_ : {Γ : Ctxt} → Form Γ → Form Γ
¬· f = f →· ⊥·

_⊑_ : {Γ : Ctxt} → (t₁ : Res Γ) → (t₂ : Res Γ) → Form Γ
_⊑_ = _⟨ LE ⟩_

_⊏_ : {Γ : Ctxt} → (t₁ : Res Γ) → (t₂ : Res Γ) → Form Γ
_⊏_ = _⟨ LT ⟩_

_⊒_ : {Γ : Ctxt} → (t₁ : Res Γ) → (t₂ : Res Γ) → Form Γ
a ⊒ b = b ⊑ a

_⊐_ : {Γ : Ctxt} → (t₁ : Res Γ) → (t₂ : Res Γ) → Form Γ
a ⊐ b = b ⊏ a

_＝_ : {Γ : Ctxt} → (t₁ : Res Γ) → (t₂ : Res Γ) → Form Γ
_＝_ = _⟨ EQ ⟩_

_◁_ :  {Γ : Ctxt} → (t₁ : Res Γ) → (t₂ : Res Γ) → Form Γ
_◁_ = _⟨ PR ⟩_

infixl 40 _⊑_
infixl 40 _⊏_
infixl 40 _⊒_
infixl 40 _⊐_
infixl 40 _＝_
infixl 40 _◁_

infixl 32 _∧·_
infixl 31 _∨·_
infixr 30 _→·_

Form₀ : Set₁
Form₀ = Form ⟨⟩


------
-- Quantifiers
--

∀ₐ : {Γ : Ctxt} → Form (Γ ، 𝕍𝕌 𝕌Agent) → Form Γ
∀ₐ f = ∀· 𝕌Agent f

∀ₛ : {Γ : Ctxt} → Form (Γ ، 𝕍𝕌 𝕌Agents) → Form Γ
∀ₛ f = ∀· 𝕌Agents f

∀ₚ : {Γ : Ctxt} → Form (Γ ، 𝕍𝕌 𝕌Prop) → Form Γ
∀ₚ f = ∀· 𝕌Prop f

∀ᵢ : {Γ : Ctxt} → Form (Γ ، 𝕍𝕌 𝕌Data) → Form Γ
∀ᵢ f = ∀· 𝕌Data f

-- Existentials
∃ₐ : {Γ : Ctxt} → Form (Γ ، 𝕍Agent) → Form Γ
∃ₐ f = ∃· 𝕌Agent f

∃ₛ : {Γ : Ctxt} → Form (Γ ، 𝕍Agents) → Form Γ
∃ₛ f = ∃· 𝕌Agents f

∃ₚ : {Γ : Ctxt} → Form (Γ ، 𝕍Prop) → Form Γ
∃ₚ f = ∃· 𝕌Prop f

∃ᵢ : {Γ : Ctxt} → Form (Γ ، 𝕍Data) → Form Γ
∃ᵢ f = ∃· 𝕌Data f


------
-- Actions/Events
--

-- sending action
send[_⇒_⇒_] : {Γ : Ctxt} → Agent Γ → Data Γ → Agents Γ → Form Γ
send[ a ⇒ p ⇒ A ] = 𝕒 (atAction (ActSend p a A)) {--⟨ p ⟩ a A--}

-- receiving event
recv[_⇐_⇐_] : {Γ : Ctxt} → Agent Γ → Data Γ → Agent Γ → Form Γ
recv[ b ⇐ p ⇐ a ] = 𝕒 (atEvent (EvtReceive p a b))

-- internal event
●[_,_] : {Γ : Ctxt} → Agent Γ → Data Γ → Form Γ
●[ a , d ] = 𝕒 (atEvent (EvtInternal a d))


------
-- Temporal operators
--

-- Eventually
◇ : {Γ : Ctxt} → Form Γ → Form Γ
◇ {Γ} ϕ = ⊤· Ｕ ϕ

-- Before
◆ : {Γ : Ctxt} → Form Γ → Form Γ
◆ {Γ} ϕ = ⊤· Ｓ ϕ

-- Strict before
◆· : {Γ : Ctxt} → Form Γ → Form Γ
◆· {Γ} ϕ = Ｙ (◆ ϕ) -- ◆ (Ｙ ϕ)

-- Always (classical)
□ : {Γ : Ctxt} → Form Γ → Form Γ
□ {Γ} ϕ = ¬· (◇ (¬· ϕ))

-- Always in the past (classical)
■ : {Γ : Ctxt} → Form Γ → Form Γ
■ {Γ} ϕ = ¬· (◆ (¬· ϕ))

-- Strict always in the past
■· : {Γ : Ctxt} → Form Γ → Form Γ
■· {Γ} ϕ = Ｂ (■ ϕ)


------
-- Variables
--

𝕔0 : {u : 𝕍} {Γ : Ctxt} → ∈Ctxt u (Γ ، u)
𝕔0 {u} {Γ} = ∈Ctxt0 Γ

𝕔1 : {u v : 𝕍} {Γ : Ctxt} → ∈Ctxt u (Γ ، u ، v)
𝕔1 {u} {v} {Γ} = ∈CtxtS v 𝕔0

𝕔2 : {u v w : 𝕍} {Γ : Ctxt} → ∈Ctxt u (Γ ، u ، v ، w)
𝕔2 {u} {v} {w} {Γ} = ∈CtxtS w 𝕔1

𝕔3 : {u v w x : 𝕍} {Γ : Ctxt} → ∈Ctxt u (Γ ، u ، v ، w ، x)
𝕔3 {u} {v} {w} {x} {Γ} = ∈CtxtS x 𝕔2

𝕔4 : {u v w x y : 𝕍} {Γ : Ctxt} → ∈Ctxt u (Γ ، u ، v ، w ، x ، y)
𝕔4 {u} {v} {w} {x} {y} {Γ} = ∈CtxtS y 𝕔3

𝕒0 : {Γ : Ctxt} → Agent (Γ ، 𝕍Agent)
𝕒0 {Γ} = agentV 𝕔0

𝕒1 : {Γ : Ctxt} {u : 𝕍} → Agent (Γ ، 𝕍Agent ، u)
𝕒1 {Γ} {u} = agentV 𝕔1

𝕒2 : {Γ : Ctxt} {u v : 𝕍} → Agent (Γ ، 𝕍Agent ، u ، v)
𝕒2 {Γ} {u} {v} = agentV 𝕔2

𝕒3 : {Γ : Ctxt} {u v w : 𝕍} → Agent (Γ ، 𝕍Agent ، u ، v ، w)
𝕒3 {Γ} {u} {v} {w} = agentV 𝕔3

𝕒4 : {Γ : Ctxt} {u v w x : 𝕍} → Agent (Γ ، 𝕍Agent ، u ، v ، w ، x)
𝕒4 {Γ} {u} {v} {w} {x} = agentV 𝕔4

𝔸0 : {Γ : Ctxt} → Agents (Γ ، 𝕍Agents)
𝔸0 {Γ} = agentsV 𝕔0

𝔸1 : {Γ : Ctxt} {u : 𝕍} → Agents (Γ ، 𝕍Agents ، u)
𝔸1 {Γ} {u} = agentsV 𝕔1

𝔸2 : {Γ : Ctxt} {u v : 𝕍} → Agents (Γ ، 𝕍Agents ، u ، v)
𝔸2 {Γ} {u} {v} = agentsV 𝕔2

𝕡0 : {Γ : Ctxt} → AtomProp (Γ ، 𝕍Prop)
𝕡0 {Γ} = atomPropV 𝕔0

𝕡1 : {Γ : Ctxt} {u : 𝕍} → AtomProp (Γ ، 𝕍Prop ، u)
𝕡1 {Γ} {u} = atomPropV 𝕔1

𝕕0 : {Γ : Ctxt} → Data (Γ ، 𝕍Data)
𝕕0 {Γ} = dataV 𝕔0

𝕕1 : {Γ : Ctxt} {u : 𝕍} → Data (Γ ، 𝕍Data ، u)
𝕕1 {Γ} {u} = dataV 𝕔1

𝕕2 : {Γ : Ctxt} {u v : 𝕍} → Data (Γ ، 𝕍Data ، u ، v)
𝕕2 {Γ} {u} {v} = dataV 𝕔2

𝐯0 : {Γ : Ctxt} → Form Γ
𝐯0 {Γ} = var 0

𝐯1 : {Γ : Ctxt} → Form Γ
𝐯1 {Γ} = var 1

𝐯2 : {Γ : Ctxt} → Form Γ
𝐯2 {Γ} = var 2


------
-- Groups of agents
--

-- builds a set containing 1 agent
[_]ₐ : {Γ : Ctxt} → Agent Γ → Agents Γ
[ a ]ₐ = agentsL [ a ]

-- builds a set containing 2 agents
[_,_]ₐ : {Γ : Ctxt} → Agent Γ → Agent Γ → Agents Γ
[ a , b ]ₐ = agentsL (a ∷ b ∷ [])

\end{code}
