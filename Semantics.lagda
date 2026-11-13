\begin{code}

{-# OPTIONS --safe #-}

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
open import Function using (_∘_ ; id)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

open import Axiom.Extensionality.Propositional

open import Misc
open import World

module Semantics(𝔻 : Set)
                (W : World)
       where

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import WorldUtil(W)

open World.World W

---- Model

-- Fault model
-- i and j are related if the connection from i to j is faulty
FaultModel : Set₁
FaultModel = agent → agent → 𝕎 → Set

-- An agent is faulty if one of its connection to a node is faulty at some point
faultyAgent : FaultModel → agent → Set
faultyAgent fm a =
  Σ 𝕎 (λ t → Σ agent (λ b → fm a b t))

-- An agent is correct it's not faulty
correctAgent : FaultModel → agent → Set
correctAgent fm a = ¬ faultyAgent fm a

-- It's a set of atomic propositions
GlobalState : Set₁
GlobalState = List atom

Run : Set₁
Run = 𝕎 → GlobalState

Runs : Set₁
Runs = Run → Set

-- interpretation of the atoms
Interp : Set₂
Interp = {--Agent →--} GlobalState → atom → Set₁
-- λ s p → p ∈ s

SemVar : Ctxt → Set₂
SemVar Γ = FormVar → (Δ : Ctxt) → Γ ⊆ Δ → Set₁
-- FormVar → Set₁

record Model (Γ : Ctxt) : Set₂ where
  constructor model
  field
--    Fm : FaultModel
--    runs   : Runs
    interp : Interp
    run    : Run
    w      : 𝕎
    subΓ   : Sub Γ
--    vars   : SemVar Γ
--    vars   : FormVar → Set₁

SemVar،→ : (Γ : Ctxt) (u : 𝕍)
        → SemVar (Γ ، u)
        → SemVar Γ
SemVar،→ Γ u s n Δ e = s n (Δ ، u) (⊆، u e)

→SemVar، : (Γ : Ctxt) (u : 𝕍)
        → SemVar Γ
        → SemVar (Γ ، u)
→SemVar، Γ u s n Δ e = s n Δ (⊆-trans ⊆₀ e)

→SemVar⊆ : {Γ Δ : Ctxt}
         → Γ ⊆ Δ
         → SemVar Γ
         → SemVar Δ
→SemVar⊆ {Γ} {Δ} e s n Φ f = s n Φ (⊆-trans e f)

Model،→ : {Γ : Ctxt} {u : 𝕍} → Model (Γ ، u) → Model Γ
Model،→ {Γ} {u} m@(model interp run w sub) =
  model interp run w (Sub،→ sub)

--_∈ₘ_ : {Γ : Ctxt} → Run → Model Γ → Set
--r ∈ₘ m = Model.runs m r

-- indistinguishability relation
--[_,_,_]_∼_ : agent → 𝕎 → Interp → Run → Run → Set₁
--[ a , t , I ] r₁ ∼ r₂ = (τ : atom) → I {--a--} (r₁ t a) τ ⇔ I {--a--} (r₂ t a) τ

--[_]_∼ₘ_ : {Γ : Ctxt} → agent → Model Γ → Run → Set₁
--[ a ] m ∼ₘ r = [ a , Model.w m , Model.interp m ] Model.run m ∼ r

-- Updates a model with a new run
_≔ᵣ_ : {Γ : Ctxt} → Model Γ → Run → Model Γ
model interp run w sub ≔ᵣ r = model interp r w sub

-- Updates a model with a new time
_≔ₜ_ : {Γ : Ctxt} → Model Γ → 𝕎 → Model Γ
model interp run w sub ≔ₜ t = model interp run t sub

-- Updates a model with a new set of agent
_≔_ : {Γ : Ctxt} → Model Γ → {u : 𝕍} → ⟦𝕍⟧ u → Model (Γ ، u)
_≔_ {Γ} (model interp run w sub) {u} v = model interp run w (sub ⹁ u ∶ v)

-- Updates a model with a new set of agent
_≔⟨_⟩_ : {Γ : Ctxt} → Model Γ → (u : 𝕍) → ⟦𝕍⟧ u → Model (Γ ، u)
_≔⟨_⟩_ {Γ} (model interp run w sub) u v = model interp run w (sub ⹁ u ∶ v)

_≔r_ : {Γ : Ctxt} → Model Γ → ⟦ℝ⟧ → Model (Γ ، 𝕍ℝ)
_≔r_ {Γ} (model interp run w sub) v = model interp run w (sub ⹁ 𝕍ℝ ∶ v)

-- Updates a model with a new set of agent
--_≔ₛ⟨_⟩_ : {Γ Δ : Ctxt} → Model Γ → Γ ⊆ Δ → Sub Δ → Model Δ
--_≔ₛ⟨_⟩_ {Γ} (model interp run w sub vars) e s = model interp run w s (→SemVar⊆ e vars)
_≔ₛ_ : {Γ Δ : Ctxt} → Model Γ → Sub Δ → Model Δ
_≔ₛ_ {Γ} (model interp run w sub) s = model interp run w s

≔ₛ-≔ᵣ : {Γ Δ : Ctxt} (M : Model Γ) (s : Sub Δ) (r : Run)
      → ((M ≔ₛ s) ≔ᵣ r) ≡ ((M ≔ᵣ r) ≔ₛ s)
≔ₛ-≔ᵣ {Γ} {Δ} (model interp r₁ w sub) s r = refl

≔ₛ-≔ₜ : {Γ Δ : Ctxt} (M : Model Γ) (s : Sub Δ) (w : 𝕎)
      → ((M ≔ₛ s) ≔ₜ w) ≡ ((M ≔ₜ w) ≔ₛ s)
≔ₛ-≔ₜ {Γ} {Δ} (model interp r w₁ sub) s w = refl

⟦_⟧ᵣ_ : {Γ : Ctxt} → Res Γ → Sub Γ → 𝕎
⟦ 𝐯 x ⟧ᵣ i  = app-sub x i
⟦ 𝟎 ⟧ᵣ i      = 𝟘
--⟦ 𝐬 t ⟧ᵣ i    = 𝕤 (⟦ t ⟧ᵣ i)
⟦ t ⋆ t₁ ⟧ᵣ i = (⟦ t ⟧ᵣ i) · (⟦ t₁ ⟧ᵣ i)
⟦ rvar ρ ⟧ᵣ i  = 𝟘

⟦_⟧ᵣ·_ : {Γ : Ctxt} → Res Γ → Model Γ → 𝕎
⟦ a ⟧ᵣ· m = ⟦ a ⟧ᵣ (Model.subΓ m)

⟦_⟧ᵢ_ : {Γ : Ctxt} → Agent Γ → Sub Γ → agent
⟦ agentV v ⟧ᵢ i = app-sub v i
⟦ agentC x ⟧ᵢ i = x

⟦_⟧ᵢ·_ : {Γ : Ctxt} → Agent Γ → Model Γ → agent
⟦ a ⟧ᵢ· m = ⟦ a ⟧ᵢ (Model.subΓ m)

⟦_⟧ₛ_ : {Γ : Ctxt} → Agents Γ → Sub Γ → agents
⟦ agentsV v ⟧ₛ i = app-sub v i
⟦ agentsL x ⟧ₛ i = Data.List.map (λ j → ⟦ j ⟧ᵢ i) x
--⟦ agentsS x ⟧ₛ i = x

⟦_⟧ₛ·_ : {Γ : Ctxt} → Agents Γ → Model Γ → agents
⟦ a ⟧ₛ· m = ⟦ a ⟧ₛ (Model.subΓ m)

⟦_⟧ₚ_ : {Γ : Ctxt} → AtomProp Γ → Sub Γ → atomProp
⟦ atomPropV v ⟧ₚ i = app-sub v i
⟦ atomPropC x ⟧ₚ i = x

⟦_⟧ₚ·_ : {Γ : Ctxt} → AtomProp Γ → Model Γ → atomProp
⟦ a ⟧ₚ· m = ⟦ a ⟧ₚ (Model.subΓ m)

⟦_⟧d_ : {Γ : Ctxt} → Data Γ → Sub Γ → 𝔻
⟦ dataV v ⟧d i = app-sub v i
⟦ dataC x ⟧d i = x

⟦_⟧d·_ : {Γ : Ctxt} → Data Γ → Model Γ → 𝔻
⟦ a ⟧d· m = ⟦ a ⟧d (Model.subΓ m)

⟦_⟧ₜ_ : {Γ : Ctxt} → Action Γ → Sub Γ → Action ⟨⟩
⟦ ActSend p a A ⟧ₜ i = ActSend (dataC (⟦ p ⟧d i)) (agentC (⟦ a ⟧ᵢ i)) (agentsS (⟦ A ⟧ₛ i))

⟦_⟧ₜ·_ : {Γ : Ctxt} → Action Γ → Model Γ → Action ⟨⟩
⟦ a ⟧ₜ· m = ⟦ a ⟧ₜ (Model.subΓ m)

⟦_⟧ₑ_ : {Γ : Ctxt} → Event Γ → Sub Γ → Event ⟨⟩
⟦ EvtReceive p a b ⟧ₑ i = EvtReceive (dataC (⟦ p ⟧d i)) (agentC (⟦ a ⟧ᵢ i)) (agentC (⟦ b ⟧ᵢ i))
⟦ EvtInternal a d ⟧ₑ i = EvtInternal (agentC (⟦ a ⟧ᵢ i)) (dataC (⟦ d ⟧d i))

⟦_⟧ₑ·_ : {Γ : Ctxt} → Event Γ → Model Γ → Event ⟨⟩
⟦ a ⟧ₑ· m = ⟦ a ⟧ₑ (Model.subΓ m)

⟦_⟧f_ : {Γ : Ctxt} → Fault Γ → Sub Γ → Fault ⟨⟩
⟦ FaultCorrect a b ⟧f i = FaultCorrect (agentC (⟦ a ⟧ᵢ i)) (agentC (⟦ b ⟧ᵢ i))

⟦_⟧f·_ : {Γ : Ctxt} → Fault Γ → Model Γ → Fault ⟨⟩
⟦ a ⟧f· m = ⟦ a ⟧f (Model.subΓ m)

⟦_⟧ₐ_ : {Γ : Ctxt} → Atom Γ → Sub Γ → atom
⟦ atProp    x ⟧ₐ i = atProp (atomPropC (⟦ x ⟧ₚ i))
⟦ atAction  x ⟧ₐ i = atAction (⟦ x ⟧ₜ i)
⟦ atEvent   x ⟧ₐ i = atEvent (⟦ x ⟧ₑ i)
⟦ atCorrect x ⟧ₐ i = atCorrect (⟦ x ⟧f i)

⟦_⟧ₐ·_ : {Γ : Ctxt} → Atom Γ → Model Γ → atom
⟦ a ⟧ₐ· m = ⟦ a ⟧ₐ (Model.subΓ m)

_≤ₜ_ : {Γ : Ctxt} → Model Γ → 𝕎 → Set
m ≤ₜ t = Model.w m ≼ t

_≥ₜ_ : {Γ : Ctxt} → Model Γ → 𝕎 → Set
m ≥ₜ t = t ≼ Model.w m

--𝕟 : { Γ : Ctxt } → Model Γ → Model Γ
--𝕟 m  = (m ≔ₜ 𝕤 (Model.w m))

--𝕓 : { Γ : Ctxt } → Model Γ → Model Γ
--𝕓 m  = (m ≔ₜ 𝕡 (Model.w m))

𝕧₀ : {Γ : Ctxt} {v : 𝕍} → ∈Ctxt v (Γ ، v)
𝕧₀ {Γ} {𝕧} = ∈Ctxt0 Γ

⟦_⟧ᶜ : Comparison → 𝕎 → 𝕎 → Set
⟦ LE ⟧ᶜ x₁ x₂ = x₁ ≼ x₂
⟦ LT ⟧ᶜ x₁ x₂ = x₁ ≺ x₂
⟦ EQ ⟧ᶜ x₁ x₂ = x₁ ≡ x₂
⟦ PR ⟧ᶜ x₁ x₂ = x₁ ◃ x₂

{--
len : {Γ : Ctxt} → Agents Γ → ℕ
len A = 0
--}
_⊨A_ : {Γ : Ctxt} → Model Γ → SetAtom Γ → Set
m ⊨A (a ∈ₐ A) = (⟦ a ⟧ᵢ· m) ∈ (⟦ A ⟧ₛ· m)
--m ⊨ (d ∈ᵢ D) = Lift _ (D (⟦ d ⟧d· m))
--m ⊨ (⟨ d ، e ⟩∈ᵣ D) =  Lift _ (D (⟦ d ⟧d· m) (⟦ e ⟧d· m))
m ⊨A (∣ A ∣ₛ＝ n) = length (⟦ A ⟧ₛ· m) ≡ n


_⊨_ : {Γ : Ctxt} → Model Γ → Form Γ → Set₁
-- Propositional
m ⊨ 𝕒 p = Model.interp m (Model.run m (Model.w m)) (⟦ p ⟧ₐ· m)
m ⊨ var x = Lift _ ⊥ --Model.vars m x
m ⊨ ⊤· = Lift _ ⊤
m ⊨ ⊥· = Lift _ ⊥
m ⊨ (f ∧· f₁) = (m ⊨ f) × (m ⊨ f₁)
m ⊨ (f ∨· f₁) = (m ⊨ f) ⊎ (m ⊨ f₁)
m ⊨ (f →· f₁) = (m ⊨ f) → (m ⊨ f₁)
--m ⊨ (¬· f) =  ¬ (m ⊨ f)
-- Predicate
m ⊨ ∀· u f = (v : ⟦𝕌⟧ u {--C⟦𝕌⟧ Γ u--}) → (m ≔ v) ⊨ f
m ⊨ ∃· u f = Σ (⟦𝕌⟧ u) (λ v → (m ≔ v) ⊨ f)
m ⊨ 𝔸 A = Lift _ (m ⊨A A)
-- Temporal
m ⊨ (f Ｕ f₁) =  ∃ (λ t → m ≤ₜ t × (m ≔ₜ t) ⊨ f₁ × ((t′ : 𝕎) → m ≤ₜ t′ → t′ ≺ t → ( (m  ≔ₜ t′) ⊨ f)))
m ⊨ Ｏ f = ∃ λ t →  Model.w m ◃ t × (m ≔ₜ t) ⊨ f
m ⊨ (f Ｓ f₁) =  ∃ (λ t → m ≥ₜ t × (m ≔ₜ t) ⊨ f₁ × ((t′ : 𝕎) → t ≺ t′ → m ≥ₜ t′ → ( (m  ≔ₜ t′) ⊨ f)))
m ⊨ Ｙ f =  ∃ λ t → t ◃ Model.w m × (m ≔ₜ t) ⊨ f
m ⊨ Ｂ f =  (t : 𝕎) → t ◃ Model.w m → (m ≔ₜ t) ⊨ f
m ⊨ (Ｆ f) = (m ≔ Model.w m) ⊨ f
m ⊨ (r₁ ⟨ c ⟩ r₂) = Lift _ (⟦ c ⟧ᶜ (⟦ r₁ ⟧ᵣ· m) (⟦ r₂ ⟧ᵣ· m))

{--
m ⊨ (_⊑_ {Γ} {ℝWorld} v c) = Lift _ (Model.w m ≼ c · lower (app-sub v (Model.subΓ m)))
m ⊨ (_⊏_ {Γ} {ℝWorld} v c) = Lift _ (𝕤 (Model.w m) ≼ c · lower (app-sub v (Model.subΓ m)))
m ⊨ (_⊒_ {Γ} {ℝWorld} v c) = Lift _ ((c · lower (app-sub v (Model.subΓ m))) ≼ Model.w m)
m ⊨ (_⊐_ {Γ} {ℝWorld} v c) = Lift _ (𝕤 (c · lower (app-sub v (Model.subΓ m))) ≼ Model.w m)
m ⊨ (_＝_ {Γ} {ℝWorld} v c) = Lift _ (Model.w m ≡ (c · lower (app-sub v (Model.subΓ m))))
--}


-- RULES

-- Intervals
data Interval (Γ : Ctxt) : Set where
  ［_,_］ : Res Γ → Res Γ → Interval Γ
  ［_,_） : Res Γ → Res Γ → Interval Γ
  （_,_］ : Res Γ → Res Γ → Interval Γ
  （_,_） : Res Γ → Res Γ → Interval Γ

-- Context extension annotation
data CE (Γ : Ctxt) : Set where
  -- context extension with a labeled hypothesis
  CEr  : Res Γ → CE Γ
  -- context extension with an unlabeled hypothesis
  CEu  : CE Γ
  -- context extension with a hypothesis labeled with an interval
  CEi  : Interval Γ → CE Γ

-- Contexts
data ℂ (Γ : Ctxt) : Set₂
ℂtxt : {Γ : Ctxt} → ℂ Γ → Ctxt

data ℂ Γ where
  -- empty context
  ℂ⟨⟩ : ℂ Γ
  -- context extension with an annotated hypothesis
  ℂx  : (c : ℂ Γ) (f : Form (ℂtxt c)) (a : CE (ℂtxt c)) → ℂ Γ
  -- context extension with a variable
  ℂv  : (c : ℂ Γ) (v : 𝕍) → ℂ Γ

ℂtxt {Γ} ℂ⟨⟩        = Γ
ℂtxt {Γ} (ℂx c f a) = ℂtxt {Γ} c
ℂtxt {Γ} (ℂv c u)   = ℂtxt {Γ} c ، u

ℂ₀ : Set₂
ℂ₀ = ℂ ⟨⟩

-- context extension with a labeled hypothesis
ℂe  : {Γ : Ctxt} (c : ℂ Γ) → Form (ℂtxt c) → Res (ℂtxt c) → ℂ Γ
ℂe c f r = ℂx c f (CEr r)

-- context extension with an unlabeled hypothesis
ℂu  : {Γ : Ctxt} (c : ℂ Γ) → Form (ℂtxt c) → ℂ Γ
ℂu c f = ℂx c f CEu

-- context extension with a hypothesis labeled with an interval
ℂi  : {Γ : Ctxt} (c : ℂ Γ) → Form (ℂtxt c) → Interval (ℂtxt c) → ℂ Γ
ℂi c f i = ℂx c f (CEi i)

ℂℂ : {Γ : Ctxt} (c : ℂ Γ) → Set₂
ℂℂ c = ℂ (ℂtxt c)

ℂCE : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂCE c = CE (ℂtxt c)

ℂRes : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂRes c = Res (ℂtxt c)

ℂData : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂData c = Data (ℂtxt c)

ℂInterval : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂInterval c = Interval (ℂtxt c)

ℂForm : {Γ : Ctxt} (c : ℂ Γ) → Set₁
ℂForm c = Form (ℂtxt c)

ℂModel : {Γ : Ctxt} (c : ℂ Γ) → Set₂
ℂModel c = Model (ℂtxt c)

ℂSub : {Γ : Ctxt} (c : ℂ Γ) → Set₁
ℂSub c = Sub (ℂtxt c)

ℂAgent : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂAgent c = Agent (ℂtxt c)

ℂAgents : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂAgents c = Agents (ℂtxt c)

ℂAtomProp : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂAtomProp c = AtomProp (ℂtxt c)

ℂ⟦𝕌⟧ : {Γ : Ctxt} (c : ℂ Γ) → 𝕌 → Set
ℂ⟦𝕌⟧ c u = C⟦𝕌⟧ (ℂtxt c) u

ℂ⟦ℝ⟧ : {Γ : Ctxt} (c : ℂ Γ) → Set
ℂ⟦ℝ⟧ c = C⟦ℝ⟧ (ℂtxt c)

Model₀ : Set₂
Model₀ = Model ⟨⟩

data Sequent : Set₂ where
  seq      : (Δ : ℂ₀) (T : ℂCE Δ) (C : ℂForm Δ) → Sequent
  nonEmpty : (Δ : ℂ₀) (R : ℂCE Δ) → Sequent

record Rule : Set₂ where
  constructor rule
  field
    Premises   : List Sequent
    Conclusion : Sequent

rseq : (Δ : ℂ₀) (r : ℂRes Δ) (φ : ℂForm Δ) → Sequent
rseq Δ r φ = seq Δ (CEr r) φ

useq : (Δ : ℂ₀) (φ : ℂForm Δ) → Sequent
useq Δ φ = seq Δ CEu φ

{--
_,_,_∈·_ : (c : ℂ) → Model (ℂtxt c) → ℂRes c → Interval (ℂtxt c) → Set
c , M , x ∈· ［ x₁ , x₂ ］ = {!!} ≼ {!!} × {!!} ≼ {!!}
c , M , x ∈· ［ x₁ , x₂ ） = {!!} ≼ {!!}  × {!!} ≼ 𝕡 {!!}
c , M , x ∈· （ x₁ , x₂ ］ = 𝕤 {!!} ≼ {!!} × {!!} ≼ {!!}
c , M , x ∈· （ x₁ , x₂ ） = 𝕤 {!!} ≼ {!!} × {!!} ≼ 𝕡 {!!}
--}

interval : {Γ : Ctxt} → Res Γ → Interval Γ →  Form Γ
interval {Γ} x ［ x₁ , x₂ ］ = (x₁ ⊑ x) ∧· (x ⊑ x₂)
interval {Γ} x ［ x₁ , x₂ ） = (x₁ ⊑ x) ∧· (x ⊏ x₂)
interval {Γ} x （ x₁ , x₂ ］ = (x₁ ⊏ x) ∧· (x ⊑ x₂)
interval {Γ} x （ x₁ , x₂ ） = (x₁ ⊏ x) ∧· (x ⊏ x₂)

inter-cond : {Γ : Ctxt} (M : Model Γ) (w : 𝕎) (i : Interval Γ) → Set
inter-cond {Γ} M w ［ x₁ , x₂ ］ = (⟦ x₁ ⟧ᵣ· M) ≼ w × w ≼ (⟦ x₂ ⟧ᵣ· M)
inter-cond {Γ} M w ［ x₁ , x₂ ） = (⟦ x₁ ⟧ᵣ· M) ≼ w × w ≺ (⟦ x₂ ⟧ᵣ· M)
inter-cond {Γ} M w （ x₁ , x₂ ］ = (⟦ x₁ ⟧ᵣ· M) ≺ w × w ≼ (⟦ x₂ ⟧ᵣ· M)
inter-cond {Γ} M w （ x₁ , x₂ ） = (⟦ x₁ ⟧ᵣ· M) ≺ w × w ≺ (⟦ x₂ ⟧ᵣ· M)

{--
sat-ctxt-annot-cond : {Γ : Ctxt} (r : Res Γ) (a : CE Γ) (M : Model Γ) → Set₁
sat-ctxt-annot-cond {Γ} r (CEr x) M = Lift _ (x ≡ r)
sat-ctxt-annot-cond {Γ} r CEu     M = Lift _ (⟦ r ⟧ᵣ· M ≡ Model.w M)
sat-ctxt-annot-cond {Γ} r (CEi i) M = M ⊨ (inter-cond r i)

sat-ctxt-annot′ : {Γ : Ctxt} (f : Form Γ) (a : CE Γ) (M : Model Γ) → Set₁
sat-ctxt-annot′ {Γ} f a M = (r : Res Γ) → sat-ctxt-annot-cond {Γ} r a M → (M ≔ₜ (⟦ r ⟧ᵣ· M)) ⊨ f
--}

-- We should be able to prove that sat-ctxt-annot and sat-ctxt-annot′ are equivalent
sat-ctxt-annot : {Γ : Ctxt} (f : Form Γ) (a : CE Γ) (M : Model Γ) → Set₁
sat-ctxt-annot {Γ} f (CEr r) M = (M ≔ₜ (⟦ r ⟧ᵣ· M)) ⊨ f
sat-ctxt-annot {Γ} f CEu     M = M ⊨ f
sat-ctxt-annot {Γ} f (CEi i) M = (w : 𝕎) → inter-cond M w i → (M ≔ₜ w) ⊨ f

sat-ctxt-annot∧·ₗ : {Γ : Ctxt} (A B : Form Γ) (a : CE Γ) (M : Model Γ)
                  → sat-ctxt-annot {Γ} (A ∧· B) a M
                  → sat-ctxt-annot {Γ} A a M
sat-ctxt-annot∧·ₗ {Γ} A B (CEr x) M (h , q) = h
sat-ctxt-annot∧·ₗ {Γ} A B CEu M (h , q) = h
sat-ctxt-annot∧·ₗ {Γ} A B (CEi x) M h r q with h r q
... | a , b = a

sat-ctxt-annot∧·ᵣ : {Γ : Ctxt} (A B : Form Γ) (a : CE Γ) (M : Model Γ)
                  → sat-ctxt-annot {Γ} (A ∧· B) a M
                  → sat-ctxt-annot {Γ} B a M
sat-ctxt-annot∧·ᵣ {Γ} A B (CEr x) M (h , q) = q
sat-ctxt-annot∧·ᵣ {Γ} A B CEu M (h , q) = q
sat-ctxt-annot∧·ᵣ {Γ} A B (CEi x) M h r q with h r q
... | a , b = b

sat-ctxt : {Γ : Ctxt} (c : ℂ Γ) (M : ℂModel c) → Set₁
sat-ctxt {Γ} ℂ⟨⟩        M = Lift _ ⊤
sat-ctxt {Γ} (ℂx c f a) M = sat-ctxt c M × sat-ctxt-annot f a M
sat-ctxt {Γ} (ℂv c u)   M = sat-ctxt c (Model،→ M)

isNonEmpty : {Γ : Ctxt} (M : Model Γ) (R : CE Γ) → Set
isNonEmpty M (CEr x) = ⊤
isNonEmpty M CEu = ⊤
isNonEmpty M (CEi x) = Σ 𝕎 (λ w → inter-cond M w x )

sat-sequent : (M : Model₀) (s : Sequent) → Set₁
sat-sequent M (seq Δ 𝕋 C) =
    (s : ℂSub Δ)
  → sat-ctxt Δ (M ≔ₛ s)
  → sat-ctxt-annot C 𝕋 (M ≔ₛ s)
sat-sequent M (nonEmpty Δ R) =
  (s : ℂSub Δ)
  → sat-ctxt Δ (M ≔ₛ s)
  → isNonEmpty (M ≔ₛ s) R

sat-sequents : (M : Model₀) (l : List Sequent) → Set₂
sat-sequents M [] = Lift _ ⊤
sat-sequents M (s ∷ l) = sat-sequent M s × sat-sequents M l

sat-rule : (M : Model₀) (r : Rule) → Set₂
sat-rule M (rule Premises Conclusion) = sat-sequents M Premises → sat-sequent M Conclusion

-- Weakening lemmas

{--
⟦⊆₀⟧ᵢ : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : Agent Γ)
      → ⟦ ↑ᵢ ⊆₀ a ⟧ᵢ (m ≔ v) ≡ ⟦ a ⟧ᵢ m
⟦⊆₀⟧ᵢ {Γ} m {u} v (agentV i) = refl
⟦⊆₀⟧ᵢ {Γ} m {u} v (agentC x) = refl

⟦⊆₀⟧ₛ : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : Agents Γ)
      → ⟦ ↑ₛ ⊆₀ a ⟧ₛ (m ≔ v) ≡ ⟦ a ⟧ₛ m
⟦⊆₀⟧ₛ {Γ} m {u} v (agentsV i) = refl
⟦⊆₀⟧ₛ {Γ} m {u} v (agentsL x) = E (λ a → {!!})
⟦⊆₀⟧ₛ {Γ} m {u} v (agentsS x) = refl

⟦⊆₀⟧ₚ : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : AtomProp Γ)
      → ⟦ ↑ₚ ⊆₀ a ⟧ₚ (m ≔ v) ≡ ⟦ a ⟧ₚ m
⟦⊆₀⟧ₚ {Γ} m {u} v (atomPropV i) = refl
⟦⊆₀⟧ₚ {Γ} m {u} v (atomPropC x) = refl

⟦⊆₀⟧ₜ : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : Action Γ)
      → ⟦ ↑ₜ ⊆₀ a ⟧ₜ (m ≔ v) ≡ ⟦ a ⟧ₜ m
⟦⊆₀⟧ₜ {Γ} m {u} v (ActSend p a A) =
  cong₃ (λ x y z → ActSend (atomPropC x) (agentC y) (agentsS z))
        (⟦⊆₀⟧ₚ m v p)
        (⟦⊆₀⟧ᵢ m v a)
        (⟦⊆₀⟧ₛ m v A)

⟦⊆₀⟧d : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : Data Γ)
      → ⟦ ↑d ⊆₀ a ⟧d (m ≔ v) ≡ ⟦ a ⟧d m
⟦⊆₀⟧d {Γ} m {u} v (dataV i) = refl
⟦⊆₀⟧d {Γ} m {u} v (dataC x) = refl

⟦⊆₀⟧ₑ : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : Event Γ)
      → ⟦ ↑ₑ ⊆₀ a ⟧ₑ (m ≔ v) ≡ ⟦ a ⟧ₑ m
⟦⊆₀⟧ₑ {Γ} m {u} v (EvtReceive p a b) =
  cong₃ (λ x y z → EvtReceive (atomPropC x) (agentC y) (agentC z))
        (⟦⊆₀⟧ₚ m v p)
        (⟦⊆₀⟧ᵢ m v a)
        (⟦⊆₀⟧ᵢ m v b)
⟦⊆₀⟧ₑ {Γ} m {u} v (EvtInternal a d) =
  cong₂ (λ x y → EvtInternal (agentC x) (dataC y))
        (⟦⊆₀⟧ᵢ m v a)
        (⟦⊆₀⟧d m v d)
⟦⊆₀⟧f : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : Fault Γ)
      → ⟦ ↑f ⊆₀ a ⟧f (m ≔ v) ≡ ⟦ a ⟧f m
⟦⊆₀⟧f {Γ} m {u} v (FaultCorrect a b) =
  cong₂ (λ x y → FaultCorrect (agentC x) (agentC y))
        (⟦⊆₀⟧ᵢ m v a)
        (⟦⊆₀⟧ᵢ m v b)

⟦⊆₀⟧ₐ : {Γ : Ctxt} (m : Model Γ) {u : 𝕌} (v : ⟦𝕌⟧ u) (a : Atom Γ)
      → ⟦ ↑ₐ ⊆₀ a ⟧ₐ (m ≔ v) ≡ ⟦ a ⟧ₐ m
⟦⊆₀⟧ₐ {Γ} m {u} v (atProp x) = cong (λ x → atProp (atomPropC x)) (⟦⊆₀⟧ₚ m v x)
⟦⊆₀⟧ₐ {Γ} m {u} v (atAction x) = cong atAction (⟦⊆₀⟧ₜ m v x)
⟦⊆₀⟧ₐ {Γ} m {u} v (atEvent x) = cong atEvent (⟦⊆₀⟧ₑ m v x)
⟦⊆₀⟧ₐ {Γ} m {u} v (atCorrect x) = cong atCorrect (⟦⊆₀⟧f m v x)
--}


⟦⊆⟧ᵢ : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Agent Γ)
     → ⟦ ↑ᵢ e a ⟧ᵢ s ≡ ⟦ a ⟧ᵢ m
⟦⊆⟧ᵢ {Γ} {Δ} m e s ⊆s (agentV i) = sym (app-sub-Sub⊆ i e m s ⊆s)
⟦⊆⟧ᵢ {Γ} {Δ} m e s ⊆s (agentC x) = refl

⟦⊆⟧ᵢl : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : List (Agent Γ))
     → Data.List.map (λ j → ⟦ j ⟧ᵢ s) (Data.List.map (↑ᵢ e) a)
     ≡ Data.List.map (λ j → ⟦ j ⟧ᵢ m) a
⟦⊆⟧ᵢl {Γ} {Δ} m e s ⊆s [] = refl
⟦⊆⟧ᵢl {Γ} {Δ} m e s ⊆s (x ∷ a) = cong₂ _∷_ (⟦⊆⟧ᵢ m e s ⊆s x) (⟦⊆⟧ᵢl m e s ⊆s a)

⟦⊆⟧ₛ : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Agents Γ)
     → ⟦ ↑ₛ e a ⟧ₛ s ≡ ⟦ a ⟧ₛ m
⟦⊆⟧ₛ {Γ} {Δ} m e s ⊆s (agentsV i) = sym (app-sub-Sub⊆ i e m s ⊆s)
⟦⊆⟧ₛ {Γ} {Δ} m e s ⊆s (agentsL x) = ⟦⊆⟧ᵢl m e s ⊆s x
--⟦⊆⟧ₛ {Γ} {Δ} m e s ⊆s (agentsS x) = refl

⟦⊆⟧ₚ : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : AtomProp Γ)
     → ⟦ ↑ₚ e a ⟧ₚ s ≡ ⟦ a ⟧ₚ m
⟦⊆⟧ₚ {Γ} {Δ} m e s ⊆s (atomPropV i) = sym (app-sub-Sub⊆ i e m s ⊆s)
⟦⊆⟧ₚ {Γ} {Δ} m e s ⊆s (atomPropC x) = refl

⟦⊆⟧d : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Data Γ)
     → ⟦ ↑d e a ⟧d s ≡ ⟦ a ⟧d m
⟦⊆⟧d {Γ} {Δ} m e s ⊆s (dataV i) = sym (app-sub-Sub⊆ i e m s ⊆s)
⟦⊆⟧d {Γ} {Δ} m e s ⊆s (dataC x) = refl

⟦⊆⟧ₜ : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Action Γ)
     → ⟦ ↑ₜ e a ⟧ₜ s ≡ ⟦ a ⟧ₜ m
⟦⊆⟧ₜ {Γ} {Δ} m e s ⊆s (ActSend p a A) =
  cong₃ (λ x y z → ActSend (dataC x) (agentC y) (agentsS z))
        (⟦⊆⟧d m e s ⊆s p)
        (⟦⊆⟧ᵢ m e s ⊆s a)
        (⟦⊆⟧ₛ m e s ⊆s A)

⟦⊆⟧ₑ : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Event Γ)
     → ⟦ ↑ₑ e a ⟧ₑ s ≡ ⟦ a ⟧ₑ m
⟦⊆⟧ₑ {Γ} {Δ} m e s ⊆s (EvtReceive p a b) =
  cong₃ (λ x y z → EvtReceive (dataC x) (agentC y) (agentC z))
        (⟦⊆⟧d m e s ⊆s p)
        (⟦⊆⟧ᵢ m e s ⊆s a)
        (⟦⊆⟧ᵢ m e s ⊆s b)
⟦⊆⟧ₑ {Γ} {Δ} m e s ⊆s (EvtInternal a d) =
  cong₂ (λ x y → EvtInternal (agentC x) (dataC y))
        (⟦⊆⟧ᵢ m e s ⊆s a)
        (⟦⊆⟧d m e s ⊆s d)

⟦⊆⟧f : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Fault Γ)
     → ⟦ ↑f e a ⟧f s ≡ ⟦ a ⟧f m
⟦⊆⟧f {Γ} {Δ} m e s ⊆s (FaultCorrect a b) =
  cong₂ (λ x y → FaultCorrect (agentC x) (agentC y))
        (⟦⊆⟧ᵢ m e s ⊆s a)
        (⟦⊆⟧ᵢ m e s ⊆s b)

⟦⊆⟧ₐ : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Atom Γ)
      → ⟦ ↑ₐ e a ⟧ₐ s ≡ ⟦ a ⟧ₐ m
⟦⊆⟧ₐ {Γ} {Δ} m e s ⊆s (atProp x) = cong (λ x → atProp (atomPropC x)) (⟦⊆⟧ₚ m e s ⊆s x)
⟦⊆⟧ₐ {Γ} {Δ} m e s ⊆s (atAction x) = cong atAction (⟦⊆⟧ₜ m e s ⊆s x)
⟦⊆⟧ₐ {Γ} {Δ} m e s ⊆s (atEvent x) = cong atEvent (⟦⊆⟧ₑ m e s ⊆s x)
⟦⊆⟧ₐ {Γ} {Δ} m e s ⊆s (atCorrect x) = cong atCorrect (⟦⊆⟧f m e s ⊆s x)

⟦⊆⟧ᵣ : {Γ Δ : Ctxt} (m : Sub Γ) (e : Γ ⊆ Δ) (s : Sub Δ) (⊆s : Sub⊆ e m s) (a : Res Γ)
     → ⟦ ↑ᵣ e a ⟧ᵣ s ≡ ⟦ a ⟧ᵣ m
⟦⊆⟧ᵣ {Γ} {Δ} m e s ⊆s (𝐯 i) = sym (app-sub-Sub⊆ i e m s ⊆s)
⟦⊆⟧ᵣ {Γ} {Δ} m e s ⊆s 𝟎 = refl
--⟦⊆⟧ᵣ {Γ} {Δ} m e s ⊆s (𝐬 a) = cong 𝕤 (⟦⊆⟧ᵣ m e s ⊆s a)
⟦⊆⟧ᵣ {Γ} {Δ} m e s ⊆s (a ⋆ a₁) = cong₂ _·_ (⟦⊆⟧ᵣ m e s ⊆s a) (⟦⊆⟧ᵣ m e s ⊆s a₁)
⟦⊆⟧ᵣ {Γ} {Δ} m e s ⊆s (rvar ρ) = refl

⊨A-↑⊆→ : {Γ Δ : Ctxt} {M : Model Γ} {a : SetAtom Γ} (s : Sub Δ)
         (e : Γ ⊆ Δ)
       → Sub⊆ e (Model.subΓ M) s
       → (M ≔ₛ s) ⊨A (↑A e a)
       → M ⊨A a
⊨A-↑⊆→ {Γ} {Δ} {m} {x ∈ₐ x₁} s e ⊆s h =
  subst₂ (λ x y → y ∈ x) (⟦⊆⟧ₛ (Model.subΓ m) e s ⊆s x₁) (⟦⊆⟧ᵢ (Model.subΓ m) e s ⊆s x) h
⊨A-↑⊆→ {Γ} {Δ} {m} {∣ A ∣ₛ＝ n} s e ⊆s h =
  trans (cong length (sym (⟦⊆⟧ₛ (Model.subΓ m) e s ⊆s A))) h

→⊨A-↑⊆ : {Γ Δ : Ctxt} {M : Model Γ} {a : SetAtom Γ} (s : Sub Δ)
         (e : Γ ⊆ Δ)
       → Sub⊆ e (Model.subΓ M) s
       → M ⊨A a
       → (M ≔ₛ s) ⊨A (↑A e a)
→⊨A-↑⊆ {Γ} {Δ} {m} {x ∈ₐ x₁} s e ⊆s h =
  subst₂ (λ x y → y ∈ x) (sym (⟦⊆⟧ₛ (Model.subΓ m) e s ⊆s x₁)) (sym (⟦⊆⟧ᵢ (Model.subΓ m) e s ⊆s x)) h
→⊨A-↑⊆ {Γ} {Δ} {m} {∣ A ∣ₛ＝ n} s e ⊆s h =
  trans (cong length (⟦⊆⟧ₛ (Model.subΓ m) e s ⊆s A)) h

mutual
  ⊨-↑⊆→ : {Γ Δ : Ctxt} {M : Model Γ} {F : Form Γ} (s : Sub Δ)
          (e : Γ ⊆ Δ)
        → Sub⊆ e (Model.subΓ M) s
        → (M ≔ₛ s) ⊨ (↑ e F)
        → M ⊨ F
  ⊨-↑⊆→ {Γ} {Δ} {m} {𝕒 x} s e ⊆s h =
    subst (Model.interp m (Model.run m (Model.w m)))
          (⟦⊆⟧ₐ (Model.subΓ m) e s ⊆s x)
          h
  ⊨-↑⊆→ {Γ} {Δ} {m} {var x} s e ⊆s h = h
  ⊨-↑⊆→ {Γ} {Δ} {m} {⊤·} s e ⊆s h = h
  ⊨-↑⊆→ {Γ} {Δ} {m} {⊥·} s e ⊆s h = h
  ⊨-↑⊆→ {Γ} {Δ} {m} {F ∧· F₁} s e ⊆s (h , q) =
    ⊨-↑⊆→ {Γ} {Δ} {m} {F}  s e ⊆s h ,
    ⊨-↑⊆→ {Γ} {Δ} {m} {F₁} s e ⊆s q
  ⊨-↑⊆→ {Γ} {Δ} {m} {F ∨· F₁} s e ⊆s (inj₁ h) = inj₁ (⊨-↑⊆→ {Γ} {Δ} {m} {F}  s e ⊆s h)
  ⊨-↑⊆→ {Γ} {Δ} {m} {F ∨· F₁} s e ⊆s (inj₂ h) = inj₂ (⊨-↑⊆→ {Γ} {Δ} {m} {F₁} s e ⊆s h)
  ⊨-↑⊆→ {Γ} {Δ} {m} {F →· F₁} s e ⊆s h q =
    ⊨-↑⊆→ {Γ} {Δ} {m} {F₁} s e ⊆s (h (→⊨-↑⊆ {Γ} {Δ} {m} {F} s e ⊆s q))
--  ⊨-↑⊆→ {Γ} {Δ} {m} {¬· F} s e ⊆s h q = h (→⊨-↑⊆ {Γ} {Δ} {m} {F} s e ⊆s q)
  ⊨-↑⊆→ {Γ} {Δ} {m} {∀· u F} s e ⊆s h w =
    ⊨-↑⊆→ {Γ ، 𝕍𝕌 u} {Δ ، 𝕍𝕌 u} {m ≔ w} {F}
          (s ⹁ 𝕍𝕌 u ∶ w) (⊆، (𝕍𝕌 u) e) (Sub⊆-⊆، ⊆s) (h w)
  ⊨-↑⊆→ {Γ} {Δ} {m} {∃· u F} s e ⊆s (v , h) =
    v ,
    ⊨-↑⊆→ {Γ ، 𝕍𝕌 u} {Δ ، 𝕍𝕌 u} {m ≔ v} {F} (s ⹁ 𝕍𝕌 u ∶ v) (⊆، (𝕍𝕌 u) e)
          (Sub⊆-⊆، ⊆s)
          h
  ⊨-↑⊆→ {Γ} {Δ} {m} {𝔸 A} s e ⊆s (lift h) =
    lift (⊨A-↑⊆→ {Γ} {Δ} {m} {A} (s) e ⊆s h)
--  ⊨-↑⊆→ {Γ} {Δ} {m} {x ∈ᵢ x₁} s e ⊆s (lift h) =
--    lift (subst x₁ (⟦⊆⟧d (Model.subΓ m) e s ⊆s x) h)
--  ⊨-↑⊆→ {Γ} {Δ} {m} {⟨ x ، x₁ ⟩∈ᵣ x₂} s e ⊆s (lift h) =
--    lift (subst₂ x₂ (⟦⊆⟧d (Model.subΓ m) e s ⊆s x) (⟦⊆⟧d (Model.subΓ m) e s ⊆s x₁) h)
  ⊨-↑⊆→ {Γ} {Δ} {m} {f Ｕ f₁} s e ⊆s (t , c₁ , c₂ , c₃) =
    t , c₁ ,
    ⊨-↑⊆→ {Γ} {Δ} {m ≔ₜ t} {f₁} s e ⊆s c₂ , 𝕚
    where
    𝕚 : (t′ : 𝕎) → m ≤ₜ t′ → t′ ≺ t → (m ≔ₜ t′) ⊨ f
    𝕚 t′ h₁ h₂ = ⊨-↑⊆→ {Γ} {Δ} {m ≔ₜ t′} {f} s e ⊆s (c₃ t′ h₁ h₂)
  ⊨-↑⊆→ {Γ} {Δ} {m} {Ｏ f} s e ⊆s (t , c₁ , c₂) =
    t , c₁ , ⊨-↑⊆→ {Γ} {Δ} {m ≔ₜ t} {f} s e ⊆s c₂
  ⊨-↑⊆→ {Γ} {Δ} {m} {f Ｓ f₁} s e ⊆s (t , c₁ , c₂ , c₃) =
    t , c₁ ,
    ⊨-↑⊆→ {Γ} {Δ} {m ≔ₜ t} {f₁} s e ⊆s c₂ , 𝕚
    where
    𝕚 : (t′ : 𝕎) → t ≺ t′ → m ≥ₜ t′ → (m ≔ₜ t′) ⊨ f
    𝕚 t′ h₁ h₂ = ⊨-↑⊆→ {Γ} {Δ} {m ≔ₜ t′} {f} s e ⊆s (c₃ t′ h₁ h₂)
  ⊨-↑⊆→ {Γ} {Δ} {m} {Ｙ f} s e ⊆s (t , c₁ , c₂) =
    t , c₁ , ⊨-↑⊆→ {Γ} {Δ} {m ≔ₜ t} {f} s e ⊆s c₂
  ⊨-↑⊆→ {Γ} {Δ} {m} {Ｂ f} s e ⊆s h w q =
    ⊨-↑⊆→ {Γ} {Δ} {m ≔ₜ w} {f} s e ⊆s (h w q)
  ⊨-↑⊆→ {Γ} {Δ} {m} {Ｆ f} s e ⊆s h =
    ⊨-↑⊆→ {Γ ، 𝕍ℝ} {Δ ، 𝕍ℝ} {m ≔ Model.w m} {f}
          (s ⹁ 𝕍ℝ ∶ Model.w m)
          (⊆، 𝕍ℝ e)
          (Sub⊆-⊆، ⊆s)
          h
  ⊨-↑⊆→ {Γ} {Δ} {m} {r₁ ⟨ c ⟩ r₂} s e ⊆s (lift h) =
    lift (subst₂ ⟦ c ⟧ᶜ
                 (⟦⊆⟧ᵣ (Model.subΓ m) e s ⊆s r₁)
                 (⟦⊆⟧ᵣ (Model.subΓ m) e s ⊆s r₂)
                 h)

  →⊨-↑⊆ : {Γ Δ : Ctxt} {M : Model Γ} {F : Form Γ} (s : Sub Δ)
          (e : Γ ⊆ Δ)
        → Sub⊆ e (Model.subΓ M) s
        → M ⊨ F
        → (M ≔ₛ s) ⊨ (↑ e F)
  →⊨-↑⊆ {Γ} {Δ} {m} {𝕒 x} s e ⊆s h =
    subst (Model.interp m (Model.run m (Model.w m)))
          (sym (⟦⊆⟧ₐ (Model.subΓ m) e s ⊆s x))
          h
  →⊨-↑⊆ {Γ} {Δ} {m} {var x} s e ⊆s h = h
  →⊨-↑⊆ {Γ} {Δ} {m} {⊤·} s e ⊆s h = h
  →⊨-↑⊆ {Γ} {Δ} {m} {⊥·} s e ⊆s h = h
  →⊨-↑⊆ {Γ} {Δ} {m} {F ∧· F₁} s e ⊆s (h , q) =
    →⊨-↑⊆ {Γ} {Δ} {m} {F}  s e ⊆s h ,
    →⊨-↑⊆ {Γ} {Δ} {m} {F₁} s e ⊆s q
  →⊨-↑⊆ {Γ} {Δ} {m} {F ∨· F₁} s e ⊆s (inj₁ h) =
    inj₁ (→⊨-↑⊆ {Γ} {Δ} {m} {F}  s e ⊆s h)
  →⊨-↑⊆ {Γ} {Δ} {m} {F ∨· F₁} s e ⊆s (inj₂ h) =
    inj₂ (→⊨-↑⊆ {Γ} {Δ} {m} {F₁} s e ⊆s h)
  →⊨-↑⊆ {Γ} {Δ} {m} {F →· F₁} s e ⊆s h q =
    →⊨-↑⊆ {Γ} {Δ} {m} {F₁} s e ⊆s (h (⊨-↑⊆→ {Γ} {Δ} {m} {F} s e ⊆s q))
--  →⊨-↑⊆ {Γ} {Δ} {m} {¬· F} s e ⊆s h q =
--    h (⊨-↑⊆→ {Γ} {Δ} {m} {F} s e ⊆s q)
  →⊨-↑⊆ {Γ} {Δ} {m} {∀· u F} s e ⊆s h w =
    →⊨-↑⊆ {Γ ، 𝕍𝕌 u} {Δ ، 𝕍𝕌 u} {m ≔ w} {F} (s ⹁ 𝕍𝕌 u ∶ w) (⊆، (𝕍𝕌 u) e)
          (Sub⊆-⊆، ⊆s)
          (h w)
  →⊨-↑⊆ {Γ} {Δ} {m} {∃· u F} s e ⊆s (v , h) =
    v ,
    →⊨-↑⊆ {Γ ، 𝕍𝕌 u} {Δ ، 𝕍𝕌 u} {m ≔ v} {F} (s ⹁ 𝕍𝕌 u ∶ v) (⊆، (𝕍𝕌 u) e)
          (Sub⊆-⊆، ⊆s)
          h
  →⊨-↑⊆ {Γ} {Δ} {m} {𝔸 A} s e ⊆s (lift h) =
    lift (→⊨A-↑⊆ {Γ} {Δ} {m} {A} s e ⊆s h)
--  →⊨-↑⊆ {Γ} {Δ} {m} {x ∈ᵢ x₁} s e ⊆s (lift h) =
--    lift (subst x₁ (sym (⟦⊆⟧d (Model.subΓ m) e s ⊆s x)) h)
--  →⊨-↑⊆ {Γ} {Δ} {m} {⟨ x ، x₁ ⟩∈ᵣ x₂} s e ⊆s (lift h) =
--    lift (subst₂ x₂ (sym (⟦⊆⟧d (Model.subΓ m) e s ⊆s x)) (sym (⟦⊆⟧d (Model.subΓ m) e s ⊆s x₁)) h)
  →⊨-↑⊆ {Γ} {Δ} {m} {f Ｕ f₁} s e ⊆s (t , c₁ , c₂ , c₃) =
    t , c₁ ,
    →⊨-↑⊆ {Γ} {Δ} {m ≔ₜ t} {f₁} s e ⊆s c₂ , 𝕚
    where
    𝕚 : (t′ : 𝕎) → (m ≔ₛ s) ≤ₜ t′ → t′ ≺ t → ((m ≔ₛ s) ≔ₜ t′) ⊨ ↑ e f
    𝕚 t′ h₁ h₂ = →⊨-↑⊆ {Γ} {Δ} {m ≔ₜ t′} {f} s e ⊆s (c₃ t′ h₁ h₂)
  →⊨-↑⊆ {Γ} {Δ} {m} {Ｏ f} s e ⊆s (t , c₁ , c₂) =
    t , c₁ , →⊨-↑⊆ {Γ} {Δ} {m ≔ₜ t} {f} s e ⊆s c₂
  →⊨-↑⊆ {Γ} {Δ} {m} {f Ｓ f₁} s e ⊆s (t , c₁ , c₂ , c₃) =
    t , c₁ ,
    →⊨-↑⊆ {Γ} {Δ} {m ≔ₜ t} {f₁} s e ⊆s c₂ , 𝕚
    where
    𝕚 : (t′ : 𝕎) → t ≺ t′ → (m ≔ₛ s) ≥ₜ t′ → ((m ≔ₛ s) ≔ₜ t′) ⊨ ↑ e f
    𝕚 t′ h₁ h₂ = →⊨-↑⊆ {Γ} {Δ} {m ≔ₜ t′} {f} s e ⊆s (c₃ t′ h₁ h₂)
  →⊨-↑⊆ {Γ} {Δ} {m} {Ｙ f} s e ⊆s (t , c₁ , c₂) =
    t , c₁ , →⊨-↑⊆ {Γ} {Δ} {m ≔ₜ t} {f} s e ⊆s c₂
  →⊨-↑⊆ {Γ} {Δ} {m} {Ｂ f} s e ⊆s h w q =
    →⊨-↑⊆ {Γ} {Δ} {m ≔ₜ w} {f} s e ⊆s (h w q)
  →⊨-↑⊆ {Γ} {Δ} {m} {Ｆ f} s e ⊆s h =
    →⊨-↑⊆ {Γ ، 𝕍ℝ} {Δ ، 𝕍ℝ} {m ≔ Model.w m} {f}
          (s ⹁ 𝕍ℝ ∶ Model.w m)
          (⊆، 𝕍ℝ e)
          (Sub⊆-⊆، ⊆s)
          h
  →⊨-↑⊆ {Γ} {Δ} {m} {r₁ ⟨ c ⟩ r₂} s e ⊆s (lift h) =
    lift (subst₂ ⟦ c ⟧ᶜ
                 (sym (⟦⊆⟧ᵣ (Model.subΓ m) e s ⊆s r₁))
                 (sym (⟦⊆⟧ᵣ (Model.subΓ m) e s ⊆s r₂))
                 h)

⊨-↑₀→ : {Γ : Ctxt} {M : Model Γ} {F : Form Γ} {u : 𝕍} (v : ⟦𝕍⟧ u)
      → (M ≔ v) ⊨ (↑₀ F)
      → M ⊨ F
⊨-↑₀→ {Γ} {m} {F} {u} v h =
  ⊨-↑⊆→ {Γ} {Γ ، u} {m} {F} ((Model.subΓ m) ⹁ u ∶ v) ⊆₀ Sub⊆-⊆₀ h

→⊨-↑₀ : {Γ : Ctxt} {M : Model Γ} {F : Form Γ} {u : 𝕍} (v : ⟦𝕍⟧ u)
      → M ⊨ F
      → (M ≔ v) ⊨ (↑₀ F)
→⊨-↑₀ {Γ} {m} {F} {u} v h =
  →⊨-↑⊆ {Γ} {Γ ، u} {m} {F} ((Model.subΓ m) ⹁ u ∶ v) ⊆₀ Sub⊆-⊆₀ h

⊨-↑₁→ : {Γ : Ctxt} {M : Model Γ} {F : Form Γ}
        {u₁ : 𝕍} (v₁ : ⟦𝕍⟧ u₁)
        {u₂ : 𝕍} (v₂ : ⟦𝕍⟧ u₂)
      → ((M ≔ v₁) ≔ v₂) ⊨ (↑₁ F)
      → M ⊨ F
⊨-↑₁→ {Γ} {m} {F} {u₁} v₁ {u₂} v₂ h =
  ⊨-↑⊆→ {Γ} {Γ ، u₁ ، u₂} {m} {F} (((Model.subΓ m) ⹁ u₁ ∶ v₁) ⹁ u₂ ∶ v₂) ⊆₁ Sub⊆-⊆₁ h

→⊨-↑₁ : {Γ : Ctxt} {M : Model Γ} {F : Form Γ}
        {u₁ : 𝕍} (v₁ : ⟦𝕍⟧ u₁)
        {u₂ : 𝕍} (v₂ : ⟦𝕍⟧ u₂)
      → M ⊨ F
      → ((M ≔ v₁) ≔ v₂) ⊨ (↑₁ F)
→⊨-↑₁ {Γ} {m} {F} {u₁} v₁ {u₂} v₂ h =
  →⊨-↑⊆ {Γ} {Γ ، u₁ ، u₂} {m} {F} (((Model.subΓ m) ⹁ u₁ ∶ v₁) ⹁ u₂ ∶ v₂) ⊆₁ Sub⊆-⊆₁ h

≡→⊨ : {Γ : Ctxt} {M₁ M₂ : Model Γ} {F : Form Γ}
    → M₁ ≡ M₂
    → M₁ ⊨ F
    → M₂ ⊨ F
≡→⊨ {Γ} {M₁} {M₂} {F} M≡ ⊨F
  rewrite M≡
  = ⊨F

≔-≔ₜ : {Γ : Ctxt} (M : Model Γ) {u : 𝕍} (v : ⟦𝕍⟧ u) (w : 𝕎)
     → ((_≔_ M {u} v) ≔ₜ w) ≡ ((M ≔ₜ w) ≔ v)
≔-≔ₜ {Γ} (model interp run w₁ sub) {u} v w = refl

⊨⊨ₜ-↑₀→ : {Γ : Ctxt} {M : Model Γ} {F : Form Γ} {u : 𝕍} (v : ⟦𝕍⟧ u) (t : 𝕎)
        → ((M ≔ v) ≔ₜ t) ⊨ (↑₀ F)
        → (M ≔ₜ t) ⊨ F
⊨⊨ₜ-↑₀→ {Γ} {M} {F} {u} v t h =
  ⊨-↑₀→ {Γ} {M ≔ₜ t} {F} {u} v (≡→⊨ {F = ↑ ⊆₀ F} (≔-≔ₜ {Γ} M {u} v t) h)

→⊨⊨ₜ-↑₀ : {Γ : Ctxt} {M : Model Γ} {F : Form Γ} {u : 𝕍} (v : ⟦𝕍⟧ u) (t : 𝕎)
        → (M ≔ₜ t) ⊨ F
        → ((M ≔ v) ≔ₜ t) ⊨ (↑₀ F)
→⊨⊨ₜ-↑₀ {Γ} {M} {F} {u} v t h =
  →⊨-↑₀ {Γ} {M ≔ₜ t} {F} {u} v h

⟦↑ᵣ₀⟧ᵣ : {Γ : Ctxt} (r : Res Γ) (s : Sub Γ) (u : 𝕍) (v : ⟦𝕍⟧ u)
       → (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ u ∶ v)) ≡ (⟦ r ⟧ᵣ s)
⟦↑ᵣ₀⟧ᵣ {Γ} r s u v = ⟦⊆⟧ᵣ s ⊆₀ (s ⹁ u ∶ v) Sub⊆-⊆₀ r

⟦↑ᵣ₁⟧ᵣ : {Γ : Ctxt} (r : Res Γ) (s : Sub Γ) (u : 𝕍) (v : ⟦𝕍⟧ u) (x : 𝕍) (y : ⟦𝕍⟧ x)
       → (⟦ ↑ᵣ₁ r ⟧ᵣ ((s ⹁ u ∶ v) ⹁ x ∶ y)) ≡ (⟦ r ⟧ᵣ s)
⟦↑ᵣ₁⟧ᵣ {Γ} r s u v x y = ⟦⊆⟧ᵣ s ⊆₁ ((s ⹁ u ∶ v) ⹁ x ∶ y) Sub⊆-⊆₁ r

⟦↑ᵣ₀⟧ᵣ𝕎 : {Γ : Ctxt} (r : Res Γ) (s : Sub Γ) (t : 𝕎)
        → (⟦ ↑ᵣ₀ r ⟧ᵣ (s ⹁ 𝕍ℝ ∶ t)) ≡ (⟦ r ⟧ᵣ s)
⟦↑ᵣ₀⟧ᵣ𝕎 {Γ} r s t = ⟦⊆⟧ᵣ s ⊆₀ (s ⹁ 𝕍ℝ ∶ t) Sub⊆-⊆₀ r

--
-- Substitution lemmas

𝕌⟦_⟧c : {u : 𝕌} {Δ : Ctxt} → C⟦𝕌⟧ Δ u → Sub Δ → ⟦𝕌⟧ u
𝕌⟦_⟧c {𝕌Agent}  {Δ} v s = ⟦ v ⟧ᵢ s
𝕌⟦_⟧c {𝕌Agents} {Δ} v s = ⟦ v ⟧ₛ s
𝕌⟦_⟧c {𝕌Prop}   {Δ} v s = ⟦ v ⟧ₚ s
𝕌⟦_⟧c {𝕌Data}   {Δ} v s = ⟦ v ⟧d s

ℝ⟦_⟧c : {Δ : Ctxt} → C⟦ℝ⟧ Δ → Sub Δ → ⟦ℝ⟧
ℝ⟦_⟧c {Δ} v s = ⟦ v ⟧ᵣ s

⟦_،_⟧c : (u : 𝕍) {Δ : Ctxt} → C⟦𝕍⟧ Δ u → Sub Δ → ⟦𝕍⟧ u
⟦_،_⟧c (𝕍𝕌 u) {Δ} v s = 𝕌⟦_⟧c {u} {Δ} v s
⟦_،_⟧c 𝕍ℝ {Δ} v s = ℝ⟦_⟧c {Δ} v s

⟦_،_⟧c· : (u : 𝕍) {Δ : Ctxt} → C⟦𝕍⟧ Δ u → Model Δ → ⟦𝕍⟧ u
⟦_،_⟧c· u {Δ} v m = ⟦_،_⟧c u {Δ} v (Model.subΓ m)

_≔=_ : {Δ Γ : Ctxt} → Model Γ → Sub Δ → Model (Γ ＋ Δ)
_≔=_ {.⟨⟩} {Γ} m ● = m
_≔=_ {.(_ ، u)} {Γ} m (s ⹁ u ∶ v) = (m ≔= s) ≔ v

sub≔= : {Γ Δ : Ctxt} (m : Model Γ) (s : Sub Δ)
      → Model.subΓ (m ≔= s)
      ≡ Model.subΓ m ＋ₛ s
sub≔= {Γ} {.⟨⟩} m ● = refl
sub≔= {Γ} {.(_ ، u)} m@(model interp run w sub₁) (s ⹁ u ∶ v) =
  cong (λ x → x ⹁ u ∶ v) (sub≔= m s)

＋→sub-agent-var : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                   (v : C⟦𝕍⟧ Γ u)
                   (i : ∈Ctxt (𝕍𝕌 𝕌Agent) ((Γ ، u) ＋ Δ))
                 → ⟦ CSub،＋ v i ⟧ᵢ (m ＋ₛ s)
                 ≡ app-sub i ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-agent-var {Γ} {⟨⟩} {.(𝕍𝕌 𝕌Agent)} m ● v (∈Ctxt0 .Γ) = refl
＋→sub-agent-var {Γ} {⟨⟩} {u} m ● v (∈CtxtS .u i) = refl
＋→sub-agent-var {Γ} {Δ ، .(𝕍𝕌 𝕌Agent)} {u} m (s ⹁ .(𝕍𝕌 𝕌Agent) ∶ v₁) v (∈Ctxt0 .((Γ ، u) ＋ Δ)) = refl
＋→sub-agent-var {Γ} {Δ ، U} {u} m (s ⹁ .U ∶ v₁) v (∈CtxtS .U i) =
  trans (⟦⊆⟧ᵢ (m ＋ₛ s) ⊆₀ ((m ＋ₛ s) ⹁ U ∶ v₁) Sub⊆-⊆₀ (CSub،＋ v i))
        (＋→sub-agent-var m s v i)

＋→sub-agent : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
               (v : C⟦𝕍⟧ Γ u)
               (x : Agent ((Γ ، u) ＋ Δ))
             → ⟦ sub-Agent x (CSub،＋ v) ⟧ᵢ (m ＋ₛ s)
             ≡ ⟦ x ⟧ᵢ ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-agent {Γ} {Δ} {u} m s v (agentV i) = ＋→sub-agent-var m s v i
＋→sub-agent {Γ} {Δ} {u} m s v (agentC x) = refl

≔→sub-agent : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
              (v : C⟦𝕍⟧ Γ u)
              (x : Agent ((Γ ، u) ＋ Δ))
            → ⟦ sub-Agent x (CSub،＋ v) ⟧ᵢ· (m ≔= s)
            ≡ ⟦ x ⟧ᵢ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-agent {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-Agent x (CSub،＋ v) ⟧ᵢ z) (sub≔= m s))
        (trans (＋→sub-agent (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧ᵢ z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

＋→sub-agentL : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                (v : C⟦𝕍⟧ Γ u)
                (x : List (Agent ((Γ ، u) ＋ Δ)))
              → Data.List.map (λ j → ⟦ j ⟧ᵢ (m ＋ₛ s)) (Data.List.map (λ j → sub-Agent j (CSub،＋ v)) x)
              ≡ Data.List.map (λ j → ⟦ j ⟧ᵢ ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)) x
＋→sub-agentL {Γ} {Δ} {u} m s v [] = refl
＋→sub-agentL {Γ} {Δ} {u} m s v (x ∷ x₁) = cong₂ _∷_ (＋→sub-agent m s v x) (＋→sub-agentL m s v x₁)

＋→sub-agents-var : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                    (v : C⟦𝕍⟧ Γ u)
                    (i : ∈Ctxt (𝕍𝕌 𝕌Agents) ((Γ ، u) ＋ Δ))
                  → ⟦ CSub،＋ v i ⟧ₛ (m ＋ₛ s)
                  ≡ app-sub i ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-agents-var {Γ} {⟨⟩} {.(𝕍𝕌 𝕌Agents)} m ● v (∈Ctxt0 .Γ) = refl
＋→sub-agents-var {Γ} {⟨⟩} {u} m ● v (∈CtxtS .u i) = refl
＋→sub-agents-var {Γ} {Δ ، .(𝕍𝕌 𝕌Agents)} {u} m (s ⹁ .(𝕍𝕌 𝕌Agents) ∶ v₁) v (∈Ctxt0 .((Γ ، u) ＋ Δ)) = refl
＋→sub-agents-var {Γ} {Δ ، U} {u} m (s ⹁ .U ∶ v₁) v (∈CtxtS .U i) =
  trans (⟦⊆⟧ₛ (m ＋ₛ s) ⊆₀ ((m ＋ₛ s) ⹁ U ∶ v₁) Sub⊆-⊆₀ (CSub،＋ v i))
        (＋→sub-agents-var m s v i)

＋→sub-agents : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                (v : C⟦𝕍⟧ Γ u)
                (x : Agents ((Γ ، u) ＋ Δ))
              → ⟦ sub-Agents x (CSub،＋ v) ⟧ₛ (m ＋ₛ s)
              ≡ ⟦ x ⟧ₛ ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-agents {Γ} {Δ} {u} m s v (agentsV i) = ＋→sub-agents-var m s v i
＋→sub-agents {Γ} {Δ} {u} m s v (agentsL x) = ＋→sub-agentL m s v x
--＋→sub-agents {Γ} {Δ} {u} m s v (agentsS x) = refl

≔→sub-agents : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
               (v : C⟦𝕍⟧ Γ u)
               (x : Agents ((Γ ، u) ＋ Δ))
             → ⟦ sub-Agents x (CSub،＋ v) ⟧ₛ· (m ≔= s)
             ≡ ⟦ x ⟧ₛ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-agents {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-Agents x (CSub،＋ v) ⟧ₛ z) (sub≔= m s))
        (trans (＋→sub-agents (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧ₛ z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

＋→sub-data-var : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                  (v : C⟦𝕍⟧ Γ u)
                  (i : ∈Ctxt (𝕍𝕌 𝕌Data) ((Γ ، u) ＋ Δ))
                → ⟦ CSub،＋ v i ⟧d (m ＋ₛ s)
                ≡ app-sub i ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-data-var {Γ} {⟨⟩} {.𝕍𝕌 𝕌Data} m ● v (∈Ctxt0 .Γ) = refl
＋→sub-data-var {Γ} {⟨⟩} {u} m ● v (∈CtxtS .u i) = refl
＋→sub-data-var {Γ} {Δ ، .(𝕍𝕌 𝕌Data)} {u} m (s ⹁ .(𝕍𝕌 𝕌Data) ∶ v₁) v (∈Ctxt0 .((Γ ، u) ＋ Δ)) = refl
＋→sub-data-var {Γ} {Δ ، U} {u} m (s ⹁ .U ∶ v₁) v (∈CtxtS .U i) =
  trans (⟦⊆⟧d (m ＋ₛ s) ⊆₀ ((m ＋ₛ s) ⹁ U ∶ v₁) Sub⊆-⊆₀ (CSub،＋ v i))
        (＋→sub-data-var m s v i)

＋→sub-data : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
              (v : C⟦𝕍⟧ Γ u)
              (x : Data ((Γ ، u) ＋ Δ))
            → ⟦ sub-Data x (CSub،＋ v) ⟧d (m ＋ₛ s)
            ≡ ⟦ x ⟧d ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-data {Γ} {Δ} {u} m s v (dataV i) = ＋→sub-data-var m s v i
＋→sub-data {Γ} {Δ} {u} m s v (dataC x) = refl

≔→sub-data : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
               (v : C⟦𝕍⟧ Γ u)
               (x : Data ((Γ ، u) ＋ Δ))
             → ⟦ sub-Data x (CSub،＋ v) ⟧d· (m ≔= s)
             ≡ ⟦ x ⟧d· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-data {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-Data x (CSub،＋ v) ⟧d z) (sub≔= m s))
        (trans (＋→sub-data (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧d z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

＋→sub-atomProp-var : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                      (v : C⟦𝕍⟧ Γ u)
                      (i : ∈Ctxt (𝕍𝕌 𝕌Prop) ((Γ ، u) ＋ Δ))
                    → ⟦ CSub،＋ v i ⟧ₚ (m ＋ₛ s)
                    ≡ app-sub i ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-atomProp-var {Γ} {⟨⟩} {.(𝕍𝕌 𝕌Prop)} m ● v (∈Ctxt0 .Γ) = refl
＋→sub-atomProp-var {Γ} {⟨⟩} {u} m ● v (∈CtxtS .u i) = refl
＋→sub-atomProp-var {Γ} {Δ ، .(𝕍𝕌 𝕌Prop)} {u} m (s ⹁ .(𝕍𝕌 𝕌Prop) ∶ v₁) v (∈Ctxt0 .((Γ ، u) ＋ Δ)) = refl
＋→sub-atomProp-var {Γ} {Δ ، U} {u} m (s ⹁ .U ∶ v₁) v (∈CtxtS .U i) =
  trans (⟦⊆⟧ₚ (m ＋ₛ s) ⊆₀ ((m ＋ₛ s) ⹁ U ∶ v₁) Sub⊆-⊆₀ (CSub،＋ v i))
        (＋→sub-atomProp-var m s v i)

＋→sub-atomProp : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                  (v : C⟦𝕍⟧ Γ u)
                  (x : AtomProp ((Γ ، u) ＋ Δ))
                → ⟦ sub-AtomProp x (CSub،＋ v) ⟧ₚ (m ＋ₛ s)
                ≡ ⟦ x ⟧ₚ ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-atomProp {Γ} {Δ} {u} m s v (atomPropV i) = ＋→sub-atomProp-var m s v i
＋→sub-atomProp {Γ} {Δ} {u} m s v (atomPropC x) = refl

≔→sub-atomProp : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
                 (v : C⟦𝕍⟧ Γ u)
                 (x : AtomProp ((Γ ، u) ＋ Δ))
               → ⟦ sub-AtomProp x (CSub،＋ v) ⟧ₚ· (m ≔= s)
               ≡ ⟦ x ⟧ₚ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-atomProp {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-AtomProp x (CSub،＋ v) ⟧ₚ z) (sub≔= m s))
        (trans (＋→sub-atomProp (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧ₚ z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

＋→sub-action : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                (v : C⟦𝕍⟧ Γ u)
                (x : Action ((Γ ، u) ＋ Δ))
              → ⟦ sub-Action x (CSub،＋ v) ⟧ₜ (m ＋ₛ s)
              ≡ ⟦ x ⟧ₜ ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-action {Γ} {Δ} {u} m s v (ActSend p a A) =
  cong₃ ActSend
        (cong dataC (＋→sub-data m s v p))
        (cong agentC (＋→sub-agent m s v a))
        (cong agentsS (＋→sub-agents m s v A))

≔→sub-action : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
               (v : C⟦𝕍⟧ Γ u)
               (x : Action ((Γ ، u) ＋ Δ))
             → ⟦ sub-Action x (CSub،＋ v) ⟧ₜ· (m ≔= s)
             ≡ ⟦ x ⟧ₜ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-action {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-Action x (CSub،＋ v) ⟧ₜ z) (sub≔= m s))
        (trans (＋→sub-action (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧ₜ z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

＋→sub-event : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
               (v : C⟦𝕍⟧ Γ u)
               (x : Event ((Γ ، u) ＋ Δ))
             → ⟦ sub-Event x (CSub،＋ v) ⟧ₑ (m ＋ₛ s)
             ≡ ⟦ x ⟧ₑ ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-event {Γ} {Δ} {u} m s v (EvtReceive p a b) =
  cong₃ EvtReceive
        (cong dataC (＋→sub-data m s v p))
        (cong agentC (＋→sub-agent m s v a))
        (cong agentC (＋→sub-agent m s v b))
＋→sub-event {Γ} {Δ} {u} m s v (EvtInternal a d) =
  cong₂ EvtInternal
        (cong agentC (＋→sub-agent m s v a))
        (cong dataC (＋→sub-data m s v d))

≔→sub-event : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
              (v : C⟦𝕍⟧ Γ u)
              (x : Event ((Γ ، u) ＋ Δ))
            → ⟦ sub-Event x (CSub،＋ v) ⟧ₑ· (m ≔= s)
            ≡ ⟦ x ⟧ₑ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-event {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-Event x (CSub،＋ v) ⟧ₑ z) (sub≔= m s))
        (trans (＋→sub-event (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧ₑ z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

＋→sub-fault : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
               (v : C⟦𝕍⟧ Γ u)
               (x : Fault ((Γ ، u) ＋ Δ))
             → ⟦ sub-Fault x (CSub،＋ v) ⟧f (m ＋ₛ s)
             ≡ ⟦ x ⟧f ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-fault {Γ} {Δ} {u} m s v (FaultCorrect a b) =
  cong₂ FaultCorrect
        (cong agentC (＋→sub-agent m s v a))
        (cong agentC (＋→sub-agent m s v b))

≔→sub-fault : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
              (v : C⟦𝕍⟧ Γ u)
              (x : Fault ((Γ ، u) ＋ Δ))
            → ⟦ sub-Fault x (CSub،＋ v) ⟧f· (m ≔= s)
            ≡ ⟦ x ⟧f· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-fault {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-Fault x (CSub،＋ v) ⟧f z) (sub≔= m s))
        (trans (＋→sub-fault (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧f z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

≔→sub-atom : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
             (v : C⟦𝕍⟧ Γ u)
             (x : Atom ((Γ ، u) ＋ Δ))
           → ⟦ sub-Atom x (CSub،＋ v) ⟧ₐ· (m ≔= s)
           ≡ ⟦ x ⟧ₐ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-atom {Γ} {Δ} {u} m s v (atProp x) = cong atProp (cong atomPropC (≔→sub-atomProp m s v x))
≔→sub-atom {Γ} {Δ} {u} m s v (atAction x) = cong atAction (≔→sub-action m s v x)
≔→sub-atom {Γ} {Δ} {u} m s v (atEvent x) = cong atEvent (≔→sub-event m s v x)
≔→sub-atom {Γ} {Δ} {u} m s v (atCorrect x) = cong atCorrect (≔→sub-fault m s v x)

＋→sub-res-var : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
                 (v : C⟦𝕍⟧ Γ u)
                 (i : ∈Ctxt 𝕍ℝ ((Γ ، u) ＋ Δ))
               → ⟦ CSub،＋ v i ⟧ᵣ (m ＋ₛ s)
               ≡ app-sub i ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-res-var {Γ} {⟨⟩} {.𝕍ℝ} m ● v (∈Ctxt0 .Γ) = refl
＋→sub-res-var {Γ} {⟨⟩} {u} m ● v (∈CtxtS .u i) = refl
＋→sub-res-var {Γ} {Δ ، .𝕍ℝ} {u} m (s ⹁ .𝕍ℝ ∶ v₁) v (∈Ctxt0 .((Γ ، u) ＋ Δ)) = refl
＋→sub-res-var {Γ} {Δ ، U} {u} m (s ⹁ .U ∶ v₁) v (∈CtxtS .U i) =
  trans (⟦⊆⟧ᵣ (m ＋ₛ s) ⊆₀ ((m ＋ₛ s) ⹁ U ∶ v₁) Sub⊆-⊆₀ (CSub،＋ v i))
        (＋→sub-res-var m s v i)

＋→sub-res : {Γ Δ : Ctxt} {u : 𝕍} (m : Sub Γ) (s : Sub Δ)
             (v : C⟦𝕍⟧ Γ u)
             (x : Res ((Γ ، u) ＋ Δ))
           → ⟦ sub-Res x (CSub،＋ v) ⟧ᵣ (m ＋ₛ s)
           ≡ ⟦ x ⟧ᵣ ((m ⹁ u ∶ ⟦ u ، v ⟧c m) ＋ₛ s)
＋→sub-res {Γ} {Δ} {u} m s v (𝐯 i) = ＋→sub-res-var m s v i
＋→sub-res {Γ} {Δ} {u} m s v 𝟎 = refl
--＋→sub-res {Γ} {Δ} {u} m s v (𝐬 x) = cong 𝕤 (＋→sub-res m s v x)
＋→sub-res {Γ} {Δ} {u} m s v (r₁ ⋆ r₂) = cong₂ _·_ (＋→sub-res m s v r₁) (＋→sub-res m s v r₂)
＋→sub-res {Γ} {Δ} {u} m s v (rvar ρ) = refl

≔→sub-res : {Γ Δ : Ctxt} {u : 𝕍} (m : Model Γ) (s : Sub Δ)
            (v : C⟦𝕍⟧ Γ u)
            (x : Res ((Γ ، u) ＋ Δ))
          → ⟦ sub-Res x (CSub،＋ v) ⟧ᵣ· (m ≔= s)
          ≡ ⟦ x ⟧ᵣ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)
≔→sub-res {Γ} {Δ} {u} m s v x =
  trans (cong (λ z → ⟦ sub-Res x (CSub،＋ v) ⟧ᵣ z) (sub≔= m s))
        (trans (＋→sub-res (Model.subΓ m) s v x)
               (sym (cong (λ z → ⟦ x ⟧ᵣ z) (sub≔= (m ≔ ⟦ u ، v ⟧c· m) s))))

interp-≔= : {Γ Δ : Ctxt} (m : Model Γ)
            (s : Sub Δ)
          → Model.interp (m ≔= s) ≡ Model.interp m
interp-≔= {Γ} {.⟨⟩} (model interp run w subΓ) ● = refl
interp-≔= {Γ} {.(_ ، u)} m (s ⹁ u ∶ v) = interp-≔= m s

{--
vars-≔= : {Γ Δ : Ctxt} (m : Model Γ)
          (s : Sub Δ)
        → Model.vars (m ≔= s) ≡ Model.vars m
vars-≔= {Γ} {.⟨⟩} (model interp run w subΓ vars) ● = refl
vars-≔= {Γ} {.(_ ، u)} m (s ⹁ u ∶ v) = vars-≔= m s
--}

run-≔= : {Γ Δ : Ctxt} (m : Model Γ)
         (s : Sub Δ)
       → Model.run (m ≔= s) ≡ Model.run m
run-≔= {Γ} {.⟨⟩} (model interp run w subΓ) ● = refl
run-≔= {Γ} {.(_ ، u)} m (s ⹁ u ∶ v) = run-≔= m s

w-≔= : {Γ Δ : Ctxt} (m : Model Γ)
       (s : Sub Δ)
     → Model.w (m ≔= s) ≡ Model.w m
w-≔= {Γ} {.⟨⟩} (model interp run w subΓ) ● = refl
w-≔= {Γ} {.(_ ، u)} m (s ⹁ u ∶ v) = w-≔= m s

≔=-≔ₜ : {Γ Δ : Ctxt} (m : Model Γ)
        (s : Sub Δ)
        (t : 𝕎)
      → (m ≔= s) ≔ₜ t ≡ (m ≔ₜ t) ≔= s
≔=-≔ₜ {Γ} {.⟨⟩} (model interp run w subΓ) ● t = refl
≔=-≔ₜ {Γ} {.(_ ، u)} m (s ⹁ u ∶ v) t = trans (≔-≔ₜ (m ≔= s) v t) (cong (λ z → z ≔ v) (≔=-≔ₜ m s t))

≔→sub-SetAtom-gen : (Γ Δ : Ctxt) {m : Model Γ} {u : 𝕍}
                    (A : SetAtom ((Γ ، u) ＋ Δ))
                    (v : C⟦𝕍⟧ Γ u)
                    (s : Sub Δ)
                  → ((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ⊨A A
                  → (m ≔= s) ⊨A sub-SetAtom A (CSub،＋ v)
≔→sub-SetAtom-gen Γ Δ {m} {u} (x ∈ₐ x₁) v s h =
  subst₂ (λ a b → b ∈ a) (sym (≔→sub-agents m s v x₁)) (sym (≔→sub-agent m s v x)) h
≔→sub-SetAtom-gen Γ Δ {m} {u} (∣ A ∣ₛ＝ n) v s h =
  trans (cong length (≔→sub-agents m s v A)) h

≔→sub-SetAtom-gen-rev : (Γ Δ : Ctxt) {m : Model Γ} {u : 𝕍}
                        (A : SetAtom ((Γ ، u) ＋ Δ))
                        (v : C⟦𝕍⟧ Γ u)
                        (s : Sub Δ)
                      → (m ≔= s) ⊨A sub-SetAtom A (CSub،＋ v)
                      → ((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ⊨A A
≔→sub-SetAtom-gen-rev Γ Δ {m} {u} (x ∈ₐ x₁) v s h =
  subst₂ (λ a b → b ∈ a) (≔→sub-agents m s v x₁) (≔→sub-agent m s v x) h
≔→sub-SetAtom-gen-rev Γ Δ {m} {u} (∣ A ∣ₛ＝ n) v s h =
  trans (cong length (sym (≔→sub-agents m s v A))) h

mutual
  ≔→sub-gen : (Γ Δ : Ctxt) {m : Model Γ} {u : 𝕍}
              (A : Form ((Γ ، u) ＋ Δ))
              (v : C⟦𝕍⟧ Γ u)
              (s : Sub Δ)
            → ((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ⊨ A
            → (m ≔= s) ⊨ sub A (CSub،＋ v)
  ≔→sub-gen Γ Δ {m} {u} (𝕒 x) v s h =
    subst₃ (λ x₁ x₂ x₃ → x₁ (x₂ x₃) (⟦ sub-Atom x (CSub،＋ v) ⟧ₐ· (m ≔= s)))
           (sym (interp-≔= m s))
           (sym (run-≔= m s))
           (sym (w-≔= m s))
           (subst (Model.interp m (Model.run m (Model.w m)))
                  (sym (≔→sub-atom m s v x))
                  (subst₃ (λ x₁ x₂ x₃ → x₁ (x₂ x₃) (⟦ x ⟧ₐ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)))
                          (interp-≔= (m ≔ ⟦ u ، v ⟧c· m) s)
                          (run-≔= (m ≔ ⟦ u ، v ⟧c· m) s)
                          (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s)
                          h))
  -- use ≔→sub-atom
  ≔→sub-gen Γ Δ {m} {u} (var x) v s h =
    h {--subst (λ z → z x)
          (sym (vars-≔= m s))
          (subst (λ z → z x) (vars-≔= (m ≔ ⟦ u ، v ⟧c· m) s) h)--}
  ≔→sub-gen Γ Δ {m} {u} ⊤· v s h = h
  ≔→sub-gen Γ Δ {m} {u} (A ∧· A₁) v s (h₁ , h₂) =
    ≔→sub-gen Γ Δ A v s h₁ ,
    ≔→sub-gen Γ Δ A₁ v s h₂
  ≔→sub-gen Γ Δ {m} {u} (A ∨· A₁) v s (inj₁ h) =
    inj₁ (≔→sub-gen Γ Δ A v s h)
  ≔→sub-gen Γ Δ {m} {u} (A ∨· A₁) v s (inj₂ h) =
    inj₂ (≔→sub-gen Γ Δ A₁ v s h)
  ≔→sub-gen Γ Δ {m} {u} (A →· A₁) v s h q =
    ≔→sub-gen Γ Δ A₁ v s (h (≔→sub-gen-rev Γ Δ A v s q))
--  ≔→sub-gen Γ Δ {m} {u} (¬· A) v s h q =
--    h (≔→sub-gen-rev Γ Δ A v s q)
  ≔→sub-gen Γ Δ {m} {u} (∀· u₁ A) v s h w =
    ≔→sub-gen Γ (Δ ، 𝕍𝕌 u₁) A v (s ⹁ 𝕍𝕌 u₁ ∶ w) (h w)
  ≔→sub-gen Γ Δ {m} {u} (∃· u₁ A) v s (t , h) =
    t , ≔→sub-gen Γ (Δ ، 𝕍𝕌 u₁) A v (s ⹁ 𝕍𝕌 u₁ ∶ t) h
  ≔→sub-gen Γ Δ {m} {u} (𝔸 A) v s (lift h) =
    lift (≔→sub-SetAtom-gen Γ Δ A v s h)
--  ≔→sub-gen Γ Δ {m} {u} (x ∈ᵢ x₁) v s (lift h) =
--    lift (subst (λ a → x₁ a) (sym (≔→sub-data m s v x)) h)
--  ≔→sub-gen Γ Δ {m} {u} (⟨ x ، x₁ ⟩∈ᵣ x₂) v s (lift h) =
--    lift (subst₂ x₂ (sym (≔→sub-data m s v x)) (sym (≔→sub-data m s v x₁)) h)
  ≔→sub-gen Γ Δ {m} {u} (f Ｕ f₁) v s (t , c₁ , c₂ , c₃) =
    t ,
    subst (λ z → z ≼ t) (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s))) c₁ ,
    subst (λ z → z ⊨ sub f₁ (CSub،＋ v))
          (sym (≔=-≔ₜ m s t))
          (≔→sub-gen Γ Δ {m ≔ₜ t} {u} f₁ v s
            (subst (λ z → z ⊨ f₁)
                   (trans (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· (m ≔ₜ t)) s t)
                          (cong (λ z → z ≔= s) (≔-≔ₜ m (⟦ u ، v ⟧c· (m ≔ₜ t)) t)))
                   c₂)) ,
    𝕀
    where
    𝕀 : (t′ : 𝕎) → (m ≔= s) ≤ₜ t′ → t′ ≺ t → ((m ≔= s) ≔ₜ t′) ⊨ sub f (CSub،＋ v)
    𝕀 t′ k₁ k₂ =
      subst (λ z → z ⊨ sub f (CSub،＋ v))
            (sym (≔=-≔ₜ m s t′))
            (≔→sub-gen Γ Δ {m ≔ₜ t′} {u} f v s
              (subst (λ z → z ⊨ f)
                (trans (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· (m ≔ₜ t′)) s t′)
                       (cong (λ z → z ≔= s) (≔-≔ₜ m (⟦ u ، v ⟧c· (m ≔ₜ t′)) t′)))
                (c₃ t′ (subst (λ z → z ≼ t′) (sym (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s)))) k₁) k₂)))
  ≔→sub-gen Γ Δ {m} {u} (Ｏ f) v s (t , c₁ , c₂) =
    t ,
    subst (λ z → z ◃ t) (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s))) c₁ ,
    subst (λ z → z ⊨ sub f (CSub،＋ v))
          (sym (≔=-≔ₜ m s t))
          (≔→sub-gen Γ Δ {m ≔ₜ t} {u} f v s
            (subst (λ z → z ⊨ f)
                   (trans (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· (m ≔ₜ t)) s t)
                          (cong (λ z → z ≔= s) (≔-≔ₜ m (⟦ u ، v ⟧c· (m ≔ₜ t)) t)))
                   c₂))
  ≔→sub-gen Γ Δ {m} {u} (f Ｓ f₁) v s (t , c₁ , c₂ , c₃) =
    t ,
    subst (λ z → t ≼ z) (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s))) c₁ ,
    subst (λ z → z ⊨ sub f₁ (CSub،＋ v))
          (sym (≔=-≔ₜ m s t))
          (≔→sub-gen Γ Δ {m ≔ₜ t} {u} f₁ v s
            (subst (λ z → z ⊨ f₁)
                   (trans (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· (m ≔ₜ t)) s t)
                          (cong (λ z → z ≔= s) (≔-≔ₜ m (⟦ u ، v ⟧c· (m ≔ₜ t)) t)))
                   c₂)) ,
    𝕀
    where
    𝕀 : (t′ : 𝕎) → t ≺ t′ → (m ≔= s) ≥ₜ t′ → ((m ≔= s) ≔ₜ t′) ⊨ sub f (CSub،＋ v)
    𝕀 t′ k₁ k₂ =
      subst (λ z → z ⊨ sub f (CSub،＋ v))
            (sym (≔=-≔ₜ m s t′))
            (≔→sub-gen Γ Δ {m ≔ₜ t′} {u} f v s
              (subst (λ z → z ⊨ f)
                (trans (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· (m ≔ₜ t′)) s t′)
                       (cong (λ z → z ≔= s) (≔-≔ₜ m (⟦ u ، v ⟧c· (m ≔ₜ t′)) t′)))
                (c₃ t′ k₁ (subst (λ z → t′ ≼ z) (sym (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s)))) k₂))))
  ≔→sub-gen Γ Δ {m} {u} (Ｙ f) v s (t , c₁ , c₂) =
    t ,
    subst (λ z → t ◃ z) (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s))) c₁ ,
    subst (λ z → z ⊨ sub f (CSub،＋ v))
          (sym (≔=-≔ₜ m s t))
          (≔→sub-gen Γ Δ {m ≔ₜ t} {u} f v s
            (subst (λ z → z ⊨ f)
                   (trans (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· (m ≔ₜ t)) s t)
                          (cong (λ z → z ≔= s) (≔-≔ₜ m (⟦ u ، v ⟧c· (m ≔ₜ t)) t)))
                   c₂))
  ≔→sub-gen Γ Δ {m} {u} (Ｂ f) v s h t q =
    subst (λ z → z ⊨ sub f (CSub،＋ v))
          (sym (≔=-≔ₜ m s t))
          (≔→sub-gen Γ Δ {m ≔ₜ t} {u} f v s
            (subst (λ z → z ⊨ f)
                   (trans (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· (m ≔ₜ t)) s t)
                          (cong (λ z → z ≔= s) (≔-≔ₜ m (⟦ u ، v ⟧c· (m ≔ₜ t)) t)))
                   (h t (subst (λ z → t ◃ z) (sym (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s)))) q))))
  ≔→sub-gen Γ Δ {m} {u} (Ｆ f) v s h =
    ≔→sub-gen
      Γ (Δ ، 𝕍ℝ) {m} {u} f v (s ⹁ 𝕍ℝ ∶ Model.w (m ≔= s))
      (subst (λ z → (((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ≔ z) ⊨ f)
             (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s)))
             h)
  ≔→sub-gen Γ Δ {m} {u} (r₁ ⟨ c ⟩ r₂) v s (lift h) =
    lift (subst₂ ⟦ c ⟧ᶜ (sym (≔→sub-res m s v r₁)) (sym (≔→sub-res m s v r₂)) h)

  ≔→sub-gen-rev : (Γ Δ : Ctxt) {m : Model Γ} {u : 𝕍}
                  (A : Form ((Γ ، u) ＋ Δ))
                  (v : C⟦𝕍⟧ Γ u)
                  (s : Sub Δ)
                → (m ≔= s) ⊨ sub A (CSub،＋ v)
                → ((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ⊨ A
  ≔→sub-gen-rev Γ Δ {m} {u} (𝕒 x) v s h =
    subst₃ (λ x₁ x₂ x₃ → x₁ (x₂ x₃) (⟦ x ⟧ₐ· ((m ≔ ⟦ u ، v ⟧c· m) ≔= s)))
           (sym (interp-≔= (m ≔ ⟦ u ، v ⟧c· m) s))
           (sym (run-≔= (m ≔ ⟦ u ، v ⟧c· m) s))
           (sym (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s))
           (subst (Model.interp m (Model.run m (Model.w m)))
                  (≔→sub-atom m s v x)
                  (subst₃ (λ x₁ x₂ x₃ → x₁ (x₂ x₃) (⟦ sub-Atom x (CSub،＋ v) ⟧ₐ· (m ≔= s)))
                          (interp-≔= m s)
                          (run-≔= m s)
                          (w-≔= m s)
                          h))
  ≔→sub-gen-rev Γ Δ {m} {u} (var x) v s h =
    h {--subst (λ z → z x)
          (sym (vars-≔= (m ≔ ⟦ u ، v ⟧c· m) s))
          (subst (λ z → z x) (vars-≔= m s) h)--}
  ≔→sub-gen-rev Γ Δ {m} {u} ⊤· v s h = h
  ≔→sub-gen-rev Γ Δ {m} {u} (A ∧· A₁) v s (h₁ , h₂) =
    ≔→sub-gen-rev Γ Δ A v s h₁ ,
    ≔→sub-gen-rev Γ Δ A₁ v s h₂
  ≔→sub-gen-rev Γ Δ {m} {u} (A ∨· A₁) v s (inj₁ h) =
    inj₁ (≔→sub-gen-rev Γ Δ A v s h)
  ≔→sub-gen-rev Γ Δ {m} {u} (A ∨· A₁) v s (inj₂ h) =
    inj₂ (≔→sub-gen-rev Γ Δ A₁ v s h)
  ≔→sub-gen-rev Γ Δ {m} {u} (A →· A₁) v s h q =
    ≔→sub-gen-rev Γ Δ A₁ v s (h (≔→sub-gen Γ Δ A v s q))
--  ≔→sub-gen-rev Γ Δ {m} {u} (¬· A) v s h q =
--    h (≔→sub-gen Γ Δ A v s q)
  ≔→sub-gen-rev Γ Δ {m} {u} (∀· u₁ A) v s h w =
    ≔→sub-gen-rev Γ (Δ ، 𝕍𝕌 u₁) A v (s ⹁ 𝕍𝕌 u₁ ∶ w) (h w)
  ≔→sub-gen-rev Γ Δ {m} {u} (∃· u₁ A) v s (t , h) =
    t , ≔→sub-gen-rev Γ (Δ ، 𝕍𝕌 u₁) A v (s ⹁ 𝕍𝕌 u₁ ∶ t) h
  ≔→sub-gen-rev Γ Δ {m} {u} (𝔸 A) v s (lift h) =
    lift (≔→sub-SetAtom-gen-rev Γ Δ A v s h)
--  ≔→sub-gen-rev Γ Δ {m} {u} (x ∈ᵢ x₁) v s (lift h) =
--    lift (subst (λ a → x₁ a) (≔→sub-data m s v x) h)
--  ≔→sub-gen-rev Γ Δ {m} {u} (⟨ x ، x₁ ⟩∈ᵣ x₂) v s (lift h) =
--    lift (subst₂ x₂ (≔→sub-data m s v x) (≔→sub-data m s v x₁) h)
  ≔→sub-gen-rev Γ Δ {m} {u} (A Ｕ A₁) v s (t , c₁ , c₂ , c₃) =
    t ,
    subst (λ z → z ≼ t) (trans (w-≔= m s) (sym (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s))) c₁ ,
    subst (λ z → z ⊨ A₁)
          (sym (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· m) s t))
          (≔→sub-gen-rev Γ Δ {m ≔ₜ t} {u} A₁ v s
            (subst (λ z → z ⊨ sub A₁ (CSub،＋ v))
                   (≔=-≔ₜ m s t)
                   c₂)) ,
    𝕀
    where
    𝕀 : (t′ : 𝕎) → ((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ≤ₜ t′ → t′ ≺ t → (((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ≔ₜ t′) ⊨ A
    𝕀 t′ k₁ k₂ =
      subst (λ z → z ⊨ A)
            (sym (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· m) s t′))
            (≔→sub-gen-rev Γ Δ {m ≔ₜ t′} {u} A v s
              (subst (λ z → z ⊨ sub A (CSub،＋ v))
                     (≔=-≔ₜ m s t′)
                     (c₃ t′ (subst (λ z → z ≼ t′) (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s))) k₁) k₂)))
  ≔→sub-gen-rev Γ Δ {m} {u} (Ｏ A) v s (t , c₁ , c₂) =
    t ,
    subst (λ z → z ◃ t) (trans (w-≔= m s) (sym (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s))) c₁ ,
    subst (λ z → z ⊨ A)
          (sym (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· m) s t))
          (≔→sub-gen-rev Γ Δ {m ≔ₜ t} {u} A v s
            (subst (λ z → z ⊨ sub A (CSub،＋ v))
                   (≔=-≔ₜ m s t)
                   c₂))
  ≔→sub-gen-rev Γ Δ {m} {u} (A Ｓ A₁) v s (t , c₁ , c₂ , c₃) =
    t ,
    subst (λ z → t ≼ z) (trans (w-≔= m s) (sym (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s))) c₁ ,
    subst (λ z → z ⊨ A₁)
          (sym (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· m) s t))
          (≔→sub-gen-rev Γ Δ {m ≔ₜ t} {u} A₁ v s
            (subst (λ z → z ⊨ sub A₁ (CSub،＋ v))
                   (≔=-≔ₜ m s t)
                   c₂)) ,
    𝕀
    where
    𝕀 : (t′ : 𝕎) → t ≺ t′ → ((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ≥ₜ t′ → (((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ≔ₜ t′) ⊨ A
    𝕀 t′ k₁ k₂ =
      subst (λ z → z ⊨ A)
            (sym (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· m) s t′))
            (≔→sub-gen-rev Γ Δ {m ≔ₜ t′} {u} A v s
              (subst (λ z → z ⊨ sub A (CSub،＋ v))
                     (≔=-≔ₜ m s t′)
                     (c₃ t′ k₁ (subst (λ z → t′ ≼ z) (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s))) k₂))))
  ≔→sub-gen-rev Γ Δ {m} {u} (Ｙ A) v s (t , c₁ , c₂) =
    t ,
    subst (λ z → t ◃ z) (trans (w-≔= m s) (sym (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s))) c₁ ,
    subst (λ z → z ⊨ A)
          (sym (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· m) s t))
          (≔→sub-gen-rev Γ Δ {m ≔ₜ t} {u} A v s
            (subst (λ z → z ⊨ sub A (CSub،＋ v))
                   (≔=-≔ₜ m s t)
                   c₂))
  ≔→sub-gen-rev Γ Δ {m} {u} (Ｂ A) v s f t q =
    subst (λ z → z ⊨ A)
          (sym (≔=-≔ₜ (m ≔ ⟦ u ، v ⟧c· m) s t))
          (≔→sub-gen-rev Γ Δ {m ≔ₜ t} {u} A v s
            (subst (λ z → z ⊨ sub A (CSub،＋ v))
                   (≔=-≔ₜ m s t)
                   (f t (subst (λ z → t ◃ z) (sym (trans (w-≔= m s) (sym (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s)))) q))))
  ≔→sub-gen-rev Γ Δ {m} {u} (Ｆ A) v s h =
    subst (λ z → (((m ≔ ⟦ u ، v ⟧c· m) ≔= s) ≔ z) ⊨ A)
          (sym (trans (w-≔= (m ≔ ⟦ u ، v ⟧c· m) s) (sym (w-≔= m s))))
          (≔→sub-gen-rev
            Γ (Δ ، 𝕍ℝ) {m} {u} A v
            (s ⹁ 𝕍ℝ ∶ Model.w (m ≔= s))
            h)
  ≔→sub-gen-rev Γ Δ {m} {u} (t₁ ⟨ x ⟩ t₂) v s (lift h) =
    lift (subst₂ ⟦ x ⟧ᶜ (≔→sub-res m s v t₁) (≔→sub-res m s v t₂) h)

≔→sub : (Γ : Ctxt) {m : Model Γ} {u : 𝕍}
        (A : Form (Γ ، u))
        (v : C⟦𝕍⟧ Γ u)
      → (m ≔ ⟦ u ، v ⟧c· m) ⊨ A
      → m ⊨ sub A (CSub،ₗ v)
≔→sub Γ {m} {u} A v h = ≔→sub-gen Γ ⟨⟩ {m} {u} A v ● h

≔→sub-rev : (Γ : Ctxt) {m : Model Γ} {u : 𝕍}
            (A : Form (Γ ، u))
            (v : C⟦𝕍⟧ Γ u)
          → m ⊨ sub A (CSub،ₗ v)
          → (m ≔ ⟦ u ، v ⟧c· m) ⊨ A
≔→sub-rev Γ {m} {u} A v h = ≔→sub-gen-rev Γ ⟨⟩ {m} {u} A v ● h

↑I : {Γ Δ : Ctxt}
    → Γ ⊆ Δ
    → Interval Γ
    → Interval Δ
↑I {Γ} {Δ} e ［ x , x₁ ］ = ［ ↑ᵣ e x , ↑ᵣ e x₁ ］
↑I {Γ} {Δ} e ［ x , x₁ ） = ［ ↑ᵣ e x , ↑ᵣ e x₁ ）
↑I {Γ} {Δ} e （ x , x₁ ］ = （ ↑ᵣ e x , ↑ᵣ e x₁ ］
↑I {Γ} {Δ} e （ x , x₁ ） = （ ↑ᵣ e x , ↑ᵣ e x₁ ）

↑CE : {Γ Δ : Ctxt}
    → Γ ⊆ Δ
    → CE Γ
    → CE Δ
↑CE {Γ} {Δ} e (CEr x) = CEr (↑ᵣ e x)
↑CE {Γ} {Δ} e CEu = CEu
↑CE {Γ} {Δ} e (CEi x) = CEi (↑I e x)

↑CE₀ : {Γ : Ctxt} {u : 𝕍} → CE Γ → CE (Γ ، u)
↑CE₀ {Γ} {u} a = ↑CE ⊆₀ a

↑CE₀، : {Γ : Ctxt} {u v : 𝕍} → CE (Γ ، v) → CE (Γ ، u ، v)
↑CE₀، {Γ} {u} {v} a = ↑CE ⊆₀، a

↑I₀ : {Γ : Ctxt} {u : 𝕍} → Interval Γ → Interval (Γ ، u)
↑I₀ {Γ} {u} a = ↑I ⊆₀ a

↑I-refl : {Γ : Ctxt}
          (e  : Γ ⊆ Γ)
          (x  : Interval Γ)
        → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
        → ↑I e x ≡ x
↑I-refl {Γ} e ［ x , x₁ ］ cond = cong₂ ［_,_］ (↑ᵣ-refl e x cond) (↑ᵣ-refl e x₁ cond)
↑I-refl {Γ} e ［ x , x₁ ） cond = cong₂ ［_,_） (↑ᵣ-refl e x cond) (↑ᵣ-refl e x₁ cond)
↑I-refl {Γ} e （ x , x₁ ］ cond = cong₂ （_,_］ (↑ᵣ-refl e x cond) (↑ᵣ-refl e x₁ cond)
↑I-refl {Γ} e （ x , x₁ ） cond = cong₂ （_,_） (↑ᵣ-refl e x cond) (↑ᵣ-refl e x₁ cond)

↑CE-refl : {Γ : Ctxt}
           (e  : Γ ⊆ Γ)
           (x  : CE Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i)
         → ↑CE e x ≡ x
↑CE-refl {Γ} e (CEr x) cond = cong CEr (↑ᵣ-refl e x cond)
↑CE-refl {Γ} e CEu cond = refl
↑CE-refl {Γ} e (CEi x) cond = cong CEi (↑I-refl e x cond)

↑I-trans : {Γ Ψ Δ : Ctxt}
           (e  : Γ ⊆ Δ)
           (e₁ : Γ ⊆ Ψ)
           (e₂ : Ψ ⊆ Δ)
           (x  : Interval Γ)
         → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
         → ↑I e x ≡ ↑I e₂ (↑I e₁ x)
↑I-trans {Γ} {Ψ} {Δ} e e₁ e₂ ［ x , x₁ ］ cond = cong₂ ［_,_］ (↑ᵣ-trans e e₁ e₂ x cond) (↑ᵣ-trans e e₁ e₂ x₁ cond)
↑I-trans {Γ} {Ψ} {Δ} e e₁ e₂ ［ x , x₁ ） cond = cong₂ ［_,_） (↑ᵣ-trans e e₁ e₂ x cond) (↑ᵣ-trans e e₁ e₂ x₁ cond)
↑I-trans {Γ} {Ψ} {Δ} e e₁ e₂ （ x , x₁ ］ cond = cong₂ （_,_］ (↑ᵣ-trans e e₁ e₂ x cond) (↑ᵣ-trans e e₁ e₂ x₁ cond)
↑I-trans {Γ} {Ψ} {Δ} e e₁ e₂ （ x , x₁ ） cond = cong₂ （_,_） (↑ᵣ-trans e e₁ e₂ x cond) (↑ᵣ-trans e e₁ e₂ x₁ cond)

↑CE-trans : {Γ Ψ Δ : Ctxt}
            (e  : Γ ⊆ Δ)
            (e₁ : Γ ⊆ Ψ)
            (e₂ : Ψ ⊆ Δ)
            (x  : CE Γ)
          → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
          → ↑CE e x ≡ ↑CE e₂ (↑CE e₁ x)
↑CE-trans {Γ} {Ψ} {Δ} e e₁ e₂ (CEr x) cond = cong CEr (↑ᵣ-trans e e₁ e₂ x cond)
↑CE-trans {Γ} {Ψ} {Δ} e e₁ e₂ CEu cond = refl
↑CE-trans {Γ} {Ψ} {Δ} e e₁ e₂ (CEi x) cond = cong CEi (↑I-trans e e₁ e₂ x cond)

↑CE⊆-refl : {Γ : Ctxt}
            (x : CE Γ)
          → ↑CE ⊆-refl x ≡ x
↑CE⊆-refl {Γ} x = ↑CE-refl ⊆-refl x (λ v i → refl)

↑CE-＋ : (Γ Δ : Ctxt)
       → CE Γ
       → CE (Γ ＋ Δ)
↑CE-＋ Γ Δ f = ↑CE (⊆-＋ Γ Δ) f

≡→⊆ : {Γ Δ : Ctxt} → Γ ≡ Δ → Γ ⊆ Δ
≡→⊆ {Γ} {Δ} refl = ⊆-refl

⋆Form : {Γ Δ : Ctxt} → Γ ≡ Δ → Form Γ → Form Δ
⋆Form {Γ} {Δ} e f = subst Form e f -- ↑ (≡→⊆ e) f

⋆Res : {Γ Δ : Ctxt} → Γ ≡ Δ → Res Γ → Res Δ
⋆Res {Γ} {Δ} e r = subst Res e r -- ↑ᵣ (≡→⊆ e) r

⋆Interval : {Γ Δ : Ctxt} → Γ ≡ Δ → Interval Γ → Interval Δ
⋆Interval {Γ} {Δ} e i = subst Interval e i -- ↑ᵣ (≡→⊆ e) r

⋆CE : {Γ Δ : Ctxt} → Γ ≡ Δ → CE Γ → CE Δ
⋆CE {Γ} {Δ} e a = subst CE e a -- ↑CE (≡→⊆ e) a

⋆Sub : {Γ Δ : Ctxt} → Γ ≡ Δ → Sub Γ → Sub Δ
⋆Sub {Γ} {Δ} e s = subst Sub e s

mutual
  _⨾_ : {Γ : Ctxt} (c : ℂ Γ) (d : ℂℂ c) → ℂ Γ
  ≡ℂtxt⨾ : {Γ : Ctxt} (c : ℂ Γ) (d : ℂℂ c) → ℂtxt {ℂtxt {Γ} c} d ≡ ℂtxt {Γ} (c ⨾ d)

  -- to allow more convenient rules that can act on hyps in the middle
  c ⨾ ℂ⟨⟩ = c
  c ⨾ ℂx d f a = ℂx (c ⨾ d) (⋆Form (≡ℂtxt⨾ c d) f) (⋆CE (≡ℂtxt⨾ c d) a)
  c ⨾ ℂv d v = ℂv (c ⨾ d) v

  ≡ℂtxt⨾ {Γ} c ℂ⟨⟩ = refl
  ≡ℂtxt⨾ {Γ} c (ℂx d f a) = ≡ℂtxt⨾ c d
  ≡ℂtxt⨾ {Γ} c (ℂv d v) = cong (λ z → z ، v) (≡ℂtxt⨾ c d)

{--
⊆⨾ : {Γ : Ctxt} (c : ℂ Γ) (d : ℂℂ c) → ℂtxt {ℂtxt {Γ} c} d ⊆ ℂtxt {Γ} (c ⨾ d) -- they're actually equal
⊆⨾ {Γ} c ℂ⟨⟩ {u} i = i
⊆⨾ {Γ} c (ℂx d f a) {u} i = ⊆⨾ c d i
⊆⨾ {Γ} c (ℂv d v) {.v} (∈Ctxt0 .(ℂtxt d)) = ∈Ctxt0 _
⊆⨾ {Γ} c (ℂv d v) {u} (∈CtxtS .v i) = ∈CtxtS v (⊆⨾ c d i)
--}

⊆⨾ : {Γ : Ctxt} (c : ℂ Γ) (d : ℂℂ c) → ℂtxt {Γ} c ⊆ ℂtxt {Γ} (c ⨾ d)
⊆⨾ {Γ} c ℂ⟨⟩ {u} i = i
⊆⨾ {Γ} c (ℂx d f a) {u} i = ⊆⨾ c d i
⊆⨾ {Γ} c (ℂv d v) {u} i = ∈CtxtS v (⊆⨾ c d i)

ℂ⊆ : {Γ : Ctxt} (c : ℂ Γ) (d : ℂℂ c) → ℂtxt {Γ} c ⊆ ℂtxt {ℂtxt {Γ} c} d
ℂ⊆ {Γ} c ℂ⟨⟩ {u} i = i
ℂ⊆ {Γ} c (ℂx d f a) {u} i = ℂ⊆ c d i
ℂ⊆ {Γ} c (ℂv d v) {u} i = ∈CtxtS v (ℂ⊆ c d i)

{--
Form⨾ : (Γ Δ : ℂ) → Form (ℂtxt Γ) → Form (ℂtxt (Γ ⨾ Δ))
Form⨾ Γ ℂ⟨⟩ f = f
Form⨾ Γ (ℂx Δ x x₁) f = Form⨾ Γ Δ f
Form⨾ Γ (ℂv Δ x) f = ↑₀ (Form⨾ Γ Δ f)

ℂtxt⨾ : (Γ Δ : ℂ) → ℂtxt (Γ ⨾ Δ) ≡ ℂtxt Γ ＋ ℂtxt Δ
ℂtxt⨾ Γ ℂ⟨⟩ = refl
ℂtxt⨾ Γ (ℂx Δ x x₁) = ℂtxt⨾ Γ Δ
ℂtxt⨾ Γ (ℂv Δ x) = cong (λ z → z ، x) (ℂtxt⨾ Γ Δ)
--}

≡ℂtxt⨾⨾ : {Γ : Ctxt} (a b : ℂ Γ) (c : ℂℂ a) (d : ℂℂ b)
        → ℂtxt c ≡ ℂtxt d
        → ℂtxt (a ⨾ c) ≡ ℂtxt (b ⨾ d)
≡ℂtxt⨾⨾ {Γ} a b c d q =
  trans (sym (≡ℂtxt⨾ a c)) (trans q (≡ℂtxt⨾ b d))

⋆Form-refl : {Γ : Ctxt} (A : Form Γ)
           → ⋆Form refl A ≡ A
⋆Form-refl {Γ} A = refl --↑⊆-refl A

⋆Res-refl : {Γ : Ctxt} (r : Res Γ)
          → ⋆Res refl r ≡ r
⋆Res-refl {Γ} r = refl --↑ᵣ⊆-refl r

sat-ctxt-annot-*subst : (M  : Model₀)
                        (b  : Ctxt)
                        (c  : Ctxt)
                        (d  : Ctxt)
                        (e  : c ≡ d)
                        (e₁ : b ≡ c)
                        (e₂ : b ≡ d)
                        (s  : Sub c)
                        (f  : Form b)
                        (a  : CE b)
                      → sat-ctxt-annot {c} (⋆Form e₁ f) (⋆CE e₁ a) (M ≔ₛ s)
                      → sat-ctxt-annot {d} (⋆Form e₂ f) (⋆CE e₂ a) (M ≔ₛ ⋆Sub e s)
sat-ctxt-annot-*subst M b .b .b refl refl refl s f a h = h

،-inj : {Γ Δ : Ctxt} {v : 𝕍} → Γ ، v ≡ Δ ، v → Γ ≡ Δ
،-inj {Γ} {.Γ} {v} refl = refl

Sub،→-⋆Sub : {Γ Δ : Ctxt} {v : 𝕍} (e : Γ ، v ≡ Δ ، v) (s : Sub (Γ ، v))
          → Sub،→ (⋆Sub e s)
          ≡ ⋆Sub (،-inj e) (Sub،→ s)
Sub،→-⋆Sub {Γ} {.Γ} {v} refl s = refl

sat-⋆Sub : (M : Model₀) {Γ Δ : Ctxt} (e : Γ ≡ Δ) (s : Sub Γ) (r : Res Γ) (A : Form Γ)
          → ((M ≔ₛ ⋆Sub e s) ≔ₜ (⟦ ⋆Res e r ⟧ᵣ ⋆Sub e s))  ⊨ ⋆Form e A
          → ((M ≔ₛ s) ≔ₜ (⟦ r ⟧ᵣ s)) ⊨ A
sat-⋆Sub M {Γ} {.Γ} refl s r A h = h
--  subst₂ (λ a b → ((M ≔ₛ s) ≔ₜ (⟦ a ⟧ᵣ s)) ⊨ b) (⋆Res-refl r) (⋆Form-refl A) h

sat-ctxt-annot-⋆Sub : (M : Model₀) {Γ Δ : Ctxt} (e : Γ ≡ Δ) (s : Sub Γ) (r : CE Γ) (A : Form Γ)
                    → sat-ctxt-annot (⋆Form e A) (⋆CE e r) (M ≔ₛ ⋆Sub e s)
                    → sat-ctxt-annot A r (M ≔ₛ s)
sat-ctxt-annot-⋆Sub M {Γ} {.Γ} refl s r A h = h

∈Ctxt⟨⟩ : {u : 𝕍} → ¬ ∈Ctxt u ⟨⟩
∈Ctxt⟨⟩ {u} ()

⊆⟨⟩ : {Γ : Ctxt}
    → Γ ⊆ ⟨⟩
    → Γ ≡ ⟨⟩
⊆⟨⟩ {⟨⟩} e = refl
⊆⟨⟩ {Γ ، U} e = ⊥-elim (∈Ctxt⟨⟩ (e (∈Ctxt0 Γ)))

↓Sub⨾ : {Γ : Ctxt} (c : ℂ Γ) (d : ℂℂ c)
      → ℂSub (c ⨾ d)
      → ℂSub c
↓Sub⨾ {Γ} c ℂ⟨⟩ s = s
↓Sub⨾ {Γ} c (ℂx d f a) s = ↓Sub⨾ c d s
↓Sub⨾ {Γ} c (ℂv d v) (s ⹁ .v ∶ u) = ↓Sub⨾ c d s

⋆Sub⹁∶ : {Γ Δ : Ctxt} {v : 𝕍} (e : Γ ، v ≡ Δ ، v) (s : Sub Γ) (u : ⟦𝕍⟧ v)
       → ⋆Sub e (s ⹁ v ∶ u) ≡ ⋆Sub (،-inj e) s ⹁ v ∶ u
⋆Sub⹁∶ {Γ} {.Γ} {v} refl s u = refl

⋆Res-↑ᵣ⨾′ : (Γ Δ Ψ : Ctxt) (r : Res Γ) (v : 𝕍)
            (e : Δ ، v ≡ Ψ ، v)
            (s : Γ ⊆ Δ)
          → ⋆Res e (↑ᵣ₀ (↑ᵣ s r))
          ≡ ↑ᵣ₀ (⋆Res (،-inj e) (↑ᵣ s r))
⋆Res-↑ᵣ⨾′ Γ Δ Ψ r v refl s = refl

⋆Res-↑ᵣ⨾ : (Γ : ℂ₀) (Δ : ℂℂ Γ) (A : ℂForm Γ) (r : ℂRes Γ)
           (e : ℂtxt (ℂe Γ A r ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ))
         → ⋆Res e (↑ᵣ (⊆⨾ (ℂe Γ A r) Δ) r) ≡ ↑ᵣ (⊆⨾ Γ Δ) r
⋆Res-↑ᵣ⨾ Γ ℂ⟨⟩ A r refl = refl
⋆Res-↑ᵣ⨾ Γ (ℂx Δ f a) A r e = ⋆Res-↑ᵣ⨾ Γ Δ A r e
⋆Res-↑ᵣ⨾ Γ (ℂv Δ v) A r e =
  trans (trans (cong (⋆Res e) (↑ᵣ-trans (⊆⨾ (ℂe Γ A r) (ℂv Δ v)) (⊆⨾ (ℂe Γ A r) Δ) ⊆₀ r (λ v i → refl)))
               (trans (⋆Res-↑ᵣ⨾′ (ℂtxt Γ) (ℂtxt (ℂe Γ A r ⨾ Δ)) (ℂtxt (Γ ⨾ Δ)) r v e (⊆⨾ (ℂe Γ A r) Δ))
                      (cong ↑ᵣ₀ (⋆Res-↑ᵣ⨾ Γ Δ A r (،-inj e)))))
        (sym (↑ᵣ-trans (⊆⨾ Γ (ℂv Δ v)) (⊆⨾ Γ Δ) ⊆₀ r (λ v i → refl)))

⋆Form-↑⨾′ : (Γ Δ Ψ : Ctxt) (B : Form Γ) (v : 𝕍)
            (e : Δ ، v ≡ Ψ ، v)
            (s : Γ ⊆ Δ)
          → ⋆Form e (↑₀ (↑ s B))
          ≡ ↑₀ (⋆Form (،-inj e) (↑ s B))
⋆Form-↑⨾′ Γ Δ Ψ B v refl s = refl

⋆Form-↑⨾ : (Γ : ℂ₀) (Δ : ℂℂ Γ) (A : ℂForm Γ) (r : ℂRes Γ) (B : ℂForm Γ)
           (e : ℂtxt (ℂe Γ A r ⨾ Δ) ≡ ℂtxt (Γ ⨾ Δ))
         → ⋆Form e (↑ (⊆⨾ (ℂe Γ A r) Δ) B) ≡ ↑ (⊆⨾ Γ Δ) B
⋆Form-↑⨾ Γ ℂ⟨⟩ A r B refl = refl
⋆Form-↑⨾ Γ (ℂx Δ f a) A r B e = ⋆Form-↑⨾ Γ Δ A r B e
⋆Form-↑⨾ Γ (ℂv Δ v) A r B e =
  trans (trans (cong (⋆Form e) (↑-trans (⊆⨾ (ℂe Γ A r) (ℂv Δ v)) (⊆⨾ (ℂe Γ A r) Δ) ⊆₀ B (λ v i → refl)))
               (trans (⋆Form-↑⨾′ (ℂtxt Γ) (ℂtxt (ℂe Γ A r ⨾ Δ)) (ℂtxt (Γ ⨾ Δ)) B v e (⊆⨾ (ℂe Γ A r) Δ))
                      (cong ↑₀ (⋆Form-↑⨾ Γ Δ A r B (،-inj e)))))
        (sym (↑-trans (⊆⨾ Γ (ℂv Δ v)) (⊆⨾ Γ Δ) ⊆₀ B (λ v i → refl)))

⋆CEᵣ : {Γ Δ : Ctxt} (e : Γ ≡ Δ) (r : Res Γ)
     → ⋆CE e (CEr r) ≡ CEr (⋆Res e r)
⋆CEᵣ {Γ} {Δ} refl r = refl

⋆CEᵤ : {Γ Δ : Ctxt} (e : Γ ≡ Δ)
     → ⋆CE e CEu ≡ CEu
⋆CEᵤ {Γ} {Δ} refl = refl

⋆CEᵢ : {Γ Δ : Ctxt} (e : Γ ≡ Δ) (i : Interval Γ)
     → ⋆CE e (CEi i) ≡ CEi (⋆Interval e i)
⋆CEᵢ {Γ} {Δ} refl i = refl

⋆Form-⊆ : (c d g : Ctxt)
          (e : c ⊆ d)
          (f : d ≡ g)
          (v : 𝕍)
          (A : Form c)
        → ⋆Form (cong (λ z → z ، v) f) (↑ (λ i → ∈CtxtS v (e i)) A) ≡ ↑₀ (⋆Form f (↑ e A))
⋆Form-⊆ c d g e refl v A = 𝕀
  where
  𝕀 : ↑ (λ i → ∈CtxtS v (e i)) A ≡ ↑₀ (↑ e A)
  𝕀 = ↑-trans (λ i → ∈CtxtS v (e i)) e ⊆₀ A (λ _ _ → refl)

⋆Res-⊆ : (c d g : Ctxt)
         (e : c ⊆ d)
         (f : d ≡ g)
         (v : 𝕍)
         (x : Res c)
       → ⋆Res (cong (λ z → z ، v) f) (↑ᵣ (λ i → ∈CtxtS v (e i)) x) ≡ ↑ᵣ₀ (⋆Res f (↑ᵣ e x))
⋆Res-⊆ c d g e refl v x = 𝕀
  where
  𝕀 : ↑ᵣ (λ i → ∈CtxtS v (e i)) x ≡ ↑ᵣ₀ (↑ᵣ e x)
  𝕀 = ↑ᵣ-trans (λ i → ∈CtxtS v (e i)) e ⊆₀ x (λ _ _ → refl)

⋆CE-⊆ : (c d g : Ctxt)
        (e : c ⊆ d)
        (f : d ≡ g)
        (v : 𝕍)
        (x : CE c)
      → ⋆CE (cong (λ z → z ، v) f) (↑CE (λ i → ∈CtxtS v (e i)) x) ≡ ↑CE₀ (⋆CE f (↑CE e x))
⋆CE-⊆ c d g e refl v x = 𝕀
  where
  𝕀 : ↑CE (λ i → ∈CtxtS v (e i)) x ≡ ↑CE₀ (↑CE e x)
  𝕀 = ↑CE-trans (λ i → ∈CtxtS v (e i)) e ⊆₀ x (λ _ _ → refl)

⋆Form-ℂ⊆ : (c : ℂ₀) (d : ℂℂ c)
           (A : ℂForm c)
         → ⋆Form (≡ℂtxt⨾ c d) (↑ (ℂ⊆ c d) A) ≡ ↑ (⊆⨾ c d) A
⋆Form-ℂ⊆ c ℂ⟨⟩ A = refl
⋆Form-ℂ⊆ c (ℂx d f a) A = ⋆Form-ℂ⊆ c d A
⋆Form-ℂ⊆ c (ℂv d v) A =
  trans (trans (⋆Form-⊆ (ℂtxt c) (ℂtxt d) (ℂtxt(c ⨾ d)) (ℂ⊆ c d) (≡ℂtxt⨾ c d) v A)
               (cong ↑₀ (⋆Form-ℂ⊆ c d A)))
        (sym (↑-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ A (λ x i → refl)))

⋆Res-ℂ⊆ : (c : ℂ₀) (d : ℂℂ c)
          (x : ℂRes c)
        → ⋆Res (≡ℂtxt⨾ c d) (↑ᵣ (ℂ⊆ c d) x) ≡ ↑ᵣ (⊆⨾ c d) x
⋆Res-ℂ⊆ c ℂ⟨⟩ x = refl
⋆Res-ℂ⊆ c (ℂx d f a) x = ⋆Res-ℂ⊆ c d x
⋆Res-ℂ⊆ c (ℂv d v) x =
  trans (trans (⋆Res-⊆ (ℂtxt c) (ℂtxt d) (ℂtxt(c ⨾ d)) (ℂ⊆ c d) (≡ℂtxt⨾ c d) v x)
               (cong ↑ᵣ₀ (⋆Res-ℂ⊆ c d x)))
        (sym (↑ᵣ-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ x (λ x i → refl)))

⋆CE-ℂ⊆ : (c : ℂ₀) (d : ℂℂ c)
         (x : ℂCE c)
       → ⋆CE (≡ℂtxt⨾ c d) (↑CE (ℂ⊆ c d) x) ≡ ↑CE (⊆⨾ c d) x
⋆CE-ℂ⊆ c ℂ⟨⟩ x = refl
⋆CE-ℂ⊆ c (ℂx d f a) x = ⋆CE-ℂ⊆ c d x
⋆CE-ℂ⊆ c (ℂv d v) x =
  trans (trans (⋆CE-⊆ (ℂtxt c) (ℂtxt d) (ℂtxt(c ⨾ d)) (ℂ⊆ c d) (≡ℂtxt⨾ c d) v x)
               (cong ↑CE₀ (⋆CE-ℂ⊆ c d x)))
        (sym (↑CE-trans (⊆⨾ c (ℂv d v)) (⊆⨾ c d) ⊆₀ x (λ x i → refl)))

⋆Sub، : (c d : Ctxt)
        (u : 𝕍)
        (v : ⟦𝕍⟧ u)
        (x : c ، u ≡ d ، u)
        (s : Sub c)
      → ⋆Sub x (s ⹁ u ∶ v) ≡ ⋆Sub (،-inj x) s ⹁ u ∶ v
⋆Sub، c d u v refl s = refl

inter-cond↑I₀ : (M : Model₀)
                {c : Ctxt}
                (u : 𝕍)
                (v : ⟦𝕍⟧ u)
                (w : 𝕎)
                (i : Interval c)
                (s : Sub c)
              → inter-cond (M ≔ₛ (s ⹁ u ∶ v)) w (↑I₀ i)
              → inter-cond (M ≔ₛ s) w i
inter-cond↑I₀ M {c} u v w ［ x , x₁ ］ s (h , q) = subst (λ x → x ≼ w) (⟦↑ᵣ₀⟧ᵣ x s u v) h , subst (λ x → w ≼ x) (⟦↑ᵣ₀⟧ᵣ x₁ s u v) q
inter-cond↑I₀ M {c} u v w ［ x , x₁ ） s (h , q) = subst (λ x → x ≼ w) (⟦↑ᵣ₀⟧ᵣ x s u v) h , subst (λ x → w ≺ x) (⟦↑ᵣ₀⟧ᵣ x₁ s u v) q
inter-cond↑I₀ M {c} u v w （ x , x₁ ］ s (h , q) = subst (λ x → x ≺ w) (⟦↑ᵣ₀⟧ᵣ x s u v) h , subst (λ x → w ≼ x) (⟦↑ᵣ₀⟧ᵣ x₁ s u v) q
inter-cond↑I₀ M {c} u v w （ x , x₁ ） s (h , q) = subst (λ x → x ≺ w) (⟦↑ᵣ₀⟧ᵣ x s u v) h , subst (λ x → w ≺ x) (⟦↑ᵣ₀⟧ᵣ x₁ s u v) q

inter-cond↑I₀′ : {c : Ctxt}
                 (M : Model c)
                 (u : 𝕍)
                 (v : ⟦𝕍⟧ u)
                 (w : 𝕎)
                 (i : Interval c)
               → inter-cond (M ≔⟨ u ⟩ v) w (↑I₀ i)
               → inter-cond M w i
inter-cond↑I₀′ {c} M u v w ［ x , x₁ ］ (h , q) = subst (λ x → x ≼ w) (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v) h , subst (λ x → w ≼ x) (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v) q
inter-cond↑I₀′ {c} M u v w ［ x , x₁ ） (h , q) = subst (λ x → x ≼ w) (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v) h , subst (λ x → w ≺ x) (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v) q
inter-cond↑I₀′ {c} M u v w （ x , x₁ ］ (h , q) = subst (λ x → x ≺ w) (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v) h , subst (λ x → w ≼ x) (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v) q
inter-cond↑I₀′ {c} M u v w （ x , x₁ ） (h , q) = subst (λ x → x ≺ w) (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v) h , subst (λ x → w ≺ x) (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v) q

inter-cond↑I₀′-rev : {c : Ctxt}
                     (M : Model c)
                     (u : 𝕍)
                     (v : ⟦𝕍⟧ u)
                     (w : 𝕎)
                     (i : Interval c)
                   → inter-cond M w i
                   → inter-cond (M ≔⟨ u ⟩ v) w (↑I₀ i)
inter-cond↑I₀′-rev {c} M u v w ［ x , x₁ ］ (h , q) = subst (λ x → x ≼ w) (sym (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v)) h , subst (λ x → w ≼ x) (sym (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v)) q
inter-cond↑I₀′-rev {c} M u v w ［ x , x₁ ） (h , q) = subst (λ x → x ≼ w) (sym (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v)) h , subst (λ x → w ≺ x) (sym (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v)) q
inter-cond↑I₀′-rev {c} M u v w （ x , x₁ ］ (h , q) = subst (λ x → x ≺ w) (sym (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v)) h , subst (λ x → w ≼ x) (sym (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v)) q
inter-cond↑I₀′-rev {c} M u v w （ x , x₁ ） (h , q) = subst (λ x → x ≺ w) (sym (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) u v)) h , subst (λ x → w ≺ x) (sym (⟦↑ᵣ₀⟧ᵣ x₁ (Model.subΓ M) u v)) q


-- An agent is correct if its connections to all other nodes are always correct
Correct : {Γ : Ctxt} → Agent Γ → Form Γ
Correct a = □ (∀ₐ (𝕒 (atCorrect (FaultCorrect (↑ᵢ₀ a) 𝕒0))))

-- Meaning of the B operator

◆-semantics→ : {Γ : Ctxt} (M : Model Γ) (F : Form Γ)
               → M ⊨ ◆ F
               → ∃ (λ t → t ≼ Model.w M × (M ≔ₜ t) ⊨ F)
◆-semantics→ {Γ} M F (t , c₁ , c₂ , h) = t , c₁ , c₂

◆-semantics← : {Γ : Ctxt} (M : Model Γ) (F : Form Γ)
               → ∃ (λ t → t ≼ Model.w M × (M ≔ₜ t) ⊨ F)
               → M ⊨ ◆ F
◆-semantics← {Γ} M F (t , c , h) = t , c , h , λ _ _ _ → lift tt

-- Meaning of the ◇ operator

◇-semantics→ : {Γ : Ctxt} (M : Model Γ) (F : Form Γ)
             → M ⊨ ◇ F
             → ∃ (λ t → (Model.w M) ≼ t × (M ≔ₜ t) ⊨ F)
◇-semantics→ {Γ} M F (t , c₁ , c₂ , h) = t , c₁ , c₂

◇-semantics← : {Γ : Ctxt} (M : Model Γ) (F : Form Γ)
             → ∃ (λ t → (Model.w M) ≼ t × (M ≔ₜ t) ⊨ F)
             → M ⊨ ◇ F
◇-semantics← {Γ} M F (t , c , h) = t , c , h , λ _ _ _ → lift tt

-- Meaning of the ◇↓ operator

◇↓-semantics→ : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
              → M ⊨ ◇↓ r F
              → ∃ (λ t → (Model.w M) ≼ t × t ≼ (Model.w M · (⟦ r ⟧ᵣ· M)) × (M ≔ₜ t) ⊨ F)
◇↓-semantics→ {Γ} M r F (t , c₁ , (lift c₂ , c₃) , h) =
  t , c₁ ,
  ≼-trans c₂
          (·-cong-≼ ≼-refl (subst (λ x → x ≼ (⟦ r ⟧ᵣ· M))
                                  (sym (⟦↑ᵣ₁⟧ᵣ r (Model.subΓ M) 𝕍ℝ (Model.w M) 𝕍ℝ t))
                                  ≼-refl)) ,
  ⊨-↑₁→ {_} {M ≔ₜ t} {F} {𝕍ℝ} (Model.w M) {𝕍ℝ} t c₃

◇↓-semantics← : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
              → ∃ (λ t → (Model.w M) ≼ t × t ≼ (Model.w M · (⟦ r ⟧ᵣ· M)) × (M ≔ₜ t) ⊨ F)
              → M ⊨ ◇↓ r F
◇↓-semantics← {Γ} M r F (t , c₁ , c₂ , h) =
  t , c₁ ,
  ((lift (≼-trans c₂ (·-cong-≼ ≼-refl (subst (λ x → (⟦ r ⟧ᵣ· M) ≼ x)
                                             (sym (⟦↑ᵣ₁⟧ᵣ r (Model.subΓ M) 𝕍ℝ (Model.w M) 𝕍ℝ t))
                                             ≼-refl)))) ,
   (→⊨-↑₁ {_} {M ≔ₜ t} {F} {𝕍ℝ} (Model.w M) {𝕍ℝ} t h)) ,
  (λ _ _ _ → lift tt)

-- Meaning of the ◇↓◆ operator

◇↓◆-semantics→ : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
                → M ⊨ ◇↓◆ r F
                → ∃ (λ t → t ≼ (Model.w M · (⟦ r ⟧ᵣ· M)) × (M ≔ₜ t) ⊨ F)
◇↓◆-semantics→ {Γ} M r F h with ◇↓-semantics→ M r (◆ F) h
... | t , c₁ , c₂ , q with ◆-semantics→ (M ≔ₜ t) F q
... | t′ , c₃ , z = t′ , ≼-trans c₃ c₂ , z

◇↓◆-semantics← : {Γ : Ctxt} (M : Model Γ) (r : Res Γ) (F : Form Γ)
                → ∃ (λ t → t ≼ (Model.w M · (⟦ r ⟧ᵣ· M)) × (M ≔ₜ t) ⊨ F)
                → M ⊨ ◇↓◆ r F
◇↓◆-semantics← {Γ} M r F (t , c , h) =
  ◇↓-semantics← M r (◆ F)
                (Model.w M · (⟦ r ⟧ᵣ· M) ,
                 ·-cong-≼-r₁ _ _ _ ≼-refl ,
                 ≼-refl ,
                 ◆-semantics← (M ≔ₜ (Model.w M · (⟦ r ⟧ᵣ· M))) F (t , c , h))

¬Ｆ-semantics→ : {Γ : Ctxt} (M : Model Γ) (F : Form (Γ ، 𝕍ℝ))
               → M ⊨ (¬· (Ｆ F))
               → M ⊨ (Ｆ (¬· F))
¬Ｆ-semantics→ {Γ} M F h = h

-- We show the equivalence between Ｙ (◆ A) and ◆ (Ｙ A)

Ｙ◆→◆Ｙ : {Γ : Ctxt} (M : Model Γ) (A : Form Γ)
        → M ⊨ Ｙ (◆ A)
        → M ⊨ ◆ (Ｙ A)
Ｙ◆→◆Ｙ {Γ} M A (t , c₁ , t′ , c₂ , c₃ , c₄) with ≼→≡⊎◃ₗ c₂
... | inj₁ refl = Model.w M , ≼-refl , (t′ , c₁ , c₃) , (λ _ _ _ → lift tt)
... | inj₂ (u , d₁ , d₂) = u , ≼-trans d₂ (◃→≼ c₁) , (t′ , d₁ , c₃) , (λ _ _ _ → lift tt)

◆Ｙ→Ｙ◆ : {Γ : Ctxt} (M : Model Γ) (A : Form Γ)
        → M ⊨ ◆ (Ｙ A)
        → M ⊨ Ｙ (◆ A)
◆Ｙ→Ｙ◆ {Γ} M A (t , c₁ , (t′ , c₂ , c₃) , c₄)
  with ≼→≡⊎◃ᵣ {t} {Model.w M} c₁
... | inj₁ refl = t′ , c₂ , t′ , ≼-refl , c₃ , λ _ _ _ → lift tt
... | inj₂ (w , t≼w , w◃M) = w , w◃M , t′ , ≼-trans (◃→≼ c₂) t≼w , c₃ , λ _ _ _ → lift tt

-- We show the equivalence between Ｏ (◇ A) and ◇ (Ｏ A)

Ｏ◇→◇Ｏ : {Γ : Ctxt} (M : Model Γ) (A : Form Γ)
        → M ⊨ Ｏ (◇ A)
        → M ⊨ ◇ (Ｏ A)
Ｏ◇→◇Ｏ {Γ} M A (t , c₁ , t′ , c₂ , c₃ , c₄) with ≼→≡⊎◃ᵣ c₂
... | inj₁ refl = Model.w M , ≼-refl , (t , c₁ , c₃) , (λ _ _ _ → lift tt)
... | inj₂ (u , d₁ , d₂) = u , ≼-trans (◃→≼ c₁) d₁ , (t′ , d₂ , c₃) , (λ _ _ _ → lift tt)

◇Ｏ→Ｏ◇ : {Γ : Ctxt} (M : Model Γ) (A : Form Γ)
        → M ⊨ ◇ (Ｏ A)
        → M ⊨ Ｏ (◇ A)
◇Ｏ→Ｏ◇ {Γ} M A (t , c₁ , (t′ , c₂ , c₃) , c₄) with ≼→≡⊎◃ₗ c₁
... | inj₁ refl = t′ , c₂ , t′ , ≼-refl , c₃ , (λ _ _ _ → lift tt)
... | inj₂ (u , d₁ , d₂) = u , d₁ , t′ , ≼-trans d₂ (◃→≼ c₂) , c₃ , (λ _ _ _ → lift tt)

Sub⊆-⊆₀، : {Γ : Ctxt} {u : 𝕍} {v : ⟦𝕍⟧ u} {a : 𝕍} {b : ⟦𝕍⟧ a} {s : Sub Γ}
        → Sub⊆ ⊆₀، (s ⹁ u ∶ v) ((s ⹁ a ∶ b) ⹁ u ∶ v)
Sub⊆-⊆₀، {Γ} {u} {v} {a} {b} {s} {z} w i (∈Sub0 .s) = ∈Sub0 (s ⹁ a ∶ b)
Sub⊆-⊆₀، {Γ} {u} {v} {a} {b} {s} {z} w i (∈SubS .s .v i₁ j) = ∈SubS (s ⹁ a ∶ b) v (∈CtxtS a i₁) (∈SubS s b i₁ j)

→⊨-↑₀، : {Γ : Ctxt} {M : Model Γ} {u₁ : 𝕍} (v₁ : ⟦𝕍⟧ u₁) {u₂ : 𝕍} (v₂ : ⟦𝕍⟧ u₂) (F : Form (Γ ، u₂))
      → (M ≔ v₂) ⊨ F
      → ((M ≔⟨ u₁ ⟩ v₁) ≔ v₂) ⊨ (↑₀، F)
→⊨-↑₀، {Γ} {m} {u₁} v₁ {u₂} v₂ F h =
  →⊨-↑⊆ {Γ ، u₂} {Γ ، u₁ ، u₂} {m ≔ v₂} {F} (Model.subΓ ((m ≔⟨ u₁ ⟩ v₁) ≔ v₂)) ⊆₀، Sub⊆-⊆₀، h

⟦↑ᵣ₀،⟧ᵣ : {Γ : Ctxt} (s : Sub Γ) (u : 𝕍) (v : ⟦𝕍⟧ u) (x : 𝕍) (y : ⟦𝕍⟧ x) (r : Res (Γ ، x))
        → (⟦ ↑ᵣ₀، r ⟧ᵣ ((s ⹁ u ∶ v) ⹁ x ∶ y)) ≡ (⟦ r ⟧ᵣ (s ⹁ x ∶ y))
⟦↑ᵣ₀،⟧ᵣ {Γ} s u v x y r = ⟦⊆⟧ᵣ (s ⹁ x ∶ y) ⊆₀، ((s ⹁ u ∶ v) ⹁ x ∶ y) Sub⊆-⊆₀، r

inter-cond↑⊆← : {Γ Δ : Ctxt} {M : Model Γ}
                (w : 𝕎) (x : Interval Γ) (s : Sub Δ)
                (e : Γ ⊆ Δ)
              → Sub⊆ e (Model.subΓ M) s
              → inter-cond M w x
              → inter-cond (M ≔ₛ s) w (↑I e x)
inter-cond↑⊆← {Γ} {Δ} {M} w ［ x , x₁ ］ s e cond (h , q) =
  (subst (λ x → x ≼ w) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x)) h) ,
  (subst (λ x → w ≼ x) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁)) q)
inter-cond↑⊆← {Γ} {Δ} {M} w ［ x , x₁ ） s e cond (h , q) =
  (subst (λ x → x ≼ w) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x)) h) ,
  (subst (λ x → w ≺ x) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁)) q)
inter-cond↑⊆← {Γ} {Δ} {M} w （ x , x₁ ］ s e cond (h , q) =
  (subst (λ x → x ≺ w) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x)) h) ,
  (subst (λ x → w ≼ x) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁)) q)
inter-cond↑⊆← {Γ} {Δ} {M} w （ x , x₁ ） s e cond (h , q) =
  (subst (λ x → x ≺ w) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x)) h) ,
  (subst (λ x → w ≺ x) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁)) q)

sat-ctxt-annot↑⊆→ : {Γ Δ : Ctxt} {M : Model Γ}
                    (A : Form Γ) (x : CE Γ) (s : Sub Δ)
                    (e : Γ ⊆ Δ)
                  → Sub⊆ e (Model.subΓ M) s
                  → sat-ctxt-annot (↑ e A) (↑CE e x) (M ≔ₛ s)
                  → sat-ctxt-annot A x M
sat-ctxt-annot↑⊆→ {Γ} {Δ} {M} A (CEr r) s e cond h =
  ⊨-↑⊆→ {_} {_} {M ≔ₜ (⟦ r ⟧ᵣ· M)} {A} s e cond (subst (λ x → ((M ≔ₛ s) ≔ₜ x) ⊨ ↑ e A) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond r) h)
sat-ctxt-annot↑⊆→ {Γ} {Δ} {M} A CEu s e cond h =
  ⊨-↑⊆→ {_} {_} {M} {A} s e cond h
sat-ctxt-annot↑⊆→ {Γ} {Δ} {M} A (CEi x) s e cond h =
  λ w j → ⊨-↑⊆→ {_} {_} {M ≔ₜ w} {A} s e cond (h w (inter-cond↑⊆← w x s e cond j))

inter-cond↑⊆ : {Γ Δ : Ctxt} {M : Model Γ}
               (w : 𝕎) (x : Interval Γ) (s : Sub Δ)
               (e : Γ ⊆ Δ)
             → Sub⊆ e (Model.subΓ M) s
             → inter-cond (M ≔ₛ s) w (↑I e x)
             → inter-cond M w x
inter-cond↑⊆ {Γ} {Δ} {M} w ［ x , x₁ ］ s e cond (h , q) =
  (subst (λ x → x ≼ w) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x) h) ,
  (subst (λ x → w ≼ x) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁) q)
inter-cond↑⊆ {Γ} {Δ} {M} w ［ x , x₁ ） s e cond (h , q) =
  (subst (λ x → x ≼ w) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x) h) ,
  (subst (λ x → w ≺ x) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁) q)
inter-cond↑⊆ {Γ} {Δ} {M} w （ x , x₁ ］ s e cond (h , q) =
  (subst (λ x → x ≺ w) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x) h) ,
  (subst (λ x → w ≼ x) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁) q)
inter-cond↑⊆ {Γ} {Δ} {M} w （ x , x₁ ） s e cond (h , q) =
  (subst (λ x → x ≺ w) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x) h) ,
  (subst (λ x → w ≺ x) (⟦⊆⟧ᵣ (Model.subΓ M) e s cond x₁) q)

sat-ctxt-annot↑⊆ : {Γ Δ : Ctxt} {M : Model Γ}
                   (A : Form Γ) (x : CE Γ) (s : Sub Δ)
                   (e : Γ ⊆ Δ)
                 → Sub⊆ e (Model.subΓ M) s
                 → sat-ctxt-annot A x M
                 → sat-ctxt-annot (↑ e A) (↑CE e x) (M ≔ₛ s)
sat-ctxt-annot↑⊆ {Γ} {Δ} {M} A (CEr r) s e cond h =
  →⊨-↑⊆ {_} {_} {M ≔ₜ (⟦ ↑ᵣ e r ⟧ᵣ· (M ≔ₛ s))} {A} s e cond
    (subst (λ x → (M ≔ₜ x) ⊨ A) (sym (⟦⊆⟧ᵣ (Model.subΓ M) e s cond r)) h)
sat-ctxt-annot↑⊆ {Γ} {Δ} {M} A CEu s e cond h =
  →⊨-↑⊆ {_} {_} {M} {A} s e cond h
sat-ctxt-annot↑⊆ {Γ} {Δ} {M} A (CEi x) s e cond h =
  λ w j → →⊨-↑⊆ {_} {_} {M ≔ₜ w} {A} s e cond (h w (inter-cond↑⊆ w x s e cond j))

sat-ctxt-annot→sub-rev : {Γ : Ctxt} {m : Model Γ} {u : 𝕍}
                         (A : Form (Γ ، u)) (x : CE Γ)
                         (v : C⟦𝕍⟧ Γ u)
                       → sat-ctxt-annot (sub A (CSub،ₗ v)) x m
                       → sat-ctxt-annot A (↑CE₀ x) (m ≔ ⟦ u ، v ⟧c· m)
sat-ctxt-annot→sub-rev {Γ} {m} {u} A (CEr x) v h =
  subst (λ x → ((m ≔ ⟦ u ، v ⟧c· m) ≔ₜ x) ⊨ A)
        (sym (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ m) u (⟦ u ، v ⟧c· m)))
        (≔→sub-rev Γ A v h)
sat-ctxt-annot→sub-rev {Γ} {m} {u} A CEu v h = ≔→sub-rev Γ A v h
sat-ctxt-annot→sub-rev {Γ} {m} {u} A (CEi x) v h w c =
  ≔→sub-rev Γ A v (h w (inter-cond↑I₀′ m u (⟦ u ، v ⟧c· m) w x c))

sat-ctxt-annot→sub : {Γ : Ctxt} {m : Model Γ} {u : 𝕍}
                         (A : Form (Γ ، u)) (x : CE Γ)
                         (v : C⟦𝕍⟧ Γ u)
                       → sat-ctxt-annot A (↑CE₀ x) (m ≔ ⟦ u ، v ⟧c· m)
                       → sat-ctxt-annot (sub A (CSub،ₗ v)) x m
sat-ctxt-annot→sub {Γ} {m} {u} A (CEr x) v h =
  ≔→sub Γ A v (subst (λ x → ((m ≔ ⟦ u ، v ⟧c· m) ≔ₜ x) ⊨ A) (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ m) u (⟦ u ، v ⟧c· m)) h)
sat-ctxt-annot→sub {Γ} {m} {u} A CEu v h = ≔→sub Γ A v h
sat-ctxt-annot→sub {Γ} {m} {u} A (CEi x) v h w c =
  ≔→sub Γ A v (h w (inter-cond↑I₀′-rev m u (⟦ u ، v ⟧c· m) w x c))

⊨interval→inter-cond : (M : Model₀) (Γ : ℂ₀) (s : ℂSub Γ) (t : 𝕎) (r : ℂRes Γ) (i : ℂInterval Γ)
                     → ((M ≔ₛ s) ≔ₜ t) ⊨ interval r i
                     → inter-cond (M ≔ₛ s) (⟦ r ⟧ᵣ s) i
⊨interval→inter-cond M Γ s t r ［ x , x₁ ］ (lift h , lift q) = h , q
⊨interval→inter-cond M Γ s t r ［ x , x₁ ） (lift h , lift q) = h , q
⊨interval→inter-cond M Γ s t r （ x , x₁ ］ (lift h , lift q) = h , q
⊨interval→inter-cond M Γ s t r （ x , x₁ ） (lift h , lift q) = h , q

{--
-- We've also proved this as a rule
¬·◇↓∧◇↓◆→◆· : {Γ : Ctxt} (M : Model Γ) (Δ : Res Γ) (A : Form Γ)
            → M ⊨ □↓ Δ (¬· A)
            → M ⊨ ◇↓◆ Δ A
            → M ⊨ ◆· A -- strict ◆
¬·◇↓∧◇↓◆→◆· {Γ} M Δ A h (t , c₁ , (lift c₂ , t′ , c₃ , c₄ , c₅) , c₆) with 𝟘⊎◃ (Model.w M)
¬·◇↓∧◇↓◆→◆· {Γ} M Δ A h (t , c₁ , (lift c₂ , t′ , c₃ , c₄ , c₅) , c₆) | inj₁ refl =
  ⊥-elim (h (t′ ,
             𝟘≼ ,
             (λ x → x (lift (≼-trans c₃ (≼-trans c₂ (subst₂ (λ x y → 𝟘 · x ≼ 𝟘 · y)
                                                            (sym (⟦↑ᵣ₁⟧ᵣ Δ (Model.subΓ M) 𝕍ℝ 𝟘 𝕍ℝ t))
                                                            (sym (⟦↑ᵣ₁⟧ᵣ Δ (Model.subΓ M) 𝕍ℝ 𝟘 𝕍ℝ t′))
                                                            ≼-refl))))
                      (→⊨-↑₁ {_} {M ≔ₜ t′} {A} {𝕍ℝ} 𝟘 {𝕍ℝ} t′ (⊨-↑₁→ {_} {M ≔ₜ t′} {A} {𝕍ℝ} 𝟘 {𝕍ℝ} t c₄))) ,
             (λ _ _ _ → lift tt)))
¬·◇↓∧◇↓◆→◆· {Γ} M Δ A h (t , c₁ , (lift c₂ , t′ , c₃ , c₄ , c₅) , c₆) | inj₂ (u , d) =
  u , d , t′ , h₁ , ⊨-↑₁→ {_} {M ≔ₜ t′} {A} {𝕍ℝ} (Model.w M) {𝕍ℝ} t c₄ , (λ _ _ _ → lift tt)
  where
  h₁ : t′ ≼ u
  h₁ with ≼⊎≺ c₃ (≼-trans (◃→≼ d) c₁)
  ... | inj₁ q = q
  ... | inj₂ q with ◃∧≺→≼ d q
  ... | q′ = ⊥-elim (h (t′ ,
                        q′ ,
                        (λ x → x (lift (≼-trans c₃ (≼-trans c₂ (subst₂ (λ x y → Model.w M · x ≼ Model.w M · y)
                                                               (sym (⟦↑ᵣ₁⟧ᵣ Δ (Model.subΓ M) 𝕍ℝ (Model.w M) 𝕍ℝ t))
                                                               (sym (⟦↑ᵣ₁⟧ᵣ Δ (Model.subΓ M) 𝕍ℝ (Model.w M) 𝕍ℝ t′))
                                                               ≼-refl))))
                                 (→⊨-↑₁ {_} {M ≔ₜ t′} {A} {𝕍ℝ} (Model.w M) {𝕍ℝ} t′ (⊨-↑₁→ {_} {M ≔ₜ t′} {A} {𝕍ℝ} (Model.w M) {𝕍ℝ} t c₄))) ,
                        (λ _ _ _ → lift tt)))
--}

sat-ctxt-annot∧ : {Γ : Ctxt} (f g : Form Γ) (a : CE Γ) (M : Model Γ)
                → sat-ctxt-annot f a M
                → sat-ctxt-annot g a M
                → sat-ctxt-annot (f ∧· g) a M
sat-ctxt-annot∧ {Γ} f g (CEr x) M h q = h , q
sat-ctxt-annot∧ {Γ} f g CEu M h q = h , q
sat-ctxt-annot∧ {Γ} f g (CEi x) M h q = λ w z → h w z , q w z

sat-ctxt-annot∨ₗ : {Γ : Ctxt} (f g : Form Γ) (a : CE Γ) (M : Model Γ)
                 → sat-ctxt-annot f a M
                 → sat-ctxt-annot (f ∨· g) a M
sat-ctxt-annot∨ₗ {Γ} f g (CEr x) M h = inj₁ h
sat-ctxt-annot∨ₗ {Γ} f g CEu M h = inj₁ h
sat-ctxt-annot∨ₗ {Γ} f g (CEi x) M h = λ w z → inj₁ (h w z)

sat-ctxt-annot∨ᵣ : {Γ : Ctxt} (f g : Form Γ) (a : CE Γ) (M : Model Γ)
                 → sat-ctxt-annot g a M
                 → sat-ctxt-annot (f ∨· g) a M
sat-ctxt-annot∨ᵣ {Γ} f g (CEr x) M h = inj₂ h
sat-ctxt-annot∨ᵣ {Γ} f g CEu M h = inj₂ h
sat-ctxt-annot∨ᵣ {Γ} f g (CEi x) M h = λ w z → inj₂ (h w z)

{--
-- Does not hold
sat-ctxt-annot∨→ : {Γ : Ctxt} (f g : Form Γ) (a : CE Γ) (M : Model Γ)
                 → sat-ctxt-annot (f ∨· g) a M
                 → (sat-ctxt-annot f a M ⊎ sat-ctxt-annot g a M)
sat-ctxt-annot∨→ {Γ} f g (CEr x) M (inj₁ y) = inj₁ y
sat-ctxt-annot∨→ {Γ} f g (CEr x) M (inj₂ y) = inj₂ y
sat-ctxt-annot∨→ {Γ} f g CEu M (inj₁ y) = inj₁ y
sat-ctxt-annot∨→ {Γ} f g CEu M (inj₂ y) = inj₂ y
sat-ctxt-annot∨→ {Γ} f g (CEi x) M h = {!!}
--}

sat-ctxt-annot⊤ : {Γ : Ctxt} (a : CE Γ) (M : Model Γ)
                → sat-ctxt-annot ⊤· a M
sat-ctxt-annot⊤ {Γ} (CEr x) M = lift tt
sat-ctxt-annot⊤ {Γ} CEu M = lift tt
sat-ctxt-annot⊤ {Γ} (CEi x) M = λ _ _ → lift tt

sat-ctxt-annot＝ : {Γ : Ctxt} (t₁ t₂ : Res Γ) (a : CE Γ) (M : Model Γ)
                → sat-ctxt-annot (t₁ ＝ t₂) CEu M
                → sat-ctxt-annot (t₁ ＝ t₂) a M
sat-ctxt-annot＝ {Γ} t₁ t₂ (CEr x) M h = h
sat-ctxt-annot＝ {Γ} t₁ t₂ CEu M h = h
sat-ctxt-annot＝ {Γ} t₁ t₂ (CEi x) M h = λ _ _ → h

sat-ctxt-annot∀ : {Γ : Ctxt} (u : 𝕌) (f : Form (Γ ، 𝕍𝕌 u)) (a : CE Γ) (M : Model Γ)
                 → ((v : ⟦𝕌⟧ u) → sat-ctxt-annot f (↑CE₀ a) (M ≔ v))
                 → sat-ctxt-annot (∀· u f) a M
sat-ctxt-annot∀ {Γ} u f (CEr x) M h v = subst (λ z → ((M ≔ₜ z) ≔ v) ⊨ f) (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) (𝕍𝕌 u) v) (h v)
sat-ctxt-annot∀ {Γ} u f CEu M h = h
sat-ctxt-annot∀ {Γ} u f (CEi x) M h w q v = h v w (inter-cond↑⊆← w x (Model.subΓ M ⹁ 𝕍𝕌 u ∶ v) ⊆₀ Sub⊆-⊆₀ q)

sat-ctxt-annot∀→ : {Γ : Ctxt} (u : 𝕌) (f : Form (Γ ، 𝕍𝕌 u)) (a : CE Γ) (M : Model Γ)
                 → sat-ctxt-annot (∀· u f) a M
                 → ((v : ⟦𝕌⟧ u) → sat-ctxt-annot f (↑CE₀ a) (M ≔ v))
sat-ctxt-annot∀→ {Γ} u f (CEr x) M h v = subst (λ z → ((M ≔ₜ z) ≔ v) ⊨ f) (sym (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) (𝕍𝕌 u) v)) (h v)
sat-ctxt-annot∀→ {Γ} u f CEu M h = h
sat-ctxt-annot∀→ {Γ} u f (CEi x) M h v w q = h w (inter-cond↑⊆ w x (Model.subΓ M ⹁ 𝕍𝕌 u ∶ v) ⊆₀ Sub⊆-⊆₀ q) v

sat-ctxt-annot∃ : {Γ : Ctxt} (u : 𝕌) (f : Form (Γ ، 𝕍𝕌 u)) (a : CE Γ) (M : Model Γ)
                 → (Σ (⟦𝕌⟧ u) (λ v → sat-ctxt-annot f (↑CE₀ a) (M ≔ v)))
                 → sat-ctxt-annot (∃· u f) a M
sat-ctxt-annot∃ {Γ} u f (CEr x) M (v , h) = v , subst (λ z → ((M ≔ₜ z) ≔ v) ⊨ f) (⟦↑ᵣ₀⟧ᵣ x (Model.subΓ M) (𝕍𝕌 u) v) h
sat-ctxt-annot∃ {Γ} u f CEu M h = h
sat-ctxt-annot∃ {Γ} u f (CEi x) M (v , h) w c = v , h w (inter-cond↑⊆← w x (Model.subΓ M ⹁ 𝕍𝕌 u ∶ v) ⊆₀ Sub⊆-⊆₀ c)

sat-ctxt-annot⊥ : {Γ : Ctxt} (a : CE Γ) (M : Model Γ)
                → sat-ctxt-annot ⊥· a M
                → isNonEmpty M a
                → ⊥
sat-ctxt-annot⊥ {Γ} (CEi x) M h (w , q) = lower (h w q)

sat-ctxt-annot-↑₀ : {Γ : Ctxt} {u : 𝕍} (M : Model (Γ ، u)) (f : Form Γ) (a : CE Γ)
                  → sat-ctxt-annot (↑₀ f) (↑CE₀ a) M
                  → sat-ctxt-annot f a (Model،→ M)
sat-ctxt-annot-↑₀ {Γ} {u} M@(model interp run w (sub ⹁ .u ∶ v)) f (CEr r) h =
  ⊨⊨ₜ-↑₀→ {Γ} {model interp run w sub} {f} {u} v (⟦ r ⟧ᵣ sub)
          (subst (λ t → (M ≔ₜ t) ⊨ (↑₀ f)) (⟦↑ᵣ₀⟧ᵣ r sub u v) h)
sat-ctxt-annot-↑₀ {Γ} {u} M@(model interp run w (sub ⹁ .u ∶ v)) f CEu h =
  ⊨-↑₀→ {Γ} {model interp run w sub} {f} {u} v h
sat-ctxt-annot-↑₀ {Γ} {u} M@(model interp run w (sub ⹁ .u ∶ v)) f (CEi i) h w′ cond =
  ⊨-↑₀→ {Γ} {model interp run w′ sub} {f} {u} v
        (h w′ (inter-cond↑⊆← {Γ} {Γ ، u} {model interp run w sub} w′ i (sub ⹁ u ∶ v)
                (λ {x} → ∈CtxtS u) (λ {u} v₁ → ∈SubS sub v) cond))

→sat-ctxt-annot-↑₀ : {Γ : Ctxt} {u : 𝕍} (M : Model (Γ ، u)) (f : Form Γ) (a : CE Γ)
                   → sat-ctxt-annot f a (Model،→ M)
                   → sat-ctxt-annot (↑₀ f) (↑CE₀ a) M
→sat-ctxt-annot-↑₀ {Γ} {u} M@(model interp run w (sub ⹁ .u ∶ v)) f (CEr r) h =
  subst (λ t → (M ≔ₜ t) ⊨ (↑₀ f))
        (sym (⟦↑ᵣ₀⟧ᵣ r sub u v))
        (→⊨⊨ₜ-↑₀  {Γ} {model interp run w sub} {f} {u} v (⟦ r ⟧ᵣ sub) h)
→sat-ctxt-annot-↑₀ {Γ} {u} M@(model interp run w (sub ⹁ .u ∶ v)) f CEu h =
  →⊨-↑₀ {Γ} {model interp run w sub} {f} {u} v h
→sat-ctxt-annot-↑₀ {Γ} {u} M@(model interp run w (sub ⹁ .u ∶ v)) f (CEi i) h w′ cond =
  →⊨-↑₀ {Γ} {model interp run w′ sub} {f} {u} v
        (h w′ (inter-cond↑⊆ w′ i (sub ⹁ u ∶ v) ⊆₀ Sub⊆-⊆₀ cond))

ℂtxt⊆ : {Γ : Ctxt} (c : ℂ Γ) → Γ ⊆ ℂtxt c
ℂtxt⊆ ℂ⟨⟩        = ⊆-refl
ℂtxt⊆ (ℂx c f a) = ℂtxt⊆ c
ℂtxt⊆ (ℂv c v)   = ⊆-trans (ℂtxt⊆ c) ⊆₀

FormSub : Ctxt → Set₁
FormSub Γ = FormVar → Form Γ

-- syntactic FormSub
data FormSub⋆ (Γ : Ctxt) : Set₁ where
  ● : FormSub⋆ Γ
  _↦_⨾_ : FormVar → Form Γ → FormSub⋆ Γ → FormSub⋆ Γ

-- Syntactic sub-context
data _⊆⋆_ : Ctxt → Ctxt → Set where
  ⊆⋆-init : (Γ : Ctxt) → ⟨⟩ ⊆⋆ Γ
  ⊆⋆-add  : {Γ Δ : Ctxt} (v : 𝕍) → Γ ⊆⋆ Δ → Γ ، v ⊆⋆ Δ ، v
  ⊆⋆-skip : {Γ Δ : Ctxt} (v : 𝕍) → Γ ⊆⋆ Δ → Γ ⊆⋆ Δ ، v

⊆⋆، : {Γ Δ : Ctxt} (u : 𝕍)
    → Γ ⊆⋆ Δ
    → (Γ ، u) ⊆⋆ (Δ ، u)
⊆⋆، {Γ} {Δ} u s = ⊆⋆-add u s

⊆⋆-refl : {Γ : Ctxt} → Γ ⊆⋆ Γ
⊆⋆-refl {⟨⟩} = ⊆⋆-init ⟨⟩
⊆⋆-refl {Γ ، U} = ⊆⋆-add U ⊆⋆-refl

⊆⋆-trans : {Γ Δ Ψ : Ctxt} → Γ ⊆⋆ Δ → Δ ⊆⋆ Ψ → Γ ⊆⋆ Ψ
⊆⋆-trans {Γ} {Δ} {Ψ} (⊆⋆-init .⟨⟩) (⊆⋆-init .Ψ) = ⊆⋆-init Ψ
⊆⋆-trans {Γ} {Δ} {Ψ} (⊆⋆-init .(_ ، v)) (⊆⋆-add v t) = ⊆⋆-init (_ ، v)
⊆⋆-trans {Γ} {Δ} {Ψ} (⊆⋆-add .v s) (⊆⋆-add v t) = ⊆⋆-add v (⊆⋆-trans s t)
⊆⋆-trans {Γ} {Δ} {Ψ} (⊆⋆-skip .v s) (⊆⋆-add v t) = ⊆⋆-skip v (⊆⋆-trans s t)
⊆⋆-trans {Γ} {Δ} {Ψ} s (⊆⋆-skip v t) = ⊆⋆-skip v (⊆⋆-trans s t)

⊆⋆₀ : {Γ : Ctxt} {u : 𝕍} → Γ ⊆⋆ (Γ ، u)
⊆⋆₀ {Γ} {u} = ⊆⋆-skip _ ⊆⋆-refl

ℂtxt⊆⋆ : {Γ : Ctxt} (c : ℂ Γ) → Γ ⊆⋆ ℂtxt c
ℂtxt⊆⋆ ℂ⟨⟩        = ⊆⋆-refl
ℂtxt⊆⋆ (ℂx c f a) = ℂtxt⊆⋆ c
ℂtxt⊆⋆ (ℂv c v)   = ⊆⋆-trans (ℂtxt⊆⋆ c) ⊆⋆₀

app-⊆⋆ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) (v : 𝕍)
       → ∈Ctxt v Γ
       → ∈Ctxt v Δ
app-⊆⋆ {Γ} {Δ} (⊆⋆-add v₁ s) v (∈Ctxt0 _) = ∈Ctxt0 _
app-⊆⋆ {Γ} {Δ} (⊆⋆-add v₁ s) v (∈CtxtS .v₁ i) = ∈CtxtS v₁ (app-⊆⋆ s v i)
app-⊆⋆ {Γ} {Δ} (⊆⋆-skip v₁ s) v i = ∈CtxtS v₁ (app-⊆⋆ s v i)

↑⋆ᵢ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Agent Γ → Agent Δ
↑⋆ᵢ s (agentV i) = agentV (app-⊆⋆ s _ i)
↑⋆ᵢ s (agentC x) = agentC x

↑⋆ₛ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Agents Γ → Agents Δ
↑⋆ₛ s (agentsV i) = agentsV (app-⊆⋆ s _ i)
↑⋆ₛ s (agentsL l) = agentsL (Data.List.map (↑⋆ᵢ s) l)

↑⋆ₚ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → AtomProp Γ → AtomProp Δ
↑⋆ₚ s (atomPropV i) = atomPropV (app-⊆⋆ s _ i)
↑⋆ₚ s (atomPropC x) = atomPropC x

↑⋆d : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Data Γ → Data Δ
↑⋆d s (dataV i) = dataV (app-⊆⋆ s _ i)
↑⋆d s (dataC x) = dataC x

↑⋆ₜ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Action Γ → Action Δ
↑⋆ₜ s (ActSend p a A) = ActSend (↑⋆d s p) (↑⋆ᵢ s a) (↑⋆ₛ s A)

↑⋆ₑ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Event Γ → Event Δ
↑⋆ₑ s (EvtReceive p a b) = EvtReceive (↑⋆d s p) (↑⋆ᵢ s a) (↑⋆ᵢ s b)
↑⋆ₑ s (EvtInternal a d) = EvtInternal (↑⋆ᵢ s a) (↑⋆d s d)

↑⋆f : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Fault Γ → Fault Δ
↑⋆f s (FaultCorrect a b) = FaultCorrect (↑⋆ᵢ s a) (↑⋆ᵢ s b)

↑⋆ₐ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Atom Γ → Atom Δ
↑⋆ₐ s (atProp    x) = atProp (↑⋆ₚ s x)
↑⋆ₐ s (atAction  x) = atAction (↑⋆ₜ s x)
↑⋆ₐ s (atEvent   x) = atEvent (↑⋆ₑ s x)
↑⋆ₐ s (atCorrect x) = atCorrect (↑⋆f s x)

↑⋆ᵣ : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → Res Γ → Res Δ
↑⋆ᵣ s (𝐯 x) = 𝐯 (app-⊆⋆ s _ x)
↑⋆ᵣ s 𝟎 = 𝟎
↑⋆ᵣ s (t ⋆ t₁) = ↑⋆ᵣ s t ⋆ ↑⋆ᵣ s t₁
↑⋆ᵣ s (rvar ρ) = rvar ρ

↑⋆A : {Γ Δ : Ctxt} (s : Γ ⊆⋆ Δ) → SetAtom Γ → SetAtom Δ
↑⋆A {Γ} {Δ} s (a ∈ₐ A) = ↑⋆ᵢ s a ∈ₐ ↑⋆ₛ s A
↑⋆A {Γ} {Δ} s (∣ A ∣ₛ＝ n) = ∣ ↑⋆ₛ s A ∣ₛ＝ n

-- Syntactic lifting
↑⋆ : {Γ Δ : Ctxt}
   → Γ ⊆⋆ Δ
   → Form Γ
   → Form Δ
--↑⋆ {⟨⟩} {⟨⟩} (⊆⋆-init ⟨⟩) f = f
↑⋆ {Γ} {Δ} s (𝕒 x) = 𝕒 (↑⋆ₐ s x)
↑⋆ {Γ} {Δ} s (var x) = var x
↑⋆ {Γ} {Δ} s ⊤· = ⊤·
↑⋆ {Γ} {Δ} s ⊥· = ⊥·
↑⋆ {Γ} {Δ} s (f ∧· f₁) = ↑⋆ s f ∧· ↑⋆ s f₁
↑⋆ {Γ} {Δ} s (f ∨· f₁) = ↑⋆ s f ∨· ↑⋆ s f₁
↑⋆ {Γ} {Δ} s (f →· f₁) = ↑⋆ s f →· ↑⋆ s f₁
↑⋆ {Γ} {Δ} s (∀· u f) = ∀· u (↑⋆ (⊆⋆، (𝕍𝕌 u) s) f)
↑⋆ {Γ} {Δ} s (∃· u f) = ∃· u (↑⋆ (⊆⋆، (𝕍𝕌 u) s) f)
↑⋆ {Γ} {Δ} s (𝔸 A) = 𝔸 (↑⋆A s A)
↑⋆ {Γ} {Δ} s (f Ｕ f₁) = ↑⋆ s f Ｕ ↑⋆ s f₁
↑⋆ {Γ} {Δ} s (Ｏ f) = Ｏ (↑⋆ s f)
↑⋆ {Γ} {Δ} s (f Ｓ f₁) = ↑⋆ s f Ｓ ↑⋆ s f₁
↑⋆ {Γ} {Δ} s (Ｙ f) = Ｙ (↑⋆ s f)
↑⋆ {Γ} {Δ} s (Ｂ f) = Ｂ (↑⋆ s f)
↑⋆ {Γ} {Δ} s (Ｆ f) = Ｆ ↑⋆ (⊆⋆، 𝕍ℝ s) f
↑⋆ {Γ} {Δ} s (t₁ ⟨ c ⟩ t₂) = ↑⋆ᵣ s t₁ ⟨ c ⟩ ↑⋆ᵣ s t₂

↑⋆I : {Γ Δ : Ctxt}
    → Γ ⊆⋆ Δ
    → Interval Γ
    → Interval Δ
↑⋆I {Γ} {Δ} e ［ x , x₁ ］ = ［ ↑⋆ᵣ e x , ↑⋆ᵣ e x₁ ］
↑⋆I {Γ} {Δ} e ［ x , x₁ ） = ［ ↑⋆ᵣ e x , ↑⋆ᵣ e x₁ ）
↑⋆I {Γ} {Δ} e （ x , x₁ ］ = （ ↑⋆ᵣ e x , ↑⋆ᵣ e x₁ ］
↑⋆I {Γ} {Δ} e （ x , x₁ ） = （ ↑⋆ᵣ e x , ↑⋆ᵣ e x₁ ）

↑⋆CE : {Γ Δ : Ctxt}
     → Γ ⊆⋆ Δ
     → CE Γ
     → CE Δ
↑⋆CE {Γ} {Δ} e (CEr x) = CEr (↑⋆ᵣ e x)
↑⋆CE {Γ} {Δ} e CEu = CEu
↑⋆CE {Γ} {Δ} e (CEi x) = CEi (↑⋆I e x)

{--
FormSub : Ctxt → Set₁
FormSub Γ = FormVar → (Δ : Ctxt) → Γ ⊆ Δ → Form Δ
--}

FormSub₀ : Set₁
FormSub₀ = FormSub ⟨⟩

FormSub⋆₀ : Set₁
FormSub⋆₀ = FormSub⋆ ⟨⟩

FormSub، : (Γ : Ctxt) (v : 𝕍)
        → FormSub Γ
        → FormSub (Γ ، v)
FormSub، Γ v s n = ↑₀ (s n)

FormSub⋆، : (Γ : Ctxt) (v : 𝕍)
          → FormSub⋆ Γ
          → FormSub⋆ (Γ ، v)
FormSub⋆، Γ v ● = ●
FormSub⋆، Γ v (x ↦ f ⨾ s) = x ↦ ↑⋆ ⊆⋆₀ f ⨾ FormSub⋆، Γ v s

↑FormSub : {Γ Δ : Ctxt}
         → Γ ⊆ Δ
         → FormSub Γ
         → FormSub Δ
↑FormSub {Γ} {Δ} s σ n = ↑ s (σ n)

↑FormSub⋆ : {Γ Δ : Ctxt}
          → Γ ⊆⋆ Δ
          → FormSub⋆ Γ
          → FormSub⋆ Δ
↑FormSub⋆ {Γ} {Δ} s ● = ●
↑FormSub⋆ {Γ} {Δ} s (x ↦ x₁ ⨾ σ) = x ↦ ↑⋆ s x₁ ⨾ ↑FormSub⋆ s σ

app-FormSub⋆ : {Γ : Ctxt} (v : FormVar) (σ : FormSub⋆ Γ) → Form Γ
app-FormSub⋆ {Γ} v ● = var v
app-FormSub⋆ {Γ} v (x ↦ f ⨾ σ) with v ≟ x
... | yes refl = f
... | no p = app-FormSub⋆ v σ

substF : {Γ : Ctxt} → FormSub Γ → Form Γ → Form Γ
substF {Γ} σ (𝕒 x) = 𝕒 x
substF {Γ} σ (var x) = σ x
substF {Γ} σ ⊤· = ⊤·
substF {Γ} σ ⊥· = ⊥·
substF {Γ} σ (f ∧· f₁) = substF σ f ∧· substF σ f₁
substF {Γ} σ (f ∨· f₁) = substF σ f ∨· substF σ f₁
substF {Γ} σ (f →· f₁) = substF σ f →· substF σ f₁
substF {Γ} σ (∀· u f) = ∀· u (substF (FormSub، Γ (𝕍𝕌 u) σ) f)
substF {Γ} σ (∃· u f) = ∃· u (substF (FormSub، Γ (𝕍𝕌 u) σ) f)
substF {Γ} σ (𝔸 x) = 𝔸 x
substF {Γ} σ (f Ｕ f₁) = substF σ f Ｕ substF σ f₁
substF {Γ} σ (Ｏ f) = Ｏ (substF σ f)
substF {Γ} σ (f Ｓ f₁) = substF σ f Ｓ substF σ f₁
substF {Γ} σ (Ｙ f) = Ｙ (substF σ f)
substF {Γ} σ (Ｂ f) = Ｂ (substF σ f)
substF {Γ} σ (Ｆ f) = Ｆ (substF (FormSub، Γ 𝕍ℝ σ) f)
substF {Γ} σ (t₁ ⟨ x ⟩ t₂) = t₁ ⟨ x ⟩ t₂

-- syntactic substitution
substF⋆ : {Γ : Ctxt} → FormSub⋆ Γ → Form Γ → Form Γ
substF⋆ {Γ} σ (𝕒 x) = 𝕒 x
substF⋆ {Γ} σ (var x) = app-FormSub⋆ x σ
substF⋆ {Γ} σ ⊤· = ⊤·
substF⋆ {Γ} σ ⊥· = ⊥·
substF⋆ {Γ} σ (f ∧· f₁) = substF⋆ σ f ∧· substF⋆ σ f₁
substF⋆ {Γ} σ (f ∨· f₁) = substF⋆ σ f ∨· substF⋆ σ f₁
substF⋆ {Γ} σ (f →· f₁) = substF⋆ σ f →· substF⋆ σ f₁
substF⋆ {Γ} σ (∀· u f) = ∀· u (substF⋆ (FormSub⋆، Γ (𝕍𝕌 u) σ) f)
substF⋆ {Γ} σ (∃· u f) = ∃· u (substF⋆ (FormSub⋆، Γ (𝕍𝕌 u) σ) f)
substF⋆ {Γ} σ (𝔸 x) = 𝔸 x
substF⋆ {Γ} σ (f Ｕ f₁) = substF⋆ σ f Ｕ substF⋆ σ f₁
substF⋆ {Γ} σ (Ｏ f) = Ｏ (substF⋆ σ f)
substF⋆ {Γ} σ (f Ｓ f₁) = substF⋆ σ f Ｓ substF⋆ σ f₁
substF⋆ {Γ} σ (Ｙ f) = Ｙ (substF⋆ σ f)
substF⋆ {Γ} σ (Ｂ f) = Ｂ (substF⋆ σ f)
substF⋆ {Γ} σ (Ｆ f) = Ｆ (substF⋆ (FormSub⋆، Γ 𝕍ℝ σ) f)
substF⋆ {Γ} σ (t₁ ⟨ x ⟩ t₂) = t₁ ⟨ x ⟩ t₂

{--
subst⊨ : {Γ : Ctxt} (m : Model Γ) (f : Form Γ)
         (σ : FormSub Γ)
       → m ⊨ f
       → m ⊨ substF σ f
subst⊨ {Γ} m f σ h = ?
--}

≡-to-⊆ : {Γ Δ : Ctxt} (e : Γ ≡ Δ) → Γ ⊆ Δ
≡-to-⊆ {Γ} {Δ} e = subst (λ z → Γ ⊆ z) e ⊆-refl

↑≡ : {Γ Δ : Ctxt} (e : Γ ≡ Δ) (f : Form Γ) → Form Δ
↑≡ {Γ} {Δ} e f = ↑ (≡-to-⊆ e) f

↑CE≡ : {Γ Δ : Ctxt} (e : Γ ≡ Δ) (f : CE Γ) → CE Δ
↑CE≡ {Γ} {Δ} e f = ↑CE (subst (λ z → Γ ⊆ z) e ⊆-refl) f

substCtxt : {Γ : Ctxt} → FormSub Γ → ℂ Γ → ℂ Γ
ℂtxt-substCtxt : {Γ : Ctxt} (σ : FormSub Γ) (c : ℂ Γ) → ℂtxt (substCtxt σ c) ≡ ℂtxt c

-- If a 'formula variable' occurs under 'context variables' it could potentially be replaced by
-- a formula that uses those 'context variables'. We're requiring here that the formulas we're
-- substituting in are closed, which is not as general as it could...
substCtxt {Γ} σ ℂ⟨⟩ = ℂ⟨⟩
substCtxt {Γ} σ (ℂx c f a) =
  ℂx (substCtxt σ c)
     (↑≡ (sym (ℂtxt-substCtxt σ c)) (substF (↑FormSub (ℂtxt⊆ c) σ) f))
     (↑CE≡ (sym (ℂtxt-substCtxt σ c)) a)
substCtxt {Γ} σ (ℂv c v) = ℂv (substCtxt σ c) v

ℂtxt-substCtxt {Γ} σ ℂ⟨⟩ = refl
ℂtxt-substCtxt {Γ} σ (ℂx c f a) = ℂtxt-substCtxt σ c
ℂtxt-substCtxt {Γ} σ (ℂv c v) = cong (λ z → z ، v) (ℂtxt-substCtxt σ c)

substCtxt⋆ : {Γ : Ctxt} → FormSub⋆ Γ → ℂ Γ → ℂ Γ
ℂtxt-substCtxt⋆ : {Γ : Ctxt} (σ : FormSub⋆ Γ) (c : ℂ Γ) → ℂtxt c ⊆⋆ ℂtxt (substCtxt⋆ σ c)

substCtxt⋆ {Γ} σ ℂ⟨⟩ = ℂ⟨⟩
substCtxt⋆ {Γ} σ (ℂx c f a) =
  ℂx (substCtxt⋆ σ c)
     (↑⋆ (ℂtxt-substCtxt⋆ σ c) (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ c) σ) f))
     (↑⋆CE (ℂtxt-substCtxt⋆ σ c) a)
substCtxt⋆ {Γ} σ (ℂv c v) = ℂv (substCtxt⋆ σ c) v

ℂtxt-substCtxt⋆ {Γ} σ ℂ⟨⟩ = ⊆⋆-refl
ℂtxt-substCtxt⋆ {Γ} σ (ℂx c f a) = ℂtxt-substCtxt⋆ σ c
ℂtxt-substCtxt⋆ {Γ} σ (ℂv c v) = ⊆⋆-add _ (ℂtxt-substCtxt⋆ σ c)

{--
substCtxt σ ℂ⟨⟩        = ℂ⟨⟩
substCtxt σ (ℂx c f a) = ℂx (substCtxt σ c) (substF (↑ (ℂtxt⊆ c) ∘ σ) f) a
substCtxt σ (ℂv c v)   = ℂv (substCtxt σ c) v
--}

substSequent : FormSub₀ → Sequent → Sequent
substSequent σ (seq Δ T C) =
  seq (substCtxt σ Δ)
      (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) T)
      (↑≡ (sym (ℂtxt-substCtxt σ Δ)) (substF (↑FormSub (ℂtxt⊆ Δ) σ) C))
substSequent σ (nonEmpty Δ R) =
  nonEmpty (substCtxt σ Δ)
           (↑CE≡ (sym (ℂtxt-substCtxt σ Δ)) R)

substSequent⋆ : FormSub⋆₀ → Sequent → Sequent
substSequent⋆ σ (seq Δ T C) =
  seq (substCtxt⋆ σ Δ)
      (↑⋆CE (ℂtxt-substCtxt⋆ σ Δ) T)
      (↑⋆ (ℂtxt-substCtxt⋆ σ Δ) (substF⋆ (↑FormSub⋆ (ℂtxt⊆⋆ Δ) σ) C))
substSequent⋆ σ (nonEmpty Δ R) =
  nonEmpty (substCtxt⋆ σ Δ)
           (↑⋆CE (ℂtxt-substCtxt⋆ σ Δ) R)

substRule : FormSub₀ → Rule → Rule
substRule σ (rule p c) = rule (Data.List.map (substSequent σ) p) (substSequent σ c)

substRule⋆ : FormSub⋆₀ → Rule → Rule
substRule⋆ σ (rule p c) = rule (Data.List.map (substSequent⋆ σ) p) (substSequent⋆ σ c)

sat-rule-test-id : (M : Model₀)
                 → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr 𝟎) (var 0 →· var 0)))
sat-rule-test-id M p s h = λ z → z

\end{code}
