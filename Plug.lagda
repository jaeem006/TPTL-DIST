Plugging a closed derivation into an arbitrary context (SUBST APPROACH).

A derivation found by search⊢ for a *closed* sequent, whose opaque
formulas and resources have been abstracted to formula variables (var k)
and resource variables (rvar k), is transported into an arbitrary context
Γ : ℂ₀, with the variables instantiated by formulas and resources over
ℂtxt Γ:

  plug-⊢ Γ σ ρ : ⊢ (seq Δ T C)
               → ⊢ (seq (plug Γ σ ρ Δ) ⟪ Δ ⟫CE T ⟪ Δ ⟫ C)

plug Γ σ ρ Δ appends the (instantiated) hypotheses of Δ to Γ.  Γ's own
hypotheses are left untouched.

⟪ Δ ⟫ = μ w ∘ ↑⋆ s, where ↑⋆ s renames Δ's bound variables into the new
context, and μ w instantiates var/rvar.  Under binders, μ accumulates the
weakening w : Wk Φ Δ' (Φ = ℂtxt Γ) instead of iterating ↑₀, so that
instantiating var x under two binders yields exactly ↑₁ A (definitionally),
which is what the derived operators (◇↓, ...) use.  With w = wk-id the
substituted formula is A itself, not ↑ ⊆-refl A.

\begin{code}
{-# OPTIONS --safe #-}

open import Level using (0ℓ ; lift) renaming (suc to lsuc)
open import Agda.Builtin.Equality
open import Data.Product
open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _≡ᵇ_)
open import Data.Bool using (Bool ; true ; false)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)

open import Misc
open import World

module Plug (W : World)
       where

open import Decidable(W)
open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)
open import Automation W

-- ---------------------------------------------------------------------------
-- Accumulated weakenings

data Wk (Φ : Ctxt) : Ctxt → Set where
  wk-id : Wk Φ Φ
  wk-S  : {Δ : Ctxt} (u : 𝕍) → Wk Φ Δ → Wk Φ (Δ ، u)

wk→⊆ : {Φ Δ : Ctxt} → Wk Φ Δ → Φ ⊆ Δ
wk→⊆ wk-id      i = i
wk→⊆ (wk-S u w) i = ∈CtxtS u (wk→⊆ w i)

-- wk-id is the identity on the nose; otherwise ↑ along wk→⊆.
wkF : {Φ Δ : Ctxt} → Wk Φ Δ → Form Φ → Form Δ
wkF wk-id        X = X
wkF w@(wk-S _ _) X = ↑ (wk→⊆ w) X

wkF≡↑ : {Φ Δ : Ctxt} (w : Wk Φ Δ) (X : Form Φ) → wkF w X ≡ ↑ (wk→⊆ w) X
wkF≡↑ wk-id      X = sym (↑-refl (λ i → i) X (λ _ _ → refl))
wkF≡↑ (wk-S _ _) X = refl

wk＋ : {Φ Γ : Ctxt} (Ψ : Ctxt) → Wk Φ Γ → Wk Φ (Γ ＋ Ψ)
wk＋ ⟨⟩      w = w
wk＋ (Ψ ، U) w = wk-S U (wk＋ Ψ w)

depthW : {Φ Δ : Ctxt} → Wk Φ Δ → ℕ
depthW wk-id      = 0
depthW (wk-S _ w) = suc (depthW w)

-- a weakening split into its inner part and its outermost m steps
SplitW : Ctxt → Ctxt → Set
SplitW Φ Δ = Σ Ctxt (λ Ψ → Wk Φ Ψ × Wk Ψ Δ)

outerW : {Φ Δ : Ctxt} (m : ℕ) → Wk Φ Δ → SplitW Φ Δ
outerW zero    w          = _ , w , wk-id
outerW (suc m) wk-id      = _ , wk-id , wk-id
outerW (suc m) (wk-S u w) = proj₁ r , proj₁ (proj₂ r) , wk-S u (proj₂ (proj₂ r))
  where r = outerW m w

outerW-⊆ : {Φ Δ : Ctxt} (m : ℕ) (w : Wk Φ Δ) {v : 𝕍} (i : ∈Ctxt v Φ)
         → wk→⊆ w i ≡ wk→⊆ (proj₂ (proj₂ (outerW m w))) (wk→⊆ (proj₁ (proj₂ (outerW m w))) i)
outerW-⊆ zero    w          i = refl
outerW-⊆ (suc m) wk-id      i = refl
outerW-⊆ (suc m) (wk-S u w) i = cong (∈CtxtS u) (outerW-⊆ m w i)

-- Shapes.  An Agda term such as ↑ᵣ₁ (↑ᵣ₃ X), at depth 6, is a nested
-- weakening that μ could not produce from X by a single ↑ᵣ (the two are
-- only propositionally equal).  A substitution may therefore give, for
-- each depth, the shape of the weakening: the lengths of its nested steps,
-- innermost first ([ 4 , 2 ] for ↑ᵣ₁ (↑ᵣ₃ X)).  Other depths use one ↑.
Shape : Set
Shape = List ℕ

sumℕ : List ℕ → ℕ
sumℕ []      = 0
sumℕ (k ∷ l) = k + sumℕ l

pick : List Shape → ℕ → Shape
pick []       d = []
pick (s ∷ ss) d with sumℕ s ≡ᵇ d
... | true  = s
... | false = pick ss d

module Nest {T : Ctxt → Set}
            (↑T : {Γ Δ : Ctxt} → Γ ⊆ Δ → T Γ → T Δ)
            (↑T-trans : {Γ Ψ Δ : Ctxt} (e : Γ ⊆ Δ) (e₁ : Γ ⊆ Ψ) (e₂ : Ψ ⊆ Δ) (a : T Γ)
                      → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ e₂ (e₁ i))
                      → ↑T e a ≡ ↑T e₂ (↑T e₁ a))
            (↑T-refl : {Γ : Ctxt} (e : Γ ⊆ Γ) (a : T Γ)
                     → ((v : 𝕍) (i : ∈Ctxt v Γ) → e i ≡ i) → ↑T e a ≡ a)
  where
  wkT : {Φ Δ : Ctxt} → Wk Φ Δ → T Φ → T Δ
  wkT wk-id        X = X
  wkT w@(wk-S _ _) X = ↑T (wk→⊆ w) X

  wkT≡↑ : {Φ Δ : Ctxt} (w : Wk Φ Δ) (X : T Φ) → wkT w X ≡ ↑T (wk→⊆ w) X
  wkT≡↑ wk-id      X = sym (↑T-refl (λ i → i) X (λ _ _ → refl))
  wkT≡↑ (wk-S _ _) X = refl

  nestT : {Φ Δ : Ctxt} → Shape → T Φ → Wk Φ Δ → T Δ
  nestT []       X w = wkT w X
  nestT (k ∷ ks) X w = nestT ks (↑T (wk→⊆ (proj₁ (proj₂ s))) X) (proj₂ (proj₂ s))
    where s = outerW (depthW w ∸ k) w

  nestT≡↑ : {Φ Δ : Ctxt} (ks : Shape) (X : T Φ) (w : Wk Φ Δ) → nestT ks X w ≡ ↑T (wk→⊆ w) X
  nestT≡↑ []       X w = wkT≡↑ w X
  nestT≡↑ (k ∷ ks) X w =
    trans (nestT≡↑ ks (↑T (wk→⊆ (proj₁ (proj₂ s))) X) (proj₂ (proj₂ s)))
          (sym (↑T-trans (wk→⊆ w) (wk→⊆ (proj₁ (proj₂ s))) (wk→⊆ (proj₂ (proj₂ s))) X
                         (λ _ i → outerW-⊆ (depthW w ∸ k) w i)))
    where s = outerW (depthW w ∸ k) w

  -- X weakened along w, in the shape given for the depth of w
  shapeT : {Φ Δ : Ctxt} → List Shape → T Φ → Wk Φ Δ → T Δ
  shapeT ss X w = nestT (pick ss (depthW w)) X w

  shapeT≡↑ : {Φ Δ : Ctxt} (ss : List Shape) (X : T Φ) (w : Wk Φ Δ) → shapeT ss X w ≡ ↑T (wk→⊆ w) X
  shapeT≡↑ ss X w = nestT≡↑ (pick ss (depthW w)) X w

  shapeT≡wk : {Φ Δ : Ctxt} (ss : List Shape) (X : T Φ) (w : Wk Φ Δ) → shapeT ss X w ≡ wkT w X
  shapeT≡wk ss X w = trans (shapeT≡↑ ss X w) (sym (wkT≡↑ w X))

module NR = Nest ↑ᵣ ↑ᵣ-trans ↑ᵣ-refl
module NA = Nest ↑ᵢ ↑ᵢ-trans ↑ᵢ-refl
module ND = Nest ↑d ↑d-trans ↑d-refl

wkR : {Φ Δ : Ctxt} → Wk Φ Δ → Res Φ → Res Δ
wkR = NR.wkT

wkR≡↑ : {Φ Δ : Ctxt} (w : Wk Φ Δ) (X : Res Φ) → wkR w X ≡ ↑ᵣ (wk→⊆ w) X
wkR≡↑ = NR.wkT≡↑

-- ---------------------------------------------------------------------------
-- Substitutions for resource variables (the analogue of FormSub⋆), and for
-- agent and data constants used as placeholders (by the tactic, for opaque
-- agents and data).  An entry may give shapes (see Shape).

data ResSub⋆ (Γ : Ctxt) : Set where
  ●ᵣ       : ResSub⋆ Γ
  _↦ᵣ_⨾_   : ResVar → Res Γ → ResSub⋆ Γ → ResSub⋆ Γ
  _↦ᵣ_∶_⨾_ : ResVar → Res Γ → List Shape → ResSub⋆ Γ → ResSub⋆ Γ

infixr 4 _↦ᵣ_⨾_
infixr 4 _↦ᵣ_∶_⨾_

app-ResSub⋆ : {Γ : Ctxt} → ResVar → ResSub⋆ Γ → Res Γ
app-ResSub⋆ x ●ᵣ = rvar x
app-ResSub⋆ x (y ↦ᵣ r ⨾ ρ) with x ≟ y
... | yes _ = r
... | no  _ = app-ResSub⋆ x ρ
app-ResSub⋆ x (y ↦ᵣ r ∶ ss ⨾ ρ) with x ≟ y
... | yes _ = r
... | no  _ = app-ResSub⋆ x ρ

shapesᵣ : {Γ : Ctxt} → ResVar → ResSub⋆ Γ → List Shape
shapesᵣ x ●ᵣ = []
shapesᵣ x (y ↦ᵣ r ⨾ ρ) with x ≟ y
... | yes _ = []
... | no  _ = shapesᵣ x ρ
shapesᵣ x (y ↦ᵣ r ∶ ss ⨾ ρ) with x ≟ y
... | yes _ = ss
... | no  _ = shapesᵣ x ρ

-- Besides agent placeholders, an AgSub⋆ can carry two more kinds of
-- placeholders, both closed:
--  * setₐ Ns ⨾ α: the empty list of agents, agentsL [], is a placeholder for
--    the agent set agentsS Ns (an arbitrary, possibly abstract, list Ns).
--  * sizeₐ i ↦ j ⨾ α: the size i in the set atoms ∣ A ∣ₛ＝ i is a placeholder
--    for the size j.
-- This lets a search run on a closed sequent with agentsL [] and a numeral
-- size, and the derivation be instantiated with any set of agents and size.
data AgSub⋆ (Γ : Ctxt) : Set where
  ●ₐ       : AgSub⋆ Γ
  _↦ₐ_∶_⨾_ : agent → Agent Γ → List Shape → AgSub⋆ Γ → AgSub⋆ Γ
  setₐ_⨾_  : List agent → AgSub⋆ Γ → AgSub⋆ Γ
  sizeₐ_↦_⨾_ : ℕ → ℕ → AgSub⋆ Γ → AgSub⋆ Γ

infixr 4 _↦ₐ_∶_⨾_ setₐ_⨾_ sizeₐ_↦_⨾_

app-AgSub⋆ : {Γ : Ctxt} → agent → AgSub⋆ Γ → Agent Γ
app-AgSub⋆ k ●ₐ = agentC k
app-AgSub⋆ k (j ↦ₐ a ∶ ss ⨾ α) with k ≟ j
... | yes _ = a
... | no  _ = app-AgSub⋆ k α
app-AgSub⋆ k (setₐ _ ⨾ α) = app-AgSub⋆ k α
app-AgSub⋆ k (sizeₐ _ ↦ _ ⨾ α) = app-AgSub⋆ k α

shapesₐ : {Γ : Ctxt} → agent → AgSub⋆ Γ → List Shape
shapesₐ k ●ₐ = []
shapesₐ k (j ↦ₐ a ∶ ss ⨾ α) with k ≟ j
... | yes _ = ss
... | no  _ = shapesₐ k α
shapesₐ k (setₐ _ ⨾ α) = shapesₐ k α
shapesₐ k (sizeₐ _ ↦ _ ⨾ α) = shapesₐ k α

-- what the empty list of agents stands for
nilₐ : {Γ Δ : Ctxt} → AgSub⋆ Γ → Agents Δ
nilₐ ●ₐ                 = agentsL []
nilₐ (_ ↦ₐ _ ∶ _ ⨾ α)   = nilₐ α
nilₐ (setₐ Ns ⨾ α)      = agentsL (Data.List.map agentC Ns)
nilₐ (sizeₐ _ ↦ _ ⨾ α)  = nilₐ α

-- what a size stands for
sizeOfₐ : {Γ : Ctxt} → AgSub⋆ Γ → ℕ → ℕ
sizeOfₐ ●ₐ n                = n
sizeOfₐ (_ ↦ₐ _ ∶ _ ⨾ α) n  = sizeOfₐ α n
sizeOfₐ (setₐ _ ⨾ α) n      = sizeOfₐ α n
sizeOfₐ (sizeₐ i ↦ j ⨾ α) n with n ≟ i
... | yes _ = j
... | no  _ = sizeOfₐ α n

map-agentC-↑ : {Δ Δ′ : Ctxt} (e : Δ ⊆ Δ′) (Ns : List agent)
             → Data.List.map (↑ᵢ e) (Data.List.map (agentC {Δ}) Ns) ≡ Data.List.map agentC Ns
map-agentC-↑ e []       = refl
map-agentC-↑ e (k ∷ Ns) = cong (agentC k ∷_) (map-agentC-↑ e Ns)

nilₐ-↑ : {Γ Δ Δ′ : Ctxt} (e : Δ ⊆ Δ′) (α : AgSub⋆ Γ) → ↑ₛ e (nilₐ {Γ} {Δ} α) ≡ nilₐ α
nilₐ-↑ e ●ₐ                = refl
nilₐ-↑ e (_ ↦ₐ _ ∶ _ ⨾ α)  = nilₐ-↑ e α
nilₐ-↑ e (setₐ Ns ⨾ α)     = cong agentsL (map-agentC-↑ e Ns)
nilₐ-↑ e (sizeₐ _ ↦ _ ⨾ α) = nilₐ-↑ e α

map-agentC-sub : {Δ Δ′ : Ctxt} (c : CSub Δ Δ′) (Ns : List agent)
               → Data.List.map (λ x → sub-Agent x c) (Data.List.map (agentC {Δ}) Ns) ≡ Data.List.map agentC Ns
map-agentC-sub c []       = refl
map-agentC-sub c (k ∷ Ns) = cong (agentC k ∷_) (map-agentC-sub c Ns)

nilₐ-sub : {Γ Δ Δ′ : Ctxt} (c : CSub Δ Δ′) (α : AgSub⋆ Γ) → sub-Agents (nilₐ {Γ} {Δ} α) c ≡ nilₐ α
nilₐ-sub c ●ₐ                = refl
nilₐ-sub c (_ ↦ₐ _ ∶ _ ⨾ α)  = nilₐ-sub c α
nilₐ-sub c (setₐ Ns ⨾ α)     = cong agentsL (map-agentC-sub c Ns)
nilₐ-sub c (sizeₐ _ ↦ _ ⨾ α) = nilₐ-sub c α

data DaSub⋆ (Γ : Ctxt) : Set where
  ●d       : DaSub⋆ Γ
  _↦d_∶_⨾_ : 𝔻 → Data Γ → List Shape → DaSub⋆ Γ → DaSub⋆ Γ

infixr 4 _↦d_∶_⨾_

app-DaSub⋆ : {Γ : Ctxt} → 𝔻 → DaSub⋆ Γ → Data Γ
app-DaSub⋆ k ●d = dataC k
app-DaSub⋆ k (j ↦d a ∶ ss ⨾ δ) with k ≟ j
... | yes _ = a
... | no  _ = app-DaSub⋆ k δ

shapes-d : {Γ : Ctxt} → 𝔻 → DaSub⋆ Γ → List Shape
shapes-d k ●d = []
shapes-d k (j ↦d a ∶ ss ⨾ δ) with k ≟ j
... | yes _ = ss
... | no  _ = shapes-d k δ

-- substituting into a weakened term of the outer context
module _ {Φ Γ : Ctxt} (U : 𝕍) where
  hw＋g : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (v : 𝕍) (i : ∈Ctxt v Φ)
        → wk→⊆ (wk＋ Ψ (wk-S U w₀)) i ≡ ⊆،＋ {Γ} {Ψ} {U} (wk→⊆ (wk＋ Ψ w₀) i)
  hw＋g ⟨⟩      w₀ v i = refl
  hw＋g (Ψ ، V) w₀ v i = cong (∈CtxtS V) (hw＋g Ψ w₀ v i)

  sub-shapeA : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : C⟦𝕍⟧ Γ U) (ss : List Shape) (X : Agent Φ)
             → sub-Agent (NA.shapeT ss X (wk＋ Ψ (wk-S U w₀))) (CSub،＋ {Γ} {Ψ} {U} a)
             ≡ ↑ᵢ (wk→⊆ (wk＋ Ψ w₀)) X
  sub-shapeA Ψ w₀ a ss X =
    trans (cong (λ z → sub-Agent z (CSub،＋ a)) (NA.shapeT≡↑ ss X (wk＋ Ψ (wk-S U w₀))))
          (trans (cong (λ z → sub-Agent z (CSub،＋ a))
                       (↑ᵢ-trans (wk→⊆ (wk＋ Ψ (wk-S U w₀))) (wk→⊆ (wk＋ Ψ w₀)) ⊆،＋ X (hw＋g Ψ w₀)))
                 (sub-Agent-↑ᵢ،＋ Γ Ψ U a (↑ᵢ (wk→⊆ (wk＋ Ψ w₀)) X)))

  sub-shapeD : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : C⟦𝕍⟧ Γ U) (ss : List Shape) (X : Data Φ)
             → sub-Data (ND.shapeT ss X (wk＋ Ψ (wk-S U w₀))) (CSub،＋ {Γ} {Ψ} {U} a)
             ≡ ↑d (wk→⊆ (wk＋ Ψ w₀)) X
  sub-shapeD Ψ w₀ a ss X =
    trans (cong (λ z → sub-Data z (CSub،＋ a)) (ND.shapeT≡↑ ss X (wk＋ Ψ (wk-S U w₀))))
          (trans (cong (λ z → sub-Data z (CSub،＋ a))
                       (↑d-trans (wk→⊆ (wk＋ Ψ (wk-S U w₀))) (wk→⊆ (wk＋ Ψ w₀)) ⊆،＋ X (hw＋g Ψ w₀)))
                 (sub-Data-↑d،＋ Γ Ψ U a (↑d (wk→⊆ (wk＋ Ψ w₀)) X)))

-- for a resource variable, the substitution of a non-resource term does not matter
CSub،＋-ℝ : {Γ : Ctxt} (Ψ : Ctxt) {x : 𝕌} (a b : C⟦𝕌⟧ Γ x) (i : ∈Ctxt 𝕍ℝ ((Γ ، 𝕍𝕌 x) ＋ Ψ))
          → CSub،＋ {Γ} {Ψ} {𝕍𝕌 x} a i ≡ CSub،＋ {Γ} {Ψ} {𝕍𝕌 x} b i
CSub،＋-ℝ ⟨⟩      a b (∈CtxtS _ j) = refl
CSub،＋-ℝ (Ψ ، U) a b (∈Ctxt0 _)   = refl
CSub،＋-ℝ (Ψ ، U) a b (∈CtxtS .U j) = cong (↑v (⊆₀ {_} {U}) {𝕍ℝ}) (CSub،＋-ℝ Ψ a b j)

-- ---------------------------------------------------------------------------
-- Instantiation of formula and resource variables, and of placeholders

module _ {Φ : Ctxt} (σ : FormSub⋆ Φ) (ρ : ResSub⋆ Φ) (α : AgSub⋆ Φ) (δ : DaSub⋆ Φ) where

  μᵣ : {Δ : Ctxt} → Wk Φ Δ → Res Δ → Res Δ
  μᵣ w (𝐯 i)    = 𝐯 i
  μᵣ w 𝟎        = 𝟎
  μᵣ w (rvar x) = NR.shapeT (shapesᵣ x ρ) (app-ResSub⋆ x ρ) w
  μᵣ w (a ⋆ b)  = μᵣ w a ⋆ μᵣ w b

  μrv≡wk : {Δ : Ctxt} (w : Wk Φ Δ) (x : ResVar) → μᵣ w (rvar x) ≡ wkR w (app-ResSub⋆ x ρ)
  μrv≡wk w x = NR.shapeT≡wk (shapesᵣ x ρ) (app-ResSub⋆ x ρ) w

  μI : {Δ : Ctxt} → Wk Φ Δ → Interval Δ → Interval Δ
  μI w ［ a , b ］ = ［ μᵣ w a , μᵣ w b ］
  μI w ［ a , b ） = ［ μᵣ w a , μᵣ w b ）
  μI w （ a , b ］ = （ μᵣ w a , μᵣ w b ］
  μI w （ a , b ） = （ μᵣ w a , μᵣ w b ）

  μCE : {Δ : Ctxt} → Wk Φ Δ → CE Δ → CE Δ
  μCE w (CEr r) = CEr (μᵣ w r)
  μCE w CEu     = CEu
  μCE w (CEi i) = CEi (μI w i)

  μAg : {Δ : Ctxt} → Wk Φ Δ → Agent Δ → Agent Δ
  μAg w (agentV i) = agentV i
  μAg w (agentC k) = NA.shapeT (shapesₐ k α) (app-AgSub⋆ k α) w

  μAgs : {Δ : Ctxt} → Wk Φ Δ → Agents Δ → Agents Δ
  μAgs w (agentsV i) = agentsV i
  μAgs w (agentsL [])      = nilₐ α
  μAgs w (agentsL (a ∷ l)) = agentsL (Data.List.map (μAg w) (a ∷ l))

  μDa : {Δ : Ctxt} → Wk Φ Δ → Data Δ → Data Δ
  μDa w (dataV i) = dataV i
  μDa w (dataC k) = ND.shapeT (shapes-d k δ) (app-DaSub⋆ k δ) w

  μAt : {Δ : Ctxt} → Wk Φ Δ → Atom Δ → Atom Δ
  μAt w (atProp x)                     = atProp x
  μAt w (atAction (ActSend p a A))     = atAction (ActSend (μDa w p) (μAg w a) (μAgs w A))
  μAt w (atEvent (EvtReceive p a b))   = atEvent (EvtReceive (μDa w p) (μAg w a) (μAg w b))
  μAt w (atEvent (EvtInternal a d))    = atEvent (EvtInternal (μAg w a) (μDa w d))
  μAt w (atCorrect (FaultCorrect a b)) = atCorrect (FaultCorrect (μAg w a) (μAg w b))

  μSA : {Δ : Ctxt} → Wk Φ Δ → SetAtom Δ → SetAtom Δ
  μSA w (a ∈ₐ A)     = μAg w a ∈ₐ μAgs w A
  μSA w (∣ A ∣ₛ＝ n) = ∣ μAgs w A ∣ₛ＝ sizeOfₐ α n

  μ𝕌 : {Δ : Ctxt} {u : 𝕌} → Wk Φ Δ → C⟦𝕌⟧ Δ u → C⟦𝕌⟧ Δ u
  μ𝕌 {u = 𝕌Agent}  w a = μAg w a
  μ𝕌 {u = 𝕌Agents} w a = μAgs w a
  μ𝕌 {u = 𝕌Prop}   w a = a
  μ𝕌 {u = 𝕌Data}   w a = μDa w a

  μ : {Δ : Ctxt} → Wk Φ Δ → Form Δ → Form Δ
  μ w (𝕒 x)         = 𝕒 (μAt w x)
  μ w (var x)       = wkF w (app-FormSub⋆ x σ)
  μ w ⊤·            = ⊤·
  μ w ⊥·            = ⊥·
  μ w (f ∧· g)      = μ w f ∧· μ w g
  μ w (f ∨· g)      = μ w f ∨· μ w g
  μ w (f →· g)      = μ w f →· μ w g
  μ w (∀· u f)      = ∀· u (μ (wk-S _ w) f)
  μ w (∃· u f)      = ∃· u (μ (wk-S _ w) f)
  μ w (𝔸 A)         = 𝔸 (μSA w A)
  μ w (f Ｕ g)      = μ w f Ｕ μ w g
  μ w (Ｏ f)        = Ｏ (μ w f)
  μ w (f Ｓ g)      = μ w f Ｓ μ w g
  μ w (Ｙ f)        = Ｙ (μ w f)
  μ w (Ｂ f)        = Ｂ (μ w f)
  μ w (Ｆ f)        = Ｆ (μ (wk-S 𝕍ℝ w) f)
  μ w (t₁ ⟨ c ⟩ t₂) = μᵣ w t₁ ⟨ c ⟩ μᵣ w t₂

  -- -------------------------------------------------------------------------
  -- μ commutes with renamings

  module _ {Δ Δ′ : Ctxt} (e : Δ ⊆ Δ′) (w : Wk Φ Δ) (w′ : Wk Φ Δ′)
           (hw : (v : 𝕍) (i : ∈Ctxt v Φ) → wk→⊆ w′ i ≡ e (wk→⊆ w i)) where
    μᵣ-↑ : (r : Res Δ) → μᵣ w′ (↑ᵣ e r) ≡ ↑ᵣ e (μᵣ w r)
    μᵣ-↑ (𝐯 i)    = refl
    μᵣ-↑ 𝟎        = refl
    μᵣ-↑ (rvar x) =
      trans (NR.shapeT≡↑ (shapesᵣ x ρ) X w′)
            (trans (↑ᵣ-trans (wk→⊆ w′) (wk→⊆ w) e X hw)
                   (cong (↑ᵣ e) (sym (NR.shapeT≡↑ (shapesᵣ x ρ) X w))))
      where X = app-ResSub⋆ x ρ
    μᵣ-↑ (a ⋆ b)  = cong₂ _⋆_ (μᵣ-↑ a) (μᵣ-↑ b)

    μCE-↑ : (x : CE Δ) → μCE w′ (↑CE e x) ≡ ↑CE e (μCE w x)
    μCE-↑ (CEr r) = cong CEr (μᵣ-↑ r)
    μCE-↑ CEu     = refl
    μCE-↑ (CEi ［ a , b ］) = cong CEi (cong₂ ［_,_］ (μᵣ-↑ a) (μᵣ-↑ b))
    μCE-↑ (CEi ［ a , b ）) = cong CEi (cong₂ ［_,_） (μᵣ-↑ a) (μᵣ-↑ b))
    μCE-↑ (CEi （ a , b ］) = cong CEi (cong₂ （_,_］ (μᵣ-↑ a) (μᵣ-↑ b))
    μCE-↑ (CEi （ a , b ）) = cong CEi (cong₂ （_,_） (μᵣ-↑ a) (μᵣ-↑ b))

    μAg-↑ : (a : Agent Δ) → μAg w′ (↑ᵢ e a) ≡ ↑ᵢ e (μAg w a)
    μAg-↑ (agentV i) = refl
    μAg-↑ (agentC k) =
      trans (NA.shapeT≡↑ (shapesₐ k α) X w′)
            (trans (↑ᵢ-trans (wk→⊆ w′) (wk→⊆ w) e X hw)
                   (cong (↑ᵢ e) (sym (NA.shapeT≡↑ (shapesₐ k α) X w))))
      where X = app-AgSub⋆ k α

    μAgL-↑ : (l : List (Agent Δ))
           → Data.List.map (μAg w′) (Data.List.map (↑ᵢ e) l) ≡ Data.List.map (↑ᵢ e) (Data.List.map (μAg w) l)
    μAgL-↑ []      = refl
    μAgL-↑ (a ∷ l) = cong₂ _∷_ (μAg-↑ a) (μAgL-↑ l)

    μAgs-↑ : (A : Agents Δ) → μAgs w′ (↑ₛ e A) ≡ ↑ₛ e (μAgs w A)
    μAgs-↑ (agentsV i) = refl
    μAgs-↑ (agentsL [])      = sym (nilₐ-↑ e α)
    μAgs-↑ (agentsL (a ∷ l)) = cong agentsL (μAgL-↑ (a ∷ l))

    μDa-↑ : (d : Data Δ) → μDa w′ (↑d e d) ≡ ↑d e (μDa w d)
    μDa-↑ (dataV i) = refl
    μDa-↑ (dataC k) =
      trans (ND.shapeT≡↑ (shapes-d k δ) X w′)
            (trans (↑d-trans (wk→⊆ w′) (wk→⊆ w) e X hw)
                   (cong (↑d e) (sym (ND.shapeT≡↑ (shapes-d k δ) X w))))
      where X = app-DaSub⋆ k δ

    μAt-↑ : (x : Atom Δ) → μAt w′ (↑ₐ e x) ≡ ↑ₐ e (μAt w x)
    μAt-↑ (atProp x)                     = refl
    μAt-↑ (atAction (ActSend p a A))     =
      cong atAction (cong₃ ActSend (μDa-↑ p) (μAg-↑ a) (μAgs-↑ A))
    μAt-↑ (atEvent (EvtReceive p a b))   =
      cong atEvent (cong₃ EvtReceive (μDa-↑ p) (μAg-↑ a) (μAg-↑ b))
    μAt-↑ (atEvent (EvtInternal a d))    =
      cong atEvent (cong₂ EvtInternal (μAg-↑ a) (μDa-↑ d))
    μAt-↑ (atCorrect (FaultCorrect a b)) =
      cong atCorrect (cong₂ FaultCorrect (μAg-↑ a) (μAg-↑ b))

    μSA-↑ : (A : SetAtom Δ) → μSA w′ (↑A e A) ≡ ↑A e (μSA w A)
    μSA-↑ (a ∈ₐ A)     = cong₂ _∈ₐ_ (μAg-↑ a) (μAgs-↑ A)
    μSA-↑ (∣ A ∣ₛ＝ n) = cong (λ z → ∣ z ∣ₛ＝ sizeOfₐ α n) (μAgs-↑ A)

    μ𝕌-↑ : {u : 𝕌} (a : C⟦𝕌⟧ Δ u) → μ𝕌 w′ (↑u e {u} a) ≡ ↑u e {u} (μ𝕌 w a)
    μ𝕌-↑ {𝕌Agent}  a = μAg-↑ a
    μ𝕌-↑ {𝕌Agents} a = μAgs-↑ a
    μ𝕌-↑ {𝕌Prop}   a = refl
    μ𝕌-↑ {𝕌Data}   a = μDa-↑ a

  hw-add : {Δ Δ′ : Ctxt} (u : 𝕍) (e : Δ ⊆ Δ′) (w : Wk Φ Δ) (w′ : Wk Φ Δ′)
           (hw : (v : 𝕍) (i : ∈Ctxt v Φ) → wk→⊆ w′ i ≡ e (wk→⊆ w i))
         → (v : 𝕍) (i : ∈Ctxt v Φ)
         → wk→⊆ (wk-S u w′) i ≡ ⊆، u e (wk→⊆ (wk-S u w) i)
  hw-add u e w w′ hw v i = cong (∈CtxtS u) (hw v i)

  μ-↑ : {Δ Δ′ : Ctxt} (e : Δ ⊆ Δ′) (w : Wk Φ Δ) (w′ : Wk Φ Δ′)
        (hw : (v : 𝕍) (i : ∈Ctxt v Φ) → wk→⊆ w′ i ≡ e (wk→⊆ w i))
        (f : Form Δ)
      → μ w′ (↑ e f) ≡ ↑ e (μ w f)
  μ-↑ e w w′ hw (𝕒 x)    = cong 𝕒 (μAt-↑ e w w′ hw x)
  μ-↑ e w w′ hw (var x)  =
    trans (wkF≡↑ w′ X)
          (trans (↑-trans (wk→⊆ w′) (wk→⊆ w) e X hw)
                 (cong (↑ e) (sym (wkF≡↑ w X))))
    where X = app-FormSub⋆ x σ
  μ-↑ e w w′ hw ⊤·       = refl
  μ-↑ e w w′ hw ⊥·       = refl
  μ-↑ e w w′ hw (f ∧· g) = cong₂ _∧·_ (μ-↑ e w w′ hw f) (μ-↑ e w w′ hw g)
  μ-↑ e w w′ hw (f ∨· g) = cong₂ _∨·_ (μ-↑ e w w′ hw f) (μ-↑ e w w′ hw g)
  μ-↑ e w w′ hw (f →· g) = cong₂ _→·_ (μ-↑ e w w′ hw f) (μ-↑ e w w′ hw g)
  μ-↑ e w w′ hw (∀· u f) =
    cong (∀· u) (μ-↑ (⊆، _ e) (wk-S _ w) (wk-S _ w′) (hw-add _ e w w′ hw) f)
  μ-↑ e w w′ hw (∃· u f) =
    cong (∃· u) (μ-↑ (⊆، _ e) (wk-S _ w) (wk-S _ w′) (hw-add _ e w w′ hw) f)
  μ-↑ e w w′ hw (𝔸 A)    = cong 𝔸 (μSA-↑ e w w′ hw A)
  μ-↑ e w w′ hw (f Ｕ g) = cong₂ _Ｕ_ (μ-↑ e w w′ hw f) (μ-↑ e w w′ hw g)
  μ-↑ e w w′ hw (Ｏ f)   = cong Ｏ (μ-↑ e w w′ hw f)
  μ-↑ e w w′ hw (f Ｓ g) = cong₂ _Ｓ_ (μ-↑ e w w′ hw f) (μ-↑ e w w′ hw g)
  μ-↑ e w w′ hw (Ｙ f)   = cong Ｙ (μ-↑ e w w′ hw f)
  μ-↑ e w w′ hw (Ｂ f)   = cong Ｂ (μ-↑ e w w′ hw f)
  μ-↑ e w w′ hw (Ｆ f)   =
    cong Ｆ_ (μ-↑ (⊆، _ e) (wk-S _ w) (wk-S _ w′) (hw-add _ e w w′ hw) f)
  μ-↑ e w w′ hw (a ⟨ c ⟩ b) =
    cong₂ (λ x y → x ⟨ c ⟩ y) (μᵣ-↑ e w w′ hw a) (μᵣ-↑ e w w′ hw b)

  -- -------------------------------------------------------------------------
  -- μ on the atoms commutes with a substitution for a bound variable of sort
  -- U, if it does on the variables (E); the placeholders are only weakened

  μ𝕌-var : {Δ : Ctxt} {y : 𝕌} (w : Wk Φ Δ) (i : ∈Ctxt (𝕍𝕌 y) Δ)
         → μ𝕌 {Δ} {y} w (𝕌CSub-var i) ≡ 𝕌CSub-var i
  μ𝕌-var {y = 𝕌Agent}  w i = refl
  μ𝕌-var {y = 𝕌Agents} w i = refl
  μ𝕌-var {y = 𝕌Prop}   w i = refl
  μ𝕌-var {y = 𝕌Data}   w i = refl

  module _ {Γ : Ctxt} (U : 𝕍) (Ψ : Ctxt) (w₀ : Wk Φ Γ) (v v′ : C⟦𝕍⟧ Γ U)
           (E : {y : 𝕌} (i : ∈Ctxt (𝕍𝕌 y) ((Γ ، U) ＋ Ψ))
              → μ𝕌 {_} {y} (wk＋ Ψ w₀) (CSub،＋ {Γ} {Ψ} {U} v i) ≡ CSub،＋ {Γ} {Ψ} {U} v′ i) where
    private
      Wₛ Wₛ′ : Wk Φ _
      Wₛ  = wk＋ Ψ w₀
      Wₛ′ = wk＋ Ψ (wk-S U w₀)
      c c′ : CSub ((Γ ، U) ＋ Ψ) (Γ ＋ Ψ)
      c  = CSub،＋ {Γ} {Ψ} {U} v
      c′ = CSub،＋ {Γ} {Ψ} {U} v′

    μAg-sub : (b : Agent ((Γ ، U) ＋ Ψ)) → μAg Wₛ (sub-Agent b c) ≡ sub-Agent (μAg Wₛ′ b) c′
    μAg-sub (agentV i) = E i
    μAg-sub (agentC k) =
      trans (NA.shapeT≡↑ (shapesₐ k α) (app-AgSub⋆ k α) Wₛ)
            (sym (sub-shapeA U Ψ w₀ v′ (shapesₐ k α) (app-AgSub⋆ k α)))

    μAgL-sub : (l : List (Agent ((Γ ، U) ＋ Ψ)))
             → Data.List.map (μAg Wₛ) (Data.List.map (λ z → sub-Agent z c) l)
             ≡ Data.List.map (λ z → sub-Agent z c′) (Data.List.map (μAg Wₛ′) l)
    μAgL-sub []      = refl
    μAgL-sub (a ∷ l) = cong₂ _∷_ (μAg-sub a) (μAgL-sub l)

    μAgs-sub : (A : Agents ((Γ ، U) ＋ Ψ)) → μAgs Wₛ (sub-Agents A c) ≡ sub-Agents (μAgs Wₛ′ A) c′
    μAgs-sub (agentsV i) = E i
    μAgs-sub (agentsL [])      = sym (nilₐ-sub c′ α)
    μAgs-sub (agentsL (a ∷ l)) = cong agentsL (μAgL-sub (a ∷ l))

    μDa-sub : (d : Data ((Γ ، U) ＋ Ψ)) → μDa Wₛ (sub-Data d c) ≡ sub-Data (μDa Wₛ′ d) c′
    μDa-sub (dataV i) = E i
    μDa-sub (dataC k) =
      trans (ND.shapeT≡↑ (shapes-d k δ) (app-DaSub⋆ k δ) Wₛ)
            (sym (sub-shapeD U Ψ w₀ v′ (shapes-d k δ) (app-DaSub⋆ k δ)))

    μAP-sub : (p : AtomProp ((Γ ، U) ＋ Ψ)) → sub-AtomProp p c ≡ sub-AtomProp p c′
    μAP-sub (atomPropV i) = E i
    μAP-sub (atomPropC x) = refl

    μAt-sub : (x : Atom ((Γ ، U) ＋ Ψ)) → μAt Wₛ (sub-Atom x c) ≡ sub-Atom (μAt Wₛ′ x) c′
    μAt-sub (atProp x) = cong atProp (μAP-sub x)
    μAt-sub (atAction (ActSend p a A)) =
      cong atAction (cong₃ ActSend (μDa-sub p) (μAg-sub a) (μAgs-sub A))
    μAt-sub (atEvent (EvtReceive p a b)) =
      cong atEvent (cong₃ EvtReceive (μDa-sub p) (μAg-sub a) (μAg-sub b))
    μAt-sub (atEvent (EvtInternal a d)) =
      cong atEvent (cong₂ EvtInternal (μAg-sub a) (μDa-sub d))
    μAt-sub (atCorrect (FaultCorrect a b)) =
      cong atCorrect (cong₂ FaultCorrect (μAg-sub a) (μAg-sub b))

    μSA-sub : (A : SetAtom ((Γ ، U) ＋ Ψ)) → μSA Wₛ (sub-SetAtom A c) ≡ sub-SetAtom (μSA Wₛ′ A) c′
    μSA-sub (a ∈ₐ A)     = cong₂ _∈ₐ_ (μAg-sub a) (μAgs-sub A)
    μSA-sub (∣ A ∣ₛ＝ n) = cong (λ z → ∣ z ∣ₛ＝ sizeOfₐ α n) (μAgs-sub A)

  -- -------------------------------------------------------------------------
  -- μ commutes with the substitution of a resource for a bound variable

  module _ {Γ : Ctxt} where
    hw＋ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (v : 𝕍) (i : ∈Ctxt v Φ)
         → wk→⊆ (wk＋ Ψ (wk-S 𝕍ℝ w₀)) i ≡ ⊆،＋ {Γ} {Ψ} {𝕍ℝ} (wk→⊆ (wk＋ Ψ w₀) i)
    hw＋ ⟨⟩      w₀ v i = refl
    hw＋ (Ψ ، U) w₀ v i = cong (∈CtxtS U) (hw＋ Ψ w₀ v i)

    CSub،＋-𝕌 : (Ψ : Ctxt) (a b : Res Γ) {x : 𝕌} (i : ∈Ctxt (𝕍𝕌 x) ((Γ ، 𝕍ℝ) ＋ Ψ))
              → CSub،＋ {Γ} {Ψ} {𝕍ℝ} a i ≡ CSub،＋ {Γ} {Ψ} {𝕍ℝ} b i
    CSub،＋-𝕌 ⟨⟩      a b (∈CtxtS .𝕍ℝ j) = refl
    CSub،＋-𝕌 (Ψ ، U) a b (∈Ctxt0 _)     = refl
    CSub،＋-𝕌 (Ψ ، U) a b {x} (∈CtxtS .U j) =
      cong (↑v (⊆₀ {_} {U}) {𝕍𝕌 x}) (CSub،＋-𝕌 Ψ a b j)

    -- the results of the substitution at the other sorts are variables, which
    -- μ leaves alone
    μ𝕌-CSubℝ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : Res Γ) {y : 𝕌} (i : ∈Ctxt (𝕍𝕌 y) ((Γ ، 𝕍ℝ) ＋ Ψ))
             → μ𝕌 {_} {y} (wk＋ Ψ w₀) (CSub،＋ {Γ} {Ψ} {𝕍ℝ} a i) ≡ CSub،＋ {Γ} {Ψ} {𝕍ℝ} a i
    μ𝕌-CSubℝ ⟨⟩      w₀ a (∈CtxtS .𝕍ℝ j) = μ𝕌-var w₀ j
    μ𝕌-CSubℝ (Ψ ، U) w₀ a (∈Ctxt0 _)     = μ𝕌-var (wk-S _ (wk＋ Ψ w₀)) (∈Ctxt0 _)
    μ𝕌-CSubℝ (Ψ ، U) w₀ a {y} (∈CtxtS .U j) =
      trans (μ𝕌-↑ ⊆₀ (wk＋ Ψ w₀) (wk-S U (wk＋ Ψ w₀)) (λ _ _ → refl) {y} (CSub،＋ a j))
            (cong (↑u ⊆₀ {y}) (μ𝕌-CSubℝ Ψ w₀ a j))

    μᵣ-sub-var : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : Res Γ) (i : ∈Ctxt 𝕍ℝ ((Γ ، 𝕍ℝ) ＋ Ψ))
               → μᵣ (wk＋ Ψ w₀) (CSub،＋ {Γ} {Ψ} {𝕍ℝ} a i)
               ≡ CSub،＋ {Γ} {Ψ} {𝕍ℝ} (μᵣ w₀ a) i
    μᵣ-sub-var ⟨⟩      w₀ a (∈Ctxt0 _)       = refl
    μᵣ-sub-var ⟨⟩      w₀ a (∈CtxtS .𝕍ℝ j)  = refl
    μᵣ-sub-var (Ψ ، U) w₀ a (∈Ctxt0 _)       = refl
    μᵣ-sub-var (Ψ ، U) w₀ a (∈CtxtS .U j)    =
      trans (μᵣ-↑ ⊆₀ (wk＋ Ψ w₀) (wk-S U (wk＋ Ψ w₀)) (λ _ _ → refl) (CSub،＋ a j))
            (cong (↑ᵣ ⊆₀) (μᵣ-sub-var Ψ w₀ a j))

    -- the bodies of instantiated variables are only weakened, so the
    -- substitution leaves them alone
    sub-wkR : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : Res Γ) (X : Res Φ)
            → sub-Res (wkR (wk＋ Ψ (wk-S 𝕍ℝ w₀)) X) (CSub،＋ {Γ} {Ψ} {𝕍ℝ} a)
            ≡ wkR (wk＋ Ψ w₀) X
    sub-wkR Ψ w₀ a X =
      trans (cong (λ z → sub-Res z (CSub،＋ a)) (wkR≡↑ (wk＋ Ψ (wk-S 𝕍ℝ w₀)) X))
            (trans (cong (λ z → sub-Res z (CSub،＋ a))
                         (↑ᵣ-trans (wk→⊆ (wk＋ Ψ (wk-S 𝕍ℝ w₀))) (wk→⊆ (wk＋ Ψ w₀)) ⊆،＋ X
                                   (hw＋ Ψ w₀)))
                   (trans (sub-Res-↑ᵣ،＋ Γ Ψ 𝕍ℝ a (↑ᵣ (wk→⊆ (wk＋ Ψ w₀)) X))
                          (sym (wkR≡↑ (wk＋ Ψ w₀) X))))

    sub-wkF : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : Res Γ) (X : Form Φ)
            → sub (wkF (wk＋ Ψ (wk-S 𝕍ℝ w₀)) X) (CSub،＋ {Γ} {Ψ} {𝕍ℝ} a)
            ≡ wkF (wk＋ Ψ w₀) X
    sub-wkF Ψ w₀ a X =
      trans (cong (λ z → sub z (CSub،＋ a)) (wkF≡↑ (wk＋ Ψ (wk-S 𝕍ℝ w₀)) X))
            (trans (cong (λ z → sub z (CSub،＋ a))
                         (↑-trans (wk→⊆ (wk＋ Ψ (wk-S 𝕍ℝ w₀))) (wk→⊆ (wk＋ Ψ w₀)) ⊆،＋ X
                                  (hw＋ Ψ w₀)))
                   (trans (sub-↑،＋ Γ Ψ 𝕍ℝ a (↑ (wk→⊆ (wk＋ Ψ w₀)) X))
                          (sym (wkF≡↑ (wk＋ Ψ w₀) X))))

    μᵣ-sub : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : Res Γ) (r : Res ((Γ ، 𝕍ℝ) ＋ Ψ))
           → μᵣ (wk＋ Ψ w₀) (sub-Res r (CSub،＋ {Γ} {Ψ} {𝕍ℝ} a))
           ≡ sub-Res (μᵣ (wk＋ Ψ (wk-S 𝕍ℝ w₀)) r) (CSub،＋ {Γ} {Ψ} {𝕍ℝ} (μᵣ w₀ a))
    μᵣ-sub Ψ w₀ a (𝐯 i)    = μᵣ-sub-var Ψ w₀ a i
    μᵣ-sub Ψ w₀ a 𝟎        = refl
    μᵣ-sub Ψ w₀ a (rvar x) =
      trans (μrv≡wk (wk＋ Ψ w₀) x)
            (trans (sym (sub-wkR Ψ w₀ (μᵣ w₀ a) (app-ResSub⋆ x ρ)))
                   (cong (λ z → sub-Res z (CSub،＋ (μᵣ w₀ a))) (sym (μrv≡wk (wk＋ Ψ (wk-S 𝕍ℝ w₀)) x))))
    μᵣ-sub Ψ w₀ a (r ⋆ s)  = cong₂ _⋆_ (μᵣ-sub Ψ w₀ a r) (μᵣ-sub Ψ w₀ a s)

  μ-sub : {Γ : Ctxt} (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : Res Γ) (f : Form ((Γ ، 𝕍ℝ) ＋ Ψ))
        → μ (wk＋ Ψ w₀) (sub f (CSub،＋ {Γ} {Ψ} {𝕍ℝ} a))
        ≡ sub (μ (wk＋ Ψ (wk-S 𝕍ℝ w₀)) f) (CSub،＋ {Γ} {Ψ} {𝕍ℝ} (μᵣ w₀ a))
  μ-sub Ψ w₀ a (𝕒 x)    = cong 𝕒 (μAt-sub 𝕍ℝ Ψ w₀ a (μᵣ w₀ a) Eℝ x)
    where Eℝ : {y : 𝕌} (i : ∈Ctxt (𝕍𝕌 y) ((_ ، 𝕍ℝ) ＋ Ψ)) → _
          Eℝ i = trans (μ𝕌-CSubℝ Ψ w₀ a i) (CSub،＋-𝕌 Ψ a (μᵣ w₀ a) i)
  μ-sub Ψ w₀ a (var x)  = sym (sub-wkF Ψ w₀ (μᵣ w₀ a) (app-FormSub⋆ x σ))
  μ-sub Ψ w₀ a ⊤·       = refl
  μ-sub Ψ w₀ a ⊥·       = refl
  μ-sub Ψ w₀ a (f ∧· g) = cong₂ _∧·_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (f ∨· g) = cong₂ _∨·_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (f →· g) = cong₂ _→·_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (∀· u f) = cong (∀· u) (μ-sub (Ψ ، 𝕍𝕌 u) w₀ a f)
  μ-sub Ψ w₀ a (∃· u f) = cong (∃· u) (μ-sub (Ψ ، 𝕍𝕌 u) w₀ a f)
  μ-sub Ψ w₀ a (𝔸 A)    = cong 𝔸 (μSA-sub 𝕍ℝ Ψ w₀ a (μᵣ w₀ a) Eℝ A)
    where Eℝ : {y : 𝕌} (i : ∈Ctxt (𝕍𝕌 y) ((_ ، 𝕍ℝ) ＋ Ψ)) → _
          Eℝ i = trans (μ𝕌-CSubℝ Ψ w₀ a i) (CSub،＋-𝕌 Ψ a (μᵣ w₀ a) i)
  μ-sub Ψ w₀ a (f Ｕ g) = cong₂ _Ｕ_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (Ｏ f)   = cong Ｏ (μ-sub Ψ w₀ a f)
  μ-sub Ψ w₀ a (f Ｓ g) = cong₂ _Ｓ_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (Ｙ f)   = cong Ｙ (μ-sub Ψ w₀ a f)
  μ-sub Ψ w₀ a (Ｂ f)   = cong Ｂ (μ-sub Ψ w₀ a f)
  μ-sub Ψ w₀ a (Ｆ f)   = cong Ｆ_ (μ-sub (Ψ ، 𝕍ℝ) w₀ a f)
  μ-sub Ψ w₀ a (r ⟨ c ⟩ s) =
    cong₂ (λ x y → x ⟨ c ⟩ y) (μᵣ-sub Ψ w₀ a r) (μᵣ-sub Ψ w₀ a s)

  -- -------------------------------------------------------------------------
  -- μ commutes with the substitution of an agent/agents/proposition/data
  -- term for a bound variable (for ∀L and ∃R), if μ is applied to the term

  module _ {Γ : Ctxt} {x : 𝕌} where
    private
      U : 𝕍
      U = 𝕍𝕌 x

    hw＋ᵤ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (v : 𝕍) (i : ∈Ctxt v Φ)
          → wk→⊆ (wk＋ Ψ (wk-S U w₀)) i ≡ ⊆،＋ {Γ} {Ψ} {U} (wk→⊆ (wk＋ Ψ w₀) i)
    hw＋ᵤ ⟨⟩      w₀ v i = refl
    hw＋ᵤ (Ψ ، V) w₀ v i = cong (∈CtxtS V) (hw＋ᵤ Ψ w₀ v i)

    sub-wkRᵤ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : C⟦𝕌⟧ Γ x) (X : Res Φ)
             → sub-Res (wkR (wk＋ Ψ (wk-S U w₀)) X) (CSub،＋ {Γ} {Ψ} {U} a)
             ≡ wkR (wk＋ Ψ w₀) X
    sub-wkRᵤ Ψ w₀ a X =
      trans (cong (λ z → sub-Res z (CSub،＋ a)) (wkR≡↑ (wk＋ Ψ (wk-S U w₀)) X))
            (trans (cong (λ z → sub-Res z (CSub،＋ a))
                         (↑ᵣ-trans (wk→⊆ (wk＋ Ψ (wk-S U w₀))) (wk→⊆ (wk＋ Ψ w₀)) ⊆،＋ X
                                   (hw＋ᵤ Ψ w₀)))
                   (trans (sub-Res-↑ᵣ،＋ Γ Ψ U a (↑ᵣ (wk→⊆ (wk＋ Ψ w₀)) X))
                          (sym (wkR≡↑ (wk＋ Ψ w₀) X))))

    sub-wkFᵤ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : C⟦𝕌⟧ Γ x) (X : Form Φ)
             → sub (wkF (wk＋ Ψ (wk-S U w₀)) X) (CSub،＋ {Γ} {Ψ} {U} a)
             ≡ wkF (wk＋ Ψ w₀) X
    sub-wkFᵤ Ψ w₀ a X =
      trans (cong (λ z → sub z (CSub،＋ a)) (wkF≡↑ (wk＋ Ψ (wk-S U w₀)) X))
            (trans (cong (λ z → sub z (CSub،＋ a))
                         (↑-trans (wk→⊆ (wk＋ Ψ (wk-S U w₀))) (wk→⊆ (wk＋ Ψ w₀)) ⊆،＋ X
                                  (hw＋ᵤ Ψ w₀)))
                   (trans (sub-↑،＋ Γ Ψ U a (↑ (wk→⊆ (wk＋ Ψ w₀)) X))
                          (sym (wkF≡↑ (wk＋ Ψ w₀) X))))

    -- time variables are only renamed by the substitution, and μ leaves
    -- them alone
    μᵣ-sub-varᵤ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : C⟦𝕌⟧ Γ x) (i : ∈Ctxt 𝕍ℝ ((Γ ، U) ＋ Ψ))
                → μᵣ (wk＋ Ψ w₀) (CSub،＋ {Γ} {Ψ} {U} a i) ≡ CSub،＋ {Γ} {Ψ} {U} a i
    μᵣ-sub-varᵤ ⟨⟩      w₀ a (∈CtxtS .U j)  = refl
    μᵣ-sub-varᵤ (Ψ ، V) w₀ a (∈Ctxt0 _)     = refl
    μᵣ-sub-varᵤ (Ψ ، V) w₀ a (∈CtxtS .V j)  =
      trans (μᵣ-↑ ⊆₀ (wk＋ Ψ w₀) (wk-S V (wk＋ Ψ w₀)) (λ _ _ → refl) (CSub،＋ a j))
            (cong (↑ᵣ ⊆₀) (μᵣ-sub-varᵤ Ψ w₀ a j))

    μᵣ-subᵤ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a a′ : C⟦𝕌⟧ Γ x) (r : Res ((Γ ، U) ＋ Ψ))
            → μᵣ (wk＋ Ψ w₀) (sub-Res r (CSub،＋ {Γ} {Ψ} {U} a))
            ≡ sub-Res (μᵣ (wk＋ Ψ (wk-S U w₀)) r) (CSub،＋ {Γ} {Ψ} {U} a′)
    μᵣ-subᵤ Ψ w₀ a a′ (𝐯 i)    = trans (μᵣ-sub-varᵤ Ψ w₀ a i) (CSub،＋-ℝ Ψ a a′ i)
    μᵣ-subᵤ Ψ w₀ a a′ 𝟎        = refl
    μᵣ-subᵤ Ψ w₀ a a′ (rvar y) =
      trans (μrv≡wk (wk＋ Ψ w₀) y)
            (trans (sym (sub-wkRᵤ Ψ w₀ a′ (app-ResSub⋆ y ρ)))
                   (cong (λ z → sub-Res z (CSub،＋ a′)) (sym (μrv≡wk (wk＋ Ψ (wk-S U w₀)) y))))
    μᵣ-subᵤ Ψ w₀ a a′ (r ⋆ s)  = cong₂ _⋆_ (μᵣ-subᵤ Ψ w₀ a a′ r) (μᵣ-subᵤ Ψ w₀ a a′ s)

    -- μ applied after the substitution reaches the substituted term
    μ𝕌-CSubᵤ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : C⟦𝕌⟧ Γ x) {y : 𝕌} (i : ∈Ctxt (𝕍𝕌 y) ((Γ ، U) ＋ Ψ))
             → μ𝕌 {_} {y} (wk＋ Ψ w₀) (CSub،＋ {Γ} {Ψ} {U} a i) ≡ CSub،＋ {Γ} {Ψ} {U} (μ𝕌 w₀ a) i
    μ𝕌-CSubᵤ ⟨⟩      w₀ a (∈Ctxt0 _)      = refl
    μ𝕌-CSubᵤ ⟨⟩      w₀ a (∈CtxtS .U j)  = μ𝕌-var w₀ j
    μ𝕌-CSubᵤ (Ψ ، V) w₀ a (∈Ctxt0 _)      = μ𝕌-var (wk-S _ (wk＋ Ψ w₀)) (∈Ctxt0 _)
    μ𝕌-CSubᵤ (Ψ ، V) w₀ a {y} (∈CtxtS .V j) =
      trans (μ𝕌-↑ ⊆₀ (wk＋ Ψ w₀) (wk-S V (wk＋ Ψ w₀)) (λ _ _ → refl) {y} (CSub،＋ a j))
            (cong (↑u ⊆₀ {y}) (μ𝕌-CSubᵤ Ψ w₀ a j))

    μ-subᵤ : (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : C⟦𝕌⟧ Γ x) (f : Form ((Γ ، U) ＋ Ψ))
           → μ (wk＋ Ψ w₀) (sub f (CSub،＋ {Γ} {Ψ} {U} a))
           ≡ sub (μ (wk＋ Ψ (wk-S U w₀)) f) (CSub،＋ {Γ} {Ψ} {U} (μ𝕌 w₀ a))
    μ-subᵤ Ψ w₀ a (𝕒 y)    = cong 𝕒 (μAt-sub U Ψ w₀ a (μ𝕌 w₀ a) (μ𝕌-CSubᵤ Ψ w₀ a) y)
    μ-subᵤ Ψ w₀ a (var y)  = sym (sub-wkFᵤ Ψ w₀ (μ𝕌 w₀ a) (app-FormSub⋆ y σ))
    μ-subᵤ Ψ w₀ a ⊤·       = refl
    μ-subᵤ Ψ w₀ a ⊥·       = refl
    μ-subᵤ Ψ w₀ a (f ∧· g) = cong₂ _∧·_ (μ-subᵤ Ψ w₀ a f) (μ-subᵤ Ψ w₀ a g)
    μ-subᵤ Ψ w₀ a (f ∨· g) = cong₂ _∨·_ (μ-subᵤ Ψ w₀ a f) (μ-subᵤ Ψ w₀ a g)
    μ-subᵤ Ψ w₀ a (f →· g) = cong₂ _→·_ (μ-subᵤ Ψ w₀ a f) (μ-subᵤ Ψ w₀ a g)
    μ-subᵤ Ψ w₀ a (∀· u f) = cong (∀· u) (μ-subᵤ (Ψ ، 𝕍𝕌 u) w₀ a f)
    μ-subᵤ Ψ w₀ a (∃· u f) = cong (∃· u) (μ-subᵤ (Ψ ، 𝕍𝕌 u) w₀ a f)
    μ-subᵤ Ψ w₀ a (𝔸 A)    = cong 𝔸 (μSA-sub U Ψ w₀ a (μ𝕌 w₀ a) (μ𝕌-CSubᵤ Ψ w₀ a) A)
    μ-subᵤ Ψ w₀ a (f Ｕ g) = cong₂ _Ｕ_ (μ-subᵤ Ψ w₀ a f) (μ-subᵤ Ψ w₀ a g)
    μ-subᵤ Ψ w₀ a (Ｏ f)   = cong Ｏ (μ-subᵤ Ψ w₀ a f)
    μ-subᵤ Ψ w₀ a (f Ｓ g) = cong₂ _Ｓ_ (μ-subᵤ Ψ w₀ a f) (μ-subᵤ Ψ w₀ a g)
    μ-subᵤ Ψ w₀ a (Ｙ f)   = cong Ｙ (μ-subᵤ Ψ w₀ a f)
    μ-subᵤ Ψ w₀ a (Ｂ f)   = cong Ｂ (μ-subᵤ Ψ w₀ a f)
    μ-subᵤ Ψ w₀ a (Ｆ f)   = cong Ｆ_ (μ-subᵤ (Ψ ، 𝕍ℝ) w₀ a f)
    μ-subᵤ Ψ w₀ a (r ⟨ c ⟩ s) =
      cong₂ (λ y z → y ⟨ c ⟩ z) (μᵣ-subᵤ Ψ w₀ a (μ𝕌 w₀ a) r) (μᵣ-subᵤ Ψ w₀ a (μ𝕌 w₀ a) s)

-- ---------------------------------------------------------------------------
-- Plugging a closed context into Γ

module _ (Γ : ℂ₀) (σ : FormSub⋆ (ℂtxt Γ)) (ρ : ResSub⋆ (ℂtxt Γ))
         (α : AgSub⋆ (ℂtxt Γ)) (δ : DaSub⋆ (ℂtxt Γ)) where

  plugₐ   : ℂ₀ → ℂ₀
  plug-s : (Δ : ℂ₀) → ℂtxt Δ ⊆⋆ ℂtxt (plugₐ Δ)
  plug-w : (Δ : ℂ₀) → Wk (ℂtxt Γ) (ℂtxt (plugₐ Δ))

  ⟪_⟫ : (Δ : ℂ₀) → ℂForm Δ → ℂForm (plugₐ Δ)
  ⟪ Δ ⟫ f = μ σ ρ α δ (plug-w Δ) (↑⋆ (plug-s Δ) f)

  ⟪_⟫ᵣ : (Δ : ℂ₀) → ℂRes Δ → ℂRes (plugₐ Δ)
  ⟪ Δ ⟫ᵣ r = μᵣ σ ρ α δ (plug-w Δ) (↑⋆ᵣ (plug-s Δ) r)

  ⟪_⟫CE : (Δ : ℂ₀) → ℂCE Δ → ℂCE (plugₐ Δ)
  ⟪ Δ ⟫CE x = μCE σ ρ α δ (plug-w Δ) (↑⋆CE (plug-s Δ) x)

  plugₐ ℂ⟨⟩        = Γ
  plugₐ (ℂx c f a) = ℂx (plugₐ c) (⟪ c ⟫ f) (⟪ c ⟫CE a)
  plugₐ (ℂv c v)   = ℂv (plugₐ c) v

  plug-s ℂ⟨⟩        = ⊆⋆-init (ℂtxt Γ)
  plug-s (ℂx c f a) = plug-s c
  plug-s (ℂv c v)   = ⊆⋆-add v (plug-s c)

  plug-w ℂ⟨⟩        = wk-id
  plug-w (ℂx c f a) = plug-w c
  plug-w (ℂv c v)   = wk-S v (plug-w c)

  -- weakening by ⊆₀ commutes with ⟪_⟫
  ⟪⟫ᵣ-↑₀ : (Δ : ℂ₀) (v : 𝕍) (r : ℂRes Δ)
         → ⟪ ℂv Δ v ⟫ᵣ (↑ᵣ₀ r) ≡ ↑ᵣ₀ (⟪ Δ ⟫ᵣ r)
  ⟪⟫ᵣ-↑₀ Δ v r =
    trans (cong (μᵣ σ ρ α δ (wk-S v (plug-w Δ))) (⋆↑ᵣ₀-add v (plug-s Δ) r))
          (μᵣ-↑ σ ρ α δ ⊆₀ (plug-w Δ) (wk-S v (plug-w Δ)) (λ _ _ → refl) (↑⋆ᵣ (plug-s Δ) r))

  ⟪⟫-↑₀ : (Δ : ℂ₀) (v : 𝕍) (f : ℂForm Δ)
        → ⟪ ℂv Δ v ⟫ (↑₀ f) ≡ ↑₀ (⟪ Δ ⟫ f)
  ⟪⟫-↑₀ Δ v f =
    trans (cong (μ σ ρ α δ (wk-S v (plug-w Δ))) (⋆↑₀-add v (plug-s Δ) f))
          (μ-↑ σ ρ α δ ⊆₀ (plug-w Δ) (wk-S v (plug-w Δ)) (λ _ _ → refl) (↑⋆ (plug-s Δ) f))

  ⟪⟫CE-↑₀ : (Δ : ℂ₀) (v : 𝕍) (x : ℂCE Δ)
          → ↑CE₀ (⟪ Δ ⟫CE x) ≡ ⟪ ℂv Δ v ⟫CE (↑CE₀ x)
  ⟪⟫CE-↑₀ Δ v x =
    trans (sym (μCE-↑ σ ρ α δ ⊆₀ (plug-w Δ) (wk-S v (plug-w Δ)) (λ _ _ → refl) (↑⋆CE (plug-s Δ) x)))
          (cong (μCE σ ρ α δ (wk-S v (plug-w Δ))) (↑CE₀-↑⋆CE v (plug-s Δ) x))

  pointCE-⟪⟫ : (Δ : ℂ₀) {x : ℂCE Δ} → pointCE x → pointCE (⟪ Δ ⟫CE x)
  pointCE-⟪⟫ Δ (ptR r) = ptR _
  pointCE-⟪⟫ Δ ptU     = ptU

  plug-Ax : {Δ : ℂ₀} {r : ℂCE Δ} {A : ℂForm Δ}
          → Ax Δ r A → Ax (plugₐ Δ) (⟪ Δ ⟫CE r) (⟪ Δ ⟫ A)
  plug-Ax (found c f a)  = found (plugₐ c) (⟪ c ⟫ f) (⟪ c ⟫CE a)
  plug-Ax (skip f a h)   = skip _ _ (plug-Ax h)
  plug-Ax (down {c} {v} {x} {C} h) =
    subst₂ (Ax (ℂv (plugₐ c) v)) (⟪⟫CE-↑₀ c v x) (sym (⟪⟫-↑₀ c v C)) (down (plug-Ax h))

  -- instantiation commutes with substituting a resource for the bound variable
  ⟪⟫-subℝ : (Δ : ℂ₀) (r : ℂRes Δ) (A : ℂForm (ℂv Δ 𝕍ℝ))
          → ⟪ Δ ⟫ (subℝ A r) ≡ subℝ (⟪ ℂv Δ 𝕍ℝ ⟫ A) (⟪ Δ ⟫ᵣ r)
  ⟪⟫-subℝ Δ r A =
    trans (cong (μ σ ρ α δ (plug-w Δ))
                (↑⋆-sub (⊆⋆-add 𝕍ℝ s) s (CSub،ₗ r) (CSub،ₗ (↑⋆ᵣ s r)) Hs A))
          (μ-sub σ ρ α δ ⟨⟩ (plug-w Δ) (↑⋆ᵣ s r) (↑⋆ (⊆⋆-add 𝕍ℝ s) A))
    where
    s : ℂtxt Δ ⊆⋆ ℂtxt (plugₐ Δ)
    s = plug-s Δ

    Hs : {v : 𝕍} (i : ∈Ctxt v (ℂtxt Δ ، 𝕍ℝ))
       → CSub،ₗ {_} {𝕍ℝ} (↑⋆ᵣ s r) {v} (app-⊆⋆ (⊆⋆-add 𝕍ℝ s) v i)
       ≡ ↑⋆v s {v} (CSub،ₗ {_} {𝕍ℝ} r {v} i)
    Hs {.𝕍ℝ} (∈Ctxt0 _)      = refl
    Hs {v}   (∈CtxtS .𝕍ℝ i) = sym (↑⋆v-CSub-var s {v} i)

  -- the same for a term of sort u (∀L, ∃R)
  ⟪⟫-subᵤ : (Δ : ℂ₀) (u : 𝕌) (v : ℂ⟦𝕌⟧ Δ u) (A : ℂForm (ℂv Δ (𝕍𝕌 u)))
          → ⟪ Δ ⟫ (sub A (CSub،ₗ {_} {𝕍𝕌 u} v))
          ≡ sub (⟪ ℂv Δ (𝕍𝕌 u) ⟫ A) (CSub،ₗ {_} {𝕍𝕌 u} (μ𝕌 σ ρ α δ (plug-w Δ) (↑⋆u (plug-s Δ) v)))
  ⟪⟫-subᵤ Δ u v A =
    trans (cong (μ σ ρ α δ (plug-w Δ))
                (↑⋆-sub (⊆⋆-add (𝕍𝕌 u) s) s (CSub،ₗ v) (CSub،ₗ (↑⋆u s v)) Hs A))
          (μ-subᵤ σ ρ α δ ⟨⟩ (plug-w Δ) (↑⋆u s v) (↑⋆ (⊆⋆-add (𝕍𝕌 u) s) A))
    where
    s : ℂtxt Δ ⊆⋆ ℂtxt (plugₐ Δ)
    s = plug-s Δ

    Hs : {w : 𝕍} (i : ∈Ctxt w (ℂtxt Δ ، 𝕍𝕌 u))
       → CSub،ₗ {_} {𝕍𝕌 u} (↑⋆u s v) {w} (app-⊆⋆ (⊆⋆-add (𝕍𝕌 u) s) w i)
       ≡ ↑⋆v s {w} (CSub،ₗ {_} {𝕍𝕌 u} v {w} i)
    Hs {.(𝕍𝕌 u)} (∈Ctxt0 _)          = refl
    Hs {w}       (∈CtxtS .(𝕍𝕌 u) i) = sym (↑⋆v-CSub-var s {w} i)

  ⟪_⟫I : (Δ : ℂ₀) → ℂInterval Δ → ℂInterval (plugₐ Δ)
  ⟪ Δ ⟫I i = μI σ ρ α δ (plug-w Δ) (↑⋆I (plug-s Δ) i)

  ⟪⟫-interval : (Δ : ℂ₀) (r : ℂRes Δ) (i : ℂInterval Δ)
              → ⟪ Δ ⟫ (interval r i) ≡ interval (⟪ Δ ⟫ᵣ r) (⟪ Δ ⟫I i)
  ⟪⟫-interval Δ r ［ a , b ］ = refl
  ⟪⟫-interval Δ r ［ a , b ） = refl
  ⟪⟫-interval Δ r （ a , b ］ = refl
  ⟪⟫-interval Δ r （ a , b ） = refl

  -- Casts for the premises of the rules that bind a time point x (𝕣₀):
  -- the instantiated premise only matches up to ⟪⟫ᵣ-↑₀, ⟪⟫-↑₀ and ⟪⟫CE-↑₀.
  module _ {Δ′ : ℂ₀} where
    private
      X : ℂ₀
      X = ℂv Δ′ 𝕍ℝ

    -- ＯL / ＹL premises: Δ′, x, (cmp)ᵘ, A^x ⊢[T] C
    cast-pt : {F F′ A A′ C C′ : ℂForm X} {T T′ : ℂCE X}
            → F ≡ F′ → A ≡ A′ → T ≡ T′ → C ≡ C′
            → ⊢ (seq (ℂe (ℂu X F) A 𝕣₀) T C)
            → ⊢ (seq (ℂe (ℂu X F′) A′ 𝕣₀) T′ C′)
    cast-pt refl refl refl refl d = d

    -- ＵL / ＳL premises: Δ′, x, (cmp)ᵘ, B^x, A^I ⊢[T] C
    cast-int : {F F′ A A′ B B′ C C′ : ℂForm X} {I I′ : Interval (ℂtxt X)} {T T′ : ℂCE X}
             → F ≡ F′ → B ≡ B′ → A ≡ A′ → I ≡ I′ → T ≡ T′ → C ≡ C′
             → ⊢ (seq (ℂi (ℂe (ℂu X F) B 𝕣₀) A I) T C)
             → ⊢ (seq (ℂi (ℂe (ℂu X F′) B′ 𝕣₀) A′ I′) T′ C′)
    cast-int refl refl refl refl refl refl d = d

  plug-⊢ₐ : {Δ : ℂ₀} {T : ℂCE Δ} {C : ℂForm Δ}
         → ⊢ (seq Δ T C)
         → ⊢ (seq (plugₐ Δ) (⟪ Δ ⟫CE T) (⟪ Δ ⟫ C))
  plug-⊢ₐ (ax p)        = ax (plug-Ax p)
  plug-⊢ₐ ⊤I            = ⊤I
  plug-⊢ₐ (∧I h h₁)     = ∧I (plug-⊢ₐ h) (plug-⊢ₐ h₁)
  plug-⊢ₐ (∨Iₗ h)       = ∨Iₗ (plug-⊢ₐ h)
  plug-⊢ₐ (∨Iᵣ h)       = ∨Iᵣ (plug-⊢ₐ h)
  plug-⊢ₐ (→I h)        = →I (plug-⊢ₐ h)
  plug-⊢ₐ (ＯI h₁ h₂)   = ＯI (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ {Δ} {CEr r} (ＵI {.Δ} {.r} {r₁} {A} {B} h₁ h₂ h₃) =
    ＵI (plug-⊢ₐ h₁) (plug-⊢ₐ h₂) q
    where
    Δ′ : ℂ₀
    Δ′ = plugₐ Δ

    H : Form (ℂtxt Δ′ ، 𝕍ℝ) → Form (ℂtxt Δ′ ، 𝕍ℝ) → Form (ℂtxt Δ′ ، 𝕍ℝ) → Set₂
    H f₁ f₂ D = ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) f₁) f₂) 𝕣₀ D)

    q : ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) (↑ᵣ₀ (⟪ Δ ⟫ᵣ r) ⊑ 𝕣₀)) (𝕣₀ ⊏ ↑ᵣ₀ (⟪ Δ ⟫ᵣ r₁)))
                𝕣₀ (↑₀ (⟪ Δ ⟫ A)))
    q = subst₃ H (cong (λ z → z ⊑ 𝕣₀) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r))
                 (cong (λ z → 𝕣₀ ⊏ z) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r₁))
                 (⟪⟫-↑₀ Δ 𝕍ℝ A)
                 (plug-⊢ₐ h₃)
  plug-⊢ₐ {Δ} (⊥L pt p)      = ⊥L (pointCE-⟪⟫ Δ pt) (plug-Ax p)
  plug-⊢ₐ (∧L p h)           = ∧L (plug-Ax p) (plug-⊢ₐ h)
  plug-⊢ₐ (→L p h₁ h₂)       = →L (plug-Ax p) (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ {Δ} (∨L pt p h₁ h₂) = ∨L (pointCE-⟪⟫ Δ pt) (plug-Ax p) (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ {Δ} (cmpR pt h)    = cmpR (pointCE-⟪⟫ Δ pt) (plug-⊢ₐ h)
  plug-⊢ₐ {Δ} {CEr r} (ＦI {.Δ} {.r} {A} h) =
    ＦI (subst (λ X → ⊢ (rseq (plugₐ Δ) (⟪ Δ ⟫ᵣ r) X)) (⟪⟫-subℝ Δ r A) (plug-⊢ₐ h))
  plug-⊢ₐ (ＹI h₁ h₂)   = ＹI (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ {Δ} {CEr r} (ＳI {.Δ} {.r} {r₁} {A} {B} h₁ h₂ h₃) =
    ＳI (plug-⊢ₐ h₁) (plug-⊢ₐ h₂) q
    where
    Δ′ : ℂ₀
    Δ′ = plugₐ Δ

    H : Form (ℂtxt Δ′ ، 𝕍ℝ) → Form (ℂtxt Δ′ ، 𝕍ℝ) → Form (ℂtxt Δ′ ، 𝕍ℝ) → Set₂
    H f₁ f₂ D = ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) f₁) f₂) 𝕣₀ D)

    q : ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) (↑ᵣ₀ (⟪ Δ ⟫ᵣ r₁) ⊏ 𝕣₀)) (𝕣₀ ⊑ ↑ᵣ₀ (⟪ Δ ⟫ᵣ r)))
                𝕣₀ (↑₀ (⟪ Δ ⟫ A)))
    q = subst₃ H (cong (λ z → z ⊏ 𝕣₀) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r₁))
                 (cong (λ z → 𝕣₀ ⊑ z) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r))
                 (⟪⟫-↑₀ Δ 𝕍ℝ A)
                 (plug-⊢ₐ h₃)
  plug-⊢ₐ {Δ} {CEr r} (ＢI {.Δ} {.r} {A} h) =
    ＢI (subst₂ (λ f D → ⊢ (rseq (ℂu (ℂv (plugₐ Δ) 𝕍ℝ) f) 𝕣₀ D))
                (cong (λ z → 𝕣₀ ◁ z) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r))
                (⟪⟫-↑₀ Δ 𝕍ℝ A)
                (plug-⊢ₐ h))
  plug-⊢ₐ {Δ} {T} {C} (ＯL {.Δ} {r} {.T} {A} {.C} p h) =
    ＯL (plug-Ax p)
        (cast-pt (cong (λ z → z ◁ 𝕣₀) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r)) (⟪⟫-↑₀ Δ 𝕍ℝ A)
                 (sym (⟪⟫CE-↑₀ Δ 𝕍ℝ T)) (⟪⟫-↑₀ Δ 𝕍ℝ C) (plug-⊢ₐ h))
  plug-⊢ₐ {Δ} {T} {C} (ＹL {.Δ} {r} {.T} {A} {.C} p h) =
    ＹL (plug-Ax p)
        (cast-pt (cong (λ z → 𝕣₀ ◁ z) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r)) (⟪⟫-↑₀ Δ 𝕍ℝ A)
                 (sym (⟪⟫CE-↑₀ Δ 𝕍ℝ T)) (⟪⟫-↑₀ Δ 𝕍ℝ C) (plug-⊢ₐ h))
  plug-⊢ₐ {Δ} {T} {C} (ＵL {.Δ} {r} {.T} {A} {B} {.C} p h) =
    ＵL (plug-Ax p)
        (cast-int (cong (λ z → z ⊑ 𝕣₀) e) (⟪⟫-↑₀ Δ 𝕍ℝ B) (⟪⟫-↑₀ Δ 𝕍ℝ A)
                  (cong (λ z → ［ z , 𝕣₀ ）) e)
                  (sym (⟪⟫CE-↑₀ Δ 𝕍ℝ T)) (⟪⟫-↑₀ Δ 𝕍ℝ C) (plug-⊢ₐ h))
    where e = ⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r
  plug-⊢ₐ {Δ} {T} {C} (ＳL {.Δ} {r} {.T} {A} {B} {.C} p h) =
    ＳL (plug-Ax p)
        (cast-int (cong (λ z → 𝕣₀ ⊑ z) e) (⟪⟫-↑₀ Δ 𝕍ℝ B) (⟪⟫-↑₀ Δ 𝕍ℝ A)
                  (cong (λ z → （ 𝕣₀ , z ］) e)
                  (sym (⟪⟫CE-↑₀ Δ 𝕍ℝ T)) (⟪⟫-↑₀ Δ 𝕍ℝ C) (plug-⊢ₐ h))
    where e = ⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r
  plug-⊢ₐ (ＢL p h₁ h₂) = ＢL (plug-Ax p) (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ {Δ} {T} (∀I {.Δ} {.T} {u} {A} h) =
    ∀I (subst (λ X → ⊢ (seq (ℂv (plugₐ Δ) (𝕍𝕌 u)) X (⟪ ℂv Δ (𝕍𝕌 u) ⟫ A)))
              (sym (⟪⟫CE-↑₀ Δ (𝕍𝕌 u) T)) (plug-⊢ₐ h))
  plug-⊢ₐ {Δ} {T} {C} (∀L {.Δ} {R} {.T} {u} {A} {.C} p v h) =
    ∀L (plug-Ax p) (μ𝕌 σ ρ α δ (plug-w Δ) (↑⋆u (plug-s Δ) v))
       (subst (λ X → ⊢ (seq (ℂx (plugₐ Δ) X (⟪ Δ ⟫CE R)) (⟪ Δ ⟫CE T) (⟪ Δ ⟫ C)))
              (⟪⟫-subᵤ Δ u v A) (plug-⊢ₐ h))
  plug-⊢ₐ {Δ} {T} (∃R {.Δ} {.T} {u} {A} v h) =
    ∃R (μ𝕌 σ ρ α δ (plug-w Δ) (↑⋆u (plug-s Δ) v))
       (subst (λ X → ⊢ (seq (plugₐ Δ) (⟪ Δ ⟫CE T) X)) (⟪⟫-subᵤ Δ u v A) (plug-⊢ₐ h))
  plug-⊢ₐ {Δ} {T} {C} (∃L {.Δ} {R} {.T} {u} {A} {.C} p h) =
    ∃L (plug-Ax p)
       (subst₃ (λ a T′ C′ → ⊢ (seq (ℂe (ℂv (plugₐ Δ) (𝕍𝕌 u)) (⟪ ℂv Δ (𝕍𝕌 u) ⟫ A) a) T′ C′))
               (⟪⟫ᵣ-↑₀ Δ (𝕍𝕌 u) R) (sym (⟪⟫CE-↑₀ Δ (𝕍𝕌 u) T)) (⟪⟫-↑₀ Δ (𝕍𝕌 u) C)
               (plug-⊢ₐ h))
  plug-⊢ₐ {Δ} (InL {.Δ} {i} {r} p h₁ h₂) =
    InL (plug-Ax p) (subst (λ X → ⊢ (useq (plugₐ Δ) X)) (⟪⟫-interval Δ r i) (plug-⊢ₐ h₁)) (plug-⊢ₐ h₂)
  plug-⊢ₐ ⊑refl         = ⊑refl
  plug-⊢ₐ ⊑𝟎            = ⊑𝟎
  plug-⊢ₐ (⊑trans h₁ h₂)  = ⊑trans (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ (⊑⊏trans h₁ h₂) = ⊑⊏trans (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ (⊏⊑trans h₁ h₂) = ⊏⊑trans (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ (◁⊑ h)        = ◁⊑ (plug-⊢ₐ h)
  plug-⊢ₐ (◁⊏ h)        = ◁⊏ (plug-⊢ₐ h)
  plug-⊢ₐ (⊏⊑ h)        = ⊏⊑ (plug-⊢ₐ h)
  plug-⊢ₐ (＝⊑ h)        = ＝⊑ (plug-⊢ₐ h)
  plug-⊢ₐ (⊑⋆ h₁ h₂)    = ⊑⋆ (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ (⊑⋆ₗ h)       = ⊑⋆ₗ (plug-⊢ₐ h)
  plug-⊢ₐ (⊑⋆ᵣ h)       = ⊑⋆ᵣ (plug-⊢ₐ h)
  plug-⊢ₐ ＝refl         = ＝refl
  plug-⊢ₐ (＝sym h)      = ＝sym (plug-⊢ₐ h)
  plug-⊢ₐ (＝trans h₁ h₂) = ＝trans (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ (＝⋆ h₁ h₂)    = ＝⋆ (plug-⊢ₐ h₁) (plug-⊢ₐ h₂)
  plug-⊢ₐ ＝assoc        = ＝assoc
  plug-⊢ₐ ＝comm         = ＝comm
  plug-⊢ₐ ＝lid          = ＝lid
  plug-⊢ₐ {Δ} (∈I {l = []} ())
  plug-⊢ₐ {Δ} (∈I {l = _ ∷ _} p) = ∈I (∈-map⁺ (μAg σ ρ α δ (plug-w Δ)) (∈-map⁺ (↑⋆ᵢ (plug-s Δ)) p))
  plug-⊢ₐ {Δ} {CEr r} (□I {.Δ} {.r} {A} h) =
    □I (subst₂ (λ f D → ⊢ (rseq (ℂu (ℂv (plugₐ Δ) 𝕍ℝ) f) 𝕣₀ D))
               (cong (λ z → z ⊑ 𝕣₀) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r))
               (⟪⟫-↑₀ Δ 𝕍ℝ A)
               (plug-⊢ₐ h))
  plug-⊢ₐ (□L em p dc d) = □L em (plug-Ax p) (plug-⊢ₐ dc) (plug-⊢ₐ d)
  plug-⊢ₐ {Δ} {T} {C} (ＦL {.Δ} {r} {.T} {A} {.C} p h) =
    ＦL (plug-Ax p)
        (subst (λ X → ⊢ (seq (ℂe (plugₐ Δ) X (⟪ Δ ⟫ᵣ r)) (⟪ Δ ⟫CE T) (⟪ Δ ⟫ C)))
               (⟪⟫-subℝ Δ r A) (plug-⊢ₐ h))

-- Without placeholder agents/data (the original interface).
module _ (Γ : ℂ₀) (σ : FormSub⋆ (ℂtxt Γ)) (ρ : ResSub⋆ (ℂtxt Γ)) where

  plug : ℂ₀ → ℂ₀
  plug = plugₐ Γ σ ρ ●ₐ ●d

  plug-⊢ : {Δ : ℂ₀} {T : ℂCE Δ} {C : ℂForm Δ}
         → ⊢ (seq Δ T C)
         → ⊢ (seq (plug Δ) (⟪_⟫CE Γ σ ρ ●ₐ ●d Δ T) (⟪_⟫ Γ σ ρ ●ₐ ●d Δ C))
  plug-⊢ = plug-⊢ₐ Γ σ ρ ●ₐ ●d

\end{code}

-- ---------------------------------------------------------------------------
-- Rules whose premises all share the conclusion's context Γ
--
--   Γ ⊢[R₁] H₁   ...   Γ ⊢[Rₙ] Hₙ
--   ----------------------------
--           Γ ⊢[T] D
--
-- follow from the single sequent  Γ, H₁@R₁, ..., Hₙ@Rₙ ⊢[T] D.

\begin{code}

Prems : ℂ₀ → Set₁
Prems Γ = List (ℂCE Γ × ℂForm Γ)

addHyps : (Γ : ℂ₀) → Prems Γ → ℂ₀
addHyps Γ []            = Γ
addHyps Γ ((R , H) ∷ ps) = addHyps (ℂx Γ H R) ps

-- ℂx does not change the variable context; for a concrete list of premises
-- this equation and the casts below reduce to refl / the identity.
ℂtxt-addHyps : (Γ : ℂ₀) (ps : Prems Γ) → ℂtxt Γ ≡ ℂtxt (addHyps Γ ps)
ℂtxt-addHyps Γ []             = refl
ℂtxt-addHyps Γ ((R , H) ∷ ps) = ℂtxt-addHyps (ℂx Γ H R) ps

castCEₕ : (Γ : ℂ₀) (ps : Prems Γ) → ℂCE Γ → ℂCE (addHyps Γ ps)
castCEₕ Γ ps = subst CE (ℂtxt-addHyps Γ ps)

castFₕ : (Γ : ℂ₀) (ps : Prems Γ) → ℂForm Γ → ℂForm (addHyps Γ ps)
castFₕ Γ ps = subst Form (ℂtxt-addHyps Γ ps)

mkSeq : (Γ : ℂ₀) → ℂCE Γ × ℂForm Γ → Sequent
mkSeq Γ (R , H) = seq Γ R H

wk-prems : (M : Model₀) (Γ : ℂ₀) (H : ℂForm Γ) (R : ℂCE Γ) (ps : Prems Γ)
         → sat-sequents M (Data.List.map (mkSeq Γ) ps)
         → sat-sequents M (Data.List.map (mkSeq (ℂx Γ H R)) ps)
wk-prems M Γ H R []             h        = h
wk-prems M Γ H R ((R′ , H′) ∷ ps) (p , h) =
  hyp-wk M Γ H R R′ H′ p , wk-prems M Γ H R ps h

hyps→rule : (M : Model₀) (Γ : ℂ₀) (ps : Prems Γ) (T : ℂCE Γ) (D : ℂForm Γ)
          → sat-sequent M (seq (addHyps Γ ps) (castCEₕ Γ ps T) (castFₕ Γ ps D))
          → sat-rule M (rule (Data.List.map (mkSeq Γ) ps) (seq Γ T D))
hyps→rule M Γ []             T D h _        = h
hyps→rule M Γ ((R , H) ∷ ps) T D h (p , ps-sat) =
  hyp-cut M Γ H R T D
          (hyps→rule M (ℂx Γ H R) ps T D h (wk-prems M Γ H R ps ps-sat))
          p

\end{code}
