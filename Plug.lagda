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
open import Data.List using (List ; _∷_ ; [])
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Misc
open import World

module Plug (W : World)
       where

open import Decidable(W)
open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)
open import Automation(W)

-- ---------------------------------------------------------------------------
-- Resource-variable substitutions (the analogue of FormSub⋆)

data ResSub⋆ (Γ : Ctxt) : Set where
  ●ᵣ     : ResSub⋆ Γ
  _↦ᵣ_⨾_ : ResVar → Res Γ → ResSub⋆ Γ → ResSub⋆ Γ

infixr 4 _↦ᵣ_⨾_

app-ResSub⋆ : {Γ : Ctxt} → ResVar → ResSub⋆ Γ → Res Γ
app-ResSub⋆ x ●ᵣ = rvar x
app-ResSub⋆ x (y ↦ᵣ r ⨾ ρ) with x ≟ y
... | yes _ = r
... | no  _ = app-ResSub⋆ x ρ

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

wkR : {Φ Δ : Ctxt} → Wk Φ Δ → Res Φ → Res Δ
wkR wk-id        X = X
wkR w@(wk-S _ _) X = ↑ᵣ (wk→⊆ w) X

wkF≡↑ : {Φ Δ : Ctxt} (w : Wk Φ Δ) (X : Form Φ) → wkF w X ≡ ↑ (wk→⊆ w) X
wkF≡↑ wk-id      X = sym (↑-refl (λ i → i) X (λ _ _ → refl))
wkF≡↑ (wk-S _ _) X = refl

wkR≡↑ : {Φ Δ : Ctxt} (w : Wk Φ Δ) (X : Res Φ) → wkR w X ≡ ↑ᵣ (wk→⊆ w) X
wkR≡↑ wk-id      X = sym (↑ᵣ-refl (λ i → i) X (λ _ _ → refl))
wkR≡↑ (wk-S _ _) X = refl

wk＋ : {Φ Γ : Ctxt} (Ψ : Ctxt) → Wk Φ Γ → Wk Φ (Γ ＋ Ψ)
wk＋ ⟨⟩      w = w
wk＋ (Ψ ، U) w = wk-S U (wk＋ Ψ w)

-- ---------------------------------------------------------------------------
-- Instantiation of formula and resource variables

module _ {Φ : Ctxt} (σ : FormSub⋆ Φ) (ρ : ResSub⋆ Φ) where

  μᵣ : {Δ : Ctxt} → Wk Φ Δ → Res Δ → Res Δ
  μᵣ w (𝐯 i)    = 𝐯 i
  μᵣ w 𝟎        = 𝟎
  μᵣ w (rvar x) = wkR w (app-ResSub⋆ x ρ)
  μᵣ w (a ⋆ b)  = μᵣ w a ⋆ μᵣ w b

  μI : {Δ : Ctxt} → Wk Φ Δ → Interval Δ → Interval Δ
  μI w ［ a , b ］ = ［ μᵣ w a , μᵣ w b ］
  μI w ［ a , b ） = ［ μᵣ w a , μᵣ w b ）
  μI w （ a , b ］ = （ μᵣ w a , μᵣ w b ］
  μI w （ a , b ） = （ μᵣ w a , μᵣ w b ）

  μCE : {Δ : Ctxt} → Wk Φ Δ → CE Δ → CE Δ
  μCE w (CEr r) = CEr (μᵣ w r)
  μCE w CEu     = CEu
  μCE w (CEi i) = CEi (μI w i)

  μ : {Δ : Ctxt} → Wk Φ Δ → Form Δ → Form Δ
  μ w (𝕒 x)         = 𝕒 x
  μ w (var x)       = wkF w (app-FormSub⋆ x σ)
  μ w ⊤·            = ⊤·
  μ w ⊥·            = ⊥·
  μ w (f ∧· g)      = μ w f ∧· μ w g
  μ w (f ∨· g)      = μ w f ∨· μ w g
  μ w (f →· g)      = μ w f →· μ w g
  μ w (∀· u f)      = ∀· u (μ (wk-S _ w) f)
  μ w (∃· u f)      = ∃· u (μ (wk-S _ w) f)
  μ w (𝔸 A)         = 𝔸 A
  μ w (f Ｕ g)      = μ w f Ｕ μ w g
  μ w (Ｏ f)        = Ｏ (μ w f)
  μ w (f Ｓ g)      = μ w f Ｓ μ w g
  μ w (Ｙ f)        = Ｙ (μ w f)
  μ w (Ｂ f)        = Ｂ (μ w f)
  μ w (Ｆ f)        = Ｆ (μ (wk-S 𝕍ℝ w) f)
  μ w (t₁ ⟨ c ⟩ t₂) = μᵣ w t₁ ⟨ c ⟩ μᵣ w t₂

  -- -------------------------------------------------------------------------
  -- μ commutes with renamings

  module _ {Δ Δ′ : Ctxt} where
    μᵣ-↑ : (e : Δ ⊆ Δ′) (w : Wk Φ Δ) (w′ : Wk Φ Δ′)
           (hw : (v : 𝕍) (i : ∈Ctxt v Φ) → wk→⊆ w′ i ≡ e (wk→⊆ w i))
           (r : Res Δ)
         → μᵣ w′ (↑ᵣ e r) ≡ ↑ᵣ e (μᵣ w r)
    μᵣ-↑ e w w′ hw (𝐯 i)    = refl
    μᵣ-↑ e w w′ hw 𝟎        = refl
    μᵣ-↑ e w w′ hw (rvar x) =
      trans (wkR≡↑ w′ X)
            (trans (↑ᵣ-trans (wk→⊆ w′) (wk→⊆ w) e X hw)
                   (cong (↑ᵣ e) (sym (wkR≡↑ w X))))
      where X = app-ResSub⋆ x ρ
    μᵣ-↑ e w w′ hw (a ⋆ b)  = cong₂ _⋆_ (μᵣ-↑ e w w′ hw a) (μᵣ-↑ e w w′ hw b)

    μCE-↑ : (e : Δ ⊆ Δ′) (w : Wk Φ Δ) (w′ : Wk Φ Δ′)
            (hw : (v : 𝕍) (i : ∈Ctxt v Φ) → wk→⊆ w′ i ≡ e (wk→⊆ w i))
            (x : CE Δ)
          → μCE w′ (↑CE e x) ≡ ↑CE e (μCE w x)
    μCE-↑ e w w′ hw (CEr r) = cong CEr (μᵣ-↑ e w w′ hw r)
    μCE-↑ e w w′ hw CEu     = refl
    μCE-↑ e w w′ hw (CEi ［ a , b ］) = cong CEi (cong₂ ［_,_］ (μᵣ-↑ e w w′ hw a) (μᵣ-↑ e w w′ hw b))
    μCE-↑ e w w′ hw (CEi ［ a , b ）) = cong CEi (cong₂ ［_,_） (μᵣ-↑ e w w′ hw a) (μᵣ-↑ e w w′ hw b))
    μCE-↑ e w w′ hw (CEi （ a , b ］) = cong CEi (cong₂ （_,_］ (μᵣ-↑ e w w′ hw a) (μᵣ-↑ e w w′ hw b))
    μCE-↑ e w w′ hw (CEi （ a , b ）) = cong CEi (cong₂ （_,_） (μᵣ-↑ e w w′ hw a) (μᵣ-↑ e w w′ hw b))

  hw-add : {Δ Δ′ : Ctxt} (u : 𝕍) (e : Δ ⊆ Δ′) (w : Wk Φ Δ) (w′ : Wk Φ Δ′)
           (hw : (v : 𝕍) (i : ∈Ctxt v Φ) → wk→⊆ w′ i ≡ e (wk→⊆ w i))
         → (v : 𝕍) (i : ∈Ctxt v Φ)
         → wk→⊆ (wk-S u w′) i ≡ ⊆، u e (wk→⊆ (wk-S u w) i)
  hw-add u e w w′ hw v i = cong (∈CtxtS u) (hw v i)

  μ-↑ : {Δ Δ′ : Ctxt} (e : Δ ⊆ Δ′) (w : Wk Φ Δ) (w′ : Wk Φ Δ′)
        (hw : (v : 𝕍) (i : ∈Ctxt v Φ) → wk→⊆ w′ i ≡ e (wk→⊆ w i))
        (f : Form Δ)
      → μ w′ (↑ e f) ≡ ↑ e (μ w f)
  μ-↑ e w w′ hw (𝕒 x)    = refl
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
  μ-↑ e w w′ hw (𝔸 A)    = refl
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
    μᵣ-sub Ψ w₀ a (rvar x) = sym (sub-wkR Ψ w₀ (μᵣ w₀ a) (app-ResSub⋆ x ρ))
    μᵣ-sub Ψ w₀ a (r ⋆ s)  = cong₂ _⋆_ (μᵣ-sub Ψ w₀ a r) (μᵣ-sub Ψ w₀ a s)

  -- substitutions that agree on the non-resource sorts agree on atoms
  module _ {Δ₁ Δ : Ctxt} (c c′ : CSub Δ₁ Δ)
           (E : {x : 𝕌} (i : ∈Ctxt (𝕍𝕌 x) Δ₁) → c i ≡ c′ i) where
    subAgent≡ : (a : Agent Δ₁) → sub-Agent a c ≡ sub-Agent a c′
    subAgent≡ (agentV i) = E i
    subAgent≡ (agentC x) = refl

    subAgentL≡ : (l : List (Agent Δ₁))
               → Data.List.map (λ x → sub-Agent x c) l ≡ Data.List.map (λ x → sub-Agent x c′) l
    subAgentL≡ []      = refl
    subAgentL≡ (a ∷ l) = cong₂ _∷_ (subAgent≡ a) (subAgentL≡ l)

    subAgents≡ : (a : Agents Δ₁) → sub-Agents a c ≡ sub-Agents a c′
    subAgents≡ (agentsV i) = E i
    subAgents≡ (agentsL l) = cong agentsL (subAgentL≡ l)

    subData≡ : (a : Data Δ₁) → sub-Data a c ≡ sub-Data a c′
    subData≡ (dataV i) = E i
    subData≡ (dataC x) = refl

    subAtomProp≡ : (a : AtomProp Δ₁) → sub-AtomProp a c ≡ sub-AtomProp a c′
    subAtomProp≡ (atomPropV i) = E i
    subAtomProp≡ (atomPropC x) = refl

    subAtom≡ : (a : Atom Δ₁) → sub-Atom a c ≡ sub-Atom a c′
    subAtom≡ (atProp x) = cong atProp (subAtomProp≡ x)
    subAtom≡ (atAction (ActSend p a A)) =
      cong atAction (cong₃ ActSend (subData≡ p) (subAgent≡ a) (subAgents≡ A))
    subAtom≡ (atEvent (EvtReceive p a b)) =
      cong atEvent (cong₃ EvtReceive (subData≡ p) (subAgent≡ a) (subAgent≡ b))
    subAtom≡ (atEvent (EvtInternal a d)) =
      cong atEvent (cong₂ EvtInternal (subAgent≡ a) (subData≡ d))
    subAtom≡ (atCorrect (FaultCorrect a b)) =
      cong atCorrect (cong₂ FaultCorrect (subAgent≡ a) (subAgent≡ b))

    subSetAtom≡ : (A : SetAtom Δ₁) → sub-SetAtom A c ≡ sub-SetAtom A c′
    subSetAtom≡ (a ∈ₐ A)     = cong₂ _∈ₐ_ (subAgent≡ a) (subAgents≡ A)
    subSetAtom≡ (∣ A ∣ₛ＝ n) = cong (λ z → ∣ z ∣ₛ＝ n) (subAgents≡ A)

  μ-sub : {Γ : Ctxt} (Ψ : Ctxt) (w₀ : Wk Φ Γ) (a : Res Γ) (f : Form ((Γ ، 𝕍ℝ) ＋ Ψ))
        → μ (wk＋ Ψ w₀) (sub f (CSub،＋ {Γ} {Ψ} {𝕍ℝ} a))
        ≡ sub (μ (wk＋ Ψ (wk-S 𝕍ℝ w₀)) f) (CSub،＋ {Γ} {Ψ} {𝕍ℝ} (μᵣ w₀ a))
  μ-sub Ψ w₀ a (𝕒 x)    = cong 𝕒 (subAtom≡ _ _ (CSub،＋-𝕌 Ψ a (μᵣ w₀ a)) x)
  μ-sub Ψ w₀ a (var x)  = sym (sub-wkF Ψ w₀ (μᵣ w₀ a) (app-FormSub⋆ x σ))
  μ-sub Ψ w₀ a ⊤·       = refl
  μ-sub Ψ w₀ a ⊥·       = refl
  μ-sub Ψ w₀ a (f ∧· g) = cong₂ _∧·_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (f ∨· g) = cong₂ _∨·_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (f →· g) = cong₂ _→·_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (∀· u f) = cong (∀· u) (μ-sub (Ψ ، 𝕍𝕌 u) w₀ a f)
  μ-sub Ψ w₀ a (∃· u f) = cong (∃· u) (μ-sub (Ψ ، 𝕍𝕌 u) w₀ a f)
  μ-sub Ψ w₀ a (𝔸 A)    = cong 𝔸 (subSetAtom≡ _ _ (CSub،＋-𝕌 Ψ a (μᵣ w₀ a)) A)
  μ-sub Ψ w₀ a (f Ｕ g) = cong₂ _Ｕ_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (Ｏ f)   = cong Ｏ (μ-sub Ψ w₀ a f)
  μ-sub Ψ w₀ a (f Ｓ g) = cong₂ _Ｓ_ (μ-sub Ψ w₀ a f) (μ-sub Ψ w₀ a g)
  μ-sub Ψ w₀ a (Ｙ f)   = cong Ｙ (μ-sub Ψ w₀ a f)
  μ-sub Ψ w₀ a (Ｂ f)   = cong Ｂ (μ-sub Ψ w₀ a f)
  μ-sub Ψ w₀ a (Ｆ f)   = cong Ｆ_ (μ-sub (Ψ ، 𝕍ℝ) w₀ a f)
  μ-sub Ψ w₀ a (r ⟨ c ⟩ s) =
    cong₂ (λ x y → x ⟨ c ⟩ y) (μᵣ-sub Ψ w₀ a r) (μᵣ-sub Ψ w₀ a s)

-- ---------------------------------------------------------------------------
-- Plugging a closed context into Γ

module _ (Γ : ℂ₀) (σ : FormSub⋆ (ℂtxt Γ)) (ρ : ResSub⋆ (ℂtxt Γ)) where

  plug   : ℂ₀ → ℂ₀
  plug-s : (Δ : ℂ₀) → ℂtxt Δ ⊆⋆ ℂtxt (plug Δ)
  plug-w : (Δ : ℂ₀) → Wk (ℂtxt Γ) (ℂtxt (plug Δ))

  ⟪_⟫ : (Δ : ℂ₀) → ℂForm Δ → ℂForm (plug Δ)
  ⟪ Δ ⟫ f = μ σ ρ (plug-w Δ) (↑⋆ (plug-s Δ) f)

  ⟪_⟫ᵣ : (Δ : ℂ₀) → ℂRes Δ → ℂRes (plug Δ)
  ⟪ Δ ⟫ᵣ r = μᵣ σ ρ (plug-w Δ) (↑⋆ᵣ (plug-s Δ) r)

  ⟪_⟫CE : (Δ : ℂ₀) → ℂCE Δ → ℂCE (plug Δ)
  ⟪ Δ ⟫CE x = μCE σ ρ (plug-w Δ) (↑⋆CE (plug-s Δ) x)

  plug ℂ⟨⟩        = Γ
  plug (ℂx c f a) = ℂx (plug c) (⟪ c ⟫ f) (⟪ c ⟫CE a)
  plug (ℂv c v)   = ℂv (plug c) v

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
    trans (cong (μᵣ σ ρ (wk-S v (plug-w Δ))) (⋆↑ᵣ₀-add v (plug-s Δ) r))
          (μᵣ-↑ σ ρ ⊆₀ (plug-w Δ) (wk-S v (plug-w Δ)) (λ _ _ → refl) (↑⋆ᵣ (plug-s Δ) r))

  ⟪⟫-↑₀ : (Δ : ℂ₀) (v : 𝕍) (f : ℂForm Δ)
        → ⟪ ℂv Δ v ⟫ (↑₀ f) ≡ ↑₀ (⟪ Δ ⟫ f)
  ⟪⟫-↑₀ Δ v f =
    trans (cong (μ σ ρ (wk-S v (plug-w Δ))) (⋆↑₀-add v (plug-s Δ) f))
          (μ-↑ σ ρ ⊆₀ (plug-w Δ) (wk-S v (plug-w Δ)) (λ _ _ → refl) (↑⋆ (plug-s Δ) f))

  ⟪⟫CE-↑₀ : (Δ : ℂ₀) (v : 𝕍) (x : ℂCE Δ)
          → ↑CE₀ (⟪ Δ ⟫CE x) ≡ ⟪ ℂv Δ v ⟫CE (↑CE₀ x)
  ⟪⟫CE-↑₀ Δ v x =
    trans (sym (μCE-↑ σ ρ ⊆₀ (plug-w Δ) (wk-S v (plug-w Δ)) (λ _ _ → refl) (↑⋆CE (plug-s Δ) x)))
          (cong (μCE σ ρ (wk-S v (plug-w Δ))) (↑CE₀-↑⋆CE v (plug-s Δ) x))

  pointCE-⟪⟫ : (Δ : ℂ₀) {x : ℂCE Δ} → pointCE x → pointCE (⟪ Δ ⟫CE x)
  pointCE-⟪⟫ Δ (ptR r) = ptR _
  pointCE-⟪⟫ Δ ptU     = ptU

  plug-Ax : {Δ : ℂ₀} {r : ℂCE Δ} {A : ℂForm Δ}
          → Ax Δ r A → Ax (plug Δ) (⟪ Δ ⟫CE r) (⟪ Δ ⟫ A)
  plug-Ax (found c f a)  = found (plug c) (⟪ c ⟫ f) (⟪ c ⟫CE a)
  plug-Ax (skip f a h)   = skip _ _ (plug-Ax h)
  plug-Ax (down {c} {v} {x} {C} h) =
    subst₂ (Ax (ℂv (plug c) v)) (⟪⟫CE-↑₀ c v x) (sym (⟪⟫-↑₀ c v C)) (down (plug-Ax h))

  plug-⊢ : {Δ : ℂ₀} {T : ℂCE Δ} {C : ℂForm Δ}
         → ⊢ (seq Δ T C)
         → ⊢ (seq (plug Δ) (⟪ Δ ⟫CE T) (⟪ Δ ⟫ C))
  plug-⊢ (ax p)        = ax (plug-Ax p)
  plug-⊢ ⊤I            = ⊤I
  plug-⊢ (∧I h h₁)     = ∧I (plug-⊢ h) (plug-⊢ h₁)
  plug-⊢ (∨Iₗ h)       = ∨Iₗ (plug-⊢ h)
  plug-⊢ (∨Iᵣ h)       = ∨Iᵣ (plug-⊢ h)
  plug-⊢ (→I h)        = →I (plug-⊢ h)
  plug-⊢ (ＯI h₁ h₂)   = ＯI (plug-⊢ h₁) (plug-⊢ h₂)
  plug-⊢ {Δ} {CEr r} (ＵI {.Δ} {.r} {r₁} {A} {B} h₁ h₂ h₃) =
    ＵI (plug-⊢ h₁) (plug-⊢ h₂) q
    where
    Δ′ : ℂ₀
    Δ′ = plug Δ

    H : Form (ℂtxt Δ′ ، 𝕍ℝ) → Form (ℂtxt Δ′ ، 𝕍ℝ) → Form (ℂtxt Δ′ ، 𝕍ℝ) → Set₂
    H f₁ f₂ D = ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) f₁) f₂) 𝕣₀ D)

    q : ⊢ (rseq (ℂu (ℂu (ℂv Δ′ 𝕍ℝ) (↑ᵣ₀ (⟪ Δ ⟫ᵣ r) ⊑ 𝕣₀)) (𝕣₀ ⊏ ↑ᵣ₀ (⟪ Δ ⟫ᵣ r₁)))
                𝕣₀ (↑₀ (⟪ Δ ⟫ A)))
    q = subst₃ H (cong (λ z → z ⊑ 𝕣₀) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r))
                 (cong (λ z → 𝕣₀ ⊏ z) (⟪⟫ᵣ-↑₀ Δ 𝕍ℝ r₁))
                 (⟪⟫-↑₀ Δ 𝕍ℝ A)
                 (plug-⊢ h₃)
  plug-⊢ {Δ} (⊥L pt p)      = ⊥L (pointCE-⟪⟫ Δ pt) (plug-Ax p)
  plug-⊢ (∧L p h)           = ∧L (plug-Ax p) (plug-⊢ h)
  plug-⊢ (→L p h₁ h₂)       = →L (plug-Ax p) (plug-⊢ h₁) (plug-⊢ h₂)
  plug-⊢ {Δ} (∨L pt p h₁ h₂) = ∨L (pointCE-⟪⟫ Δ pt) (plug-Ax p) (plug-⊢ h₁) (plug-⊢ h₂)
  plug-⊢ {Δ} (cmpR pt h)    = cmpR (pointCE-⟪⟫ Δ pt) (plug-⊢ h)
  plug-⊢ {Δ} {CEr r} (ＦI {.Δ} {.r} {A} h) =
    ＦI (subst (λ X → ⊢ (rseq (plug Δ) (⟪ Δ ⟫ᵣ r) X)) eq (plug-⊢ h))
    where
    s : ℂtxt Δ ⊆⋆ ℂtxt (plug Δ)
    s = plug-s Δ

    Hs : {v : 𝕍} (i : ∈Ctxt v (ℂtxt Δ ، 𝕍ℝ))
       → CSub،ₗ {_} {𝕍ℝ} (↑⋆ᵣ s r) {v} (app-⊆⋆ (⊆⋆-add 𝕍ℝ s) v i)
       ≡ ↑⋆v s {v} (CSub،ₗ {_} {𝕍ℝ} r {v} i)
    Hs {.𝕍ℝ} (∈Ctxt0 _)      = refl
    Hs {v}   (∈CtxtS .𝕍ℝ i) = sym (↑⋆v-CSub-var s {v} i)

    eq : ⟪ Δ ⟫ (subℝ A r) ≡ subℝ (⟪ ℂv Δ 𝕍ℝ ⟫ A) (⟪ Δ ⟫ᵣ r)
    eq = trans (cong (μ σ ρ (plug-w Δ))
                     (↑⋆-sub (⊆⋆-add 𝕍ℝ s) s (CSub،ₗ r) (CSub،ₗ (↑⋆ᵣ s r)) Hs A))
               (μ-sub σ ρ ⟨⟩ (plug-w Δ) (↑⋆ᵣ s r) (↑⋆ (⊆⋆-add 𝕍ℝ s) A))

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
