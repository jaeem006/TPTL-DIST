\begin{code}
{-# OPTIONS --with-K #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Axiom.ExcludedMiddle -- used to prove rule-classical-sat
open import Data.Product

\end{code}

The semantics of TPTL-dist is given w.r.t. to a type of Worlds, which is defined abstractly here.
The file also contains an instance using ℕ.

\begin{code}

open import World

\end{code}

We now import TPTL and its applications.

\begin{code}

module Index2025(𝔻 : Set)
                (W : World)
                (EM : ExcludedMiddle (lsuc(0ℓ)))
       where

Figure2 : Set₁
Figure2 = World

\end{code}

The syntax of TPTL-dist is defined here:

\begin{code}

open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)

Section3-1-Type : Set
Section3-1-Type = 𝕌

Section3-1-Agent : (Γ : Ctxt) → Set
Section3-1-Agent = Agent

Section3-1-Agents : (Γ : Ctxt) → Set
Section3-1-Agents = Agents

Section3-1-Data : (Γ : Ctxt) → Set
Section3-1-Data = Data

Section3-1-Time : (Γ : Ctxt) → Set
Section3-1-Time = Res

Section3-1-Comparison : Set
Section3-1-Comparison = Comparison

Section3-1-DistAtom : (Γ : Ctxt) → Set₁
Section3-1-DistAtom = Atom

Section3-1-SetAtom : (Γ : Ctxt) → Set₁
Section3-1-SetAtom = Form

Section3-1-Formula : (Γ : Ctxt) → Set₁
Section3-1-Formula = Form

Section3-1-Temporal-Operators :
     ({Γ : Ctxt} → Form Γ → Form Γ)
   × ({Γ : Ctxt} → Form Γ → Form Γ)
   × ({Γ : Ctxt} → Form Γ → Form Γ)
   × ({Γ : Ctxt} → Form Γ → Form Γ)
Section3-1-Temporal-Operators =
   ◇ , ◆ , □ , ■

Section3-1-Bounded-Temporal-Operators :
     ({Γ : Ctxt} → Res Γ → Form Γ → Form Γ)
   × ({Γ : Ctxt} → Res Γ → Form Γ → Form Γ)
   × ({Γ : Ctxt} → Form Γ → Form Γ)
Section3-1-Bounded-Temporal-Operators =
   ◇↓ , □↓ , ◆·
\end{code}

The semantics of TPTL-dist is defined here:

\begin{code}

open import Semantics(𝔻)(W)

open World.World W

Section3-3-Figure2 : Set₁
Section3-3-Figure2 = World

Section3-3-Figure3 :
    ({Γ : Ctxt} → Agent Γ → Sub Γ → agent)
  × ({Γ : Ctxt} → Agents Γ → Sub Γ → agents)
  × ({Γ : Ctxt} → Atom Γ → Sub Γ → atom)
  × ({Γ : Ctxt} → Data Γ → Sub Γ → 𝔻)
  × ({Γ : Ctxt} → Res Γ → Sub Γ → 𝕎)
  × (Comparison → 𝕎 → 𝕎 → Set)
Section3-3-Figure3 =
  Section3-3-Figure3-Agent ,
  Section3-3-Figure3-Agents ,
  Section3-3-Figure3-Atom ,
  Section3-3-Figure3-Data ,
  Section3-3-Figure3-Time ,
  Section3-3-Figure3-Comparison
  where
    Section3-3-Figure3-Agent : {Γ : Ctxt} → Agent Γ → Sub Γ → agent
    Section3-3-Figure3-Agent = ⟦_⟧ᵢ_

    Section3-3-Figure3-Agents : {Γ : Ctxt} → Agents Γ → Sub Γ → agents
    Section3-3-Figure3-Agents = ⟦_⟧ₛ_

    Section3-3-Figure3-Atom : {Γ : Ctxt} → Atom Γ → Sub Γ → atom
    Section3-3-Figure3-Atom = ⟦_⟧ₐ_

    Section3-3-Figure3-Data : {Γ : Ctxt} → Data Γ → Sub Γ → 𝔻
    Section3-3-Figure3-Data = ⟦_⟧d_

    Section3-3-Figure3-Time : {Γ : Ctxt} → Res Γ → Sub Γ → 𝕎
    Section3-3-Figure3-Time = ⟦_⟧ᵣ_

    Section3-3-Figure3-Comparison : Comparison → 𝕎 → 𝕎 → Set
    Section3-3-Figure3-Comparison = ⟦_⟧ᶜ

Section3-3-Figure4 : {Γ : Ctxt} → Model Γ → Form Γ → Set₁
Section3-3-Figure4 = _⊨_

\end{code}

The forwarding example is defined here:

\begin{code}

open import Rules(𝔻)(W)(EM)

Section3-2-Synchrony : {Γ : Ctxt} (Δ : Res Γ) → Form Γ
Section3-2-Synchrony = synchrony-assumption

Section3-2-Forward : {Γ : Ctxt} → Agent Γ → Agent Γ → Agent Γ → Form Γ
Section3-2-Forward = relay

Section-3-2-Conlcusion : (Γ : ℂ₀) (a b c : ℂAgent Γ) (Δ r : ℂRes Γ) (p : ℂData Γ) → Rule
Section-3-2-Conlcusion = example1

\end{code}

TPTL-dist's rules are defined here. These files include both primitive and derived rules.

\begin{code}

open import RulesProp(𝔻)(W)          -- propositional logic
open import RulesPred(𝔻)(W)          -- predicate logic
open import RulesTemp(𝔻)(W)          -- timed/temporal rules
open import RulesClassical(𝔻)(W)(EM) -- rules that require classical reasoning
open import RulesInd(𝔻)(W)           -- induction rule
open import RulesMisc(𝔻)(W)          -- other rule

Section3-4-Annotations : (Γ : Ctxt) → Set
Section3-4-Annotations = Interval

Section3-4-Hypothesis-Semantics : {Γ : Ctxt} (f : Form Γ) (a : CE Γ) (M : Model Γ) → Set₁
Section3-4-Hypothesis-Semantics = sat-ctxt-annot

Section3-4-Semantics :
    ({Γ : Ctxt} (c : ℂ Γ) (M : ℂModel c) → Set₁)
  × ((M : Model₀) (s : Sequent) → Set₁)
  × ((M : Model₀) (r : Rule) → Set₂)
Section3-4-Semantics  =
    sat-ctxt
  , sat-sequent
  , sat-rule

Section-3-5-Propositional-Logic-Rules :
    ((Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂCE Γ) (x : ℂCE Γ) (A B C : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂCE Γ) (A B : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂRes Γ) (R : ℂCE Γ) (A B C : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂRes Γ) (A B : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (T : ℂCE Γ) (R : ℂRes Γ) (A B C : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂCE Γ) (A : ℂForm Γ) → Rule)
Section-3-5-Propositional-Logic-Rules =
    rule¬I
  , rule∧I
  , rule∧E
  , rule∨Iₗ
  , rule∨Iᵣ
  , rule∨E
  , rule→I
  , rule→L
  , ruleLbl

Section3-5-Temporal-Rules :
    ((Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r r₁ : ℂRes Γ) (A B : ℂForm Γ) → Rule)
  × (((Γ : ℂ₀) (r r₁ : ℂRes Γ) (A B : ℂForm Γ) → Rule))
  × ((Γ : ℂ₀) (T r : ℂRes Γ) (A B C : ℂForm Γ) → Rule)
Section3-5-Temporal-Rules =
    ruleＯR
  , ruleＵR
  , {! ruleＯL!}
  , ruleＵL

Section3-5-Timed-Rules :
    ((Γ : ℂ₀) (r : ℂRes Γ) (T : ℂCE Γ) (A : Form (ℂtxt Γ ، 𝕍ℝ)) (C : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm (ℂv Γ 𝕍ℝ)) → Rule)
  × ((Γ : ℂ₀) (r₁ r₂ : ℂRes Γ) (R : ℂCE Γ) → Rule)
Section3-5-Timed-Rules =
    ruleＦL
  , ruleＦR
  , rule＝-⋆-sym

Section3-5-Inteval-Rules :
    ((Γ : ℂ₀) (r r′ : ℂRes Γ) (i : ℂInterval Γ) (A B : ℂForm Γ) → Rule)
  × {!!}
Section3-5-Inteval-Rules =
    ruleIn
  , {!!}


Section3-5-Induction-Rule : (Γ : ℂ₀) (A : Form (ℂtxt Γ ، 𝕍ℝ)) → Rule
Section3-5-Induction-Rule = rule-induction

Section3-5-Classical-Rule : {Γ : Ctxt} (A : Form Γ) → Form Γ
Section3-5-Classical-Rule = LEM

Section3-5-Derived-Rules :
    ((Γ : ℂ₀) (T : ℂRes Γ) (A : ℂForm Γ) → Rule)
  × ({!!})
  × ((Γ : ℂ₀) (r R : ℂRes Γ) (A : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (r R : ℂRes Γ) (A C : ℂForm Γ) → Rule)
  × ((Γ : ℂ₀) (t r T : ℂRes Γ) (A C : ℂForm Γ) → Rule)
Section3-5-Derived-Rules =
    rule□R
  , {!!}
  , ◆·R
  , rule◇↓R
  , ◆·L
  , rule◇↓L
\end{code}

The following file includes simple examples of formulas that can be derived using the above rules:

\begin{code}

--open import Rules(𝔻)(W)(EM)
open import RulesProp(𝔻)(W)

\end{code}

The following file contains the proof of a key property of the Pistis broadcast algorithm:

\begin{code}

open import Data.Nat
open import Data.Nat.Properties

open import Pistis(𝔻)(W)(EM)

Section4-1-Pushing : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
Section4-1-Pushing = pushing

Section4-1-Pulling : {!!}
Section4-1-Pulling = {!!}

Section4-1-Figure-6 :
    ({Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ)
  × ({Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ)
  × ({Γ : Ctxt} → Form Γ)
Section4-1-Figure-6 =
    boundedPushing
  , pushing
  , correctBefore

Section4-2-Lemma-2 : (Γ : ℂ₀) (r Δ : ℂRes Γ) (q : ℕ) (del : ℂData Γ) → Rule
Section4-2-Lemma-2 = pistis1
\end{code}

The following file contains a slightly more convenient definition of TPTL-dist's semantics
as well as a proof checker for TPTL-dist (WIP).

\begin{code}

open import ISemantics(W)

\end{code}
