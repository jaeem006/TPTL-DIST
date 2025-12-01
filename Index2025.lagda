\begin{code}
{-# OPTIONS --with-K #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Axiom.ExcludedMiddle -- used to prove rule-classical-sat

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

\end{code}

The semantics of TPTL-dist is defined here:

\begin{code}

open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open World.World W

Section3-3-Figure2 : Set₁
Section3-3-Figure2 = World

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

Section3-3-Figure3 : {Γ : Ctxt} → Model Γ → Form Γ → Set₁
Section3-3-Figure3 = _⊨_

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

Section3-4-Annotations : (Γ : Ctxt) → Set
Section3-4-Annotations = Interval


Section3-4-Hypothesis-Semantics : {Γ : Ctxt} (f : Form Γ) (a : CE Γ) (M : Model Γ) → Set₁
Section3-4-Hypothesis-Semantics = sat-ctxt-annot

\end{code}

The following file includes simple examples of formulas that can be derived using the above rules:

\begin{code}

open import Rules(𝔻)(W)(EM)

\end{code}

The following file contains the proof of a key property of the Pistis broadcast algorithm:

\begin{code}

open import Pistis(𝔻)(W)(EM)

\end{code}

The following file contains a slightly more convenient definition of TPTL-dist's semantics
as well as a proof checker for TPTL-dist (WIP).

\begin{code}

open import ISemantics(W)

\end{code}
