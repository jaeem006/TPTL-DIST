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

module Index(𝔻 : Set)
            (W : World)
            (EM : ExcludedMiddle (lsuc(0ℓ)))
       where

\end{code}

The syntax of TPTL-dist is defined here:

\begin{code}

open import Syntax(𝔻)(W)

\end{code}

The semantics of TPTL-dist is defined here:

\begin{code}

open import Semantics(𝔻)(W)

\end{code}

TPTL-dist's rules are defined here. These files include both primitive and derived rules.

\begin{code}

open import RulesProp(𝔻)(W)          -- propositional logic
open import RulesPred(𝔻)(W)          -- predicate logic
open import RulesTemp(𝔻)(W)          -- timed/temporal rules
open import RulesClassical(𝔻)(W)(EM) -- rules that require classical reasoning
open import RulesInd(𝔻)(W)           -- induction rule

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
