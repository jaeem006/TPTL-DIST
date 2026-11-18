\begin{code}
{-# OPTIONS --with-K #-}
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

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)

open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle -- used to prove rule-classical-sat

open import Misc
open import World

module Pistis(𝔻 : Set)
             (W : World)
             (EM : ExcludedMiddle (lsuc(0ℓ)))
       where

open import WorldUtil(W)
open import Syntax(𝔻)(W)
open import Subst(𝔻)(W)
open import Semantics(𝔻)(W)

open import RulesMisc(𝔻)(W)
open import RulesProp(𝔻)(W)
open import RulesPred(𝔻)(W)
open import RulesTemp(𝔻)(W)
open import RulesClassical(𝔻)(W)(EM)
open import Rules(𝔻)(W)(EM)
open import RulesInd(𝔻)(W)

open World.World W

pushing-aux₆ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent ، 𝕍Agents ، 𝕍Agent)
pushing-aux₆ {Γ} q del Δ =
  (𝔸 (𝕒0 ∈ₐ 𝔸1)) -- for all nodes in 𝔸 that is correct
  →· ◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]

pushing-aux₅ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent ، 𝕍Agents ، 𝕍Agent)
pushing-aux₅ {Γ} q del Δ =
  Correct 𝕒0
  →· pushing-aux₆ q del Δ

pushing-aux₄ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent ، 𝕍Agents)
pushing-aux₄ {Γ} q del Δ =
  ∀ₐ (pushing-aux₅ q del Δ)

pushing-aux₃ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent)
pushing-aux₃ {Γ} q del Δ =
  ∃ₛ ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) -- there are 2f+1 (q) nodes in 𝔸0
      ∧· pushing-aux₄ q del Δ)

pushing₃ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
pushing₃ {Γ} q del Δ =
  ∃ₛ ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) -- there are 2f+1 (q) nodes in 𝔸0
      ∧· ∀ₐ (Correct 𝕒0
             →· (𝔸 (𝕒0 ∈ₐ 𝔸1)) -- for all nodes in 𝔸 that is correct
             →· ◇↓◆ (↑ᵣ₁ Δ) ●[ 𝕒0 , ↑d₁ del ]))

pushing₃-aux₃ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ)
              → pushing-aux₃ q del Δ ≡ ↑₀ (pushing₃ q del Δ)
pushing₃-aux₃ {Γ} q del Δ =
  cong (λ x → ∃ₛ ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) ∧· ∀ₐ (Correct 𝕒0 →· (𝔸 (𝕒0 ∈ₐ 𝔸1)) →· x)))
       (trans (cong₂ ◇↓◆ (↑ᵣ₂≡↑ᵣ₀،،↑ᵣ₁ Δ) ((cong ●[ 𝕒0 ,_]) (↑d₂≡↑d₀،،↑d₁ del)))
              (sym (↑◇↓◆ ⊆₀،، _ _)))

-- NOTE:  Why is it at timw 𝕣?
pushing-aux₂ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent)
pushing-aux₂ {Γ} q del Δ =
  ●[ 𝕒0 , ↑d₀ del ]     -- 𝕒 delivers at time 𝕣
  →· pushing-aux₃ q del Δ

pushing-aux₁ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent)
pushing-aux₁ {Γ} q del Δ =
  Correct 𝕒0  -- 𝕒 is correct
  →· pushing-aux₂ q del Δ

pushing-aux₀ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
pushing-aux₀ {Γ} q del Δ = ∀ₐ (pushing-aux₁ {Γ} q del Δ)

-- if a 'del' event happened at a correct node
-- then there must be a collection of 2f+1 nodes such that the 'del' event also happened
--   at all correct nodes in that collection at most by time Δ
pushing : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
pushing {Γ} q del Δ = □ (pushing-aux₀ q del Δ)

boundedPushing-aux₆ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent ، 𝕍Agents ، 𝕍Agent)
boundedPushing-aux₆ {Γ} q del Δ =
  (𝔸 (𝕒0 ∈ₐ 𝔸1))
  →· ◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]

boundedPushing-aux₅ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent ، 𝕍Agents ، 𝕍Agent)
boundedPushing-aux₅ {Γ} q del Δ =
  Correct 𝕒0
  →· boundedPushing-aux₆ q del Δ

boundedPushing-aux₄ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent ، 𝕍Agents)
boundedPushing-aux₄ {Γ} q del Δ = ◇↓◆ (↑ᵣ₁ Δ) (∀ₐ (boundedPushing-aux₅ q del Δ))

boundedPushing-aux₃ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent)
boundedPushing-aux₃ {Γ} q del Δ =
  ∃ₛ ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) -- there are 2f+1 (q) nodes in 𝔸0
     ∧· boundedPushing-aux₄ q del Δ)

boundedPushing₅ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agents)
boundedPushing₅ {Γ} q del Δ =
  ∀ₐ (Correct 𝕒0
      →· (𝔸 (𝕒0 ∈ₐ 𝔸1))
      →· ◇↓ (↑ᵣ₁ Δ) ●[ 𝕒0 , ↑d₁ del ])

boundedPushing₄ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agents)
boundedPushing₄ {Γ} q del Δ =
  (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) -- there are 2f+1 (q) nodes in 𝔸0
  ∧· ◇↓◆ (↑ᵣ₀ Δ) (boundedPushing₅ q del Δ)

boundedPushing₃ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
boundedPushing₃ {Γ} q del Δ =
  ∃ₛ (boundedPushing₄ q del Δ)

boundedPushing₃-aux₃ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ)
                     → boundedPushing-aux₃ q del Δ ≡ ↑₀ (boundedPushing₃ q del Δ)
boundedPushing₃-aux₃ {Γ} q del Δ =
  cong (λ x → ∃ₛ ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) ∧· x))
       (trans (cong₂ ◇↓◆ (sym (↑ᵣ₀،-↑ᵣ₀ Δ))
                     (cong (λ x → ∀ₐ (Correct 𝕒0 →· (𝔸 (𝕒0 ∈ₐ 𝔸1)) →· x))
                           (trans (cong₂ ◇↓ (sym (↑ᵣ₀،،-↑ᵣ₁ Δ)) (cong ●[ 𝕒0 ,_] (sym (↑d₀،،-↑d₁ del)))) (sym (↑◇↓ ⊆₀،، _ _)))))
              (sym (↑◇↓◆ ⊆₀، _ _)))

boundedPushing-aux₂ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent)
boundedPushing-aux₂ {Γ} q del Δ =
  ●[ 𝕒0 , ↑d₀ del ]     -- 𝕒 delivers at time 𝕣
  →· boundedPushing-aux₃ q del Δ

boundedPushing-aux₁ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent)
boundedPushing-aux₁ {Γ} q del Δ =
  Correct 𝕒0             -- 𝕒 is correct
  →· boundedPushing-aux₂ q del Δ

boundedPushing-aux₀ : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
boundedPushing-aux₀ {Γ} q del Δ =
  ∀ₐ (boundedPushing-aux₁ q del Δ)

-- if a 'del' event happened at a correct node at time t
-- then there must be a collection of 2f+1 nodes such that the 'del' event also happened
--   at all correct nodes in that collection during some Δ time window starting before t + Δ
boundedPushing : {Γ : Ctxt} (q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
boundedPushing {Γ} q del Δ =
  □ (boundedPushing-aux₀ q del Δ)

-- If a correct node sends a 'p' message,
-- then the 'del' event must have occured in the past (before ◆)
send-if-event : {Γ : Ctxt} (del : Data Γ) → Form Γ
send-if-event {Γ} del =
  □ (∀ₐ (Correct 𝕒0 →· ∀ₛ (send[ 𝕒1 ⇒ ↑d₁ del ⇒ 𝔸0 ] →· ◆ ●[ 𝕒1 , ↑d₁ del ])))

-- If a node 'a' receives a message from a correct node 'b'
-- then 'b' must have sent the message in the past
send-if-received : {Γ : Ctxt} (p : Data Γ) → Form Γ
send-if-received {Γ} p =
  □ (∀ₐ {-- receiver --} (∀ₐ {-- sender --}
        (recv[ 𝕒1 ⇐ ↑d₁ p ⇐ 𝕒0 ]
          →· ◆ send[ 𝕒0 ⇒ ↑d₁ p ⇒ [ 𝕒1 ]ₐ ] )))

event-if-received-aux₀ : {Γ : Ctxt} (Q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form (Γ ، 𝕍Agent)
event-if-received-aux₀ {Γ} Q del Δ =
  ∃ₛ ((𝔸 (∣ 𝔸0 ∣ₛ＝ Q))
      ∧· ∀ₐ ((𝔸 (𝕒0 ∈ₐ 𝔸1)) →· ◇↓ (↑ᵣ₂ Δ) (recv[ 𝕒2 ⇐ ↑d₂ del ⇐ 𝕒0 ])))

event-if-received-aux₁ : {Γ : Ctxt} (Q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
event-if-received-aux₁ {Γ} Q del Δ =
  ∀ₐ (Correct 𝕒0
      →· ●[ 𝕒0 , ↑d₀ del ]
      →· event-if-received-aux₀ Q del Δ)

-- If a 'del' event occurs at some correct node 'a' at time 't'
-- then 'a' must have received 'Q' 'del' messages by 't+Δ'
event-if-received : {Γ : Ctxt} (Q : ℕ) (del : Data Γ) (Δ : Res Γ) → Form Γ
event-if-received {Γ} Q del Δ =
  □ (event-if-received-aux₁ Q del Δ)

-- Derivable from the "classical" rule:
--
--    Γ, ∃· u (¬· A) ⊢[T] B
-- ---------------------------
--    Γ, ¬· (∀· u A) ⊢[T] B

rule¬∀L : (Γ : ℂ₀) (T R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ) → Rule
rule¬∀L Γ T R u A B =
  rule (rseq (ℂe Γ (∃· u (¬· A)) R) T B ∷ [])
       (rseq (ℂe Γ (¬· (∀· u A)) R) T B)

rule¬∀L-sat : (M : Model₀) (Γ : ℂ₀) (T R : ℂRes Γ) (u : 𝕌) (A : ℂForm (ℂv Γ (𝕍𝕌 u))) (B : ℂForm Γ)
            → sat-rule M (rule¬∀L Γ T R u A B)
rule¬∀L-sat M Γ T R u A B (satB , _) =
  by-cases-sat M (ℂe Γ (¬· ∀· u A) R) T T B B
    (ruleLbl-sat M (ℂe Γ (¬· ∀· u A) R) (CEr T) B (lift tt) ,
     rule-cut-sat M (ℂe (ℂe Γ (¬· ∀· u A) R) (¬· B) T) (CEr T) (CEr R) B (∃· u (¬· A))
      (by-cases-sat M (ℂe (ℂe Γ (¬· ∀· u A) R) (¬· B) T) R R (∃· u (¬· A)) (∃· u (¬· A))
        (ruleLbl-sat M (ℂe (ℂe Γ (¬· ∀· u A) R) (¬· B) T) (CEr R) (∃· u (¬· A)) (lift tt)  ,
         prove⊥-sat M (ℂe (ℂe (ℂe Γ (¬· ∀· u A) R) (¬· B) T) (¬· ∃· u (¬· A)) R) (CEr R) (∃· u (¬· A))
           (rule-thin1-sat M (ℂe Γ (¬· ∀· u A) R) (¬· B) (¬· ∃· u (¬· A)) (CEr T) (CEr R) (CEr R) ⊥·
             (rule-swap-sat M Γ (¬· ∀· u A) (¬· ∃· u (¬· A)) (CEr R) (CEr R) (CEr R) ⊥·
               (rule¬E-last-sat M (ℂe Γ (¬· ∃· u (¬· A)) R) R (∀· u A) R ⊥·
                 (rule∀I-sat M (ℂe Γ (¬· ∃· u (¬· A)) R) (CEr R) u A
                   (by-cases-sat M (ℂv (ℂe Γ (¬· ∃· u (¬· A)) R) (𝕍𝕌 u)) (↑ᵣ₀ R) (↑ᵣ₀ R) A A
                     (ruleLbl-sat M (ℂv (ℂe Γ (¬· ∃· u (¬· A)) R) (𝕍𝕌 u)) (CEr (↑ᵣ₀ R)) A (lift tt) ,
                      prove⊥-sat M (ℂe (ℂv (ℂe Γ (¬· ∃· u (¬· A)) R) (𝕍𝕌 u)) (¬· A) (↑ᵣ₀ R)) (CEr (↑ᵣ₀ R)) A
                        (rule¬E-sat M Γ (ℂe (ℂv ℂ⟨⟩ (𝕍𝕌 u)) (¬· A) (↑ᵣ₀ R)) R (∃· u (¬· A)) (CEr (↑ᵣ₀ R)) ⊥·
                          (𝕀 , lift tt) , lift tt) ,
                      lift tt) , lift tt) ,
                  lift tt) , lift tt) ,
              lift tt) , lift tt)
          , lift tt) ,
       rule-thin1-sat M (ℂe Γ (¬· ∀· u A) R) (¬· B) (∃· u (¬· A)) (CEr T) (CEr R) (CEr T) B
         (rule-thin1-sat M Γ (¬· ∀· u A) (∃· u (¬· A)) (CEr R) (CEr R) (CEr T) B (satB , lift tt) , lift tt) ,
       lift tt) ,
     -- 1. Switch to proving ⊥·
     -- 2. Eliminate the ¬· ∀· i.e., move the ∀· to the conclusion
     -- 3. Do a ∀I/R -- now we have a 'u' in the context and are proving A
     -- 4. Go "by-cases" on A: (a) if A is true then we conclude
     -- 5. (b) if A is false, bring back B to the conclusion     -- and so on
     lift tt)
  where
  𝕀 : sat-sequent M (rseq (ℂe (ℂv Γ (𝕍𝕌 u)) (¬· A) (↑ᵣ₀ R)) (↑ᵣ₀ R) (∃· u (¬· (↑₀، A))))
  𝕀 = rule∃R-sat M (ℂe (ℂv Γ (𝕍𝕌 u)) (¬· A) (↑ᵣ₀ R)) (CEr (↑ᵣ₀ R)) u (¬· ↑₀، A) 𝕦0
        (subst (λ x → sat-sequent M (rseq (ℂe (ℂv Γ (𝕍𝕌 u)) (¬· A) (↑ᵣ₀ R)) (↑ᵣ₀ R) (¬· x)))
               (sym (sub-var0₀ (ℂtxt Γ) (𝕍𝕌 u) A))
               (ruleLbl-sat M (ℂv Γ (𝕍𝕌 u)) (CEr (↑ᵣ₀ R)) (¬· A) (lift tt)) , lift tt)

--        Γ, _ , _ ⊢[𝟎] pushing-aux₄ q del Δ
-- ---------------------------------------------------
--    Γ, _ , _ ⊢[𝟎] ∀ₐ (boundedPushing-aux₅ q del Δ)

→boundedPushing0 : (Γ : ℂ₀) (q : ℕ) (del : ℂData Γ) (Δ : ℂRes Γ) → Rule
→boundedPushing0 Γ q del Δ =
  rule [] (rseq (ℂe (ℂv (ℂv Γ 𝕍Agent) 𝕍Agents) (pushing-aux₄ q del Δ) 𝟎) 𝟎 (∀ₐ (boundedPushing-aux₅ q del Δ)))

→boundedPushing0-sat : (M : Model₀) (Γ : ℂ₀) (q : ℕ) (del : ℂData Γ) (Δ : ℂRes Γ)
                     → sat-rule M (→boundedPushing0 Γ q del Δ)
→boundedPushing0-sat M Γ q del Δ _ =
  rule∀I-sat M Γ₁ (CEr 𝟎) 𝕌Agent (boundedPushing-aux₅ q del Δ)
   (rule→I-sat M Γ₂ 𝟎 (Correct 𝕒0) (boundedPushing-aux₆ q del Δ)
     (rule→I-sat M Γ₃ 𝟎 (𝔸 (𝕒0 ∈ₐ 𝔸1)) (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
       (ℍ₁ , lift tt) , lift tt) , lift tt)
  where
  Γ₁ : ℂ₀
  Γ₁ = ℂe (ℂv (ℂv Γ 𝕍Agent) 𝕍Agents) (pushing-aux₄ q del Δ) 𝟎

  Γ₂ : ℂ₀
  Γ₂ = ℂv Γ₁ 𝕍Agent

  Γ₃ : ℂ₀
  Γ₃ = ℂe Γ₂ (Correct 𝕒0) 𝟎

  Γ₄ : ℂ₀
  Γ₄ = ℂe Γ₃ (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝟎

  Γ₅ : ℂ₀
  Γ₅ = ℂe (ℂe (ℂv (ℂv (ℂv Γ 𝕍Agent) 𝕍Agents) 𝕍Agent) (Correct 𝕒0) 𝟎) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝟎

  Γ₆ : ℂ₀
  Γ₆ = ℂe Γ₅ (↑₀ (pushing-aux₄ q del Δ)) 𝟎

  Γ₇ : ℂ₀
  Γ₇ = ℂe Γ₅ (sub (↑₀، (pushing-aux₅ q del Δ)) (CSub،ₗ 𝕒0)) 𝟎

  Γ₈ : ℂ₀
  Γ₈ = ℂe Γ₅ (sub (↑₀، (pushing-aux₆ q del Δ)) (CSub،ₗ 𝕒0)) 𝟎

  Γ₉ : ℂ₀
  Γ₉ = ℂe Γ₅ (sub (↑₀، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) (CSub،ₗ 𝕒0)) 𝟎

  Γ₁₀ : ℂ₀
  Γ₁₀ = ℂe Γ₅ (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]) 𝟎

  ℍ₆ : sat-sequent M (rseq Γ₁₀ 𝟎 (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
  ℍ₆ = ◇↓◆𝟎→◇↓-sat M Γ₅ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ] (lift tt)

  ℍ₅ : sat-sequent M (rseq Γ₉ 𝟎 (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
  ℍ₅ = move-to-concl-ext-sat M {Γ₅} 𝟎
        (sub (↑₀، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) (CSub،ₗ 𝕒0))
        (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
        (subst (λ x → sat-sequent M (rseq Γ₅ 𝟎 (x →· (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))))
               (sym (sub-var0₀ _ 𝕍Agent (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])))
               (rule→I-sat M Γ₅ 𝟎
                 (◇↓◆ (↑ᵣ₂ Δ) (𝕒 (atEvent (EvtInternal 𝕒0 (↑d₂ del)))))
                 (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]) (ℍ₆ , lift tt)) , lift tt)

  ℍ₄ : sat-sequent M (rseq Γ₈ 𝟎 (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
  ℍ₄ = rule→L-sat M Γ₅ (CEr 𝟎) 𝟎 (𝔸 (𝕒0 ∈ₐ 𝔸1))
        (sub (↑₀، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) (CSub،ₗ 𝕒0))
        (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
        (ruleLbl-sat M (ℂe (ℂv (ℂv (ℂv Γ 𝕍Agent) 𝕍Agents) 𝕍Agent) (Correct 𝕒0) 𝟎) (CEr 𝟎) (𝔸 (𝕒0 ∈ₐ 𝔸1)) (lift tt) ,
         ℍ₅ ,
         lift tt)

  ℍ₃ : sat-sequent M (rseq Γ₇ 𝟎 (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
  ℍ₃ = rule→L-sat M Γ₅ (CEr 𝟎) 𝟎 (Correct 𝕒0) (sub (↑₀، (pushing-aux₆ q del Δ)) (CSub،ₗ 𝕒0)) (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
         (rule-thin-sat M
           (ℂe (ℂv (ℂv (ℂv Γ 𝕍Agent) 𝕍Agents) 𝕍Agent) (Correct 𝕒0) 𝟎) (𝔸 (𝕒0 ∈ₐ 𝔸1)) (CEr 𝟎) (CEr 𝟎) (Correct 𝕒0)
           (ruleLbl-sat M (ℂv (ℂv (ℂv Γ 𝕍Agent) 𝕍Agents) 𝕍Agent) (CEr 𝟎) (Correct 𝕒0)
             (lift tt) , lift tt) ,
          ℍ₄ ,
          lift tt)

  ℍ₂ : sat-sequent M (rseq Γ₆ (⋆Res refl 𝟎) (⋆Form refl (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])))
  ℍ₂ = subst₂ (λ x y → sat-sequent M (rseq Γ₆ x y))
              (sym (⋆Res-refl 𝟎))
              (sym (⋆Form-refl (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])))
              (rule∀L′-sat M Γ₅ 𝟎 𝟎 𝕌Agent (↑₀، (pushing-aux₅ q del Δ))
                (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]) 𝕒0 (ℍ₃ , lift tt))

  ℍ₁ : sat-sequent M (rseq Γ₄ 𝟎 (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
  ℍ₁ = rule-move-sat M (ℂv (ℂv Γ 𝕍Agent) 𝕍Agents)
        (ℂe (ℂe (ℂv ℂ⟨⟩ 𝕍Agent) (Correct 𝕒0) 𝟎) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝟎)
        (pushing-aux₄ q del Δ) (CEr 𝟎) (CEr 𝟎) (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
        (ℍ₂ , lift tt)

-- if a node is correct now then it was correct in the past too
correctBefore : {Γ : Ctxt} → Form Γ
correctBefore {Γ} = ∀ₐ (□ (Correct 𝕒0 →· ■ (Correct 𝕒0)))

-- PISTIS

pistis1 : (Γ : ℂ₀) (r Δ : ℂRes Γ) (q : ℕ) (del : ℂData Γ) → Rule
pistis1 Γ r Δ q del =
  rule (rseq Γ r (pushing q del Δ) ∷ rseq Γ r correctBefore ∷ [])
       (rseq Γ r (boundedPushing q del Δ))

pistis1-true : (L : Induction {lsuc(0ℓ)} W)
               (M : Model₀)
               {Γ : ℂ₀} (Δ : ℂRes Γ) (q : ℕ) (del : ℂData Γ)
             → sat-rule M (pistis1 Γ 𝟎 Δ q del)
pistis1-true L M {Γ} Δ q del (hyp1 , hyp2 , _) =
  rule□R-sat M Γ r (boundedPushing-aux₀ q del Δ) (ℍ , lift tt)
  where
  r : ℂRes Γ
  r = 𝟎

  Γ₁ : ℂ₀
  Γ₁ = ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)

  Γ₂ : ℂ₀
  Γ₂ = ℂi (ℂv Γ 𝕍ℝ) (Ｆ (↑₀، (↑ᵣ₀ r ⊑ 𝕣₀ →· ↑₀ (boundedPushing-aux₀ q del Δ)))) ［ 𝟎 , 𝕣₀ ）

  Γ₃ : ℂ₀
  Γ₃ = ℂe Γ₂ (↑ᵣ₀ r ⊑ 𝕣₀) 𝕣₀

  Γ₄ : ℂ₀
  Γ₄ = ℂv Γ₃ 𝕍Agent

  Γ₅ : ℂ₀
  Γ₅ = ℂe Γ₄ (Correct 𝕒0) 𝕣₁

  Γ₆ : ℂ₀
  Γ₆ = ℂe Γ₅ (●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ]) 𝕣₁

  𝔾Γ₇ : ℂ₀
  𝔾Γ₇ = ℂe Γ₆ (↑₀، (pushing-aux₃ q del Δ)) 𝕣₁

  𝔾Γ₈ : ℂ₀
  𝔾Γ₈ = ℂe (ℂv Γ₆ 𝕍Agents) ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) ∧· ↑₀،، (pushing-aux₄ q del Δ)) 𝕣₂

  𝔾Γ₉ : ℂ₀
  𝔾Γ₉ = ℂe (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂) (↑₀،، (pushing-aux₄ q del Δ)) 𝕣₂

  𝔾Γ₁₀ : ℂ₀
  𝔾Γ₁₀ = ℂe 𝔾Γ₉ (↑₀،، (boundedPushing-aux₄ q del Δ)) 𝕣₂

  𝔾Γ₁₁ : ℂ₀
  𝔾Γ₁₁ = ℂe 𝔾Γ₉ (¬· (↑₀،، (◇↓◆ (↑ᵣ₁ Δ) (∀ₐ (boundedPushing-aux₅ q del Δ))))) 𝕣₂

  𝔾Γ₁₂ : ℂ₀
  𝔾Γ₁₂ = ℂe 𝔾Γ₉ (□↓■ (↑ᵣ ⊆₀،، (↑ᵣ₁ Δ)) (¬· (∀ₐ (↑₀،،، (boundedPushing-aux₅ q del Δ))))) 𝕣₂

  𝔾Γ₁₃ : ℂ₀
  𝔾Γ₁₃ = ℂe 𝔾Γ₉ (■ (¬· (∀ₐ (↑₀،،، (boundedPushing-aux₅ q del Δ))))) 𝕣₂

  𝔾Γ₁₄ : ℂ₀
  𝔾Γ₁₄ = ℂe (ℂe (ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝕣₃) (¬· ↑₀،،، (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃

  ℍΓ₁₅ : ℂ₀
  ℍΓ₁₅ = ℂe (ℂe 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃) (◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃

  𝕘Γ   : ℂ₀
  𝕘Γ   = ℂe (ℂe (ℂv (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂) 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝕣₃

  𝔾Γ₁₅ : ℂ₀
  𝔾Γ₁₅ = ℂe 𝕘Γ (↑₀ (↑₀،، (pushing-aux₄ q del Δ))) 𝕣₃

  𝔾Γ₁₆ : ℂ₀
  𝔾Γ₁₆ = ℂe 𝕘Γ (sub (↑₀، (↑₀،،، (pushing-aux₅ q del Δ))) (CSub،ₗ 𝕒0)) 𝕣₃

  ℍΓ₁₉ : ℂ₀
  ℍΓ₁₉ = ℂu (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] 𝕣₀) (𝕣₀ ⊏ 𝕣₂)

  𝔽Γ₈ : ℂ₀
  𝔽Γ₈ = ℂe Γ₆ (↑₁ (pushing q del Δ)) (↑ᵣ₁ r)

  𝔽Γ₉ : ℂ₀
  𝔽Γ₉ = ℂe Γ₆ (↑₁ (pushing-aux₀ q del Δ)) 𝕣₁

  𝔽Γ₁₀ : ℂ₀
  𝔽Γ₁₀ = ℂe Γ₆ (Correct 𝕒0 →· sub (↑ (⊆، 𝕍Agent ⊆₁) (pushing-aux₂ q del Δ)) (CSub،ₗ 𝕒0)) 𝕣₁

  𝔽Γ₁₁ : ℂ₀
  𝔽Γ₁₁ = ℂe Γ₆ (●[ 𝕒0 , sub-Data (↑d (⊆، 𝕍Agent ⊆₁) (↑d₀ del)) (CSub،ₗ 𝕒0) ] →· sub (↑ (⊆، 𝕍Agent ⊆₁) (pushing-aux₃ q del Δ)) (CSub،ₗ 𝕒0)) 𝕣₁

  𝔽Γ₁₂ : ℂ₀
  𝔽Γ₁₂ = ℂe Γ₆ (sub (↑ (⊆، 𝕍Agent ⊆₁) (pushing-aux₃ q del Δ)) (CSub،ₗ 𝕒0)) 𝕣₁

  𝔼𝟙𝟙 : sat-sequent M (rseq 𝔾Γ₁₀ 𝕣₂ (𝔸 (∣ 𝔸0 ∣ₛ＝ q)))
  𝔼𝟙𝟙 = rule-thin-sat M 𝔾Γ₉ (↑₀،، (boundedPushing-aux₄ q del Δ)) (CEr 𝕣₂) (CEr 𝕣₂) (𝔸 (∣ 𝔸0 ∣ₛ＝ q))
                     (rule-thin-sat M (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂)
                       (↑₀،، (pushing-aux₄ q del Δ)) (CEr 𝕣₂) (CEr 𝕣₂)
                       (𝔸 (∣ 𝔸0 ∣ₛ＝ q))
                       ((ruleLbl-sat M (ℂv Γ₆ 𝕍Agents) (CEr 𝕣₂) (𝔸 (∣ 𝔸0 ∣ₛ＝ q))
                         (lift tt))
                       , (lift tt))
                     , (lift tt))

  𝔼𝟙𝟚 : sat-sequent M (rseq 𝔾Γ₁₀ 𝕣₂ (sub (↑₀، (↑₀،، (boundedPushing-aux₄ q del Δ))) (CSub،ₗ 𝔸0)))
  𝔼𝟙𝟚 = subst (λ x → sat-sequent M (rseq 𝔾Γ₁₀ 𝕣₂ x))
              (sym (sub-var0₀ _ 𝕍Agents (↑₀،، (boundedPushing-aux₄ q del Δ))))
              (ruleLbl-sat M 𝔾Γ₉ (CEr 𝕣₂) (↑₀،، (boundedPushing-aux₄ q del Δ)) (lift tt))

  𝔼𝟙𝟘 : sat-sequent M (rseq 𝔾Γ₁₀ 𝕣₂ ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) ∧· sub (↑₀، (↑₀،، (boundedPushing-aux₄ q del Δ))) (CSub،ₗ 𝔸0)))
  𝔼𝟙𝟘 = rule∧I-sat M 𝔾Γ₁₀ (CEr 𝕣₂) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) (sub (↑₀، (↑₀،، (boundedPushing-aux₄ q del Δ))) (CSub،ₗ 𝔸0))
                   (𝔼𝟙𝟙 , 𝔼𝟙𝟚 , (lift tt))

  𝔼𝟡 : sat-sequent M (rseq 𝔾Γ₁₀ 𝕣₂ (∃ₛ ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) ∧· ↑₀، (↑₀،، (boundedPushing-aux₄ q del Δ)))))
  𝔼𝟡 = rule∃R-sat
         M 𝔾Γ₁₀ (CEr 𝕣₂) 𝕌Agents ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) ∧· ↑₀، (↑₀،، (boundedPushing-aux₄ q del Δ)))
         𝔸0
         (𝔼𝟙𝟘 , lift tt)

  -- easy case
  𝔾𝟡 : sat-sequent M (rseq 𝔾Γ₁₀ 𝕣₂ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
  𝔾𝟡 = 𝔼𝟡
  -- use rule∃R-sat on the set of variable in 𝕍Agents in 𝔾Γ₉, and then conclude thanks to the
  -- assumptions in both 𝔾Γ₉ and 𝔾Γ₁₀ (using rule∧I-sat among others)

  𝔾𝟙𝟞 : sat-sequent M (rseq 𝔾Γ₁₆ 𝕣₃ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])))
  𝔾𝟙𝟞 = move-to-concl-ext-sat M {𝕘Γ} 𝕣₃
         (sub (↑₀، (↑₀،،، (pushing-aux₅ q del Δ))) (CSub،ₗ 𝕒0))
         (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
         (subst (λ x → sat-sequent M (rseq 𝕘Γ 𝕣₃ (x →· ↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))))
                (sym (sub-var0₀ _ 𝕍Agent (↑₀،،، (pushing-aux₅ q del Δ))))
                (rule→I-sat M 𝕘Γ 𝕣₃ (↑₀،،، (pushing-aux₅ q del Δ))
                  (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
                  (rule→L-sat M 𝕘Γ (CEr 𝕣₃) 𝕣₃ (Correct 𝕒0) (↑₀،،، (pushing-aux₆ q del Δ))
                    (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
                    (rule-thin-sat M
                      (ℂe (ℂv (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂) 𝕍Agent) (Correct 𝕒0) 𝕣₃)
                      (𝔸 (𝕒0 ∈ₐ 𝔸1)) (CEr 𝕣₃) (CEr 𝕣₃) (Correct 𝕒0)
                      (ruleLbl-sat M (ℂv (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂) 𝕍Agent) (CEr 𝕣₃) (Correct 𝕒0) (lift tt) , lift tt) ,
                     rule→L-sat M 𝕘Γ (CEr 𝕣₃) 𝕣₃ (𝔸 (𝕒0 ∈ₐ 𝔸1))
                      (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
                      (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
                      (ruleLbl-sat M
                        (ℂe (ℂv (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂) 𝕍Agent) (Correct 𝕒0) 𝕣₃)
                        (CEr 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) (lift tt) ,
                       ruleLbl-sat M 𝕘Γ (CEr 𝕣₃) (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) (lift tt) ,
                       lift tt) ,
                     lift tt) , lift tt)) , lift tt)

  𝔾𝟙𝟝 : sat-sequent M (rseq 𝔾Γ₁₅ 𝕣₃ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])))
  𝔾𝟙𝟝 = rule∀L′-sat M
         𝕘Γ 𝕣₃ 𝕣₃ 𝕌Agent (↑₀، (↑₀،،، (pushing-aux₅ q del Δ)))
         (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕒0
         (𝔾𝟙𝟞 , lift tt)

  𝔾𝟙𝟜 : sat-sequent M (rseq (ℂe (ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝕣₃) 𝕣₃ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])))
  𝔾𝟙𝟜 = rule-move-sat M (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂)
         (ℂe (ℂe (ℂv ℂ⟨⟩ 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝕣₃)
         (↑₀،، (pushing-aux₄ q del Δ)) (CEr 𝕣₂) (CEr 𝕣₃)
         (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
         (𝔾𝟙𝟝 , lift tt)

  ℍ𝟚𝟛 : sat-sequent M (rseq (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (↑₂، (boundedPushing₄ q del Δ)) 𝕣₁) 𝕣₃ (↑₂، (boundedPushing₄ q del Δ)))
  ℍ𝟚𝟛 = rule∧E-sat M (ℂv ℍΓ₁₉ 𝕍Agents) (CEr 𝕣₃) (CEr 𝕣₁) (𝔸 (∣ 𝔸0 ∣ₛ＝ q))
         (↑₂، (◇↓◆ (↑ᵣ₀ Δ) (boundedPushing₅ q del Δ)))
         (↑₂، (boundedPushing₄ q del Δ))
         (rule∧I-sat M
           (ℂe (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₁) (↑₂، (◇↓◆ (↑ᵣ₀ Δ) (boundedPushing₅ q del Δ))) 𝕣₁)
           (CEr 𝕣₃) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) (↑₂، (◇↓◆ (↑ᵣ₀ Δ) (boundedPushing₅ q del Δ)))
           (rule-thin-sat M (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₁)
             (↑₂، (◇↓◆ (↑ᵣ₀ Δ) (boundedPushing₅ q del Δ))) (CEr 𝕣₁) (CEr 𝕣₃)
             (𝔸 (∣ 𝔸0 ∣ₛ＝ q))
             (rule-size-change-resources-sat M
               (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₁) 𝕣₃ 𝕣₁ 𝔸0 q
               (ruleLbl-sat M (ℂv ℍΓ₁₉ 𝕍Agents) (CEr 𝕣₁) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) (lift tt) , lift tt) , lift tt) ,
            subst (λ x → sat-sequent M (rseq (ℂe (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₁) x 𝕣₁) 𝕣₃ x))
                  (sym (↑◇↓◆ ⊆₂، (↑ᵣ₀ Δ) (boundedPushing₅ q del Δ)))
                  (◇↓◆⊑-sat M
                    (ℂe (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₁) (◇↓◆ (↑ᵣ₂، (↑ᵣ₀ Δ)) (↑₂، (boundedPushing₅ q del Δ))) 𝕣₁)
                    𝕣₃ 𝕣₁ 𝕣₃ (↑ᵣ₂، (↑ᵣ₀ Δ)) (↑₂، (boundedPushing₅ q del Δ))
                    (ruleLbl-sat M (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₁) (CEr 𝕣₁)
                      (◇↓◆ (↑ᵣ₂، (↑ᵣ₀ Δ)) (↑₂، (boundedPushing₅ q del Δ)))
                      (lift tt) ,
                     rule-thin-sat M (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₁)
                      (◇↓◆ (↑ᵣ₂، (↑ᵣ₀ Δ)) (↑₂، (boundedPushing₅ q del Δ))) (CEr 𝕣₁) (CEr 𝕣₃)
                      (𝕣₁ ⊑ 𝕣₃)
                      (rule-thin-sat M (ℂv ℍΓ₁₉ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) (CEr 𝕣₁) (CEr 𝕣₃) (𝕣₁ ⊑ 𝕣₃)
                        (rule-thin-v-sat M ℍΓ₁₉ 𝕍Agents 𝕣₂ (𝕣₀ ⊑ 𝕣₂)
                          (⊏→⊑-sat M ℍΓ₁₉ 𝕣₀ 𝕣₂ 𝕣₂
                            (rule-id-comp-u-sat M
                              (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] 𝕣₀)
                              (CEr 𝕣₂) 𝕣₀ 𝕣₂ LT (lift tt) ,
                             lift tt) , lift tt) , lift tt) , lift tt) ,
                     lift tt)) ,
            lift tt) , lift tt)

  ℍ𝟚𝟚 : sat-sequent M (rseq (ℂe ℍΓ₁₉ (sub (↑₂، (boundedPushing-aux₃ q del Δ)) (CSub،ₗ 𝕒1)) 𝕣₀)
                           𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ))))
  ℍ𝟚𝟚 = subst (λ x → sat-sequent M (rseq (ℂe ℍΓ₁₉ (sub (↑₂، x) (CSub،ₗ 𝕒1)) 𝕣₀) 𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ)))))
               (sym (boundedPushing₃-aux₃ q del Δ))
               (subst₂ (λ x y → sat-sequent M (rseq (ℂe ℍΓ₁₉ (sub x (CSub،ₗ 𝕒1)) 𝕣₀) 𝕣₂ y))
                       (sym (↑₂،-↑₀ (boundedPushing₃ q del Δ)))
                       (sym (↑₀-↑₁≡↑₂ _ _ _ _ (boundedPushing₃ q del Δ)))
                       (subst (λ x → sat-sequent M (rseq (ℂe ℍΓ₁₉ x 𝕣₀) 𝕣₂ (↑₂ (boundedPushing₃ q del Δ))))
                              (sym (sub-↑₃ _ _ _ _ _ 𝕒1 (boundedPushing₃ q del Δ)))
                              (rule∃L-sat M ℍΓ₁₉ (CEr 𝕣₂) 𝕣₀ 𝕌Agents (↑₂، (boundedPushing₄ q del Δ))
                                (↑₂ (boundedPushing₃ q del Δ))
                                (rule∃R-sat M
                                  (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (↑₂، (boundedPushing₄ q del Δ)) 𝕣₁) (CEr 𝕣₃)
                                  𝕌Agents (↑₀، (↑₂، (boundedPushing₄ q del Δ))) 𝔸0
                                  (subst (λ x → sat-sequent M (rseq (ℂe (ℂv ℍΓ₁₉ 𝕍Agents) (↑₂، (boundedPushing₄ q del Δ)) 𝕣₁) 𝕣₃ x))
                                         (sym (sub-var0₀ _ 𝕍Agents (↑₂، (boundedPushing₄ q del Δ))))
                                         ℍ𝟚𝟛 , lift tt) , lift tt))))
  -- We need to use the fact that if boundedPushing₃ at r and r ⊑ r′ then boundedPushing₃ is true at r′ (◇↓◆⊑-sat)

  𝕀𝟚𝟚 : sat-sequent M (rseq ℍΓ₁₉ 𝕣₀ (Correct 𝕒1))
  𝕀𝟚𝟚 = rule-cut-sat M ℍΓ₁₉ (CEr 𝕣₀) (CEr 𝟎) (Correct 𝕒1) correctBefore
          (rule-thin-sat M -- thin
            (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] 𝕣₀)
            (𝕣₀ ⊏ 𝕣₂) CEu (CEr 𝟎) correctBefore
            (rule-thin-sat M
              (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] (CEr 𝕣₀) (CEr 𝟎) correctBefore
              (rule-thin-v-sat M (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ 𝟎 correctBefore
                (rule-thin-sat M (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) (CEr 𝕣₁) (CEr 𝟎) correctBefore
                  (rule-thin-v-sat M (ℂv Γ 𝕍ℝ) 𝕍Agent 𝟎 correctBefore
                    (rule-thin-v-sat M Γ 𝕍ℝ 𝟎 correctBefore
                      (hyp2 , lift tt) , lift tt) , lift tt) , lift tt) , lift tt) , lift tt) ,
           rule∀L′-sat M ℍΓ₁₉ 𝕣₀ 𝟎 𝕌Agent (□ (Correct 𝕒0 →· ■ (Correct 𝕒0))) (Correct 𝕒1) 𝕒1
             (rule□L′-sat M ℍΓ₁₉ 𝟎 𝕣₂ 𝕣₀ (Correct 𝕒1 →· ■ (Correct 𝕒1)) (Correct 𝕒1)
               (rule→L-sat M ℍΓ₁₉ (CEr 𝕣₀) 𝕣₂ (Correct 𝕒1) (■ (Correct 𝕒1)) (Correct 𝕒1)
                 (rule-thin-sat M
                   (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] 𝕣₀)
                   (𝕣₀ ⊏ 𝕣₂) CEu (CEr 𝕣₂) (Correct 𝕒1)
                   (rule-thin-sat M (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ)
                     ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] (CEr 𝕣₀) (CEr 𝕣₂) (Correct 𝕒1)
                     (rule-thin-v-sat M (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ 𝕣₁
                       (Correct 𝕒0)
                       (ruleLbl-sat M (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (CEr 𝕣₁) (Correct 𝕒0) (lift tt) , lift tt) , lift tt) , lift tt) ,
                  rule■L′-sat M ℍΓ₁₉ 𝕣₂ 𝕣₀ 𝕣₀ (Correct 𝕒1) (Correct 𝕒1)
                    (ruleLbl-sat M ℍΓ₁₉ (CEr 𝕣₀) (Correct 𝕒1) (lift tt) ,
                     ⊏→⊑-sat M ℍΓ₁₉ 𝕣₀ 𝕣₂ 𝕣₂
                       (rule-id-comp-u-sat M
                          (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] 𝕣₀)
                          (CEr 𝕣₂) 𝕣₀ 𝕣₂ LT (lift tt) ,
                         lift tt)  ,
                     lift tt) ,
                  lift tt) ,
                rule𝟎min-sat M ℍΓ₁₉ 𝕣₂ 𝕣₂ (lift tt) ,
                lift tt) , lift tt) ,
           lift tt)

  ℍ𝟚𝟙 : sat-sequent M (rseq (ℂe ℍΓ₁₉ (Correct 𝕒1 →· sub (↑₂، (boundedPushing-aux₂ q del Δ)) (CSub،ₗ 𝕒1)) 𝕣₀)
                           𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ))))
  ℍ𝟚𝟙 = rule→L-sat M ℍΓ₁₉ (CEr 𝕣₂) 𝕣₀ (Correct 𝕒1)
         (sub (↑₂، (boundedPushing-aux₂ q del Δ)) (CSub،ₗ 𝕒1))
         (↑₀ (↑₁ (boundedPushing₃ q del Δ)))
         (𝕀𝟚𝟚  , -- since the node was correct at 𝕣₂ and 𝕣₀ ⊏ 𝕣₂ then it was correct at 𝕣₀ (use the correctBefore hyp -- hyp2)
          rule→L-sat M ℍΓ₁₉ (CEr 𝕣₂) 𝕣₀ (●[ 𝕒1 , sub-Data (↑d₂، (↑d₀ del)) (CSub،ₗ 𝕒1) ])
           (sub (↑₂، (boundedPushing-aux₃ q del Δ)) (CSub،ₗ 𝕒1))
           (↑₀ (↑₁ (boundedPushing₃ q del Δ)))
           (subst (λ x → sat-sequent M (rseq ℍΓ₁₉ 𝕣₀ ●[ 𝕒1 , sub-Data x (CSub،ₗ 𝕒1) ]))
                  (sym (↑d₂،-↑d₀ del))
                  (subst (λ x → sat-sequent M (rseq ℍΓ₁₉ 𝕣₀ ●[ 𝕒1 , x ]))
                         (sym (sub-Data-↑d₃ _ _ _ _ _ 𝕒1 del))
                         (rule-thin-sat M  -- start thinning
                           (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] 𝕣₀)
                           (𝕣₀ ⊏ 𝕣₂) CEu (CEr 𝕣₀) ●[ 𝕒1 , ↑d₂ del ]
                           (subst (λ x → sat-sequent M (rseq (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] 𝕣₀) 𝕣₀ ●[ 𝕒1 , x ]))
                                  (sym (↑d₂≡↑d₀↑d₁ del))
                                  (ruleLbl-sat M (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ)
                                    (CEr 𝕣₀) ●[ 𝕒1 , ↑d₀ (↑d₁ del) ] (lift tt)) , lift tt))) ,
            ℍ𝟚𝟚 ,
            lift tt) ,
         lift tt)

  ℍ𝟚𝟘 : sat-sequent M (rseq (ℂe ℍΓ₁₉ (sub-Res (↑ᵣ₁، {_} {_} {_} {𝕍ℝ} (↑ᵣ₀، (↑ᵣ₀ r))) (CSub،ₗ 𝕣₀) ⊑ 𝕣₀ →· subℝ (↑₁، (↑₀، (↑₀ (boundedPushing-aux₀ q del Δ)))) 𝕣₀) 𝕣₀)
                           𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ))))
  ℍ𝟚𝟘 = rule→L-sat M ℍΓ₁₉ (CEr 𝕣₂) 𝕣₀
         (sub-Res (↑ᵣ₁، {_} {_} {_} {𝕍ℝ} (↑ᵣ₀، (↑ᵣ₀ r))) (CSub،ₗ 𝕣₀) ⊑ 𝕣₀)
         (subℝ (↑₁، (↑₀، (↑₀ (boundedPushing-aux₀ q del Δ)))) 𝕣₀)
         (↑₀ (↑₁ (boundedPushing₃ q del Δ)))
         (rule𝟎min-sat M ℍΓ₁₉ 𝕣₀ 𝕣₀ (lift tt) ,
          subst (λ x → sat-sequent M (rseq (ℂe ℍΓ₁₉ (subℝ (↑₁، x) 𝕣₀) 𝕣₀) 𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ)))))
                (sym (↑₀،-↑₀ (boundedPushing-aux₀ q del Δ)))
                (subst (λ x → sat-sequent M (rseq (ℂe ℍΓ₁₉ (subℝ x 𝕣₀) 𝕣₀) 𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ)))))
                       (sym (↑₁،-↑₁ (boundedPushing-aux₀ q del Δ)))
                       (subst (λ x → sat-sequent M (rseq (ℂe ℍΓ₁₉ x 𝕣₀) 𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ)))))
                              (sym (sub-↑₃ _ _ _ _ _ 𝕣₀ (boundedPushing-aux₀ q del Δ)))
                              (rule∀L′-sat M ℍΓ₁₉ 𝕣₂ 𝕣₀ 𝕌Agent
                                (↑₂، (boundedPushing-aux₁ q del Δ))
                                (↑₀ (↑₁ (boundedPushing₃ q del Δ))) 𝕒1
                                (ℍ𝟚𝟙 , lift tt)))) ,
          lift tt)

  ℍ𝟙𝟡 : sat-sequent M (rseq (ℂi ℍΓ₁₉ (Ｆ (↑₁، (↑₀، (↑ᵣ₀ r ⊑ 𝕣₀ →· ↑₀ (boundedPushing-aux₀ q del Δ))))) ［ 𝟎 , 𝕣₂ ）)
                           𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ))))
  ℍ𝟙𝟡 = ruleIn-sat M ℍΓ₁₉ 𝕣₀ 𝕣₂ ［ 𝟎 , 𝕣₂ ）
         (Ｆ ↑₁، (↑₀، (↑ᵣ₀ r ⊑ 𝕣₀ →· ↑₀ (boundedPushing-aux₀ q del Δ))))
         (↑₀ (↑₁ (boundedPushing₃ q del Δ)))
         (rule∧I-sat M ℍΓ₁₉ (CEr 𝕣₂) (𝟎 ⊑ 𝕣₀) (𝕣₀ ⊏ 𝕣₂)
           (rule𝟎min-sat M ℍΓ₁₉ 𝕣₂ 𝕣₀ (lift tt) ,
            rule-id-comp-u-sat M
             (ℂe (ℂv (ℂe (ℂv (ℂv Γ 𝕍ℝ) 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) (↑₀ ●[ 𝕒0 , ↑d₁ del ]) 𝕣₀)
             (CEr 𝕣₂) 𝕣₀ 𝕣₂ LT (lift tt) ,
            lift tt) ,
          ruleＦL-sat M ℍΓ₁₉ 𝕣₀ (CEr 𝕣₂)
           (↑₁، (↑₀، (↑ᵣ₀ r ⊑ 𝕣₀ →· ↑₀ (boundedPushing-aux₀ q del Δ))))
           (↑₀ (↑₁ (boundedPushing₃ q del Δ)))
           (ℍ𝟚𝟘 , lift tt) ,
          lift tt)

  ℍ𝟙𝟠 : sat-sequent M (rseq (ℂu (ℂe (ℂv (ℂe (ℂv Γ₂ 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) (↑₀ ●[ 𝕒0 , ↑d₁ del ]) 𝕣₀) (𝕣₀ ⊏ 𝕣₂))
                           𝕣₂ (↑₀ (↑₁ (boundedPushing₃ q del Δ))))
  ℍ𝟙𝟠 = rule-move-sat M (ℂv Γ 𝕍ℝ)
         (ℂu (ℂe (ℂv (ℂe (ℂv ℂ⟨⟩ 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕍ℝ) (↑₀ ●[ 𝕒0 , ↑d₁ del ]) 𝕣₀) (𝕣₀ ⊏ 𝕣₂))
         (Ｆ ↑₀، (↑ᵣ₀ r ⊑ 𝕣₀ →· ↑₀ (boundedPushing-aux₀ q del Δ)))
         (CEi ［ 𝟎 , 𝕣₀ ）) (CEr 𝕣₂) (↑₀ (↑₁ (boundedPushing₃ q del Δ)))
         (ℍ𝟙𝟡 , lift tt)

  ℍ𝟙𝟟 : sat-sequent M (rseq Γ₂ 𝕣₀ (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₁ del ] →· ↑₁ (boundedPushing₃ q del Δ))))
  ℍ𝟙𝟟 = rule∀I-sat M Γ₂ (CEr 𝕣₀) 𝕌Agent
         (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₁ del ] →· ↑₁ (boundedPushing₃ q del Δ))
         (rule→I-sat M (ℂv Γ₂ 𝕍Agent) 𝕣₁ (Correct 𝕒0)
           (◆· ●[ 𝕒0 , ↑d₁ del ] →· ↑₁ (boundedPushing₃ q del Δ))
           (rule→I-sat M (ℂe (ℂv Γ₂ 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕣₁
             (◆· ●[ 𝕒0 , ↑d₁ del ]) (↑₁ (boundedPushing₃ q del Δ))
             (◆·L-sat M (ℂe (ℂv Γ₂ 𝕍Agent) (Correct 𝕒0) 𝕣₁) 𝕣₁ 𝕣₁
               ●[ 𝕒0 , ↑d₁ del ] (↑₁ (boundedPushing₃ q del Δ))
               (ℍ𝟙𝟠 , lift tt) , lift tt) , lift tt) , lift tt)

  ℍ𝟙𝟞 : sat-sequent M (rseq (ℂv Γ₆ 𝕍Agents) 𝕣₂ (↑₀ (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₂ del ] →· ↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))))
  ℍ𝟙𝟞 = rule-thin-v-sat M Γ₆ 𝕍Agents 𝕣₁
         (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₂ del ] →· ↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
         (rule-thin-sat M Γ₅ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (CEr 𝕣₁) (CEr 𝕣₁)
           (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₂ del ] →· ↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
           (rule-thin-sat M Γ₄ (Correct 𝕒0) (CEr 𝕣₁) (CEr 𝕣₁)
             (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₂ del ] →· ↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
             (subst₂ (λ x y → sat-sequent M (rseq Γ₄ 𝕣₁ (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , x ] →· ↑₀ (↑₀، y)))))
                     (↑d₀،-↑d₁ del) (sym (boundedPushing₃-aux₃ q del Δ))
                     (subst (λ x → sat-sequent M (rseq Γ₄ 𝕣₁ (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₀، (↑d₁ del) ] →· x))))
                            (sym (↑₀↑₀،↑₀ (boundedPushing₃ q del Δ)))
                            (subst (λ x → sat-sequent M (rseq Γ₄ 𝕣₁ (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₀، (↑d₁ del) ] →· x))))
                                   (sym (↑₂≡↑₀،↑₁ (boundedPushing₃ q del Δ)))
                                   (rule-thin-v-sat M Γ₃ 𝕍Agent 𝕣₀
                                     (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₁ del ] →· ↑₁ (boundedPushing₃ q del Δ)))
                                     (rule-thin-sat M Γ₂ (↑ᵣ₀ r ⊑ 𝕣₀) (CEr 𝕣₀) (CEr 𝕣₀)
                                       (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , ↑d₁ del ] →· ↑₁ (boundedPushing₃ q del Δ)))
                                       (ℍ𝟙𝟟 , lift tt) , lift tt)))) , lift tt) , lift tt) , lift tt)

  ℍ𝟙𝟝 : sat-sequent M (rseq ℍΓ₁₅ 𝕣₃ (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))))
  ℍ𝟙𝟝 = rule-thin1-sat M 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
         (◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ])) (CEr 𝕣₃) (CEr 𝕣₃) (CEr 𝕣₃)
         (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
         (rule-thin1-sat M
           (ℂe (ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝕣₃)
           (¬· ↑₀،،، (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
           (◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ])) (CEr 𝕣₃) (CEr 𝕣₃) (CEr 𝕣₃)
           (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
           (rule-thin1-sat M (ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1))
             (◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ])) (CEr 𝕣₃) (CEr 𝕣₃) (CEr 𝕣₃)
             (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
             (move-to-concl-ext-sat M {ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃} 𝕣₃
               (◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ]))
               (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
               (move-to-concl-ext-sat M {ℂv 𝔾Γ₉ 𝕍Agent} 𝕣₃ (Correct 𝕒0)
                 (◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ]) →· ↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
                 (move-to-concl-v-sat M 𝔾Γ₉ 𝕌Agent 𝕣₂
                   (Correct 𝕒0 →· ◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ]) →· ↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
                   (rule-thin-sat M (ℂe (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) 𝕣₂)
                     (↑₀،، (pushing-aux₄ q del Δ)) (CEr 𝕣₂) (CEr 𝕣₂)
                     (∀ₐ (Correct 𝕒0 →· ◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ]) →· ↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))))
                     (rule-thin-sat M (ℂv Γ₆ 𝕍Agents) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) (CEr 𝕣₂) (CEr 𝕣₂)
                       (∀ₐ (Correct 𝕒0 →· ◆· (●[ 𝕒0 , ↑d₀،،، (↑d₂ del) ]) →· ↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))))
                       (subst₂ (λ x y → sat-sequent M (rseq (ℂv Γ₆ 𝕍Agents) 𝕣₂ (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , x ] →· y))))
                               (↑d₃≡↑d₀،،،↑d₂ del) (↑₀،↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))
                               (subst (λ x → sat-sequent M (rseq (ℂv Γ₆ 𝕍Agents) 𝕣₂ (∀ₐ (Correct 𝕒0 →· ◆· ●[ 𝕒0 , x ] →· ↑₀، (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))))))
                                      (sym (↑d₃≡↑d₀،↑d₂ del))
                                      ℍ𝟙𝟞) ,
                        lift tt) , lift tt) , lift tt) , lift tt) , lift tt) , lift tt) , lift tt) , lift tt)

  ℍ𝟙𝟜 : sat-sequent M (rseq (ℂe 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃) 𝕣₃ (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))))
  ℍ𝟙𝟜 = rule-cut-sat M (ℂe 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃)
         (CEr 𝕣₃) (CEr 𝕣₃) (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
         (◆· (↑₀،،، ●[ 𝕒0 , ↑d₂ del ]))
         (□↓¬∧◇↓◆⇒◆·-sat M
           (ℂe 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃)
           (↑ᵣ₀،،، (↑ᵣ₂ Δ)) 𝕣₃ (↑₀،،، ●[ 𝕒0 , ↑d₂ del ])
           (¬◇↓R-sat M (ℂe 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃) 𝕣₃ (↑ᵣ₀،،، (↑ᵣ₂ Δ)) (↑₀،،، ●[ 𝕒0 , ↑d₂ del ])
             ((subst (λ x → sat-sequent M (rseq (ℂe 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃) 𝕣₃ (¬· x)))
                     (↑◇↓ ⊆₀،،، (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
                     (rule-thin-sat M 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
                       (CEr 𝕣₃) (CEr 𝕣₃) (¬· ↑₀،،، (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
                       (ruleLbl-sat M
                         (ℂe (ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝕣₃) (CEr 𝕣₃)
                         (¬· ↑₀،،، (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) (lift tt) , lift tt))) , lift tt) ,
            subst (λ x → sat-sequent M (rseq (ℂe 𝔾Γ₁₄ (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) 𝕣₃) 𝕣₃ x))
                  (↑◇↓◆ ⊆₀،،، (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
                  (ruleLbl-sat M 𝔾Γ₁₄ (CEr 𝕣₃) (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) (lift tt)) ,
            lift tt) ,
          ℍ𝟙𝟝 ,
          lift tt)

  -- From 𝔾Γ₉'s last hyp, we can get that ◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ] --- this is 𝔾𝟙𝟜
  -- We also have ℍΓ₁₄'s last hyp, i.e., ¬· (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])
  -- So, it must be that ◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ] (strictly!) -- PROVE THIS!
  -- We can then eliminate the ◆ to jump to an earlier time
  -- and finally use the induction hyp in Γ₂
  𝔾𝟙𝟛 : sat-sequent M (rseq 𝔾Γ₁₄ 𝕣₃ (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))))
  𝔾𝟙𝟛 = rule-cut-sat M 𝔾Γ₁₄ (CEr 𝕣₃) (CEr 𝕣₃)
         (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
         (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
         (rule-thin-sat M
           (ℂe (ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃) (𝔸 (𝕒0 ∈ₐ 𝔸1)) 𝕣₃)
           (¬· ↑₀،،، (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ])) (CEr 𝕣₃) (CEr 𝕣₃)
           (↑₀،،، (◇↓◆ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
           (𝔾𝟙𝟜 , lift tt) ,
          ℍ𝟙𝟜 ,
          lift tt)

  𝔾𝟙𝟚 : sat-sequent M (rseq 𝔾Γ₁₃ 𝕣₂ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
  𝔾𝟙𝟚 = rule■L-now-sat M 𝔾Γ₉ 𝕣₂ 𝕣₂
         (¬· ∀ₐ (↑₀،،، (boundedPushing-aux₅ q del Δ)))
         (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))
         (rule¬∀L-sat M 𝔾Γ₉ 𝕣₂ 𝕣₂ 𝕌Agent
           (↑₀،،، (boundedPushing-aux₅ q del Δ))
           (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))
           (rule∃L-sat M 𝔾Γ₉ (CEr 𝕣₂) 𝕣₂ 𝕌Agent
             (¬· ↑₀،،، (boundedPushing-aux₅ q del Δ))
             (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))
             (rule¬→L-sat M (ℂv 𝔾Γ₉ 𝕍Agent) 𝕣₃ 𝕣₃ (Correct 𝕒0)
               (↑₀،،، (boundedPushing-aux₆ q del Δ))
               (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
               (rule¬→L-sat M (ℂe (ℂv 𝔾Γ₉ 𝕍Agent) (Correct 𝕒0) 𝕣₃) 𝕣₃ 𝕣₃
                 (𝔸 (𝕒0 ∈ₐ 𝔸1)) (↑₀،،، (◇↓ (↑ᵣ₂ Δ) ●[ 𝕒0 , ↑d₂ del ]))
                 (↑₀ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
                 (𝔾𝟙𝟛 , lift tt) , lift tt) , lift tt) , lift tt) , lift tt)

  𝔾𝟙𝟙 : sat-sequent M (rseq 𝔾Γ₁₂ 𝕣₂ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
  𝔾𝟙𝟙 = □↓L-now-sat M 𝔾Γ₉ 𝕣₂ 𝕣₂ (↑ᵣ ⊆₀،، (↑ᵣ₁ Δ))
         (■ (¬· ∀ₐ (↑₀،،، (boundedPushing-aux₅ q del Δ))))
         (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))
         (𝔾𝟙𝟚 , lift tt)

  -- hard case
  𝔾𝟙𝟘 : sat-sequent M (rseq 𝔾Γ₁₁ 𝕣₂ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ))))
  𝔾𝟙𝟘 = subst (λ x → sat-sequent M (rseq (ℂe 𝔾Γ₉ (¬· x) 𝕣₂) 𝕣₂ (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))))
              (sym (↑◇↓◆ ⊆₀،، (↑ᵣ₁ Δ) (∀ₐ (boundedPushing-aux₅ q del Δ))))
              (¬◇↓◆L-sat M 𝔾Γ₉ 𝕣₂ 𝕣₂ (↑ᵣ ⊆₀،، (↑ᵣ₁ Δ))
                (↑₀،، (∀ₐ (boundedPushing-aux₅ q del Δ)))
                (↑₀ (↑₀، (boundedPushing-aux₃ q del Δ)))
                (𝔾𝟙𝟙 , lift tt))

  -- now we need to go by cases
  𝔾𝟠 : sat-sequent M (rseq 𝔾Γ₉ 𝕣₂ (↑₀ (↑ ⊆₀، (boundedPushing-aux₃ q del Δ))))
  𝔾𝟠 = rule-cut-sat M 𝔾Γ₉ (CEr 𝕣₂) (CEr 𝕣₂) (↑₀ (↑ ⊆₀، (boundedPushing-aux₃ q del Δ)))
         (LEM (↑ ⊆₀،، (boundedPushing-aux₄ q del Δ)))
         (rule-classical-sat M 𝔾Γ₉ 𝕣₂ (↑ ⊆₀،، (boundedPushing-aux₄ q del Δ)) (lift tt) ,
          rule∨E-sat M 𝔾Γ₉ 𝕣₂ (CEr 𝕣₂)
           (↑ ⊆₀،، (boundedPushing-aux₄ q del Δ))
           (¬· ↑ ⊆₀،، (boundedPushing-aux₄ q del Δ))
           (↑₀ (↑ ⊆₀، (boundedPushing-aux₃ q del Δ)))
           (𝔾𝟡 , 𝔾𝟙𝟘 , lift tt) ,
          lift tt)

  𝔾𝟟 : sat-sequent M (rseq 𝔾Γ₈ 𝕣₂ (↑₀ (↑ ⊆₀، (boundedPushing-aux₃ q del Δ))))
  𝔾𝟟 = rule∧E-sat M (ℂv Γ₆ 𝕍Agents) (CEr 𝕣₂) (CEr 𝕣₂) (𝔸 (∣ 𝔸0 ∣ₛ＝ q)) (↑ ⊆₀،، (pushing-aux₄ q del Δ))
         (↑₀ (↑ ⊆₀، (boundedPushing-aux₃ q del Δ)))
         (𝔾𝟠 , lift tt)

  𝔾𝟞 : sat-sequent M (rseq 𝔾Γ₇ 𝕣₁ (↑ ⊆₀، (boundedPushing-aux₃ q del Δ))) -- from the last assumption
  𝔾𝟞 = rule∃L-sat M Γ₆ (CEr 𝕣₁) 𝕣₁ 𝕌Agents
         ((𝔸 (∣ 𝔸0 ∣ₛ＝ q)) ∧· ↑ ⊆₀،، (pushing-aux₄ q del Δ))
         (↑ ⊆₀، (boundedPushing-aux₃ q del Δ))
         (𝔾𝟟 , lift tt)

  𝔽𝟟 : sat-sequent M (rseq Γ₆ (↑ᵣ₁ r) (↑₁ (pushing q del Δ))) -- thin all hyps
  𝔽𝟟 = rule-thin-sat M Γ₅ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (CEr 𝕣₁) (CEr (↑ᵣ₁ r)) (↑₁ (pushing q del Δ))
         (rule-thin-sat M Γ₄ (Correct 𝕒0) (CEr 𝕣₁) (CEr (↑ᵣ₁ r)) (↑₁ (pushing q del Δ))
           (subst₂ (λ x y → sat-sequent M (rseq Γ₄ x y)) (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r)) (sym (↑₁≡↑₀↑₀ (pushing q del Δ)))
             (rule-thin-v-sat M Γ₃ 𝕍Agent (↑ᵣ₀ r) (↑₀ (pushing q del Δ))
               (rule-thin-sat M Γ₂ (↑ᵣ₀ r ⊑ 𝕣₀) (CEr 𝕣₀) (CEr (↑ᵣ₀ r)) (↑₀ (pushing q del Δ))
                 (rule-thin-sat M (ℂv Γ 𝕍ℝ) (↑₀ (Ｆ (↑ᵣ₀ r ⊑ 𝕣₀ →· ↑₀ (boundedPushing-aux₀ q del Δ)))) (CEi ［ ↑ᵣ₀ 𝟎 , 𝕣₀ ）) (CEr (↑ᵣ₀ r)) (↑₀ (pushing q del Δ))
                   (rule-thin-v-sat M Γ 𝕍ℝ r (pushing q del Δ) (hyp1 , lift tt) , lift tt) ,
                  lift tt) ,
                lift tt)) ,
            lift tt) ,
          lift tt)

  𝔽𝟙𝟚 : sat-sequent M (rseq Γ₆ 𝕣₁ (Correct 𝕒0)) -- one of the hyps, thin the rest
  𝔽𝟙𝟚 = rule-thin-sat M Γ₅ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (CEr 𝕣₁) (CEr 𝕣₁) (Correct 𝕒0)
          (ruleLbl-sat M Γ₄ (CEr 𝕣₁) (Correct 𝕒0) (lift tt) , lift tt)

  aux₀ : sub-Data (↑d₁، (↑d₀ del)) (CSub،ₗ 𝕒0) ≡ ↑d₀، (↑d₀ del)
  aux₀ = trans (cong (λ x → sub-Data x (CSub،ₗ 𝕒0)) (↑d₁،-↑d₀ del))
               (trans (cong (λ x → sub-Data x (CSub،ₗ 𝕒0)) (↑d₂≡↑d₀↑d₁ del))
                      (trans (sub-Data-↑d₀ _ _ 𝕒0 (↑d₁ del)) (↑d₁≡↑d₀،↑d₀ del)))

  aux₁ : sub (↑₁، (pushing-aux₃ q del Δ)) (CSub،ₗ 𝕒0) ≡ ↑₀، (pushing-aux₃ q del Δ)
  aux₁ = subst (λ x → sub (↑₁، {_} {𝕍ℝ} {𝕍Agent} x) (CSub،ₗ 𝕒0) ≡ ↑₀، x)
               (sym (pushing₃-aux₃ q del Δ))
               (trans (cong (λ x → sub x (CSub،ₗ 𝕒0)) (↑₁،-↑₀ (pushing₃ q del Δ)))
                      (trans (cong (λ x → sub x (CSub،ₗ 𝕒0)) (sym (↑₀-↑₁≡↑₂ _ _ _ _ (pushing₃ q del Δ))))
                             (trans (sub-↑₀ _ _ 𝕒0 (↑₁ (pushing₃ q del Δ)))
                                    (sym (↑₀،-↑₀ (pushing₃ q del Δ))))))

  𝔽𝟙𝟜 : sat-sequent M (rseq Γ₆ 𝕣₁ (●[ 𝕒0 , sub-Data (↑d (⊆، 𝕍Agent ⊆₁) (↑d₀ del)) (CSub،ₗ 𝕒0) ])) -- one of the hyps, thin the rest
  𝔽𝟙𝟜 = subst (λ x → sat-sequent M (rseq Γ₆ 𝕣₁ ●[ 𝕒0 , x ])) (sym aux₀)
              (ruleLbl-sat M Γ₅ (CEr 𝕣₁) ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (lift tt))

  𝔽𝟙𝟝 : sat-sequent M (rseq 𝔽Γ₁₂ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ))) -- from the last hyp
  𝔽𝟙𝟝 = subst (λ x → sat-sequent M (rseq 𝔽Γ₁₂ 𝕣₁ x)) aux₁
              (ruleLbl-sat M Γ₆ (CEr 𝕣₁) ((sub (↑ (⊆، 𝕍Agent ⊆₁) (pushing-aux₃ q del Δ)) (CSub،ₗ 𝕒0))) (lift tt))

  𝔽𝟙𝟛 : sat-sequent M (rseq 𝔽Γ₁₁ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ))) -- from the last hyp
  𝔽𝟙𝟛 = rule→L-sat M Γ₆ (CEr 𝕣₁) 𝕣₁
         (●[ 𝕒0 , sub-Data (↑d (⊆، 𝕍Agent ⊆₁) (↑d₀ del)) (CSub،ₗ 𝕒0) ])
         (sub (↑ (⊆، 𝕍Agent ⊆₁) (pushing-aux₃ q del Δ)) (CSub،ₗ 𝕒0))
         (↑ ⊆₀، (pushing-aux₃ q del Δ))
         (𝔽𝟙𝟜 , 𝔽𝟙𝟝 , lift tt)

  𝔽𝟙𝟙 : sat-sequent M (rseq 𝔽Γ₁₀ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ)))
  𝔽𝟙𝟙 = rule→L-sat M Γ₆ (CEr 𝕣₁) 𝕣₁ (Correct 𝕒0)
         (sub (↑ (⊆، 𝕍Agent ⊆₁) (pushing-aux₂ q del Δ)) (CSub،ₗ 𝕒0))
         (↑ ⊆₀، (pushing-aux₃ q del Δ))
         (𝔽𝟙𝟚 , 𝔽𝟙𝟛 , lift tt)

  𝔽𝟡 : sat-sequent M (rseq 𝔽Γ₉ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ))) -- instantiate the last hyp
  𝔽𝟡 = rule∀L′-sat M Γ₆ 𝕣₁ 𝕣₁ 𝕌Agent (↑ (⊆، 𝕍Agent ⊆₁) (pushing-aux₁ q del Δ)) (↑ ⊆₀، (pushing-aux₃ q del Δ)) 𝕒0
        (𝔽𝟙𝟙 , lift tt)

  𝔽𝟙𝟘 : sat-sequent M (rseq Γ₆ 𝕣₁ ((↑ᵣ₁ r) ⊑ 𝕣₁)) -- an hyp -- thin out all the others
  𝔽𝟙𝟘 = rule-thin-sat M Γ₅ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (CEr 𝕣₁) (CEr 𝕣₁) (↑ᵣ₁ r ⊑ 𝕣₁)
          (rule-thin-sat M Γ₄ (Correct 𝕒0) (CEr 𝕣₁) (CEr 𝕣₁) (↑ᵣ₁ r ⊑ 𝕣₁)
            (subst (λ x → sat-sequent M (rseq Γ₄ 𝕣₁ (x ⊑ 𝕣₁))) (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r))
              (rule-thin-v-sat M Γ₃ 𝕍Agent 𝕣₀ (↑ᵣ₀ r ⊑ 𝕣₀)
                (ruleLbl-sat M Γ₂ (CEr 𝕣₀) (↑ᵣ₀ r ⊑ 𝕣₀) (lift tt) , lift tt)) , lift tt) , lift tt)

  𝔽𝟠 : sat-sequent M (rseq 𝔽Γ₈ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ))) -- from the last hyp
  𝔽𝟠 = rule□L′-sat M Γ₆ (↑ᵣ₁ r) 𝕣₁ 𝕣₁ (↑₁ (pushing-aux₀ q del Δ)) (↑ ⊆₀، (pushing-aux₃ q del Δ))
         (𝔽𝟡 , 𝔽𝟙𝟘 , lift tt)

  𝔽𝟞 : sat-sequent M (rseq Γ₆ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ))) -- from the hypothesis
  𝔽𝟞 = rule-cut-sat M Γ₆ (CEr 𝕣₁) (CEr (↑ᵣ₁ r)) (↑ ⊆₀، (pushing-aux₃ q del Δ)) (↑₁ (pushing q del Δ)) (𝔽𝟟 , 𝔽𝟠 , lift tt)

  ℍ𝟝 : sat-sequent M (rseq Γ₆ 𝕣₁ (↑ ⊆₀، (boundedPushing-aux₃ q del Δ)))
  ℍ𝟝 = rule-cut-sat M Γ₆ (CEr 𝕣₁) (CEr 𝕣₁)
        (↑ ⊆₀، (boundedPushing-aux₃ q del Δ))
        (↑ ⊆₀، (pushing-aux₃ q del Δ))
        (𝔽𝟞 , 𝔾𝟞 , lift tt)

  ℍ𝟜 : sat-sequent M (rseq Γ₅ 𝕣₁ (↑ ⊆₀، (boundedPushing-aux₂ q del Δ)))
  ℍ𝟜 = rule→I-sat M Γ₅ 𝕣₁ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (↑ ⊆₀، (boundedPushing-aux₃ q del Δ)) (ℍ𝟝 , lift tt)

  ℍ𝟛 : sat-sequent M (rseq Γ₄ 𝕣₁ (↑ ⊆₀، (boundedPushing-aux₁ q del Δ)))
  ℍ𝟛 = rule→I-sat M Γ₄ 𝕣₁ (Correct 𝕒0) (↑ ⊆₀، (boundedPushing-aux₂ q del Δ)) (ℍ𝟜 , lift tt)

  ℍ𝟚 : sat-sequent M (rseq Γ₃ 𝕣₀ (↑₀ (boundedPushing-aux₀ q del Δ)))
  ℍ𝟚 = rule∀I-sat M Γ₃ (CEr 𝕣₀) 𝕌Agent (↑ ⊆₀، (boundedPushing-aux₁ q del Δ)) (ℍ𝟛 , lift tt)

  ℍ𝟙 : sat-sequent M (rseq Γ₂ 𝕣₀ (↑ᵣ₀ r ⊑ 𝕣₀ →· ↑₀ (boundedPushing-aux₀ q del Δ)))
  ℍ𝟙 = rule→I-sat M Γ₂ 𝕣₀ (↑ᵣ₀ r ⊑ 𝕣₀) (↑₀ (boundedPushing-aux₀ q del Δ)) (ℍ𝟚 , lift tt)

  ℍ𝟘 : sat-sequent M (rseq (ℂv Γ 𝕍ℝ) 𝕣₀ ((↑ᵣ₀ r ⊑ 𝕣₀) →· ↑₀ (boundedPushing-aux₀ q del Δ)))
  ℍ𝟘 = rule-induction-sat L M Γ ((↑ᵣ₀ r ⊑ 𝕣₀) →· ↑₀ (boundedPushing-aux₀ q del Δ)) (ℍ𝟙 , lift tt)

  ℍ : sat-sequent M (rseq Γ₁ 𝕣₀ (↑₀ (boundedPushing-aux₀ q del Δ)))
  ℍ = move-to-concl-sat M {ℂv Γ 𝕍ℝ} 𝕣₀ (↑ᵣ₀ r) 𝕣₀ LE (↑₀ (boundedPushing-aux₀ q del Δ)) (ℍ𝟘 , lift tt)

\end{code}

pistis2 : (Γ : ℂ₀) (r Δ : ℂRes Γ) (q : ℕ) (del : ℂData Γ) → Rule
pistis2 Γ r Δ q del =
  rule (rseq Γ r (send-if-event del)
        ∷ rseq Γ r (send-if-received del)
        ∷ rseq Γ r (event-if-received q del Δ)
        ∷ [])
       (rseq Γ r (pushing q del Δ))

-- hyp1: □(∀(a:Agent).Correct(a) → ∀(A:Agents). a sends del to A → del happened at a before)
-- hyp2: □(∀(a:Agent).∀(b:Agent). a reveived del from b → b send del to a before)
-- hyp3: □(∀(a:Agent).Correct(a) → del happened at a → ∃(A:Agents). |A|=Q ∧ ∀(b:Agent).◇↓ Δ (a received del from b))

pistis2-true : (M : Model₀)
               {Γ : ℂ₀} (r Δ : ℂRes Γ) (q : ℕ) (del : ℂData Γ)
             → sat-rule M (pistis2 Γ r Δ q del)
pistis2-true M {Γ} r Δ q del (hyp1 , hyp2 , hyp3 , _) =
  rule□R-sat M Γ r (pushing-aux₀ q del Δ)
    (rule∀I-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕣₀ 𝕌Agent (↑ ⊆₀، (pushing-aux₁ q del Δ))
      (𝟙 , (lift tt)) ,
     lift tt)
  where
  Γ₀ : ℂ₀
  Γ₀ = ℂe (ℂv (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent) (Correct 𝕒0) 𝕣₁

  Γ₁ : ℂ₀
  Γ₁ = ℂe Γ₀ (●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ]) 𝕣₁

  Γ₂ : ℂ₀
  Γ₂ = ℂe Γ₁ (↑ ⊆₀، (event-if-received-aux₀ q del Δ)) 𝕣₁

  Γ₃ : ℂ₀
  Γ₃ = ℂe Γ₁ (↑₁ (event-if-received q del Δ)) (↑ᵣ₁ r)

  Γ₄ : ℂ₀
  Γ₄ = ℂe Γ₁ (↑₁ (event-if-received-aux₁ q del Δ)) 𝕣₁

  Γ₅ : ℂ₀
  Γ₅ = ℂe Γ₁ (Correct 𝕒0 →· ●[ 𝕒0 , sub-Data (↑d (⊆، 𝕍Agent ⊆₁) (↑d₀ del)) (CSub،ₗ 𝕒0) ] →· sub (↑ (⊆، 𝕍Agent ⊆₁) (event-if-received-aux₀ q del Δ)) (CSub،ₗ 𝕒0)) 𝕣₁

  𝟞 : sat-sequent M (rseq Γ₁ (↑ᵣ₁ r) (↑₁ (event-if-received q del Δ))) -- by thinning to get back to Γ and so hyp3
  𝟞 = rule-thin-sat M Γ₀ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (CEr 𝕣₁) (CEr (↑ᵣ₁ r)) (↑₁ (event-if-received q del Δ))
        (rule-thin-sat M (ℂv (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent) (Correct 𝕒0) (CEr 𝕣₁) (CEr (↑ᵣ₁ r)) (↑₁ (event-if-received q del Δ))
           (subst₂ (λ x y → sat-sequent M (rseq (ℂv (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent) x y))
                   (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r))
                   (sym (↑₁≡↑₀↑₀ (event-if-received q del Δ)))
                   (rule-thin-v-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent (↑ᵣ₀ r) (↑₀ (event-if-received q del Δ))
                     (rule-thin-sat M (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀) CEu (CEr (↑ᵣ₀ r)) (↑₀ (event-if-received q del Δ))
                       (rule-thin-v-sat M Γ 𝕍ℝ r (event-if-received q del Δ) (hyp3 , lift tt) ,
                        lift tt) ,
                      lift tt)) ,
            lift tt) ,
         lift tt)

  𝟙𝟘 : sat-sequent M (rseq Γ₅ 𝕣₁ (↑ ⊆₀، (event-if-received-aux₀ q del Δ))) -- from the last hyp in Γ₅ - use rule→L-sat
  𝟙𝟘 = {!!}

  𝟠 : sat-sequent M (rseq Γ₄ 𝕣₁ (↑ ⊆₀، (event-if-received-aux₀ q del Δ))) -- from the last hyp in Γ₄ - use ∀L
  𝟠 = rule∀L′-sat M Γ₁ 𝕣₁ 𝕣₁ 𝕌Agent
        (↑ (⊆، 𝕍Agent ⊆₁) (Correct 𝕒0 →· ●[ 𝕒0 , ↑d₀ del ] →· event-if-received-aux₀ q del Δ))
        (↑ ⊆₀، (event-if-received-aux₀ q del Δ)) 𝕒0 (𝟙𝟘 , lift tt)

  𝟡 : sat-sequent M (rseq Γ₁ 𝕣₁ (↑ᵣ₁ r ⊑ 𝕣₁)) -- thin
  𝟡 = rule-thin-sat M Γ₀ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (CEr 𝕣₁) (CEr 𝕣₁) (↑ᵣ₁ r ⊑ 𝕣₁)
        (rule-thin-sat M (ℂv (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent) (Correct 𝕒0) (CEr 𝕣₁) (CEr 𝕣₁) (↑ᵣ₁ r ⊑ 𝕣₁)
          (subst (λ x → sat-sequent M (rseq (ℂv (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent) 𝕣₁ (x ⊑ 𝕣₁)))
                 (sym (↑ᵣ₁≡↑ᵣ₀↑ᵣ₀ r))
                 (rule-thin-v-sat M (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent 𝕣₀ (↑ᵣ₀ r ⊑ 𝕣₀)
                   (rule-id-comp-u-sat M (ℂv Γ 𝕍ℝ) (CEr 𝕣₀) (↑ᵣ₀ r) 𝕣₀ LE (lift tt) , lift tt)) ,
           lift tt) ,
         lift tt)

  𝟟 : sat-sequent M (rseq Γ₃ 𝕣₁ (↑ ⊆₀، (event-if-received-aux₀ q del Δ))) -- from the last hyp in Γ₃
  𝟟 = rule□L′-sat M Γ₁ (↑ᵣ₁ r) 𝕣₁ 𝕣₁ (↑₁ (event-if-received-aux₁ q del Δ)) (↑ ⊆₀، (event-if-received-aux₀ q del Δ))
       (𝟠 , 𝟡 , lift tt)

  𝟜 : sat-sequent M (rseq Γ₁ 𝕣₁ (↑ ⊆₀، (event-if-received-aux₀ q del Δ))) -- from hyp3
  𝟜 = rule-cut-sat M Γ₁ (CEr 𝕣₁) (CEr (↑ᵣ₁ r)) (↑ ⊆₀، (event-if-received-aux₀ q del Δ)) (↑₁ (event-if-received q del Δ))
        (𝟞 , 𝟟 , lift tt)

  𝟝 : sat-sequent M (rseq Γ₂ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ)))
  𝟝 = {!!} -- eliminate the ∃ in the last hypothesis

  𝟛 : sat-sequent M (rseq Γ₁ 𝕣₁ (↑ ⊆₀، (pushing-aux₃ q del Δ)))
  𝟛 = rule-cut-sat M Γ₁ (CEr 𝕣₁) (CEr 𝕣₁) (↑ ⊆₀، (pushing-aux₃ q del Δ)) (↑ ⊆₀، (event-if-received-aux₀ q del Δ))
        (𝟜 , 𝟝 , lift tt)

  𝟚 : sat-sequent M (rseq Γ₀ 𝕣₁ (↑ ⊆₀، (pushing-aux₂ q del Δ)))
  𝟚 = rule→I-sat M Γ₀ 𝕣₁ ●[ 𝕒0 , ↑d ⊆₀، (↑d₀ del) ] (↑ ⊆₀، (pushing-aux₃ q del Δ)) (𝟛 , lift tt)

  𝟙 : sat-sequent M (rseq (ℂv (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent) 𝕣₁ (↑ ⊆₀، (pushing-aux₁ q del Δ)))
  𝟙 = rule→I-sat M (ℂv (ℂu (ℂv Γ 𝕍ℝ) (↑ᵣ₀ r ⊑ 𝕣₀)) 𝕍Agent) 𝕣₁ (Correct 𝕒0) (↑ ⊆₀، (pushing-aux₂ q del Δ))
        (𝟚 , lift tt)


\end{code}
