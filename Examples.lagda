The same examples proved with both methods for meta-level unknowns (Agda
variables standing for formulas, time expressions or contexts).

  * SUBSTITUTION (by hand): abstract the goal by hand, using formula
    variables (var k) and resource variables (rvar k), run search⊢, extract
    the derivation with from-just (which only typechecks if the search
    succeeds), and instantiate it with plug-⊢ (Plug.lagda), which plugs the
    result into a context Γ (here often the empty context ℂ⟨⟩).  Rules are
    proved with hyps→rule + plug-⊢.
  * REFLECTION (ProveTactic.lagda): the macro `prove n` does the abstraction
    and the instantiation itself, on goals ⊢ s, sat-sequent M s and
    sat-rule M (rule ps s).

Each example has the same statement in both sections; the names end in
-refl and -subst respectively.

\begin{code}
{-# OPTIONS --safe #-}

open import Level using (0ℓ ; lift) renaming (suc to lsuc)
open import Data.List using ([] ; _∷_)
open import Data.Product using (_,_)
open import Data.Maybe using (from-just)

open import World

module Examples (W : World)
       where

open import Decidable(W)
open import Syntax(𝔻)(W)
open import Subst(𝔻)(W) using (𝕣₀ ; ◇↓ ; ↑₀)
open import Semantics(𝔻)(W)
open import Automation W
open import Plug W
open import ProveTactic W
open import RulesTemp(𝔻)(W)
  using (rule◇↓R ; rule◇R ; ruleＯR ; rule◇↓R-now ; rule◆R-now ; rule⊑-trans ; rule＝-⋆-congᵣ)

\end{code}

SUBST APPROACH

\begin{code}

id-subst : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
         → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr t) (A →· A)))
id-subst M A t _ =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (𝐯0 →· 𝐯0))))

∧-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
        → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A ∧· B) →· B ∧· A))
∧-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 ∧· 𝐯1) →· 𝐯1 ∧· 𝐯0))))

→-subst : (M : Model₀) (A B C : Form₀) (t : ℂRes ℂ⟨⟩)
        → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· A →· C))
→-subst M A B C t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ C ⨾ ●))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 →· 𝐯1) →· (𝐯1 →· 𝐯2) →· 𝐯0 →· 𝐯2))))

chain3-subst : (M : Model₀) (A B C D : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· A →· D))
chain3-subst M A B C D t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ C ⨾ (3 ↦ D ⨾ ●)))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0))
              ((𝐯0 →· 𝐯1) →· (𝐯1 →· 𝐯2) →· (𝐯2 →· var 3) →· 𝐯0 →· var 3))))

chain4-subst : (M : Model₀) (A B C D E : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· (D →· E) →· A →· E))
chain4-subst M A B C D E t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ C ⨾ (3 ↦ D ⨾ (4 ↦ E ⨾ ●))))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 →· 𝐯1) →· (𝐯1 →· 𝐯2) →· (𝐯2 →· var 3) →· (var 3 →· var 4) →· 𝐯0 →· var 4))))

chain5-subst : (M : Model₀) (A B C D E F : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· (D →· E) →· (E →· F) →· A →· F))
chain5-subst M A B C D E F t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ C ⨾ (3 ↦ D ⨾ (4 ↦ E ⨾ (5 ↦ F ⨾ ●)))))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 →· 𝐯1) →· (𝐯1 →· 𝐯2) →· (𝐯2 →· var 3) →· (var 3 →· var 4) →· (var 4 →· var 5) →· 𝐯0 →· var 5))))

chain6-subst : (M : Model₀) (A B C D E F G : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· (D →· E) →· (E →· F) →· (F →· G) →· A →· G))
chain6-subst M A B C D E F G t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ C ⨾ (3 ↦ D ⨾ (4 ↦ E ⨾ (5 ↦ F ⨾ (6 ↦ G ⨾ ●))))))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 →· 𝐯1) →· (𝐯1 →· 𝐯2) →· (𝐯2 →· var 3) →· (var 3 →· var 4) →· (var 4 →· var 5) →· (var 5 →· var 6) →· 𝐯0 →· var 6))))

distr-subst : (M : Model₀) (A B C D : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t)
                (((A ∨· B) ∧· (C ∨· D)) →· (((A ∧· C) ∨· (A ∧· D)) ∨· ((B ∧· C) ∨· (B ∧· D)))))
distr-subst M A B C D t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ C ⨾ (3 ↦ D ⨾ ●)))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0))
              (((𝐯0 ∨· 𝐯1) ∧· (𝐯2 ∨· var 3)) →· (((𝐯0 ∧· 𝐯2) ∨· (𝐯0 ∧· var 3)) ∨· ((𝐯1 ∧· 𝐯2) ∨· (𝐯1 ∧· var 3)))))))

∨-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
        → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A ∨· B) →· (B ∨· A)))
∨-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 ∨· 𝐯1) →· (𝐯1 ∨· 𝐯0)))))

-- The hypotheses of the abstract sequent are instantiated by plug-⊢ too.
ctx-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
          → sat-sequent M (seq (ℂe ℂ⟨⟩ (A ∧· B) t) (CEr t) (B ∨· ⊥·))
ctx-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe ℂ⟨⟩ (𝐯0 ∧· 𝐯1) (rvar 0)) (CEr (rvar 0)) (𝐯1 ∨· ⊥·))))

-- A is substituted for var 1; var 0 is not in the domain of σ and stays.
mixed-subst : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((Ｏ A ∧· var 0) →· (var 0 ∧· Ｏ A)))
mixed-subst M A t =
  sound M (plug-⊢ ℂ⟨⟩ (1 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((Ｏ 𝐯1 ∧· 𝐯0) →· (𝐯0 ∧· Ｏ 𝐯1)))))

next-subst : (M : Model₀) (A : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t ◁ t₁)) A t₁) (CEr t) (Ｏ A))
next-subst M A t t₁ =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe (ℂu ℂ⟨⟩ (rvar 0 ◁ rvar 1)) 𝐯0 (rvar 1)) (CEr (rvar 0)) (Ｏ 𝐯0))))

eventually-subst : (M : Model₀) (B : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
                 → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t ⊑ t₁)) B t₁) (CEr t) (◇ B))
eventually-subst M B t t₁ =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ B ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe (ℂu ℂ⟨⟩ (rvar 0 ⊑ rvar 1)) 𝐯0 (rvar 1)) (CEr (rvar 0)) (◇ 𝐯0))))

-- Open formulas: plug the closed derivation into Γ = ℂv ℂ⟨⟩ 𝕍ℝ, with the
-- label 𝕣₀ given as a resource variable.
binder-subst : (A B : Form (⟨⟩ ، 𝕍ℝ))
             → ⊢ (seq (ℂe (ℂv ℂ⟨⟩ 𝕍ℝ) (A ∧· B) 𝕣₀) (CEr 𝕣₀) (B ∧· A))
binder-subst A B =
  plug-⊢ (ℂv ℂ⟨⟩ 𝕍ℝ) (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ 𝕣₀ ⨾ ●ᵣ)
    (from-just (search⊢ 10 (ℂe ℂ⟨⟩ (𝐯0 ∧· 𝐯1) (rvar 0)) (CEr (rvar 0)) (𝐯1 ∧· 𝐯0)))

-- Rules over an arbitrary context Γ, with opaque resources.
-- The premises become hypotheses (hyps→rule), the opaque formulas and
-- resources become var k / rvar k, and the derivation found for the closed
-- version is plugged into Γ (plug-⊢).
◇↓R-subst : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ)
          → sat-rule M (rule◇↓R Γ t r r₁ A)
◇↓R-subst M Γ t r r₁ A =
  hyps→rule M Γ ((CEr r , r ⊑ r₁) ∷ (CEr r , r₁ ⊑ r ⋆ t) ∷ (CEr r₁ , A) ∷ []) (CEr r) (◇↓ t A)
    (sound M (plug-⊢ Γ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ r ⨾ 2 ↦ᵣ r₁ ⨾ ●ᵣ)
      (from-just (search⊢ 10
        (addHyps ℂ⟨⟩ ((CEr (rvar 1) , rvar 1 ⊑ rvar 2)
                    ∷ (CEr (rvar 1) , rvar 2 ⊑ rvar 1 ⋆ rvar 0)
                    ∷ (CEr (rvar 2) , 𝐯0) ∷ []))
        (CEr (rvar 1)) (◇↓ (rvar 0) 𝐯0)))))

◇R-subst : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
         → sat-rule M (rule◇R Γ r r₁ A)
◇R-subst M Γ r r₁ A =
  hyps→rule M Γ ((CEr r , r ⊑ r₁) ∷ (CEr r₁ , A) ∷ []) (CEr r) (◇ A)
    (sound M (plug-⊢ Γ (0 ↦ A ⨾ ●) (0 ↦ᵣ r ⨾ 1 ↦ᵣ r₁ ⨾ ●ᵣ)
      (from-just (search⊢ 10
        (addHyps ℂ⟨⟩ ((CEr (rvar 0) , rvar 0 ⊑ rvar 1) ∷ (CEr (rvar 1) , 𝐯0) ∷ []))
        (CEr (rvar 0)) (◇ 𝐯0)))))

ＯR-subst : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
          → sat-rule M (ruleＯR Γ r r₁ A)
ＯR-subst M Γ r r₁ A =
  hyps→rule M Γ ((CEu , r ◁ r₁) ∷ (CEr r₁ , A) ∷ []) (CEr r) (Ｏ A)
    (sound M (plug-⊢ Γ (0 ↦ A ⨾ ●) (0 ↦ᵣ r ⨾ 1 ↦ᵣ r₁ ⨾ ●ᵣ)
      (from-just (search⊢ 10
        (addHyps ℂ⟨⟩ ((CEu , rvar 0 ◁ rvar 1) ∷ (CEr (rvar 1) , 𝐯0) ∷ []))
        (CEr (rvar 0)) (Ｏ 𝐯0)))))


-- Past operators and temporal left rules.

-- ＯL, then ＯI with the new time point as witness.
nextL-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) (Ｏ A →· Ｏ (A ∨· B)))
nextL-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (Ｏ 𝐯0 →· Ｏ (𝐯0 ∨· 𝐯1)))))

-- ＵL, then ＵI (◇ B = ⊤· Ｕ B).
untilL-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｕ B) →· ◇ B))
untilL-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 Ｕ 𝐯1) →· ◇ 𝐯1))))

-- ＦL (freeze): Ｆ A at t gives A[x/t] at t.
freezeL-subst : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
              → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((Ｆ (↑₀ A)) →· A))
freezeL-subst M A t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((Ｆ 𝐯0) →· 𝐯0))))

-- ＹI, with the witness taken from the hypothesis t₁ ◁ t.
prev-subst : (M : Model₀) (A : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t₁ ◁ t)) A t₁) (CEr t) (Ｙ A))
prev-subst M A t t₁ =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe (ℂu ℂ⟨⟩ (rvar 1 ◁ rvar 0)) 𝐯0 (rvar 1)) (CEr (rvar 0)) (Ｙ 𝐯0))))

-- ＹL, then ＹI.
prevL-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) (Ｙ A →· Ｙ (A ∨· B)))
prevL-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (Ｙ 𝐯0 →· Ｙ (𝐯0 ∨· 𝐯1)))))

-- ＳI (◆ B = ⊤· Ｓ B), with the witness taken from the hypothesis t₁ ⊑ t.
before-subst : (M : Model₀) (B : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t₁ ⊑ t)) B t₁) (CEr t) (◆ B))
before-subst M B t t₁ =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ B ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe (ℂu ℂ⟨⟩ (rvar 1 ⊑ rvar 0)) 𝐯0 (rvar 1)) (CEr (rvar 0)) (◆ 𝐯0))))

-- ＳL, then ＳI.
sinceL-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｓ B) →· ◆ B))
sinceL-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 Ｓ 𝐯1) →· ◆ 𝐯1))))

-- ＢL, instantiated at t₁ from the hypothesis t₁ ◁ t.
bprevL-subst : (M : Model₀) (A : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t₁ ◁ t)) (Ｂ A) t) (CEr t₁) A)
bprevL-subst M A t t₁ =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe (ℂu ℂ⟨⟩ (rvar 1 ◁ rvar 0)) (Ｂ 𝐯0) (rvar 0)) (CEr (rvar 1)) 𝐯0)))

-- ＢI, then ＢL at the new time point.
bprev-subst : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) (Ｂ (A ∧· B) →· Ｂ A))
bprev-subst M A B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ ●)) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (Ｂ (𝐯0 ∧· 𝐯1) →· Ｂ 𝐯0))))


-- Reasoning about comparisons.

-- Transitivity through ◁, ⊑ and ⊏; the result is used at label t.
cmp-trans-subst : (M : Model₀) (t t₁ t₂ t₃ : ℂRes ℂ⟨⟩)
                → sat-sequent M (seq (ℂu (ℂu (ℂu ℂ⟨⟩ (t₁ ◁ t₂)) (t₂ ⊑ t₃)) (t₃ ⊏ t)) (CEr t) (t₁ ⊏ t))
cmp-trans-subst M t t₁ t₂ t₃ =
  sound M (plug-⊢ ℂ⟨⟩ ● (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ 2 ↦ᵣ t₂ ⨾ 3 ↦ᵣ t₃ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂu (ℂu (ℂu ℂ⟨⟩ (rvar 1 ◁ rvar 2)) (rvar 2 ⊑ rvar 3)) (rvar 3 ⊏ rvar 0))
                                   (CEr (rvar 0)) (rvar 1 ⊏ rvar 0))))

-- Congruence of ⋆, with an equation turned around.
cmp-cong-subst : (M : Model₀) (t t₁ t₂ : ℂRes ℂ⟨⟩)
               → sat-sequent M (seq (ℂu ℂ⟨⟩ (t₂ ＝ t₁)) CEu (t ⋆ t₁ ⊑ t ⋆ t₂))
cmp-cong-subst M t t₁ t₂ =
  sound M (plug-⊢ ℂ⟨⟩ ● (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ 2 ↦ᵣ t₂ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂu ℂ⟨⟩ (rvar 2 ＝ rvar 1)) CEu (rvar 0 ⋆ rvar 1 ⊑ rvar 0 ⋆ rvar 2))))

-- Monoid equations and 𝟎 ⊑ t.
cmp-monoid-subst : (M : Model₀) (t t₁ : ℂRes ℂ⟨⟩)
                 → sat-sequent M (seq ℂ⟨⟩ (CEr t) (((𝟎 ⋆ t) ⋆ t₁ ＝ t ⋆ t₁) ∧· (t ⋆ t₁ ＝ t₁ ⋆ t) ∧· (𝟎 ⊑ t₁)))
cmp-monoid-subst M t t₁ =
  sound M (plug-⊢ ℂ⟨⟩ ● (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (((𝟎 ⋆ rvar 0) ⋆ rvar 1 ＝ rvar 0 ⋆ rvar 1) ∧· (rvar 0 ⋆ rvar 1 ＝ rvar 1 ⋆ rvar 0) ∧· (𝟎 ⊑ rvar 1)))))

-- ◇ with the current time as witness (r ⊑ r).
eventually-now-subst : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
                     → sat-sequent M (seq (ℂe ℂ⟨⟩ A t) (CEr t) (◇ A))
eventually-now-subst M A t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe ℂ⟨⟩ 𝐯0 (rvar 0)) (CEr (rvar 0)) (◇ 𝐯0))))

-- rule◇↓R-now, which needs r ⊑ r and r ⊑ r ⋆ t.
◇↓R-now-subst : (M : Model₀) (Γ : ℂ₀) (t r : ℂRes Γ) (A : ℂForm Γ)
              → sat-rule M (rule◇↓R-now Γ t r A)
◇↓R-now-subst M Γ t r A =
  hyps→rule M Γ ((CEr r , A) ∷ []) (CEr r) (◇↓ t A)
    (sound M (plug-⊢ Γ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ r ⨾ ●ᵣ)
      (from-just (search⊢ 10
        (addHyps ℂ⟨⟩ ((CEr (rvar 1) , 𝐯0) ∷ []))
        (CEr (rvar 1)) (◇↓ (rvar 0) 𝐯0)))))


-- Quantifiers.  p₀ is the proposition variable bound by the quantifier.

-- Interval hypotheses (InL): monotonicity of Ｕ and Ｓ, where the A@[t,x)
-- hypothesis that ＵL/ＳL produce is used at the fresh point of ＵR/ＳR.
untilMono-subst : (M : Model₀) (A B D : Form₀) (t : ℂRes ℂ⟨⟩)
                → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｕ B) →· ((A ∨· D) Ｕ B)))
untilMono-subst M A B D t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ D ⨾ ●))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 Ｕ 𝐯1) →· ((𝐯0 ∨· 𝐯2) Ｕ 𝐯1)))))

sinceMono-subst : (M : Model₀) (A B D : Form₀) (t : ℂRes ℂ⟨⟩)
                → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｓ B) →· ((A ∨· D) Ｓ B)))
sinceMono-subst M A B D t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ (1 ↦ B ⨾ (2 ↦ D ⨾ ●))) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) ((𝐯0 Ｓ 𝐯1) →· ((𝐯0 ∨· 𝐯2) Ｓ 𝐯1)))))

-- A hypothesis over a closed interval, used at a point placed in it by
-- comparison hypotheses.
inClosed-subst : (M : Model₀) (A : Form₀) (t t₁ t₂ : ℂRes ℂ⟨⟩)
               → sat-sequent M (seq (ℂu (ℂu (ℂi ℂ⟨⟩ A ［ t₁ , t₂ ］) (t₁ ⊑ t)) (t ⊑ t₂)) (CEr t) A)
inClosed-subst M A t t₁ t₂ =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ 2 ↦ᵣ t₂ ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂu (ℂu (ℂi ℂ⟨⟩ 𝐯0 ［ rvar 1 , rvar 2 ］) (rvar 1 ⊑ rvar 0)) (rvar 0 ⊑ rvar 2))
                                   (CEr (rvar 0)) 𝐯0)))

-- □I: □ (A →· A).
always-subst : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) (□ (A →· A)))
always-subst M A t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (□ (𝐯0 →· 𝐯0)))))

-- ∈I: membership in an explicit list of (constant) agents.
member-subst : (M : Model₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) (𝔸 (agentC 1 ∈ₐ agentsL (agentC 0 ∷ agentC 1 ∷ []))))
member-subst M t =
  sound M (plug-⊢ ℂ⟨⟩ ● (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (𝔸 (agentC 1 ∈ₐ agentsL (agentC 0 ∷ agentC 1 ∷ []))))))

-- □L (classical, with search⊢ᶜ): □ A at t₁ and t₁ ⊑ t give A at t.
module _ (em : EMT) where
  alwaysL-subst : (M : Model₀) (A : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
                → sat-sequent M (seq (ℂu (ℂe ℂ⟨⟩ (□ A) t₁) (t₁ ⊑ t)) (CEr t) A)
  alwaysL-subst M A t t₁ =
    sound M (plug-⊢ ℂ⟨⟩ (0 ↦ A ⨾ ●) (0 ↦ᵣ t ⨾ 1 ↦ᵣ t₁ ⨾ ●ᵣ)
              (from-just (search⊢ᶜ em 10 (ℂu (ℂe ℂ⟨⟩ (□ 𝐯0) (rvar 1)) (rvar 1 ⊑ rvar 0)) (CEr (rvar 0)) 𝐯0)))

-- forwarding of Rules.lagda, with concrete agents a, b, c (agentC 0, 1, 2),
-- data p (dataC 0) and resources Δ, r (rvar 0, rvar 1): by search⊢ᶜ, which
-- instantiates the synchrony assumption and the relay hypothesis by
-- matching and derives the facts forward (see "Matching and saturation" in
-- SUMMARY.md).  forwarding-auto below proves the general rule.
module _ (em : EMT) where
  open import Rules(𝔻)(W)(em) using (forwarding ; synchrony-assumption ; relay)

  forwarding-concrete : (M : Model₀)
    → sat-rule M (forwarding ℂ⟨⟩ (agentC 0) (agentC 1) (agentC 2) (rvar 0) (rvar 1) (dataC 0))
  forwarding-concrete M =
    hyps→rule M ℂ⟨⟩ ((CEr r , synchrony-assumption Δ) ∷ (CEr r , relay a b c) ∷ (CEr r , send[ a ⇒ p ⇒ [ b ]ₐ ]) ∷ [])
      (CEr r) (◇↓ (Δ ⋆ Δ) recv[ c ⇐ p ⇐ b ])
      (sound M (from-just (search⊢ᶜ em 5 (ℂe (ℂe (ℂe ℂ⟨⟩ (synchrony-assumption Δ) r) (relay a b c) r) send[ a ⇒ p ⇒ [ b ]ₐ ] r)
                                        (CEr r) (◇↓ (Δ ⋆ Δ) recv[ c ⇐ p ⇐ b ]))))
    where
    a b c : {Γ : Ctxt} → Agent Γ
    a = agentC 0
    b = agentC 1
    c = agentC 2
    p : {Γ : Ctxt} → Data Γ
    p = dataC 0
    Δ r : {Γ : Ctxt} → Res Γ
    Δ = rvar 0
    r = rvar 1

p₀ : {Γ : Ctxt} → Form (Γ ، 𝕍𝕌 𝕌Prop)
p₀ {Γ} = 𝕒 (atProp (atomPropV (∈Ctxt0 Γ)))

-- ∀I, then ∀L with the new variable.
forall-subst : (M : Model₀) (B : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) (∀· 𝕌Prop (p₀ ∧· ↑₀ B) →· ∀· 𝕌Prop (p₀ ∨· ↑₀ B)))
forall-subst M B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ B ⨾ ●) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (∀· 𝕌Prop (p₀ ∧· 𝐯0) →· ∀· 𝕌Prop (p₀ ∨· 𝐯0)))))

-- ∃L, then ∃R with the new variable.
exists-subst : (M : Model₀) (B : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) (∃· 𝕌Prop (p₀ ∧· ↑₀ B) →· (∃· 𝕌Prop p₀ ∧· B)))
exists-subst M B t =
  sound M (plug-⊢ ℂ⟨⟩ (0 ↦ B ⨾ ●) (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 ℂ⟨⟩ (CEr (rvar 0)) (∃· 𝕌Prop (p₀ ∧· 𝐯0) →· (∃· 𝕌Prop p₀ ∧· 𝐯0)))))

-- ∃L, then ∀L and ∃R at the same variable.
forall-exists-subst : (M : Model₀) (t : ℂRes ℂ⟨⟩)
                    → sat-sequent M (seq (ℂe ℂ⟨⟩ (∃· 𝕌Prop p₀) t) (CEr t)
                                         (∀· 𝕌Prop (p₀ →· p₀) →· ∃· 𝕌Prop p₀))
forall-exists-subst M t =
  sound M (plug-⊢ ℂ⟨⟩ ● (0 ↦ᵣ t ⨾ ●ᵣ)
            (from-just (search⊢ 10 (ℂe ℂ⟨⟩ (∃· 𝕌Prop p₀) (rvar 0)) (CEr (rvar 0))
                                   (∀· 𝕌Prop (p₀ →· p₀) →· ∃· 𝕌Prop p₀))))

\end{code}

REFLECTION APPROACH

\begin{code}

id-refl : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
        → sat-rule M (rule [] (seq ℂ⟨⟩ (CEr t) (A →· A)))
id-refl M A t = prove 10

∧-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
       → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A ∧· B) →· B ∧· A))
∧-refl M A B t = prove 10

→-refl : (M : Model₀) (A B C : Form₀) (t : ℂRes ℂ⟨⟩)
       → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· A →· C))
→-refl M A B C t = prove 10

-- Longer chains of implications.
chain3-refl : (M : Model₀) (A B C D : Form₀) (t : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· A →· D))
chain3-refl M A B C D t = prove 10

chain4-refl : (M : Model₀) (A B C D E : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· (D →· E) →· A →· E))
chain4-refl M A B C D E t = prove 10

chain5-refl : (M : Model₀) (A B C D E F : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· (D →· E) →· (E →· F) →· A →· F))
chain5-refl M A B C D E F t = prove 10

chain6-refl : (M : Model₀) (A B C D E F G : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A →· B) →· (B →· C) →· (C →· D) →· (D →· E) →· (E →· F) →· (F →· G) →· A →· G))
chain6-refl M A B C D E F G t = prove 10

-- Distributivity: branching on two disjunctions (∨L).
distr-refl : (M : Model₀) (A B C D : Form₀) (t : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq ℂ⟨⟩ (CEr t)
               (((A ∨· B) ∧· (C ∨· D)) →· (((A ∧· C) ∨· (A ∧· D)) ∨· ((B ∧· C) ∨· (B ∧· D)))))
distr-refl M A B C D t = prove 10

∨-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
       → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A ∨· B) →· (B ∨· A)))
∨-refl M A B t = prove 10

-- A hypothesis in the context.
ctx-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
         → sat-sequent M (seq (ℂe ℂ⟨⟩ (A ∧· B) t) (CEr t) (B ∨· ⊥·))
ctx-refl M A B t = prove 10

-- Agda formulas mixed with object variables, and inside a temporal operator.
mixed-refl : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((Ｏ A ∧· var 0) →· (var 0 ∧· Ｏ A)))
mixed-refl M A t = prove 10

-- Ｏ with the witness taken from the hypothesis t ◁ t₁.
next-refl : (M : Model₀) (A : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
          → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t ◁ t₁)) A t₁) (CEr t) (Ｏ A))
next-refl M A t t₁ = prove 10

-- ◇ B = ⊤· Ｕ B, with the witness taken from the hypothesis t ⊑ t₁.
eventually-refl : (M : Model₀) (B : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
                → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t ⊑ t₁)) B t₁) (CEr t) (◇ B))
eventually-refl M B t t₁ = prove 10

-- Formulas that live under a variable binder (see binder-subst above).
binder-refl : (A B : Form (⟨⟩ ، 𝕍ℝ))
            → ⊢ (seq (ℂe (ℂv ℂ⟨⟩ 𝕍ℝ) (A ∧· B) 𝕣₀) (CEr 𝕣₀) (B ∧· A))
binder-refl A B = prove 10

-- The same rules as above, with the abstraction done by the macro.
◇↓R-refl : (M : Model₀) (Γ : ℂ₀) (t r r₁ : ℂRes Γ) (A : ℂForm Γ)
         → sat-rule M (rule◇↓R Γ t r r₁ A)
◇↓R-refl M Γ t r r₁ A = prove 10

◇R-refl : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
        → sat-rule M (rule◇R Γ r r₁ A)
◇R-refl M Γ r r₁ A = prove 10

ＯR-refl : (M : Model₀) (Γ : ℂ₀) (r r₁ : ℂRes Γ) (A : ℂForm Γ)
         → sat-rule M (ruleＯR Γ r r₁ A)
ＯR-refl M Γ r r₁ A = prove 10

-- Past operators and temporal left rules (see the SUBST section).
nextL-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq ℂ⟨⟩ (CEr t) (Ｏ A →· Ｏ (A ∨· B)))
nextL-refl M A B t = prove 10

untilL-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｕ B) →· ◇ B))
untilL-refl M A B t = prove 10

freezeL-refl : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
             → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((Ｆ (↑₀ A)) →· A))
freezeL-refl M A t = prove 10

prev-refl : (M : Model₀) (A : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
          → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t₁ ◁ t)) A t₁) (CEr t) (Ｙ A))
prev-refl M A t t₁ = prove 10

prevL-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq ℂ⟨⟩ (CEr t) (Ｙ A →· Ｙ (A ∨· B)))
prevL-refl M A B t = prove 10

before-refl : (M : Model₀) (B : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t₁ ⊑ t)) B t₁) (CEr t) (◆ B))
before-refl M B t t₁ = prove 10

sinceL-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｓ B) →· ◆ B))
sinceL-refl M A B t = prove 10

bprevL-refl : (M : Model₀) (A : Form₀) (t t₁ : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq (ℂe (ℂu ℂ⟨⟩ (t₁ ◁ t)) (Ｂ A) t) (CEr t₁) A)
bprevL-refl M A t t₁ = prove 10

bprev-refl : (M : Model₀) (A B : Form₀) (t : ℂRes ℂ⟨⟩)
           → sat-sequent M (seq ℂ⟨⟩ (CEr t) (Ｂ (A ∧· B) →· Ｂ A))
bprev-refl M A B t = prove 10

-- Reasoning about comparisons (see the SUBST section).
cmp-trans-refl : (M : Model₀) (t t₁ t₂ t₃ : ℂRes ℂ⟨⟩)
               → sat-sequent M (seq (ℂu (ℂu (ℂu ℂ⟨⟩ (t₁ ◁ t₂)) (t₂ ⊑ t₃)) (t₃ ⊏ t)) (CEr t) (t₁ ⊏ t))
cmp-trans-refl M t t₁ t₂ t₃ = prove 10

cmp-cong-refl : (M : Model₀) (t t₁ t₂ : ℂRes ℂ⟨⟩)
              → sat-sequent M (seq (ℂu ℂ⟨⟩ (t₂ ＝ t₁)) CEu (t ⋆ t₁ ⊑ t ⋆ t₂))
cmp-cong-refl M t t₁ t₂ = prove 10

cmp-monoid-refl : (M : Model₀) (t t₁ : ℂRes ℂ⟨⟩)
                → sat-sequent M (seq ℂ⟨⟩ (CEr t) (((𝟎 ⋆ t) ⋆ t₁ ＝ t ⋆ t₁) ∧· (t ⋆ t₁ ＝ t₁ ⋆ t) ∧· (𝟎 ⊑ t₁)))
cmp-monoid-refl M t t₁ = prove 10

untilMono-refl : (M : Model₀) (A B D : Form₀) (t : ℂRes ℂ⟨⟩)
               → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｕ B) →· ((A ∨· D) Ｕ B)))
untilMono-refl M A B D t = prove 10

sinceMono-refl : (M : Model₀) (A B D : Form₀) (t : ℂRes ℂ⟨⟩)
               → sat-sequent M (seq ℂ⟨⟩ (CEr t) ((A Ｓ B) →· ((A ∨· D) Ｓ B)))
sinceMono-refl M A B D t = prove 10

inClosed-refl : (M : Model₀) (A : Form₀) (t t₁ t₂ : ℂRes ℂ⟨⟩)
              → sat-sequent M (seq (ℂu (ℂu (ℂi ℂ⟨⟩ A ［ t₁ , t₂ ］) (t₁ ⊑ t)) (t ⊑ t₂)) (CEr t) A)
inClosed-refl M A t t₁ t₂ = prove 10

always-refl : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) (□ (A →· A)))
always-refl M A t = prove 10

eventually-now-refl : (M : Model₀) (A : Form₀) (t : ℂRes ℂ⟨⟩)
                    → sat-sequent M (seq (ℂe ℂ⟨⟩ A t) (CEr t) (◇ A))
eventually-now-refl M A t = prove 10

◇↓R-now-refl : (M : Model₀) (Γ : ℂ₀) (t r : ℂRes Γ) (A : ℂForm Γ)
             → sat-rule M (rule◇↓R-now Γ t r A)
◇↓R-now-refl M Γ t r A = prove 10

◆R-now-refl : (M : Model₀) (Γ : ℂ₀) (r : ℂRes Γ) (A : ℂForm Γ)
            → sat-rule M (rule◆R-now Γ r A)
◆R-now-refl M Γ r A = prove 10

⊑-trans-refl : (M : Model₀) (Γ : ℂ₀) (r₁ r r₂ R : ℂRes Γ)
             → sat-rule M (rule⊑-trans Γ r₁ r r₂ R)
⊑-trans-refl M Γ r₁ r r₂ R = prove 10

＝-⋆-congᵣ-refl : (M : Model₀) (Γ : ℂ₀) (r r₁ r₂ R : ℂRes Γ)
               → sat-rule M (rule＝-⋆-congᵣ Γ r r₁ r₂ R)
＝-⋆-congᵣ-refl M Γ r r₁ r₂ R = prove 10

-- Quantifiers (see the SUBST section).
forall-refl : (M : Model₀) (B : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) (∀· 𝕌Prop (p₀ ∧· ↑₀ B) →· ∀· 𝕌Prop (p₀ ∨· ↑₀ B)))
forall-refl M B t = prove 10

exists-refl : (M : Model₀) (B : Form₀) (t : ℂRes ℂ⟨⟩)
            → sat-sequent M (seq ℂ⟨⟩ (CEr t) (∃· 𝕌Prop (p₀ ∧· ↑₀ B) →· (∃· 𝕌Prop p₀ ∧· B)))
exists-refl M B t = prove 10

forall-exists-refl : (M : Model₀) (t : ℂRes ℂ⟨⟩)
                   → sat-sequent M (seq (ℂe ℂ⟨⟩ (∃· 𝕌Prop p₀) t) (CEr t)
                                        (∀· 𝕌Prop (p₀ →· p₀) →· ∃· 𝕌Prop p₀))
forall-exists-refl M t = prove 10

-- forwarding of Rules.lagda in general (Γ, the agents, the data and the
-- resources are all opaque), i.e. forwarding-true, by the tactic: proveᶜ
-- abstracts the opaque agents and data to placeholder constants, runs
-- search⊢ᶜ, and plugs the derivation back with plug-⊢ₐ, which reproduces the
-- nested weakening ↑ᵣ₁ (↑ᵣ₃ Δ) of the synchrony assumption from the shape
-- [4,2] that the tactic reads off its normal form ("Placeholders and
-- shapes" in SUMMARY.md).
module _ (em : EMT) where
  open import Rules(𝔻)(W)(em) using (forwarding)

  forwarding-auto : (M : Model₀) {Γ : ℂ₀} (a b c : ℂAgent Γ) (Δ r : ℂRes Γ) (p : ℂData Γ)
                → sat-rule M (forwarding Γ a b c Δ r p)
  forwarding-auto M a b c Δ r p = proveᶜ em 5

\end{code}
