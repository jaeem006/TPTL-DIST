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
open import Subst(𝔻)(W) using (𝕣₀ ; ◇↓)
open import Semantics(𝔻)(W)
open import Automation(W)
open import Plug(W)
open import ProveTactic(W)
open import RulesTemp(𝔻)(W) using (rule◇↓R ; rule◇R ; ruleＯR)

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

\end{code}
