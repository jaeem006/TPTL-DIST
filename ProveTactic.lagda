REFLECTION FRONT END to search⊢: the macro `prove n`.

search⊢ (Automation.lagda) compares formulas and time expressions with
decidable equality, which gets stuck on meta-level unknowns, i.e. Agda
variables such as A : Form Γ or r : Res Γ.  `prove n` automates the three
steps of the method (Examples.lagda shows the same steps done by hand):

  1. ABSTRACT.  It reads the goal, one of
       ⊢ s,   sat-sequent M s,   sat-rule M (rule ps s),
     with s = seq Γ T D and every premise in ps of the form seq Γ R H.
     Opaque formulas become formula variables var k and opaque time
     expressions become rvar k (equal unknowns get the same variable).  The
     concrete hypotheses at the end of Γ and the premises ps become the
     hypotheses of a closed context Δ; what remains of Γ is the base Γ₀.
  2. SEARCH.  It runs search⊢ n on the closed sequent Δ ⊢ D′ at T′ by
     normalisation.
  3. INSTANTIATE.  It plugs the derivation found into Γ₀ with plug-⊢
     (Plug.lagda), which puts the unknowns back.  For sat-sequent and
     sat-rule goals it then applies `sound`, and for sat-rule turns the
     hypotheses coming from ps back into premises with hyps→rule.

Nothing here needs to be trusted: Agda typechecks the resulting term against
the original goal.  Opaque labels (an Agda variable T : ℂCE Γ) are not
supported.

\begin{code}
{-# OPTIONS --safe #-}

open import Level using (0ℓ) renaming (suc to lsuc)
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∨_ ; _∧_)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _⊔_ ; _<ᵇ_)
open import Data.List using (List ; _∷_ ; [] ; length ; _++_ ; reverse)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Unit using (⊤ ; tt)
open import Agda.Builtin.Char using (Char ; primCharEquality)
open import Agda.Builtin.String using (primStringToList)

-- Only the builtin reflection API, so that this works with Agda 2.6.3 too.
import Agda.Builtin.Reflection as R
open R using (TC ; Term ; Name ; Arg ; arg)
open import Agda.Builtin.Nat using () renaming (_==_ to _==ℕ_)

open import World
import Syntax as S
import Semantics as Sem
import Plug as P
import Subst as Sb

module ProveTactic (W : World)
       where

open import Decidable(W)
open import Syntax(𝔻)(W)
open import Semantics(𝔻)(W)
open import Subst(𝔻)(W) using (𝕣₀)
open import Automation(W)
open import Plug(W)

private
  _>>=_ : {A B : Set} → TC A → (A → TC B) → TC B
  _>>=_ = R.bindTC

  _>>_ : {A B : Set} → TC A → TC B → TC B
  m >> n = R.bindTC m (λ _ → n)

  _==_ : Name → Name → Bool
  _==_ = R.primQNameEquality

  -- Normalisation may print a constructor through any of the module copies
  -- (Syntax.Form.var, Automation._.var, ...), so constructors are compared
  -- by their unqualified name.
  base : Name → List Char
  base n = go (primStringToList (R.primShowQName n)) []
    where
    go : List Char → List Char → List Char
    go []       acc = reverse acc
    go (c ∷ cs) acc = if primCharEquality c '.' then go cs [] else go cs (c ∷ acc)

  eqChars : List Char → List Char → Bool
  eqChars []       []       = true
  eqChars (c ∷ cs) (d ∷ ds) = primCharEquality c d ∧ eqChars cs ds
  eqChars _        _        = false

  _≈_ : Name → Name → Bool
  x ≈ y = (x == y) ∨ eqChars (base x) (base y)

  -- Conservative syntactic equality on reflected terms: false means "treat as
  -- different atoms", which can only make the search fail, never unsound.
  eqT    : Term → Term → Bool
  eqArgs : List (Arg Term) → List (Arg Term) → Bool
  -- `unknown` (e.g. an omitted module parameter) matches anything.
  eqT R.unknown _ = true
  eqT _ R.unknown = true
  eqT (R.var x xs) (R.var y ys) = (x ==ℕ y) ∧ eqArgs xs ys
  eqT (R.con c xs) (R.con d ys) = (c == d) ∧ eqArgs xs ys
  eqT (R.def f xs) (R.def g ys) = (f == g) ∧ eqArgs xs ys
  eqT (R.lit (R.nat m)) (R.lit (R.nat n)) = m ==ℕ n
  eqT (R.lit (R.name m)) (R.lit (R.name n)) = m == n
  eqT _ _ = false
  -- Hidden arguments (object-level contexts) are ignored: the same term may
  -- show them in different but convertible forms, e.g. ℂtxt (ℂv ℂ⟨⟩ 𝕍ℝ) and
  -- ⟨⟩ ، 𝕍ℝ.  Identifying two terms wrongly can only make the final type
  -- check fail.
  eqArgs []                                    []       = true
  eqArgs (arg (R.arg-info R.visible _) x ∷ xs) (arg (R.arg-info R.visible _) y ∷ ys) =
    eqT x y ∧ eqArgs xs ys
  eqArgs (arg (R.arg-info R.hidden _) _ ∷ xs)   ys       = eqArgs xs ys
  eqArgs (arg (R.arg-info R.instance′ _) _ ∷ xs) ys      = eqArgs xs ys
  eqArgs xs (arg (R.arg-info R.hidden _) _ ∷ ys)         = eqArgs xs ys
  eqArgs xs (arg (R.arg-info R.instance′ _) _ ∷ ys)      = eqArgs xs ys
  eqArgs _                                     _        = false

  varName : Name
  varName = quote S.var

  Atoms : Set
  Atoms = List Term

  mkVar : ℕ → Term
  mkVar k = R.con varName (arg (R.arg-info R.hidden (R.modality R.relevant R.quantity-ω)) R.unknown
                              ∷ arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) (R.lit (R.nat k)) ∷ [])

  index : Term → Atoms → Maybe ℕ
  index t []       = nothing
  index t (u ∷ us) with eqT t u | index t us
  ... | true  | _        = just 0
  ... | false | just i   = just (suc i)
  ... | false | nothing  = nothing

  isVis : Arg Term → Bool
  isVis (arg (R.arg-info R.visible _) _) = true
  isVis _                                = false

  -- Largest formula-variable literal occurring in a term, plus one.
  maxLit : List (Arg Term) → ℕ
  maxLit []                               = 0
  maxLit (arg _ (R.lit (R.nat k)) ∷ args) = suc k ⊔ maxLit args
  maxLit (_ ∷ args)                       = maxLit args

  freshVar     : Term → ℕ
  freshVarArgs : List (Arg Term) → ℕ
  freshVar (R.con c args) = (if c ≈ varName then maxLit args else 0) ⊔ freshVarArgs args
  freshVar (R.def f args) = freshVarArgs args
  freshVar (R.var x args) = freshVarArgs args
  freshVar _              = 0
  freshVarArgs []               = 0
  freshVarArgs (arg _ t ∷ args) = freshVar t ⊔ freshVarArgs args

  lastVis : List (Arg Term) → List Term
  lastVis args = go (reverse args)
    where
    go : List (Arg Term) → List Term
    go []                                     = []
    go (arg (R.arg-info R.visible _) t ∷ as) = t ∷ go as
    go (_ ∷ as)                               = go as

  hArg : Term → Arg Term
  hArg = arg (R.arg-info R.hidden (R.modality R.relevant R.quantity-ω))

  vArg : Term → Arg Term
  vArg = arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω))

  -- Apply a quoted function to more arguments.
  _·_ : Term → List (Arg Term) → Term
  R.def f xs · ys = R.def f (xs ++ ys)
  R.con c xs · ys = R.con c (xs ++ ys)
  R.var x xs · ys = R.var x (xs ++ ys)
  t          · ys = t

private
  -- -------------------------------------------------------------------------
  -- Abstraction of opaque formulas and resources.
  --
  -- Opaque formulas become var k and opaque resources rvar k.  The
  -- abstracted goal lives in the empty variable context, so every hidden
  -- argument (the object-level context) is replaced by `unknown` and
  -- re-elaborated.  Under an object-level binder only ↑₀ X / ↑ᵣ₀ X (depth 1)
  -- and ↑₁ X / ↑ᵣ₁ X (depth 2) are abstracted, because these are exactly what
  -- plug-⊢ produces when instantiating a variable at that depth.  Anything
  -- else is left alone; if that makes the abstract goal ill-typed or the
  -- search fail, the macro reports an error.

  St : Set
  St = Atoms × Atoms   -- opaque formulas, opaque resources

  unk : Arg Term → Arg Term
  unk (arg i@(R.arg-info R.visible _) t) = arg i t
  unk (arg i t)                           = arg i R.unknown

  mkRVar : ℕ → Term
  mkRVar k = R.con (quote S.rvar) (arg (R.arg-info R.hidden (R.modality R.relevant R.quantity-ω)) R.unknown
                                   ∷ arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) (R.lit (R.nat k)) ∷ [])

  atomF : ℕ → St → Term → St × Term
  atomF b (fs , rs) t with index t fs
  ... | just i  = (fs , rs) , mkVar (b + i)
  ... | nothing = (fs ++ (t ∷ []) , rs) , mkVar (b + length fs)

  atomR : ℕ → St → Term → St × Term
  atomR b (fs , rs) t with index t rs
  ... | just i  = (fs , rs) , mkRVar (b + i)
  ... | nothing = (fs , rs ++ (t ∷ [])) , mkRVar (b + length rs)

  data Kind : Set where
    kF kR kN kO : Kind

  cls : Term → Kind
  cls (R.def f _) =
    if f ≈ quote S.Form then kF
    else if f ≈ quote S.Res then kR
    else if (f ≈ quote Sem.CE) ∨ (f ≈ quote Sem.Interval) then kN
    else kO
  cls _ = kO

  kindOf : Term → TC Kind
  -- speculative: inferType elaborates t, and e.g. a bare 𝟎 has an
  -- unsolvable implicit context
  kindOf t = R.runSpeculative
               (R.catchTC (R.inferType t >>= λ ty → R.normalise ty >>= λ ty → R.returnTC (cls ty , false))
                          (R.returnTC (kO , false)))

  ret : {A : Set} → A → TC A
  ret = R.returnTC

  anyFR : List Kind → Bool
  anyFR []        = false
  anyFR (kF ∷ ks) = true
  anyFR (kR ∷ ks) = true
  anyFR (_  ∷ ks) = anyFR ks

  kinds : List (Arg Term) → TC (List Kind)
  kinds []                 = ret []
  kinds (arg i t ∷ args)   = kindOf t >>= λ k → kinds args >>= λ ks → ret (k ∷ ks)

  depthOf : Name → ℕ
  depthOf f = if (f ≈ quote Sb.↑₀) ∨ (f ≈ quote Sb.↑ᵣ₀) then 1
              else if (f ≈ quote Sb.↑₁) ∨ (f ≈ quote Sb.↑ᵣ₁) then 2 else 0

  -- depth 0
  absF0  : ℕ → St → Term → TC (St × Term)
  absR0  : ℕ → St → Term → TC (St × Term)
  absN0  : ℕ → St → Term → TC (St × Term)
  absK0  : ℕ → Kind → St → Term → TC (St × Term)
  absVis : ℕ → St → List (Arg Term) → TC (St × List (Arg Term))
  -- under d object-level binders
  absU   : ℕ → ℕ → St → Term → TC (St × Term)
  absUR  : ℕ → ℕ → St → Term → TC (St × Term)
  absUVis : ℕ → ℕ → St → List (Arg Term) → TC (St × List (Arg Term))
  absUK  : ℕ → ℕ → Kind → St → Term → TC (St × Term)

  absK0 b kF st t = absF0 b st t
  absK0 b kR st t = absR0 b st t
  absK0 b kN st t = absN0 b st t
  absK0 b kO st t = ret (st , t)

  absVis b st [] = ret (st , [])
  absVis b st (a@(arg i t) ∷ args) with isVis a
  ... | false = absVis b st args >>= λ { (st′ , args′) → ret (st′ , unk a ∷ args′) }
  ... | true  = kindOf t >>= λ k → absK0 b k st t >>= λ { (st₁ , t′) →
                absVis b st₁ args >>= λ { (st₂ , args′) → ret (st₂ , arg i t′ ∷ args′) } }

  absN0 b st (R.con c args) = absVis b st args >>= λ { (st′ , args′) → ret (st′ , R.con c args′) }
  absN0 b st t = R.typeError (R.strErr "prove: opaque labels (CE) are not supported:" ∷ R.termErr t ∷ [])

  absF0 b st t@(R.con c args) =
    if (c ≈ quote S.Ｆ_) ∨ (c ≈ quote S.∀·) ∨ (c ≈ quote S.∃·)
      then absUVis b 1 st args >>= (λ { (st′ , args′) → ret (st′ , R.con c args′) })
    else if (c ≈ quote S.𝕒) ∨ (c ≈ quote S.𝔸)
      then ret (atomF b st t)
    else absVis b st args >>= (λ { (st′ , args′) → ret (st′ , R.con c args′) })
  absF0 b st t@(R.def f args) =
    kinds args >>= λ ks →
    if anyFR ks
      then absVis b st args >>= (λ { (st′ , args′) → ret (st′ , R.def f args′) })
      else ret (atomF b st t)
  absF0 b st t = ret (atomF b st t)

  absR0 b st t@(R.con c args) =
    if c ≈ quote S.𝐯 then ret (atomR b st t)
    else absVis b st args >>= (λ { (st′ , args′) → ret (st′ , R.con c args′) })
  absR0 b st t = ret (atomR b st t)

  absUVis b d st [] = ret (st , [])
  absUVis b d st (a@(arg i t) ∷ args) with isVis a
  ... | false = absUVis b d st args >>= λ { (st′ , args′) → ret (st′ , unk a ∷ args′) }
  ... | true  = kindOf t >>= λ k → absUK b d k st t >>= λ { (st₁ , t′) →
                absUVis b d st₁ args >>= λ { (st₂ , args′) → ret (st₂ , arg i t′ ∷ args′) } }

  absUK b d kF st t = absU b d st t
  absUK b d kR st t = absUR b d st t
  absUK b d kN st (R.con c as) = absUVis b d st as >>= λ { (st′ , as′) → ret (st′ , R.con c as′) }
  absUK b d kN st t = ret (st , t)
  absUK b d kO st t = ret (st , t)

  absU b d st t@(R.con c args) =
    if (c ≈ quote S.Ｆ_) ∨ (c ≈ quote S.∀·) ∨ (c ≈ quote S.∃·)
      then absUVis b (suc d) st args >>= (λ { (st′ , args′) → ret (st′ , R.con c args′) })
    else absUVis b d st args >>= (λ { (st′ , args′) → ret (st′ , R.con c args′) })
  absU b d st t@(R.def f args) with depthOf f ==ℕ d | lastVis args
  ... | true  | (X ∷ _) = ret (atomF b st X)
  ... | _     | _       = absUVis b d st args >>= (λ { (st′ , args′) → ret (st′ , R.def f args′) })
  absU b d st t = ret (st , t)

  absUR b d st t@(R.con c args) =
    absUVis b d st args >>= (λ { (st′ , args′) → ret (st′ , R.con c args′) })
  absUR b d st t@(R.def f args) with depthOf f ==ℕ d | lastVis args
  ... | true  | (X ∷ _) = ret (atomR b st X)
  ... | _     | _       = ret (st , t)
  absUR b d st t = ret (st , t)

  -- reflected lists and pairs
  mkList : List Term → Term
  mkList []       = R.con (quote Data.List.List.[]) []
  mkList (t ∷ ts) = R.con (quote Data.List.List._∷_) (vArg t ∷ vArg (mkList ts) ∷ [])

  mkPair : Term → Term → Term
  mkPair a b = R.con (quote Data.Product._,_) (vArg a ∷ vArg b ∷ [])

  mkσ : ℕ → ℕ → List Term → Term
  mkσ b i []       = R.con (quote Sem.●) []
  mkσ b i (t ∷ ts) = R.con (quote Sem._↦_⨾_) (vArg (R.lit (R.nat (b + i))) ∷ vArg t ∷ vArg (mkσ b (suc i) ts) ∷ [])

  mkρ : ℕ → ℕ → List Term → Term
  mkρ b i []       = R.con (quote P.●ᵣ) []
  mkρ b i (t ∷ ts) = R.con (quote P._↦ᵣ_⨾_) (vArg (R.lit (R.nat (b + i))) ∷ vArg t ∷ vArg (mkρ b (suc i) ts) ∷ [])

  -- the premises of a rule, as (Γ , T , C) triples
  conArgs : Term → List (Arg Term)
  conArgs (R.con _ args) = args
  conArgs _              = []

  listElems : ℕ → Term → TC (List Term)
  listElemsV : ℕ → List Term → TC (List Term)
  listElems zero    t = R.typeError (R.strErr "prove: too many premises" ∷ [])
  -- R.reduce elaborates its argument, which would leave unsolvable metas
  -- for the parameters of a bare [] : only reduce what is not a constructor.
  listElems (suc k) t@(R.con _ args) = listElemsV k (lastVis args)
  listElems (suc k) t = R.reduce t >>= λ t′ → listElemsV k (lastVis (conArgs t′))
  listElemsV k (tl ∷ hd ∷ _) = listElems k tl >>= λ ts → ret (hd ∷ ts)
  listElemsV k _             = ret []

  seqParts : Term → TC (Term × Term × Term)
  seqParts t@(R.con c args) with lastVis args
  ... | (C ∷ T ∷ Γ ∷ _) = ret (Γ , T , C)
  ... | _ = R.typeError (R.strErr "prove: expected seq Γ T C, got" ∷ R.termErr t ∷ [])
  seqParts t = R.reduce t >>= λ
    { (R.con c args) → parts (lastVis args)
    ; t′ → R.typeError (R.strErr "prove: expected seq Γ T C, got" ∷ R.termErr t′ ∷ []) }
    where
    parts : List Term → TC (Term × Term × Term)
    parts (C ∷ T ∷ Γ ∷ _) = ret (Γ , T , C)
    parts _ = R.typeError (R.strErr "prove: expected seq Γ T C, got" ∷ R.termErr t ∷ [])

  absPrems : ℕ → St → List Term → TC (St × List Term × List Term)
  absPrems b st [] = ret (st , [] , [])
  absPrems b st (p ∷ ps) =
    seqParts p >>= λ { (Γ , T , C) →
    absN0 b st T >>= λ { (st₁ , T′) →
    absF0 b st₁ C >>= λ { (st₂ , C′) →
    absPrems b st₂ ps >>= λ { (st₃ , real , abst) →
    ret (st₃ , mkPair T C ∷ real , mkPair T′ C′ ∷ abst) } } } }

  -- Largest rvar literal in a term, plus one.
  freshRVar     : Term → ℕ
  freshRVarArgs : List (Arg Term) → ℕ
  freshRVar (R.con c args) = (if c ≈ quote S.rvar then maxLit args else 0) ⊔ freshRVarArgs args
  freshRVar (R.def f args) = freshRVarArgs args
  freshRVar (R.var x args) = freshRVarArgs args
  freshRVar _              = 0
  freshRVarArgs []               = 0
  freshRVarArgs (arg _ t ∷ args) = freshRVar t ⊔ freshRVarArgs args

  -- Split a context into an opaque (or binder-ending) base and the concrete
  -- hypotheses on top of it, innermost first.
  peelCtx : ℕ → Term → TC (Term × List Term)
  -- R.reduce would elaborate the term and leave unsolvable metas for its
  -- omitted module parameters, so ℂe / ℂu are unfolded by hand.
  peelCtx zero    Γ = ret (Γ , [])
  peelCtx (suc k) Γ@(R.con c args) with lastVis args
  ... | (a ∷ f ∷ c′ ∷ _) = if c ≈ quote Sem.ℂx then push c′ a f else ret (Γ , [])
    where push : Term → Term → Term → TC (Term × List Term)
          push c′ a f = peelCtx k c′ >>= λ { (base , hs) → ret (base , hs ++ (mkPair a f ∷ [])) }
  ... | _ = ret (Γ , [])
  -- (the module parameters 𝔻 and W come first, so lastVis lists the
  -- visible arguments as  r f c …  for ℂe c f r  and  f c …  for ℂu c f)
  peelCtx (suc k) Γ@(R.def g args) with lastVis args
  ... | (x ∷ y ∷ z ∷ _) =
    if g ≈ quote Sem.ℂe then push z (R.con (quote Sem.CEr) (vArg x ∷ [])) y
    else if g ≈ quote Sem.ℂu then push y (R.con (quote Sem.CEu) []) x
    else ret (Γ , [])
    where push : Term → Term → Term → TC (Term × List Term)
          push c′ a f = peelCtx k c′ >>= λ { (base , hs) → ret (base , hs ++ (mkPair a f ∷ [])) }
  ... | _ = ret (Γ , [])
  peelCtx (suc k) Γ = ret (Γ , [])

  pairParts : Term → Term × Term
  pairParts (R.con _ args) with lastVis args
  ... | (b ∷ a ∷ _) = a , b
  ... | _           = R.unknown , R.unknown
  pairParts t = R.unknown , R.unknown

  absPairs : ℕ → St → List Term → TC (St × List Term)
  absPairs b st [] = ret (st , [])
  absPairs b st (p ∷ ps) with pairParts p
  ... | (T , C) =
    absN0 b st T >>= λ { (st₁ , T′) →
    absF0 b st₁ C >>= λ { (st₂ , C′) →
    absPairs b st₂ ps >>= λ { (st₃ , abst) →
    ret (st₃ , mkPair T′ C′ ∷ abst) } } }

  -- The common core.  Given a sequent  seq Γ T D  and premises (all over Γ),
  -- abstract everything, run the search, and return
  --   * the plugged derivation  plug-⊢ Γ₀ σ ρ d,
  --     of type ⊢ (seq (addHyps Γ prems) T D) up to computation, where Γ₀ is
  --     Γ without its concrete hypotheses, and
  --   * the premises as (T , C) pairs, for hyps→rule.
  proveCore : ℕ → Term → Term → Term → Term → List Term → TC (Term × List Term)
  proveCore n goal Γ T D prems = do
    (Γ₀ , ctxHyps) ← peelCtx 1000 Γ
    let b = freshVar goal ⊔ freshRVar goal
    (st₀ , absCtx) ← absPairs b ([] , []) ctxHyps
    (st₁ , real , abst) ← absPrems b st₀ prems
    (st₂ , T′) ← absN0 b st₁ T
    ((fs , rs) , D′) ← absF0 b st₂ D
    addH ← R.quoteTC addHyps
    dec  ← R.quoteTC search⊢
    let Δ = addH · (vArg (R.con (quote Sem.ℂ⟨⟩) []) ∷ vArg (mkList (absCtx ++ abst)) ∷ [])
    d ← R.runSpeculative (search′ Δ T′ D′ dec)
    pl  ← R.quoteTC plug-⊢
    ret (pl · (vArg Γ₀ ∷ vArg (mkσ b 0 fs) ∷ vArg (mkρ b 0 rs) ∷ hArg Δ ∷ hArg T′ ∷ hArg D′ ∷ vArg d ∷ [])
        , real)
    where
    -- run speculatively: the metas created while elaborating the abstract
    -- sequent are discarded; the normal form d does not mention them
    search′ : Term → Term → Term → Term → TC (Σ Term (λ _ → Bool))
    search′ Δ T′ D′ dec = do
     q ← R.catchTC (R.checkType (dec · (vArg (R.lit (R.nat n)) ∷ vArg Δ ∷ vArg T′ ∷ vArg D′ ∷ [])) R.unknown)
                   (R.typeError (R.strErr "prove: the abstracted goal is ill-typed:"
                                 ∷ R.termErr Δ ∷ R.strErr "⊢" ∷ R.termErr D′ ∷ []))
     r ← R.normalise q
     R.con _ jargs ← ret r
       where _ → R.typeError (R.strErr "prove: search got stuck:" ∷ R.termErr r ∷ [])
     (d ∷ _) ← ret (lastVis jargs)
       where _ → R.typeError (R.strErr "prove: no derivation found with fuel"
                                      ∷ R.termErr (R.lit (R.nat n)) ∷ [])
     ret (d , false)

  -- Goals  ⊢ s,  sat-sequent M s  and  sat-rule M (rule ps s).
  proveGoal : ℕ → Term → TC Term
  proveGoal n ty = do
    R.def f args ← ret ty
      where _ → R.typeError (R.strErr "prove: unsupported goal" ∷ R.termErr ty ∷ [])
    go f (lastVis args)
    where
    go : Name → List Term → TC Term
    go f (s ∷ rest) =
      if f ≈ quote ⊢ then
        (seqParts s >>= λ { (Γ , T , D) →
         proveCore n ty Γ T D [] >>= λ { (pd , _) → ret pd } })
      else if f ≈ quote sat-sequent then
        (withM rest λ M →
         seqParts s >>= λ { (Γ , T , D) →
         proveCore n ty Γ T D [] >>= λ { (pd , _) →
         R.quoteTC sound >>= λ snd →
         ret (snd · (vArg M ∷ hArg R.unknown ∷ vArg pd ∷ [])) } })
      else if f ≈ quote sat-rule then
        (withM rest λ M →
         R.reduce s >>= λ ρ → ruleParts ρ >>= λ { (c , ps) →
         listElems 1000 ps >>= λ prems →
         seqParts c >>= λ { (Γ , T , D) →
         proveCore n ty Γ T D prems >>= λ { (pd , real) →
         R.quoteTC sound >>= λ snd →
         R.quoteTC hyps→rule >>= λ hr →
         ret (hr · (vArg M ∷ vArg Γ ∷ vArg (mkList real) ∷ vArg T ∷ vArg D
                    ∷ vArg (snd · (vArg M ∷ hArg R.unknown ∷ vArg pd ∷ [])) ∷ [])) } } })
      else R.typeError (R.strErr "prove: unsupported goal" ∷ R.termErr ty ∷ [])
      where
      withM : List Term → (Term → TC Term) → TC Term
      withM (M ∷ _) k = k M
      withM []      k = R.typeError (R.strErr "prove: unsupported goal" ∷ R.termErr ty ∷ [])
      ruleParts : Term → TC (Term × Term)
      ruleParts (R.con _ rargs) with lastVis rargs
      ... | (c ∷ ps ∷ _) = ret (c , ps)
      ... | _ = R.typeError (R.strErr "prove: expected rule ps c" ∷ R.termErr ty ∷ [])
      ruleParts t = R.typeError (R.strErr "prove: expected rule ps c" ∷ R.termErr t ∷ [])
    go f [] = R.typeError (R.strErr "prove: unsupported goal" ∷ R.termErr ty ∷ [])

macro
  -- Works on goals  ⊢ s,  sat-sequent M s  and  sat-rule M (rule ps s),  where
  -- s = seq Γ T C and every premise in ps has the form  seq Γ R H  for the
  -- same Γ.  Γ, the formulas and the resources may be opaque (Agda
  -- variables); concrete hypotheses at the end of Γ are abstracted too.
  prove : ℕ → Term → TC ⊤
  prove n hole = do
    ty ← R.inferType hole
    t ← proveGoal n ty
    R.unify hole t

\end{code}
