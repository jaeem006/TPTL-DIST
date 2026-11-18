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
     (Plug.lagda), which puts the unknowns back.  The derivation is passed
     as  from-just (search⊢ n Δ T′ D′), as in the hand-written proofs, and
     not as its quoted normal form, which Agda would have to type-check
     again rule by rule.  For sat-sequent and
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
open import Data.List using (List ; _∷_ ; [] ; length ; _++_ ; reverse ; map)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Maybe using (Maybe ; just ; nothing ; from-just ; is-just)
open import Agda.Builtin.Equality using (_≡_ ; refl)
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
open import Automation W
open import Plug W

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

  freshLit     : Name → Term → ℕ
  freshLitArgs : Name → List (Arg Term) → ℕ
  freshLit nm (R.con c args) = (if c ≈ nm then maxLit args else 0) ⊔ freshLitArgs nm args
  freshLit nm (R.def f args) = freshLitArgs nm args
  freshLit nm (R.var x args) = freshLitArgs nm args
  freshLit nm _              = 0
  freshLitArgs nm []               = 0
  freshLitArgs nm (arg _ t ∷ args) = freshLit nm t ⊔ freshLitArgs nm args

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
  St = Atoms × Atoms × Atoms × Atoms   -- opaque formulas, resources, agents, data

  -- dp: also abstract opaque agents and data (to placeholder constants
  -- agentC / dataC numbered from bA / bD); bF: first variable number.
  record Cfg : Set where
    constructor cfg
    field
      dp : Bool
      bF bA bD : ℕ
  open Cfg

  unk : Arg Term → Arg Term
  unk (arg i@(R.arg-info R.visible _) t) = arg i t
  unk (arg i t)                           = arg i R.unknown

  mkRVar : ℕ → Term
  mkRVar k = R.con (quote S.rvar) (arg (R.arg-info R.hidden (R.modality R.relevant R.quantity-ω)) R.unknown
                                   ∷ arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) (R.lit (R.nat k)) ∷ [])

  mkCon1 : Name → ℕ → Term
  mkCon1 c k = R.con c (arg (R.arg-info R.hidden (R.modality R.relevant R.quantity-ω)) R.unknown
                        ∷ arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) (R.lit (R.nat k)) ∷ [])

  atomF : Cfg → St → Term → St × Term
  atomF c (fs , rs , as , ds) t with index t fs
  ... | just i  = (fs , rs , as , ds) , mkVar (bF c + i)
  ... | nothing = (fs ++ (t ∷ []) , rs , as , ds) , mkVar (bF c + length fs)

  atomR : Cfg → St → Term → St × Term
  atomR c (fs , rs , as , ds) t with index t rs
  ... | just i  = (fs , rs , as , ds) , mkRVar (bF c + i)
  ... | nothing = (fs , rs ++ (t ∷ []) , as , ds) , mkRVar (bF c + length rs)

  atomA : Cfg → St → Term → St × Term
  atomA c (fs , rs , as , ds) t with index t as
  ... | just i  = (fs , rs , as , ds) , mkCon1 (quote S.agentC) (bA c + i)
  ... | nothing = (fs , rs , as ++ (t ∷ []) , ds) , mkCon1 (quote S.agentC) (bA c + length as)

  atomD : Cfg → St → Term → St × Term
  atomD c (fs , rs , as , ds) t with index t ds
  ... | just i  = (fs , rs , as , ds) , mkCon1 (quote S.dataC) (bD c + i)
  ... | nothing = (fs , rs , as , ds ++ (t ∷ [])) , mkCon1 (quote S.dataC) (bD c + length ds)

  data Kind : Set where
    kF kR kN kO kA kAs kD : Kind

  cls : Term → Kind
  cls (R.def f _) =
    if f ≈ quote S.Form then kF
    else if f ≈ quote S.Res then kR
    else if (f ≈ quote Sem.CE) ∨ (f ≈ quote Sem.Interval) then kN
    else if f ≈ quote S.Agent then kA
    else if f ≈ quote S.Agents then kAs
    else if f ≈ quote S.Data then kD
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

  anyFR : Cfg → List Kind → Bool
  anyFR c []         = false
  anyFR c (kF ∷ ks)  = true
  anyFR c (kR ∷ ks)  = true
  anyFR c (kA ∷ ks)  = dp c ∨ anyFR c ks
  anyFR c (kAs ∷ ks) = dp c ∨ anyFR c ks
  anyFR c (kD ∷ ks)  = dp c ∨ anyFR c ks
  anyFR c (_  ∷ ks)  = anyFR c ks

  -- With dp, a hidden argument is kept when its type is a defined type other
  -- than Ctxt, e.g. the module parameter EM of a constructor copied by a
  -- module application (Rules._._⋆_), which nothing else determines.
  -- Object-level contexts (and sorts, e.g. the type of a list) are
  -- re-elaborated, as without dp.
  keepHidden : Term → TC Bool
  keepHidden t = R.runSpeculative
    (R.catchTC (R.inferType t >>= λ ty → R.normalise ty >>= λ ty →
                R.returnTC (isDefNotCtxt ty , false))
               (R.returnTC (false , false)))
    where
    isDefNotCtxt : Term → Bool
    isKO : Kind → Bool
    isKO kO = true
    isKO _  = false
    isDefNotCtxt ty@(R.def f _) = if f ≈ quote S.Ctxt then false else isKO (cls ty)
    isDefNotCtxt _           = false

  unkM : Cfg → Arg Term → TC (Arg Term)
  unkM c a@(arg (R.arg-info R.visible _) _) = ret a
  unkM c a@(arg i t) =
    if dp c then (keepHidden t >>= λ k → ret (if k then a else unk a)) else ret (unk a)

  kinds : List (Arg Term) → TC (List Kind)
  kinds []                 = ret []
  kinds (arg i t ∷ args)   = kindOf t >>= λ k → kinds args >>= λ ks → ret (k ∷ ks)

  depthOf : Name → ℕ
  depthOf f = if (f ≈ quote Sb.↑₀) ∨ (f ≈ quote Sb.↑ᵣ₀) then 1
              else if (f ≈ quote Sb.↑₁) ∨ (f ≈ quote Sb.↑ᵣ₁) then 2 else 0

  -- depth 0
  absF0  : Cfg → St → Term → TC (St × Term)
  absR0  : Cfg → St → Term → TC (St × Term)
  absN0  : Cfg → St → Term → TC (St × Term)
  absK0  : Cfg → Kind → St → Term → TC (St × Term)
  absVis : Cfg → St → List (Arg Term) → TC (St × List (Arg Term))
  absA0 : Cfg → St → Term → TC (St × Term)
  absD0 : Cfg → St → Term → TC (St × Term)
  absLA : ℕ → Cfg → St → Term → TC (St × Term)
  absAs0 : Cfg → St → Term → TC (St × Term)
  -- under d object-level binders
  absU   : Cfg → ℕ → St → Term → TC (St × Term)
  absUR  : Cfg → ℕ → St → Term → TC (St × Term)
  absUVis : Cfg → ℕ → St → List (Arg Term) → TC (St × List (Arg Term))
  absUK  : Cfg → ℕ → Kind → St → Term → TC (St × Term)

  absK0 b kF st t = absF0 b st t
  absK0 b kR st t = absR0 b st t
  absK0 b kN st t = absN0 b st t
  absK0 b kO st t = ret (st , t)
  absK0 b kA st t = if dp b then absA0 b st t else ret (st , t)
  absK0 b kD st t = if dp b then absD0 b st t else ret (st , t)
  absK0 b kAs st t = if dp b then absAs0 b st t else ret (st , t)

  -- opaque agents and data (only at depth 0)
  absA0 b st t@(R.con k _) = if k ≈ quote S.agentC then ret (st , t) else ret (atomA b st t)
  absA0 b st t = ret (atomA b st t)

  absD0 b st t@(R.con k _) = if k ≈ quote S.dataC then ret (st , t) else ret (atomD b st t)
  absD0 b st t = ret (atomD b st t)

  -- a list of agents, given by _∷_ and []
  absLA zero    b st t = ret (st , t)
  absLA (suc n) b st t@(R.con k args) with lastVis args
  ... | (xs ∷ x ∷ _) =
    if k ≈ quote Data.List.List._∷_
      then (absA0 b st x >>= λ { (st₁ , x′) → absLA n b st₁ xs >>= λ { (st₂ , xs′) →
            ret (st₂ , R.con k (hArg R.unknown ∷ hArg R.unknown ∷ vArg x′ ∷ vArg xs′ ∷ [])) } })
      else ret (st , t)
  ... | _ = ret (st , R.con k (map unk args))
  absLA (suc n) b st t = ret (st , t)

  absAs0 b st t@(R.con k args) with lastVis args
  ... | (l ∷ _) = if k ≈ quote S.agentsL
                    then (absLA 1000 b st l >>= λ { (st′ , l′) → ret (st′ , R.con k (hArg R.unknown ∷ vArg l′ ∷ [])) })
                    else ret (st , t)
  ... | _ = ret (st , t)
  absAs0 b st t@(R.def f args) = absVis b st args >>= λ { (st′ , args′) → ret (st′ , R.def f args′) }
  absAs0 b st t = ret (st , t)

  absVis b st [] = ret (st , [])
  absVis b st (a@(arg i t) ∷ args) with isVis a
  ... | false = unkM b a >>= λ a′ → absVis b st args >>= λ { (st′ , args′) → ret (st′ , a′ ∷ args′) }
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
    if anyFR b ks
      then absVis b st args >>= (λ { (st′ , args′) → ret (st′ , R.def f args′) })
      else ret (atomF b st t)
  absF0 b st t = ret (atomF b st t)

  absR0 b st t@(R.con c args) =
    if c ≈ quote S.𝐯 then ret (atomR b st t)
    else absVis b st args >>= (λ { (st′ , args′) → ret (st′ , R.con c args′) })
  absR0 b st t = ret (atomR b st t)

  absUVis b d st [] = ret (st , [])
  absUVis b d st (a@(arg i t) ∷ args) with isVis a
  ... | false = unkM b a >>= λ a′ → absUVis b d st args >>= λ { (st′ , args′) → ret (st′ , a′ ∷ args′) }
  ... | true  = kindOf t >>= λ k → absUK b d k st t >>= λ { (st₁ , t′) →
                absUVis b d st₁ args >>= λ { (st₂ , args′) → ret (st₂ , arg i t′ ∷ args′) } }

  absUK b d kF st t = absU b d st t
  absUK b d kR st t = absUR b d st t
  absUK b d kN st (R.con c as) = absUVis b d st as >>= λ { (st′ , as′) → ret (st′ , R.con c as′) }
  absUK b d kN st t = ret (st , t)
  absUK b d _  st t = ret (st , t)

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

  -- ---------------------------------------------------------------------------
  -- Shapes (see Plug.lagda): nested weakenings  ↑ e₂ (↑ e₁ X)  of an opaque
  -- X, found in the normal forms of the formulas, innermost segment first.

  data Tag : Set where
    tR tA tD : Tag

  eqTag : Tag → Tag → Bool
  eqTag tR tR = true
  eqTag tA tA = true
  eqTag tD tD = true
  eqTag _  _  = false

  ShE : Set
  ShE = Tag × Term × List ℕ

  upTag : Name → Maybe Tag
  upTag f = if f ≈ quote Sb.↑ᵣ then just tR
            else if f ≈ quote Sb.↑ᵢ then just tA
            else if f ≈ quote Sb.↑d then just tD
            else nothing

  -- number of ∈CtxtS steps of a weakening  Γ ⊆ Γ ، u₁ … ، uₙ
  cntS : ℕ → Term → Maybe ℕ
  cntS zero    t = nothing
  cntS (suc n) (R.var _ []) = just 0
  cntS (suc n) (R.con c args) with lastVis args
  ... | (i ∷ _) = if c ≈ quote S.∈CtxtS then sucM (cntS n i) else nothing
    where sucM : Maybe ℕ → Maybe ℕ
          sucM (just k) = just (suc k)
          sucM nothing  = nothing
  ... | _ = nothing
  cntS (suc n) t = nothing

  lenSub : Term → Maybe ℕ
  lenSub (R.lam _ (R.abs _ t)) = lenSub t
  lenSub (R.def f _) =
    if f ≈ quote Sb.⊆₀ then just 1 else if f ≈ quote Sb.⊆₁ then just 2
    else if f ≈ quote Sb.⊆₂ then just 3 else if f ≈ quote Sb.⊆₃ then just 4
    else if f ≈ quote Sb.⊆₄ then just 5 else nothing
  lenSub t = cntS 1000 t

  chain : ℕ → Tag → Term → Term × List ℕ × Bool
  chain zero    tg t = t , [] , false
  chain (suc n) tg t@(R.def f args) with upTag f | lastVis args
  ... | just tg′ | (X ∷ e ∷ _) = if eqTag tg tg′ then add (lenSub e) (chain n tg X) else (t , [] , true)
    where add : Maybe ℕ → Term × List ℕ × Bool → Term × List ℕ × Bool
          add (just k) (x , ss , ok) = x , ss ++ (k ∷ []) , ok
          add nothing  (x , ss , ok) = x , ss , false
  ... | _ | _ = t , [] , true
  chain (suc n) tg t = t , [] , true

  scan     : Term → List ShE
  scanArgs : List (Arg Term) → List ShE
  scan t@(R.def f args) with upTag f
  ... | just tg = entry tg (chain 1000 tg t)
    where entry : Tag → Term × List ℕ × Bool → List ShE
          entry tg (x , ss@(_ ∷ _ ∷ _) , true) = (tg , x , ss) ∷ []
          entry tg _ = []
  ... | nothing = scanArgs args
  scan (R.con c args) = scanArgs args
  scan (R.var x args) = scanArgs args
  scan _ = []
  scanArgs [] = []
  scanArgs (arg (R.arg-info R.visible _) t ∷ as) = scan t ++ scanArgs as
  scanArgs (_ ∷ as) = scanArgs as

  shapesOf : Tag → Term → List ShE → List (List ℕ)
  shapesOf tg x [] = []
  shapesOf tg x ((tg′ , y , ss) ∷ es) =
    if eqTag tg tg′ ∧ eqT x y then ss ∷ shapesOf tg x es else shapesOf tg x es

  natT : ℕ → Term
  natT k = R.lit (R.nat k)

  mkShapes : List (List ℕ) → Term
  mkShapes sss = mkList (map (λ ss → mkList (map natT ss)) sss)

  isNil : {A : Set} → List A → Bool
  isNil [] = true
  isNil _  = false

  mkρs : List ShE → ℕ → ℕ → List Term → Term
  mkρs sh b i []       = R.con (quote P.●ᵣ) []
  mkρs sh b i (t ∷ ts) =
    if isNil (shapesOf tR t sh)
      then R.con (quote P._↦ᵣ_⨾_) (vArg (natT (b + i)) ∷ vArg t ∷ vArg (mkρs sh b (suc i) ts) ∷ [])
      else R.con (quote P._↦ᵣ_∶_⨾_) (vArg (natT (b + i)) ∷ vArg t ∷ vArg (mkShapes (shapesOf tR t sh))
                                     ∷ vArg (mkρs sh b (suc i) ts) ∷ [])

  mkα : List ShE → ℕ → ℕ → List Term → Term
  mkα sh b i []       = R.con (quote P.●ₐ) []
  mkα sh b i (t ∷ ts) = R.con (quote P._↦ₐ_∶_⨾_) (vArg (natT (b + i)) ∷ vArg t ∷ vArg (mkShapes (shapesOf tA t sh))
                                                 ∷ vArg (mkα sh b (suc i) ts) ∷ [])

  mkδ : List ShE → ℕ → ℕ → List Term → Term
  mkδ sh b i []       = R.con (quote P.●d) []
  mkδ sh b i (t ∷ ts) = R.con (quote P._↦d_∶_⨾_) (vArg (natT (b + i)) ∷ vArg t ∷ vArg (mkShapes (shapesOf tD t sh))
                                                 ∷ vArg (mkδ sh b (suc i) ts) ∷ [])

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

  absPrems : Cfg → St → List Term → TC (St × List Term × List Term)
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
  -- omitted module parameters, so ℂe / ℂu / ℂi are unfolded by hand.
  peelCtx zero    Γ = ret (Γ , [])
  peelCtx (suc k) Γ@(R.con c args) with lastVis args
  ... | (a ∷ f ∷ c′ ∷ _) = if c ≈ quote Sem.ℂx then push c′ a f else ret (Γ , [])
    where push : Term → Term → Term → TC (Term × List Term)
          push c′ a f = peelCtx k c′ >>= λ { (base , hs) → ret (base , hs ++ (mkPair a f ∷ [])) }
  ... | _ = ret (Γ , [])
  -- (the module parameters 𝔻 and W come first, so lastVis lists the
  -- visible arguments as  r f c …  for ℂe c f r,  i f c …  for ℂi c f i
  -- and  f c …  for ℂu c f)
  peelCtx (suc k) Γ@(R.def g args) with lastVis args
  ... | (x ∷ y ∷ z ∷ _) =
    if g ≈ quote Sem.ℂe then push z (R.con (quote Sem.CEr) (vArg x ∷ [])) y
    else if g ≈ quote Sem.ℂu then push y (R.con (quote Sem.CEu) []) x
    else if g ≈ quote Sem.ℂi then push z (R.con (quote Sem.CEi) (vArg x ∷ [])) y
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

  absPairs : Cfg → St → List Term → TC (St × List Term)
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
  -- Constructors copied by a module application (e.g. Rules._._⋆_, from an
  -- `open import Syntax ...` inside a parameterised module) carry that
  -- module's parameters as hidden arguments, which reflection gives as
  -- unknown.  In the abstract sequent nothing determines them, so (with dp)
  -- such constructors are replaced by the original ones.
  canonTable : List Name
  canonTable =
    quote S.Res._⋆_ ∷ quote S.rvar ∷ quote S.𝟎 ∷ quote S.𝐯 ∷
    quote S.𝕒 ∷ quote S.var ∷ quote S.⊤· ∷ quote S.⊥· ∷ quote S._∧·_ ∷ quote S._∨·_ ∷
    quote S._→·_ ∷ quote S.∀· ∷ quote S.∃· ∷ quote S.𝔸 ∷ quote S._Ｕ_ ∷ quote S.Ｏ ∷
    quote S._Ｓ_ ∷ quote S.Ｙ ∷ quote S.Ｂ ∷ quote S.Ｆ_ ∷ quote S._⟨_⟩_ ∷
    quote S.agentV ∷ quote S.agentC ∷ quote S.agentsV ∷ quote S.agentsL ∷
    quote S.dataV ∷ quote S.dataC ∷
    quote Sem.CEr ∷ quote Sem.CEu ∷ quote Sem.CEi ∷ []

  canonName : Name → TC Name
  canonName c = ret (find canonTable)
    where
    find : List Name → Name
    find [] = c
    find (c′ ∷ cs) = if c′ ≈ c then c′ else find cs

  visOnly : List (Arg Term) → List (Arg Term)
  visOnly [] = []
  visOnly (a ∷ as) = if isVis a then a ∷ visOnly as else visOnly as

  canonT    : ℕ → Term → TC Term
  canonArgs : ℕ → List (Arg Term) → TC (List (Arg Term))
  canonT zero    t = ret t
  canonT (suc n) (R.con c args) =
    canonName c >>= λ c′ → canonArgs n args >>= λ args′ →
    ret (if c′ == c then R.con c args′ else R.con c′ (visOnly args′))
  canonT (suc n) (R.def f args) = canonArgs n args >>= λ args′ → ret (R.def f args′)
  canonT (suc n) t = ret t
  canonArgs n [] = ret []
  canonArgs n (arg i t ∷ as) = canonT n t >>= λ t′ → canonArgs n as >>= λ as′ → ret (arg i t′ ∷ as′)

  -- the formulas of the hypotheses, premises and goal, for the shape scan
  formulas : List Term → List Term → Term → TC (List Term)
  formulas ctxHyps prems D = premF prems >>= λ fs → ret (D ∷ map (λ p → proj₂ (pairParts p)) ctxHyps ++ fs)
    where
    premF : List Term → TC (List Term)
    premF []       = ret []
    premF (p ∷ ps) = seqParts p >>= λ { (_ , _ , C) → premF ps >>= λ cs → ret (C ∷ cs) }

  normAll : List Term → TC (List Term)
  normAll []       = ret []
  normAll (t ∷ ts) = R.normalise t >>= λ t′ → normAll ts >>= λ ts′ → ret (t′ ∷ ts′)

  maxL : List ℕ → ℕ
  maxL []       = 0
  maxL (k ∷ ks) = k ⊔ maxL ks

  -- The common core.  Given a sequent  seq Γ T D  and premises (all over Γ),
  -- abstract everything, run the search srch, and return
  --   * the plugged derivation  plug-⊢ Γ₀ σ ρ d  (dp = false) or
  --     plug-⊢ₐ Γ₀ σ ρ α δ d  (dp = true),
  --     of type ⊢ (seq (addHyps Γ prems) T D) up to computation, where Γ₀ is
  --     Γ without its concrete hypotheses, and
  --   * the premises as (T , C) pairs, for hyps→rule.
  proveCore : Bool → Bool → Term → ℕ → Term → Term → Term → Term → List Term → TC (Term × List Term)
  proveCore chk dpm srch n goal Γ T D prems = do
    (Γ₀ , ctxHyps) ← peelCtx 1000 Γ
    let b = freshVar goal ⊔ freshRVar goal
    -- R.normalise elaborates its argument, which creates metas for omitted
    -- module parameters: it is run speculatively (only the shape of the
    -- normal forms is used).
    nfs ← (if dpm then R.runSpeculative ((formulas ctxHyps prems D >>= normAll) >>= λ ts → ret (ts , false))
                  else ret [])
    let ba = maxL (map (freshLit (quote S.agentC)) (goal ∷ nfs))
    let bd = maxL (map (freshLit (quote S.dataC)) (goal ∷ nfs))
    let sh = Data.List.concatMap scan nfs
    let c = cfg dpm b ba bd
    (st₀ , absCtx) ← absPairs c ([] , [] , [] , []) ctxHyps
    (st₁ , real , abst) ← absPrems c st₀ prems
    (st₂ , T′) ← absN0 c st₁ T
    ((fs , rs , as , ds) , D′) ← absF0 c st₂ D
    addH ← R.quoteTC addHyps
    hs ← (if dpm then canonT 10000 (mkList (absCtx ++ abst)) else ret (mkList (absCtx ++ abst)))
    T′ ← (if dpm then canonT 10000 T′ else ret T′)
    D′ ← (if dpm then canonT 10000 D′ else ret D′)
    let Δ = addH · (vArg (R.con (quote Sem.ℂ⟨⟩) []) ∷ vArg hs ∷ [])
    let q = srch · (vArg (R.lit (R.nat n)) ∷ vArg Δ ∷ vArg T′ ∷ vArg D′ ∷ [])
    (if chk then R.runSpeculative (check q) else ret tt)
    -- As in Method 1, the derivation is passed as  from-just (search⊢ n Δ T′ D′)
    -- rather than as its quoted normal form: Agda then only evaluates the
    -- search, instead of type-checking every rule application of the
    -- derivation again, which is much slower for large derivations.
    let d = R.def (quote from-just) (vArg q ∷ [])
    if dpm
      then (R.quoteTC plug-⊢ₐ >>= λ pl →
            ret (pl · (vArg Γ₀ ∷ vArg (mkσ b 0 fs) ∷ vArg (mkρs sh b 0 rs) ∷ vArg (mkα sh ba 0 as)
                       ∷ vArg (mkδ sh bd 0 ds) ∷ vArg d ∷ [])
                , real))
      else (R.quoteTC plug-⊢ >>= λ pl →
            ret (pl · (vArg Γ₀ ∷ vArg (mkσ b 0 fs) ∷ vArg (mkρ b 0 rs) ∷ hArg Δ ∷ hArg T′ ∷ hArg D′ ∷ vArg d ∷ [])
                , real))
    where
    -- Check, speculatively, that the abstract goal is well typed and that the
    -- search succeeds, to give a helpful error message otherwise.  The metas
    -- created while elaborating the abstract sequent are discarded.
    check : Term → TC (Σ ⊤ (λ _ → Bool))
    check q = do
     q′ ← R.catchTC (R.checkType q R.unknown)
                   (R.typeError (R.strErr "prove: the abstracted goal is ill-typed:"
                                 ∷ R.termErr q ∷ []))
     -- The search is run by checking  refl : is-just q′ ≡ true.  Agda's
     -- conversion checker evaluates it with sharing; evaluating it with
     -- R.reduce instead can be exponentially slower (and run out of memory).
     R.catchTC
       (R.checkType (R.con (quote refl) [])
                    (R.def (quote _≡_) (vArg (R.def (quote is-just) (vArg q′ ∷ []))
                                        ∷ vArg (R.con (quote true) []) ∷ []))
        >>= λ _ → ret (tt , false))
       (R.typeError (R.strErr "prove: no derivation found (or the search got stuck) with fuel"
                     ∷ R.termErr (R.lit (R.nat n)) ∷ []))

  -- Goals  ⊢ s,  sat-sequent M s  and  sat-rule M (rule ps s).
  proveGoal : Bool → Bool → Term → ℕ → Term → TC Term
  proveGoal chk dpm srch n ty = do
    R.def f args ← ret ty
      where _ → R.typeError (R.strErr "prove: unsupported goal" ∷ R.termErr ty ∷ [])
    go f (lastVis args)
    where
    go : Name → List Term → TC Term
    go f (s ∷ rest) =
      if f ≈ quote ⊢ then
        (seqParts s >>= λ { (Γ , T , D) →
         proveCore chk dpm srch n ty Γ T D [] >>= λ { (pd , _) → ret pd } })
      else if f ≈ quote sat-sequent then
        (withM rest λ M →
         seqParts s >>= λ { (Γ , T , D) →
         proveCore chk dpm srch n ty Γ T D [] >>= λ { (pd , _) →
         R.quoteTC sound >>= λ snd →
         ret (snd · (vArg M ∷ hArg R.unknown ∷ vArg pd ∷ [])) } })
      else if f ≈ quote sat-rule then
        (withM rest λ M →
         R.reduce s >>= λ ρ₀ → (if dpm then canonT 100000 ρ₀ else ret ρ₀) >>= λ ρ → ruleParts ρ >>= λ { (c , ps) →
         listElems 1000 ps >>= λ prems →
         seqParts c >>= λ { (Γ , T , D) →
         proveCore chk dpm srch n ty Γ T D prems >>= λ { (pd , real) →
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

private
  -- With dp, the search is not run beforehand (by check), which would run
  -- it twice: if the final term does not type-check, the goal is analysed
  -- again with check, for a helpful error message.
  proveDp : Term → ℕ → Term → TC ⊤
  proveDp srch n hole = do
    ty ← R.inferType hole
    ty ← canonT 100000 ty
    R.catchTC
      (proveGoal false true srch n ty >>= λ t → canonT 100000 t >>= λ t → R.unify hole t)
      (proveGoal true true srch n ty >>= λ t → canonT 100000 t >>= λ t → R.unify hole t)

macro
  -- Works on goals  ⊢ s,  sat-sequent M s  and  sat-rule M (rule ps s),  where
  -- s = seq Γ T C and every premise in ps has the form  seq Γ R H  for the
  -- same Γ.  Γ, the formulas and the resources may be opaque (Agda
  -- variables); concrete hypotheses at the end of Γ are abstracted too.
  prove : ℕ → Term → TC ⊤
  prove n hole = do
    ty ← R.inferType hole
    srch ← R.quoteTC search⊢
    t ← proveGoal true false srch n ty
    R.unify hole t

  -- The same with the matching and saturation search search⊢⁺, where opaque
  -- agents and data (at depth 0) are abstracted to placeholder constants,
  -- and nested weakenings of opaque terms are reproduced (shapes).
  prove⁺ : ℕ → Term → TC ⊤
  prove⁺ n hole = R.quoteTC search⊢⁺ >>= λ srch → proveDp srch n hole

  -- The same with the classical search search⊢ᶜ em (□L on □ = ¬◇¬).
  proveᶜ : Term → ℕ → Term → TC ⊤
  proveᶜ em n hole = R.quoteTC search⊢ᶜ >>= λ srch → proveDp (srch · (vArg em ∷ [])) n hole
\end{code}
