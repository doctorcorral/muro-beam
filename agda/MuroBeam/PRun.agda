------------------------------------------------------------------------
-- Process-layer steps. The ether is a flight list in the sender's
-- Code, counted by ctlRefs, not a new field of Sys and not a new Msg.
-- v0 send stays atomic. PStep is the v1b step relation: every Step,
-- plus these steps, so a reply can be in flight while the caller
-- demonitors.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.PRun where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _≡ᵇ_; z≤n)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Grade using (Grade; g0; g1; GTm)

open import MuroBeam.Grade using (selfKept; isZeroGrade; isG1; kind; Kind; Kmove; Kcopy)
open import MuroBeam.Heap using
  ( Obj; cell; live; Val; nat; suc↑; clo; payload; kids
  ; Ref; ref; obj; checked; residual; repl
  ; count; hasG1; count-++; has-++
  ; edgeRefs
  ; Bound; bnil; bcons; bound-++ )
open import MuroBeam.Lib using (lookup; update; mapCons; ≤-refl; +-mono; ∨-trueʳ)
open import MuroBeam.PSyntax using
  ( Thin; t[]; keep; skip
  ; PTm; done; send; recv; spawn; seq; await; ignore; nignore
  ; awaitT; ignoreT; flushT; ncheckT; ndemonT
  ; Flight; flight; flightRefs; Code; go; codeDead; codeDemo
  ; applyMoves; replyRoot; isProtoAt; protoTag; reply-slot )
open import MuroBeam.Process using
  ( Proc; proc; PState; ready; waiting; Sys; sys; heap; procs
  ; ctl; Ctl; idle; ev; rv; pr
  ; Frame; ar; fn; su; mt; bd; saved; seg
  ; roots; inbox; state; Msg; msg; post; setProc; snoc
  ; refsOf; regrade )
  renaming (done to pstDone)
open import MuroBeam.Collect using (Step)

------------------------------------------------------------------------
-- Maybe sequencing. Local, so it does not clash with Result._>>=_.
------------------------------------------------------------------------

_>>=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= _ = nothing
just x  >>= f = f x

infixl 1 _>>=_

------------------------------------------------------------------------
-- Tags recorded on a process. demo is demonitor. dead is consumption.
-- A tag parked under seq is read off the saved frame.
------------------------------------------------------------------------

deadFrames : List Frame → List ℕ
deadFrames []             = []
deadFrames (saved c ∷ ks) = codeDead c ++ deadFrames ks
deadFrames (_ ∷ ks)       = deadFrames ks

demoFrames : List Frame → List ℕ
demoFrames []             = []
demoFrames (saved c ∷ ks) = codeDemo c ++ demoFrames ks
demoFrames (_ ∷ ks)       = demoFrames ks

deadInCtl : Ctl → List ℕ
deadInCtl idle         = []
deadInCtl (ev _ _ k)   = deadFrames k
deadInCtl (rv _ _ k)   = deadFrames k
deadInCtl (pr c)       = codeDead c

demoInCtl : Ctl → List ℕ
demoInCtl idle         = []
demoInCtl (ev _ _ k)   = demoFrames k
demoInCtl (rv _ _ k)   = demoFrames k
demoInCtl (pr c)       = codeDemo c

hasTag : ℕ → List ℕ → Bool
hasTag _ []       = false
hasTag τ (x ∷ xs) = (x ≡ᵇ τ) ∨ hasTag τ xs

inboxHas : List Msg → ℕ → Bool
inboxHas []             _ = false
inboxHas (msg r ∷ ms)   τ = (obj r ≡ᵇ τ) ∨ inboxHas ms τ

mailHas : List Proc → ℕ → ℕ → Bool
mailHas ps i τ with lookup ps i
... | nothing = false
... | just p  = inboxHas (inbox p) τ

deadAt : List Proc → ℕ → ℕ → Bool
deadAt ps i τ with lookup ps i
... | nothing = false
... | just p  = hasTag τ (deadInCtl (ctl p))

------------------------------------------------------------------------
-- One fresh g0 cell. Moved slots and scrubbed slots point at it.
-- It is not an alias of an object that already exists.
------------------------------------------------------------------------

placeholder : List Obj → Ref
placeholder h = ref (length h) g0 g0 (selfKept g0)

------------------------------------------------------------------------
-- Handover. keep + g0 fails. keep + move records (index, object).
-- keep + copy aliases. skip stays with the parent. One placeholder
-- is shared by every moved slot.
------------------------------------------------------------------------

Split = List Ref × List Ref × List (ℕ × ℕ)

splitGo : ∀ {m n} → ℕ → Ref → Thin m n → List Ref → Maybe Split
splitGo _ _ t[] [] = just ([] , [] , [])
splitGo i ph (skip th) (r ∷ rs) =
  splitGo (suc i) ph th rs >>= λ (ce , pe , mv) →
  just (ce , r ∷ pe , mv)
splitGo i ph (keep th) (r ∷ rs) with kind (checked r)
... | nothing     = nothing
... | just Kmove  =
  splitGo (suc i) ph th rs >>= λ (ce , pe , mv) →
  just (r ∷ ce , ph ∷ pe , (i , obj r) ∷ mv)
... | just Kcopy  =
  splitGo (suc i) ph th rs >>= λ (ce , pe , mv) →
  just (r ∷ ce , r ∷ pe , mv)
splitGo _ _ t[] (_ ∷ _)   = nothing
splitGo _ _ (skip _) []   = nothing
splitGo _ _ (keep _) []   = nothing

spawn1 : Sys → ℕ → Maybe Sys
spawn1 (sys h ps) i =
  lookup ps i >>= λ p →
  spawned (ctl p) p
  where
  spawned : Ctl → Proc → Maybe Sys
  spawned (pr (go (spawn th ch pa) env eth d dm)) _ =
    let ph = placeholder h
        h' = snoc h (nat zero)
    in splitGo zero ph th env >>= λ (ce , pe , mv) →
       let pcode = pr (go (applyMoves mv pa) pe eth d dm)
           ccode = pr (go ch ce [] [] [])
           child = proc (length ps) ready [] [] ccode
       in setProc ps i pcode >>= λ ps1 →
          just (sys h' (ps1 ++ child ∷ []))
  spawned _ _ = nothing

------------------------------------------------------------------------
-- Emit. A finite point moves into a flight. ω and intervals are
-- copied into a flight. g0 is not sent. A destination that has
-- already demonitored or consumed the tag refuses a new emit.
-- Flights already in the ether are not recalled.
------------------------------------------------------------------------

blocked : List Proc → ℕ → ℕ → Bool
blocked ps j τ with lookup ps j
... | nothing = true
... | just q  = hasTag τ (deadInCtl (ctl q)) ∨ hasTag τ (demoInCtl (ctl q))

-- Top-level so a caller can name the same term `emit1` reduces to
-- once the process has been found.
emitCtl : List Obj → List Proc → ℕ → Ctl → Maybe Sys
emitCtl h ps i (pr (go (send j x k) env eth d dm)) =
  lookup env (toℕ x) >>= λ r →
  if isZeroGrade (residual r) then nothing
  else if blocked ps j (obj r) then nothing
  else sendAs (kind (checked r)) r j k env eth d dm
  where
  sendAs : Maybe Kind → Ref → ℕ → ∀ {n} → PTm n → List Ref →
           List Flight → List ℕ → List ℕ → Maybe Sys
  sendAs nothing _ _ _ _ _ _ _ = nothing
  sendAs (just Kmove) r j k env eth d dm =
    let ph  = placeholder h
        h'  = snoc h (nat zero)
        env' = repl (toℕ x) ph env
        c'  = pr (go k env' (eth ++ flight j r ∷ []) d dm)
    in setProc ps i c' >>= λ ps' → just (sys h' ps')
  sendAs (just Kcopy) r j k env eth d dm =
    let c' = pr (go k env (eth ++ flight j r ∷ []) d dm)
    in setProc ps i c' >>= λ ps' → just (sys h ps')
emitCtl _ _ _ _ = nothing

emit1 : Sys → ℕ → Maybe Sys
emit1 (sys h ps) i =
  lookup ps i >>= λ p →
  emitCtl h ps i (ctl p)

------------------------------------------------------------------------
-- Deliver. Pull one flight from `pr`, or from a `saved` frame while
-- seq is running. dead drops the flight. demo does not: a reply
-- in flight across demonitor is still enqueued. waiting wakes.
------------------------------------------------------------------------

pullCode : Code → Maybe (Flight × Code)
pullCode (go tm env (flight j r ∷ eth) d dm) = just (flight j r , go tm env eth d dm)
pullCode (go _ _ [] _ _) = nothing

pullFrames : List Frame → Maybe (Flight × List Frame)
pullFrames [] = nothing
pullFrames (saved c ∷ ks) with pullCode c
... | just (f , c') = just (f , saved c' ∷ ks)
... | nothing =
  pullFrames ks >>= λ (f , ks') →
  just (f , saved c ∷ ks')
pullFrames (k ∷ ks) =
  pullFrames ks >>= λ (f , ks') →
  just (f , k ∷ ks')

pullCtl : Ctl → Maybe (Flight × Ctl)
pullCtl (pr c) with pullCode c
... | just (f , c') = just (f , pr c')
... | nothing      = nothing
pullCtl (ev t e k) with pullFrames k
... | just (f , k') = just (f , ev t e k')
... | nothing       = nothing
pullCtl (rv r e k) with pullFrames k
... | just (f , k') = just (f , rv r e k')
... | nothing       = nothing
pullCtl idle = nothing

wake : Proc → Proc
wake p with state p
... | waiting = record p { state = ready }
... | ready   = p
... | pstDone = p

deliver1 : Sys → ℕ → Maybe Sys
deliver1 (sys h ps) i =
  lookup ps i >>= λ p →
  pullCtl (ctl p) >>= land
  where
  land : Flight × Ctl → Maybe Sys
  land (flight j r , c1) =
    setProc ps i c1 >>= λ ps1 →
    lookup ps1 j >>= λ q →
    if hasTag (obj r) (deadInCtl (ctl q))
      then just (sys h ps1)
      else update j (wake (post q r)) ps1 >>= λ ps2 →
           just (sys h ps2)

------------------------------------------------------------------------
-- Receive. Empty and ready parks the process in `waiting`.
-- The v0 `recv` function is untouched and still returns nothing.
------------------------------------------------------------------------

setCtlSt : List Proc → ℕ → Ctl → PState → Maybe (List Proc)
setCtlSt []       _       _ _  = nothing
setCtlSt (p ∷ ps) zero    c st = just (record p { ctl = c ; state = st } ∷ ps)
setCtlSt (p ∷ ps) (suc i) c st = mapCons p (setCtlSt ps i c st)

-- Top-level so a proof can case on the state and the inbox without
-- rewriting those projections. `recv1` is this function after lookup.
recvStep : List Obj → List Proc → ℕ → Proc → Ctl → PState → List Msg → Maybe Sys
recvStep h ps i p (pr (go (recv _ _ k) env eth d dm)) _ (msg r ∷ ms) =
  let p' = record p
             { state = ready
             ; inbox = ms
             ; ctl   = pr (go k (r ∷ env) eth d dm) }
  in update i p' ps >>= λ ps' → just (sys h ps')
recvStep h ps i p (pr (go (recv _ _ _) _ _ _ _)) ready [] =
  update i (record p { state = waiting }) ps >>= λ ps' →
  just (sys h ps')
recvStep _ _ _ _ _ _ _ = nothing

recv1 : Sys → ℕ → Maybe Sys
recv1 (sys h ps) i =
  lookup ps i >>= λ p →
  recvStep h ps i p (ctl p) (state p) (inbox p)

------------------------------------------------------------------------
-- Scrub a tag out of every non-edge position. Environment slots are
-- replaced, so de Bruijn indices stay put. Mailbox messages, roots,
-- and flights are deleted, so the mailbox does not keep a dummy.
-- A suc↑ or clo edge is not replaced by the placeholder: that index
-- sits at the end of the heap and would break the child-below-parent
-- order. `blankEdges` clears any payload that still holds the tag,
-- so the edge is not a reference anymore.
------------------------------------------------------------------------

scrubOne : ℕ → Ref → Ref → Ref
scrubOne τ ph r = if obj r ≡ᵇ τ then ph else r

scrubRefs : ℕ → Ref → List Ref → List Ref
scrubRefs _ _  []       = []
scrubRefs τ ph (r ∷ rs) = scrubOne τ ph r ∷ scrubRefs τ ph rs

dropRefs : ℕ → List Ref → List Ref
dropRefs _ []       = []
dropRefs τ (r ∷ rs) = if obj r ≡ᵇ τ then dropRefs τ rs else r ∷ dropRefs τ rs

dropMsgs : ℕ → List Msg → List Msg
dropMsgs _ []           = []
dropMsgs τ (msg r ∷ ms) = if obj r ≡ᵇ τ then dropMsgs τ ms else msg r ∷ dropMsgs τ ms

dropFlights : ℕ → List Flight → List Flight
dropFlights _ []                     = []
dropFlights τ (flight j r ∷ fs)      =
  if obj r ≡ᵇ τ then dropFlights τ fs else flight j r ∷ dropFlights τ fs

scrubCode : ℕ → Ref → Code → Code
scrubCode τ ph (go tm env eth d dm) =
  go tm (scrubRefs τ ph env) (dropFlights τ eth) d dm

scrubFrame : ℕ → Ref → Frame → Frame
scrubFrame τ ph (fn r)    = fn (scrubOne τ ph r)
scrubFrame τ ph (bd env)  = bd (scrubRefs τ ph env)
scrubFrame τ ph (saved c) = saved (scrubCode τ ph c)
scrubFrame _ _  (ar a)    = ar a
scrubFrame _ _  su        = su
scrubFrame _ _  (mt e z s) = mt e z s
scrubFrame _ _  (seg ds)  = seg ds

scrubFrames : ℕ → Ref → List Frame → List Frame
scrubFrames _ _  []       = []
scrubFrames τ ph (k ∷ ks) = scrubFrame τ ph k ∷ scrubFrames τ ph ks

scrubCtl : ℕ → Ref → Ctl → Ctl
scrubCtl _ _  idle         = idle
scrubCtl τ ph (ev t e k)   = ev t (scrubRefs τ ph e) (scrubFrames τ ph k)
scrubCtl τ ph (rv r e k)   = rv (scrubOne τ ph r) (scrubRefs τ ph e) (scrubFrames τ ph k)
scrubCtl τ ph (pr c)       = pr (scrubCode τ ph c)

scrubProc : ℕ → Ref → Proc → Proc
scrubProc τ ph p = record p
  { roots = dropRefs τ (roots p)
  ; inbox = dropMsgs τ (inbox p)
  ; ctl   = scrubCtl τ ph (ctl p)
  }

-- After the scrub the term is still the tagged form. Rewrite it to
-- the continuation and record the tag as dead.
finishFlush : ℕ → Ctl → Maybe Ctl
finishFlush τ (pr (go (flushT τ' k) env eth d dm)) =
  if τ ≡ᵇ τ' then just (pr (go k env eth (τ ∷ d) dm)) else nothing
finishFlush _ _ = nothing

finishAwait : ℕ → Ctl → Maybe Ctl
finishAwait τ (pr (go (awaitT τ' k) env eth d dm)) =
  if τ ≡ᵇ τ' then just (pr (go k env eth (τ ∷ d) dm)) else nothing
finishAwait _ _ = nothing

finishPeek : ℕ → Ctl → Maybe Ctl
finishPeek τ (pr (go (ncheckT τ' k) env eth d dm)) =
  if τ ≡ᵇ τ' then just (pr (go k env eth (τ ∷ d) dm)) else nothing
finishPeek _ _ = nothing

------------------------------------------------------------------------
-- Edge scrub. A payload that holds the tag becomes `nat 0`, which has
-- no children. A nat stays a nat. The placeholder is not written into
-- an edge: its index is the length of the heap, so it is not below
-- its parent. Clearing the payload keeps the ordered heap and drops
-- the reference, including every other child of that same closure.
------------------------------------------------------------------------

-- Local absurdity. Hidden from the umbrella so it does not clash
-- with the copy in Collect.
data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

holdsRefs : ℕ → List Ref → Bool
holdsRefs _ []       = false
holdsRefs τ (r ∷ rs) = (obj r ≡ᵇ τ) ∨ holdsRefs τ rs

holdsVal : ℕ → Val → Bool
holdsVal _ (nat _)     = false
holdsVal τ (suc↑ r)    = obj r ≡ᵇ τ
holdsVal τ (clo rs _)  = holdsRefs τ rs

blankVal : ℕ → Val → Val
blankVal τ v = if holdsVal τ v then nat zero else v

blankObj : ℕ → Obj → Obj
blankObj τ o = record o { payload = blankVal τ (payload o) }

blankEdges : ℕ → List Obj → List Obj
blankEdges _ []       = []
blankEdges τ (o ∷ os) = blankObj τ o ∷ blankEdges τ os

blank-length : ∀ τ h → length (blankEdges τ h) ≡ length h
blank-length _ []       = refl
blank-length τ (_ ∷ os) = cong suc (blank-length τ os)

holdsRefs-0 : ∀ τ rs → holdsRefs τ rs ≡ false → count τ rs ≡ 0
holdsRefs-0 _ []       _  = refl
holdsRefs-0 τ (r ∷ rs) eq with obj r ≡ᵇ τ
... | true  = ⊥-elim (boom eq)
  where
  boom : true ≡ false → ⊥
  boom ()
... | false = holdsRefs-0 τ rs eq

kids-blank : ∀ τ v → count τ (kids (blankVal τ v)) ≡ 0
kids-blank _ (nat _) = refl
kids-blank τ (suc↑ r) with obj r ≡ᵇ τ in eq
... | true  = refl
... | false rewrite eq = refl
kids-blank τ (clo rs _) with holdsRefs τ rs in eq
... | true  = refl
... | false = holdsRefs-0 τ rs eq

blank-edge-0 : ∀ τ h → count τ (edgeRefs (blankEdges τ h)) ≡ 0
blank-edge-0 _ []       = refl
blank-edge-0 τ (o ∷ os) rewrite
    count-++ τ (kids (payload (blankObj τ o))) (edgeRefs (blankEdges τ os))
  | kids-blank τ (payload o)
  | blank-edge-0 τ os = refl

kids-le : ∀ k τ v → count k (kids (blankVal τ v)) ≤ count k (kids v)
kids-le _ _ (nat _) = ≤-refl
kids-le _ τ (suc↑ r) with obj r ≡ᵇ τ
... | true  = z≤n
... | false = ≤-refl
kids-le _ τ (clo rs _) with holdsRefs τ rs
... | true  = z≤n
... | false = ≤-refl

blank-count-≤ : ∀ k τ h →
  count k (edgeRefs (blankEdges τ h)) ≤ count k (edgeRefs h)
blank-count-≤ _ _ []       = ≤-refl
blank-count-≤ k τ (o ∷ os) rewrite
    count-++ k (kids (payload (blankObj τ o))) (edgeRefs (blankEdges τ os))
  | count-++ k (kids (payload o)) (edgeRefs os) =
  +-mono (kids-le k τ (payload o)) (blank-count-≤ k τ os)

kids-has : ∀ k τ v →
  hasG1 k (kids (blankVal τ v)) ≡ true → hasG1 k (kids v) ≡ true
kids-has _ _ (nat _) ()
kids-has _ τ (suc↑ r) eq with obj r ≡ᵇ τ
... | true  = ⊥-elim (boom eq)
  where
  boom : false ≡ true → ⊥
  boom ()
... | false = eq
kids-has _ τ (clo rs _) eq with holdsRefs τ rs
... | true  = ⊥-elim (boom eq)
  where
  boom : false ≡ true → ⊥
  boom ()
... | false = eq

or-keep : ∀ {a b c d} →
  (a ≡ true → c ≡ true) → (b ≡ true → d ≡ true) →
  (a ∨ b) ≡ true → (c ∨ d) ≡ true
or-keep {a = a} {b = b} {c = c} {d = d} ac k2 eq = body a b c d ac k2 eq
  where
  body : (x y p q : Bool) →
         (x ≡ true → p ≡ true) → (y ≡ true → q ≡ true) →
         (x ∨ y) ≡ true → (p ∨ q) ≡ true
  body true  _ p _ ac' _  _   rewrite ac' refl = refl
  body false _ p _ _   k2' eq' rewrite k2' eq' = ∨-trueʳ p

blank-has : ∀ k τ h →
  hasG1 k (edgeRefs (blankEdges τ h)) ≡ true → hasG1 k (edgeRefs h) ≡ true
blank-has _ _ [] ()
blank-has k τ (o ∷ os) eq =
  subst (_≡ true) (sym (has-++ k (kids (payload o)) (edgeRefs os)))
    (or-keep (kids-has k τ (payload o)) (blank-has k τ os)
      (subst (_≡ true) (has-++ k (kids (payload (blankObj τ o)))
                                 (edgeRefs (blankEdges τ os))) eq))

split-bound : ∀ {n} xs ys → Bound n (xs ++ ys) → Bound n xs × Bound n ys
split-bound []       ys b = bnil , b
split-bound (x ∷ xs) ys (bcons lt rest) =
  let bx , by = split-bound xs ys rest
  in bcons lt bx , by

kids-bound : ∀ {n} τ v → Bound n (kids v) → Bound n (kids (blankVal τ v))
kids-bound _ (nat _)    b = b
kids-bound τ (suc↑ r)   b with obj r ≡ᵇ τ
... | true  = bnil
... | false = b
kids-bound τ (clo rs _) b with holdsRefs τ rs
... | true  = bnil
... | false = b

blank-bound : ∀ {n} τ h → Bound n (edgeRefs h) → Bound n (edgeRefs (blankEdges τ h))
blank-bound _ []       b = b
blank-bound τ (o ∷ os) b =
  let bk , br = split-bound (kids (payload o)) (edgeRefs os) b
  in bound-++ (kids-bound τ (payload o) bk) (blank-bound τ os br)

consume : Sys → ℕ → ℕ → (ℕ → Ctl → Maybe Ctl) → Maybe Sys
consume (sys h ps) i τ finish =
  let ph  = placeholder h
      h'  = snoc (blankEdges τ h) (nat zero)
      ps1 = map (scrubProc τ ph) ps
  in lookup ps1 i >>= λ p1 →
     finish τ (ctl p1) >>= λ c' →
     setCtlSt ps1 i c' ready >>= λ ps2 →
     just (sys h' ps2)

------------------------------------------------------------------------
-- Proper ignore: demonitor, then flush. Demonitor does not flush.
------------------------------------------------------------------------

arm1 : Sys → ℕ → Maybe Sys
arm1 (sys h ps) i =
  lookup ps i >>= λ _ →
  lookup ps i >>= λ p →
  armed (ctl p)
  where
  armed : Ctl → Maybe Sys
  armed (pr (go (ignoreT τ k) env eth d dm)) =
    setProc ps i (pr (go (flushT τ k) env eth d (τ ∷ dm))) >>= λ ps' →
    just (sys h ps')
  armed _ = nothing

flush1 : Sys → ℕ → Maybe Sys
flush1 s i =
  lookup (procs s) i >>= λ p →
  flushed (ctl p)
  where
  flushed : Ctl → Maybe Sys
  flushed (pr (go (flushT τ _) _ _ _ _)) = consume s i τ finishFlush
  flushed _ = nothing

------------------------------------------------------------------------
-- await consumes a reply that has arrived, and waits otherwise.
-- The reference is dropped. It is not bound.
------------------------------------------------------------------------

awaitPark : List Obj → List Proc → ℕ → ℕ → ∀ {n} → PTm n →
            List Ref → List Flight → List ℕ → List ℕ → PState → Maybe Sys
awaitPark h ps i τ k env eth d dm ready =
  setCtlSt ps i (pr (go (awaitT τ k) env eth d dm)) waiting >>= λ ps' →
  just (sys h ps')
awaitPark _ _ _ _ _ _ _ _ _ _ = nothing

-- The boolean is `inboxHas`, passed in so a proof can case on it.
awaitOn : List Obj → List Proc → ℕ → Proc → Ctl → Bool → Maybe Sys
awaitOn h ps i p (pr (go (awaitT τ k) env eth d dm)) true =
  consume (sys h ps) i τ finishAwait
awaitOn h ps i p (pr (go (awaitT τ k) env eth d dm)) false =
  awaitPark h ps i τ k env eth d dm (state p)
awaitOn _ _ _ _ _ _ = nothing

await1 : Sys → ℕ → Maybe Sys
await1 (sys h ps) i =
  lookup ps i >>= λ p →
  awaitOn h ps i p (ctl p) (inboxHas (inbox p) (awaitTag (ctl p)))
  where
  awaitTag : Ctl → ℕ
  awaitTag (pr (go (awaitT τ _) _ _ _ _)) = τ
  awaitTag _ = zero

------------------------------------------------------------------------
-- Naive ignore. `npeek1` is `after 0`. A hit consumes. A miss
-- becomes demonitor with no flush and without setting dead, so a
-- flight still in the ether is delivered afterwards.
------------------------------------------------------------------------

npeekOn : List Obj → List Proc → ℕ → Ctl → Bool → Maybe Sys
npeekOn h ps i (pr (go (ncheckT τ k) env eth d dm)) true =
  consume (sys h ps) i τ finishPeek
npeekOn h ps i (pr (go (ncheckT τ k) env eth d dm)) false =
  setProc ps i (pr (go (ndemonT τ k) env eth d dm)) >>= λ ps' →
  just (sys h ps')
npeekOn _ _ _ _ _ = nothing

npeek1 : Sys → ℕ → Maybe Sys
npeek1 (sys h ps) i =
  lookup ps i >>= λ p →
  npeekOn h ps i (ctl p) (inboxHas (inbox p) (npeekTag (ctl p)))
  where
  npeekTag : Ctl → ℕ
  npeekTag (pr (go (ncheckT τ _) _ _ _ _)) = τ
  npeekTag _ = zero

ndemon1 : Sys → ℕ → Maybe Sys
ndemon1 (sys h ps) i =
  lookup ps i >>= λ _ →
  lookup ps i >>= λ p →
  demon (ctl p)
  where
  demon : Ctl → Maybe Sys
  demon (pr (go (ndemonT τ k) env eth d dm)) =
    setProc ps i (pr (go k env eth d (τ ∷ dm))) >>= λ ps' →
    just (sys h ps')
  demon _ = nothing

------------------------------------------------------------------------
-- seq runs the entry under `saved ∷ seg ds`. The ether moves onto
-- `saved` and is not duplicated into that frame's environment.
-- bind resumes `saved ∷ []`, and it resumes `saved ∷ seg ∷ []` when
-- the continuation is not `done`. A `done` continuation stays parked,
-- which is how a pure `(seq <btm> (done))` image stops stuck.
-- A reply root regrades a unique returned cell to g1. See `bind1`.
-- done drops roots and the environment and keeps flights.
------------------------------------------------------------------------

seq1 : Sys → ℕ → Maybe Sys
seq1 (sys h ps) i =
  lookup ps i >>= λ _ →
  lookup ps i >>= λ p →
  sequenced (ctl p)
  where
  sequenced : Ctl → Maybe Sys
  sequenced (pr (go (seq ds e k) env eth d dm)) =
    setProc ps i (ev e env (saved (go k [] eth d dm) ∷ seg ds ∷ [])) >>= λ ps' →
    just (sys h ps')
  sequenced _ = nothing

-- `done` is the pure-image continuation. Anything else is a process
-- the seq was waiting to run.
openCont : ∀ {n} → PTm n → Bool
openCont done            = false
openCont (send _ _ _)    = true
openCont (recv _ _ _)    = true
openCont (spawn _ _ _)   = true
openCont (seq _ _ _)     = true
openCont (await _ _)     = true
openCont (ignore _ _)    = true
openCont (nignore _ _)   = true
openCont (awaitT _ _)    = true
openCont (ignoreT _ _)   = true
openCont (flushT _ _)    = true
openCont (ncheckT _ _)   = true
openCont (ndemonT _ _)   = true

-- Resume `saved` over `seg`. A reply root names slot 0, which `seq`
-- checked at grade 1. The cell `eval` just returned is still ω.
-- Regrade it to g1 when it is not already g1 and it is the only
-- reference to its object (`bind-promotes`). `regrade-move` says
-- that head is `Kmove`. `bind-spawn-tag` is the step from this
-- `just` through one `spawn1` to the tagged parent. It still
-- assumes the tail of the environment splits. `checkP`'s fresh-body
-- guard is not a premise of that lemma.
-- An aliased non-g1 result is refused (`bind-count-refuses`): a
-- second g1 alias would break `Grade1Unique`, and the ω alias
-- would not be the move `markProto` tags. The already-g1 branch
-- does not read the count. `freshBody` is syntactic. It does not
-- read the heap, so an aliased fresh head can still be a checked
-- image. There is no theorem from that guard to this count.
-- A singleton `saved` is the book bind and is not regraded.
bind1 : Sys → ℕ → Maybe Sys
bind1 (sys h ps) i =
  lookup ps i >>= λ _ →
  lookup ps i >>= λ p →
  bound (ctl p)
  where
  bound : Ctl → Maybe Sys
  bound (rv r env (saved (go k cenv eth d dm) ∷ [])) =
    setProc ps i (pr (go k (r ∷ (env ++ cenv)) eth d dm)) >>= λ ps' →
    just (sys h ps')
  bound (rv r env (saved (go k cenv eth d dm) ∷ seg _ ∷ [])) with openCont k
  ... | false = nothing
  ... | true with replyRoot k
  ... | false =
    setProc ps i (pr (go k (r ∷ (env ++ cenv)) eth d dm)) >>= λ ps' →
    just (sys h ps')
  ... | true with isG1 (checked r) | count (obj r) (refsOf (sys h ps)) ≡ᵇ 1
  ... | true  | _     =
    setProc ps i (pr (go k (r ∷ (env ++ cenv)) eth d dm)) >>= λ ps' →
    just (sys h ps')
  ... | false | false = nothing
  ... | false | true  =
    setProc ps i (pr (go k (regrade r g1 ∷ (env ++ cenv)) eth d dm)) >>= λ ps' →
    just (sys h ps')
  bound _ = nothing

-- `setProc` writes the control and leaves the rest of the process.
setProc-lookup :
  ∀ ps i c p ps' →
  lookup ps i ≡ just p →
  setProc ps i c ≡ just ps' →
  lookup ps' i ≡ just (record p { ctl = c })
setProc-lookup [] i c p ps' () eq
setProc-lookup (p ∷ ps) zero c .p .(record p { ctl = c } ∷ ps) refl refl = refl
setProc-lookup (x ∷ ps) (suc i) c p ps' lk eq
  with setProc ps i c in es
... | nothing = no eq
  where
  no : nothing ≡ just ps' →
       lookup ps' (suc i) ≡ just (record p { ctl = c })
  no ()
... | just ps0 = yes eq
  where
  yes : just (x ∷ ps0) ≡ just ps' →
        lookup ps' (suc i) ≡ just (record p { ctl = c })
  yes refl = setProc-lookup ps i c p ps0 lk es

-- The regraded head is the moved grade. `kind g1` is `Kmove`.
regrade-move : ∀ r → kind (checked (regrade r g1)) ≡ just Kmove
regrade-move r = refl

-- A reply root whose returned cell is not g1, and is named once,
-- is installed regraded. The other `bind1` branches are the
-- `false ≡ true` cases of these premises.
bind-promotes :
  ∀ {n} h ps i r env (k : PTm n) cenv eth d dm {ds} p t →
  lookup ps i ≡ just p →
  ctl p ≡ rv r env (saved (go k cenv eth d dm) ∷ seg ds ∷ []) →
  openCont k ≡ true →
  replyRoot k ≡ true →
  isG1 (checked r) ≡ false →
  (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ true →
  bind1 (sys h ps) i ≡ just t →
  lookup (procs t) i ≡
    just (record p { ctl = pr (go k (regrade r g1 ∷ (env ++ cenv)) eth d dm) })
bind-promotes h ps i r env k cenv eth d dm p t lk ce oc rr ng one eq
  rewrite lk | ce | oc | rr | ng | one = finish eq
  where
  c = pr (go k (regrade r g1 ∷ (env ++ cenv)) eth d dm)
  finish : (setProc ps i c >>= λ ps' → just (sys h ps')) ≡ just t →
           lookup (procs t) i ≡ just (record p { ctl = c })
  finish eq2 with setProc ps i c in sp
  ... | nothing = no eq2
    where
    no : nothing ≡ just t → lookup (procs t) i ≡ just (record p { ctl = c })
    no ()
  ... | just ps' = yes eq2
    where
    yes : just (sys h ps') ≡ just t →
          lookup (procs t) i ≡ just (record p { ctl = c })
    yes refl = setProc-lookup ps i c p ps' lk sp

-- A reply root on `saved ∷ seg ∷ []` whose returned cell is not g1,
-- and whose object is not named exactly once, is refused. This is
-- the `false | false` branch of `bind1`. The `isG1` branch does not
-- consult the count: a cell that is already g1 is installed as it is.
-- `alias-await-probe` in `MuroBeam.RunImage` is a closed test of this
-- lemma, not the lemma itself.
bind-count-refuses :
  ∀ {n} h ps i r env (k : PTm n) cenv eth d dm {ds} p →
  lookup ps i ≡ just p →
  ctl p ≡ rv r env (saved (go k cenv eth d dm) ∷ seg ds ∷ []) →
  openCont k ≡ true →
  replyRoot k ≡ true →
  isG1 (checked r) ≡ false →
  (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ false →
  bind1 (sys h ps) i ≡ nothing
bind-count-refuses h ps i r env k cenv eth d dm p lk ce oc rr ng many
  rewrite lk | ce | oc | rr | ng | many = refl

-- `keep` of a `Kmove` cell records `(index, object)` and continues.
split-keep-move : ∀ {m n} i ph (th : Thin m n) r rs ce pe mv →
  kind (checked r) ≡ just Kmove →
  splitGo (suc i) ph th rs ≡ just (ce , pe , mv) →
  splitGo i ph (keep th) (r ∷ rs) ≡
    just (r ∷ ce , ph ∷ pe , (i , obj r) ∷ mv)
split-keep-move i ph th r rs ce pe mv kq sq rewrite kq = peel sq
  where
  peel : splitGo (suc i) ph th rs ≡ just (ce , pe , mv) →
         (splitGo (suc i) ph th rs >>= λ (ce' , pe' , mv') →
            just (r ∷ ce' , ph ∷ pe' , (i , obj r) ∷ mv'))
           ≡ just (r ∷ ce , ph ∷ pe , (i , obj r) ∷ mv)
  peel eq rewrite eq = refl

-- The head of a kept move list is slot 0 when the split started there.
split-head : ∀ {m n} ph (th : Thin m n) r rs ce pe mv →
  kind (checked r) ≡ just Kmove →
  splitGo zero ph (keep th) (r ∷ rs) ≡ just (ce , pe , mv) →
  ∃ λ ce' → ∃ λ pe' → ∃ λ mv' →
    ce ≡ r ∷ ce' × pe ≡ ph ∷ pe' ×
    mv ≡ (zero , obj r) ∷ mv' ×
    splitGo (suc zero) ph th rs ≡ just (ce' , pe' , mv')
split-head ph th r rs ce pe mv kq eq rewrite kq = peel eq
  where
  peel : (splitGo (suc zero) ph th rs >>= λ (ce' , pe' , mv') →
            just (r ∷ ce' , ph ∷ pe' , (zero , obj r) ∷ mv'))
           ≡ just (ce , pe , mv) →
         ∃ λ ce' → ∃ λ pe' → ∃ λ mv' →
           ce ≡ r ∷ ce' × pe ≡ ph ∷ pe' ×
           mv ≡ (zero , obj r) ∷ mv' ×
           splitGo (suc zero) ph th rs ≡ just (ce' , pe' , mv')
  peel eq2 with splitGo (suc zero) ph th rs
  ... | nothing = no eq2
    where
    no : ∀ {A : Set} → nothing ≡ just (ce , pe , mv) → A
    no ()
  ... | just (ce' , pe' , mv') = yes eq2
    where
    yes : just (r ∷ ce' , ph ∷ pe' , (zero , obj r) ∷ mv') ≡ just (ce , pe , mv) →
          ∃ λ ce0 → ∃ λ pe0 → ∃ λ mv0 →
            ce ≡ r ∷ ce0 × pe ≡ ph ∷ pe0 ×
            mv ≡ (zero , obj r) ∷ mv0 ×
            just (ce' , pe' , mv') ≡ just (ce0 , pe0 , mv0)
    yes refl = ce' , pe' , mv' , refl , refl , refl , refl

-- A kept `Kmove` at index 0 tags the protocol root. Later moves do not
-- untag it (`reply-slot`, via `split-head`). The parent of
-- `spawn (keep th)` is a `PTm (suc n)`: `keep th` has codomain `suc n`.
spawn-reply-tag :
  ∀ {m n} (ph : Ref) (th : Thin m n) (pa : PTm (suc n)) (r : Ref)
    (rs ce pe : List Ref) (mv : List (ℕ × ℕ)) →
  kind (checked r) ≡ just Kmove →
  splitGo {suc m} {suc n} zero ph (keep th) (r ∷ rs) ≡ just (ce , pe , mv) →
  isProtoAt zero pa ≡ true →
  applyMoves mv pa ≡ protoTag (obj r) pa
spawn-reply-tag ph th pa r rs ce pe mv kq eq proto =
  tagged (split-head ph th r rs ce pe mv kq eq)
  where
  tagged :
    (∃ λ ce' → ∃ λ pe' → ∃ λ mv' →
      ce ≡ r ∷ ce' × pe ≡ ph ∷ pe' ×
      mv ≡ (zero , obj r) ∷ mv' ×
      splitGo (suc zero) ph th rs ≡ just (ce' , pe' , mv')) →
    applyMoves mv pa ≡ protoTag (obj r) pa
  tagged (_ , _ , mv' , _ , _ , mvq , _) =
    subst (λ mv0 → applyMoves mv0 pa ≡ protoTag (obj r) pa) (sym mvq)
      (reply-slot pa (obj r) mv' proto)

-- `setProc` succeeds wherever `lookup` does. The written control is
-- whatever the caller passed.
setProc-just : ∀ ps i p c → lookup ps i ≡ just p → ∃ λ ps' → setProc ps i c ≡ just ps'
setProc-just [] i p c ()
setProc-just (p0 ∷ ps) zero .p0 c refl = (record p0 { ctl = c } ∷ ps) , refl
setProc-just (p0 ∷ ps) (suc i) p c lk =
  let ps' , eq = setProc-just ps i p c lk
  in (p0 ∷ ps') , cong (mapCons p0) eq

-- Appending a child does not move an index that was already present.
lookup-++-just : ∀ {A : Set} (xs ys : List A) i x →
  lookup xs i ≡ just x → lookup (xs ++ ys) i ≡ just x
lookup-++-just [] ys i x ()
lookup-++-just (x0 ∷ xs) ys zero .x0 refl = refl
lookup-++-just (x0 ∷ xs) ys (suc i) x eq = lookup-++-just xs ys i x eq

-- `spawn1` after the process, the split, and the tag are known.
-- Each rewrite is a variable. This clause does not mention `bind1`,
-- so it does not unfold the `with` inside `bind-promotes`.
spawn-at :
  ∀ {m n} h ps i p (th : Thin m n) (ch : PTm m) (pa : PTm n)
    env eth d dm ce pe mv τ ps1 →
  lookup ps i ≡ just p →
  ctl p ≡ pr (go (spawn th ch pa) env eth d dm) →
  splitGo zero (placeholder h) th env ≡ just (ce , pe , mv) →
  applyMoves mv pa ≡ protoTag τ pa →
  setProc ps i (pr (go (protoTag τ pa) pe eth d dm)) ≡ just ps1 →
  spawn1 (sys h ps) i ≡
    just (sys (snoc h (nat zero))
          (ps1 ++ proc (length ps) ready [] [] (pr (go ch ce [] [] [])) ∷ []))
spawn-at h ps i p th ch pa env eth d dm ce pe mv τ ps1 lk cq sq tq spe
  rewrite lk | cq | sq | tq | spe = refl

-- A promoting `bind1` whose continuation is `spawn (keep th) ch pa`,
-- followed by one `spawn1`, tags that parent.
--
-- Composes `bind-promotes`, `regrade-move`, `split-keep-move`, and
-- `spawn-reply-tag` (`split-head` and `reply-slot`).
--
-- Premises `bind1 ≡ just` does not discharge:
-- * the continuation is this `spawn (keep th)`, so the head slot is
--   the one `keep` moves (`replyRoot` of that term is `isProtoAt zero pa`);
-- * `isG1 (checked r) ≡ false` and the count is 1, the branch that
--   regrades (the already-`g1` branch installs `r` unchanged);
-- * `splitGo (suc zero) (placeholder h) th (env ++ cenv) ≡ just (ce , pe , mv)`.
--   A later `keep` of a `g0` cell, or a thinning that does not match
--   the tail, is still `nothing`. `placeholder h` is the cell `spawn1`
--   allocates. `bind1` does not change the heap, so that cell is the
--   one `spawn1` computes from `t`.
-- * `freshBody` is not a premise. There is no theorem from that guard
--   to this tag.
--
-- `openCont` of a `spawn` is `true`, so that premise of `bind-promotes`
-- holds by computation. The object's index is `obj r` after `regrade`.
-- The conclusion is the parent's control. `u` also snocs the placeholder
-- and appends the child; those are what `spawn1` builds and are not
-- restated as a separate equation.
--
-- The proof splits `bind1` once, on the promoting branch `bind-promotes`
-- names, and passes that lemma's lookup to `setProc-just`. `spawn-at`
-- rewrites the lookup, the control, `full`, `tagq`, and the second
-- `setProc` as variables. The `with` inside `bind-promotes` and
-- `spawn-reply-tag` is not unfolded again.
bind-spawn-tag :
  ∀ {n m} h ps i r env (th : Thin m n) (ch : PTm (suc m)) (pa : PTm (suc n))
    cenv eth d dm {ds} p t ce pe mv →
  lookup ps i ≡ just p →
  ctl p ≡
    rv r env
      (saved (go (spawn (keep th) ch pa) cenv eth d dm) ∷ seg ds ∷ []) →
  isProtoAt zero pa ≡ true →
  isG1 (checked r) ≡ false →
  (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ true →
  bind1 (sys h ps) i ≡ just t →
  splitGo (suc zero) (placeholder h) th (env ++ cenv) ≡ just (ce , pe , mv) →
  ∃ λ u →
    spawn1 t i ≡ just u ×
    lookup (procs u) i ≡
      just (record (record p { ctl =
              pr (go (spawn (keep th) ch pa)
                     (regrade r g1 ∷ (env ++ cenv)) eth d dm) })
            { ctl =
              pr (go (protoTag (obj r) pa)
                     (placeholder h ∷ pe) eth d dm) })
bind-spawn-tag h ps i r env th ch pa cenv eth d dm {ds} p t ce pe mv
  lk ctlq proto ng uniq bq tail =
  fromBind bq
  where
  k = spawn (keep th) ch pa
  rg = regrade r g1
  rest = env ++ cenv
  env' = rg ∷ rest
  c0 = pr (go k env' eth d dm)
  p1 = record p { ctl = c0 }
  ph = placeholder h
  km = regrade-move r
  ce0 = rg ∷ ce
  pe0 = ph ∷ pe
  mv0 = (zero , obj rg) ∷ mv
  full = split-keep-move zero ph th rg rest ce pe mv km tail
  tagq = spawn-reply-tag ph th pa rg rest ce0 pe0 mv0 km full proto
  pcode = pr (go (protoTag (obj r) pa) pe0 eth d dm)
  lkPost = bind-promotes h ps i r env k cenv eth d dm p t lk ctlq refl proto ng uniq bq
  parent = record p1 { ctl = pcode }

  fromBind : bind1 (sys h ps) i ≡ just t →
              ∃ λ u → spawn1 t i ≡ just u × lookup (procs u) i ≡ just parent
  fromBind eq rewrite lk | ctlq | proto | ng | uniq = finish eq
    where
    finish : (setProc ps i c0 >>= λ ps' → just (sys h ps')) ≡ just t →
             ∃ λ u → spawn1 t i ≡ just u × lookup (procs u) i ≡ just parent
    finish eq2 with setProc ps i c0
    ... | nothing = no eq2
      where
      no : nothing ≡ just t →
           ∃ λ u → spawn1 t i ≡ just u × lookup (procs u) i ≡ just parent
      no ()
    ... | just ps' = yes eq2
      where
      yes : just (sys h ps') ≡ just t →
            ∃ λ u → spawn1 t i ≡ just u × lookup (procs u) i ≡ just parent
      yes refl =
        let ps1 , spe = setProc-just ps' i p1 pcode lkPost
            child = proc (length ps') ready [] [] (pr (go ch ce0 [] [] []))
            u = sys (snoc h (nat zero)) (ps1 ++ child ∷ [])
        in u , spawn-at h ps' i p1 (keep th) ch pa env' eth d dm
                 ce0 pe0 mv0 (obj r) ps1 lkPost refl full tagq spe ,
             lookup-++-just ps1 (child ∷ []) i parent
               (setProc-lookup ps' i pcode p1 ps1 lkPost spe)

-- Top-level so a proof can pass the process it found. `done1` is
-- this function after lookup. The control match is the whole story:
-- an already `pstDone` process still ends.
doneStep : List Obj → List Proc → ℕ → Proc → Ctl → Maybe Sys
doneStep h ps i p (pr (go {n} done _ eth d dm)) =
  let p' = record p { state = pstDone ; roots = [] ; ctl = pr (go {n} done [] eth d dm) }
  in update i p' ps >>= λ ps' → just (sys h ps')
doneStep _ _ _ _ _ = nothing

done1 : Sys → ℕ → Maybe Sys
done1 (sys h ps) i =
  lookup ps i >>= λ p →
  doneStep h ps i p (ctl p)

------------------------------------------------------------------------
-- v1b step. `lift` is every v0/v1a step, including atomic send.
------------------------------------------------------------------------

data PStep : Sys → Sys → Set where
  p-lift    : ∀ {s t} → Step s t → PStep s t
  p-spawn   : ∀ {s i t} → spawn1 s i ≡ just t → PStep s t
  p-emit    : ∀ {s i t} → emit1 s i ≡ just t → PStep s t
  p-deliver : ∀ {s i t} → deliver1 s i ≡ just t → PStep s t
  p-recv    : ∀ {s i t} → recv1 s i ≡ just t → PStep s t
  p-await   : ∀ {s i t} → await1 s i ≡ just t → PStep s t
  p-arm     : ∀ {s i t} → arm1 s i ≡ just t → PStep s t
  p-flush   : ∀ {s i t} → flush1 s i ≡ just t → PStep s t
  p-npeek   : ∀ {s i t} → npeek1 s i ≡ just t → PStep s t
  p-ndemon  : ∀ {s i t} → ndemon1 s i ≡ just t → PStep s t
  p-seq     : ∀ {s i t} → seq1 s i ≡ just t → PStep s t
  p-bind    : ∀ {s i t} → bind1 s i ≡ just t → PStep s t
  p-done    : ∀ {s i t} → done1 s i ≡ just t → PStep s t

data PStep* : Sys → Sys → Set where
  pdone : ∀ {s} → PStep* s s
  pmore : ∀ {s t u} → PStep s t → PStep* t u → PStep* s u
