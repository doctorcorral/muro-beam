------------------------------------------------------------------------
-- No stray reply.
--
-- A count of zero for an in-bounds object is preserved by every PStep.
-- A mailbox message is a reference in refsOf, so once that count is zero
-- the mailbox cannot hold the tag. flush and a consuming await establish
-- the count by blanking every payload that holds the tag (a suc↑ or a clo
-- becomes nat 0) and then scrubbing the non-edge copies. The mailbox fact
-- is unchanged: after that step, count τ (refsOf t) ≡ 0, and every later
-- PStep* keeps the mailbox clear of τ.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Stray where

open import Data.Bool.Base using (Bool; true; false; not; _∨_; if_then_else_)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _≡ᵇ_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (run)
open import Muro.Grade using
  ( Grade; g0; gω; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch )

open import MuroBeam.Grade using
  ( selfKept; isZeroGrade; isG1; kind; Kind; Kmove; Kcopy )
open import MuroBeam.Heap using
  ( Obj; cell; live; Val; nat; suc↑; clo; Ref; ref; obj; checked; residual
  ; repl; count; kids; payload; edgeRefs; spendRef; spendRef-obj
  ; count-++ ; removeAt-count )
open import MuroBeam.Lib using
  ( ⊥; ⊥-elim; ≤-step; ≤-subst
  ; +-identityʳ; +-zero
  ; ≡ᵇ-sym; ≡ᵇ-cong; ≡ᵇ-refl; ≡ᵇ-sound; <≡ᵇ-false
  ; ext; ext-0
  ; lookup; update; mapCons; removeAt
  ; ++-assoc; ++-identityʳ )
open import MuroBeam.Process using
  ( Proc; proc; PState; ready; waiting; Sys; sys; heap; procs
  ; ctl; Ctl; idle; ev; rv; pr
  ; Frame; ar; fn; su; mt; bd; saved
  ; roots; inbox; state; Msg; msg; mapRef
  ; refsP; refsPs; refsOf; ctlRefs; ctlRefsPs; framesRefs; frameRefs
  ; preOf; mapSys; post; putRoot; setProc; install; pass; snoc
  ; freshRef; regrade; payloadAt; setPayload; poke; length-poke
  ; deref; alloc; reuse; eval1; evalHere; evalTm; evalRet
  ; useVar; beta; onMatch
  ; rootAt; derefAt; derefSpent; recvAt; recvInbox; addRoot
  ; sendFrom; sendTaken; dropRoot; dispatch; addMsg
  ; reuseFrom; reuseOk; anyG1; badG1; predComp
  ; ctlEq-putRoot; ctlEq-update )
  renaming (done to pstDone; send to vsend; recv to vrecv)
open import MuroBeam.Collect using
  ( Step; step-deref; step-send; step-recv; step-alloc; step-reuse
  ; step-eval; step-collect
  ; collect; apply; markVec; clean )
open import MuroBeam.PSyntax using
  ( Thin; t[]; keep; skip
  ; PTm; done; send; recv; spawn; seq; await; ignore; nignore
  ; awaitT; ignoreT; flushT; ncheckT; ndemonT
  ; Flight; flight; flightRef; flightRefs; Code; go; codeRefs
  ; applyMoves )
open import MuroBeam.PRun using
  ( PStep; PStep*; p-lift; p-spawn; p-emit; p-deliver; p-recv
  ; p-await; p-arm; p-flush; p-npeek; p-ndemon; p-seq; p-bind; p-done
  ; pmore; pdone
  ; spawn1; emit1; deliver1; recv1; recvStep; await1; awaitOn; awaitPark
  ; arm1; flush1; npeek1; npeekOn; ndemon1
  ; seq1; bind1; done1
  ; splitGo; Split; placeholder; blocked
  ; pullCode; pullFrames; pullCtl; wake
  ; setCtlSt; scrubOne; scrubRefs; scrubCode; scrubFrame; scrubFrames; scrubCtl
  ; scrubProc; dropRefs; dropMsgs; dropFlights
  ; finishFlush; finishAwait; finishPeek; consume
  ; blankEdges; blank-length; blank-count-≤; blank-edge-0
  ; mailHas; deadAt; inboxHas; deadInCtl; hasTag
  ; _>>=_ )
open import MuroBeam.Unique using
  ( just-inj; nothing≢just; stuck-just; pass-ok; true≢false
  ; length-snoc; length-set; length-apply
  ; put-count; upd-count; post-count; snoc-root-count; recv-refs
  ; keep-on; refs-count; set-refsPs
  ; edge-nat; edge-suc; edge-clo; edge-at; EdgeAt; eat
  ; sub-zero; count-edge; count-filter; ctl-clean; refs-cleaned
  ; root-lookup )

------------------------------------------------------------------------
-- Completion of a reply. The mailbox fact is the count. dead records
-- that await or flush, not a mere demonitor, is what finished it.
------------------------------------------------------------------------

data ReplyDone (s : Sys) (i τ : ℕ) : Set where
  replied :
      count τ (refsOf s) ≡ 0
    → τ < length (heap s)
    → deadAt (procs s) i τ ≡ true
    → ReplyDone s i τ

------------------------------------------------------------------------
-- Handover view. Moved slots become the one shared placeholder.
------------------------------------------------------------------------

data Hand (ph : Ref) : List Ref → List Ref → List Ref → Set where
  hn-nil  : Hand ph [] [] []
  hn-skip : ∀ {r rs ce pe} → Hand ph rs ce pe → Hand ph (r ∷ rs) ce (r ∷ pe)
  hn-move : ∀ {r rs ce pe} → kind (checked r) ≡ just Kmove →
            Hand ph rs ce pe → Hand ph (r ∷ rs) (r ∷ ce) (ph ∷ pe)
  hn-copy : ∀ {r rs ce pe} → kind (checked r) ≡ just Kcopy →
            Hand ph rs ce pe → Hand ph (r ∷ rs) (r ∷ ce) (r ∷ pe)

split-hand : ∀ {m n} i ph (th : Thin m n) rs ce pe mv →
  splitGo i ph th rs ≡ just (ce , pe , mv) →
  Hand ph rs ce pe
split-hand i ph t[] [] .[] .[] .[] refl = hn-nil
split-hand i ph (skip th) (r ∷ rs) ce pe mv eq =
  kont (splitGo (suc i) ph th rs) eq refl
  where
  kont : (m : Maybe Split) →
         (m >>= λ (ce0 , pe0 , mv0) → just (ce0 , r ∷ pe0 , mv0)) ≡ just (ce , pe , mv) →
         splitGo (suc i) ph th rs ≡ m →
         Hand ph (r ∷ rs) ce pe
  kont nothing () _
  kont (just (ce0 , pe0 , mv0)) refl eqm =
    hn-skip (split-hand (suc i) ph th rs ce0 pe0 mv0 eqm)
split-hand i ph (keep th) (r ∷ rs) ce pe mv eq =
  klass (kind (checked r)) eq refl
  where
  klass : (k : Maybe Kind) →
          splitGo i ph (keep th) (r ∷ rs) ≡ just (ce , pe , mv) →
          kind (checked r) ≡ k →
          Hand ph (r ∷ rs) ce pe
  klass nothing eqk ek rewrite ek with eqk
  ... | ()
  klass (just Kmove) eqk ek rewrite ek =
    kont (splitGo (suc i) ph th rs) eqk refl
    where
    kont : (m : Maybe Split) →
           (m >>= λ (ce0 , pe0 , mv0) →
              just (r ∷ ce0 , ph ∷ pe0 , (i , obj r) ∷ mv0)) ≡ just (ce , pe , mv) →
           splitGo (suc i) ph th rs ≡ m →
           Hand ph (r ∷ rs) ce pe
    kont nothing () _
    kont (just (ce0 , pe0 , mv0)) refl eqm =
      hn-move ek (split-hand (suc i) ph th rs ce0 pe0 mv0 eqm)
  klass (just Kcopy) eqk ek rewrite ek =
    kont (splitGo (suc i) ph th rs) eqk refl
    where
    kont : (m : Maybe Split) →
           (m >>= λ (ce0 , pe0 , mv0) → just (r ∷ ce0 , r ∷ pe0 , mv0)) ≡ just (ce , pe , mv) →
           splitGo (suc i) ph th rs ≡ m →
           Hand ph (r ∷ rs) ce pe
    kont nothing () _
    kont (just (ce0 , pe0 , mv0)) refl eqm =
      hn-copy ek (split-hand (suc i) ph th rs ce0 pe0 mv0 eqm)
split-hand _ _ t[] (_ ∷ _) _ _ _ ()
split-hand _ _ (skip _) [] _ _ _ ()
split-hand _ _ (keep _) [] _ _ _ ()

refsPs-++ : ∀ xs ys → refsPs (xs ++ ys) ≡ refsPs xs ++ refsPs ys
refsPs-++ [] ys = refl
refsPs-++ (p ∷ xs) ys =
  trans (cong (refsP p ++_) (refsPs-++ xs ys))
        (sym (++-assoc (refsP p) (refsPs xs) (refsPs ys)))

ctlRefsPs-++ : ∀ xs ys → ctlRefsPs (xs ++ ys) ≡ ctlRefsPs xs ++ ctlRefsPs ys
ctlRefsPs-++ [] ys = refl
ctlRefsPs-++ (p ∷ xs) ys =
  trans (cong (ctlRefs (ctl p) ++_) (ctlRefsPs-++ xs ys))
        (sym (++-assoc (ctlRefs (ctl p)) (ctlRefsPs xs) (ctlRefsPs ys)))

flightRefs-++ : ∀ xs ys → flightRefs (xs ++ ys) ≡ flightRefs xs ++ flightRefs ys
flightRefs-++ [] ys = refl
flightRefs-++ (flight j r ∷ xs) ys rewrite flightRefs-++ xs ys = refl

------------------------------------------------------------------------
-- One tag. Every lemma below is about this object index.
------------------------------------------------------------------------

module Preserve (τ : ℕ) where

  ≤-zero : ∀ {n} → n ≤ zero → n ≡ zero
  ≤-zero z≤n = refl

  le0 : ∀ {m n} → m ≤ n → n ≡ zero → m ≡ zero
  le0 le eq = ≤-zero (≤-subst le eq)

  len-miss : ∀ {n} → τ < n → (n ≡ᵇ τ) ≡ false
  len-miss lt = trans (≡ᵇ-sym _ τ) (<≡ᵇ-false lt)

  0++ : ∀ xs ys → count τ xs ≡ 0 → count τ ys ≡ 0 → count τ (xs ++ ys) ≡ 0
  0++ xs ys zx zy rewrite count-++ τ xs ys | zx | zy = refl

  ++0 : ∀ xs ys → count τ (xs ++ ys) ≡ 0 → count τ xs ≡ 0 × count τ ys ≡ 0
  ++0 xs ys eq =
    +-zero (count τ xs) (count τ ys) (trans (sym (count-++ τ xs ys)) eq)

  cons0 : ∀ r rs → (obj r ≡ᵇ τ) ≡ false → count τ rs ≡ 0 → count τ (r ∷ rs) ≡ 0
  cons0 r rs nr zr rewrite nr = zr

  head0 : ∀ r rs → count τ (r ∷ rs) ≡ 0 → (obj r ≡ᵇ τ) ≡ false × count τ rs ≡ 0
  head0 r rs eq =
    let ze , zr = +-zero (ext (obj r ≡ᵇ τ)) (count τ rs) eq
    in ext-0 (obj r ≡ᵇ τ) ze , zr

  count-idʳ : ∀ xs → count τ (xs ++ []) ≡ count τ xs
  count-idʳ xs rewrite count-++ τ xs [] | +-identityʳ (count τ xs) = refl

  parts : ∀ h ps → count τ (refsOf (sys h ps)) ≡ 0 →
          count τ (edgeRefs h) ≡ 0 × count τ (ctlRefsPs ps) ≡ 0 × count τ (refsPs ps) ≡ 0
  parts h ps eq rewrite refs-count τ h ps =
    let ec , zr = +-zero (count τ (edgeRefs h) + count τ (ctlRefsPs ps)) (count τ (refsPs ps)) eq
        ze , zc = +-zero (count τ (edgeRefs h)) (count τ (ctlRefsPs ps)) ec
    in ze , zc , zr

  refs0 : ∀ h ps →
          count τ (edgeRefs h) ≡ 0 →
          count τ (ctlRefsPs ps) ≡ 0 →
          count τ (refsPs ps) ≡ 0 →
          count τ (refsOf (sys h ps)) ≡ 0
  refs0 h ps ze zc zr rewrite refs-count τ h ps | ze | zc | zr = refl

  lookup-ctl0 : ∀ i ps p →
    lookup ps i ≡ just p →
    count τ (ctlRefsPs ps) ≡ 0 →
    count τ (ctlRefs (ctl p)) ≡ 0
  lookup-ctl0 _ [] _ () _
  lookup-ctl0 zero (p ∷ ps) .p refl z = proj₁ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) z)
  lookup-ctl0 (suc i) (p ∷ ps) q eq z =
    lookup-ctl0 i ps q eq (proj₂ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) z))

  ctl0 : ∀ {c c'} → c ≡ c' → count τ (ctlRefs c) ≡ 0 → count τ (ctlRefs c') ≡ 0
  ctl0 eq z = subst (λ c0 → count τ (ctlRefs c0) ≡ 0) eq z

  lookup-refs0 : ∀ i ps p →
    lookup ps i ≡ just p →
    count τ (refsPs ps) ≡ 0 →
    count τ (refsP p) ≡ 0
  lookup-refs0 _ [] _ () _
  lookup-refs0 zero (p ∷ ps) .p refl z = proj₁ (++0 (refsP p) (refsPs ps) z)
  lookup-refs0 (suc i) (p ∷ ps) q eq z =
    lookup-refs0 i ps q eq (proj₂ (++0 (refsP p) (refsPs ps) z))

  lookup-miss : ∀ rs n r → lookup rs n ≡ just r → count τ rs ≡ 0 → (obj r ≡ᵇ τ) ≡ false
  lookup-miss [] _ _ () _
  lookup-miss (x ∷ xs) zero .x refl eq = proj₁ (head0 x xs eq)
  lookup-miss (x ∷ xs) (suc n) r eq z =
    lookup-miss xs n r eq (proj₂ (head0 x xs z))

  repl-keep0 : ∀ n xs r →
    count τ xs ≡ 0 → (obj r ≡ᵇ τ) ≡ false → count τ (repl n r xs) ≡ 0
  repl-keep0 _ [] _ _ _ = refl
  repl-keep0 zero (x ∷ xs) r eq nr =
    cons0 r xs nr (proj₂ (head0 x xs eq))
  repl-keep0 (suc n) (x ∷ xs) r eq nr =
    let nr0 , zxs = head0 x xs eq
    in cons0 x (repl n r xs) nr0 (repl-keep0 n xs r zxs nr)

  fit-snoc : ∀ h v → τ < length h → τ < length (snoc h v)
  fit-snoc h v lt rewrite length-snoc h (cell v live) = ≤-step lt

  fit-poke : ∀ h k v → τ < length h → τ < length (poke h k v)
  fit-poke h k v lt rewrite length-poke h k v = lt

  fit-set : ∀ h k v → τ < length h → τ < length (setPayload h k v)
  fit-set h k v lt rewrite length-set h k v = lt

  fit-apply : ∀ bs h → τ < length h → τ < length (apply bs h)
  fit-apply bs h lt rewrite length-apply bs h = lt

  setProc-ctl0 : ∀ i ps c ps' →
    count τ (ctlRefsPs ps) ≡ 0 →
    count τ (ctlRefs c) ≡ 0 →
    setProc ps i c ≡ just ps' →
    count τ (ctlRefsPs ps') ≡ 0
  setProc-ctl0 _ [] _ _ _ _ ()
  setProc-ctl0 zero (p ∷ ps) c .(record p { ctl = c } ∷ ps) zps zc refl =
    0++ (ctlRefs c) (ctlRefsPs ps) zc (proj₂ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) zps))
  setProc-ctl0 (suc i) (p ∷ ps) c ps' zps zc eq =
    kont (setProc ps i c) eq refl
    where
    zh = proj₁ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) zps)
    zt = proj₂ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) zps)
    kont : (m : Maybe (List Proc)) → mapCons p m ≡ just ps' → setProc ps i c ≡ m →
           count τ (ctlRefsPs ps') ≡ 0
    kont nothing () _
    kont (just qs) refl eqm =
      0++ (ctlRefs (ctl p)) (ctlRefsPs qs) zh (setProc-ctl0 i ps c qs zt zc eqm)

  setCtl-refsEq : ∀ i ps c st ps' →
    setCtlSt ps i c st ≡ just ps' → refsPs ps' ≡ refsPs ps
  setCtl-refsEq _ [] _ _ _ ()
  setCtl-refsEq zero (p ∷ ps) c st .(record p { ctl = c ; state = st } ∷ ps) refl = refl
  setCtl-refsEq (suc i) (p ∷ ps) c st ps' eq = kont (setCtlSt ps i c st) eq refl
    where
    kont : (m : Maybe (List Proc)) → mapCons p m ≡ just ps' → setCtlSt ps i c st ≡ m →
           refsPs ps' ≡ refsPs (p ∷ ps)
    kont nothing () _
    kont (just qs) refl eqm = cong (refsP p ++_) (setCtl-refsEq i ps c st qs eqm)

  setCtl-ctl0 : ∀ i ps c st ps' →
    count τ (ctlRefsPs ps) ≡ 0 →
    count τ (ctlRefs c) ≡ 0 →
    setCtlSt ps i c st ≡ just ps' →
    count τ (ctlRefsPs ps') ≡ 0
  setCtl-ctl0 _ [] _ _ _ _ _ ()
  setCtl-ctl0 zero (p ∷ ps) c st .(record p { ctl = c ; state = st } ∷ ps) zps zc refl =
    0++ (ctlRefs c) (ctlRefsPs ps) zc (proj₂ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) zps))
  setCtl-ctl0 (suc i) (p ∷ ps) c st ps' zps zc eq =
    kont (setCtlSt ps i c st) eq refl
    where
    zh = proj₁ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) zps)
    zt = proj₂ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) zps)
    kont : (m : Maybe (List Proc)) → mapCons p m ≡ just ps' → setCtlSt ps i c st ≡ m →
           count τ (ctlRefsPs ps') ≡ 0
    kont nothing () _
    kont (just qs) refl eqm =
      0++ (ctlRefs (ctl p)) (ctlRefsPs qs) zh (setCtl-ctl0 i ps c st qs zt zc eqm)

  setCtl-dead : ∀ i ps c st ps' →
    setCtlSt ps i c st ≡ just ps' →
    hasTag τ (deadInCtl c) ≡ true →
    deadAt ps' i τ ≡ true
  setCtl-dead _ [] _ _ _ () _
  setCtl-dead zero (p ∷ ps) c st .(record p { ctl = c ; state = st } ∷ ps) refl ht
    rewrite ht = refl
  setCtl-dead (suc i) (p ∷ ps) c st ps' eq ht =
    kont (setCtlSt ps i c st) eq refl
    where
    kont : (m : Maybe (List Proc)) → mapCons p m ≡ just ps' → setCtlSt ps i c st ≡ m →
           deadAt ps' (suc i) τ ≡ true
    kont nothing () _
    kont (just qs) refl eqm = setCtl-dead i ps c st qs eqm ht

  upd-both0 : ∀ n ps p p' ps' →
    lookup ps n ≡ just p →
    update n p' ps ≡ just ps' →
    count τ (ctlRefs (ctl p')) ≡ 0 →
    count τ (refsP p') ≡ 0 →
    count τ (ctlRefsPs ps) ≡ 0 →
    count τ (refsPs ps) ≡ 0 →
    count τ (ctlRefsPs ps') ≡ 0 × count τ (refsPs ps') ≡ 0
  upd-both0 _ [] _ _ _ () _ _ _ _ _
  upd-both0 zero (p ∷ ps) .p p' .(p' ∷ ps) refl refl zc' zr' zps zrs =
    0++ (ctlRefs (ctl p')) (ctlRefsPs ps) zc' (proj₂ (++0 (ctlRefs (ctl p)) (ctlRefsPs ps) zps))
    , 0++ (refsP p') (refsPs ps) zr' (proj₂ (++0 (refsP p) (refsPs ps) zrs))
  upd-both0 (suc n) (q ∷ ps) p p' ps' lk eq zc' zr' zps zrs =
    kont (update n p' ps) eq refl
    where
    zh = proj₁ (++0 (ctlRefs (ctl q)) (ctlRefsPs ps) zps)
    zt = proj₂ (++0 (ctlRefs (ctl q)) (ctlRefsPs ps) zps)
    rh = proj₁ (++0 (refsP q) (refsPs ps) zrs)
    rt = proj₂ (++0 (refsP q) (refsPs ps) zrs)
    kont : (m : Maybe (List Proc)) → mapCons q m ≡ just ps' → update n p' ps ≡ m →
           count τ (ctlRefsPs ps') ≡ 0 × count τ (refsPs ps') ≡ 0
    kont nothing () _
    kont (just qs) refl eqm =
      let zc , zr = upd-both0 n ps p p' qs lk eqm zc' zr' zt rt
      in 0++ (ctlRefs (ctl q)) (ctlRefsPs qs) zh zc
       , 0++ (refsP q) (refsPs qs) rh zr

  ------------------------------------------------------------------------
  -- Scrub. keep: an absent tag stays absent. kill: the scrub tag is
  -- forced out of every non-edge position.
  ------------------------------------------------------------------------

  scrubOne-keep : ∀ τf ph r →
    (obj r ≡ᵇ τ) ≡ false → (obj ph ≡ᵇ τ) ≡ false →
    (obj (scrubOne τf ph r) ≡ᵇ τ) ≡ false
  scrubOne-keep τf ph r nr np with obj r ≡ᵇ τf
  ... | true  = np
  ... | false = nr

  scrubRefs-keep : ∀ τf ph rs →
    (obj ph ≡ᵇ τ) ≡ false → count τ rs ≡ 0 → count τ (scrubRefs τf ph rs) ≡ 0
  scrubRefs-keep _ _ [] _ _ = refl
  scrubRefs-keep τf ph (r ∷ rs) np eq =
    let nr , zrs = head0 r rs eq
    in cons0 (scrubOne τf ph r) (scrubRefs τf ph rs) (scrubOne-keep τf ph r nr np)
         (scrubRefs-keep τf ph rs np zrs)

  dropRefs-keep : ∀ τf rs → count τ rs ≡ 0 → count τ (dropRefs τf rs) ≡ 0
  dropRefs-keep _ [] _ = refl
  dropRefs-keep τf (r ∷ rs) eq with obj r ≡ᵇ τf
  ... | true  = dropRefs-keep τf rs (proj₂ (head0 r rs eq))
  ... | false =
    cons0 r (dropRefs τf rs) (proj₁ (head0 r rs eq))
      (dropRefs-keep τf rs (proj₂ (head0 r rs eq)))

  dropMsgs-keep : ∀ τf ms → count τ (mapRef ms) ≡ 0 → count τ (mapRef (dropMsgs τf ms)) ≡ 0
  dropMsgs-keep _ [] _ = refl
  dropMsgs-keep τf (msg r ∷ ms) eq with obj r ≡ᵇ τf
  ... | true  = dropMsgs-keep τf ms (proj₂ (head0 r (mapRef ms) eq))
  ... | false =
    cons0 r (mapRef (dropMsgs τf ms)) (proj₁ (head0 r (mapRef ms) eq))
      (dropMsgs-keep τf ms (proj₂ (head0 r (mapRef ms) eq)))

  dropFlights-keep : ∀ τf fs → count τ (flightRefs fs) ≡ 0 →
                     count τ (flightRefs (dropFlights τf fs)) ≡ 0
  dropFlights-keep _ [] _ = refl
  dropFlights-keep τf (flight j r ∷ fs) eq with obj r ≡ᵇ τf
  ... | true  = dropFlights-keep τf fs (proj₂ (head0 r (flightRefs fs) eq))
  ... | false =
    cons0 r (flightRefs (dropFlights τf fs)) (proj₁ (head0 r (flightRefs fs) eq))
      (dropFlights-keep τf fs (proj₂ (head0 r (flightRefs fs) eq)))

  scrubFrame-keep : ∀ τf ph k →
    (obj ph ≡ᵇ τ) ≡ false → count τ (frameRefs k) ≡ 0 →
    count τ (frameRefs (scrubFrame τf ph k)) ≡ 0
  scrubCode-keep : ∀ τf ph c →
    (obj ph ≡ᵇ τ) ≡ false → count τ (codeRefs c) ≡ 0 →
    count τ (codeRefs (scrubCode τf ph c)) ≡ 0
  scrubFrames-keep : ∀ τf ph ks →
    (obj ph ≡ᵇ τ) ≡ false → count τ (framesRefs ks) ≡ 0 →
    count τ (framesRefs (scrubFrames τf ph ks)) ≡ 0

  scrubCode-keep τf ph (go tm env eth d dm) np eq =
    let ze , zf = ++0 env (flightRefs eth) eq
    in 0++ (scrubRefs τf ph env) (flightRefs (dropFlights τf eth))
         (scrubRefs-keep τf ph env np ze) (dropFlights-keep τf eth zf)

  scrubFrame-keep τf ph (fn r) np eq =
    cons0 (scrubOne τf ph r) [] (scrubOne-keep τf ph r (proj₁ (head0 r [] eq)) np) refl
  scrubFrame-keep τf ph (bd env) np eq = scrubRefs-keep τf ph env np eq
  scrubFrame-keep τf ph (saved c) np eq = scrubCode-keep τf ph c np eq
  scrubFrame-keep _ _ (ar _) _ eq = eq
  scrubFrame-keep _ _ su _ eq = eq
  scrubFrame-keep _ _ (mt _ _ _) _ eq = eq

  scrubFrames-keep _ _ [] _ _ = refl
  scrubFrames-keep τf ph (k ∷ ks) np eq =
    let zk , zks = ++0 (frameRefs k) (framesRefs ks) eq
    in 0++ (frameRefs (scrubFrame τf ph k)) (framesRefs (scrubFrames τf ph ks))
         (scrubFrame-keep τf ph k np zk) (scrubFrames-keep τf ph ks np zks)

  scrubCtl-keep : ∀ τf ph c →
    (obj ph ≡ᵇ τ) ≡ false → count τ (ctlRefs c) ≡ 0 →
    count τ (ctlRefs (scrubCtl τf ph c)) ≡ 0
  scrubCtl-keep _ _ idle _ eq = eq
  scrubCtl-keep τf ph (ev t e k) np eq =
    let ze , zf = ++0 e (framesRefs k) eq
    in 0++ (scrubRefs τf ph e) (framesRefs (scrubFrames τf ph k))
         (scrubRefs-keep τf ph e np ze) (scrubFrames-keep τf ph k np zf)
  scrubCtl-keep τf ph (rv r e k) np eq =
    let nr , zrest = head0 r (e ++ framesRefs k) eq
        ze , zf = ++0 e (framesRefs k) zrest
    in cons0 (scrubOne τf ph r) (scrubRefs τf ph e ++ framesRefs (scrubFrames τf ph k))
         (scrubOne-keep τf ph r nr np)
         (0++ (scrubRefs τf ph e) (framesRefs (scrubFrames τf ph k))
            (scrubRefs-keep τf ph e np ze) (scrubFrames-keep τf ph k np zf))
  scrubCtl-keep τf ph (pr c) np eq = scrubCode-keep τf ph c np eq

  refsP-keep : ∀ τf p → count τ (refsP p) ≡ 0 → count τ (refsP (scrubProc τf (placeholder []) p)) ≡ 0
  refsP-keep τf p eq =
    let zr , zi = ++0 (roots p) (mapRef (inbox p)) eq
    in 0++ (dropRefs τf (roots p)) (mapRef (dropMsgs τf (inbox p)))
         (dropRefs-keep τf (roots p) zr) (dropMsgs-keep τf (inbox p) zi)

  -- placeholder is irrelevant for roots and messages; the real one is passed for control.
  refsP-keep' : ∀ τf ph p → count τ (refsP p) ≡ 0 → count τ (refsP (scrubProc τf ph p)) ≡ 0
  refsP-keep' τf ph p eq =
    let zr , zi = ++0 (roots p) (mapRef (inbox p)) eq
    in 0++ (dropRefs τf (roots p)) (mapRef (dropMsgs τf (inbox p)))
         (dropRefs-keep τf (roots p) zr) (dropMsgs-keep τf (inbox p) zi)

  ctlKeep : ∀ τf ph ps →
    (obj ph ≡ᵇ τ) ≡ false → count τ (ctlRefsPs ps) ≡ 0 →
    count τ (ctlRefsPs (map (scrubProc τf ph) ps)) ≡ 0
  ctlKeep _ _ [] _ _ = refl
  ctlKeep τf ph (p ∷ ps) np eq =
    let zh , zt = ++0 (ctlRefs (ctl p)) (ctlRefsPs ps) eq
    in 0++ (ctlRefs (ctl (scrubProc τf ph p))) (ctlRefsPs (map (scrubProc τf ph) ps))
         (scrubCtl-keep τf ph (ctl p) np zh) (ctlKeep τf ph ps np zt)

  refsKeep : ∀ τf ph ps →
    count τ (refsPs ps) ≡ 0 →
    count τ (refsPs (map (scrubProc τf ph) ps)) ≡ 0
  refsKeep _ _ [] _ = refl
  refsKeep τf ph (p ∷ ps) eq =
    let zh , zt = ++0 (refsP p) (refsPs ps) eq
    in 0++ (refsP (scrubProc τf ph p)) (refsPs (map (scrubProc τf ph) ps))
         (refsP-keep' τf ph p zh) (refsKeep τf ph ps zt)

  scrubOne-kill : ∀ ph r → (obj ph ≡ᵇ τ) ≡ false → (obj (scrubOne τ ph r) ≡ᵇ τ) ≡ false
  scrubOne-kill ph r np with obj r ≡ᵇ τ in eq
  ... | true  = np
  ... | false = eq

  scrubRefs-kill : ∀ ph rs → (obj ph ≡ᵇ τ) ≡ false → count τ (scrubRefs τ ph rs) ≡ 0
  scrubRefs-kill _ [] _ = refl
  scrubRefs-kill ph (r ∷ rs) np =
    cons0 (scrubOne τ ph r) (scrubRefs τ ph rs) (scrubOne-kill ph r np) (scrubRefs-kill ph rs np)

  dropRefs-kill : ∀ rs → count τ (dropRefs τ rs) ≡ 0
  dropRefs-kill [] = refl
  dropRefs-kill (r ∷ rs) with obj r ≡ᵇ τ in eq
  ... | true  = dropRefs-kill rs
  ... | false = cons0 r (dropRefs τ rs) eq (dropRefs-kill rs)

  dropMsgs-kill : ∀ ms → count τ (mapRef (dropMsgs τ ms)) ≡ 0
  dropMsgs-kill [] = refl
  dropMsgs-kill (msg r ∷ ms) with obj r ≡ᵇ τ in eq
  ... | true  = dropMsgs-kill ms
  ... | false = cons0 r (mapRef (dropMsgs τ ms)) eq (dropMsgs-kill ms)

  dropFlights-kill : ∀ fs → count τ (flightRefs (dropFlights τ fs)) ≡ 0
  dropFlights-kill [] = refl
  dropFlights-kill (flight j r ∷ fs) with obj r ≡ᵇ τ in eq
  ... | true  = dropFlights-kill fs
  ... | false = cons0 r (flightRefs (dropFlights τ fs)) eq (dropFlights-kill fs)

  scrubCode-kill : ∀ ph c → (obj ph ≡ᵇ τ) ≡ false → count τ (codeRefs (scrubCode τ ph c)) ≡ 0
  scrubFrame-kill : ∀ ph k → (obj ph ≡ᵇ τ) ≡ false → count τ (frameRefs (scrubFrame τ ph k)) ≡ 0
  scrubFrames-kill : ∀ ph ks → (obj ph ≡ᵇ τ) ≡ false → count τ (framesRefs (scrubFrames τ ph ks)) ≡ 0

  scrubCode-kill ph (go tm env eth d dm) np =
    0++ (scrubRefs τ ph env) (flightRefs (dropFlights τ eth))
      (scrubRefs-kill ph env np) (dropFlights-kill eth)

  scrubFrame-kill ph (fn r) np = cons0 (scrubOne τ ph r) [] (scrubOne-kill ph r np) refl
  scrubFrame-kill ph (bd env) np = scrubRefs-kill ph env np
  scrubFrame-kill ph (saved c) np = scrubCode-kill ph c np
  scrubFrame-kill _ (ar _) _ = refl
  scrubFrame-kill _ su _ = refl
  scrubFrame-kill _ (mt _ _ _) _ = refl

  scrubFrames-kill _ [] _ = refl
  scrubFrames-kill ph (k ∷ ks) np =
    0++ (frameRefs (scrubFrame τ ph k)) (framesRefs (scrubFrames τ ph ks))
      (scrubFrame-kill ph k np) (scrubFrames-kill ph ks np)

  scrubCtl-kill : ∀ ph c → (obj ph ≡ᵇ τ) ≡ false → count τ (ctlRefs (scrubCtl τ ph c)) ≡ 0
  scrubCtl-kill _ idle _ = refl
  scrubCtl-kill ph (ev t e k) np =
    0++ (scrubRefs τ ph e) (framesRefs (scrubFrames τ ph k))
      (scrubRefs-kill ph e np) (scrubFrames-kill ph k np)
  scrubCtl-kill ph (rv r e k) np =
    cons0 (scrubOne τ ph r) (scrubRefs τ ph e ++ framesRefs (scrubFrames τ ph k))
      (scrubOne-kill ph r np)
      (0++ (scrubRefs τ ph e) (framesRefs (scrubFrames τ ph k))
         (scrubRefs-kill ph e np) (scrubFrames-kill ph k np))
  scrubCtl-kill ph (pr c) np = scrubCode-kill ph c np

  refsP-kill : ∀ ph p → count τ (refsP (scrubProc τ ph p)) ≡ 0
  refsP-kill ph p =
    0++ (dropRefs τ (roots p)) (mapRef (dropMsgs τ (inbox p)))
      (dropRefs-kill (roots p)) (dropMsgs-kill (inbox p))

  ctlKill : ∀ ph ps → (obj ph ≡ᵇ τ) ≡ false →
            count τ (ctlRefsPs (map (scrubProc τ ph) ps)) ≡ 0
  ctlKill _ [] _ = refl
  ctlKill ph (p ∷ ps) np =
    0++ (ctlRefs (ctl (scrubProc τ ph p))) (ctlRefsPs (map (scrubProc τ ph) ps))
      (scrubCtl-kill ph (ctl p) np) (ctlKill ph ps np)

  refsKill : ∀ ph ps → count τ (refsPs (map (scrubProc τ ph) ps)) ≡ 0
  refsKill _ [] = refl
  refsKill ph (p ∷ ps) =
    0++ (refsP (scrubProc τ ph p)) (refsPs (map (scrubProc τ ph) ps))
      (refsP-kill ph p) (refsKill ph ps)

  ------------------------------------------------------------------------
  -- finish keeps the references and records the tag as dead.
  ------------------------------------------------------------------------

  finishFlush-refs : ∀ τf c c' → finishFlush τf c ≡ just c' → ctlRefs c' ≡ ctlRefs c
  finishFlush-refs τf c c' eq = walk c eq
    where
    walk : (c0 : Ctl) → finishFlush τf c0 ≡ just c' → ctlRefs c' ≡ ctlRefs c0
    walk (pr (go (flushT τ' k) env eth d dm)) eqf with τf ≡ᵇ τ'
    ... | true  = sym (cong ctlRefs (just-inj eqf))
    ... | false = stuck-just eqf
    walk (pr (go done _ _ _ _)) ()
    walk (pr (go (send _ _ _) _ _ _ _)) ()
    walk (pr (go (recv _ _ _) _ _ _ _)) ()
    walk (pr (go (spawn _ _ _) _ _ _ _)) ()
    walk (pr (go (seq _ _) _ _ _ _)) ()
    walk (pr (go (await _ _) _ _ _ _)) ()
    walk (pr (go (ignore _ _) _ _ _ _)) ()
    walk (pr (go (nignore _ _) _ _ _ _)) ()
    walk (pr (go (awaitT _ _) _ _ _ _)) ()
    walk (pr (go (ignoreT _ _) _ _ _ _)) ()
    walk (pr (go (ncheckT _ _) _ _ _ _)) ()
    walk (pr (go (ndemonT _ _) _ _ _ _)) ()
    walk idle ()
    walk (ev _ _ _) ()
    walk (rv _ _ _) ()

  finishAwait-refs : ∀ τf c c' → finishAwait τf c ≡ just c' → ctlRefs c' ≡ ctlRefs c
  finishAwait-refs τf c c' eq = walk c eq
    where
    walk : (c0 : Ctl) → finishAwait τf c0 ≡ just c' → ctlRefs c' ≡ ctlRefs c0
    walk (pr (go (awaitT τ' k) env eth d dm)) eqf with τf ≡ᵇ τ'
    ... | true  = sym (cong ctlRefs (just-inj eqf))
    ... | false = stuck-just eqf
    walk (pr (go done _ _ _ _)) ()
    walk (pr (go (send _ _ _) _ _ _ _)) ()
    walk (pr (go (recv _ _ _) _ _ _ _)) ()
    walk (pr (go (spawn _ _ _) _ _ _ _)) ()
    walk (pr (go (seq _ _) _ _ _ _)) ()
    walk (pr (go (await _ _) _ _ _ _)) ()
    walk (pr (go (ignore _ _) _ _ _ _)) ()
    walk (pr (go (nignore _ _) _ _ _ _)) ()
    walk (pr (go (flushT _ _) _ _ _ _)) ()
    walk (pr (go (ignoreT _ _) _ _ _ _)) ()
    walk (pr (go (ncheckT _ _) _ _ _ _)) ()
    walk (pr (go (ndemonT _ _) _ _ _ _)) ()
    walk idle ()
    walk (ev _ _ _) ()
    walk (rv _ _ _) ()

  finishPeek-refs : ∀ τf c c' → finishPeek τf c ≡ just c' → ctlRefs c' ≡ ctlRefs c
  finishPeek-refs τf c c' eq = walk c eq
    where
    walk : (c0 : Ctl) → finishPeek τf c0 ≡ just c' → ctlRefs c' ≡ ctlRefs c0
    walk (pr (go (ncheckT τ' k) env eth d dm)) eqf with τf ≡ᵇ τ'
    ... | true  = sym (cong ctlRefs (just-inj eqf))
    ... | false = stuck-just eqf
    walk (pr (go done _ _ _ _)) ()
    walk (pr (go (send _ _ _) _ _ _ _)) ()
    walk (pr (go (recv _ _ _) _ _ _ _)) ()
    walk (pr (go (spawn _ _ _) _ _ _ _)) ()
    walk (pr (go (seq _ _) _ _ _ _)) ()
    walk (pr (go (await _ _) _ _ _ _)) ()
    walk (pr (go (ignore _ _) _ _ _ _)) ()
    walk (pr (go (nignore _ _) _ _ _ _)) ()
    walk (pr (go (awaitT _ _) _ _ _ _)) ()
    walk (pr (go (ignoreT _ _) _ _ _ _)) ()
    walk (pr (go (flushT _ _) _ _ _ _)) ()
    walk (pr (go (ndemonT _ _) _ _ _ _)) ()
    walk idle ()
    walk (ev _ _ _) ()
    walk (rv _ _ _) ()

  tagHere : ∀ d → hasTag τ (τ ∷ d) ≡ true
  tagHere d rewrite ≡ᵇ-refl τ = refl

  finishFlush-dead : ∀ c c' → finishFlush τ c ≡ just c' → hasTag τ (deadInCtl c') ≡ true
  finishFlush-dead c c' eq = walk c eq
    where
    walk : (c0 : Ctl) → finishFlush τ c0 ≡ just c' → hasTag τ (deadInCtl c') ≡ true
    walk (pr (go (flushT τ' k) env eth d dm)) eqf with τ ≡ᵇ τ'
    ... | false = stuck-just eqf
    ... | true =
      subst (λ c1 → hasTag τ (deadInCtl c1) ≡ true) (just-inj eqf) (tagHere d)
    walk (pr (go done _ _ _ _)) ()
    walk (pr (go (send _ _ _) _ _ _ _)) ()
    walk (pr (go (recv _ _ _) _ _ _ _)) ()
    walk (pr (go (spawn _ _ _) _ _ _ _)) ()
    walk (pr (go (seq _ _) _ _ _ _)) ()
    walk (pr (go (await _ _) _ _ _ _)) ()
    walk (pr (go (ignore _ _) _ _ _ _)) ()
    walk (pr (go (nignore _ _) _ _ _ _)) ()
    walk (pr (go (awaitT _ _) _ _ _ _)) ()
    walk (pr (go (ignoreT _ _) _ _ _ _)) ()
    walk (pr (go (ncheckT _ _) _ _ _ _)) ()
    walk (pr (go (ndemonT _ _) _ _ _ _)) ()
    walk idle ()
    walk (ev _ _ _) ()
    walk (rv _ _ _) ()

  finishAwait-dead : ∀ c c' → finishAwait τ c ≡ just c' → hasTag τ (deadInCtl c') ≡ true
  finishAwait-dead c c' eq = walk c eq
    where
    walk : (c0 : Ctl) → finishAwait τ c0 ≡ just c' → hasTag τ (deadInCtl c') ≡ true
    walk (pr (go (awaitT τ' k) env eth d dm)) eqf with τ ≡ᵇ τ'
    ... | false = stuck-just eqf
    ... | true =
      subst (λ c1 → hasTag τ (deadInCtl c1) ≡ true) (just-inj eqf) (tagHere d)
    walk (pr (go done _ _ _ _)) ()
    walk (pr (go (send _ _ _) _ _ _ _)) ()
    walk (pr (go (recv _ _ _) _ _ _ _)) ()
    walk (pr (go (spawn _ _ _) _ _ _ _)) ()
    walk (pr (go (seq _ _) _ _ _ _)) ()
    walk (pr (go (await _ _) _ _ _ _)) ()
    walk (pr (go (ignore _ _) _ _ _ _)) ()
    walk (pr (go (nignore _ _) _ _ _ _)) ()
    walk (pr (go (flushT _ _) _ _ _ _)) ()
    walk (pr (go (ignoreT _ _) _ _ _ _)) ()
    walk (pr (go (ncheckT _ _) _ _ _ _)) ()
    walk (pr (go (ndemonT _ _) _ _ _ _)) ()
    walk idle ()
    walk (ev _ _ _) ()
    walk (rv _ _ _) ()

  ------------------------------------------------------------------------
  -- Pulling a flight removes one reference that was already counted.
  ------------------------------------------------------------------------

  pullCode-free : ∀ c f c' →
    pullCode c ≡ just (f , c') →
    count τ (codeRefs c) ≡ 0 →
    (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (codeRefs c') ≡ 0
  pullCode-free (go _ _ [] _ _) _ _ () _
  pullCode-free (go _ env (flight j r ∷ eth) _ _) .(flight j r) .(go _ env eth _ _) refl z =
    let ze , zfl = ++0 env (r ∷ flightRefs eth) z
        nr , zrest = head0 r (flightRefs eth) zfl
    in nr , 0++ env (flightRefs eth) ze zrest

  mutual
    pullFrames-free : ∀ ks f ks' →
      pullFrames ks ≡ just (f , ks') →
      count τ (framesRefs ks) ≡ 0 →
      (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (framesRefs ks') ≡ 0
    pullFrames-free [] _ _ () _
    pullFrames-free (saved c ∷ ks) f ks' eq z =
      let zc , zks = ++0 (codeRefs c) (framesRefs ks) z
      in savedGo (pullCode c) eq refl zc zks
      where
      savedGo : (m : Maybe (Flight × Code)) →
                pullFrames (saved c ∷ ks) ≡ just (f , ks') →
                pullCode c ≡ m →
                count τ (codeRefs c) ≡ 0 →
                count τ (framesRefs ks) ≡ 0 →
                (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (framesRefs ks') ≡ 0
      savedGo (just (f0 , c0)) eqp ep zc zks rewrite ep = body eqp
        where
        body : just (f0 , saved c0 ∷ ks) ≡ just (f , ks') →
               (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (framesRefs ks') ≡ 0
        body refl =
          let nr , zc0 = pullCode-free c f0 c0 ep zc
          in nr , 0++ (codeRefs c0) (framesRefs ks) zc0 zks
      savedGo nothing eqp ep zc zks rewrite ep = deep (pullFrames ks) eqp refl
        where
        deep : (m : Maybe (Flight × List Frame)) →
               (m >>= λ (f1 , ks1) → just (f1 , saved c ∷ ks1)) ≡ just (f , ks') →
               pullFrames ks ≡ m →
               (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (framesRefs ks') ≡ 0
        deep nothing () _
        deep (just (f1 , ks1)) refl eqm =
          let nr , zks1 = pullFrames-free ks f1 ks1 eqm zks
          in nr , 0++ (codeRefs c) (framesRefs ks1) zc zks1
    pullFrames-free (ar a ∷ ks) f ks' eq z = pullRest (ar a) ks f ks' eq z
    pullFrames-free (fn r ∷ ks) f ks' eq z = pullRest (fn r) ks f ks' eq z
    pullFrames-free (su ∷ ks) f ks' eq z = pullRest su ks f ks' eq z
    pullFrames-free (mt e0 z0 s ∷ ks) f ks' eq z = pullRest (mt e0 z0 s) ks f ks' eq z
    pullFrames-free (bd env ∷ ks) f ks' eq z = pullRest (bd env) ks f ks' eq z

    -- A non-saved frame has no ether of its own, so the flight is deeper.
    pullRest : ∀ k ks f ks' →
      (pullFrames ks >>= λ (f1 , ks1) → just (f1 , k ∷ ks1)) ≡ just (f , ks') →
      count τ (framesRefs (k ∷ ks)) ≡ 0 →
      (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (framesRefs ks') ≡ 0
    pullRest k ks f ks' eq z = deep (pullFrames ks) eq refl
      where
      zk = proj₁ (++0 (frameRefs k) (framesRefs ks) z)
      zks = proj₂ (++0 (frameRefs k) (framesRefs ks) z)
      deep : (m : Maybe (Flight × List Frame)) →
             (m >>= λ (f1 , ks1) → just (f1 , k ∷ ks1)) ≡ just (f , ks') →
             pullFrames ks ≡ m →
             (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (framesRefs ks') ≡ 0
      deep nothing () _
      deep (just (f1 , ks1)) refl eqm =
        let nr , zks1 = pullFrames-free ks f1 ks1 eqm zks
        in nr , 0++ (frameRefs k) (framesRefs ks1) zk zks1

  pullCtl-free : ∀ c f c' →
    pullCtl c ≡ just (f , c') →
    count τ (ctlRefs c) ≡ 0 →
    (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (ctlRefs c') ≡ 0
  pullCtl-free idle _ _ () _
  pullCtl-free (pr c) f c' eq z = prGo (pullCode c) eq refl
    where
    prGo : (m : Maybe (Flight × Code)) →
           pullCtl (pr c) ≡ just (f , c') →
           pullCode c ≡ m →
           (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (ctlRefs c') ≡ 0
    prGo nothing eqp ep rewrite ep = stuck-just eqp
    prGo (just (f0 , c0)) eqp ep rewrite ep = body eqp
      where
      body : just (f0 , pr c0) ≡ just (f , c') →
             (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (ctlRefs c') ≡ 0
      body refl = pullCode-free c f0 c0 ep z
  pullCtl-free (ev t e k) f c' eq z =
    let ze , zf = ++0 e (framesRefs k) z
    in evGo (pullFrames k) eq refl ze zf
    where
    evGo : (m : Maybe (Flight × List Frame)) →
           pullCtl (ev t e k) ≡ just (f , c') →
           pullFrames k ≡ m →
           count τ e ≡ 0 → count τ (framesRefs k) ≡ 0 →
           (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (ctlRefs c') ≡ 0
    evGo nothing eqp ep _ _ rewrite ep = stuck-just eqp
    evGo (just (f0 , k0)) eqp ep ze zf rewrite ep = body eqp
      where
      body : just (f0 , ev t e k0) ≡ just (f , c') →
             (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (ctlRefs c') ≡ 0
      body refl =
        let nr , zk0 = pullFrames-free k f0 k0 ep zf
        in nr , 0++ e (framesRefs k0) ze zk0
  pullCtl-free (rv r e k) f c' eq z =
    let nr0 , zrest = head0 r (e ++ framesRefs k) z
        ze , zf = ++0 e (framesRefs k) zrest
    in rvGo (pullFrames k) eq refl nr0 ze zf
    where
    rvGo : (m : Maybe (Flight × List Frame)) →
           pullCtl (rv r e k) ≡ just (f , c') →
           pullFrames k ≡ m →
           (obj r ≡ᵇ τ) ≡ false → count τ e ≡ 0 → count τ (framesRefs k) ≡ 0 →
           (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (ctlRefs c') ≡ 0
    rvGo nothing eqp ep _ _ _ rewrite ep = stuck-just eqp
    rvGo (just (f0 , k0)) eqp ep nr0 ze zf rewrite ep = body eqp
      where
      body : just (f0 , rv r e k0) ≡ just (f , c') →
             (obj (flightRef f) ≡ᵇ τ) ≡ false × count τ (ctlRefs c') ≡ 0
      body refl =
        let nr , zk0 = pullFrames-free k f0 k0 ep zf
        in nr , cons0 r (e ++ framesRefs k0) nr0 (0++ e (framesRefs k0) ze zk0)

  wake-ctl : ∀ p → ctl (wake p) ≡ ctl p
  wake-ctl p = walk (state p) refl
    where
    walk : (st : PState) → state p ≡ st → ctl (wake p) ≡ ctl p
    walk waiting eq rewrite eq = refl
    walk ready eq rewrite eq = refl
    walk pstDone eq rewrite eq = refl

  wake-refs : ∀ p → refsP (wake p) ≡ refsP p
  wake-refs p = walk (state p) refl
    where
    walk : (st : PState) → state p ≡ st → refsP (wake p) ≡ refsP p
    walk waiting eq rewrite eq = refl
    walk ready eq rewrite eq = refl
    walk pstDone eq rewrite eq = refl

  hand-free : ∀ {ph rs ce pe} → Hand ph rs ce pe →
    count τ rs ≡ 0 → (obj ph ≡ᵇ τ) ≡ false →
    count τ ce ≡ 0 × count τ pe ≡ 0
  hand-free hn-nil _ _ = refl , refl
  hand-free (hn-skip {r} {rs} {pe = pe} h) eq np =
    let nr , zrs = head0 r rs eq
        zc , zp = hand-free h zrs np
    in zc , cons0 r pe nr zp
  hand-free {ph} (hn-move {r} {rs} {ce = ce} {pe = pe} _ h) eq np =
    let nr , zrs = head0 r rs eq
        zc , zp = hand-free h zrs np
    in cons0 r ce nr zc , cons0 ph pe np zp
  hand-free (hn-copy {r} {rs} {ce = ce} {pe = pe} _ h) eq np =
    let nr , zrs = head0 r rs eq
        zc , zp = hand-free h zrs np
    in cons0 r ce nr zc , cons0 r pe nr zp

  ------------------------------------------------------------------------
  -- The seven lifted steps, then the process steps.
  ------------------------------------------------------------------------

  record Clear (s : Sys) : Set where
    constructor clear
    field
      cnt : count τ (refsOf s) ≡ 0
      fit : τ < length (heap s)

  open Clear

  deref-clear : ∀ s i j t → deref run s i j ≡ just t → Clear s → Clear t
  deref-clear (sys h ps) i j t eq (clear zc fit) = root (rootAt (sys h ps) i j) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    root : (m : Maybe Ref) → derefAt (sys h ps) i j m ≡ just t → rootAt (sys h ps) i j ≡ m → Clear t
    root nothing () _
    root (just r) eqd rk = spent (spendRef r) eqd refl
      where
      spent : (m : Maybe Ref) → derefSpent h ps i j r m ≡ just t → spendRef r ≡ m → Clear t
      spent nothing () _
      spent (just r') eqd es = via (putRoot ps i j r') eqd refl
        where
        via : (m : Maybe (List Proc)) → mapSys h m ≡ just t → putRoot ps i j r' ≡ m → Clear t
        via nothing () _
        via (just ps') refl ep =
          let trip = root-lookup ps i j r rk
              p    = proj₁ trip
              lk   = proj₁ (proj₂ trip)
              lr   = proj₂ (proj₂ trip)
              eo   = spendRef-obj r r' es
              ec   = ctlEq-putRoot ps i j r' ps' ep
              cq   = put-count τ i j ps p r r' ps' lk lr eo ep
          in clear (refs0 h ps' ze (trans (cong (count τ) ec) zctl) (trans cq zr)) fit

  recv-clear : ∀ h ps i t → vrecv (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  recv-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    from : (m : Maybe Proc) → recvAt h ps i m ≡ just t → lookup ps i ≡ m → Clear t
    from nothing () _
    from (just p) eqr lk = box (inbox p) eqr refl
      where
      box : (ms : List Msg) → recvInbox h ps i p ms ≡ just t → inbox p ≡ ms → Clear t
      box [] () _
      box (msg r ∷ ms) eqb em = upd (update i p' ps) eqb refl
        where
        p' = record p { roots = roots p ++ r ∷ [] ; inbox = ms }
        same = recv-refs p r ms em
        upd : (m : Maybe (List Proc)) → mapSys h m ≡ just t → update i p' ps ≡ m → Clear t
        upd nothing () _
        upd (just ps') refl eu =
          let cq = upd-count τ i ps p p' ps' lk eu (cong (count τ) same)
              cc = ctlEq-update i ps p' ps' eu
                     (λ q eqq → cong ctl (just-inj (trans (sym lk) eqq)))
          in clear (refs0 h ps' ze (trans (cong (count τ) cc) zctl) (trans cq zr)) fit

  copy-count : ∀ p r → (obj r ≡ᵇ τ) ≡ false → count τ (refsP p) ≡ 0 →
               count τ (refsP (post p r)) ≡ 0
  copy-count p r nr zp rewrite post-count τ p r | nr | zp = refl

  snoc-count : ∀ p r → (obj r ≡ᵇ τ) ≡ false → count τ (refsP p) ≡ 0 →
               count τ (refsP (record p { roots = roots p ++ r ∷ [] })) ≡ 0
  snoc-count p r nr zp rewrite snoc-root-count τ p r | nr | zp = refl

  alloc-clear : ∀ h ps i g v t → alloc (sys h ps) i g v ≡ just t → Clear (sys h ps) → Clear t
  alloc-clear h ps i g v t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    r = ref (length h) g g (selfKept g)
    nr = len-miss fit
    h' = snoc h (nat v)
    from : (m : Maybe Proc) →
           mapSys h' (addRoot ps i r) ≡ just t →
           lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk with eqa
    ... | ()
    from (just p) eqa lk rewrite lk = upd (update i p' ps) eqa refl
      where
      p' = record p { roots = roots p ++ r ∷ [] }
      upd : (m : Maybe (List Proc)) → mapSys h' m ≡ just t → update i p' ps ≡ m → Clear t
      upd nothing () _
      upd (just ps') refl eu =
        let zrp = lookup-refs0 i ps p lk zr
            cr  = trans (snoc-count p r nr zrp) (sym zrp)
            cq  = upd-count τ i ps p p' ps' lk eu cr
            cc  = ctlEq-update i ps p' ps' eu
                    (λ q eqq → cong ctl (just-inj (trans (sym lk) eqq)))
            ze' = trans (cong (count τ) (edge-nat h v)) ze
        in clear (refs0 h' ps' ze' (trans (cong (count τ) cc) zctl) (trans cq zr)) (fit-snoc h (nat v) fit)

  send-clear : ∀ h ps si sj ri t → vsend (sys h ps) si sj ri ≡ just t →
               Clear (sys h ps) → Clear t
  send-clear h ps si sj ri t eq (clear zc fit) = from (lookup ps si) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    from : (m : Maybe Proc) → sendFrom m si sj ri h ps ≡ just t → lookup ps si ≡ m → Clear t
    from nothing () _
    from (just sp) eqs lk = rooted (removeAt sj (roots sp)) eqs refl
      where
      rooted : (m : Maybe (Ref × List Ref)) →
               sendTaken (dropRoot sp m) si ri h ps ≡ just t →
               removeAt sj (roots sp) ≡ m → Clear t
      rooted nothing () _
      rooted (just (r , ys)) eqs rm =
        class (isZeroGrade (residual r)) (kind (checked r)) eqs refl refl
        where
        sp' = record sp { roots = ys }
        zsp = lookup-refs0 si ps sp lk zr
        zroots = proj₁ (++0 (roots sp) (mapRef (inbox sp)) zsp)
        nr = proj₁ (head0 r ys (trans (sym (removeAt-count τ sj (roots sp) r ys rm)) zroots))
        class : (z : Bool) (kd : Maybe Kind) →
                dispatch z kd r sp' si ri h ps ≡ just t →
                isZeroGrade (residual r) ≡ z →
                kind (checked r) ≡ kd → Clear t
        class true _ () _ _
        class false nothing () _ _
        class false (just Kmove) eqs _ _ =
          let kh = keep-on h ps si sj ri t r ys sp (si ≡ᵇ ri) lk rm refl eqs
          in clear (trans (proj₂ kh τ) zc) (subst (λ h0 → τ < length h0) (sym (proj₁ kh)) fit)
        class false (just Kcopy) eqs _ _ = copied (lookup ps ri) eqs refl
          where
          copied : (m : Maybe Proc) → mapSys h (addMsg ps ri r) ≡ just t → lookup ps ri ≡ m → Clear t
          copied nothing eq2 lk2 rewrite lk2 with eq2
          ... | ()
          copied (just rp) eq2 lk2 rewrite lk2 = updated (update ri (post rp r) ps) eq2 refl
            where
            updated : (m : Maybe (List Proc)) → mapSys h m ≡ just t →
                      update ri (post rp r) ps ≡ m → Clear t
            updated nothing () _
            updated (just ps') refl eu =
              let zrp = lookup-refs0 ri ps rp lk2 zr
                  cq  = upd-count τ ri ps rp (post rp r) ps' lk2 eu
                          (trans (copy-count rp r nr zrp) (sym zrp))
                  cc  = ctlEq-update ri ps (post rp r) ps' eu
                          (λ q eqq → cong ctl (just-inj (trans (sym lk2) eqq)))
              in clear (refs0 h ps' ze (trans (cong (count τ) cc) zctl) (trans cq zr)) fit

  poke-edge0 : ∀ h k v → count τ (edgeRefs h) ≡ 0 → count τ (edgeRefs (poke h k v)) ≡ 0
  poke-edge0 [] _ _ _ = refl
  poke-edge0 (o ∷ os) zero v eq =
    let _ , zos = ++0 (kids (payload o)) (edgeRefs os) eq
    in zos
  poke-edge0 (o ∷ os) (suc k) v eq =
    let zk , zos = ++0 (kids (payload o)) (edgeRefs os) eq
    in 0++ (kids (payload o)) (edgeRefs (poke os k v)) zk (poke-edge0 os k v zos)

  reuse-clear : ∀ s i j g v t → reuse s i j g v ≡ just t → Clear s → Clear t
  reuse-clear (sys h ps) i j g v t eq (clear zc fit) = from (rootAt (sys h ps) i j) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    from : (m : Maybe Ref) → reuseFrom (sys h ps) i j g v m ≡ just t →
           rootAt (sys h ps) i j ≡ m → Clear t
    from nothing eqr rk rewrite rk with eqr
    ... | ()
    from (just r) eqr rk rewrite rk =
      gates (isG1 (checked r)) (isZeroGrade (residual r))
            (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) eqr refl refl refl
      where
      gates : (a b c : Bool) →
              reuseOk (sys h ps) i j g v r a b c ≡ just t →
              isG1 (checked r) ≡ a →
              isZeroGrade (residual r) ≡ b →
              (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1) ≡ c →
              Clear t
      gates false _ _ () _ _ _
      gates true false _ () _ _ _
      gates true true false () _ _ _
      gates true true true eqg _ _ gc = landed (putRoot ps i j r') eqg refl
        where
        r' = ref (obj r) g g (selfKept g)
        nr : (obj r ≡ᵇ τ) ≡ false
        nr with obj r ≡ᵇ τ in eob
        ... | false = refl
        ... | true =
          ⊥-elim (true≢false
            (trans (sym (subst (λ o → (count o (refsOf (sys h ps)) ≡ᵇ 1) ≡ true)
                               (≡ᵇ-sound (obj r) τ eob) gc))
                   (cong (_≡ᵇ 1) zc)))
        landed : (m : Maybe (List Proc)) →
                 mapSys (poke h (obj r) v) m ≡ just t →
                 putRoot ps i j r' ≡ m → Clear t
        landed nothing () _
        landed (just ps') refl ep =
          let trip = root-lookup ps i j r rk
              p    = proj₁ trip
              lk   = proj₁ (proj₂ trip)
              lr   = proj₂ (proj₂ trip)
              cq   = put-count τ i j ps p r r' ps' lk lr refl ep
              cc   = ctlEq-putRoot ps i j r' ps' ep
              h'   = poke h (obj r) v
          in clear (refs0 h' ps' (poke-edge0 h (obj r) v ze)
                          (trans (cong (count τ) cc) zctl)
                          (trans cq zr))
                   (fit-poke h (obj r) v fit)

  -- ≡ᵇ-sound was imported inside nr. Hoist it: the inner open is local
  -- to the true branch, which is what we need. If Agda rejects the open
  -- inside the clause, the top-level import is added on the next edit.

  collect-clear : ∀ s → Clear s → Clear (collect s)
  collect-clear (sys h ps) (clear zc fit) =
    let ze = proj₁ (parts h ps zc)
        zctl = proj₁ (proj₂ (parts h ps zc))
        zr = proj₂ (proj₂ (parts h ps zc))
        bs = markVec (sys h ps)
        h' = apply bs h
        ps' = map clean ps
        ze' = le0 (count-edge bs h τ) ze
        zc' = trans (cong (count τ) (ctl-clean ps)) zctl
        zr' = le0 (subst (λ rs → count τ rs ≤ count τ (refsPs ps))
                         (sym (refs-cleaned ps)) (count-filter τ (refsPs ps))) zr
    in clear (refs0 h' ps' ze' zc' zr') (fit-apply bs h fit)

  -- eval is the long case. It only rearranges refs that are already
  -- present, or allocates a fresh index.
  eval-clear : ∀ h ps i t → eval1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  eval-clear h ps i t eq c0@(clear zc fit) = at (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))

    seal : ∀ h' c →
      count τ (edgeRefs h') ≡ 0 →
      count τ (ctlRefs c) ≡ 0 →
      τ < length h' →
      mapSys h' (setProc ps i c) ≡ just t →
      Clear t
    seal h' c ze' znew lt eqm = landed (setProc ps i c) eqm refl
      where
      landed : (m : Maybe (List Proc)) → mapSys h' m ≡ just t → setProc ps i c ≡ m → Clear t
      landed nothing () _
      landed (just ps') refl es =
        clear (refs0 h' ps' ze' (setProc-ctl0 i ps c ps' zctl znew es)
                     (trans (cong (count τ) (set-refsPs i ps c ps' es)) zr))
              lt

    freshCtl : ∀ env k g' → count τ env ≡ 0 → count τ (framesRefs k) ≡ 0 →
               count τ (ctlRefs (rv (freshRef h g') env k)) ≡ 0
    freshCtl env k g' ze0 zf = cons0 (freshRef h g') (env ++ framesRefs k) (len-miss fit) (0++ env (framesRefs k) ze0 zf)

    at : (m : Maybe Proc) → eval1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    at nothing eqa lk rewrite lk with eqa
    ... | ()
    at (just p) eqa lk rewrite lk = on (ctl p) eqa refl
      where
      here = lookup-ctl0 i ps p lk zctl

      onTm : ∀ {n} (tm : GTm n) env k →
             count τ env ≡ 0 → count τ (framesRefs k) ≡ 0 →
             evalTm h ps i tm env k ≡ just t → Clear t
      onTm (gapp f a) env k ze0 zf eqt =
        seal h (ev f env (ar a ∷ k)) ze (0++ env (framesRefs k) ze0 zf) fit eqt
      onTm (gsu e0) env k ze0 zf eqt =
        seal h (ev e0 env (su ∷ k)) ze (0++ env (framesRefs k) ze0 zf) fit eqt
      onTm (gmatch e0 z s) env k ze0 zf eqt =
        seal h (ev e0 env (mt e0 z s ∷ k)) ze (0++ env (framesRefs k) ze0 zf) fit eqt
      onTm (gtyp _) env k ze0 zf eqt =
        seal (snoc h (nat zero)) (rv (freshRef h gω) env k) (trans (cong (count τ) (edge-nat h zero)) ze)
             (freshCtl env k gω ze0 zf) (fit-snoc h (nat zero) fit) eqt
      onTm (gpi _ _ _) env k ze0 zf eqt =
        seal (snoc h (nat zero)) (rv (freshRef h gω) env k) (trans (cong (count τ) (edge-nat h zero)) ze)
             (freshCtl env k gω ze0 zf) (fit-snoc h (nat zero) fit) eqt
      onTm gze env k ze0 zf eqt =
        seal (snoc h (nat zero)) (rv (freshRef h gω) env k) (trans (cong (count τ) (edge-nat h zero)) ze)
             (freshCtl env k gω ze0 zf) (fit-snoc h (nat zero) fit) eqt
      onTm {n} (glam cG ty b) env k ze0 zf eqt =
        let _ , eI = pass-ok (not (anyG1 env))
                       (install (snoc h (clo env (n , glam cG ty b))) ps i
                         (rv (freshRef h gω) env k)) eqt
            h2 = snoc h (clo env (n , glam cG ty b))
        in seal h2 (rv (freshRef h gω) env k)
             (trans (cong (count τ) (edge-clo h env (n , glam cG ty b))) (0++ (edgeRefs h) env ze ze0))
             (freshCtl env k gω ze0 zf)
             (fit-snoc h (clo env (n , glam cG ty b)) fit) eI
      onTm (gvar x) env k ze0 zf eqt = varGo (lookup env (toℕ x)) eqt refl
        where
        ix = toℕ x
        varGo : (m : Maybe Ref) → useVar h ps i env k ix m ≡ just t → lookup env ix ≡ m → Clear t
        varGo nothing () _
        varGo (just r) eqv lr = fromS (spendRef r) eqv refl
          where
          nr = lookup-miss env ix r lr ze0
          nrOf : ∀ r' → spendRef r ≡ just r' → (obj r' ≡ᵇ τ) ≡ false
          nrOf r' es = trans (≡ᵇ-cong (obj r') (obj r) τ (spendRef-obj r r' es)) nr
          natGo : ∀ r' nv → spendRef r ≡ just r' →
                  install (snoc h (nat nv)) ps i
                    (rv (freshRef h gω) (repl ix r' env) k) ≡ just t →
                  Clear t
          natGo r' nv es eqm =
            let nr' = nrOf r' es
            in seal (snoc h (nat nv)) (rv (freshRef h gω) (repl ix r' env) k)
                 (trans (cong (count τ) (edge-nat h nv)) ze)
                 (freshCtl (repl ix r' env) k gω (repl-keep0 ix env r' ze0 nr') zf)
                 (fit-snoc h (nat nv) fit) eqm
          moveGo : ∀ r' → spendRef r ≡ just r' →
            pass (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1)
                 (install (snoc h (nat zero)) ps i
                   (rv r' (repl ix (freshRef h g0) env) k)) ≡ just t →
            Clear t
          moveGo r' es eqm =
            let nr' = nrOf r' es
                _ , eI = pass-ok (count (obj r) (refsOf (sys h ps)) ≡ᵇ 1)
                           (install (snoc h (nat zero)) ps i
                             (rv r' (repl ix (freshRef h g0) env) k)) eqm
                envG = repl ix (freshRef h g0) env
            in seal (snoc h (nat zero)) (rv r' envG k)
                 (trans (cong (count τ) (edge-nat h zero)) ze)
                 (cons0 r' (envG ++ framesRefs k) nr'
                    (0++ envG (framesRefs k)
                       (repl-keep0 ix env (freshRef h g0) ze0 (len-miss fit)) zf))
                 (fit-snoc h (nat zero) fit) eI
          aliasGo : ∀ r' → spendRef r ≡ just r' →
                    install h ps i (rv r' (repl ix r' env) k) ≡ just t → Clear t
          aliasGo r' es eqm =
            let nr' = nrOf r' es
                envA = repl ix r' env
            in seal h (rv r' envA k) ze
                 (cons0 r' (envA ++ framesRefs k) nr'
                    (0++ envA (framesRefs k) (repl-keep0 ix env r' ze0 nr') zf))
                 fit eqm
          fromS : (m : Maybe Ref) → useVar h ps i env k ix (just r) ≡ just t → spendRef r ≡ m → Clear t
          fromS nothing eqv es rewrite es with eqv
          ... | ()
          fromS (just r') eqv es rewrite es with payloadAt h (obj r)
          fromS (just r') eqv es | nothing with eqv
          fromS (just r') eqv es | nothing | ()
          fromS (just r') eqv es | just (nat nv) = natGo r' nv es eqv
          fromS (just r') eqv es | just (suc↑ _) with isG1 (checked r')
          fromS (just r') eqv es | just (suc↑ _) | true  = moveGo r' es eqv
          fromS (just r') eqv es | just (suc↑ _) | false = aliasGo r' es eqv
          fromS (just r') eqv es | just (clo _ _) with isG1 (checked r')
          fromS (just r') eqv es | just (clo _ _) | true  = moveGo r' es eqv
          fromS (just r') eqv es | just (clo _ _) | false = aliasGo r' es eqv

      onRet : ∀ r env k →
              (obj r ≡ᵇ τ) ≡ false → count τ env ≡ 0 → count τ (framesRefs k) ≡ 0 →
              evalRet h ps i r env k ≡ just t → Clear t
      onRet r env [] _ _ _ ()
      onRet r env (ar a ∷ k) nr ze0 zf eqt =
        seal h (ev a env (fn r ∷ k)) ze
          (0++ env (r ∷ framesRefs k) ze0 (cons0 r (framesRefs k) nr zf)) fit eqt
      onRet r env (fn rf ∷ k) nr ze0 zf eqt = betaGo eqt
        where
        nrf = proj₁ (head0 rf (framesRefs k) zf)
        zfr = proj₂ (head0 rf (framesRefs k) zf)
        betaGo : beta h ps i r rf env k ≡ just t → Clear t
        betaGo eqb = opened (payloadAt h (obj rf)) eqb refl
          where
          opened : (v : Maybe Val) → beta h ps i r rf env k ≡ just t → payloadAt h (obj rf) ≡ v → Clear t
          opened nothing eqp pv rewrite pv = stuck-just eqp
          opened (just (nat _)) eqp pv rewrite pv = stuck-just eqp
          opened (just (suc↑ _)) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (_ , gvar _))) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (_ , gtyp _))) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (_ , gpi _ _ _))) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (_ , gapp _ _))) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (_ , gze))) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (_ , gsu _))) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (_ , gmatch _ _ _))) eqp pv rewrite pv = stuck-just eqp
          opened (just (clo envC (nb , glam cG ty body))) eqp pv rewrite pv =
            let inner = install h ps i (ev body (regrade r cG ∷ envC) (bd env ∷ k))
                outer = pass-ok (not (badG1 cG (obj r) (refsOf (sys h ps))))
                                (pass (not (anyG1 envC)) inner) eqp
                inn = pass-ok (not (anyG1 envC)) inner (proj₂ outer)
                zEC = kidsOf (edge-at h (obj rf) (clo envC (nb , glam cG ty body)) pv)
            in seal h (ev body (regrade r cG ∷ envC) (bd env ∷ k)) ze
                 (cons0 (regrade r cG) (envC ++ (env ++ framesRefs k)) nr
                    (0++ envC (env ++ framesRefs k) zEC (0++ env (framesRefs k) ze0 zfr)))
                 fit (proj₂ inn)
            where
            kidsOf : EdgeAt h (obj rf) (clo envC (nb , glam cG ty body)) → count τ envC ≡ 0
            kidsOf (eat L R e1 _) =
              sub-zero τ L envC R
                (trans (cong (count τ) (sym e1)) ze)
      onRet r env (su ∷ k) nr ze0 zf eqt =
        seal (snoc h (suc↑ r)) (rv (freshRef h gω) env k)
          (trans (cong (count τ) (edge-suc h r)) (0++ (edgeRefs h) (r ∷ []) ze (cons0 r [] nr refl)))
          (freshCtl env k gω ze0 zf)
          (fit-snoc h (suc↑ r) fit) eqt
      onRet r env (mt e0 z s ∷ k) nr ze0 zf eqt = onV (payloadAt h (obj r)) eqt refl
        where
        onV : (v : Maybe Val) →
              onMatch h ps i r env e0 z s k v ≡ just t →
              payloadAt h (obj r) ≡ v → Clear t
        onV nothing eqp pv rewrite pv = stuck-just eqp
        onV (just (nat (suc _))) eqp pv rewrite pv = stuck-just eqp
        onV (just (clo _ _)) eqp pv rewrite pv = stuck-just eqp
        onV (just (nat zero)) eqp pv rewrite pv =
          seal h (ev z env k) ze (0++ env (framesRefs k) ze0 zf) fit eqp
        onV (just (suc↑ pred)) eqp pv rewrite pv =
          let inner = install (setPayload h (obj r) (nat zero)) ps i
                        (ev s (regrade pred (predComp env e0) ∷ env) k)
              op = pass-ok (not (badG1 (predComp env e0) (obj pred) (refsOf (sys h ps)))) inner eqp
              eA = edge-at h (obj r) (suc↑ pred) pv
          in sucDone eA (proj₂ op)
          where
          sucDone : EdgeAt h (obj r) (suc↑ pred) →
                    install (setPayload h (obj r) (nat zero)) ps i
                      (ev s (regrade pred (predComp env e0) ∷ env) k) ≡ just t →
                    Clear t
          sucDone (eat L R e1 e2) eI =
            let zKids = sub-zero τ L (pred ∷ []) R (trans (cong (count τ) (sym e1)) ze)
                np = proj₁ (head0 pred [] zKids)
                zL , zKR = ++0 L (pred ∷ R) (trans (cong (count τ) (sym e1)) ze)
                _ , zR = head0 pred R zKR
                h2 = setPayload h (obj r) (nat zero)
            in seal h2 (ev s (regrade pred (predComp env e0) ∷ env) k)
                 (trans (cong (count τ) e2) (0++ L R zL zR))
                 (cons0 (regrade pred (predComp env e0)) (env ++ framesRefs k) np
                    (0++ env (framesRefs k) ze0 zf))
                 (fit-set h (obj r) (nat zero) fit) eI
      onRet r env (bd env0 ∷ k) nr ze0 zf eqt =
        let z0 , zf' = ++0 env0 (framesRefs k) zf
        in seal h (rv r env0 k) ze (cons0 r (env0 ++ framesRefs k) nr (0++ env0 (framesRefs k) z0 zf')) fit eqt
      onRet r env (saved _ ∷ _) _ _ _ eqt = stuck-just eqt

      on : (c : Ctl) → evalHere h ps i c ≡ just t → ctl p ≡ c → Clear t
      on idle eqh _ = stuck-just eqh
      on (pr _) eqh _ = stuck-just eqh
      on (ev tm env k) eqh ec =
        let zhere = subst (λ c → count τ (ctlRefs c) ≡ 0) ec here
        in onTm tm env k (proj₁ (++0 env (framesRefs k) zhere))
                         (proj₂ (++0 env (framesRefs k) zhere)) eqh
      on (rv r env k) eqh ec =
        let zhere = subst (λ c → count τ (ctlRefs c) ≡ 0) ec here
            nr , zrest = head0 r (env ++ framesRefs k) zhere
            ze0 , zf = ++0 env (framesRefs k) zrest
        in onRet r env k nr ze0 zf eqh


  ------------------------------------------------------------------------
  -- setProc / update when the heap is unchanged.
  ------------------------------------------------------------------------

  sealProc : ∀ h ps i t c →
    count τ (edgeRefs h) ≡ 0 →
    count τ (ctlRefsPs ps) ≡ 0 →
    count τ (refsPs ps) ≡ 0 →
    τ < length h →
    count τ (ctlRefs c) ≡ 0 →
    (setProc ps i c >>= λ ps' → just (sys h ps')) ≡ just t →
    Clear t
  sealProc h ps i t c ze zctl zr fit znew eq = landed (setProc ps i c) eq refl
    where
    nope : nothing ≡ just t → Clear t
    nope ()
    landed : (m : Maybe (List Proc)) →
             (m >>= λ ps' → just (sys h ps')) ≡ just t →
             setProc ps i c ≡ m → Clear t
    landed nothing eql el rewrite el = nope eql
    landed (just ps') refl el =
      clear (refs0 h ps' ze (setProc-ctl0 i ps c ps' zctl znew el)
                   (trans (cong (count τ) (set-refsPs i ps c ps' el)) zr))
            fit

  sealUpd : ∀ h ps i t p p' →
    lookup ps i ≡ just p →
    count τ (edgeRefs h) ≡ 0 →
    count τ (ctlRefsPs ps) ≡ 0 →
    count τ (refsPs ps) ≡ 0 →
    τ < length h →
    count τ (ctlRefs (ctl p')) ≡ 0 →
    count τ (refsP p') ≡ 0 →
    (update i p' ps >>= λ ps' → just (sys h ps')) ≡ just t →
    Clear t
  sealUpd h ps i t p p' lk ze zctl zr fit zc' zr' eq = landed (update i p' ps) eq refl
    where
    nope : nothing ≡ just t → Clear t
    nope ()
    landed : (m : Maybe (List Proc)) →
             (m >>= λ ps' → just (sys h ps')) ≡ just t →
             update i p' ps ≡ m → Clear t
    landed nothing eql el rewrite el = nope eql
    landed (just ps') refl el =
      let zc2 , zr2 = upd-both0 i ps p p' ps' lk el zc' zr' zctl zr
      in clear (refs0 h ps' ze zc2 zr2) fit

  ------------------------------------------------------------------------
  -- Consume keeps an absent tag absent. The scrub tag may be another one.
  ------------------------------------------------------------------------

  consume-keep : ∀ h ps i τf finish t →
    consume (sys h ps) i τf finish ≡ just t →
    (∀ c c' → finish τf c ≡ just c' → ctlRefs c' ≡ ctlRefs c) →
    Clear (sys h ps) →
    Clear t
  consume-keep h ps i τf finish t eq fre (clear zc fit) = at (lookup ps1 i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    ph = placeholder h
    np = len-miss fit
    hB = blankEdges τf h
    h' = snoc hB (nat zero)
    ps1 = map (scrubProc τf ph) ps
    nope : nothing ≡ just t → Clear t
    nope ()
    zctl1 = ctlKeep τf ph ps np zctl
    zr1 = refsKeep τf ph ps zr
    zeB = le0 (blank-count-≤ τ τf h) ze
    ze' = trans (cong (count τ) (edge-nat hB zero)) zeB
    fitB = subst (τ <_) (sym (blank-length τf h)) fit
    at : (m : Maybe Proc) →
         (m >>= λ p1 →
            finish τf (ctl p1) >>= λ c' →
            setCtlSt ps1 i c' ready >>= λ ps2 →
            just (sys h' ps2)) ≡ just t →
         lookup ps1 i ≡ m →
         Clear t
    at nothing eql lk rewrite lk = nope eql
    at (just p1) eql lk rewrite lk = fin (finish τf (ctl p1)) eql refl
      where
      zhere = lookup-ctl0 i ps1 p1 lk zctl1
      fin : (m : Maybe Ctl) →
            (m >>= λ c' → setCtlSt ps1 i c' ready >>= λ ps2 → just (sys h' ps2)) ≡ just t →
            finish τf (ctl p1) ≡ m →
            Clear t
      fin nothing eqf ef rewrite ef = nope eqf
      fin (just c') eqf ef rewrite ef = st (setCtlSt ps1 i c' ready) eqf refl
        where
        zc' = trans (cong (count τ) (fre (ctl p1) c' ef)) zhere
        st : (m : Maybe (List Proc)) →
             (m >>= λ ps2 → just (sys h' ps2)) ≡ just t →
             setCtlSt ps1 i c' ready ≡ m →
             Clear t
        st nothing eqs es rewrite es = nope eqs
        st (just ps2) refl es =
          let zc2 = setCtl-ctl0 i ps1 c' ready ps2 zctl1 zc' es
              zr2 = trans (cong (count τ) (setCtl-refsEq i ps1 c' ready ps2 es)) zr1
          in clear (refs0 h' ps2 ze' zc2 zr2) (fit-snoc hB (nat zero) fitB)

  ------------------------------------------------------------------------
  -- Consume of this tag establishes the count. Payloads that hold the
  -- tag are blanked to nat 0, so a prior edge is not a premise.
  ------------------------------------------------------------------------

  consume-establish : ∀ h ps i finish t →
    consume (sys h ps) i τ finish ≡ just t →
    (∀ c c' → finish τ c ≡ just c' → ctlRefs c' ≡ ctlRefs c) →
    (∀ c c' → finish τ c ≡ just c' → hasTag τ (deadInCtl c') ≡ true) →
    τ < length h →
    ReplyDone t i τ
  consume-establish h ps i finish t eq fre fdead fit = at (lookup ps1 i) eq refl
    where
    ph = placeholder h
    np = len-miss fit
    hB = blankEdges τ h
    h' = snoc hB (nat zero)
    ps1 = map (scrubProc τ ph) ps
    nope : nothing ≡ just t → ReplyDone t i τ
    nope ()
    zctl1 = ctlKill ph ps np
    zr1 = refsKill ph ps
    ze' = trans (cong (count τ) (edge-nat hB zero)) (blank-edge-0 τ h)
    fitB = subst (τ <_) (sym (blank-length τ h)) fit
    at : (m : Maybe Proc) →
         (m >>= λ p1 →
            finish τ (ctl p1) >>= λ c' →
            setCtlSt ps1 i c' ready >>= λ ps2 →
            just (sys h' ps2)) ≡ just t →
         lookup ps1 i ≡ m →
         ReplyDone t i τ
    at nothing eql lk rewrite lk = nope eql
    at (just p1) eql lk rewrite lk = fin (finish τ (ctl p1)) eql refl
      where
      zhere = lookup-ctl0 i ps1 p1 lk zctl1
      fin : (m : Maybe Ctl) →
            (m >>= λ c' → setCtlSt ps1 i c' ready >>= λ ps2 → just (sys h' ps2)) ≡ just t →
            finish τ (ctl p1) ≡ m →
            ReplyDone t i τ
      fin nothing eqf ef rewrite ef = nope eqf
      fin (just c') eqf ef rewrite ef = st (setCtlSt ps1 i c' ready) eqf refl
        where
        zc' = trans (cong (count τ) (fre (ctl p1) c' ef)) zhere
        st : (m : Maybe (List Proc)) →
             (m >>= λ ps2 → just (sys h' ps2)) ≡ just t →
             setCtlSt ps1 i c' ready ≡ m →
             ReplyDone t i τ
        st nothing eqs es rewrite es = nope eqs
        st (just ps2) refl es =
          let zc2 = setCtl-ctl0 i ps1 c' ready ps2 zctl1 zc' es
              zr2 = trans (cong (count τ) (setCtl-refsEq i ps1 c' ready ps2 es)) zr1
          in replied (refs0 h' ps2 ze' zc2 zr2) (fit-snoc hB (nat zero) fitB)
                     (setCtl-dead i ps1 c' ready ps2 es (fdead (ctl p1) c' ef))

  ignore-consumes : ∀ {h ps i t n} {k : PTm n} {env eth d dm p} →
    lookup ps i ≡ just p →
    ctl p ≡ pr (go (flushT τ k) env eth d dm) →
    flush1 (sys h ps) i ≡ just t →
    τ < length h →
    ReplyDone t i τ
  ignore-consumes {h = h} {ps = ps} {i = i} {t = t} lk ec eq fit =
    consume-establish h ps i finishFlush t (reduced eq)
      (finishFlush-refs τ) finishFlush-dead fit
    where
    reduced : flush1 (sys h ps) i ≡ just t → consume (sys h ps) i τ finishFlush ≡ just t
    reduced eqf rewrite lk | ec = eqf

  await-consumes : ∀ {h ps i t n} {k : PTm n} {env eth d dm p} →
    lookup ps i ≡ just p →
    ctl p ≡ pr (go (awaitT τ k) env eth d dm) →
    inboxHas (inbox p) τ ≡ true →
    await1 (sys h ps) i ≡ just t →
    τ < length h →
    ReplyDone t i τ
  await-consumes {h = h} {ps = ps} {i = i} {t = t} lk ec hb eq fit =
    consume-establish h ps i finishAwait t (reduced eq)
      (finishAwait-refs τ) finishAwait-dead fit
    where
    reduced : await1 (sys h ps) i ≡ just t → consume (sys h ps) i τ finishAwait ≡ just t
    reduced eqa rewrite lk | ec | hb = eqa

  ------------------------------------------------------------------------
  -- Process steps.
  ------------------------------------------------------------------------

  spawnAs : List Obj → List Proc → ℕ → Ctl → Maybe Sys
  spawnAs h ps i (pr (go (spawn th ch pa) env eth d dm)) =
    let ph = placeholder h
        h' = snoc h (nat zero)
    in splitGo zero ph th env >>= λ (ce , pe , mv) →
       let pcode = pr (go (applyMoves mv pa) pe eth d dm)
           child = proc (length ps) ready [] [] (pr (go ch ce [] [] []))
       in setProc ps i pcode >>= λ ps1 →
          just (sys h' (ps1 ++ child ∷ []))
  spawnAs _ _ _ _ = nothing

  spawn-as : ∀ h ps i p c → lookup ps i ≡ just p → ctl p ≡ c →
             spawn1 (sys h ps) i ≡ spawnAs h ps i c
  spawn-as h ps i p idle lk refl rewrite lk = refl
  spawn-as h ps i p (ev _ _ _) lk refl rewrite lk = refl
  spawn-as h ps i p (rv _ _ _) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go done _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (send _ _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (recv _ _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (seq _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (await _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (ignore _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (nignore _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (awaitT _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (ignoreT _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (flushT _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (ncheckT _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (ndemonT _ _) _ _ _ _)) lk refl rewrite lk = refl
  spawn-as h ps i p (pr (go (spawn _ _ _) _ _ _ _)) lk refl rewrite lk = refl

  spawn-clear : ∀ h ps i t → spawn1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  spawn-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    ph = placeholder h
    np = len-miss fit
    h' = snoc h (nat zero)
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → spawn1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk =
      onC (ctl p) (trans (sym (spawn-as h ps i p (ctl p) lk refl)) eqa) refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → spawnAs h ps i c ≡ just t → ctl p ≡ c → Clear t
      onC idle eqc refl = nope eqc
      onC (ev _ _ _) eqc refl = nope eqc
      onC (rv _ _ _) eqc refl = nope eqc
      onC (pr (go done _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc refl = nope eqc
      onC (pr (go (spawn th ch pa) env eth d dm)) eqc refl =
        spl (splitGo zero ph th env) eqc refl
        where
        ze0 = proj₁ (++0 env (flightRefs eth) here)
        zfl = proj₂ (++0 env (flightRefs eth) here)
        spl : (m : Maybe Split) →
              (m >>= λ (ce , pe , mv) →
                 setProc ps i (pr (go (applyMoves mv pa) pe eth d dm)) >>= λ ps1 →
                 just (sys h' (ps1 ++ proc (length ps) ready [] []
                   (pr (go ch ce [] [] [])) ∷ []))) ≡ just t →
              splitGo zero ph th env ≡ m →
              Clear t
        spl nothing eqm _ = nope eqm
        spl (just (ce , pe , mv)) eqm es =
          landed (setProc ps i pcode) eqm refl
          where
          pcode = pr (go (applyMoves mv pa) pe eth d dm)
          child = proc (length ps) ready [] [] (pr (go ch ce [] [] []))
          zce = proj₁ (hand-free (split-hand zero ph th env ce pe mv es) ze0 np)
          zpe = proj₂ (hand-free (split-hand zero ph th env ce pe mv es) ze0 np)
          landed : (m : Maybe (List Proc)) →
                   (m >>= λ ps1 → just (sys h' (ps1 ++ child ∷ []))) ≡ just t →
                   setProc ps i pcode ≡ m →
                   Clear t
          landed nothing eql _ = nope eql
          landed (just ps1) eqj el =
            subst Clear (just-inj eqj)
              (let zps1 = setProc-ctl0 i ps pcode ps1 zctl
                           (0++ pe (flightRefs eth) zpe zfl) el
                   rps1 = trans (cong (count τ) (set-refsPs i ps pcode ps1 el)) zr
                   zCh = trans (count-idʳ (ctlRefs (ctl child))) (trans (count-idʳ ce) zce)
                   zCtlAll = trans (cong (count τ) (ctlRefsPs-++ ps1 (child ∷ [])))
                                   (0++ (ctlRefsPs ps1) (ctlRefsPs (child ∷ [])) zps1 zCh)
                   zRs = trans (cong (count τ) (refsPs-++ ps1 (child ∷ [])))
                               (0++ (refsPs ps1) (refsPs (child ∷ [])) rps1 refl)
                   ze' = trans (cong (count τ) (edge-nat h zero)) ze
               in clear (refs0 h' (ps1 ++ child ∷ []) ze' zCtlAll zRs)
                        (fit-snoc h (nat zero) fit))

  emit-clear : ∀ h ps i t → emit1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  emit-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    np = len-miss fit
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → emit1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → emit1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk refl rewrite lk = nope eqc
      onC (ev _ _ _) eqc lk refl rewrite lk = nope eqc
      onC (rv _ _ _) eqc lk refl rewrite lk = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk refl rewrite lk = nope eqc
      onC (pr (go (send j x k) env eth d dm)) eqc lk refl rewrite lk
        with lookup env (toℕ x) in lref
      ... | nothing = nope eqc
      ... | just r with isZeroGrade (residual r)
      ... | true = nope eqc
      ... | false with blocked ps j (obj r)
      ... | true = nope eqc
      ... | false with kind (checked r)
      ... | nothing = nope eqc
      ... | just Kcopy =
        sealProc h ps i t ccopy ze zctl zr fit
          (0++ env (flightRefs flights) ze0 zadd) eqc
        where
        ze0 = proj₁ (++0 env (flightRefs eth) here)
        zfl = proj₂ (++0 env (flightRefs eth) here)
        nr = lookup-miss env (toℕ x) r lref ze0
        flights = eth ++ flight j r ∷ []
        zadd = trans (cong (count τ) (flightRefs-++ eth (flight j r ∷ [])))
                     (0++ (flightRefs eth) (r ∷ []) zfl (cons0 r [] nr refl))
        ccopy = pr (go k env flights d dm)
      ... | just Kmove = landed (setProc ps i cmove) eqc refl
        where
        ze0 = proj₁ (++0 env (flightRefs eth) here)
        zfl = proj₂ (++0 env (flightRefs eth) here)
        nr = lookup-miss env (toℕ x) r lref ze0
        flights = eth ++ flight j r ∷ []
        zadd = trans (cong (count τ) (flightRefs-++ eth (flight j r ∷ [])))
                     (0++ (flightRefs eth) (r ∷ []) zfl (cons0 r [] nr refl))
        ph = placeholder h
        h' = snoc h (nat zero)
        env' = repl (toℕ x) ph env
        cmove = pr (go k env' flights d dm)
        landed : (m : Maybe (List Proc)) →
                 (m >>= λ ps' → just (sys h' ps')) ≡ just t →
                 setProc ps i cmove ≡ m → Clear t
        landed nothing eql _ = nope eql
        landed (just ps') eqj el =
          subst Clear (just-inj eqj)
            (let zenv = repl-keep0 (toℕ x) env ph ze0 np
                 znew = 0++ env' (flightRefs flights) zenv zadd
                 zctl' = setProc-ctl0 i ps cmove ps' zctl znew el
                 zr' = trans (cong (count τ) (set-refsPs i ps cmove ps' el)) zr
                 ze' = trans (cong (count τ) (edge-nat h zero)) ze
             in clear (refs0 h' ps' ze' zctl' zr') (fit-snoc h (nat zero) fit))

  deliver-clear : ∀ h ps i t → deliver1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  deliver-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → deliver1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = use eqa lk
      where
      here = lookup-ctl0 i ps p lk zctl
      use : deliver1 (sys h ps) i ≡ just t → lookup ps i ≡ just p → Clear t
      use eqc lk rewrite lk with pullCtl (ctl p) in ep
      ... | nothing = nope eqc
      ... | just (flight j r , c1) = sent (setProc ps i c1) eqc refl
        where
        nr = proj₁ (pullCtl-free (ctl p) (flight j r) c1 ep here)
        zc1 = proj₂ (pullCtl-free (ctl p) (flight j r) c1 ep here)
        sent : (m : Maybe (List Proc)) →
               (m >>= λ ps1 →
                  lookup ps1 j >>= λ q →
                  if hasTag (obj r) (deadInCtl (ctl q)) then just (sys h ps1)
                  else update j (wake (post q r)) ps1 >>= λ ps2 → just (sys h ps2)) ≡ just t →
               setProc ps i c1 ≡ m →
               Clear t
        sent nothing eql el rewrite el = nope eql
        sent (just ps1) eql el rewrite el = dest (lookup ps1 j) eql refl
          where
          zctl1 = setProc-ctl0 i ps c1 ps1 zctl zc1 el
          zr1 = trans (cong (count τ) (set-refsPs i ps c1 ps1 el)) zr
          dest : (m : Maybe Proc) →
                 (m >>= λ q →
                    if hasTag (obj r) (deadInCtl (ctl q)) then just (sys h ps1)
                    else update j (wake (post q r)) ps1 >>= λ ps2 → just (sys h ps2)) ≡ just t →
                 lookup ps1 j ≡ m →
                 Clear t
          dest nothing eqd ld rewrite ld = nope eqd
          dest (just q) eqd ld rewrite ld = br (hasTag (obj r) (deadInCtl (ctl q))) eqd refl
            where
            br : (b : Bool) →
                 (if b then just (sys h ps1)
                       else update j (wake (post q r)) ps1 >>= λ ps2 → just (sys h ps2)) ≡ just t →
                 hasTag (obj r) (deadInCtl (ctl q)) ≡ b →
                 Clear t
            br true eqb eb rewrite eb =
              subst Clear (just-inj eqb) (clear (refs0 h ps1 ze zctl1 zr1) fit)
            br false eqb eb rewrite eb = posted (update j qp ps1) eqb refl
              where
              qp = wake (post q r)
              zc' = trans (cong (count τ) (cong ctlRefs (wake-ctl (post q r))))
                          (lookup-ctl0 j ps1 q ld zctl1)
              zr' = trans (cong (count τ) (wake-refs (post q r)))
                          (copy-count q r nr (lookup-refs0 j ps1 q ld zr1))
              posted : (m : Maybe (List Proc)) →
                       (m >>= λ ps2 → just (sys h ps2)) ≡ just t →
                       update j qp ps1 ≡ m →
                       Clear t
              posted nothing equ eu rewrite eu = nope equ
              posted (just ps2) refl eu =
                let zc2 , zr2 = upd-both0 j ps1 q qp ps2 ld eu zc' zr' zctl1 zr1
                in clear (refs0 h ps2 ze zc2 zr2) fit

  recvP-clear : ∀ h ps i t → recv1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  recvP-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → recv1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      onC : (c : Ctl) → recv1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 refl rewrite lk0 = nope eqc
      onC (ev _ _ _) eqc lk0 refl rewrite lk0 = nope eqc
      onC (rv _ _ _) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 refl rewrite lk0 = nope eqc
      onC (pr (go (recv _ _ k) env eth d dm)) eqc lk0 ec =
        elim lk0 ec eqc (lookup-ctl0 i ps p lk0 zctl) (lookup-refs0 i ps p lk0 zr)
        where
        code = pr (go (recv _ _ k) env eth d dm)
        elim : lookup ps i ≡ just p → ctl p ≡ code →
               recv1 (sys h ps) i ≡ just t →
               count τ (ctlRefs (ctl p)) ≡ 0 → count τ (refsP p) ≡ 0 → Clear t
        elim lk1 ec eq zhere zrP rewrite lk1 = opened ec eq
          where
          step : (st : PState) (ib : List Msg) → state p ≡ st → inbox p ≡ ib →
                 recvStep h ps i p code st ib ≡ just t → Clear t
          step waiting [] _ _ eq = nope eq
          step pstDone [] _ _ eq = nope eq
          step ready [] _ _ eq =
            sealUpd h ps i t p p' lk1 ze zctl zr fit zhere zrP eq
            where
            p' = record p { state = waiting }
          step st (msg r ∷ ms) _ ei eq =
            sealUpd h ps i t p p' lk1 ze zctl zr fit zc' zr' eq
            where
            p' = record p { state = ready ; inbox = ms
                          ; ctl = pr (go k (r ∷ env) eth d dm) }
            zib = subst (λ ib → count τ (roots p ++ mapRef ib) ≡ 0) ei zrP
            zroots = proj₁ (++0 (roots p) (r ∷ mapRef ms) zib)
            zcons = proj₂ (++0 (roots p) (r ∷ mapRef ms) zib)
            nr = proj₁ (head0 r (mapRef ms) zcons)
            zms = proj₂ (head0 r (mapRef ms) zcons)
            zr' = 0++ (roots p) (mapRef ms) zroots zms
            zenv = ctl0 ec zhere
            ze0 = proj₁ (++0 env (flightRefs eth) zenv)
            zfl = proj₂ (++0 env (flightRefs eth) zenv)
            zc' = 0++ (r ∷ env) (flightRefs eth) (cons0 r env nr ze0) zfl
          opened : ctl p ≡ code →
                   recvStep h ps i p (ctl p) (state p) (inbox p) ≡ just t → Clear t
          opened ec eq rewrite ec = step (state p) (inbox p) refl refl eq

  await-clear : ∀ h ps i t → await1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  await-clear h ps i t eq c0@(clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → await1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → await1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk ec rewrite lk | ec = nope eqc
      onC (ev _ _ _) eqc lk ec rewrite lk | ec = nope eqc
      onC (rv _ _ _) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk ec rewrite lk | ec = nope eqc
      onC (pr (go (awaitT τf k) env eth d dm)) eqc lk ec rewrite lk | ec =
        onB (inboxHas (inbox p) τf) refl eqc
        where
        onB : (b : Bool) → inboxHas (inbox p) τf ≡ b →
              awaitOn h ps i p (pr (go (awaitT τf k) env eth d dm)) b ≡ just t →
              Clear t
        onB true _ eqb =
          consume-keep h ps i τf finishAwait t eqb (finishAwait-refs τf) c0
        onB false _ eqb = onSt (state p) refl eqb
          where
          onSt : (st : PState) → state p ≡ st →
                 awaitPark h ps i τf k env eth d dm st ≡ just t → Clear t
          onSt waiting _ eqs = nope eqs
          onSt pstDone _ eqs = nope eqs
          onSt ready _ eqs = parked (setCtlSt ps i cwait waiting) eqs refl
            where
            cwait = pr (go (awaitT τf k) env eth d dm)
            parked : (m : Maybe (List Proc)) →
                     (m >>= λ ps' → just (sys h ps')) ≡ just t →
                     setCtlSt ps i cwait waiting ≡ m → Clear t
            parked nothing eql _ = nope eql
            parked (just ps') refl el =
              clear (refs0 h ps' ze
                      (setCtl-ctl0 i ps cwait waiting ps' zctl (ctl0 ec here) el)
                      (trans (cong (count τ) (setCtl-refsEq i ps cwait waiting ps' el)) zr))
                    fit

  arm-clear : ∀ h ps i t → arm1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  arm-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → arm1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → arm1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignoreT τf k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
        sealProc h ps i t (pr (go (flushT τf k) env eth d (τf ∷ dm)))
          ze zctl zr fit (ctl0 ec here) eqc

  flush-clear : ∀ h ps i t → flush1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  flush-clear h ps i t eq c0@(clear _ _) = from (lookup (procs (sys h ps)) i) eq refl
    where
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → flush1 (sys h ps) i ≡ just t →
           lookup (procs (sys h ps)) i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      onC : (c : Ctl) → flush1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (flushT τf _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec =
        consume-keep h ps i τf finishFlush t eqc (finishFlush-refs τf) c0

  npeek-clear : ∀ h ps i t → npeek1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  npeek-clear h ps i t eq c0@(clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → npeek1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → npeek1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ncheckT τf k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
        onB (inboxHas (inbox p) τf) refl eqc
        where
        onB : (b : Bool) → inboxHas (inbox p) τf ≡ b →
              npeekOn h ps i (pr (go (ncheckT τf k) env eth d dm)) b ≡ just t →
              Clear t
        onB true _ eqb =
          consume-keep h ps i τf finishPeek t eqb (finishPeek-refs τf) c0
        onB false _ eqb =
          sealProc h ps i t (pr (go (ndemonT τf k) env eth d dm))
            ze zctl zr fit (ctl0 ec here) eqb

  ndemon-clear : ∀ h ps i t → ndemon1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  ndemon-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → ndemon1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → ndemon1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ndemonT τf k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
        sealProc h ps i t (pr (go k env eth d (τf ∷ dm))) ze zctl zr fit (ctl0 ec here) eqc

  seq-clear : ∀ h ps i t → seq1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  seq-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → seq1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → seq1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (seq e k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
        sealProc h ps i t c' ze zctl zr fit znew eqc
        where
        c' = ev e env (saved (go k [] eth d dm) ∷ [])
        ze0 = proj₁ (++0 env (flightRefs eth) (ctl0 ec here))
        zfl = proj₂ (++0 env (flightRefs eth) (ctl0 ec here))
        znew = 0++ env (flightRefs eth ++ []) ze0 (trans (count-idʳ (flightRefs eth)) zfl)

  bind-clear : ∀ h ps i t → bind1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  bind-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → bind1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      onC : (c : Ctl) → bind1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv r env []) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ (ar _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ (fn _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ (su ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ (mt _ _ _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ (bd _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ (saved (go _ _ _ _ _) ∷ _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv r env (saved (go k cenv eth d dm) ∷ [])) eqc lk0 ec rewrite lk0 | ec =
        sealProc h ps i t c' ze zctl zr fit znew eqc
        where
        c' = pr (go k (r ∷ (env ++ cenv)) eth d dm)
        tail0 = env ++ ((cenv ++ flightRefs eth) ++ [])
        nr = proj₁ (head0 r tail0 (ctl0 ec here))
        zrest = proj₂ (head0 r tail0 (ctl0 ec here))
        ze0 = proj₁ (++0 env ((cenv ++ flightRefs eth) ++ []) zrest)
        zpad = proj₂ (++0 env ((cenv ++ flightRefs eth) ++ []) zrest)
        zboth = trans (sym (count-idʳ (cenv ++ flightRefs eth))) zpad
        zcenv = proj₁ (++0 cenv (flightRefs eth) zboth)
        zfl = proj₂ (++0 cenv (flightRefs eth) zboth)
        znew = 0++ (r ∷ (env ++ cenv)) (flightRefs eth)
                 (cons0 r (env ++ cenv) nr (0++ env cenv ze0 zcenv)) zfl

  done-clear : ∀ h ps i t → done1 (sys h ps) i ≡ just t → Clear (sys h ps) → Clear t
  done-clear h ps i t eq (clear zc fit) = from (lookup ps i) eq refl
    where
    ze = proj₁ (parts h ps zc)
    zctl = proj₁ (proj₂ (parts h ps zc))
    zr = proj₂ (proj₂ (parts h ps zc))
    nope : nothing ≡ just t → Clear t
    nope ()
    from : (m : Maybe Proc) → done1 (sys h ps) i ≡ just t → lookup ps i ≡ m → Clear t
    from nothing eqa lk rewrite lk = nope eqa
    from (just p) eqa lk = onC (ctl p) eqa lk refl
      where
      here = lookup-ctl0 i ps p lk zctl
      zr0 = lookup-refs0 i ps p lk zr
      onC : (c : Ctl) → done1 (sys h ps) i ≡ just t →
            lookup ps i ≡ just p → ctl p ≡ c → Clear t
      onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
      onC (pr (go {n} done env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
        sealUpd h ps i t p p' lk0 ze zctl zr fit zfl zin eqc
        where
        p' = record p { state = pstDone ; roots = [] ; ctl = pr (go {n} done [] eth d dm) }
        zfl = proj₂ (++0 env (flightRefs eth) (ctl0 ec here))
        zin = proj₂ (++0 (roots p) (mapRef (inbox p)) zr0)

  step-clear : ∀ {s t} → PStep s t → Clear s → Clear t
  step-clear (p-lift (step-deref eq)) c = deref-clear _ _ _ _ eq c
  step-clear (p-lift (step-send eq)) c = send-clear _ _ _ _ _ _ eq c
  step-clear (p-lift (step-recv eq)) c = recv-clear _ _ _ _ eq c
  step-clear (p-lift (step-alloc eq)) c = alloc-clear _ _ _ _ _ _ eq c
  step-clear (p-lift (step-reuse eq)) c = reuse-clear _ _ _ _ _ _ eq c
  step-clear (p-lift (step-eval eq)) c = eval-clear _ _ _ _ eq c
  step-clear (p-lift step-collect) c = collect-clear _ c
  step-clear (p-spawn eq) c = spawn-clear _ _ _ _ eq c
  step-clear (p-emit eq) c = emit-clear _ _ _ _ eq c
  step-clear (p-deliver eq) c = deliver-clear _ _ _ _ eq c
  step-clear (p-recv eq) c = recvP-clear _ _ _ _ eq c
  step-clear (p-await eq) c = await-clear _ _ _ _ eq c
  step-clear (p-arm eq) c = arm-clear _ _ _ _ eq c
  step-clear (p-flush eq) c = flush-clear _ _ _ _ eq c
  step-clear (p-npeek eq) c = npeek-clear _ _ _ _ eq c
  step-clear (p-ndemon eq) c = ndemon-clear _ _ _ _ eq c
  step-clear (p-seq eq) c = seq-clear _ _ _ _ eq c
  step-clear (p-bind eq) c = bind-clear _ _ _ _ eq c
  step-clear (p-done eq) c = done-clear _ _ _ _ eq c

  steps : ∀ {s t} → PStep* s t → Clear s → Clear t
  steps pdone c = c
  steps (pmore st later) c = steps later (step-clear st c)

  inbox-none : ∀ ms → count τ (mapRef ms) ≡ 0 → inboxHas ms τ ≡ false
  inbox-none [] _ = refl
  inbox-none (msg r ∷ ms) eq =
    let nr , zrest = head0 r (mapRef ms) eq
    in body nr (inbox-none ms zrest)
    where
    body : (obj r ≡ᵇ τ) ≡ false → inboxHas ms τ ≡ false → inboxHas (msg r ∷ ms) τ ≡ false
    body nr nh rewrite nr | nh = refl

  mail-none : ∀ ps i → count τ (refsPs ps) ≡ 0 → mailHas ps i τ ≡ false
  mail-none ps i z = from (lookup ps i) refl
    where
    from : (m : Maybe Proc) → lookup ps i ≡ m → mailHas ps i τ ≡ false
    from nothing eq rewrite eq = refl
    from (just p) eq rewrite eq =
      inbox-none (inbox p) (proj₂ (++0 (roots p) (mapRef (inbox p)) (lookup-refs0 i ps p eq z)))

  theorem : ∀ {s t i} → PStep* s t → ReplyDone s i τ → mailHas (procs t) i τ ≡ false
  theorem {t = t} {i = i} tr (replied zc fit _) =
    mail-none (procs t) i
      (proj₂ (proj₂ (parts (heap t) (procs t) (cnt (steps tr (clear zc fit))))))

no-stray-reply : ∀ {s t i τ} → PStep* s t → ReplyDone s i τ → mailHas (procs t) i τ ≡ false
no-stray-reply {τ = τ} tr d = Preserve.theorem τ tr d

ignore-consumes : ∀ {h ps i t τ n} {k : PTm n} {env eth d dm p} →
  lookup ps i ≡ just p →
  ctl p ≡ pr (go (flushT τ k) env eth d dm) →
  flush1 (sys h ps) i ≡ just t →
  τ < length h →
  ReplyDone t i τ
ignore-consumes {h = h} {ps = ps} {i = i} {t = t} {τ = τ} lk ec eq fit =
  Preserve.ignore-consumes τ {h = h} {ps = ps} {i = i} {t = t} lk ec eq fit

await-consumes : ∀ {h ps i t τ n} {k : PTm n} {env eth d dm p} →
  lookup ps i ≡ just p →
  ctl p ≡ pr (go (awaitT τ k) env eth d dm) →
  inboxHas (inbox p) τ ≡ true →
  await1 (sys h ps) i ≡ just t →
  τ < length h →
  ReplyDone t i τ
await-consumes {h = h} {ps = ps} {i = i} {t = t} {τ = τ} lk ec hb eq fit =
  Preserve.await-consumes τ {h = h} {ps = ps} {i = i} {t = t} lk ec hb eq fit
