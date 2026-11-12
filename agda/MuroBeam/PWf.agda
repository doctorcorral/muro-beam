------------------------------------------------------------------------
-- Well-formedness of the process layer.
--
-- `PStep` keeps the v1a invariant: every reference index lies in the
-- heap, and a grade-1 reference is the only reference to its object.
-- Spawn reuses the v0 move and copy accounting. A fresh placeholder is
-- grade 0, so it is not a second grade-1 alias. Flush and a consuming
-- await only delete or replace the reply, and the replacement is that
-- same grade-0 placeholder.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.PWf where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _≡ᵇ_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Grade using (Grade; g0; g1; GTm)

open import MuroBeam.Grade using
  ( selfKept; isG1; isZeroGrade; kind; Kind; Kmove; Kcopy; copy-not-g1 )
open import MuroBeam.Heap using
  ( Obj; cell; live; Val; nat; Ref; ref; obj; checked; residual
  ; count; hasG1; Grade1Unique; count-++; has-++; count-snoc; has-snoc
  ; Bound; bnil; bcons; bound-++
  ; count0-has; bound-count0; obj≠
  ; same-unique
  ; repl; edgeRefs )
open import MuroBeam.Lib using
  ( ⊥; ⊥-elim; ≤-refl; ≤-trans; ≤-antisym; ≤-subst; ≤-step
  ; +-assoc; +-comm; +-identityʳ; +-zero; +-suc; +-swap; +-mono
  ; k≤n+k; m≤m+k; ≤-+ˡ; ≤-+ʳ
  ; ≡ᵇ-sound; ≡ᵇ-refl
  ; ∨-assoc; ∨-comm; ∨-swap; ∨-falseʳ; ∨-trueʳ; ext
  ; lookup; update; mapCons
  ; ++-assoc; ++-identityʳ )
open import MuroBeam.Process using
  ( Proc; proc; PState; ready; waiting; Sys; sys; heap; procs
  ; ctl; Ctl; idle; ev; rv; pr
  ; Frame; ar; fn; su; mt; bd; saved
  ; roots; inbox; state; Msg; msg; mapRef; post
  ; refsP; refsPs; refsOf; ctlRefs; ctlRefsPs; framesRefs; frameRefs
  ; preOf; mapSys; setProc; snoc
  ; AllInv; residual-inv-refs; ctlEq-update )
  renaming (done to pstDone)
open import MuroBeam.Collect using (Step)
open import MuroBeam.PSyntax using
  ( Thin; PTm; done; send; recv; spawn; seq; await; ignore; nignore
  ; awaitT; ignoreT; flushT; ncheckT; ndemonT
  ; Flight; flight; flightRef; flightRefs; Code; go; codeRefs; applyMoves )
open import MuroBeam.PRun using
  ( PStep; PStep*; p-lift; p-spawn; p-emit; p-deliver; p-recv
  ; p-await; p-arm; p-flush; p-npeek; p-ndemon; p-seq; p-bind; p-done
  ; pmore; pdone
  ; _>>=_
  ; spawn1; emit1; deliver1; recv1; await1; arm1; flush1
  ; npeek1; ndemon1; seq1; bind1; done1
  ; placeholder; splitGo; Split
  ; setCtlSt; recvStep; pullCtl; pullCode; pullFrames
  ; inboxHas; awaitOn; awaitPark; npeekOn
  ; deadInCtl; hasTag; blocked
  ; consume; finishFlush; finishAwait; finishPeek
  ; scrubOne; scrubRefs; scrubFrame; scrubFrames; scrubCtl; scrubProc
  ; dropRefs; dropMsgs; dropFlights
  ; wake )
open import MuroBeam.Unique using
  ( WF; step-preserves-grade1; thin-unique; grow-unique
  ; xfer-set; grow-sys; fresh-zero; set-both; set-refsPs; Both; both
  ; ctl-bound-at; bound-split; edge-nat; monoS; length-snoc; fresh-<
  ; repl-swap; repl-move-has; has-nong1
  ; upd-count; upd-has; upd-bound; upd-add; sealMove; lookup-bound
  ; bound-lookup
  ; post-count; post-has; post-bound; true≢false; ∧-falseʳ; just-inj
  ; +-right; has-count; mapRef-++
  ; lift-plus; lift-has; set-ctl-bound; bound-snoc; bound-repl-< )
open import MuroBeam.Stray using
  ( Hand; hn-nil; hn-skip; hn-move; hn-copy; split-hand
  ; flightRefs-++ ; refsPs-++ ; ctlRefsPs-++ )
open import MuroBeam.PTm using (CheckedP; lowerP; lowerP-wf)

------------------------------------------------------------------------
-- Counting.
------------------------------------------------------------------------

g0-ng : isG1 g0 ≡ false
g0-ng = refl

count-pad : ∀ k xs → count k (xs ++ []) ≡ count k xs
count-pad k xs rewrite count-++ k xs [] | +-identityʳ (count k xs) = refl

has-pad : ∀ k xs → hasG1 k (xs ++ []) ≡ hasG1 k xs
has-pad k xs rewrite has-++ k xs [] | ∨-falseʳ (hasG1 k xs) = refl

bound-pad : ∀ {n} xs → Bound n xs → Bound n (xs ++ [])
bound-pad xs b = subst (Bound _) (sym (++-identityʳ xs)) b

-- A non-g1 reference sitting in a unique list cannot be a live g1 object.
occ-ext : ∀ k pre r post →
  isG1 (checked r) ≡ false →
  Grade1Unique (pre ++ r ∷ post) →
  hasG1 k (pre ++ r ∷ post) ≡ true →
  ext (obj r ≡ᵇ k) ≡ 0
occ-ext k pre r post ng uq hf = contra (obj r ≡ᵇ k) refl
  where
  contra : (b : Bool) → (obj r ≡ᵇ k) ≡ b → ext (obj r ≡ᵇ k) ≡ 0
  contra false eb rewrite eb = refl
  contra true eb = ⊥-elim (true≢false (trans (sym hf) gone))
    where
    suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
    suc-inj refl = refl
    total : count k (pre ++ r ∷ post) ≡ 1
    total = uq k hf
    opened : count k pre + (ext (obj r ≡ᵇ k) + count k post) ≡ 1
    opened = trans (sym (count-++ k pre (r ∷ post))) total
    opened' : count k pre + suc (count k post) ≡ 1
    opened' = subst (λ b → count k pre + (ext b + count k post) ≡ 1) eb opened
    shifted : suc (count k pre + count k post) ≡ suc zero
    shifted = trans (sym (+-suc (count k pre) (count k post))) opened'
    zSum : count k pre + count k post ≡ zero
    zSum = suc-inj shifted
    zPre : count k pre ≡ zero
    zPre = proj₁ (+-zero (count k pre) (count k post) zSum)
    zPost : count k post ≡ zero
    zPost = proj₂ (+-zero (count k pre) (count k post) zSum)
    tail : hasG1 k (r ∷ post) ≡ false
    tail =
      trans (cong (λ b → (b ∧ isG1 (checked r)) ∨ hasG1 k post) eb)
      (trans (cong (λ g → (true ∧ g) ∨ hasG1 k post) ng)
             (count0-has k post zPost))
    gone : hasG1 k (pre ++ r ∷ post) ≡ false
    gone =
      trans (has-++ k pre (r ∷ post))
      (trans (cong (hasG1 k pre ∨_) tail)
      (trans (cong (λ b → b ∨ false) (count0-has k pre zPre))
             (∨-falseʳ false)))

ctlHere : ∀ h ps i p → WF (sys h ps) → lookup ps i ≡ just p →
          Bound (length h) (ctlRefs (ctl p))
ctlHere h ps i p wf lk =
  ctl-bound-at i ps p lk
    (proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps)
              (proj₁ (bound-split (preOf h ps) (refsPs ps) (proj₁ wf)))))

refsHere : ∀ h ps i p → WF (sys h ps) → lookup ps i ≡ just p →
           Bound (length h) (refsP p)
refsHere h ps i p wf lk =
  lookup-bound i ps p
    (proj₂ (bound-split (preOf h ps) (refsPs ps) (proj₁ wf))) lk

-- setProc whose new control has the same reference multiset.
keep-counts : ∀ h ps i p c t →
  WF (sys h ps) →
  lookup ps i ≡ just p →
  (setProc ps i c >>= λ ps' → just (sys h ps')) ≡ just t →
  (∀ k → count k (ctlRefs c) ≡ count k (ctlRefs (ctl p))) →
  (∀ k → hasG1 k (ctlRefs c) ≡ hasG1 k (ctlRefs (ctl p))) →
  Bound (length h) (ctlRefs c) →
  WF t
keep-counts h ps i p c t wf lk eq cq hq bc = landed (setProc ps i c) eq refl
  where
  nope : nothing ≡ just t → WF t
  nope ()
  landed : (m : Maybe (List Proc)) →
           (m >>= λ ps' → just (sys h ps')) ≡ just t →
           setProc ps i c ≡ m → WF t
  landed nothing eql el rewrite el = nope eql
  landed (just ps') refl es = xfer-set h ps i p c ps' wf lk es cq hq bc

keep-set : ∀ h ps i p c t →
  WF (sys h ps) →
  lookup ps i ≡ just p →
  (setProc ps i c >>= λ ps' → just (sys h ps')) ≡ just t →
  ctlRefs c ≡ ctlRefs (ctl p) →
  WF t
keep-set h ps i p c t wf lk eq creq =
  keep-counts h ps i p c t wf lk eq
    (λ k → cong (count k) creq)
    (λ k → cong (hasG1 k) creq)
    (subst (Bound (length h)) (sym creq) (ctlHere h ps i p wf lk))

------------------------------------------------------------------------
-- Handover. `bonus` is the extra aliases: one placeholder per move,
-- one extra copy per copied slot. Grade 1 is not among them.
------------------------------------------------------------------------

bonus : ∀ {ph rs ce pe} → Hand ph rs ce pe → ℕ → ℕ
bonus hn-nil _ = zero
bonus (hn-skip h) k = bonus h k
bonus {ph} (hn-move _ h) k = ext (obj ph ≡ᵇ k) + bonus h k
bonus (hn-copy {r} _ h) k = ext (obj r ≡ᵇ k) + bonus h k

-- a + (e + p) ≡ (a + p) + e
rot3 : ∀ a e p → a + (e + p) ≡ (a + p) + e
rot3 a e p =
  trans (cong (a +_) (+-comm e p))
        (sym (+-assoc a p e))

-- (a + b) + (c + d) ≡ (a + c) + (b + d)
add2 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
add2 a b c d =
  trans (+-assoc a b (c + d))
  (trans (cong (a +_) (cong (b +_) (+-comm c d)))
  (trans (cong (a +_) (sym (+-assoc b d c)))
  (trans (cong (a +_) (+-comm (b + d) c))
         (sym (+-assoc a c (b + d))))))

-- (a + e) + (s + d) ≡ (a + s) + (e + d)
cross : ∀ a e s d → (a + e) + (s + d) ≡ (a + s) + (e + d)
cross a e s d =
  trans (sym (+-assoc (a + e) s d))
  (trans (cong (_+ d) (+-assoc a e s))
  (trans (cong (λ z → (a + z) + d) (+-comm e s))
  (trans (cong (_+ d) (sym (+-assoc a s e)))
         (+-assoc (a + s) e d))))

hand-count : ∀ {ph rs ce pe} (hn : Hand ph rs ce pe) k →
  count k (ce ++ pe) ≡ count k rs + bonus hn k
hand-count hn-nil k = refl
hand-count (hn-skip {r} {rs} {ce} {pe} h) k =
  let a = count k ce
      e = ext (obj r ≡ᵇ k)
      p = count k pe
      s = count k rs
      d = bonus h k
      ih = hand-count h k
  in trans (count-++ k ce (r ∷ pe))
     (trans (rot3 a e p)
     (trans (cong (_+ e) (sym (count-++ k ce pe)))
     (trans (cong (_+ e) ih)
     (trans (+-comm (s + d) e)
            (sym (+-assoc e s d))))))
hand-count {ph} (hn-move {r} {rs} {ce} {pe} _ h) k =
  let a = ext (obj r ≡ᵇ k)
      b = count k ce
      e = ext (obj ph ≡ᵇ k)
      p = count k pe
      s = count k rs
      d = bonus h k
      ih = hand-count h k
  in trans (count-++ k (r ∷ ce) (ph ∷ pe))
     (trans (add2 a b e p)
     (trans (cong ((a + e) +_) (trans (sym (count-++ k ce pe)) ih))
            (cross a e s d)))
hand-count (hn-copy {r} {rs} {ce} {pe} _ h) k =
  let a = ext (obj r ≡ᵇ k)
      b = count k ce
      p = count k pe
      s = count k rs
      d = bonus h k
      ih = hand-count h k
  in trans (count-++ k (r ∷ ce) (r ∷ pe))
     (trans (add2 a b a p)
     (trans (cong ((a + a) +_) (trans (sym (count-++ k ce pe)) ih))
            (cross a a s d)))

gbit : Ref → ℕ → Bool
gbit r k = (obj r ≡ᵇ k) ∧ isG1 (checked r)

∨-idem : ∀ b → (b ∨ b) ≡ b
∨-idem true  = refl
∨-idem false = refl

-- a ∨ (b ∨ (a ∨ c)) ≡ a ∨ (b ∨ c)
absorb : ∀ a b c → a ∨ (b ∨ (a ∨ c)) ≡ a ∨ (b ∨ c)
absorb a b c =
  trans (cong (a ∨_) (sym (∨-assoc b a c)))
  (trans (cong (λ z → a ∨ (z ∨ c)) (∨-comm b a))
  (trans (cong (a ∨_) (∨-assoc a b c))
  (trans (sym (∨-assoc a a (b ∨ c)))
         (cong (λ z → z ∨ (b ∨ c)) (∨-idem a)))))

hand-has : ∀ {ph rs ce pe} (hn : Hand ph rs ce pe) k →
  isG1 (checked ph) ≡ false →
  hasG1 k (ce ++ pe) ≡ hasG1 k rs
hand-has hn-nil k _ = refl
hand-has (hn-skip {r} {ce = ce} {pe = pe} h) k np =
  trans (has-++ k ce (r ∷ pe))
  (trans (sym (∨-assoc (hasG1 k ce) (gbit r k) (hasG1 k pe)))
  (trans (cong (_∨ hasG1 k pe) (∨-comm (hasG1 k ce) (gbit r k)))
  (trans (∨-assoc (gbit r k) (hasG1 k ce) (hasG1 k pe))
  (trans (cong (gbit r k ∨_) (sym (has-++ k ce pe)))
         (cong (gbit r k ∨_) (hand-has h k np))))))
hand-has {ph} (hn-move {r} {ce = ce} {pe = pe} _ h) k np =
  trans (has-++ k (r ∷ ce) (ph ∷ pe))
  (trans (cong (hasG1 k (r ∷ ce) ∨_) drop)
  (trans (∨-assoc (gbit r k) (hasG1 k ce) (hasG1 k pe))
  (trans (cong (gbit r k ∨_) (sym (has-++ k ce pe)))
         (cong (gbit r k ∨_) (hand-has h k np)))))
  where
  drop : hasG1 k (ph ∷ pe) ≡ hasG1 k pe
  drop =
    trans (cong (λ b → b ∨ hasG1 k pe) (cong ((obj ph ≡ᵇ k) ∧_) np))
          (cong (λ b → b ∨ hasG1 k pe) (∧-falseʳ (obj ph ≡ᵇ k)))
hand-has (hn-copy {r} {ce = ce} {pe = pe} _ h) k np =
  trans (has-++ k (r ∷ ce) (r ∷ pe))
  (trans (∨-assoc (gbit r k) (hasG1 k ce) (gbit r k ∨ hasG1 k pe))
  (trans (absorb (gbit r k) (hasG1 k ce) (hasG1 k pe))
  (trans (cong (gbit r k ∨_) (sym (has-++ k ce pe)))
         (cong (gbit r k ∨_) (hand-has h k np)))))

-- pre ++ (r ∷ (rs ++ post)) ≡ (pre ++ (r ∷ [])) ++ (rs ++ post)
regroup' : (pre : List Ref) (r : Ref) (rs post : List Ref) →
  pre ++ (r ∷ rs ++ post) ≡ (pre ++ (r ∷ [])) ++ (rs ++ post)
regroup' pre r rs post = sym (++-assoc pre (r ∷ []) (rs ++ post))

bonus-zero : ∀ {ph rs ce pe} (hn : Hand ph rs ce pe) k pre post →
  Bound (obj ph) (pre ++ rs ++ post) →
  isG1 (checked ph) ≡ false →
  Grade1Unique (pre ++ rs ++ post) →
  hasG1 k (pre ++ rs ++ post) ≡ true →
  bonus hn k ≡ 0
bonus-zero hn-nil k pre post _ _ _ _ = refl
bonus-zero {ph} (hn-skip {r} {rs} h) k pre post b0 np uq hf =
  bonus-zero h k (pre ++ (r ∷ [])) post
    (subst (Bound (obj ph)) (regroup' pre r rs post) b0) np
    (subst Grade1Unique (regroup' pre r rs post) uq)
    (subst (λ xs → hasG1 k xs ≡ true) (regroup' pre r rs post) hf)
bonus-zero {ph} (hn-move {r} {rs} _ h) k pre post b0 np uq hf =
  trans (cong (_+ bonus h k)
          (fresh-zero k (obj ph) (pre ++ (r ∷ rs) ++ post) b0 hf))
  (cong (zero +_)
    (bonus-zero h k (pre ++ (r ∷ [])) post
      (subst (Bound (obj ph)) (regroup' pre r rs post) b0) np
      (subst Grade1Unique (regroup' pre r rs post) uq)
      (subst (λ xs → hasG1 k xs ≡ true) (regroup' pre r rs post) hf)))
bonus-zero {ph} (hn-copy {r} {rs} ek h) k pre post b0 np uq hf =
  trans (cong (_+ bonus h k)
          (occ-ext k pre r (rs ++ post) (copy-not-g1 (checked r) ek) uq hf))
  (cong (zero +_)
    (bonus-zero h k (pre ++ (r ∷ [])) post
      (subst (Bound (obj ph)) (regroup' pre r rs post) b0) np
      (subst Grade1Unique (regroup' pre r rs post) uq)
      (subst (λ xs → hasG1 k xs ≡ true) (regroup' pre r rs post) hf)))

------------------------------------------------------------------------
-- Steps whose control references have the same multiset.
------------------------------------------------------------------------

nope : ∀ {t : Sys} → nothing ≡ just t → WF t
nope ()

seq-count : ∀ k env eth →
  count k (env ++ (flightRefs eth ++ [])) ≡ count k (env ++ flightRefs eth)
seq-count k env eth =
  trans (count-++ k env (flightRefs eth ++ []))
  (trans (cong (count k env +_) (count-pad k (flightRefs eth)))
         (sym (count-++ k env (flightRefs eth))))

seq-has : ∀ k env eth →
  hasG1 k (env ++ (flightRefs eth ++ [])) ≡ hasG1 k (env ++ flightRefs eth)
seq-has k env eth =
  trans (has-++ k env (flightRefs eth ++ []))
  (trans (cong (hasG1 k env ∨_) (has-pad k (flightRefs eth)))
         (sym (has-++ k env (flightRefs eth))))

seq-bound : ∀ {n} env eth →
  Bound n (env ++ flightRefs eth) →
  Bound n (env ++ (flightRefs eth ++ []))
seq-bound env eth b =
  let be , bf = bound-split env (flightRefs eth) b
  in bound-++ be (bound-pad (flightRefs eth) bf)

add4 : ∀ a b c d → a + (b + (c + d)) ≡ (a + (b + c)) + d
add4 a b c d =
  trans (cong (a +_) (sym (+-assoc b c d)))
        (sym (+-assoc a (b + c) d))

bind-count : ∀ k r env cenv eth →
  count k ((r ∷ (env ++ cenv)) ++ flightRefs eth) ≡
  count k (r ∷ env ++ ((cenv ++ flightRefs eth) ++ []))
bind-count k r env cenv eth = trans newN (sym oldN)
  where
  fl = flightRefs eth
  er = ext (obj r ≡ᵇ k)
  E = count k env
  C = count k cenv
  F = count k fl
  newN : count k ((r ∷ (env ++ cenv)) ++ fl) ≡ (er + (E + C)) + F
  newN =
    trans (count-++ k (r ∷ (env ++ cenv)) fl)
          (cong (_+ F) (cong (er +_) (count-++ k env cenv)))
  oldN : count k (r ∷ env ++ ((cenv ++ fl) ++ [])) ≡ (er + (E + C)) + F
  oldN =
    trans (cong (er +_) (count-++ k env ((cenv ++ fl) ++ [])))
    (trans (cong (λ n → er + (E + n)) (count-++ k (cenv ++ fl) []))
    (trans (cong (λ n → er + (E + (n + zero))) (count-++ k cenv fl))
    (trans (cong (λ n → er + (E + n)) (+-identityʳ (C + F)))
           (add4 er E C F))))

bind-has : ∀ k r env cenv eth →
  hasG1 k ((r ∷ (env ++ cenv)) ++ flightRefs eth) ≡
  hasG1 k (r ∷ env ++ ((cenv ++ flightRefs eth) ++ []))
bind-has k r env cenv eth = trans newN (sym oldN)
  where
  fl = flightRefs eth
  a = gbit r k
  b = hasG1 k env
  c = hasG1 k cenv
  d = hasG1 k fl
  newN : hasG1 k ((r ∷ (env ++ cenv)) ++ fl) ≡ a ∨ (b ∨ (c ∨ d))
  newN =
    trans (has-++ k (r ∷ (env ++ cenv)) fl)
    (trans (cong (_∨ d) (cong (a ∨_) (has-++ k env cenv)))
    (trans (∨-assoc a (b ∨ c) d)
           (cong (a ∨_) (∨-assoc b c d))))
  oldN : hasG1 k (r ∷ env ++ ((cenv ++ fl) ++ [])) ≡ a ∨ (b ∨ (c ∨ d))
  oldN =
    trans (cong (a ∨_) (has-++ k env ((cenv ++ fl) ++ [])))
    (trans (cong (λ z → a ∨ (b ∨ z)) (has-++ k (cenv ++ fl) []))
    (trans (cong (λ z → a ∨ (b ∨ (z ∨ false))) (has-++ k cenv fl))
           (cong (λ z → a ∨ (b ∨ z)) (∨-falseʳ (c ∨ d)))))

bind-bound : ∀ {n} r env cenv eth →
  Bound n (r ∷ env ++ ((cenv ++ flightRefs eth) ++ [])) →
  Bound n ((r ∷ (env ++ cenv)) ++ flightRefs eth)
bind-bound r env cenv eth (bcons lt rest) =
  let fl = flightRefs eth
      bE = proj₁ (bound-split env ((cenv ++ fl) ++ []) rest)
      bPad = proj₂ (bound-split env ((cenv ++ fl) ++ []) rest)
      bCF = subst (Bound _) (++-identityʳ (cenv ++ fl)) bPad
      bC = proj₁ (bound-split cenv fl bCF)
      bF = proj₂ (bound-split cenv fl bCF)
  in bound-++ (bcons lt (bound-++ bE bC)) bF

arm-wf : ∀ h ps i t → WF (sys h ps) → arm1 (sys h ps) i ≡ just t → WF t
arm-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → arm1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = nope eqa
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → arm1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
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
    onC (pr (go (ignoreT τ k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
      keep-set h ps i p (pr (go (flushT τ k) env eth d (τ ∷ dm))) t wf lk0 eqc
        (subst (λ c0 → ctlRefs (pr (go (flushT τ k) env eth d (τ ∷ dm))) ≡ ctlRefs c0)
               (sym ec) refl)

ndemon-wf : ∀ h ps i t → WF (sys h ps) → ndemon1 (sys h ps) i ≡ just t → WF t
ndemon-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → ndemon1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = nope eqa
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → ndemon1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
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
    onC (pr (go (ndemonT τ k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
      keep-set h ps i p (pr (go k env eth d (τ ∷ dm))) t wf lk0 eqc
        (subst (λ c0 → ctlRefs (pr (go k env eth d (τ ∷ dm))) ≡ ctlRefs c0) (sym ec) refl)

seq-wf : ∀ h ps i t → WF (sys h ps) → seq1 (sys h ps) i ≡ just t → WF t
seq-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → seq1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = nope eqa
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → seq1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
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
      keep-counts h ps i p c t wf lk0 eqc
        (λ q → subst (λ c0 → count q (ctlRefs c) ≡ count q (ctlRefs c0)) (sym ec) (seq-count q env eth))
        (λ q → subst (λ c0 → hasG1 q (ctlRefs c) ≡ hasG1 q (ctlRefs c0)) (sym ec) (seq-has q env eth))
        (seq-bound env eth (subst (λ c0 → Bound (length h) (ctlRefs c0)) ec (ctlHere h ps i p wf lk0)))
      where c = ev e env (saved (go k [] eth d dm) ∷ [])

bind-wf : ∀ h ps i t → WF (sys h ps) → bind1 (sys h ps) i ≡ just t → WF t
bind-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → bind1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = nope eqa
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → bind1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (pr _) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv _ _ []) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv _ _ (ar _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv _ _ (fn _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv _ _ (su ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv _ _ (mt _ _ _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv _ _ (bd _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv _ _ (saved (go _ _ _ _ _) ∷ _ ∷ _)) eqc lk0 ec rewrite lk0 | ec = nope eqc
    onC (rv r env (saved (go k cenv eth d dm) ∷ [])) eqc lk0 ec rewrite lk0 | ec =
      keep-counts h ps i p c t wf lk0 eqc
        (λ q → subst (λ c0 → count q (ctlRefs c) ≡ count q (ctlRefs c0)) (sym ec) (bind-count q r env cenv eth))
        (λ q → subst (λ c0 → hasG1 q (ctlRefs c) ≡ hasG1 q (ctlRefs c0)) (sym ec) (bind-has q r env cenv eth))
        (bind-bound r env cenv eth (subst (λ c0 → Bound (length h) (ctlRefs c0)) ec (ctlHere h ps i p wf lk0)))
      where c = pr (go k (r ∷ (env ++ cenv)) eth d dm)

------------------------------------------------------------------------
-- A fresh grade-0 cell may replace a tag. Counts of every other index
-- do not grow, and the fresh index is not grade 1.
------------------------------------------------------------------------

≤-sum : ∀ {a b c d} → a ≤ c → b ≤ d → a + b ≤ c + d
≤-sum = +-mono

subst₂ : ∀ {A : Set} (P : A → A → Set) {a b c d : A} →
  a ≡ c → b ≡ d → P c d → P a b
subst₂ P refl refl p0 = p0

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
  x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ _ refl refl = refl

≤-++ : ∀ k xs xs' ys ys' →
  count k xs ≤ count k xs' → count k ys ≤ count k ys' →
  count k (xs ++ ys) ≤ count k (xs' ++ ys')
≤-++ k xs xs' ys ys' lx ly =
  subst₂ (λ a b → a ≤ b) (count-++ k xs ys) (count-++ k xs' ys') (≤-sum lx ly)

drop-++ : ∀ τ xs ys → dropRefs τ (xs ++ ys) ≡ dropRefs τ xs ++ dropRefs τ ys
drop-++ τ [] ys = refl
drop-++ τ (r ∷ xs) ys with obj r ≡ᵇ τ
... | true = drop-++ τ xs ys
... | false rewrite drop-++ τ xs ys = refl

drop-count : ∀ k τ rs → count k (dropRefs τ rs) ≤ count k rs
drop-count k τ [] = z≤n
drop-count k τ (r ∷ rs) with obj r ≡ᵇ τ
... | true =
  ≤-trans (drop-count k τ rs)
          (k≤n+k (ext (obj r ≡ᵇ k)) (count k rs))
... | false = ≤-+ˡ (ext (obj r ≡ᵇ k)) (drop-count k τ rs)

drop-has : ∀ k τ rs → hasG1 k (dropRefs τ rs) ≡ true → hasG1 k rs ≡ true
drop-has k τ [] ()
drop-has k τ (r ∷ rs) hf with obj r ≡ᵇ τ
... | true =
  trans (cong (gbit r k ∨_) (drop-has k τ rs hf)) (∨-trueʳ (gbit r k))
... | false with (obj r ≡ᵇ k) ∧ isG1 (checked r) in eb
... | true rewrite eb = refl
... | false rewrite eb = drop-has k τ rs hf

scrub-count : ∀ k τ ph rs → (obj ph ≡ᵇ k) ≡ false →
  count k (scrubRefs τ ph rs) ≤ count k rs
scrub-count k τ ph [] hp = z≤n
scrub-count k τ ph (r ∷ rs) hp with obj r ≡ᵇ τ
... | true rewrite hp =
  ≤-trans (scrub-count k τ ph rs hp)
          (k≤n+k (ext (obj r ≡ᵇ k)) (count k rs))
... | false = ≤-+ˡ (ext (obj r ≡ᵇ k)) (scrub-count k τ ph rs hp)

scrub-has : ∀ k τ ph rs → isG1 (checked ph) ≡ false →
  hasG1 k (scrubRefs τ ph rs) ≡ true → hasG1 k rs ≡ true
scrub-has k τ ph [] ng ()
scrub-has k τ ph (r ∷ rs) ng hf with obj r ≡ᵇ τ
... | true rewrite ng | ∧-falseʳ (obj ph ≡ᵇ k) =
  trans (cong (gbit r k ∨_) (scrub-has k τ ph rs ng hf)) (∨-trueʳ (gbit r k))
... | false with (obj r ≡ᵇ k) ∧ isG1 (checked r) in eb
... | true rewrite eb = refl
... | false rewrite eb = scrub-has k τ ph rs ng hf

scrub-bound : ∀ {n} τ ph rs → Bound n rs → obj ph < n → Bound n (scrubRefs τ ph rs)
scrub-bound τ ph [] b _ = b
scrub-bound τ ph (r ∷ rs) (bcons lt rest) olt with obj r ≡ᵇ τ
... | true = bcons olt (scrub-bound τ ph rs rest olt)
... | false = bcons lt (scrub-bound τ ph rs rest olt)

drop-bound : ∀ {n} τ rs → Bound n rs → Bound n (dropRefs τ rs)
drop-bound τ [] b = b
drop-bound τ (r ∷ rs) (bcons lt rest) with obj r ≡ᵇ τ
... | true = drop-bound τ rs rest
... | false = bcons lt (drop-bound τ rs rest)

dropMsgs-refs : ∀ τ ms → mapRef (dropMsgs τ ms) ≡ dropRefs τ (mapRef ms)
dropMsgs-refs τ [] = refl
dropMsgs-refs τ (msg r ∷ ms) with obj r ≡ᵇ τ
... | true = dropMsgs-refs τ ms
... | false rewrite dropMsgs-refs τ ms = refl

dropFlights-refs : ∀ τ fs →
  flightRefs (dropFlights τ fs) ≡ dropRefs τ (flightRefs fs)
dropFlights-refs τ [] = refl
dropFlights-refs τ (flight j r ∷ fs) with obj r ≡ᵇ τ
... | true = dropFlights-refs τ fs
... | false rewrite dropFlights-refs τ fs = refl

frames-le : ∀ k τ ph fs → (obj ph ≡ᵇ k) ≡ false →
  count k (framesRefs (scrubFrames τ ph fs)) ≤ count k (framesRefs fs)

frame-le : ∀ k τ ph f → (obj ph ≡ᵇ k) ≡ false →
  count k (frameRefs (scrubFrame τ ph f)) ≤ count k (frameRefs f)
frame-le k τ ph (ar _) hp = ≤-refl
frame-le k τ ph su hp = ≤-refl
frame-le k τ ph (mt _ _ _) hp = ≤-refl
frame-le k τ ph (fn r) hp with obj r ≡ᵇ τ
... | true rewrite hp = z≤n
... | false = ≤-refl
frame-le k τ ph (bd env) hp = scrub-count k τ ph env hp
frame-le k τ ph (saved (go _ env eth _ _)) hp =
  ≤-++ k (scrubRefs τ ph env) env (flightRefs (dropFlights τ eth)) (flightRefs eth)
       (scrub-count k τ ph env hp)
       (subst (λ xs → count k xs ≤ count k (flightRefs eth))
              (sym (dropFlights-refs τ eth))
              (drop-count k τ (flightRefs eth)))

frames-le k τ ph [] hp = z≤n
frames-le k τ ph (f ∷ fs) hp =
  ≤-++ k (frameRefs (scrubFrame τ ph f)) (frameRefs f)
       (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
       (frame-le k τ ph f hp) (frames-le k τ ph fs hp)

ctl-le : ∀ k τ ph c → (obj ph ≡ᵇ k) ≡ false →
  count k (ctlRefs (scrubCtl τ ph c)) ≤ count k (ctlRefs c)
ctl-le k τ ph idle hp = ≤-refl
ctl-le k τ ph (ev _ e fs) hp =
  ≤-++ k (scrubRefs τ ph e) e (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
       (scrub-count k τ ph e hp) (frames-le k τ ph fs hp)
ctl-le k τ ph (rv r e fs) hp with obj r ≡ᵇ τ
... | true rewrite hp =
  ≤-trans (≤-++ k (scrubRefs τ ph e) e (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
                 (scrub-count k τ ph e hp) (frames-le k τ ph fs hp))
          (k≤n+k (ext (obj r ≡ᵇ k)) (count k (e ++ framesRefs fs)))
... | false =
  ≤-+ˡ (ext (obj r ≡ᵇ k))
       (≤-++ k (scrubRefs τ ph e) e (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
             (scrub-count k τ ph e hp) (frames-le k τ ph fs hp))
ctl-le k τ ph (pr (go _ env eth _ _)) hp =
  ≤-++ k (scrubRefs τ ph env) env (flightRefs (dropFlights τ eth)) (flightRefs eth)
       (scrub-count k τ ph env hp)
       (subst (λ xs → count k xs ≤ count k (flightRefs eth))
              (sym (dropFlights-refs τ eth))
              (drop-count k τ (flightRefs eth)))

refsP-le : ∀ k τ ph p → count k (refsP (scrubProc τ ph p)) ≤ count k (refsP p)
refsP-le k τ ph p =
  subst (λ xs → count k xs ≤ count k (refsP p))
        (sym (trans (cong (dropRefs τ (roots p) ++_) (dropMsgs-refs τ (inbox p)))
                    (sym (drop-++ τ (roots p) (mapRef (inbox p))))))
        (drop-count k τ (refsP p))

proc-le : ∀ k τ ph p → (obj ph ≡ᵇ k) ≡ false →
  count k (ctlRefs (ctl (scrubProc τ ph p))) + count k (refsP (scrubProc τ ph p)) ≤
  count k (ctlRefs (ctl p)) + count k (refsP p)
proc-le k τ ph p hp = ≤-sum (ctl-le k τ ph (ctl p) hp) (refsP-le k τ ph p)

map-le : ∀ k τ ph ps → (obj ph ≡ᵇ k) ≡ false →
  count k (ctlRefsPs (map (scrubProc τ ph) ps)) + count k (refsPs (map (scrubProc τ ph) ps)) ≤
  count k (ctlRefsPs ps) + count k (refsPs ps)
map-le k τ ph [] hp = ≤-refl
map-le k τ ph (p ∷ ps) hp =
  subst₂ (λ a b → a ≤ b) newEq oldEq
    (≤-sum (proc-le k τ ph p hp) (map-le k τ ph ps hp))
  where
  newEq =
    trans (cong₂ _+_
             (count-++ k (ctlRefs (ctl (scrubProc τ ph p)))
                        (ctlRefsPs (map (scrubProc τ ph) ps)))
             (count-++ k (refsP (scrubProc τ ph p))
                        (refsPs (map (scrubProc τ ph) ps))))
          (add2 (count k (ctlRefs (ctl (scrubProc τ ph p))))
                (count k (ctlRefsPs (map (scrubProc τ ph) ps)))
                (count k (refsP (scrubProc τ ph p)))
                (count k (refsPs (map (scrubProc τ ph) ps))))
  oldEq =
    trans (cong₂ _+_
             (count-++ k (ctlRefs (ctl p)) (ctlRefsPs ps))
             (count-++ k (refsP p) (refsPs ps)))
          (add2 (count k (ctlRefs (ctl p))) (count k (ctlRefsPs ps))
                (count k (refsP p)) (count k (refsPs ps)))

------------------------------------------------------------------------
-- Has-bits and bounds for the same scrub. The placeholder is grade 0,
-- so a grade-1 bit in the scrubbed list was already a grade-1 bit.
------------------------------------------------------------------------

∨-imp : ∀ a b c d →
  (a ≡ true → c ≡ true) →
  (b ≡ true → d ≡ true) →
  (a ∨ b) ≡ true →
  (c ∨ d) ≡ true
∨-imp true  _ c d f _ _ = cong (_∨ d) (f refl)
∨-imp false true c d _ g _ =
  trans (cong (c ∨_) (g refl)) (∨-trueʳ c)
∨-imp false false _ _ _ _ ()

∨-both-false : ∀ {a b} → a ≡ false → b ≡ false → (a ∨ b) ≡ false
∨-both-false refl refl = refl

-- (a ∨ b) ∨ (c ∨ d) ≡ (a ∨ c) ∨ (b ∨ d)
or-cross : ∀ a b c d → (a ∨ b) ∨ (c ∨ d) ≡ (a ∨ c) ∨ (b ∨ d)
or-cross a b c d =
  trans (∨-assoc a b (c ∨ d))
  (trans (cong (a ∨_) (sym (∨-assoc b c d)))
  (trans (cong (a ∨_) (cong (λ z → z ∨ d) (∨-comm b c)))
  (trans (cong (a ∨_) (∨-assoc c b d))
         (sym (∨-assoc a c (b ∨ d))))))

has-++-imp : ∀ k xs xs' ys ys' →
  (hasG1 k xs ≡ true → hasG1 k xs' ≡ true) →
  (hasG1 k ys ≡ true → hasG1 k ys' ≡ true) →
  hasG1 k (xs ++ ys) ≡ true →
  hasG1 k (xs' ++ ys') ≡ true
has-++-imp k xs xs' ys ys' hx hy hf =
  subst (λ z → z ≡ true) (sym (has-++ k xs' ys'))
    (∨-imp (hasG1 k xs) (hasG1 k ys) (hasG1 k xs') (hasG1 k ys') hx hy
      (subst (λ z → z ≡ true) (has-++ k xs ys) hf))

has-both-false : ∀ k xs ys →
  hasG1 k xs ≡ false → hasG1 k ys ≡ false →
  hasG1 k (xs ++ ys) ≡ false
has-both-false k xs ys hx hy =
  trans (has-++ k xs ys) (∨-both-false hx hy)

refsP-drop : ∀ τ ph p → refsP (scrubProc τ ph p) ≡ dropRefs τ (refsP p)
refsP-drop τ ph p =
  trans (cong (dropRefs τ (roots p) ++_) (dropMsgs-refs τ (inbox p)))
        (sym (drop-++ τ (roots p) (mapRef (inbox p))))

frames-has : ∀ k τ ph fs → isG1 (checked ph) ≡ false →
  hasG1 k (framesRefs (scrubFrames τ ph fs)) ≡ true →
  hasG1 k (framesRefs fs) ≡ true

frame-has : ∀ k τ ph f → isG1 (checked ph) ≡ false →
  hasG1 k (frameRefs (scrubFrame τ ph f)) ≡ true →
  hasG1 k (frameRefs f) ≡ true
frame-has k τ ph (ar _) ng ()
frame-has k τ ph su ng ()
frame-has k τ ph (mt _ _ _) ng ()
frame-has k τ ph (fn r) ng hf with obj r ≡ᵇ τ
... | true rewrite ng | ∧-falseʳ (obj ph ≡ᵇ k) =
  ⊥-elim (true≢false (sym hf))
... | false = hf
frame-has k τ ph (bd env) ng hf = scrub-has k τ ph env ng hf
frame-has k τ ph (saved (go _ env eth _ _)) ng hf =
  has-++-imp k (scrubRefs τ ph env) env
    (flightRefs (dropFlights τ eth)) (flightRefs eth)
    (scrub-has k τ ph env ng)
    (λ hb → drop-has k τ (flightRefs eth)
              (subst (λ xs → hasG1 k xs ≡ true) (dropFlights-refs τ eth) hb))
    hf

frames-has k τ ph [] ng ()
frames-has k τ ph (f ∷ fs) ng hf =
  has-++-imp k (frameRefs (scrubFrame τ ph f)) (frameRefs f)
    (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
    (frame-has k τ ph f ng) (frames-has k τ ph fs ng) hf

ctl-has : ∀ k τ ph c → isG1 (checked ph) ≡ false →
  hasG1 k (ctlRefs (scrubCtl τ ph c)) ≡ true →
  hasG1 k (ctlRefs c) ≡ true
ctl-has k τ ph idle ng ()
ctl-has k τ ph (ev _ e fs) ng hf =
  has-++-imp k (scrubRefs τ ph e) e
    (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
    (scrub-has k τ ph e ng) (frames-has k τ ph fs ng) hf
ctl-has k τ ph (rv r e fs) ng hf with obj r ≡ᵇ τ
... | true rewrite ng | ∧-falseʳ (obj ph ≡ᵇ k) =
  trans (cong (gbit r k ∨_) (rest hf)) (∨-trueʳ (gbit r k))
  where
  rest : hasG1 k (scrubRefs τ ph e ++ framesRefs (scrubFrames τ ph fs)) ≡ true →
         hasG1 k (e ++ framesRefs fs) ≡ true
  rest = has-++-imp k (scrubRefs τ ph e) e
           (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
           (scrub-has k τ ph e ng) (frames-has k τ ph fs ng)
... | false with gbit r k in eb
... | true rewrite eb = refl
... | false rewrite eb =
  has-++-imp k (scrubRefs τ ph e) e
    (framesRefs (scrubFrames τ ph fs)) (framesRefs fs)
    (scrub-has k τ ph e ng) (frames-has k τ ph fs ng) hf
ctl-has k τ ph (pr (go _ env eth _ _)) ng hf =
  has-++-imp k (scrubRefs τ ph env) env
    (flightRefs (dropFlights τ eth)) (flightRefs eth)
    (scrub-has k τ ph env ng)
    (λ hb → drop-has k τ (flightRefs eth)
              (subst (λ xs → hasG1 k xs ≡ true) (dropFlights-refs τ eth) hb))
    hf

refsP-has : ∀ k τ ph p →
  hasG1 k (refsP (scrubProc τ ph p)) ≡ true →
  hasG1 k (refsP p) ≡ true
refsP-has k τ ph p hf =
  drop-has k τ (refsP p)
    (subst (λ xs → hasG1 k xs ≡ true) (refsP-drop τ ph p) hf)

map-has : ∀ k τ ph ps → isG1 (checked ph) ≡ false →
  (hasG1 k (ctlRefsPs (map (scrubProc τ ph) ps)) ∨
   hasG1 k (refsPs (map (scrubProc τ ph) ps))) ≡ true →
  (hasG1 k (ctlRefsPs ps) ∨ hasG1 k (refsPs ps)) ≡ true
map-has k τ ph [] ng ()
map-has k τ ph (p ∷ ps) ng hf =
  subst (λ z → z ≡ true) (sym closeEq)
    (subst (λ z → z ≡ true) (sym (or-cross a b c d)) moved)
  where
  aS = hasG1 k (ctlRefs (ctl (scrubProc τ ph p)))
  bS = hasG1 k (ctlRefsPs (map (scrubProc τ ph) ps))
  cS = hasG1 k (refsP (scrubProc τ ph p))
  dS = hasG1 k (refsPs (map (scrubProc τ ph) ps))
  a  = hasG1 k (ctlRefs (ctl p))
  b  = hasG1 k (ctlRefsPs ps)
  c  = hasG1 k (refsP p)
  d  = hasG1 k (refsPs ps)
  openEq =
    trans (cong (_∨ hasG1 k (refsP (scrubProc τ ph p) ++ refsPs (map (scrubProc τ ph) ps)))
                (has-++ k (ctlRefs (ctl (scrubProc τ ph p)))
                          (ctlRefsPs (map (scrubProc τ ph) ps))))
          (cong ((aS ∨ bS) ∨_)
                (has-++ k (refsP (scrubProc τ ph p))
                          (refsPs (map (scrubProc τ ph) ps))))
  opened = subst (λ z → z ≡ true) openEq hf
  crossed = subst (λ z → z ≡ true) (or-cross aS bS cS dS) opened
  head = ∨-imp aS cS a c (ctl-has k τ ph (ctl p) ng) (refsP-has k τ ph p)
  tail = map-has k τ ph ps ng
  moved = ∨-imp (aS ∨ cS) (bS ∨ dS) (a ∨ c) (b ∨ d) head tail crossed
  closeEq =
    trans (cong (_∨ hasG1 k (refsP p ++ refsPs ps))
                (has-++ k (ctlRefs (ctl p)) (ctlRefsPs ps)))
          (cong ((a ∨ b) ∨_) (has-++ k (refsP p) (refsPs ps)))

------------------------------------------------------------------------
-- The fresh placeholder is not grade 1, and every old index is below it.
------------------------------------------------------------------------

scrub-miss : ∀ τ ph rs → isG1 (checked ph) ≡ false → Bound (obj ph) rs →
  hasG1 (obj ph) (scrubRefs τ ph rs) ≡ false
scrub-miss τ ph [] ng b = refl
scrub-miss τ ph (r ∷ rs) ng (bcons lt rest) with obj r ≡ᵇ τ
... | true rewrite ≡ᵇ-refl (obj ph) | ng | ∧-falseʳ true =
  scrub-miss τ ph rs ng rest
... | false rewrite obj≠ (obj r) lt ≤-refl =
  scrub-miss τ ph rs ng rest

drop-miss : ∀ k τ rs → Bound k rs → hasG1 k (dropRefs τ rs) ≡ false
drop-miss k τ rs b =
  count0-has k (dropRefs τ rs) (bound-count0 (drop-bound τ rs b) k ≤-refl)

frames-miss : ∀ τ ph fs → isG1 (checked ph) ≡ false →
  Bound (obj ph) (framesRefs fs) →
  hasG1 (obj ph) (framesRefs (scrubFrames τ ph fs)) ≡ false

frame-miss : ∀ τ ph f → isG1 (checked ph) ≡ false →
  Bound (obj ph) (frameRefs f) →
  hasG1 (obj ph) (frameRefs (scrubFrame τ ph f)) ≡ false
frame-miss τ ph (ar _) ng b = refl
frame-miss τ ph su ng b = refl
frame-miss τ ph (mt _ _ _) ng b = refl
frame-miss τ ph (fn r) ng (bcons lt _) with obj r ≡ᵇ τ
... | true rewrite ≡ᵇ-refl (obj ph) | ng | ∧-falseʳ true = refl
... | false rewrite obj≠ (obj r) lt ≤-refl = refl
frame-miss τ ph (bd env) ng b = scrub-miss τ ph env ng b
frame-miss τ ph (saved (go _ env eth _ _)) ng b =
  has-both-false (obj ph) (scrubRefs τ ph env) (flightRefs (dropFlights τ eth))
    (scrub-miss τ ph env ng be)
    (count0-has (obj ph) (flightRefs (dropFlights τ eth))
      (subst (λ xs → count (obj ph) xs ≡ 0)
             (sym (dropFlights-refs τ eth))
             (bound-count0 (drop-bound τ (flightRefs eth) bf) (obj ph) ≤-refl)))
  where
  be = proj₁ (bound-split env (flightRefs eth) b)
  bf = proj₂ (bound-split env (flightRefs eth) b)

frames-miss τ ph [] ng b = refl
frames-miss τ ph (f ∷ fs) ng b =
  has-both-false (obj ph) (frameRefs (scrubFrame τ ph f))
    (framesRefs (scrubFrames τ ph fs))
    (frame-miss τ ph f ng bf) (frames-miss τ ph fs ng bfs)
  where
  bf = proj₁ (bound-split (frameRefs f) (framesRefs fs) b)
  bfs = proj₂ (bound-split (frameRefs f) (framesRefs fs) b)

ctl-miss : ∀ τ ph c → isG1 (checked ph) ≡ false → Bound (obj ph) (ctlRefs c) →
  hasG1 (obj ph) (ctlRefs (scrubCtl τ ph c)) ≡ false
ctl-miss τ ph idle ng b = refl
ctl-miss τ ph (ev _ e fs) ng b =
  has-both-false (obj ph) (scrubRefs τ ph e) (framesRefs (scrubFrames τ ph fs))
    (scrub-miss τ ph e ng be) (frames-miss τ ph fs ng bfs)
  where
  be = proj₁ (bound-split e (framesRefs fs) b)
  bfs = proj₂ (bound-split e (framesRefs fs) b)
ctl-miss τ ph (rv r e fs) ng (bcons lt rest) with obj r ≡ᵇ τ
... | true rewrite ≡ᵇ-refl (obj ph) | ng | ∧-falseʳ true =
  has-both-false (obj ph) (scrubRefs τ ph e) (framesRefs (scrubFrames τ ph fs))
    (scrub-miss τ ph e ng be) (frames-miss τ ph fs ng bfs)
  where
  be = proj₁ (bound-split e (framesRefs fs) rest)
  bfs = proj₂ (bound-split e (framesRefs fs) rest)
... | false rewrite obj≠ (obj r) lt ≤-refl =
  has-both-false (obj ph) (scrubRefs τ ph e) (framesRefs (scrubFrames τ ph fs))
    (scrub-miss τ ph e ng be) (frames-miss τ ph fs ng bfs)
  where
  be = proj₁ (bound-split e (framesRefs fs) rest)
  bfs = proj₂ (bound-split e (framesRefs fs) rest)
ctl-miss τ ph (pr (go _ env eth _ _)) ng b =
  has-both-false (obj ph) (scrubRefs τ ph env) (flightRefs (dropFlights τ eth))
    (scrub-miss τ ph env ng be)
    (count0-has (obj ph) (flightRefs (dropFlights τ eth))
      (subst (λ xs → count (obj ph) xs ≡ 0)
             (sym (dropFlights-refs τ eth))
             (bound-count0 (drop-bound τ (flightRefs eth) bf) (obj ph) ≤-refl)))
  where
  be = proj₁ (bound-split env (flightRefs eth) b)
  bf = proj₂ (bound-split env (flightRefs eth) b)

refsP-miss : ∀ k τ ph p → Bound k (refsP p) →
  hasG1 k (refsP (scrubProc τ ph p)) ≡ false
refsP-miss k τ ph p b =
  count0-has k (refsP (scrubProc τ ph p))
    (subst (λ xs → count k xs ≡ 0) (sym (refsP-drop τ ph p))
      (bound-count0 (drop-bound τ (refsP p) b) k ≤-refl))

map-miss : ∀ τ ph ps → isG1 (checked ph) ≡ false →
  Bound (obj ph) (ctlRefsPs ps) → Bound (obj ph) (refsPs ps) →
  hasG1 (obj ph) (ctlRefsPs (map (scrubProc τ ph) ps)) ≡ false ×
  hasG1 (obj ph) (refsPs (map (scrubProc τ ph) ps)) ≡ false
map-miss τ ph [] ng bc br = refl , refl
map-miss τ ph (p ∷ ps) ng bc br =
  has-both-false (obj ph) (ctlRefs (ctl (scrubProc τ ph p)))
    (ctlRefsPs (map (scrubProc τ ph) ps))
    (ctl-miss τ ph (ctl p) ng bc0) (proj₁ tail)
  , has-both-false (obj ph) (refsP (scrubProc τ ph p))
      (refsPs (map (scrubProc τ ph) ps))
      (refsP-miss (obj ph) τ ph p br0) (proj₂ tail)
  where
  bc0 = proj₁ (bound-split (ctlRefs (ctl p)) (ctlRefsPs ps) bc)
  bcs = proj₂ (bound-split (ctlRefs (ctl p)) (ctlRefsPs ps) bc)
  br0 = proj₁ (bound-split (refsP p) (refsPs ps) br)
  brs = proj₂ (bound-split (refsP p) (refsPs ps) br)
  tail = map-miss τ ph ps ng bcs brs

frames-bd : ∀ {n} τ ph fs → Bound n (framesRefs fs) → obj ph < n →
  Bound n (framesRefs (scrubFrames τ ph fs))

frame-bd : ∀ {n} τ ph f → Bound n (frameRefs f) → obj ph < n →
  Bound n (frameRefs (scrubFrame τ ph f))
frame-bd τ ph (ar _) b olt = b
frame-bd τ ph su b olt = b
frame-bd τ ph (mt _ _ _) b olt = b
frame-bd τ ph (fn r) (bcons lt rest) olt with obj r ≡ᵇ τ
... | true = bcons olt rest
... | false = bcons lt rest
frame-bd τ ph (bd env) b olt = scrub-bound τ ph env b olt
frame-bd τ ph (saved (go _ env eth _ _)) b olt =
  bound-++ (scrub-bound τ ph env be olt)
           (subst (Bound _) (sym (dropFlights-refs τ eth))
             (drop-bound τ (flightRefs eth) bf))
  where
  be = proj₁ (bound-split env (flightRefs eth) b)
  bf = proj₂ (bound-split env (flightRefs eth) b)

frames-bd τ ph [] b olt = b
frames-bd τ ph (f ∷ fs) b olt =
  bound-++ (frame-bd τ ph f bf olt) (frames-bd τ ph fs bfs olt)
  where
  bf = proj₁ (bound-split (frameRefs f) (framesRefs fs) b)
  bfs = proj₂ (bound-split (frameRefs f) (framesRefs fs) b)

ctl-bd : ∀ {n} τ ph c → Bound n (ctlRefs c) → obj ph < n →
  Bound n (ctlRefs (scrubCtl τ ph c))
ctl-bd τ ph idle b olt = b
ctl-bd τ ph (ev _ e fs) b olt =
  bound-++ (scrub-bound τ ph e be olt) (frames-bd τ ph fs bfs olt)
  where
  be = proj₁ (bound-split e (framesRefs fs) b)
  bfs = proj₂ (bound-split e (framesRefs fs) b)
ctl-bd τ ph (rv r e fs) (bcons lt rest) olt with obj r ≡ᵇ τ
... | true =
  bcons olt (bound-++ (scrub-bound τ ph e be olt) (frames-bd τ ph fs bfs olt))
  where
  be = proj₁ (bound-split e (framesRefs fs) rest)
  bfs = proj₂ (bound-split e (framesRefs fs) rest)
... | false =
  bcons lt (bound-++ (scrub-bound τ ph e be olt) (frames-bd τ ph fs bfs olt))
  where
  be = proj₁ (bound-split e (framesRefs fs) rest)
  bfs = proj₂ (bound-split e (framesRefs fs) rest)
ctl-bd τ ph (pr (go _ env eth _ _)) b olt =
  bound-++ (scrub-bound τ ph env be olt)
           (subst (Bound _) (sym (dropFlights-refs τ eth))
             (drop-bound τ (flightRefs eth) bf))
  where
  be = proj₁ (bound-split env (flightRefs eth) b)
  bf = proj₂ (bound-split env (flightRefs eth) b)

refsP-bd : ∀ {n} τ ph p → Bound n (refsP p) → Bound n (refsP (scrubProc τ ph p))
refsP-bd τ ph p b =
  subst (Bound _) (sym (refsP-drop τ ph p)) (drop-bound τ (refsP p) b)

map-bd : ∀ {n} τ ph ps →
  Bound n (ctlRefsPs ps) → Bound n (refsPs ps) → obj ph < n →
  Bound n (ctlRefsPs (map (scrubProc τ ph) ps)) ×
  Bound n (refsPs (map (scrubProc τ ph) ps))
map-bd τ ph [] bc br olt = bc , br
map-bd τ ph (p ∷ ps) bc br olt =
  bound-++ (ctl-bd τ ph (ctl p) bc0 olt) (proj₁ tail)
  , bound-++ (refsP-bd τ ph p br0) (proj₂ tail)
  where
  bc0 = proj₁ (bound-split (ctlRefs (ctl p)) (ctlRefsPs ps) bc)
  bcs = proj₂ (bound-split (ctlRefs (ctl p)) (ctlRefsPs ps) bc)
  br0 = proj₁ (bound-split (refsP p) (refsPs ps) br)
  brs = proj₂ (bound-split (refsP p) (refsPs ps) br)
  tail = map-bd τ ph ps bcs brs olt

refs-sum : ∀ k h ps →
  count k (refsOf (sys h ps)) ≡
  (count k (edgeRefs h) + count k (ctlRefsPs ps)) + count k (refsPs ps)
refs-sum k h ps =
  trans (count-++ k (preOf h ps) (refsPs ps))
        (cong (_+ count k (refsPs ps)) (count-++ k (edgeRefs h) (ctlRefsPs ps)))

refs-or : ∀ k h ps →
  hasG1 k (refsOf (sys h ps)) ≡
  (hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps)) ∨ hasG1 k (refsPs ps)
refs-or k h ps =
  trans (has-++ k (preOf h ps) (refsPs ps))
        (cong (_∨ hasG1 k (refsPs ps)) (has-++ k (edgeRefs h) (ctlRefsPs ps)))

-- A fresh index may gain grade-0 aliases. Every other index only shrinks,
-- and the fresh index itself is not grade 1.
mask-unique : ∀ new old n →
  (∀ i → (n ≡ᵇ i) ≡ false → count i new ≤ count i old) →
  (∀ i → (n ≡ᵇ i) ≡ false → hasG1 i new ≡ true → hasG1 i old ≡ true) →
  hasG1 n new ≡ false →
  Grade1Unique old → Grade1Unique new
mask-unique new old n le hs zn u i hn = pick (n ≡ᵇ i) refl
  where
  pick : (b : Bool) → (n ≡ᵇ i) ≡ b → count i new ≡ 1
  pick true eb =
    ⊥-elim (true≢false
      (trans (sym hn) (subst (λ j → hasG1 j new ≡ false) (≡ᵇ-sound n i eb) zn)))
  pick false eb =
    sym (≤-antisym (has-count i new hn) (≤-subst (le i eb) (u i (hs i eb hn))))

-- setCtlSt keeps roots and the mailbox. Equal control references
-- stay equal as lists.
setCtl-keep : ∀ i ps c st ps' p →
  lookup ps i ≡ just p →
  setCtlSt ps i c st ≡ just ps' →
  ctlRefs c ≡ ctlRefs (ctl p) →
  ctlRefsPs ps' ≡ ctlRefsPs ps × refsPs ps' ≡ refsPs ps
setCtl-keep _ [] _ _ _ _ () _ _
setCtl-keep zero (p ∷ ps) c st .(record p { ctl = c ; state = st } ∷ ps) .p refl refl creq =
  cong (_++ ctlRefsPs ps) creq , refl
setCtl-keep (suc i) (q ∷ ps) c st ps' p lk eq creq =
  tail (setCtlSt ps i c st) eq refl
  where
  tail : (m : Maybe (List Proc)) →
         mapCons q m ≡ just ps' →
         setCtlSt ps i c st ≡ m →
         ctlRefsPs ps' ≡ ctlRefsPs (q ∷ ps) × refsPs ps' ≡ refsPs (q ∷ ps)
  tail nothing () _
  tail (just qs) refl eqs =
    let cq , rq = setCtl-keep i ps c st qs p lk eqs creq
    in cong (ctlRefs (ctl q) ++_) cq , cong (refsP q ++_) rq

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

-- Equal control-reference lists and process-reference lists give the
-- same `refsOf`. State and the term may still differ.
refs-eq : ∀ h ps ps' →
  ctlRefsPs ps' ≡ ctlRefsPs ps → refsPs ps' ≡ refsPs ps →
  refsOf (sys h ps') ≡ refsOf (sys h ps)
refs-eq h ps ps' cq rq =
  trans (cong (λ c → (edgeRefs h ++ c) ++ refsPs ps') cq)
        (cong ((edgeRefs h ++ ctlRefsPs ps) ++_) rq)

-- Scrubbing deletes or replaces. With the fresh cell's edges unchanged,
-- every index other than the placeholder only loses references.
scrub-shrink : ∀ k τ h ps → (obj (placeholder h) ≡ᵇ k) ≡ false →
  (count k (edgeRefs h) + count k (ctlRefsPs (map (scrubProc τ (placeholder h)) ps)))
    + count k (refsPs (map (scrubProc τ (placeholder h)) ps))
  ≤
  (count k (edgeRefs h) + count k (ctlRefsPs ps)) + count k (refsPs ps)
scrub-shrink k τ h ps hp =
  subst (λ m → m ≤ (E + C) + R) (sym (+-assoc E C' R'))
    (subst (λ m → E + (C' + R') ≤ m) (sym (+-assoc E C R))
      (≤-+ˡ E (map-le k τ (placeholder h) ps hp)))
  where
  E  = count k (edgeRefs h)
  C' = count k (ctlRefsPs (map (scrubProc τ (placeholder h)) ps))
  R' = count k (refsPs (map (scrubProc τ (placeholder h)) ps))
  C  = count k (ctlRefsPs ps)
  R  = count k (refsPs ps)

scrub-has-step : ∀ k τ h ps →
  ((hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs (map (scrubProc τ (placeholder h)) ps))) ∨
   hasG1 k (refsPs (map (scrubProc τ (placeholder h)) ps))) ≡ true →
  ((hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps)) ∨ hasG1 k (refsPs ps)) ≡ true
scrub-has-step k τ h ps hf = body (hasG1 k (edgeRefs h)) refl
  where
  ph = placeholder h
  np : isG1 (checked ph) ≡ false
  np = refl
  body : (b : Bool) → hasG1 k (edgeRefs h) ≡ b →
         ((b ∨ hasG1 k (ctlRefsPs ps)) ∨ hasG1 k (refsPs ps)) ≡ true
  body true eb rewrite eb = refl
  body false eb rewrite eb = map-has k τ ph ps np hf

------------------------------------------------------------------------
-- consume snocs one grade-0 cell and scrubs the tag everywhere except
-- heap edges. `finish` keeps the scrubbed control references.
------------------------------------------------------------------------

consume-wf : ∀ h ps i τ finish t →
  WF (sys h ps) →
  consume (sys h ps) i τ finish ≡ just t →
  (∀ c c' → finish τ c ≡ just c' → ctlRefs c' ≡ ctlRefs c) →
  WF t
consume-wf h ps i τ finish t wf eq fre = at (lookup ps1 i) eq refl
  where
  n = length h
  bAll = proj₁ wf
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bCtl = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
  ph = placeholder h
  np : isG1 (checked ph) ≡ false
  np = refl
  h' = snoc h (nat zero)
  ps1 = map (scrubProc τ ph) ps
  at : (m : Maybe Proc) →
       (m >>= λ p1 →
          finish τ (ctl p1) >>= λ c' →
          setCtlSt ps1 i c' ready >>= λ ps2 →
          just (sys h' ps2)) ≡ just t →
       lookup ps1 i ≡ m → WF t
  at nothing eql lk rewrite lk = ⊥-elim (nothing≢just eql)
  at (just p1) eql lk = fin (finish τ (ctl p1)) eql refl
    where
    fin : (m : Maybe Ctl) →
          (m >>= λ c' → setCtlSt ps1 i c' ready >>= λ ps2 → just (sys h' ps2)) ≡ just t →
          finish τ (ctl p1) ≡ m → WF t
    fin nothing eqf ef rewrite ef = ⊥-elim (nothing≢just eqf)
    fin (just c') eqf ef = st (setCtlSt ps1 i c' ready) (fre (ctl p1) c' ef) eqf refl
      where
      st : (m : Maybe (List Proc)) → ctlRefs c' ≡ ctlRefs (ctl p1) →
           (m >>= λ ps2 → just (sys h' ps2)) ≡ just t →
           setCtlSt ps1 i c' ready ≡ m → WF t
      st nothing creq eqs es rewrite es = ⊥-elim (nothing≢just eqs)
      st (just ps2) creq refl es =
        let cq , rq = setCtl-keep i ps1 c' ready ps2 p1 lk es creq
            cMiss , rMiss = map-miss τ ph ps np bCtl bRs
            bMapC , bMapR = map-bd τ ph ps (monoS bCtl) (monoS bRs) (fresh-< n)
            eF = count0-has n (edgeRefs h) (bound-count0 bEdge n ≤-refl)
            eF' = trans (cong (hasG1 n) (edge-nat h zero)) eF
            cF = trans (cong (hasG1 n) cq) cMiss
            rF = trans (cong (hasG1 n) rq) rMiss
            zn = trans (refs-or n h' ps2)
                   (∨-both-false (∨-both-false eF' cF) rF)
            bEdge' = subst (Bound (suc n)) (sym (edge-nat h zero)) (monoS bEdge)
            bCtl2 = subst (Bound (suc n)) (sym cq) bMapC
            bRs2 = subst (Bound (suc n)) (sym rq) bMapR
            bSuc = bound-++ (bound-++ bEdge' bCtl2) bRs2
            bLen = subst (λ m → Bound m (refsOf (sys h' ps2)))
                     (sym (length-snoc h (cell (nat zero) live))) bSuc
        in bLen , mask-unique (refsOf (sys h' ps2)) (refsOf (sys h ps)) n
             (λ i eb → leStep i eb cq rq) (λ i eb hf → hasStep i eb cq rq hf) zn (proj₂ wf)
        where
        leStep : ∀ i → (n ≡ᵇ i) ≡ false →
                 ctlRefsPs ps2 ≡ ctlRefsPs ps1 → refsPs ps2 ≡ refsPs ps1 →
                 count i (refsOf (sys h' ps2)) ≤ count i (refsOf (sys h ps))
        leStep i eb cq0 rq0 =
          ≤-subst (subst (λ m → m ≤ mid) (sym newEq) (scrub-shrink i τ h ps eb))
                  (sym (refs-sum i h ps))
          where
          mid = (count i (edgeRefs h) + count i (ctlRefsPs ps)) + count i (refsPs ps)
          newEq =
            trans (refs-sum i h' ps2)
            (trans (cong (λ e → (e + count i (ctlRefsPs ps2)) + count i (refsPs ps2))
                         (cong (count i) (edge-nat h zero)))
            (trans (cong (λ c → (count i (edgeRefs h) + c) + count i (refsPs ps2))
                         (cong (count i) cq0))
                   (cong (λ r → (count i (edgeRefs h) + count i (ctlRefsPs ps1)) + r)
                         (cong (count i) rq0))))
        hasStep : ∀ i → (n ≡ᵇ i) ≡ false →
                  ctlRefsPs ps2 ≡ ctlRefsPs ps1 → refsPs ps2 ≡ refsPs ps1 →
                  hasG1 i (refsOf (sys h' ps2)) ≡ true →
                  hasG1 i (refsOf (sys h ps)) ≡ true
        hasStep i eb cq0 rq0 hf =
          subst (λ z → z ≡ true) (sym (refs-or i h ps))
            (scrub-has-step i τ h ps
              (subst (λ z → z ≡ true) orEq
                (subst (λ z → z ≡ true) (refs-or i h' ps2) hf)))
          where
          orEq =
            trans (cong (λ e → (e ∨ hasG1 i (ctlRefsPs ps2)) ∨ hasG1 i (refsPs ps2))
                        (cong (hasG1 i) (edge-nat h zero)))
            (trans (cong (λ c → (hasG1 i (edgeRefs h) ∨ c) ∨ hasG1 i (refsPs ps2))
                         (cong (hasG1 i) cq0))
                   (cong (λ r → (hasG1 i (edgeRefs h) ∨ hasG1 i (ctlRefsPs ps1)) ∨ r)
                         (cong (hasG1 i) rq0)))

flush-refs : ∀ τ c c' → finishFlush τ c ≡ just c' → ctlRefs c' ≡ ctlRefs c
flush-refs τ idle _ ()
flush-refs τ (ev _ _ _) _ ()
flush-refs τ (rv _ _ _) _ ()
flush-refs τ (pr (go done _ _ _ _)) _ ()
flush-refs τ (pr (go (send _ _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (recv _ _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (spawn _ _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (seq _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (await _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (ignore _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (nignore _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (awaitT _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (ignoreT _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (ncheckT _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (ndemonT _ _) _ _ _ _)) _ ()
flush-refs τ (pr (go (flushT τ' k) env eth d dm)) c' eq with τ ≡ᵇ τ'
... | true = sym (cong ctlRefs (just-inj eq))
... | false = ⊥-elim (nothing≢just eq)

await-refs : ∀ τ c c' → finishAwait τ c ≡ just c' → ctlRefs c' ≡ ctlRefs c
await-refs τ idle _ ()
await-refs τ (ev _ _ _) _ ()
await-refs τ (rv _ _ _) _ ()
await-refs τ (pr (go done _ _ _ _)) _ ()
await-refs τ (pr (go (send _ _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (recv _ _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (spawn _ _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (seq _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (await _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (ignore _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (nignore _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (flushT _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (ignoreT _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (ncheckT _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (ndemonT _ _) _ _ _ _)) _ ()
await-refs τ (pr (go (awaitT τ' k) env eth d dm)) c' eq with τ ≡ᵇ τ'
... | true = sym (cong ctlRefs (just-inj eq))
... | false = ⊥-elim (nothing≢just eq)

peek-refs : ∀ τ c c' → finishPeek τ c ≡ just c' → ctlRefs c' ≡ ctlRefs c
peek-refs τ idle _ ()
peek-refs τ (ev _ _ _) _ ()
peek-refs τ (rv _ _ _) _ ()
peek-refs τ (pr (go done _ _ _ _)) _ ()
peek-refs τ (pr (go (send _ _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (recv _ _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (spawn _ _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (seq _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (await _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (ignore _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (nignore _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (awaitT _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (ignoreT _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (flushT _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (ndemonT _ _) _ _ _ _)) _ ()
peek-refs τ (pr (go (ncheckT τ' k) env eth d dm)) c' eq with τ ≡ᵇ τ'
... | true = sym (cong ctlRefs (just-inj eq))
... | false = ⊥-elim (nothing≢just eq)

flush-wf : ∀ h ps i t → WF (sys h ps) → flush1 (sys h ps) i ≡ just t → WF t
flush-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → flush1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = ⊥-elim (nothing≢just eqa)
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → flush1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (flushT τ k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
      consume-wf h ps i τ finishFlush t wf eqc (flush-refs τ)

------------------------------------------------------------------------
-- Moving one reference between control and a mailbox preserves the
-- multiset. Spawn and emit use the same regrouping.
------------------------------------------------------------------------

shuffle : ∀ a b c d e → ((a + b) + c) + (d + e) ≡ (b + c) + (d + (a + e))
shuffle a b c d e =
  trans (cong (_+ (d + e)) (+-assoc a b c))
  (trans (+-assoc a (b + c) (d + e))
  (trans (+-swap a (b + c) (d + e))
         (cong ((b + c) +_) (+-swap a d e))))

huffle : ∀ a b c d e → ((a ∨ b) ∨ c) ∨ (d ∨ e) ≡ (b ∨ c) ∨ (d ∨ (a ∨ e))
huffle a b c d e =
  trans (cong (_∨ (d ∨ e)) (∨-assoc a b c))
  (trans (∨-assoc a (b ∨ c) (d ∨ e))
  (trans (∨-swap a (b ∨ c) (d ∨ e))
         (cong ((b ∨ c) ∨_) (∨-swap a d e))))

recv-sum : ∀ k r env eth roots ms →
  count k ((r ∷ env) ++ flightRefs eth) + count k (roots ++ mapRef ms) ≡
  count k (env ++ flightRefs eth) + count k (roots ++ (r ∷ mapRef ms))
recv-sum k r env eth roots ms =
  let fl = flightRefs eth
      mr = mapRef ms
  in trans (cong₂ _+_ (count-++ k (r ∷ env) fl) (count-++ k roots mr))
     (trans (shuffle (ext (obj r ≡ᵇ k)) (count k env) (count k fl)
                     (count k roots) (count k mr))
            (sym (cong₂ _+_ (count-++ k env fl) (count-++ k roots (r ∷ mr)))))

recv-has : ∀ k r env eth roots ms →
  hasG1 k ((r ∷ env) ++ flightRefs eth) ∨ hasG1 k (roots ++ mapRef ms) ≡
  hasG1 k (env ++ flightRefs eth) ∨ hasG1 k (roots ++ (r ∷ mapRef ms))
recv-has k r env eth roots ms =
  let fl = flightRefs eth
      mr = mapRef ms
  in trans (cong₂ _∨_ (has-++ k (r ∷ env) fl) (has-++ k roots mr))
     (trans (huffle (gbit r k) (hasG1 k env) (hasG1 k fl)
                    (hasG1 k roots) (hasG1 k mr))
            (sym (cong₂ _∨_ (has-++ k env fl) (has-++ k roots (r ∷ mr)))))

sum4 : ∀ e a b c d → a + b ≡ c + d → (e + a) + b ≡ (e + c) + d
sum4 e a b c d eq =
  trans (+-assoc e a b)
  (trans (cong (e +_) eq)
         (sym (+-assoc e c d)))

or4 : ∀ e a b c d → (a ∨ b) ≡ (c ∨ d) → ((e ∨ a) ∨ b) ≡ ((e ∨ c) ∨ d)
or4 e a b c d eq =
  trans (∨-assoc e a b)
  (trans (cong (e ∨_) eq)
         (sym (∨-assoc e c d)))

upd-both-count : ∀ i k ps p p' ps' →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  count k (ctlRefs (ctl p')) + count k (refsP p') ≡
  count k (ctlRefs (ctl p)) + count k (refsP p) →
  count k (ctlRefsPs ps') + count k (refsPs ps') ≡
  count k (ctlRefsPs ps) + count k (refsPs ps)
upd-both-count i k ps p p' ps' lk eq pres = walk i ps p ps' lk eq pres
  where
  walk : ∀ i ps p ps' →
         lookup ps i ≡ just p → update i p' ps ≡ just ps' →
         count k (ctlRefs (ctl p')) + count k (refsP p') ≡
         count k (ctlRefs (ctl p)) + count k (refsP p) →
         count k (ctlRefsPs ps') + count k (refsPs ps') ≡
         count k (ctlRefsPs ps) + count k (refsPs ps)
  walk _ [] _ _ () _ _
  walk zero (q ∷ qs) .q .(p' ∷ qs) refl refl pres0 =
    trans newEq (trans (cong (_+ (b + d)) pres0) (sym oldEq))
    where
    a = count k (ctlRefs (ctl p'))
    b = count k (ctlRefsPs qs)
    c = count k (refsP p')
    d = count k (refsPs qs)
    a0 = count k (ctlRefs (ctl q))
    c0 = count k (refsP q)
    newEq =
      trans (cong₂ _+_ (count-++ k (ctlRefs (ctl p')) (ctlRefsPs qs))
                       (count-++ k (refsP p') (refsPs qs)))
            (add2 a b c d)
    oldEq =
      trans (cong₂ _+_ (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                       (count-++ k (refsP q) (refsPs qs)))
            (add2 a0 b c0 d)
  walk (suc j) (q ∷ qs) p0 ps0 lk0 eq0 pres0 = step (update j p' qs) eq0 refl
    where
    step : (m : Maybe (List Proc)) → mapCons q m ≡ just ps0 →
           update j p' qs ≡ m →
           count k (ctlRefsPs ps0) + count k (refsPs ps0) ≡
           count k (ctlRefsPs (q ∷ qs)) + count k (refsPs (q ∷ qs))
    step nothing () _
    step (just qs') refl equ =
      trans newEq (trans (cong ((a + c) +_) ih) (sym oldEq))
      where
      a = count k (ctlRefs (ctl q))
      c = count k (refsP q)
      b' = count k (ctlRefsPs qs')
      d' = count k (refsPs qs')
      b = count k (ctlRefsPs qs)
      d = count k (refsPs qs)
      ih = walk j qs p0 qs' lk0 equ pres0
      newEq =
        trans (cong₂ _+_ (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs'))
                         (count-++ k (refsP q) (refsPs qs')))
              (add2 a b' c d')
      oldEq =
        trans (cong₂ _+_ (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                         (count-++ k (refsP q) (refsPs qs)))
              (add2 a b c d)

upd-both-has : ∀ i k ps p p' ps' →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  hasG1 k (ctlRefs (ctl p')) ∨ hasG1 k (refsP p') ≡
  hasG1 k (ctlRefs (ctl p)) ∨ hasG1 k (refsP p) →
  hasG1 k (ctlRefsPs ps') ∨ hasG1 k (refsPs ps') ≡
  hasG1 k (ctlRefsPs ps) ∨ hasG1 k (refsPs ps)
upd-both-has i k ps p p' ps' lk eq pres = walk i ps p ps' lk eq pres
  where
  walk : ∀ i ps p ps' →
         lookup ps i ≡ just p → update i p' ps ≡ just ps' →
         hasG1 k (ctlRefs (ctl p')) ∨ hasG1 k (refsP p') ≡
         hasG1 k (ctlRefs (ctl p)) ∨ hasG1 k (refsP p) →
         hasG1 k (ctlRefsPs ps') ∨ hasG1 k (refsPs ps') ≡
         hasG1 k (ctlRefsPs ps) ∨ hasG1 k (refsPs ps)
  walk _ [] _ _ () _ _
  walk zero (q ∷ qs) .q .(p' ∷ qs) refl refl pres0 =
    trans newEq (trans (cong (_∨ (b ∨ d)) pres0) (sym oldEq))
    where
    a = hasG1 k (ctlRefs (ctl p'))
    b = hasG1 k (ctlRefsPs qs)
    c = hasG1 k (refsP p')
    d = hasG1 k (refsPs qs)
    a0 = hasG1 k (ctlRefs (ctl q))
    c0 = hasG1 k (refsP q)
    newEq =
      trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl p')) (ctlRefsPs qs))
                       (has-++ k (refsP p') (refsPs qs)))
            (or-cross a b c d)
    oldEq =
      trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                       (has-++ k (refsP q) (refsPs qs)))
            (or-cross a0 b c0 d)
  walk (suc j) (q ∷ qs) p0 ps0 lk0 eq0 pres0 = step (update j p' qs) eq0 refl
    where
    step : (m : Maybe (List Proc)) → mapCons q m ≡ just ps0 →
           update j p' qs ≡ m →
           hasG1 k (ctlRefsPs ps0) ∨ hasG1 k (refsPs ps0) ≡
           hasG1 k (ctlRefsPs (q ∷ qs)) ∨ hasG1 k (refsPs (q ∷ qs))
    step nothing () _
    step (just qs') refl equ =
      trans newEq (trans (cong ((a ∨ c) ∨_) ih) (sym oldEq))
      where
      a = hasG1 k (ctlRefs (ctl q))
      c = hasG1 k (refsP q)
      b' = hasG1 k (ctlRefsPs qs')
      d' = hasG1 k (refsPs qs')
      b = hasG1 k (ctlRefsPs qs)
      d = hasG1 k (refsPs qs)
      ih = walk j qs p0 qs' lk0 equ pres0
      newEq =
        trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl q)) (ctlRefsPs qs'))
                         (has-++ k (refsP q) (refsPs qs')))
              (or-cross a b' c d')
      oldEq =
        trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                         (has-++ k (refsP q) (refsPs qs)))
              (or-cross a b c d)

upd-ctl-bound : ∀ {n} i ps p p' ps' →
  Bound n (ctlRefsPs ps) →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  Bound n (ctlRefs (ctl p')) →
  Bound n (ctlRefsPs ps')
upd-ctl-bound {n} i ps p p' ps' bAll lk eq bc' = walk i ps p ps' bAll lk eq
  where
  walk : ∀ i ps p ps' →
         Bound n (ctlRefsPs ps) →
         lookup ps i ≡ just p →
         update i p' ps ≡ just ps' →
         Bound n (ctlRefsPs ps')
  walk _ [] _ _ _ () _
  walk zero (q ∷ qs) .q .(p' ∷ qs) bd0 refl refl =
    bound-++ bc' (proj₂ (bound-split (ctlRefs (ctl q)) (ctlRefsPs qs) bd0))
  walk (suc j) (q ∷ qs) p0 ps0 bd0 lk0 eq0 =
    step (update j p' qs) eq0 refl (proj₂ (bound-split (ctlRefs (ctl q)) (ctlRefsPs qs) bd0))
    where
    step : (m : Maybe (List Proc)) → mapCons q m ≡ just ps0 →
           update j p' qs ≡ m →
           Bound n (ctlRefsPs qs) →
           Bound n (ctlRefsPs ps0)
    step nothing () _ _
    step (just qs') refl equ bqs =
      bound-++ (proj₁ (bound-split (ctlRefs (ctl q)) (ctlRefsPs qs) bd0))
               (walk j qs p0 qs' bqs lk0 equ)

cons-bound : ∀ {n r rs} → Bound n (r ∷ rs) → obj r < n × Bound n rs
cons-bound (bcons lt rest) = lt , rest

keep-refs : ∀ h ps ps' →
  WF (sys h ps) →
  (∀ k → count k (refsOf (sys h ps')) ≡ count k (refsOf (sys h ps))) →
  (∀ k → hasG1 k (refsOf (sys h ps')) ≡ hasG1 k (refsOf (sys h ps))) →
  Bound (length h) (refsOf (sys h ps')) →
  WF (sys h ps')
keep-refs h ps ps' (_ , uq) cq hq bNew =
  bNew , same-unique {rs = refsOf (sys h ps)} {rs' = refsOf (sys h ps')} cq hq uq

await-wf : ∀ h ps i t → WF (sys h ps) → await1 (sys h ps) i ≡ just t → WF t
await-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → await1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = ⊥-elim (nothing≢just eqa)
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → await1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (awaitT τ k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
      onB (inboxHas (inbox p) τ) refl eqc
      where
      code = pr (go (awaitT τ k) env eth d dm)
      onB : (b : Bool) → inboxHas (inbox p) τ ≡ b →
            awaitOn h ps i p code b ≡ just t → WF t
      onB true _ eqb = consume-wf h ps i τ finishAwait t wf eqb (await-refs τ)
      onB false _ eqb = onSt (state p) refl eqb
        where
        onSt : (st : PState) → state p ≡ st →
               awaitPark h ps i τ k env eth d dm st ≡ just t → WF t
        onSt waiting _ eqst = ⊥-elim (nothing≢just eqst)
        onSt pstDone _ eqst = ⊥-elim (nothing≢just eqst)
        onSt ready est eqst rewrite est = landed (setCtlSt ps i code waiting) eqst refl
          where
          landed : (m : Maybe (List Proc)) →
                   (m >>= λ ps' → just (sys h ps')) ≡ just t →
                   setCtlSt ps i code waiting ≡ m → WF t
          landed nothing eql el rewrite el = ⊥-elim (nothing≢just eql)
          landed (just ps') refl es =
            let cq , rq = setCtl-keep i ps code waiting ps' p lk0 es
                  (subst (λ c0 → ctlRefs code ≡ ctlRefs c0) (sym ec) refl)
            in subst (λ rs → Bound (length h) rs × Grade1Unique rs)
                 (sym (refs-eq h ps ps' cq rq)) wf

npeek-wf : ∀ h ps i t → WF (sys h ps) → npeek1 (sys h ps) i ≡ just t → WF t
npeek-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → npeek1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = ⊥-elim (nothing≢just eqa)
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → npeek1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ncheckT τ k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
      onB (inboxHas (inbox p) τ) refl eqc
      where
      onB : (b : Bool) → inboxHas (inbox p) τ ≡ b →
            npeekOn h ps i (pr (go (ncheckT τ k) env eth d dm)) b ≡ just t → WF t
      onB true _ eqb = consume-wf h ps i τ finishPeek t wf eqb (peek-refs τ)
      onB false _ eqb =
        keep-set h ps i p (pr (go (ndemonT τ k) env eth d dm)) t wf lk0 eqb
          (subst (λ c0 → ctlRefs (pr (go (ndemonT τ k) env eth d dm)) ≡ ctlRefs c0)
                 (sym ec) refl)

recv-wf : ∀ h ps i t → WF (sys h ps) → recv1 (sys h ps) i ≡ just t → WF t
recv-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  bAll = proj₁ wf
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
  bCtl = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
  from : (m : Maybe Proc) → recv1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = ⊥-elim (nothing≢just eqa)
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → recv1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (recv _ _ k) env eth d dm)) eqc lk0 ec rewrite lk0 =
      opened ec eqc
      where
      code = pr (go (recv _ _ k) env eth d dm)
      step : (st : PState) (ib : List Msg) → state p ≡ st → inbox p ≡ ib →
             recvStep h ps i p code st ib ≡ just t → WF t
      step waiting [] _ _ eqst = ⊥-elim (nothing≢just eqst)
      step pstDone [] _ _ eqst = ⊥-elim (nothing≢just eqst)
      step ready [] est ei eqst =
        moved (update i p' ps) eqst refl
        where
        p' = record p { state = waiting }
        moved : (m : Maybe (List Proc)) →
                (m >>= λ ps' → just (sys h ps')) ≡ just t →
                update i p' ps ≡ m → WF t
        moved nothing eql el rewrite el = ⊥-elim (nothing≢just eql)
        moved (just ps') refl eu =
          sealMove h ps ps'
            (ctlEq-update i ps p' ps' eu (λ q eqq → cong ctl (just-inj (trans (sym lk0) eqq))))
            (λ kq → upd-count kq i ps p p' ps' lk0 eu refl)
            (λ kq → upd-has kq i ps p p' ps' lk0 eu refl)
            (upd-bound i ps p p' ps' bRs lk0 eu (refsHere h ps i p wf lk0))
            bAll (proj₂ wf)
      step st (msg r ∷ ms) est ei eqst =
        moved (update i p' ps) eqst refl
        where
        p' = record p { state = ready ; inbox = ms
                      ; ctl = pr (go k (r ∷ env) eth d dm) }
        moved : (m : Maybe (List Proc)) →
                (m >>= λ ps' → just (sys h ps')) ≡ just t →
                update i p' ps ≡ m → WF t
        moved nothing eql el rewrite el = ⊥-elim (nothing≢just eql)
        moved (just ps') refl eu =
          keep-refs h ps ps' wf (λ kq → countAll kq) (λ kq → hasAll kq) bNew
          where
          bHere =
            subst (λ c0 → Bound (length h) (ctlRefs c0)) ec
              (ctl-bound-at i ps p lk0 bCtl)
          bEnv = proj₁ (bound-split env (flightRefs eth) bHere)
          bFl = proj₂ (bound-split env (flightRefs eth) bHere)
          bRP =
            subst (λ ib → Bound (length h) (roots p ++ mapRef ib)) ei
              (refsHere h ps i p wf lk0)
          bRoots = proj₁ (bound-split (roots p) (r ∷ mapRef ms) bRP)
          lt = proj₁ (cons-bound (proj₂ (bound-split (roots p) (r ∷ mapRef ms) bRP)))
          bMs = proj₂ (cons-bound (proj₂ (bound-split (roots p) (r ∷ mapRef ms) bRP)))
          bCtl' = bcons lt (bound-++ bEnv bFl)
          bRef' = bound-++ bRoots bMs
          bCtlPs' = upd-ctl-bound i ps p p' ps' bCtl lk0 eu bCtl'
          bRs' = upd-bound i ps p p' ps' bRs lk0 eu bRef'
          bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
          bNew = bound-++ (bound-++ bEdge bCtlPs') bRs'
          oneC : ∀ kq →
            count kq (ctlRefs (ctl p')) + count kq (refsP p') ≡
            count kq (ctlRefs (ctl p)) + count kq (refsP p)
          oneC kq =
            trans (recv-sum kq r env eth (roots p) ms)
            (trans (cong (λ xs → count kq xs + count kq (roots p ++ (r ∷ mapRef ms)))
                         (cong ctlRefs (sym ec)))
                   (cong (count kq (ctlRefs (ctl p)) +_)
                         (cong (count kq) (cong (_++_ (roots p)) (cong mapRef (sym ei))))))
          oneH : ∀ kq →
            hasG1 kq (ctlRefs (ctl p')) ∨ hasG1 kq (refsP p') ≡
            hasG1 kq (ctlRefs (ctl p)) ∨ hasG1 kq (refsP p)
          oneH kq =
            trans (recv-has kq r env eth (roots p) ms)
            (trans (cong (λ xs → hasG1 kq xs ∨ hasG1 kq (roots p ++ (r ∷ mapRef ms)))
                         (cong ctlRefs (sym ec)))
                   (cong (hasG1 kq (ctlRefs (ctl p)) ∨_)
                         (cong (hasG1 kq) (cong (_++_ (roots p)) (cong mapRef (sym ei))))))
          countAll : ∀ kq → count kq (refsOf (sys h ps')) ≡ count kq (refsOf (sys h ps))
          countAll kq =
            trans (refs-sum kq h ps')
            (trans (sum4 (count kq (edgeRefs h))
                      (count kq (ctlRefsPs ps')) (count kq (refsPs ps'))
                      (count kq (ctlRefsPs ps)) (count kq (refsPs ps))
                      (upd-both-count i kq ps p p' ps' lk0 eu (oneC kq)))
                   (sym (refs-sum kq h ps)))
          hasAll : ∀ kq → hasG1 kq (refsOf (sys h ps')) ≡ hasG1 kq (refsOf (sys h ps))
          hasAll kq =
            trans (refs-or kq h ps')
            (trans (or4 (hasG1 kq (edgeRefs h))
                      (hasG1 kq (ctlRefsPs ps')) (hasG1 kq (refsPs ps'))
                      (hasG1 kq (ctlRefsPs ps)) (hasG1 kq (refsPs ps))
                      (upd-both-has i kq ps p p' ps' lk0 eu (oneH kq)))
                   (sym (refs-or kq h ps)))
      opened : ctl p ≡ code → recvStep h ps i p (ctl p) (state p) (inbox p) ≡ just t → WF t
      opened ec0 eq0 rewrite ec0 = step (state p) (inbox p) refl refl eq0

------------------------------------------------------------------------
-- A smaller multiset of the same references stays well formed.
------------------------------------------------------------------------

≤-left : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
≤-left refl le = le

≤-cast : ∀ {a b c d} → a ≡ b → b ≤ c → c ≡ d → a ≤ d
≤-cast refl le refl = le

sum-le : ∀ e a b c d → a + b ≤ c + d → (e + a) + b ≤ (e + c) + d
sum-le e a b c d le =
  ≤-cast (+-assoc e a b) (≤-+ˡ e le) (sym (+-assoc e c d))

-- The changed process is on the right of the disjunction.
or-keepˡ : ∀ x y z → (y ≡ true → z ≡ true) → (x ∨ y) ≡ true → (x ∨ z) ≡ true
or-keepˡ x true z f _ = trans (cong (x ∨_) (f refl)) (∨-trueʳ x)
or-keepˡ true false z _ _ = refl
or-keepˡ false false z _ ()

-- The changed process is on the left of the disjunction.
or-keepʳ : ∀ y z x → (y ≡ true → z ≡ true) → (y ∨ x) ≡ true → (z ∨ x) ≡ true
or-keepʳ true z x f _ = sym (cong (_∨ x) (sym (f refl)))
or-keepʳ false z x _ hf = trans (cong (z ∨_) hf) (∨-trueʳ z)

upd-both-le : ∀ i k ps p p' ps' →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  count k (ctlRefs (ctl p')) + count k (refsP p') ≤
  count k (ctlRefs (ctl p)) + count k (refsP p) →
  count k (ctlRefsPs ps') + count k (refsPs ps') ≤
  count k (ctlRefsPs ps) + count k (refsPs ps)
upd-both-le i k ps p p' ps' lk eq le1 = walk i ps p ps' lk eq le1
  where
  walk : ∀ i ps p ps' →
         lookup ps i ≡ just p → update i p' ps ≡ just ps' →
         count k (ctlRefs (ctl p')) + count k (refsP p') ≤
         count k (ctlRefs (ctl p)) + count k (refsP p) →
         count k (ctlRefsPs ps') + count k (refsPs ps') ≤
         count k (ctlRefsPs ps) + count k (refsPs ps)
  walk _ [] _ _ () _ _
  walk zero (q ∷ qs) .q .(p' ∷ qs) refl refl le0 =
    ≤-cast newEq (≤-+ʳ (b + d) le0) (sym oldEq)
    where
    a = count k (ctlRefs (ctl p'))
    b = count k (ctlRefsPs qs)
    c = count k (refsP p')
    d = count k (refsPs qs)
    a0 = count k (ctlRefs (ctl q))
    c0 = count k (refsP q)
    newEq =
      trans (cong₂ _+_ (count-++ k (ctlRefs (ctl p')) (ctlRefsPs qs))
                       (count-++ k (refsP p') (refsPs qs)))
            (add2 a b c d)
    oldEq =
      trans (cong₂ _+_ (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                       (count-++ k (refsP q) (refsPs qs)))
            (add2 a0 b c0 d)
  walk (suc j) (q ∷ qs) p0 ps0 lk0 eq0 le0 = step (update j p' qs) eq0 refl
    where
    step : (m : Maybe (List Proc)) → mapCons q m ≡ just ps0 →
           update j p' qs ≡ m →
           count k (ctlRefsPs ps0) + count k (refsPs ps0) ≤
           count k (ctlRefsPs (q ∷ qs)) + count k (refsPs (q ∷ qs))
    step nothing () _
    step (just qs') refl equ =
      ≤-cast newEq (≤-+ˡ (a + c) ih) (sym oldEq)
      where
      a = count k (ctlRefs (ctl q))
      c = count k (refsP q)
      b' = count k (ctlRefsPs qs')
      d' = count k (refsPs qs')
      b = count k (ctlRefsPs qs)
      d = count k (refsPs qs)
      ih = walk j qs p0 qs' lk0 equ le0
      newEq =
        trans (cong₂ _+_ (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs'))
                         (count-++ k (refsP q) (refsPs qs')))
              (add2 a b' c d')
      oldEq =
        trans (cong₂ _+_ (count-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                         (count-++ k (refsP q) (refsPs qs)))
              (add2 a b c d)

upd-both-imp : ∀ i k ps p p' ps' →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  (hasG1 k (ctlRefs (ctl p')) ∨ hasG1 k (refsP p') ≡ true →
   hasG1 k (ctlRefs (ctl p)) ∨ hasG1 k (refsP p) ≡ true) →
  hasG1 k (ctlRefsPs ps') ∨ hasG1 k (refsPs ps') ≡ true →
  hasG1 k (ctlRefsPs ps) ∨ hasG1 k (refsPs ps) ≡ true
upd-both-imp i k ps p p' ps' lk eq imp hf = walk i ps p ps' lk eq imp hf
  where
  walk : ∀ i ps p ps' →
         lookup ps i ≡ just p → update i p' ps ≡ just ps' →
         (hasG1 k (ctlRefs (ctl p')) ∨ hasG1 k (refsP p') ≡ true →
          hasG1 k (ctlRefs (ctl p)) ∨ hasG1 k (refsP p) ≡ true) →
         hasG1 k (ctlRefsPs ps') ∨ hasG1 k (refsPs ps') ≡ true →
         hasG1 k (ctlRefsPs ps) ∨ hasG1 k (refsPs ps) ≡ true
  walk _ [] _ _ () _ _ _
  walk zero (q ∷ qs) .q .(p' ∷ qs) refl refl imp0 hf0 =
    subst (λ z → z ≡ true) (sym oldEq) moved
    where
    a = hasG1 k (ctlRefs (ctl p'))
    b = hasG1 k (ctlRefsPs qs)
    c = hasG1 k (refsP p')
    d = hasG1 k (refsPs qs)
    a0 = hasG1 k (ctlRefs (ctl q))
    c0 = hasG1 k (refsP q)
    newEq =
      trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl p')) (ctlRefsPs qs))
                       (has-++ k (refsP p') (refsPs qs)))
            (or-cross a b c d)
    oldEq =
      trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                       (has-++ k (refsP q) (refsPs qs)))
            (or-cross a0 b c0 d)
    moved = or-keepʳ (a ∨ c) (a0 ∨ c0) (b ∨ d) imp0
              (subst (λ z → z ≡ true) newEq hf0)
  walk (suc j) (q ∷ qs) p0 ps0 lk0 eq0 imp0 hf0 = step (update j p' qs) eq0 refl hf0
    where
    step : (m : Maybe (List Proc)) → mapCons q m ≡ just ps0 →
           update j p' qs ≡ m →
           hasG1 k (ctlRefsPs ps0) ∨ hasG1 k (refsPs ps0) ≡ true →
           hasG1 k (ctlRefsPs (q ∷ qs)) ∨ hasG1 k (refsPs (q ∷ qs)) ≡ true
    step nothing () _ _
    step (just qs') refl equ hf1 =
      subst (λ z → z ≡ true) (sym oldEq) moved
      where
      a = hasG1 k (ctlRefs (ctl q))
      c = hasG1 k (refsP q)
      b' = hasG1 k (ctlRefsPs qs')
      d' = hasG1 k (refsPs qs')
      b = hasG1 k (ctlRefsPs qs)
      d = hasG1 k (refsPs qs)
      ih = walk j qs p0 qs' lk0 equ imp0
      newEq =
        trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl q)) (ctlRefsPs qs'))
                         (has-++ k (refsP q) (refsPs qs')))
              (or-cross a b' c d')
      oldEq =
        trans (cong₂ _∨_ (has-++ k (ctlRefs (ctl q)) (ctlRefsPs qs))
                         (has-++ k (refsP q) (refsPs qs)))
              (or-cross a b c d)
      moved = or-keepˡ (a ∨ c) (b' ∨ d') (b ∨ d) ih
                (subst (λ z → z ≡ true) newEq hf1)

thin-wf : ∀ h ps ps' →
  WF (sys h ps) →
  (∀ k → count k (refsOf (sys h ps')) ≤ count k (refsOf (sys h ps))) →
  (∀ k → hasG1 k (refsOf (sys h ps')) ≡ true →
         hasG1 k (refsOf (sys h ps)) ≡ true) →
  Bound (length h) (refsOf (sys h ps')) →
  WF (sys h ps')
thin-wf h ps ps' (_ , uq) le hs bNew =
  bNew , thin-unique (refsOf (sys h ps')) (refsOf (sys h ps)) le hs uq

-- Finishing drops the environment and the roots. The ether and the
-- mailbox stay, so every remaining reference was already in range.
done-wf : ∀ h ps i t → WF (sys h ps) → done1 (sys h ps) i ≡ just t → WF t
done-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  bAll = proj₁ wf
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
  bCtl = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  from : (m : Maybe Proc) → done1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = ⊥-elim (nothing≢just eqa)
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → done1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = ⊥-elim (nothing≢just eqc)
    onC (pr (go done env eth d dm)) eqc lk0 ec rewrite lk0 | ec =
      moved (update i p' ps) eqc refl
      where
      p' = record p { state = pstDone ; roots = []
                    ; ctl = pr (go done [] eth d dm) }
      fl = flightRefs eth
      msgs = mapRef (inbox p)
      moved : (m : Maybe (List Proc)) →
              (m >>= λ ps' → just (sys h ps')) ≡ just t →
              update i p' ps ≡ m → WF t
      moved nothing eql el rewrite el = ⊥-elim (nothing≢just eql)
      moved (just ps') refl eu =
        thin-wf h ps ps' wf (λ kq → leAll kq) (λ kq → hasAll kq) bNew
        where
        leOne : ∀ kq →
          count kq (ctlRefs (ctl p')) + count kq (refsP p') ≤
          count kq (ctlRefs (ctl p)) + count kq (refsP p)
        leOne kq =
          ≤-subst
            (≤-trans (≤-+ʳ (count kq msgs) (k≤n+k (count kq env) (count kq fl)))
                     (≤-+ˡ (count kq env + count kq fl)
                           (k≤n+k (count kq (roots p)) (count kq msgs))))
            (trans (cong (_+ (count kq (roots p) + count kq msgs))
                         (sym (count-++ kq env fl)))
            (trans (cong (count kq (env ++ fl) +_)
                         (sym (count-++ kq (roots p) msgs)))
                   (cong (λ xs → count kq xs + count kq (refsP p))
                         (cong ctlRefs (sym ec)))))
        impOne : ∀ kq →
          hasG1 kq (ctlRefs (ctl p')) ∨ hasG1 kq (refsP p') ≡ true →
          hasG1 kq (ctlRefs (ctl p)) ∨ hasG1 kq (refsP p) ≡ true
        impOne kq hf =
          subst (λ xs → hasG1 kq xs ∨ hasG1 kq (refsP p) ≡ true)
                (cong ctlRefs (sym ec))
                (∨-imp (hasG1 kq fl) (hasG1 kq msgs)
                       (hasG1 kq (env ++ fl)) (hasG1 kq (roots p ++ msgs))
                       (λ h1 → trans (has-++ kq env fl)
                                     (trans (cong (hasG1 kq env ∨_) h1)
                                            (∨-trueʳ (hasG1 kq env))))
                       (λ h1 → trans (has-++ kq (roots p) msgs)
                                     (trans (cong (hasG1 kq (roots p) ∨_) h1)
                                            (∨-trueʳ (hasG1 kq (roots p)))))
                       hf)
        leAll : ∀ kq → count kq (refsOf (sys h ps')) ≤ count kq (refsOf (sys h ps))
        leAll kq =
          ≤-left (refs-sum kq h ps')
            (≤-subst (sum-le (count kq (edgeRefs h))
                        (count kq (ctlRefsPs ps')) (count kq (refsPs ps'))
                        (count kq (ctlRefsPs ps)) (count kq (refsPs ps))
                        (upd-both-le i kq ps p p' ps' lk0 eu (leOne kq)))
                     (sym (refs-sum kq h ps)))
        hasAll : ∀ kq → hasG1 kq (refsOf (sys h ps')) ≡ true →
                        hasG1 kq (refsOf (sys h ps)) ≡ true
        hasAll kq hf =
          let mid = subst (λ z → z ≡ true) (refs-or kq h ps') hf
              flat = subst (λ z → z ≡ true)
                       (∨-assoc (hasG1 kq (edgeRefs h))
                                (hasG1 kq (ctlRefsPs ps'))
                                (hasG1 kq (refsPs ps')))
                       mid
              kept = or-keepˡ (hasG1 kq (edgeRefs h))
                       (hasG1 kq (ctlRefsPs ps') ∨ hasG1 kq (refsPs ps'))
                       (hasG1 kq (ctlRefsPs ps) ∨ hasG1 kq (refsPs ps))
                       (upd-both-imp i kq ps p p' ps' lk0 eu (impOne kq))
                       flat
              back = subst (λ z → z ≡ true)
                       (sym (∨-assoc (hasG1 kq (edgeRefs h))
                                     (hasG1 kq (ctlRefsPs ps))
                                     (hasG1 kq (refsPs ps))))
                       kept
          in subst (λ z → z ≡ true) (sym (refs-or kq h ps)) back
        bCtl' =
          proj₂ (bound-split env fl
            (subst (λ c0 → Bound (length h) (ctlRefs c0)) ec
                   (ctl-bound-at i ps p lk0 bCtl)))
        bRef' = proj₂ (bound-split (roots p) msgs (refsHere h ps i p wf lk0))
        bCtlPs' = upd-ctl-bound i ps p p' ps' bCtl lk0 eu bCtl'
        bRs' = upd-bound i ps p p' ps' bRs lk0 eu bRef'
        bNew = bound-++ (bound-++ bEdge bCtlPs') bRs'

------------------------------------------------------------------------
-- Pulling a flight deletes exactly one reference from control.
------------------------------------------------------------------------

data Drop (r : Ref) : List Ref → List Ref → Set where
  here  : ∀ rs → Drop r (r ∷ rs) rs
  there : ∀ x xs ys → Drop r xs ys → Drop r (x ∷ xs) (x ∷ ys)

pair-inj : ∀ {A B : Set} {x y : A} {u v : B} → (x , u) ≡ (y , v) → x ≡ y × u ≡ v
pair-inj refl = refl , refl

gone-++ : ∀ r xs ys zs → Drop r ys zs → Drop r (xs ++ ys) (xs ++ zs)
gone-++ r [] ys zs d = d
gone-++ r (x ∷ xs) ys zs d = there x (xs ++ ys) (xs ++ zs) (gone-++ r xs ys zs d)

gone-left : ∀ r xs ys zs → Drop r xs ys → Drop r (xs ++ zs) (ys ++ zs)
gone-left r .(r ∷ xs) xs zs (here xs) = here (xs ++ zs)
gone-left r .(x ∷ xs) .(x ∷ ys) zs (there x xs ys d) =
  there x (xs ++ zs) (ys ++ zs) (gone-left r xs ys zs d)

gone-count : ∀ k r xs ys → Drop r xs ys →
  count k ys + ext (obj r ≡ᵇ k) ≡ count k xs
gone-count k r .(r ∷ rs) rs (here rs) = +-comm (count k rs) (ext (obj r ≡ᵇ k))
gone-count k r .(x ∷ xs) .(x ∷ ys) (there x xs ys d) =
  trans (+-assoc (ext (obj x ≡ᵇ k)) (count k ys) (ext (obj r ≡ᵇ k)))
        (cong (ext (obj x ≡ᵇ k) +_) (gone-count k r xs ys d))

gone-has : ∀ k r xs ys → Drop r xs ys →
  hasG1 k ys ≡ true → hasG1 k xs ≡ true
gone-has k r .(r ∷ rs) rs (here rs) hf =
  trans (cong (gbit r k ∨_) hf) (∨-trueʳ (gbit r k))
gone-has k r .(x ∷ xs) .(x ∷ ys) (there x xs ys d) hf =
  or-keepˡ (gbit x k) (hasG1 k ys) (hasG1 k xs) (gone-has k r xs ys d) hf

gone-or : ∀ k r xs ys → Drop r xs ys →
  hasG1 k xs ≡ hasG1 k ys ∨ gbit r k
gone-or k r .(r ∷ rs) rs (here rs) = ∨-comm (gbit r k) (hasG1 k rs)
gone-or k r .(x ∷ xs) .(x ∷ ys) (there x xs ys d) =
  trans (cong (gbit x k ∨_) (gone-or k r xs ys d))
        (sym (∨-assoc (gbit x k) (hasG1 k ys) (gbit r k)))

gone-bound : ∀ {n} r xs ys → Drop r xs ys → Bound n xs → Bound n ys
gone-bound r .(r ∷ rs) rs (here rs) (bcons _ rest) = rest
gone-bound r .(x ∷ xs) .(x ∷ ys) (there x xs ys d) (bcons lt rest) =
  bcons lt (gone-bound r xs ys d rest)

pullCode-drop : ∀ c f c1 → pullCode c ≡ just (f , c1) →
  Drop (flightRef f) (codeRefs c) (codeRefs c1)
pullCode-drop (go _ _ [] _ _) _ _ ()
pullCode-drop (go _ env (flight j r ∷ eth) _ _) .(flight j r) .(go _ env eth _ _) refl =
  gone-++ r env (r ∷ flightRefs eth) (flightRefs eth) (here (flightRefs eth))

mutual
  frame-tail : (hd : Frame) (ks : List Frame) (f : Flight) (fs' : List Frame) →
    (pullFrames ks >>= λ (f0 , ks0) → just (f0 , hd ∷ ks0)) ≡ just (f , fs') →
    Drop (flightRef f) (frameRefs hd ++ framesRefs ks) (framesRefs fs')
  frame-tail hd ks f fs' eq = nested (pullFrames ks) eq refl
    where
    nested : (m : Maybe (Flight × List Frame)) →
             (m >>= λ (f0 , ks0) → just (f0 , hd ∷ ks0)) ≡ just (f , fs') →
             pullFrames ks ≡ m →
             Drop (flightRef f) (frameRefs hd ++ framesRefs ks) (framesRefs fs')
    nested nothing () _
    nested (just (f0 , ks0)) refl equ =
      gone-++ (flightRef f0) (frameRefs hd) (framesRefs ks) (framesRefs ks0)
              (pullFrames-drop ks f0 ks0 equ)

  pullFrames-drop : ∀ fs f fs' → pullFrames fs ≡ just (f , fs') →
    Drop (flightRef f) (framesRefs fs) (framesRefs fs')
  pullFrames-drop [] _ _ ()
  pullFrames-drop (saved c ∷ ks) f fs' eq with pullCode c in ep
  ... | nothing = nested (pullFrames ks) eq refl
    where
    nested : (m : Maybe (Flight × List Frame)) →
             (m >>= λ (f0 , ks0) → just (f0 , saved c ∷ ks0)) ≡ just (f , fs') →
             pullFrames ks ≡ m →
             Drop (flightRef f) (framesRefs (saved c ∷ ks)) (framesRefs fs')
    nested nothing () _
    nested (just (f0 , ks0)) refl equ =
      gone-++ (flightRef f0) (codeRefs c) (framesRefs ks) (framesRefs ks0)
              (pullFrames-drop ks f0 ks0 equ)
  ... | just (flight j r , c') =
    let ej , es = pair-inj (just-inj eq)
        dropped = gone-left r (codeRefs c) (codeRefs c') (framesRefs ks)
                    (pullCode-drop c (flight j r) c' ep)
    in subst (λ fs0 → Drop (flightRef f) (framesRefs (saved c ∷ ks)) (framesRefs fs0)) es
         (subst (λ f0 → Drop (flightRef f0) (framesRefs (saved c ∷ ks))
                              (framesRefs (saved c' ∷ ks))) ej dropped)
  pullFrames-drop (ar a ∷ ks) f fs' eq = frame-tail (ar a) ks f fs' eq
  pullFrames-drop (fn r ∷ ks) f fs' eq = frame-tail (fn r) ks f fs' eq
  pullFrames-drop (su ∷ ks) f fs' eq = frame-tail su ks f fs' eq
  pullFrames-drop (mt a b c ∷ ks) f fs' eq = frame-tail (mt a b c) ks f fs' eq
  pullFrames-drop (bd env ∷ ks) f fs' eq = frame-tail (bd env) ks f fs' eq

pullCtl-drop : ∀ c f c1 → pullCtl c ≡ just (f , c1) →
  Drop (flightRef f) (ctlRefs c) (ctlRefs c1)
pullCtl-drop idle _ _ ()
pullCtl-drop (pr c) f c1 eq with pullCode c in ep
... | nothing = ⊥-elim (nothing≢just eq)
... | just (f0 , c') =
  let ej , ec0 = pair-inj (just-inj eq)
  in subst (λ c2 → Drop (flightRef f) (codeRefs c) (ctlRefs c2)) ec0
       (subst (λ f1 → Drop (flightRef f1) (codeRefs c) (codeRefs c')) ej
              (pullCode-drop c f0 c' ep))
pullCtl-drop (ev t e k) f c1 eq with pullFrames k in ep
... | nothing = ⊥-elim (nothing≢just eq)
... | just (f0 , k') =
  let ej , ec0 = pair-inj (just-inj eq)
      dropped = gone-++ (flightRef f0) e (framesRefs k) (framesRefs k')
                  (pullFrames-drop k f0 k' ep)
  in subst (λ c2 → Drop (flightRef f) (ctlRefs (ev t e k)) (ctlRefs c2)) ec0
       (subst (λ f1 → Drop (flightRef f1) (ctlRefs (ev t e k)) (ctlRefs (ev t e k'))) ej
              dropped)
pullCtl-drop (rv x e k) f c1 eq with pullFrames k in ep
... | nothing = ⊥-elim (nothing≢just eq)
... | just (f0 , k') =
  let ej , ec0 = pair-inj (just-inj eq)
      pre = x ∷ e
      dropped = gone-++ (flightRef f0) pre (framesRefs k) (framesRefs k')
                  (pullFrames-drop k f0 k' ep)
  in subst (λ c2 → Drop (flightRef f) (ctlRefs (rv x e k)) (ctlRefs c2)) ec0
       (subst (λ f1 → Drop (flightRef f1) (ctlRefs (rv x e k)) (ctlRefs (rv x e k'))) ej
              dropped)

------------------------------------------------------------------------
-- Delivery. A dead tag drops the flight. Otherwise the flight moves
-- into the receiver's mailbox, including when sender and receiver
-- are the same process.
------------------------------------------------------------------------

wake-ctl : ∀ p → ctl (wake p) ≡ ctl p
wake-ctl p with state p
... | waiting = refl
... | ready   = refl
... | pstDone = refl

wake-refs : ∀ p → refsP (wake p) ≡ refsP p
wake-refs p with state p
... | waiting = refl
... | ready   = refl
... | pstDone = refl

gone-obj : ∀ {n} r xs ys → Drop r xs ys → Bound n xs → obj r < n
gone-obj r .(r ∷ rs) rs (here rs) (bcons lt _) = lt
gone-obj r .(x ∷ xs) .(x ∷ ys) (there x xs ys d) (bcons _ rest) =
  gone-obj r xs ys d rest

ctlPs-drop : ∀ i ps p c1 ps1 f →
  lookup ps i ≡ just p →
  setProc ps i c1 ≡ just ps1 →
  pullCtl (ctl p) ≡ just (f , c1) →
  Drop (flightRef f) (ctlRefsPs ps) (ctlRefsPs ps1)
ctlPs-drop i ps p c1 ps1 f lk es ep with set-both i ps p c1 ps1 lk es
... | both L R e1 e2 _ =
  let fr = flightRef f
      inner = gone-left fr (ctlRefs (ctl p)) (ctlRefs c1) R (pullCtl-drop (ctl p) f c1 ep)
      full = gone-++ fr L (ctlRefs (ctl p) ++ R) (ctlRefs c1 ++ R) inner
  in subst (λ xs → Drop fr (ctlRefsPs ps) xs) (sym e2)
       (subst (λ ys → Drop fr ys (L ++ ctlRefs c1 ++ R)) (sym e1) full)

shift : ∀ e a b r x → a + x ≡ b → ((e + a) + r) + x ≡ (e + b) + r
shift e a b r x eq =
  trans (+-assoc (e + a) r x)
  (trans (cong ((e + a) +_) (+-comm r x))
  (trans (sym (+-assoc (e + a) x r))
  (trans (cong (_+ r) (+-assoc e a x))
         (cong (λ z → (e + z) + r) eq))))

lose-sum : ∀ k h ps ps1 r →
  Drop r (ctlRefsPs ps) (ctlRefsPs ps1) →
  refsPs ps1 ≡ refsPs ps →
  count k (refsOf (sys h ps1)) + ext (obj r ≡ᵇ k) ≡ count k (refsOf (sys h ps))
lose-sum k h ps ps1 r d rq =
  trans (cong (_+ ext (obj r ≡ᵇ k)) (refs-sum k h ps1))
  (trans (cong (λ z → ((count k (edgeRefs h) + count k (ctlRefsPs ps1)) + z) + ext (obj r ≡ᵇ k))
               (cong (count k) rq))
  (trans (shift (count k (edgeRefs h)) (count k (ctlRefsPs ps1)) (count k (ctlRefsPs ps))
                (count k (refsPs ps)) (ext (obj r ≡ᵇ k))
                (gone-count k r (ctlRefsPs ps) (ctlRefsPs ps1) d))
         (sym (refs-sum k h ps))))

reassoc : ∀ a b c d → (a ∨ (b ∨ c)) ∨ d ≡ ((a ∨ b) ∨ d) ∨ c
reassoc a b c d =
  trans (cong (_∨ d) (sym (∨-assoc a b c)))
  (trans (∨-assoc (a ∨ b) c d)
  (trans (cong ((a ∨ b) ∨_) (∨-comm c d))
         (sym (∨-assoc (a ∨ b) d c))))

lose-or : ∀ k h ps ps1 r →
  Drop r (ctlRefsPs ps) (ctlRefsPs ps1) →
  refsPs ps1 ≡ refsPs ps →
  hasG1 k (refsOf (sys h ps)) ≡ hasG1 k (refsOf (sys h ps1)) ∨ gbit r k
lose-or k h ps ps1 r d rq =
  trans (refs-or k h ps)
  (trans (cong (λ z → (hasG1 k (edgeRefs h) ∨ z) ∨ hasG1 k (refsPs ps))
               (gone-or k r (ctlRefsPs ps) (ctlRefsPs ps1) d))
  (trans (cong (λ z → (hasG1 k (edgeRefs h) ∨ (hasG1 k (ctlRefsPs ps1) ∨ gbit r k)) ∨ z)
               (sym (cong (hasG1 k) rq)))
  (trans (reassoc (hasG1 k (edgeRefs h)) (hasG1 k (ctlRefsPs ps1)) (gbit r k)
                  (hasG1 k (refsPs ps1)))
         (cong (_∨ gbit r k) (sym (refs-or k h ps1))))))

ctl-same : ∀ i ps p p' ps' →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  ctlRefs (ctl p') ≡ ctlRefs (ctl p) →
  ctlRefsPs ps' ≡ ctlRefsPs ps
ctl-same i ps p p' ps' lk eq creq = walk i ps p ps' lk eq creq
  where
  walk : ∀ i ps p ps' →
         lookup ps i ≡ just p → update i p' ps ≡ just ps' →
         ctlRefs (ctl p') ≡ ctlRefs (ctl p) →
         ctlRefsPs ps' ≡ ctlRefsPs ps
  walk _ [] _ _ () _ _
  walk zero (q ∷ qs) .q .(p' ∷ qs) refl refl cq =
    cong (_++ ctlRefsPs qs) cq
  walk (suc j) (q ∷ qs) p0 ps0 lk0 eq0 cq = step (update j p' qs) eq0 refl
    where
    step : (m : Maybe (List Proc)) → mapCons q m ≡ just ps0 →
           update j p' qs ≡ m → ctlRefsPs ps0 ≡ ctlRefsPs (q ∷ qs)
    step nothing () _
    step (just qs') refl equ =
      cong (ctlRefs (ctl q) ++_) (walk j qs p0 qs' lk0 equ cq)

has-gain : ∀ k g i ps p p' ps' →
  lookup ps i ≡ just p →
  update i p' ps ≡ just ps' →
  hasG1 k (refsP p') ≡ hasG1 k (refsP p) ∨ g →
  hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps) ∨ g
has-gain k g i ps p p' ps' lk eq hq = walk i ps p ps' lk eq hq
  where
  walk : ∀ i ps p ps' →
         lookup ps i ≡ just p → update i p' ps ≡ just ps' →
         hasG1 k (refsP p') ≡ hasG1 k (refsP p) ∨ g →
         hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps) ∨ g
  walk _ [] _ _ () _ _
  walk zero (q ∷ qs) .q .(p' ∷ qs) refl refl hq0 =
    trans (has-++ k (refsP p') (refsPs qs))
    (trans (cong (_∨ hasG1 k (refsPs qs)) hq0)
    (trans (cong (λ z → (z ∨ hasG1 k (refsPs qs))) (∨-comm (hasG1 k (refsP q)) g))
    (trans (∨-assoc g (hasG1 k (refsP q)) (hasG1 k (refsPs qs)))
    (trans (∨-comm g (hasG1 k (refsP q) ∨ hasG1 k (refsPs qs)))
           (cong (_∨ g) (sym (has-++ k (refsP q) (refsPs qs))))))))
  walk (suc j) (q ∷ qs) p0 ps0 lk0 eq0 hq0 = step (update j p' qs) eq0 refl
    where
    step : (m : Maybe (List Proc)) → mapCons q m ≡ just ps0 →
           update j p' qs ≡ m →
           hasG1 k (refsPs ps0) ≡ hasG1 k (refsPs (q ∷ qs)) ∨ g
    step nothing () _
    step (just qs') refl equ =
      trans (has-++ k (refsP q) (refsPs qs'))
      (trans (cong (hasG1 k (refsP q) ∨_) (walk j qs p0 qs' lk0 equ hq0))
      (trans (sym (∨-assoc (hasG1 k (refsP q)) (hasG1 k (refsPs qs)) g))
             (cong (_∨ g) (sym (has-++ k (refsP q) (refsPs qs))))))

drop-keep : ∀ h ps ps1 r →
  WF (sys h ps) →
  Drop r (ctlRefsPs ps) (ctlRefsPs ps1) →
  refsPs ps1 ≡ refsPs ps →
  WF (sys h ps1)
drop-keep h ps ps1 r wf d rq =
  thin-wf h ps ps1 wf leAll hasAll bNew
  where
  bAll = proj₁ wf
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
  bCtl = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  leAll : ∀ k → count k (refsOf (sys h ps1)) ≤ count k (refsOf (sys h ps))
  leAll k = ≤-subst (m≤m+k (count k (refsOf (sys h ps1))) (ext (obj r ≡ᵇ k)))
                    (lose-sum k h ps ps1 r d rq)
  hasAll : ∀ k → hasG1 k (refsOf (sys h ps1)) ≡ true →
                  hasG1 k (refsOf (sys h ps)) ≡ true
  hasAll k hf =
    trans (lose-or k h ps ps1 r d rq) (cong (_∨ gbit r k) hf)
  bNew = bound-++ (bound-++ bEdge (gone-bound r (ctlRefsPs ps) (ctlRefsPs ps1) d bCtl))
                  (subst (Bound (length h)) (sym rq) bRs)

post-keep : ∀ h ps ps1 ps2 j q r qp →
  WF (sys h ps) →
  Drop r (ctlRefsPs ps) (ctlRefsPs ps1) →
  refsPs ps1 ≡ refsPs ps →
  lookup ps1 j ≡ just q →
  update j qp ps1 ≡ just ps2 →
  qp ≡ wake (post q r) →
  WF (sys h ps2)
post-keep h ps ps1 ps2 j q r qp wf d rq ld eu ewake =
  keep-refs h ps ps2 wf countAll hasAll bNew
  where
  bAll = proj₁ wf
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
  bCtl = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs1 = subst (Bound (length h)) (sym rq) bRs
  ctlEq = ctl-same j ps1 q qp ps2 ld eu
            (trans (cong ctlRefs (cong ctl ewake)) (cong ctlRefs (wake-ctl (post q r))))
  countAll : ∀ k → count k (refsOf (sys h ps2)) ≡ count k (refsOf (sys h ps))
  countAll k =
    trans (refs-sum k h ps2)
    (trans (cong (λ c → (count k (edgeRefs h) + c) + count k (refsPs ps2))
                 (cong (count k) ctlEq))
    (trans (cong ((count k (edgeRefs h) + count k (ctlRefsPs ps1)) +_)
                 (upd-add k j ps1 q qp ps2 (ext (obj r ≡ᵇ k)) ld eu
                    (trans (cong (count k) (cong refsP ewake))
                    (trans (cong (count k) (wake-refs (post q r)))
                           (post-count k q r)))))
    (trans (sym (+-assoc (count k (edgeRefs h) + count k (ctlRefsPs ps1))
                         (count k (refsPs ps1)) (ext (obj r ≡ᵇ k))))
    (trans (cong (_+ ext (obj r ≡ᵇ k)) (sym (refs-sum k h ps1)))
           (lose-sum k h ps ps1 r d rq)))))
  hasAll : ∀ k → hasG1 k (refsOf (sys h ps2)) ≡ hasG1 k (refsOf (sys h ps))
  hasAll k =
    trans (refs-or k h ps2)
    (trans (cong (λ c → (hasG1 k (edgeRefs h) ∨ c) ∨ hasG1 k (refsPs ps2))
                 (cong (hasG1 k) ctlEq))
    (trans (cong ((hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps1)) ∨_)
                 (has-gain k (gbit r k) j ps1 q qp ps2 ld eu
                    (trans (cong (hasG1 k) (cong refsP ewake))
                    (trans (cong (hasG1 k) (wake-refs (post q r)))
                           (post-has k q r)))))
    (trans (sym (∨-assoc (hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps1))
                         (hasG1 k (refsPs ps1)) (gbit r k)))
    (trans (cong (_∨ gbit r k) (sym (refs-or k h ps1)))
           (sym (lose-or k h ps ps1 r d rq))))))
  olt = gone-obj r (ctlRefsPs ps) (ctlRefsPs ps1) d bCtl
  bCtl1 = gone-bound r (ctlRefsPs ps) (ctlRefsPs ps1) d bCtl
  bHere = lookup-bound j ps1 q bRs1 ld
  bPost = subst (Bound (length h)) (sym (wake-refs (post q r))) (post-bound q r bHere olt)
  bRef2 = subst (Bound (length h)) (cong refsP (sym ewake)) bPost
  bCtl2 = subst (Bound (length h)) (sym ctlEq) bCtl1
  bRs2 = upd-bound j ps1 q qp ps2 bRs1 ld eu bRef2
  bNew = bound-++ (bound-++ bEdge bCtl2) bRs2

deliver-wf : ∀ h ps i t → WF (sys h ps) → deliver1 (sys h ps) i ≡ just t → WF t
deliver-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  from : (m : Maybe Proc) → deliver1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = ⊥-elim (nothing≢just eqa)
  from (just p) eqa lk rewrite lk with pullCtl (ctl p) in ep
  ... | nothing = ⊥-elim (nothing≢just eqa)
  ... | just (flight j r , c1) = sent (setProc ps i c1) eqa refl
    where
    sent : (m : Maybe (List Proc)) →
           (m >>= λ ps1 →
              lookup ps1 j >>= λ q →
              if hasTag (obj r) (deadInCtl (ctl q)) then just (sys h ps1)
              else update j (wake (post q r)) ps1 >>= λ ps2 → just (sys h ps2)) ≡ just t →
           setProc ps i c1 ≡ m → WF t
    sent nothing eql el rewrite el = ⊥-elim (nothing≢just eql)
    sent (just ps1) eql el rewrite el = dest (lookup ps1 j) eql refl
      where
      dropped = ctlPs-drop i ps p c1 ps1 (flight j r) lk el ep
      sameR = set-refsPs i ps c1 ps1 el
      dest : (m : Maybe Proc) →
             (m >>= λ q →
                if hasTag (obj r) (deadInCtl (ctl q)) then just (sys h ps1)
                else update j (wake (post q r)) ps1 >>= λ ps2 → just (sys h ps2)) ≡ just t →
             lookup ps1 j ≡ m → WF t
      dest nothing eqd ld rewrite ld = ⊥-elim (nothing≢just eqd)
      dest (just q) eqd ld rewrite ld = br (hasTag (obj r) (deadInCtl (ctl q))) eqd refl
        where
        br : (b : Bool) →
             (if b then just (sys h ps1)
                   else update j (wake (post q r)) ps1 >>= λ ps2 → just (sys h ps2)) ≡ just t →
             hasTag (obj r) (deadInCtl (ctl q)) ≡ b → WF t
        br true eb _ =
          subst WF (just-inj eb) (drop-keep h ps ps1 (flightRef (flight j r)) wf dropped sameR)
        br false eb _ = posted (update j (wake (post q r)) ps1) eb refl
          where
          posted : (m : Maybe (List Proc)) →
                   (m >>= λ ps2 → just (sys h ps2)) ≡ just t →
                   update j (wake (post q r)) ps1 ≡ m → WF t
          posted nothing equ eu rewrite eu = ⊥-elim (nothing≢just equ)
          posted (just ps2) refl eu =
            post-keep h ps ps1 ps2 j q (flightRef (flight j r)) (wake (post q r))
              wf dropped sameR ld eu refl

------------------------------------------------------------------------
-- Emit. A copy appends one non-g1 alias. A move takes the reference
-- out of the environment and puts the same reference on a flight,
-- leaving a fresh g0 placeholder behind.
------------------------------------------------------------------------

fly-count : ∀ k env eth j r →
  count k (env ++ flightRefs (eth ++ flight j r ∷ [])) ≡
  count k (env ++ flightRefs eth) + ext (obj r ≡ᵇ k)
fly-count k env eth j r =
  trans (cong (count k) (cong (env ++_) (flightRefs-++ eth (flight j r ∷ []))))
  (trans (cong (count k) (sym (++-assoc env (flightRefs eth) (r ∷ []))))
         (count-snoc k (env ++ flightRefs eth) r))

fly-has : ∀ k env eth j r → isG1 (checked r) ≡ false →
  hasG1 k (env ++ flightRefs (eth ++ flight j r ∷ [])) ≡
  hasG1 k (env ++ flightRefs eth)
fly-has k env eth j r ng =
  trans (cong (hasG1 k) (cong (env ++_) (flightRefs-++ eth (flight j r ∷ []))))
  (trans (cong (hasG1 k) (sym (++-assoc env (flightRefs eth) (r ∷ []))))
  (trans (has-snoc k (env ++ flightRefs eth) r)
  (trans (cong (hasG1 k (env ++ flightRefs eth) ∨_)
               (trans (cong ((obj r ≡ᵇ k) ∧_) ng) (∧-falseʳ (obj r ≡ᵇ k))))
         (∨-falseʳ (hasG1 k (env ++ flightRefs eth))))))

park-count : ∀ k n xs r b ys →
  lookup xs n ≡ just r →
  count k (repl n b xs ++ (ys ++ (r ∷ []))) ≡
  count k (xs ++ ys) + ext (obj b ≡ᵇ k)
park-count _ _ [] _ _ _ ()
park-count k zero (x ∷ xs) .x b ys refl =
  trans (cong (ext (obj b ≡ᵇ k) +_)
              (trans (cong (count k) (sym (++-assoc xs ys (x ∷ []))))
                     (count-snoc k (xs ++ ys) x)))
  (trans (sym (+-assoc (ext (obj b ≡ᵇ k)) (count k (xs ++ ys)) (ext (obj x ≡ᵇ k))))
  (trans (cong (_+ ext (obj x ≡ᵇ k)) (+-comm (ext (obj b ≡ᵇ k)) (count k (xs ++ ys))))
  (trans (+-assoc (count k (xs ++ ys)) (ext (obj b ≡ᵇ k)) (ext (obj x ≡ᵇ k)))
  (trans (cong (count k (xs ++ ys) +_) (+-comm (ext (obj b ≡ᵇ k)) (ext (obj x ≡ᵇ k))))
  (trans (sym (+-assoc (count k (xs ++ ys)) (ext (obj x ≡ᵇ k)) (ext (obj b ≡ᵇ k))))
         (cong (_+ ext (obj b ≡ᵇ k)) (+-comm (count k (xs ++ ys)) (ext (obj x ≡ᵇ k)))))))))
park-count k (suc n) (x ∷ xs) r b ys eq =
  trans (cong (ext (obj x ≡ᵇ k) +_) (park-count k n xs r b ys eq))
        (sym (+-assoc (ext (obj x ≡ᵇ k)) (count k (xs ++ ys)) (ext (obj b ≡ᵇ k))))

park-has : ∀ k n xs r b ys →
  lookup xs n ≡ just r →
  isG1 (checked b) ≡ false →
  hasG1 k (repl n b xs ++ (ys ++ (r ∷ []))) ≡ hasG1 k (xs ++ ys)
park-has _ _ [] _ _ _ () _
park-has k zero (x ∷ xs) .x b ys refl ng =
  trans (cong (λ g → ((obj b ≡ᵇ k) ∧ g) ∨ hasG1 k (xs ++ (ys ++ (x ∷ [])))) ng)
  (trans (cong (λ w → w ∨ hasG1 k (xs ++ (ys ++ (x ∷ [])))) (∧-falseʳ (obj b ≡ᵇ k)))
  (trans (cong (hasG1 k) (sym (++-assoc xs ys (x ∷ []))))
  (trans (has-snoc k (xs ++ ys) x)
         (∨-comm (hasG1 k (xs ++ ys)) (gbit x k)))))
park-has k (suc n) (x ∷ xs) r b ys eq ng =
  cong (λ w → ((obj x ≡ᵇ k) ∧ isG1 (checked x)) ∨ w)
       (park-has k n xs r b ys eq ng)

add-ctl : ∀ k h h' ps ps' n →
  count k (edgeRefs h') ≡ count k (edgeRefs h) →
  count k (ctlRefsPs ps') ≡ count k (ctlRefsPs ps) + n →
  count k (refsPs ps') ≡ count k (refsPs ps) →
  count k (refsOf (sys h' ps')) ≡ count k (refsOf (sys h ps)) + n
add-ctl k h h' ps ps' n eqE cq rq =
  trans (refs-sum k h' ps')
  (trans (cong (λ e → (e + count k (ctlRefsPs ps')) + count k (refsPs ps')) eqE)
  (trans (cong (λ c → (count k (edgeRefs h) + c) + count k (refsPs ps')) cq)
  (trans (cong (λ z → (count k (edgeRefs h) + (count k (ctlRefsPs ps) + n)) + z) rq)
  (trans (cong (_+ count k (refsPs ps))
               (sym (+-assoc (count k (edgeRefs h)) (count k (ctlRefsPs ps)) n)))
  (trans (+-right (count k (edgeRefs h) + count k (ctlRefsPs ps)) n
                  (count k (refsPs ps)))
         (cong (_+ n) (sym (refs-sum k h ps))))))))

same-has : ∀ k h h' ps ps' →
  hasG1 k (edgeRefs h') ≡ hasG1 k (edgeRefs h) →
  hasG1 k (ctlRefsPs ps') ≡ hasG1 k (ctlRefsPs ps) →
  hasG1 k (refsPs ps') ≡ hasG1 k (refsPs ps) →
  hasG1 k (refsOf (sys h' ps')) ≡ hasG1 k (refsOf (sys h ps))
same-has k h h' ps ps' eqE cq rq =
  trans (refs-or k h' ps')
  (trans (cong (λ e → (e ∨ hasG1 k (ctlRefsPs ps')) ∨ hasG1 k (refsPs ps')) eqE)
  (trans (cong (λ c → (hasG1 k (edgeRefs h) ∨ c) ∨ hasG1 k (refsPs ps')) cq)
  (trans (cong (λ z → (hasG1 k (edgeRefs h) ∨ hasG1 k (ctlRefsPs ps)) ∨ z) rq)
         (sym (refs-or k h ps)))))

open-at : ∀ xs n r → lookup xs n ≡ just r →
  Σ (List Ref) (λ pre → Σ (List Ref) (λ post → xs ≡ pre ++ (r ∷ post)))
open-at [] _ _ ()
open-at (x ∷ xs) zero .x refl = [] , (xs , refl)
open-at (x ∷ xs) (suc n) r eq = (x ∷ pre) , (suf , cong (x ∷_) e)
  where
  got = open-at xs n r eq
  pre = proj₁ got
  suf = proj₁ (proj₂ got)
  e = proj₂ (proj₂ got)

ctl-open : ∀ i ps p → lookup ps i ≡ just p →
  Σ (List Ref) (λ L → Σ (List Ref) (λ R →
    ctlRefsPs ps ≡ L ++ ctlRefs (ctl p) ++ R))
ctl-open _ [] _ ()
ctl-open zero (p ∷ ps) .p refl = [] , (ctlRefsPs ps , refl)
ctl-open (suc i) (q ∷ ps) p eq = (ctlRefs (ctl q) ++ L) , (R , eqAll)
  where
  got = ctl-open i ps p eq
  L = proj₁ got
  R = proj₁ (proj₂ got)
  e = proj₂ (proj₂ got)
  eqAll =
    trans (cong (ctlRefs (ctl q) ++_) e)
          (sym (++-assoc (ctlRefs (ctl q)) L (ctlRefs (ctl p) ++ R)))

bury : (ys pre : List Ref) (r : Ref) (post zs : List Ref) →
  ys ++ (pre ++ (r ∷ post)) ++ zs ≡ (ys ++ pre) ++ (r ∷ (post ++ zs))
bury ys pre r post zs =
  trans (cong (ys ++_) (++-assoc pre (r ∷ post) zs))
        (sym (++-assoc ys pre (r ∷ (post ++ zs))))

alias-miss : ∀ k h ps i p env r pre post eth →
  lookup ps i ≡ just p →
  ctlRefs (ctl p) ≡ env ++ flightRefs eth →
  env ≡ pre ++ (r ∷ post) →
  isG1 (checked r) ≡ false →
  Grade1Unique (refsOf (sys h ps)) →
  hasG1 k (refsOf (sys h ps)) ≡ true →
  ext (obj r ≡ᵇ k) ≡ 0
alias-miss k h ps i p env r pre post eth lk cr eenv ng uq hf =
  occ-ext k preAll r postAll ng
    (subst Grade1Unique flat uq)
    (subst (λ xs → hasG1 k xs ≡ true) flat hf)
  where
  got = ctl-open i ps p lk
  L = proj₁ got
  R = proj₁ (proj₂ got)
  ectl = proj₂ (proj₂ got)
  mid = post ++ flightRefs eth
  stepCode : ctlRefs (ctl p) ≡ pre ++ (r ∷ mid)
  stepCode =
    trans cr
    (trans (cong (_++ flightRefs eth) eenv)
           (++-assoc pre (r ∷ post) (flightRefs eth)))
  form = (L ++ pre) ++ (r ∷ (mid ++ R))
  eCtlPs : ctlRefsPs ps ≡ form
  eCtlPs =
    trans ectl
    (trans (cong (λ c → L ++ c ++ R) stepCode)
           (bury L pre r mid R))
  rest = mid ++ R
  preAll = edgeRefs h ++ (L ++ pre)
  postAll = rest ++ refsPs ps
  flat : refsOf (sys h ps) ≡ preAll ++ (r ∷ postAll)
  flat =
    trans (cong (λ c → (edgeRefs h ++ c) ++ refsPs ps) eCtlPs)
    (trans (++-assoc (edgeRefs h) form (refsPs ps))
           (bury (edgeRefs h) (L ++ pre) r rest (refsPs ps)))

copy-step : ∀ {n} h ps i p ps' j (x : Fin n) cont env eth d dm r →
  WF (sys h ps) →
  lookup ps i ≡ just p →
  ctl p ≡ pr (go (send j x cont) env eth d dm) →
  lookup env (toℕ x) ≡ just r →
  isG1 (checked r) ≡ false →
  setProc ps i (pr (go cont env (eth ++ flight j r ∷ []) d dm)) ≡ just ps' →
  WF (sys h ps')
copy-step h ps i p ps' j x cont env eth d dm r wf lk ec lu ng es =
  grow-sys {h} {ps} h ps' (λ kq → ext (obj r ≡ᵇ kq)) wf bNew
    (λ kq → countAll kq) (λ kq → hasAll kq) zx
  where
  c' = pr (go cont env (eth ++ flight j r ∷ []) d dm)
  oreq = cong ctlRefs ec
  bAll = proj₁ wf
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
  bCtlPs = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bCode = subst (Bound (length h)) oreq (ctlHere h ps i p wf lk)
  bEnv = proj₁ (bound-split env (flightRefs eth) bCode)
  olt = bound-lookup env (toℕ x) r bEnv lu
  eqNew : ctlRefs c' ≡ (env ++ flightRefs eth) ++ (r ∷ [])
  eqNew =
    trans (cong (env ++_) (flightRefs-++ eth (flight j r ∷ [])))
          (sym (++-assoc env (flightRefs eth) (r ∷ [])))
  bCtl1 = subst (Bound (length h)) (sym eqNew) (bound-snoc bCode olt)
  bCtl' = set-ctl-bound i ps p c' ps' lk es bCtlPs bCtl1
  bRs' = subst (Bound (length h)) (sym (set-refsPs i ps c' ps' es)) bRs
  bNew = bound-++ (bound-++ bEdge bCtl') bRs'
  cOne : ∀ kq → count kq (ctlRefs c') ≡ count kq (ctlRefs (ctl p)) + ext (obj r ≡ᵇ kq)
  cOne kq =
    trans (fly-count kq env eth j r)
          (cong (_+ ext (obj r ≡ᵇ kq)) (sym (cong (count kq) oreq)))
  hOne : ∀ kq → hasG1 kq (ctlRefs c') ≡ hasG1 kq (ctlRefs (ctl p))
  hOne kq =
    trans (fly-has kq env eth j r ng)
          (sym (cong (hasG1 kq) oreq))
  countAll : ∀ kq →
    count kq (refsOf (sys h ps')) ≡ count kq (refsOf (sys h ps)) + ext (obj r ≡ᵇ kq)
  countAll kq =
    add-ctl kq h h ps ps' (ext (obj r ≡ᵇ kq)) refl
      (lift-plus kq i ps p c' ps' (ext (obj r ≡ᵇ kq)) lk es (cOne kq))
      (cong (count kq) (set-refsPs i ps c' ps' es))
  hasAll : ∀ kq → hasG1 kq (refsOf (sys h ps')) ≡ hasG1 kq (refsOf (sys h ps))
  hasAll kq =
    same-has kq h h ps ps' refl
      (lift-has kq i ps p c' ps' lk es (hOne kq))
      (cong (hasG1 kq) (set-refsPs i ps c' ps' es))
  got = open-at env (toℕ x) r lu
  pre = proj₁ got
  suf = proj₁ (proj₂ got)
  eenv = proj₂ (proj₂ got)
  zx : ∀ kq → hasG1 kq (refsOf (sys h ps)) ≡ true → ext (obj r ≡ᵇ kq) ≡ 0
  zx kq hf =
    alias-miss kq h ps i p env r pre suf eth lk oreq eenv ng (proj₂ wf) hf

move-step : ∀ {n} h ps i p ps' j (x : Fin n) cont env eth d dm r →
  WF (sys h ps) →
  lookup ps i ≡ just p →
  ctl p ≡ pr (go (send j x cont) env eth d dm) →
  lookup env (toℕ x) ≡ just r →
  setProc ps i (pr (go cont (repl (toℕ x) (placeholder h) env)
                       (eth ++ flight j r ∷ []) d dm)) ≡ just ps' →
  WF (sys (snoc h (nat zero)) ps')
move-step h ps i p ps' j x cont env eth d dm r wf lk ec lu es =
  grow-sys {h} {ps} h' ps' (λ kq → ext (length h ≡ᵇ kq)) wf bNew
    (λ kq → countAll kq) (λ kq → hasAll kq) zx
  where
  ph = placeholder h
  h' = snoc h (nat zero)
  env' = repl (toℕ x) ph env
  c' = pr (go cont env' (eth ++ flight j r ∷ []) d dm)
  oreq = cong ctlRefs ec
  len = length-snoc h (cell (nat zero) live)
  bAll = proj₁ wf
  bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
  bCtlPs = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
  bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
  bCode = subst (Bound (length h)) oreq (ctlHere h ps i p wf lk)
  bEnv = proj₁ (bound-split env (flightRefs eth) bCode)
  bFly = proj₂ (bound-split env (flightRefs eth) bCode)
  olt = bound-lookup env (toℕ x) r bEnv lu
  bRepl = bound-repl-< (toℕ x) env ph r (monoS bEnv) lu (fresh-< (length h))
  bSnoc = bound-snoc (monoS bFly) (≤-step olt)
  mreq : ctlRefs c' ≡ env' ++ (flightRefs eth ++ (r ∷ []))
  mreq = cong (env' ++_) (flightRefs-++ eth (flight j r ∷ []))
  bCtl1 = subst (Bound (suc (length h))) (sym mreq) (bound-++ bRepl bSnoc)
  bCtl' = set-ctl-bound i ps p c' ps' lk es (monoS bCtlPs) bCtl1
  bEdge' = subst (Bound (suc (length h))) (sym (edge-nat h zero)) (monoS bEdge)
  bRs' = subst (Bound (suc (length h))) (sym (set-refsPs i ps c' ps' es)) (monoS bRs)
  bSuc = bound-++ (bound-++ bEdge' bCtl') bRs'
  bNew = subst (λ n → Bound n (refsOf (sys h' ps'))) (sym len) bSuc
  cOne : ∀ kq →
    count kq (ctlRefs c') ≡ count kq (ctlRefs (ctl p)) + ext (length h ≡ᵇ kq)
  cOne kq =
    trans (cong (count kq) mreq)
    (trans (park-count kq (toℕ x) env r ph (flightRefs eth) lu)
           (cong (_+ ext (obj ph ≡ᵇ kq)) (sym (cong (count kq) oreq))))
  hOne : ∀ kq → hasG1 kq (ctlRefs c') ≡ hasG1 kq (ctlRefs (ctl p))
  hOne kq =
    trans (cong (hasG1 kq) mreq)
    (trans (park-has kq (toℕ x) env r ph (flightRefs eth) lu g0-ng)
           (sym (cong (hasG1 kq) oreq)))
  countAll : ∀ kq →
    count kq (refsOf (sys h' ps')) ≡
    count kq (refsOf (sys h ps)) + ext (length h ≡ᵇ kq)
  countAll kq =
    add-ctl kq h h' ps ps' (ext (length h ≡ᵇ kq))
      (cong (count kq) (edge-nat h zero))
      (lift-plus kq i ps p c' ps' (ext (length h ≡ᵇ kq)) lk es (cOne kq))
      (cong (count kq) (set-refsPs i ps c' ps' es))
  hasAll : ∀ kq → hasG1 kq (refsOf (sys h' ps')) ≡ hasG1 kq (refsOf (sys h ps))
  hasAll kq =
    same-has kq h h' ps ps' (cong (hasG1 kq) (edge-nat h zero))
      (lift-has kq i ps p c' ps' lk es (hOne kq))
      (cong (hasG1 kq) (set-refsPs i ps c' ps' es))
  zx : ∀ kq → hasG1 kq (refsOf (sys h ps)) ≡ true → ext (length h ≡ᵇ kq) ≡ 0
  zx kq hf = fresh-zero kq (length h) (refsOf (sys h ps)) bAll hf

emit-wf : ∀ h ps i t → WF (sys h ps) → emit1 (sys h ps) i ≡ just t → WF t
emit-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  no : nothing ≡ just t → WF t
  no e = ⊥-elim (nothing≢just e)
  from : (m : Maybe Proc) → emit1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = no eqa
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → emit1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (spawn _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (send j x k) env eth d dm)) eqc lk0 ec rewrite lk0 | ec
      with lookup env (toℕ x) in lu
    ... | nothing = no eqc
    ... | just r with isZeroGrade (residual r) in ez
    ... | true = no eqc
    ... | false with blocked ps j (obj r) in eb
    ... | true = no eqc
    ... | false with kind (checked r) in ek
    ... | nothing = no eqc
    ... | just Kmove = moved (setProc ps i cM) eqc refl
      where
      cM = pr (go k (repl (toℕ x) (placeholder h) env) (eth ++ flight j r ∷ []) d dm)
      moved : (m : Maybe (List Proc)) →
              (m >>= λ ps' → just (sys (snoc h (nat zero)) ps')) ≡ just t →
              setProc ps i cM ≡ m → WF t
      moved nothing eql es0 = no eql
      moved (just ps') refl es0 =
        move-step h ps i p ps' j x k env eth d dm r wf lk0 ec lu es0
    ... | just Kcopy = copied (setProc ps i cC) eqc refl
      where
      cC = pr (go k env (eth ++ flight j r ∷ []) d dm)
      copied : (m : Maybe (List Proc)) →
               (m >>= λ ps' → just (sys h ps')) ≡ just t →
               setProc ps i cC ≡ m → WF t
      copied nothing eql es0 = no eql
      copied (just ps') refl es0 =
        copy-step h ps i p ps' j x k env eth d dm r wf lk0 ec lu
          (copy-not-g1 (checked r) ek) es0

------------------------------------------------------------------------
-- Spawn. The child receives the moved and copied slots. The parent
-- keeps the rest, with one shared g0 placeholder for every move.
-- The fresh cell is grade 0, so grade-1 uniqueness is unchanged.
------------------------------------------------------------------------

or-right : ∀ x k c → (x ∨ k) ∨ c ≡ (x ∨ c) ∨ k
or-right x k c =
  trans (∨-assoc x k c)
  (trans (cong (x ∨_) (∨-comm k c))
         (sym (∨-assoc x c k)))

mix : ∀ L pe ys R ce env b →
  ce + pe ≡ env + b →
  ((L + (pe + ys)) + R) + ce ≡ (L + ((env + ys) + R)) + b
mix L pe ys R ce env b eq =
  trans s1 (trans s2 (trans s3 (trans s4 (trans s5
  (trans s6 (trans s7 (trans s8 (trans s9 (trans s10 s11)))))))))
  where
  s1 : ((L + (pe + ys)) + R) + ce ≡ (((L + pe) + ys) + R) + ce
  s1 = cong (λ z → (z + R) + ce) (sym (+-assoc L pe ys))
  s2 : (((L + pe) + ys) + R) + ce ≡ (((L + pe) + ys) + ce) + R
  s2 = +-right ((L + pe) + ys) R ce
  s3 : (((L + pe) + ys) + ce) + R ≡ (((L + pe) + ce) + ys) + R
  s3 = cong (_+ R) (+-right (L + pe) ys ce)
  s4 : (((L + pe) + ce) + ys) + R ≡ (((L + ce) + pe) + ys) + R
  s4 = cong (λ z → (z + ys) + R) (+-right L pe ce)
  s5 : (((L + ce) + pe) + ys) + R ≡ ((L + (ce + pe)) + ys) + R
  s5 = cong (λ z → (z + ys) + R) (+-assoc L ce pe)
  s6 : ((L + (ce + pe)) + ys) + R ≡ ((L + (env + b)) + ys) + R
  s6 = cong (λ z → ((L + z) + ys) + R) eq
  s7 : ((L + (env + b)) + ys) + R ≡ (((L + env) + b) + ys) + R
  s7 = cong (λ z → (z + ys) + R) (sym (+-assoc L env b))
  s8 : (((L + env) + b) + ys) + R ≡ (((L + env) + ys) + b) + R
  s8 = cong (_+ R) (+-right (L + env) b ys)
  s9 : (((L + env) + ys) + b) + R ≡ (((L + env) + ys) + R) + b
  s9 = +-right ((L + env) + ys) b R
  s10 : (((L + env) + ys) + R) + b ≡ ((L + (env + ys)) + R) + b
  s10 = cong (λ z → (z + R) + b) (+-assoc L env ys)
  s11 : ((L + (env + ys)) + R) + b ≡ (L + ((env + ys) + R)) + b
  s11 = cong (_+ b) (+-assoc L (env + ys) R)

mix∨ : ∀ L pe ys R ce env →
  ce ∨ pe ≡ env →
  ((L ∨ (pe ∨ ys)) ∨ R) ∨ ce ≡ L ∨ ((env ∨ ys) ∨ R)
mix∨ L pe ys R ce env eq =
  trans s1 (trans s2 (trans s3 (trans s4
  (trans s5 (trans s6 (trans s7 s8))))))
  where
  s1 : ((L ∨ (pe ∨ ys)) ∨ R) ∨ ce ≡ (((L ∨ pe) ∨ ys) ∨ R) ∨ ce
  s1 = cong (λ z → (z ∨ R) ∨ ce) (sym (∨-assoc L pe ys))
  s2 : (((L ∨ pe) ∨ ys) ∨ R) ∨ ce ≡ (((L ∨ pe) ∨ ys) ∨ ce) ∨ R
  s2 = or-right ((L ∨ pe) ∨ ys) R ce
  s3 : (((L ∨ pe) ∨ ys) ∨ ce) ∨ R ≡ (((L ∨ pe) ∨ ce) ∨ ys) ∨ R
  s3 = cong (_∨ R) (or-right (L ∨ pe) ys ce)
  s4 : (((L ∨ pe) ∨ ce) ∨ ys) ∨ R ≡ (((L ∨ ce) ∨ pe) ∨ ys) ∨ R
  s4 = cong (λ z → (z ∨ ys) ∨ R) (or-right L pe ce)
  s5 : (((L ∨ ce) ∨ pe) ∨ ys) ∨ R ≡ ((L ∨ (ce ∨ pe)) ∨ ys) ∨ R
  s5 = cong (λ z → (z ∨ ys) ∨ R) (∨-assoc L ce pe)
  s6 : ((L ∨ (ce ∨ pe)) ∨ ys) ∨ R ≡ ((L ∨ env) ∨ ys) ∨ R
  s6 = cong (λ z → ((L ∨ z) ∨ ys) ∨ R) eq
  s7 : ((L ∨ env) ∨ ys) ∨ R ≡ (L ∨ (env ∨ ys)) ∨ R
  s7 = cong (_∨ R) (∨-assoc L env ys)
  s8 : (L ∨ (env ∨ ys)) ∨ R ≡ L ∨ ((env ∨ ys) ∨ R)
  s8 = ∨-assoc L (env ∨ ys) R

hand-bd : ∀ {n} ph rs ce pe → Hand ph rs ce pe →
  Bound n rs → obj ph < n → Bound n ce × Bound n pe
hand-bd _ _ _ _ hn-nil _ _ = bnil , bnil
hand-bd ph _ _ _ (hn-skip h) (bcons lt rest) olt =
  proj₁ ih , bcons lt (proj₂ ih)
  where ih = hand-bd ph _ _ _ h rest olt
hand-bd ph _ _ _ (hn-move _ h) (bcons lt rest) olt =
  bcons lt (proj₁ ih) , bcons olt (proj₂ ih)
  where ih = hand-bd ph _ _ _ h rest olt
hand-bd ph _ _ _ (hn-copy _ h) (bcons lt rest) olt =
  bcons lt (proj₁ ih) , bcons lt (proj₂ ih)
  where ih = hand-bd ph _ _ _ h rest olt

spawn-step : ∀ {m n} h ps i p ps1 (th : Thin m n) (ch : PTm m) (pa : PTm n)
  (env : List Ref) (eth : List Flight) (d dm : List ℕ)
  (ce pe : List Ref) (mv : List (ℕ × ℕ)) →
  WF (sys h ps) →
  lookup ps i ≡ just p →
  ctl p ≡ pr (go (spawn th ch pa) env eth d dm) →
  splitGo zero (placeholder h) th env ≡ just (ce , pe , mv) →
  setProc ps i (pr (go (applyMoves mv pa) pe eth d dm)) ≡ just ps1 →
  WF (sys (snoc h (nat zero))
        (ps1 ++ proc (length ps) ready [] [] (pr (go ch ce [] [] [])) ∷ []))
spawn-step h ps i p ps1 th ch pa env eth d dm ce pe mv wf lk ec sg es =
  finish (set-both i ps p pcode ps1 lk es)
  where
  ph = placeholder h
  h' = snoc h (nat zero)
  ys = flightRefs eth
  pcode = pr (go (applyMoves mv pa) pe eth d dm)
  ccode = pr (go ch ce [] [] [])
  child = proc (length ps) ready [] [] ccode
  psNew = ps1 ++ child ∷ []
  hn = split-hand zero ph th env ce pe mv sg
  oreq = cong ctlRefs ec
  len = length-snoc h (cell (nat zero) live)
  finish : Both ps ps1 p pcode → WF (sys h' psNew)
  finish (both L R eOld eNew rEq) =
    grow-sys {h} {ps} h' psNew (bonus hn) wf bNew countAll hasAll zx
    where
    bAll = proj₁ wf
    bPre = proj₁ (bound-split (preOf h ps) (refsPs ps) bAll)
    bCtlPs = proj₂ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
    bRs = proj₂ (bound-split (preOf h ps) (refsPs ps) bAll)
    bEdge = proj₁ (bound-split (edgeRefs h) (ctlRefsPs ps) bPre)
    bCode = subst (Bound (length h)) oreq (ctlHere h ps i p wf lk)
    bEnv = proj₁ (bound-split env ys bCode)
    bFly = proj₂ (bound-split env ys bCode)
    parts = hand-bd ph env ce pe hn (monoS bEnv) (fresh-< (length h))
    bCe = proj₁ parts
    bPe = proj₂ parts
    bParent = bound-++ bPe (monoS bFly)
    bCtl1 = set-ctl-bound i ps p pcode ps1 lk es (monoS bCtlPs) bParent
    bChild =
      subst (Bound (suc (length h))) (sym (++-identityʳ (ce ++ [])))
        (subst (Bound (suc (length h))) (sym (++-identityʳ ce)) bCe)
    eChild : ctlRefsPs (child ∷ []) ≡ (ce ++ []) ++ []
    eChild = refl
    bCtlNew =
      subst (Bound (suc (length h)))
        (sym (ctlRefsPs-++ ps1 (child ∷ [])))
        (bound-++ bCtl1 (subst (Bound (suc (length h))) (sym eChild) bChild))
    bEdge' = subst (Bound (suc (length h))) (sym (edge-nat h zero)) (monoS bEdge)
    emptyChild : refsPs (child ∷ []) ≡ []
    emptyChild = refl
    rnew : refsPs psNew ≡ refsPs ps
    rnew =
      trans (refsPs-++ ps1 (child ∷ []))
      (trans (cong (refsPs ps1 ++_) emptyChild)
      (trans (++-identityʳ (refsPs ps1)) rEq))
    bRs' = subst (Bound (suc (length h))) (sym rnew) (monoS bRs)
    bSuc = bound-++ (bound-++ bEdge' bCtlNew) bRs'
    bNew = subst (λ n → Bound n (refsOf (sys h' psNew))) (sym len) bSuc
    oldShape : ctlRefsPs ps ≡ L ++ ((env ++ ys) ++ R)
    oldShape = trans eOld (cong (λ c → L ++ (c ++ R)) oreq)
    newShape : ctlRefsPs ps1 ≡ L ++ ((pe ++ ys) ++ R)
    newShape = eNew
    childShape : ctlRefsPs psNew ≡ ctlRefsPs ps1 ++ ((ce ++ []) ++ [])
    childShape = ctlRefsPs-++ ps1 (child ∷ [])
    ceCount : ∀ kq → count kq ce + count kq pe ≡ count kq env + bonus hn kq
    ceCount kq =
      trans (sym (count-++ kq ce pe)) (hand-count hn kq)
    ceHas : ∀ kq → hasG1 kq ce ∨ hasG1 kq pe ≡ hasG1 kq env
    ceHas kq =
      trans (sym (has-++ kq ce pe)) (hand-has hn kq g0-ng)
    pads : ∀ kq → count kq ((ce ++ []) ++ []) ≡ count kq ce
    pads kq = trans (count-pad kq (ce ++ [])) (count-pad kq ce)
    padsH : ∀ kq → hasG1 kq ((ce ++ []) ++ []) ≡ hasG1 kq ce
    padsH kq = trans (has-pad kq (ce ++ [])) (has-pad kq ce)
    splitNew : ∀ kq →
      count kq (L ++ ((pe ++ ys) ++ R)) ≡
      count kq L + ((count kq pe + count kq ys) + count kq R)
    splitNew kq =
      trans (count-++ kq L ((pe ++ ys) ++ R))
      (trans (cong (count kq L +_) (count-++ kq (pe ++ ys) R))
             (cong (count kq L +_) (cong (_+ count kq R) (count-++ kq pe ys))))
    splitOld : ∀ kq →
      count kq (L ++ ((env ++ ys) ++ R)) ≡
      count kq L + ((count kq env + count kq ys) + count kq R)
    splitOld kq =
      trans (count-++ kq L ((env ++ ys) ++ R))
      (trans (cong (count kq L +_) (count-++ kq (env ++ ys) R))
             (cong (count kq L +_) (cong (_+ count kq R) (count-++ kq env ys))))
    opened : ∀ kq →
      (count kq L + ((count kq pe + count kq ys) + count kq R)) + count kq ce ≡
      ((count kq L + (count kq pe + count kq ys)) + count kq R) + count kq ce
    opened kq =
      cong (_+ count kq ce)
           (sym (+-assoc (count kq L) (count kq pe + count kq ys) (count kq R)))
    splitNewH : ∀ kq →
      hasG1 kq (L ++ ((pe ++ ys) ++ R)) ≡
      hasG1 kq L ∨ ((hasG1 kq pe ∨ hasG1 kq ys) ∨ hasG1 kq R)
    splitNewH kq =
      trans (has-++ kq L ((pe ++ ys) ++ R))
      (trans (cong (hasG1 kq L ∨_) (has-++ kq (pe ++ ys) R))
             (cong (hasG1 kq L ∨_) (cong (_∨ hasG1 kq R) (has-++ kq pe ys))))
    splitOldH : ∀ kq →
      hasG1 kq (L ++ ((env ++ ys) ++ R)) ≡
      hasG1 kq L ∨ ((hasG1 kq env ∨ hasG1 kq ys) ∨ hasG1 kq R)
    splitOldH kq =
      trans (has-++ kq L ((env ++ ys) ++ R))
      (trans (cong (hasG1 kq L ∨_) (has-++ kq (env ++ ys) R))
             (cong (hasG1 kq L ∨_) (cong (_∨ hasG1 kq R) (has-++ kq env ys))))
    openedH : ∀ kq →
      (hasG1 kq L ∨ ((hasG1 kq pe ∨ hasG1 kq ys) ∨ hasG1 kq R)) ∨ hasG1 kq ce ≡
      ((hasG1 kq L ∨ (hasG1 kq pe ∨ hasG1 kq ys)) ∨ hasG1 kq R) ∨ hasG1 kq ce
    openedH kq =
      cong (_∨ hasG1 kq ce)
           (sym (∨-assoc (hasG1 kq L) (hasG1 kq pe ∨ hasG1 kq ys) (hasG1 kq R)))
    ctlEq : ∀ kq →
      count kq (ctlRefsPs psNew) ≡ count kq (ctlRefsPs ps) + bonus hn kq
    ctlEq kq =
      trans (cong (count kq) childShape)
      (trans (count-++ kq (ctlRefsPs ps1) ((ce ++ []) ++ []))
      (trans (cong (count kq (ctlRefsPs ps1) +_) (pads kq))
      (trans (cong (_+ count kq ce) (cong (count kq) newShape))
      (trans (cong (_+ count kq ce) (splitNew kq))
      (trans (opened kq)
      (trans (mix (count kq L) (count kq pe) (count kq ys) (count kq R)
                  (count kq ce) (count kq env) (bonus hn kq) (ceCount kq))
      (trans (cong (_+ bonus hn kq) (sym (splitOld kq)))
             (cong (_+ bonus hn kq) (sym (cong (count kq) oldShape))))))))))
    hasEq : ∀ kq → hasG1 kq (ctlRefsPs psNew) ≡ hasG1 kq (ctlRefsPs ps)
    hasEq kq =
      trans (cong (hasG1 kq) childShape)
      (trans (has-++ kq (ctlRefsPs ps1) ((ce ++ []) ++ []))
      (trans (cong (hasG1 kq (ctlRefsPs ps1) ∨_) (padsH kq))
      (trans (cong (_∨ hasG1 kq ce) (cong (hasG1 kq) newShape))
      (trans (cong (_∨ hasG1 kq ce) (splitNewH kq))
      (trans (openedH kq)
      (trans (mix∨ (hasG1 kq L) (hasG1 kq pe) (hasG1 kq ys) (hasG1 kq R)
                   (hasG1 kq ce) (hasG1 kq env) (ceHas kq))
      (trans (sym (splitOldH kq))
             (sym (cong (hasG1 kq) oldShape)))))))))
    countAll : ∀ kq →
      count kq (refsOf (sys h' psNew)) ≡
      count kq (refsOf (sys h ps)) + bonus hn kq
    countAll kq =
      add-ctl kq h h' ps psNew (bonus hn kq)
        (cong (count kq) (edge-nat h zero))
        (ctlEq kq)
        (cong (count kq) rnew)
    hasAll : ∀ kq →
      hasG1 kq (refsOf (sys h' psNew)) ≡ hasG1 kq (refsOf (sys h ps))
    hasAll kq =
      same-has kq h h' ps psNew
        (cong (hasG1 kq) (edge-nat h zero))
        (hasEq kq)
        (cong (hasG1 kq) rnew)
    pre = edgeRefs h ++ L
    aft = (ys ++ R) ++ refsPs ps
    flat : refsOf (sys h ps) ≡ pre ++ (env ++ aft)
    flat =
      trans (cong (λ c → (edgeRefs h ++ c) ++ refsPs ps) oldShape)
      (trans (cong (_++ refsPs ps) (cong (edgeRefs h ++_)
                   (cong (L ++_) (++-assoc env ys R))))
      (trans (cong (_++ refsPs ps) (sym (++-assoc (edgeRefs h) L
                                            (env ++ (ys ++ R)))))
      (trans (++-assoc pre (env ++ (ys ++ R)) (refsPs ps))
             (cong (pre ++_) (++-assoc env (ys ++ R) (refsPs ps))))))
    bReg = subst (Bound (obj ph)) flat bAll
    uReg = subst Grade1Unique flat (proj₂ wf)
    zx : ∀ kq → hasG1 kq (refsOf (sys h ps)) ≡ true → bonus hn kq ≡ 0
    zx kq hf =
      bonus-zero hn kq pre aft bReg g0-ng uReg
        (subst (λ xs → hasG1 kq xs ≡ true) flat hf)

spawn-wf : ∀ h ps i t → WF (sys h ps) → spawn1 (sys h ps) i ≡ just t → WF t
spawn-wf h ps i t wf eq = from (lookup ps i) eq refl
  where
  no : nothing ≡ just t → WF t
  no e = ⊥-elim (nothing≢just e)
  from : (m : Maybe Proc) → spawn1 (sys h ps) i ≡ just t → lookup ps i ≡ m → WF t
  from nothing eqa lk rewrite lk = no eqa
  from (just p) eqa lk = onC (ctl p) eqa lk refl
    where
    onC : (c : Ctl) → spawn1 (sys h ps) i ≡ just t →
          lookup ps i ≡ just p → ctl p ≡ c → WF t
    onC idle eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (ev _ _ _) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (rv _ _ _) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go done _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (send _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (recv _ _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (seq _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (await _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (nignore _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (awaitT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ignoreT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (flushT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ncheckT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (ndemonT _ _) _ _ _ _)) eqc lk0 ec rewrite lk0 | ec = no eqc
    onC (pr (go (spawn th ch pa) env eth d dm)) eqc lk0 ec rewrite lk0 | ec
      with splitGo zero (placeholder h) th env in sg
    ... | nothing = no eqc
    ... | just (ce , pe , mv) = placed (setProc ps i pcode) eqc refl
      where
      pcode = pr (go (applyMoves mv pa) pe eth d dm)
      ccode = pr (go ch ce [] [] [])
      child = proc (length ps) ready [] [] ccode
      placed : (m : Maybe (List Proc)) →
               (m >>= λ ps1 →
                  just (sys (snoc h (nat zero)) (ps1 ++ child ∷ []))) ≡ just t →
               setProc ps i pcode ≡ m → WF t
      placed nothing eql es0 = no eql
      placed (just ps1) refl es0 =
        spawn-step h ps i p ps1 th ch pa env eth d dm ce pe mv wf lk0 ec sg es0

------------------------------------------------------------------------
-- Every v1b step keeps the v1a invariant. Lowering a checked process
-- therefore stays well-formed, and every reference still satisfies
-- the v0 residual invariant.
------------------------------------------------------------------------

pstep-wf : ∀ {s t} → PStep s t → WF s → WF t
pstep-wf (p-lift st) wf = step-preserves-grade1 st wf
pstep-wf (p-spawn {sys h ps} {i} eq) wf = spawn-wf h ps i _ wf eq
pstep-wf (p-emit {sys h ps} {i} eq) wf = emit-wf h ps i _ wf eq
pstep-wf (p-deliver {sys h ps} {i} eq) wf = deliver-wf h ps i _ wf eq
pstep-wf (p-recv {sys h ps} {i} eq) wf = recv-wf h ps i _ wf eq
pstep-wf (p-await {sys h ps} {i} eq) wf = await-wf h ps i _ wf eq
pstep-wf (p-arm {sys h ps} {i} eq) wf = arm-wf h ps i _ wf eq
pstep-wf (p-flush {sys h ps} {i} eq) wf = flush-wf h ps i _ wf eq
pstep-wf (p-npeek {sys h ps} {i} eq) wf = npeek-wf h ps i _ wf eq
pstep-wf (p-ndemon {sys h ps} {i} eq) wf = ndemon-wf h ps i _ wf eq
pstep-wf (p-seq {sys h ps} {i} eq) wf = seq-wf h ps i _ wf eq
pstep-wf (p-bind {sys h ps} {i} eq) wf = bind-wf h ps i _ wf eq
pstep-wf (p-done {sys h ps} {i} eq) wf = done-wf h ps i _ wf eq

psteps : ∀ {s t} → PStep* s t → WF s → WF t
psteps pdone wf = wf
psteps (pmore st later) wf = psteps later (pstep-wf st wf)

spawn-preserves-grade1 : ∀ {s i t} → spawn1 s i ≡ just t → WF s → WF t
spawn-preserves-grade1 {sys h ps} {i} eq wf = spawn-wf h ps i _ wf eq

lowerP-safe : ∀ {p s} → PStep* (lowerP p) s → WF s × AllInv (refsOf s)
lowerP-safe {p} {s} tr = psteps tr (lowerP-wf p) , residual-inv-refs s
