------------------------------------------------------------------------
-- muro-beam v1b, plus the boundary v1 contract.
-- v0 is the tagged parent. v1a lowered GTm. v1c adds adequacy.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam where

open import MuroBeam.Grade public
open import MuroBeam.Heap public
open import MuroBeam.Process public
open import MuroBeam.Collect public
-- Unique defines the same `true≢false` as Collect. Export Collect's.
open import MuroBeam.Unique public hiding (true≢false)
open import MuroBeam.Source public
open import MuroBeam.Lower public
-- Boundary re-exports the names above. Hide the copies so the
-- umbrella keeps a single binding for each v1a theorem.
open import MuroBeam.Boundary public hiding (
    grade0; grade1; gradeω
  ; Kept; iv-kept; isG1; isZeroGrade
  ; kind; Kind; Kmove; Kcopy
  ; spend; spend-finite; spend-ω; spend-iv; Spent; spent
  ; Val; nat; suc↑; clo; Ref; Ordered; checked; spendRef
  ; Sys; alloc; deref; send; anyG1; reuse-ordered; grade0-not-dereferenced
  ; Step; Reach; collect; collect-safe; collect-frees-zero; residual-inv-step
  ; WF; grade1-unique; send-g1-moves
  ; Checked; term
  ; lower; Step*; lower-safe; lower-g0-never-deref
  )
open import MuroBeam.Example public
-- `go` is Collect's traversal. `done`, `send`, and `recv` are the v0
-- machine. The process constructors stay on `MuroBeam.PSyntax`.
open import MuroBeam.PSyntax public hiding (go; done; send; recv; hasTag)
open import MuroBeam.PRun public hiding (hasTag; Split)
open import MuroBeam.PTm public
open import MuroBeam.Stray public
open import MuroBeam.PWf public using
  ( lowerP-safe; spawn-preserves-grade1; pstep-wf; psteps )
open import MuroBeam.PExample public hiding (take)
