------------------------------------------------------------------------
-- muro-beam v1a. The book is the modules imported below.
-- v0 is the tagged parent. v1b adds spawn; v1c adds adequacy.
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
open import MuroBeam.Example public
