------------------------------------------------------------------------
-- checkP, lowerP, and the process-layer safety theorems.
-- Grade decisions go through muro's decide, sat, and checkGrade.
-- No new lattice. No multiplicative application.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.PTm where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; length) renaming ([] to nil; _∷_ to _∷ₗ_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Data.Unit.Base using (⊤; tt)
open import Muro.Base using
  ( run; Result; ok; fail; Use; U0; U1; Uω; _>>=_; _>>_; _orElse_; guard )
open import Muro.Grade using
  ( Grade; g0; g1; gω; gze; Count; finᶜ; many; Point; fin; pt
  ; sat; checkGrade
  ; Pair; gp; Spent; sp; Uses; GCtx
  ; under; hold; addU; oneS; charge; zeros; pcomp )

open import MuroBeam.BTm using
  ( BTm; embed; decideB; lookupIx
  ; gvar; gtyp; glam; gpi; gapp; gmatch )
  renaming (gze to bze; gsu to bsu; gref to bref)

open import MuroBeam.Boundary using (inB?; Cxt; sharpCxt)
open import MuroBeam.Grade using (kind; Kind; Kmove; Kcopy)
open import MuroBeam.Heap using
  ( Obj; Ref; count; Bound; bnil; Grade1Unique; uniq-nil )
open import MuroBeam.Process using
  ( Sys; sys; Proc; proc; ready; Msg; pr; refsOf; AllInv; refs-inv )
open import MuroBeam.PSyntax using
  ( Thin; t[]; keep; skip
  ; PTm; done; send; recv; spawn; seq
  ; await; ignore; nignore
  ; awaitT; ignoreT; flushT; ncheckT; ndemonT
  ; Code; go; Flight; isProtoAt; replyRoot; keptAt )
open import MuroBeam.PRun using (spawn1)
open import MuroBeam.Unique using (WF)

------------------------------------------------------------------------
-- A point saturates its own finite count. g1 therefore passes sat
-- at one. A larger finite point passes sat at that point, and the
-- use vector, not this gate, is what `hold` later discharges.
-- g0 never reaches this gate: `kind` is nothing, and `sat g0 (finᶜ 1)`
-- is the refusal.
------------------------------------------------------------------------

selfSat : Grade → Bool
selfSat (pt (fin n)) = sat (pt (fin n)) (finᶜ n)
selfSat _ = false

sendGate : Grade → Result ⊤
sendGate g with kind g
... | nothing    = guard "erased variable used computationally" (sat g (finᶜ 1))
... | just Kmove = guard "move" (selfSat g)
... | just Kcopy =
  checkGrade run g U0 orElse checkGrade run g U1 orElse checkGrade run g Uω

compOf : Spent → Count
compOf (sp c _) = c

typeOf : Spent → Count
typeOf (sp _ t) = t

isZeroCount : Count → Bool
isZeroCount (finᶜ zero)    = true
isZeroCount (finᶜ (suc _)) = false
isZeroCount many = false

isOneCount : Count → Bool
isOneCount (finᶜ (suc zero)) = true
isOneCount (finᶜ zero)       = false
isOneCount (finᶜ (suc (suc _))) = false
isOneCount many            = false

boundaryOk : ∀ {A : Set} → Dec A → Result ⊤
boundaryOk (yes _) = ok tt
boundaryOk (no _)  = fail "outside the boundary"

comps : ∀ {n} → GCtx n → Cxt n
comps []             = []
comps (gp c _ ∷ Γ)   = c ∷ comps Γ

------------------------------------------------------------------------
-- Thin the context the child sees. keep keeps the grade. skip drops it.
------------------------------------------------------------------------

thinCtx : ∀ {m n} → Thin m n → GCtx n → Result (GCtx m)
thinCtx t[]             []       = ok []
thinCtx (skip th)       (_ ∷ Γ)  = thinCtx th Γ
thinCtx (keep th)       (p ∷ Γ)  = thinCtx th Γ >>= λ Γ' → ok (p ∷ Γ')

-- Same thinning as `thinCtx`, on the recv-origin mask.
thinMask : ∀ {m n} → Thin m n → Vec Bool n → Vec Bool m
thinMask t[]       []       = []
thinMask (skip th) (_ ∷ ρ) = thinMask th ρ
thinMask (keep th) (b ∷ ρ) = b ∷ thinMask th ρ

-- No binder in this context was introduced by `recv`.
falses : ∀ {n} → Vec Bool n
falses {zero}  = []
falses {suc n} = false ∷ falses

-- A kept protocol slot has to move. `markProto` rewrites only the
-- parent root, and only a moved slot. A copy leaves that rewrite
-- with an empty move list, so `checkP` refuses the copy.
-- `isMove` reads the binder grade. That grade is the runtime grade
-- for a `seq` binder and for a context the caller passed in. It is
-- not the runtime grade of a `recv` binder: `recvStep` installs the
-- sender's reference and does not regrade it, and `spawn1` moves by
-- `kind (checked r)`.
isMove : Grade → Bool
isMove g with kind g
... | just Kmove = true
... | _          = false

-- The binder `seq` introduces is g1 exactly when the continuation is
-- a spawn that keeps slot 0 and whose parent root is the protocol.
-- Otherwise the binder stays ω, which is what `send`/`recv` copy.
seqGrade : ∀ {n} → PTm n → Grade
seqGrade k with replyRoot k
... | true  = g1
... | false = gω

-- A protocol name has to be a kept slot. A skipped slot never reaches
-- `slot`, so the guard there cannot see it. A tagged parent is not
-- this catch-all's job: `isProtoAt` is false on a tag, so the catch-all
-- would be true and the move check would not run. `checkP` refuses
-- that spawn before `checkSpawn`. A tag buried under the parent is
-- the same hole on the generic arm. `containsTag` refuses it before
-- `checkSpawn` as well. The tag is an object index, not a slot, so
-- the move, one-computational-use, and zero-type guards cannot run
-- on it.
protoKept : ∀ {m n} → Thin m n → PTm n → Bool
protoKept th (await x _)   = keptAt (toℕ x) th
protoKept th (ignore x _)  = keptAt (toℕ x) th
protoKept th (nignore x _) = keptAt (toℕ x) th
protoKept _ _              = true

-- A protocol consumer at this index is one computational use, and that
-- use is not added to the child's. The parent use at this index has to
-- be exactly that one computational use, and it has to be zero in the
-- type grade. `await` / `ignore` / `nignore` add `charge run`, whose
-- type count is zero. A type use in the continuation, such as
-- `seq (gtyp 0) done` under `await 0`, is in `typeOf u`. Returning the
-- child use `v` would drop it, and the reply binder's type grade is
-- `g0`, so `under` would not see it. Both guards run before that drop.
-- The slot itself must move. `fromRecv` is true when this binder
-- was introduced by `recv`. The annotation can be `g1` while the
-- payload `recvStep` installed is a copy, so `isMove` on that
-- annotation is not a move guarantee. `kind g1` is `Kmove`. The
-- refusal is the checker, not a claim that the payload is not a
-- move. The recv guard on a protocol consumer runs after the move
-- guard: a copied annotation is still `protocol slot is not moved`.
-- A keep that is not a protocol consumer would move or copy by
-- `kind c`. That is the annotation, not `kind (checked r)`, so it
-- is refused before `kind` is read, including at `g1` and at ω.
-- Anything else moved must be quiet in the parent. A copy is held on
-- each side and the parent use remains.
slot : ∀ {n} → ℕ → Bool → Grade → Grade → Spent → Spent → PTm n → Result Spent
slot i fromRecv c t v u tm with isProtoAt i tm
... | true =
  guard "protocol slot is not moved" (isMove c) >>
  guard "protocol slot came from recv" (not fromRecv) >>
  guard "protocol slot is not one computational use" (isOneCount (compOf u)) >>
  guard "protocol slot has a type use" (isZeroCount (typeOf u)) >>
  hold run c t v >>
  ok v
... | false with fromRecv
... | true = fail "kept slot came from recv"
... | false with kind c
... | nothing =
  guard "erased variable used computationally" (sat c (finᶜ 1)) >>
  ok u
... | just Kmove =
  guard "moved" (isZeroCount (compOf u) ∧ isZeroCount (typeOf u)) >>
  hold run c t v >>
  ok v
... | just Kcopy =
  hold run c t v >>
  hold run c t u >>
  ok u

merge : ∀ {m n k} → ℕ → Thin m n → Vec Bool n → GCtx n → Uses m → Uses n → PTm k → Result (Uses n)
merge _ t[]       []           []           []        []       _  = ok []
merge i (skip th) (_ ∷ ρ)      (_ ∷ Γ)      cu        (u ∷ pu) tm =
  merge (suc i) th ρ Γ cu pu tm >>= λ rest → ok (u ∷ rest)
merge i (keep th) (b ∷ ρ)      (gp c t ∷ Γ) (v ∷ cu)  (u ∷ pu) tm =
  slot i b c t v u tm >>= λ w →
  merge (suc i) th ρ Γ cu pu tm >>= λ rest → ok (w ∷ rest)

------------------------------------------------------------------------
-- The checker. `seq` asks `decideB` and `inB?`. A reply root also
-- requires a fresh body. `freshBody` is syntactic: it does not read
-- the heap, so an aliased fresh head is still a checked image.
-- `alias-bind.mbi` loads. `bind-count-refuses` refuses that alias
-- later, when the count is not 1. There is no theorem from
-- `freshBody` to the count.
-- A recv binder is `under`. A send is one computational use, gated by
-- `sat` or `checkGrade`.
--
-- Definitions are checked once, in order. Definition i may mention
-- itself and every earlier definition (`gref` below `suc i`). A later
-- index is `bad gref`. The entry is not a definition: its bound is
-- the length of the table, so it may call every definition and may
-- not call itself under a fresh index.
------------------------------------------------------------------------

checkDef : ℕ → BTm 0 → Result ⊤
checkDef bound d =
  boundaryOk (inB? [] d) >>
  decideB bound run [] d >>= λ _ →
  ok tt

checkDefs : ℕ → List (BTm 0) → Result ⊤
checkDefs _ nil = ok tt
checkDefs i (d ∷ₗ ds) = checkDef (suc i) d >> checkDefs (suc i) ds

-- Join a child use and a parent use. A protocol name that the
-- thinning skipped never reaches `slot`, so it is refused here.
checkSpawn : ∀ {m n} → Thin m n → Vec Bool n → GCtx n → Uses m → Uses n → PTm n → Result (Uses n)
checkSpawn th ρ Γ cu pu pa =
  guard "protocol slot is not moved" (protoKept th pa) >>
  merge zero th ρ Γ cu pu pa

-- A fresh head allocates its result. `gsu` allocates the successor
-- cell even when its argument is an existing pointer. `gvar`, `gapp`,
-- and `gmatch` can return a pointer that is already in scope.
-- `glam` allocates a closure. `evalTm` takes that step only when
-- `not (anyG1 env)`. `guardGlam` refuses a direct `glam` reply body
-- when `sharpCxt` of the context is true, before `inB?`. A `gref`
-- of a `glam` runs under `[]`, so it is not that guard. An ω binder
-- can still hold a runtime `g1` reference; `guardGlam` does not see it.
freshHead : ∀ {n} → BTm n → Bool
freshHead bze           = true
freshHead (bsu _)       = true
freshHead (glam _ _ _)  = true
freshHead (gtyp _)      = true
freshHead (gpi _ _ _)   = true
freshHead _             = false

-- One `gref`, and only to a fresh head. A chain of `gref`s is not fresh.
freshBody : List (BTm 0) → ∀ {n} → BTm n → Bool
freshBody ds (bref k) with lookupIx ds k
... | just d  = freshHead d
... | nothing = false
freshBody _ e = freshHead e

-- Reply roots are the only `seq` continuations whose binder is g1.
-- Anything else may return an alias; `bind1` will not promote it.
guardReply : ∀ {n} → List (BTm 0) → BTm n → PTm (suc n) → Result ⊤
guardReply ds e k with replyRoot k
... | false = ok tt
... | true  = guard "reply result is not fresh" (freshBody ds e)

-- A direct `glam` is evaluated in the caller's environment.
-- `evalTm` refuses that step when `anyG1` is true. A `g1` already
-- in `Γ` is `sharpCxt`. This guard names that reply case. `inB?`
-- refuses the same body. A `gref` is not a direct `glam`.
isGlam : ∀ {n} → BTm n → Bool
isGlam (glam _ _ _)   = true
isGlam (gvar _)       = false
isGlam (gtyp _)       = false
isGlam (gpi _ _ _)    = false
isGlam (gapp _ _)     = false
isGlam bze            = false
isGlam (bsu _)        = false
isGlam (gmatch _ _ _) = false
isGlam (bref _)       = false

guardGlam : ∀ {n} → GCtx n → BTm n → PTm (suc n) → Result ⊤
guardGlam Γ e k with replyRoot k
... | false = ok tt
... | true  = guard "glam reply under g1" (not (isGlam e ∧ sharpCxt (comps Γ)))

-- A tagged constructor anywhere in the term. `awaitT` carries an
-- object index, not a de Bruijn slot, and so do `ignoreT`, `flushT`,
-- `ncheckT`, and `ndemonT`. `isProtoAt` is false on each of them.
containsTag : ∀ {n} → PTm n → Bool
containsTag done             = false
containsTag (send _ _ k)    = containsTag k
containsTag (recv _ _ k)    = containsTag k
containsTag (spawn _ ch pa) = containsTag ch ∨ containsTag pa
containsTag (seq _ _ k)     = containsTag k
containsTag (await _ k)     = containsTag k
containsTag (ignore _ k)    = containsTag k
containsTag (nignore _ k)   = containsTag k
containsTag (awaitT _ _)    = true
containsTag (ignoreT _ _)   = true
containsTag (flushT _ _)    = true
containsTag (ncheckT _ _)   = true
containsTag (ndemonT _ _)   = true

-- `ρ` marks binders introduced by `recv`. `spawn1` moves by the
-- runtime grade of the reference, and `recvStep` does not regrade
-- the sender's reference to this annotation, so a protocol use of
-- a marked slot is `protocol slot came from recv`. A keep that is
-- not a protocol consumer is `kept slot came from recv`. A `seq`
-- binder is unmarked: its grade is `seqGrade`, and a reply root is
-- what `bind1` regrades. The caller's context is unmarked too.
checkGo : ∀ {n} → Vec Bool n → GCtx n → PTm n → Result (Uses n)
checkGo {n} _ Γ done = ok (zeros {n})
checkGo ρ Γ (send _ x k) =
  sendGate (pcomp (lookup Γ x)) >>
  checkGo ρ Γ k >>= λ uk →
  ok (addU (oneS x (charge run)) uk)
checkGo ρ Γ (recv c t k) =
  checkGo (true ∷ ρ) (gp c t ∷ Γ) k >>= λ uk →
  under run c t uk
-- The protocol form is legal only as this spawn parent. Its
-- continuation is checked with `checkGo`, so an untagged protocol
-- buried under the continuation is refused (`protocol is not a spawn
-- reply`). A tag in that continuation is `tagged protocol`. The
-- parent's one computational use is
-- the shape check inside `slot` and is not added again. A further
-- computational use is `protocol slot is not one computational use`.
-- A type use of that slot in the continuation is
-- `protocol slot has a type use`. `slot` refuses both before it
-- returns the child use. A protocol slot marked by `recv` is
-- `protocol slot came from recv` even when the annotation moves.
-- A marked slot whose parent is not a protocol form is
-- `kept slot came from recv`.
checkGo ρ Γ (spawn th ch (await x k)) =
  thinCtx th Γ >>= λ Γ' →
  checkGo (thinMask th ρ) Γ' ch >>= λ cu →
  checkGo ρ Γ k >>= λ uk →
  checkSpawn th ρ Γ cu (addU (oneS x (charge run)) uk) (await x k)
checkGo ρ Γ (spawn th ch (ignore x k)) =
  thinCtx th Γ >>= λ Γ' →
  checkGo (thinMask th ρ) Γ' ch >>= λ cu →
  checkGo ρ Γ k >>= λ uk →
  checkSpawn th ρ Γ cu (addU (oneS x (charge run)) uk) (ignore x k)
checkGo ρ Γ (spawn th ch (nignore x k)) =
  thinCtx th Γ >>= λ Γ' →
  checkGo (thinMask th ρ) Γ' ch >>= λ cu →
  checkGo ρ Γ k >>= λ uk →
  checkSpawn th ρ Γ cu (addU (oneS x (charge run)) uk) (nignore x k)
-- A tagged parent is what `markProto`, `arm1`, and `npeek1` write
-- after a move. `isProtoAt` does not see it, and `protoKept`'s
-- catch-all is true, so the generic arm would skip the move,
-- one-computational-use, and zero-type checks. Refuse it here.
-- Surface syntax has no tagged constructor, so `load` never builds
-- these five. `spawnTagAwait-no` and the four sibling pins are the
-- hand-built equations. `tagged-spawn.mbi` is the parse refusal
-- `not surface` for an `awaitT` parent. It is not this equation.
checkGo _ _ (spawn _ _ (awaitT _ _))  = fail "tagged spawn parent"
checkGo _ _ (spawn _ _ (ignoreT _ _)) = fail "tagged spawn parent"
checkGo _ _ (spawn _ _ (flushT _ _))  = fail "tagged spawn parent"
checkGo _ _ (spawn _ _ (ncheckT _ _)) = fail "tagged spawn parent"
checkGo _ _ (spawn _ _ (ndemonT _ _)) = fail "tagged spawn parent"
-- A tag under this parent is not a protocol root. `isProtoAt` is
-- false on `seq`, `send`, `recv`, `spawn`, `await`, `ignore`, and
-- `nignore`, and on every tagged constructor, so `slot` would
-- skip the move, one-computational-use, and zero-type guards.
-- `containsTag` walks each of those continuations. Refuse before
-- that merge. The tag clauses below are the refusal when the tagged
-- form itself is what `checkGo` is called on. A tag in the
-- continuation of a protocol `await`, `ignore`, or `nignore` is
-- this function on that continuation, not the `containsTag` guard.
checkGo ρ Γ (spawn th ch pa) =
  guard "tagged protocol" (not (containsTag pa)) >>
  thinCtx th Γ >>= λ Γ' →
  checkGo (thinMask th ρ) Γ' ch >>= λ cu →
  checkGo ρ Γ pa >>= λ pu →
  checkSpawn th ρ Γ cu pu pa
checkGo ρ Γ (seq ds e k) =
  checkDefs zero ds >>= λ _ →
  guardGlam Γ e k >>= λ _ →
  boundaryOk (inB? (comps Γ) e) >>= λ _ →
  decideB (length ds) run Γ e >>= λ eu →
  guardReply ds e k >>= λ _ →
  checkGo (false ∷ ρ) (gp (seqGrade k) g0 ∷ Γ) k >>= λ uk →
  under run (seqGrade k) g0 uk >>= λ ku →
  ok (addU eu ku)
checkGo _ _ (await _ _)   = fail "protocol is not a spawn reply"
checkGo _ _ (ignore _ _)  = fail "protocol is not a spawn reply"
checkGo _ _ (nignore _ _) = fail "protocol is not a spawn reply"
-- Surface syntax has no tagged constructor (`SPtm`, `toP`), so `load`
-- never builds these five. A hand-built tag that is not the direct
-- spawn parent used to be accepted: the old clause was `replyTok`,
-- `sat g1 (finᶜ 1)`, which holds, and then the continuation.
-- Promotion does not need that acceptance. `markProto` writes
-- `awaitT`, `ignoreT`, and `ncheckT` after the move. `arm1` writes
-- `flushT`. `npeek1` writes `ndemonT` when the mailbox does not hold
-- the tag. Those runtime terms are not passed to `checkP` again.
-- There is no theorem from `checkP` or `load` to that promotion.
-- Parse refuses the words with `not surface`. `tagAwait-no` and the
-- four siblings are the hand-built equations, not a load of a file.
checkGo _ _ (awaitT _ _)  = fail "tagged protocol"
checkGo _ _ (ignoreT _ _) = fail "tagged protocol"
checkGo _ _ (flushT _ _)  = fail "tagged protocol"
checkGo _ _ (ncheckT _ _) = fail "tagged protocol"
checkGo _ _ (ndemonT _ _) = fail "tagged protocol"

-- The mask starts false. Grades in the caller's context are not
-- `recv` annotations.
checkP : ∀ {n} → GCtx n → PTm n → Result (Uses n)
checkP Γ p = checkGo falses Γ p

------------------------------------------------------------------------
-- Lowering. One process, empty heap, the checked program in `pr`.
------------------------------------------------------------------------

record CheckedP : Set where
  constructor checkedP
  field
    prog : PTm 0
    okp  : checkP [] prog ≡ ok []

lowerP : CheckedP → Sys
lowerP p =
  sys (nil {A = Obj})
    (proc zero ready (nil {A = Ref}) (nil {A = Msg})
       (pr (go (CheckedP.prog p)
             (nil {A = Ref}) (nil {A = Flight})
             (nil {A = ℕ}) (nil {A = ℕ})))
     ∷ₗ nil {A = Proc})

lowerP-refs : ∀ p → refsOf (lowerP p) ≡ nil {A = Ref}
lowerP-refs p = refl

lowerP-wf : ∀ p → WF (lowerP p)
lowerP-wf p = bnil , uniq-nil

-- Same strength as send-preserves-residual. Every Ref carries Kept.
spawn-preserves-residual : ∀ {s i t} →
  spawn1 s i ≡ just t →
  AllInv (refsOf t)
spawn-preserves-residual _ = refs-inv _

------------------------------------------------------------------------
-- Open programs the traces run. The use that remains is the child's
-- single send of the grade-1 slot. `hold` discharged it; the parent
-- protocol use is the shape check and is not added again.
------------------------------------------------------------------------

g1ctx : GCtx 1
g1ctx = gp g1 g0 ∷ []

ignoreProg : PTm 1
ignoreProg = spawn (keep t[]) (send zero fzero (done {1})) (ignore fzero (done {1}))

ignore-checks : checkP g1ctx ignoreProg ≡ ok (sp (finᶜ 1) (finᶜ 0) ∷ [])
ignore-checks = refl

roundProg : PTm 1
roundProg = spawn (keep t[]) (send zero fzero (done {1})) (recv gω g0 (done {2}))

round-checks : checkP g1ctx roundProg ≡ ok (sp (finᶜ 1) (finᶜ 0) ∷ [])
round-checks = refl

closedSeq : PTm 0
closedSeq = seq nil (embed gze) (done {1})

closed-checks : checkP [] closedSeq ≡ ok []
closed-checks = refl

-- Closed programs a `.mbi` entry can name. A file starts at scope 0,
-- so these are `PTm 0`. `spawn t[]` of `done` is the same program as
-- `twoTm` in `MuroBeam.SchedThm`. The send copies the ω nat `seq`
-- binds, because the continuation is `recv`, not a reply root.
-- A bare `await`, `ignore`, or `nignore` is refused. A `g0` recv
-- binder does not send.

spawnClosed : PTm 0
spawnClosed = spawn t[] (done {0}) (done {0})

spawnClosed-ok : checkP [] spawnClosed ≡ ok []
spawnClosed-ok = refl

doneClosed : PTm 0
doneClosed = done {0}

doneClosed-ok : checkP [] doneClosed ≡ ok []
doneClosed-ok = refl

nat2 : BTm 0
nat2 = bsu (bsu bze)

sendRecv : PTm 0
sendRecv =
  seq nil nat2
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (recv gω g0 (done {2})))

sendRecv-ok : checkP [] sendRecv ≡ ok []
sendRecv-ok = refl

awaitClosed : PTm 0
awaitClosed = seq nil bze (await fzero (done {1}))

-- A bare consumer is not a spawn parent, so the binder is not a reply.
awaitClosed-no : checkP [] awaitClosed ≡ fail "protocol is not a spawn reply"
awaitClosed-no = refl

ignoreClosed : PTm 0
ignoreClosed = seq nil bze (ignore fzero (done {1}))

ignoreClosed-no : checkP [] ignoreClosed ≡ fail "protocol is not a spawn reply"
ignoreClosed-no = refl

nignoreClosed : PTm 0
nignoreClosed = seq nil bze (nignore fzero (done {1}))

nignoreClosed-no : checkP [] nignoreClosed ≡ fail "protocol is not a spawn reply"
nignoreClosed-no = refl

defSpawn : PTm 0
defSpawn =
  seq (bze ∷ₗ nil) (bref zero)
    (spawn (skip t[]) (done {0}) (done {1}))

defSpawn-ok : checkP [] defSpawn ≡ ok []
defSpawn-ok = refl

-- The continuation is a spawn that keeps slot 0 and awaits or ignores
-- it, so `seq` binds that slot at g1. `spawn` moves it. A skipped
-- protocol slot, a copied protocol slot, and a protocol buried under
-- `seq` are refused: they would not be rewritten.

spawnIgnore : PTm 0
spawnIgnore =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (ignore fzero (done {1})))

spawnIgnore-ok : checkP [] spawnIgnore ≡ ok []
spawnIgnore-ok = refl

spawnAwait : PTm 0
spawnAwait =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

spawnAwait-ok : checkP [] spawnAwait ≡ ok []
spawnAwait-ok = refl

g0send : PTm 0
g0send = seq nil bze (recv g0 g0 (send zero fzero (done {2})))

g0send-no : checkP [] g0send ≡ fail "erased variable used computationally"
g0send-no = refl

skipAwait : PTm 0
skipAwait =
  seq nil bze
    (spawn (skip t[])
      (done {0})
      (await fzero (done {1})))

skipAwait-no : checkP [] skipAwait ≡ fail "protocol slot is not moved"
skipAwait-no = refl

ωctx : GCtx 1
ωctx = gp gω g0 ∷ []

copyAwait : PTm 1
copyAwait =
  spawn (keep t[])
    (send zero fzero (done {1}))
    (await fzero (done {1}))

copyAwait-no : checkP ωctx copyAwait ≡ fail "protocol slot is not moved"
copyAwait-no = refl

buriedAwait : PTm 0
buriedAwait =
  spawn t[]
    (done {0})
    (seq nil bze (await fzero (done {1})))

buriedAwait-no : checkP [] buriedAwait ≡ fail "protocol is not a spawn reply"
buriedAwait-no = refl

-- The same copied slot, closed: the ω binder is a `recv`, not an open context.
copyClosed : PTm 0
copyClosed =
  recv gω g0
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

copyClosed-no : checkP [] copyClosed ≡ fail "protocol slot is not moved"
copyClosed-no = refl

-- Naive ignore at a spawn parent. The binder is g1. The body is fresh.
spawnNignore : PTm 0
spawnNignore =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (nignore fzero (done {1})))

spawnNignore-ok : checkP [] spawnNignore ≡ ok []
spawnNignore-ok = refl

-- A `gref` whose definition is itself a fresh head is a fresh body.
grefAwait : PTm 0
grefAwait =
  seq (bze ∷ₗ nil) (bref zero)
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

grefAwait-ok : checkP [] grefAwait ≡ ok []
grefAwait-ok = refl

-- Application can return a pointer the closure still holds. That is
-- not a fresh cell, so a reply root is refused before `bind1`.
aliasAwait : PTm 0
aliasAwait =
  seq nil
    (gapp
      (glam gω g0
        (gapp
          (glam gω g0 (gvar (fsuc fzero)))
          (gvar fzero)))
      (bsu bze))
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

aliasAwait-no : checkP [] aliasAwait ≡ fail "reply result is not fresh"
aliasAwait-no = refl

-- The same refusal for the other non-fresh heads. `gmatch` and a
-- `gref` chain are closed. `gvar` needs a binder, so the entry is a
-- `recv` and the body names that slot. These are the programs in
-- `gmatch-await.mbi`, `gvar-await.mbi`, and `gref-chain.mbi`.
gmatchAwait : PTm 0
gmatchAwait =
  seq nil (gmatch bze bze (gvar fzero))
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

gmatchAwait-no : checkP [] gmatchAwait ≡ fail "reply result is not fresh"
gmatchAwait-no = refl

gvarAwait : PTm 0
gvarAwait =
  recv gω g0
    (seq nil (gvar fzero)
      (spawn (keep (skip t[]))
        (send zero fzero (done {1}))
        (await fzero (done {2}))))

gvarAwait-no : checkP [] gvarAwait ≡ fail "reply result is not fresh"
gvarAwait-no = refl

-- Definition 0 is `gze`. Definition 1 is a `gref` to it. The entry
-- `gref`s definition 1, so `freshBody` sees a `gref`, not a fresh head.
grefChain : PTm 0
grefChain =
  seq (bze ∷ₗ bref zero ∷ₗ nil) (bref (suc zero))
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

grefChain-no : checkP [] grefChain ≡ fail "reply result is not fresh"
grefChain-no = refl

-- A direct `glam` reply under a prior `g1` binder. `evalTm` would
-- refuse the closure (`anyG1`). `guardGlam` refuses it at `checkP`.
-- The file is `examples/images/glam-g1.mbi`.
glamG1 : PTm 0
glamG1 =
  recv g1 g0
    (seq nil (glam gω g0 bze)
      (spawn (keep (skip t[]))
        (send zero fzero (done {1}))
        (await fzero (done {2}))))

glamG1-no : checkP [] glamG1 ≡ fail "glam reply under g1"
glamG1-no = refl

-- Direct `glam` at scope 0. No `g1` is in scope, so `guardGlam`
-- allows it. The file is `examples/images/glam-reply.mbi`. The
-- payload is a closure. `drive` does not keep it as a nat.
glamReply : PTm 0
glamReply =
  seq nil (glam gω g0 bze)
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

glamReply-ok : checkP [] glamReply ≡ ok []
glamReply-ok = refl

-- Direct `gpi`. `evalTm` ignores the body and allocates nat zero.
-- The body is a successor, so that zero is not the body. The file
-- is `examples/images/gpi-reply.mbi`.
gpiReply : PTm 0
gpiReply =
  seq nil (gpi gω g0 (bsu bze))
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

gpiReply-ok : checkP [] gpiReply ≡ ok []
gpiReply-ok = refl

-- `(gtyp 0)` needs a binder whose type grade allows one use. A `seq`
-- binder is type grade 0, which is `type grade 0 does not allow 1 uses`.
-- The child sends a closure, not a nat. `drive` keeps the first
-- delivered nat, and `readNat` of a closure is nothing, so the kept
-- nat is the cell `evalTm` allocates for `gtyp`. A child that sent
-- `gsu gze` would keep that successor instead. The closure body is a
-- successor and is not evaluated. The file is `examples/images/gtyp-reply.mbi`.
gtypReply : PTm 0
gtypReply =
  spawn t[]
    (seq nil (glam gω g0 (bsu bze))
      (send zero fzero (done {1})))
    (recv gω gω
      (seq nil (gtyp fzero)
        (spawn (keep (skip t[]))
          (send zero fzero (done {1}))
          (await fzero (done {2})))))

gtypReply-ok : checkP [] gtypReply ≡ ok []
gtypReply-ok = refl

-- `seq (gvar 0) done` under `await 0`. Index 0 is the reply binder.
-- `await` already contributes one computational use (`charge run`).
-- `gvar` records a second. `isOneCount` refuses that count before
-- `slot` returns the child use. `compIgnore` and `compNignore` are
-- the same shape with `ignore` and `nignore`. The files are
-- `comp-await.mbi`, `comp-ignore.mbi`, and `comp-nignore.mbi`.
compAwait : PTm 0
compAwait =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero
        (seq nil (gvar fzero) (done {2}))))

compAwait-no :
  checkP [] compAwait ≡ fail "protocol slot is not one computational use"
compAwait-no = refl

compIgnore : PTm 0
compIgnore =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (ignore fzero
        (seq nil (gvar fzero) (done {2}))))

compIgnore-no :
  checkP [] compIgnore ≡ fail "protocol slot is not one computational use"
compIgnore-no = refl

compNignore : PTm 0
compNignore =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (nignore fzero
        (seq nil (gvar fzero) (done {2}))))

compNignore-no :
  checkP [] compNignore ≡ fail "protocol slot is not one computational use"
compNignore-no = refl

-- `seq (gtyp 0) done` under `await 0`. Index 0 is the reply binder,
-- whose type grade is `g0`. `gtyp` records one type use. `slot` must
-- refuse that use. Dropping the parent use would let `under` accept
-- the binder. `typeIgnore` and `typeNignore` are the same shape with
-- `ignore` and `nignore`. The files are `type-await.mbi`,
-- `type-ignore.mbi`, and `type-nignore.mbi`.
typeAwait : PTm 0
typeAwait =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero
        (seq nil (gtyp fzero) (done {2}))))

typeAwait-no : checkP [] typeAwait ≡ fail "protocol slot has a type use"
typeAwait-no = refl

typeIgnore : PTm 0
typeIgnore =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (ignore fzero
        (seq nil (gtyp fzero) (done {2}))))

typeIgnore-no : checkP [] typeIgnore ≡ fail "protocol slot has a type use"
typeIgnore-no = refl

typeNignore : PTm 0
typeNignore =
  seq nil bze
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (nignore fzero
        (seq nil (gtyp fzero) (done {2}))))

typeNignore-no : checkP [] typeNignore ≡ fail "protocol slot has a type use"
typeNignore-no = refl

-- A spawn whose parent is already tagged. The slot guards do not
-- match these heads. `load` does not build them: parse refuses the
-- word. `tagged-spawn.mbi` is an `awaitT` parent and is `not surface`.
-- These five equations are hand-built terms, not a load of that file.
spawnTagAwait : PTm 0
spawnTagAwait = spawn t[] (done {0}) (awaitT zero (done {0}))

spawnTagAwait-no :
  checkP [] spawnTagAwait ≡ fail "tagged spawn parent"
spawnTagAwait-no = refl

spawnTagIgnore : PTm 0
spawnTagIgnore = spawn t[] (done {0}) (ignoreT zero (done {0}))

spawnTagIgnore-no :
  checkP [] spawnTagIgnore ≡ fail "tagged spawn parent"
spawnTagIgnore-no = refl

spawnTagFlush : PTm 0
spawnTagFlush = spawn t[] (done {0}) (flushT zero (done {0}))

spawnTagFlush-no :
  checkP [] spawnTagFlush ≡ fail "tagged spawn parent"
spawnTagFlush-no = refl

spawnTagNcheck : PTm 0
spawnTagNcheck = spawn t[] (done {0}) (ncheckT zero (done {0}))

spawnTagNcheck-no :
  checkP [] spawnTagNcheck ≡ fail "tagged spawn parent"
spawnTagNcheck-no = refl

spawnTagNdemon : PTm 0
spawnTagNdemon = spawn t[] (done {0}) (ndemonT zero (done {0}))

spawnTagNdemon-no :
  checkP [] spawnTagNdemon ≡ fail "tagged spawn parent"
spawnTagNdemon-no = refl

-- A tagged form that is not a spawn parent. The old clause accepted
-- it (`replyTok`). Promotion does not re-run `checkP`, so the
-- acceptance is not required. Parse refuses the word with
-- `not surface`. These five equations are hand-built terms.
tagAwait : PTm 0
tagAwait = awaitT zero (done {0})

tagAwait-no : checkP [] tagAwait ≡ fail "tagged protocol"
tagAwait-no = refl

tagIgnore : PTm 0
tagIgnore = ignoreT zero (done {0})

tagIgnore-no : checkP [] tagIgnore ≡ fail "tagged protocol"
tagIgnore-no = refl

tagFlush : PTm 0
tagFlush = flushT zero (done {0})

tagFlush-no : checkP [] tagFlush ≡ fail "tagged protocol"
tagFlush-no = refl

tagNcheck : PTm 0
tagNcheck = ncheckT zero (done {0})

tagNcheck-no : checkP [] tagNcheck ≡ fail "tagged protocol"
tagNcheck-no = refl

tagNdemon : PTm 0
tagNdemon = ndemonT zero (done {0})

tagNdemon-no : checkP [] tagNdemon ≡ fail "tagged protocol"
tagNdemon-no = refl

-- `seq` of a tag, as the spawn parent. This is not a protocol root,
-- so it used to take the generic arm and skip the slot guards.
-- `containsTag` refuses it first. The files `buried-awaitT.mbi` and
-- its four siblings are the parse refusal `not surface`. These
-- equations are not a load of those files.
buriedTagAwait : PTm 0
buriedTagAwait =
  spawn t[] (done {0})
    (seq nil bze (awaitT zero (done {1})))

buriedTagAwait-no :
  checkP [] buriedTagAwait ≡ fail "tagged protocol"
buriedTagAwait-no = refl

buriedTagIgnore : PTm 0
buriedTagIgnore =
  spawn t[] (done {0})
    (seq nil bze (ignoreT zero (done {1})))

buriedTagIgnore-no :
  checkP [] buriedTagIgnore ≡ fail "tagged protocol"
buriedTagIgnore-no = refl

buriedTagFlush : PTm 0
buriedTagFlush =
  spawn t[] (done {0})
    (seq nil bze (flushT zero (done {1})))

buriedTagFlush-no :
  checkP [] buriedTagFlush ≡ fail "tagged protocol"
buriedTagFlush-no = refl

buriedTagNcheck : PTm 0
buriedTagNcheck =
  spawn t[] (done {0})
    (seq nil bze (ncheckT zero (done {1})))

buriedTagNcheck-no :
  checkP [] buriedTagNcheck ≡ fail "tagged protocol"
buriedTagNcheck-no = refl

buriedTagNdemon : PTm 0
buriedTagNdemon =
  spawn t[] (done {0})
    (seq nil bze (ndemonT zero (done {1})))

buriedTagNdemon-no :
  checkP [] buriedTagNdemon ≡ fail "tagged protocol"
buriedTagNdemon-no = refl

-- `containsTag` walks `send`, `recv`, `spawn`, `await`, `ignore`,
-- and `nignore`, not only `seq`. These parents are not protocol
-- roots, so the generic arm runs that guard and does not merge.
-- The outer `seq` in `sendTagAwait` only puts a slot in scope.

sendTagAwait : PTm 0
sendTagAwait =
  seq nil bze
    (spawn (skip t[]) (done {0})
      (send zero fzero (awaitT zero (done {1}))))

sendTagAwait-no : checkP [] sendTagAwait ≡ fail "tagged protocol"
sendTagAwait-no = refl

recvTagAwait : PTm 0
recvTagAwait =
  spawn t[] (done {0})
    (recv gω g0 (awaitT zero (done {1})))

recvTagAwait-no : checkP [] recvTagAwait ≡ fail "tagged protocol"
recvTagAwait-no = refl

spawnTagBuried : PTm 0
spawnTagBuried =
  spawn t[] (done {0})
    (spawn t[] (done {0}) (awaitT zero (done {0})))

spawnTagBuried-no : checkP [] spawnTagBuried ≡ fail "tagged protocol"
spawnTagBuried-no = refl

-- The `await` is under `recv`, so it is not the spawn parent root.
-- `containsTag` walks `recv`, then `await`.
awaitUnderRecv : PTm 0
awaitUnderRecv =
  spawn t[] (done {0})
    (recv gω g0
      (await fzero (awaitT zero (done {1}))))

awaitUnderRecv-no : checkP [] awaitUnderRecv ≡ fail "tagged protocol"
awaitUnderRecv-no = refl

ignoreUnderRecv : PTm 0
ignoreUnderRecv =
  spawn t[] (done {0})
    (recv gω g0
      (ignore fzero (awaitT zero (done {1}))))

ignoreUnderRecv-no : checkP [] ignoreUnderRecv ≡ fail "tagged protocol"
ignoreUnderRecv-no = refl

nignoreUnderRecv : PTm 0
nignoreUnderRecv =
  spawn t[] (done {0})
    (recv gω g0
      (nignore fzero (awaitT zero (done {1}))))

nignoreUnderRecv-no : checkP [] nignoreUnderRecv ≡ fail "tagged protocol"
nignoreUnderRecv-no = refl

-- A tag in the continuation of a protocol consumer. This is the
-- special arm: `checkGo` of that continuation hits the tag clause.
-- It does not call `containsTag`.
awaitContTag : PTm 0
awaitContTag =
  seq nil bze
    (spawn (keep t[]) (done {1})
      (await fzero (awaitT zero (done {1}))))

awaitContTag-no : checkP [] awaitContTag ≡ fail "tagged protocol"
awaitContTag-no = refl

ignoreContTag : PTm 0
ignoreContTag =
  seq nil bze
    (spawn (keep t[]) (done {1})
      (ignore fzero (awaitT zero (done {1}))))

ignoreContTag-no : checkP [] ignoreContTag ≡ fail "tagged protocol"
ignoreContTag-no = refl

nignoreContTag : PTm 0
nignoreContTag =
  seq nil bze
    (spawn (keep t[]) (done {1})
      (nignore fzero (awaitT zero (done {1}))))

nignoreContTag-no : checkP [] nignoreContTag ≡ fail "tagged protocol"
nignoreContTag-no = refl

-- The child binds `(gsu gze)` at ω, because the continuation is
-- `send`, not a reply root, and sends that cell with `Kcopy`.
-- The parent `recv` annotates the binder `g1`. `recvStep` installs
-- the sender's reference and does not regrade it. For this payload
-- `spawn1` copies, the move list is empty, and the parent `await`
-- stays untagged, so `await1` does not match it. A payload whose
-- checked grade is `Kmove` is not this term: `spawn1` would move
-- that reference. There is no theorem that the annotation is the
-- payload's kind. `checkP` refuses the protocol use.
-- `recv-move.mbi` is this program. `recv-move-ignore.mbi` and
-- `recv-move-nignore.mbi` are the same guard. `recv-move-shift.mbi`
-- awaits the `recv` binder at index 1, under a later `seq`.
recvMoveAwait : PTm 0
recvMoveAwait =
  spawn t[]
    (seq nil (bsu bze) (send zero fzero (done {1})))
    (recv g1 g0
      (spawn (keep t[])
        (send zero fzero (done {1}))
        (await fzero (done {1}))))

recvMoveAwait-no :
  checkP [] recvMoveAwait ≡ fail "protocol slot came from recv"
recvMoveAwait-no = refl

recvMoveIgnore : PTm 0
recvMoveIgnore =
  spawn t[]
    (seq nil (bsu bze) (send zero fzero (done {1})))
    (recv g1 g0
      (spawn (keep t[])
        (send zero fzero (done {1}))
        (ignore fzero (done {1}))))

recvMoveIgnore-no :
  checkP [] recvMoveIgnore ≡ fail "protocol slot came from recv"
recvMoveIgnore-no = refl

recvMoveNignore : PTm 0
recvMoveNignore =
  spawn t[]
    (seq nil (bsu bze) (send zero fzero (done {1})))
    (recv g1 g0
      (spawn (keep t[])
        (send zero fzero (done {1}))
        (nignore fzero (done {1}))))

recvMoveNignore-no :
  checkP [] recvMoveNignore ≡ fail "protocol slot came from recv"
recvMoveNignore-no = refl

recvMoveShift : PTm 0
recvMoveShift =
  recv g1 g0
    (seq nil bze
      (spawn (skip (keep t[]))
        (send zero fzero (done {1}))
        (await (fsuc fzero) (done {2}))))

recvMoveShift-no :
  checkP [] recvMoveShift ≡ fail "protocol slot came from recv"
recvMoveShift-no = refl

-- Parent is `done`, so `isProtoAt` is false. The annotation is `g1`
-- (`kind g1` is `Kmove`) and the child sends the slot once, so the
-- old `kind` branch accepted the keep. The sender binds `(gsu gze)`
-- at ω and sends `Kcopy`. `spawn1` would copy that payload. The
-- guard runs before `kind`, so this is not a theorem that the
-- grades differ. `recv-keep.mbi` is this program.
recvKeep : PTm 0
recvKeep =
  spawn t[]
    (seq nil (bsu bze) (send zero fzero (done {1})))
    (recv g1 g0
      (spawn (keep t[])
        (send zero fzero (done {1}))
        (done {1})))

recvKeep-no :
  checkP [] recvKeep ≡ fail "kept slot came from recv"
recvKeep-no = refl

-- The annotation is ω, so `kind` is `Kcopy`, and the parent is
-- `done`. One send in the child is a use ω accepts, so the old copy
-- branch accepted the keep. `spawn1` would still move a payload
-- whose checked grade is `Kmove`. `recv-keep-copy.mbi` is this
-- program. Same refusal, still not a grade theorem.
recvKeepCopy : PTm 0
recvKeepCopy =
  recv gω g0
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (done {1}))

recvKeepCopy-no :
  checkP [] recvKeepCopy ≡ fail "kept slot came from recv"
recvKeepCopy-no = refl

-- A nested `seq` does not inherit the root definition list.
-- `(gref 0)` in the inner body is out of that empty bound.
-- The file is `examples/images/nested-seq.mbi`.
nestedSeq : PTm 0
nestedSeq =
  seq (bze ∷ₗ nil) bze
    (seq nil (bref zero) (done {2}))

nestedSeq-no : checkP [] nestedSeq ≡ fail "bad gref"
nestedSeq-no = refl

-- Fresh `gsu`. `load` accepts it and `drive` promotes the successor.
-- The file is `examples/images/alias-bind.mbi`. The plant that
-- refuses an alias of this shape is `alias-bind-plant`, on the
-- file's text, not this `checkP` pin.
aliasBind : PTm 0
aliasBind =
  seq nil (bsu bze)
    (spawn (keep t[])
      (send zero fzero (done {1}))
      (await fzero (done {1})))

aliasBind-ok : checkP [] aliasBind ≡ ok []
aliasBind-ok = refl

------------------------------------------------------------------------
-- An accepted reply `seq` has a fresh body. `guardGlam` sits before
-- `inB?`, and `guardReply` sits after `decideB`, so peeling those
-- binds reaches the fresh-body guard. `replyRoot` is already `true`,
-- so `guardGlam` is the boolean guard. `decideB` does not have to reduce.
------------------------------------------------------------------------

ok-bind : ∀ {A B : Set} {r : Result A} {f : A → Result B} {y : B} →
  (r >>= f) ≡ ok y → ∃ λ x → f x ≡ ok y
ok-bind {r = ok x} eq = x , eq
ok-bind {r = fail _} ()

guard-ok : ∀ {A : Set} {msg} {b : Bool} {f : ⊤ → Result A} {y : A} →
  (guard msg b >>= f) ≡ ok y → b ≡ true
guard-ok {b = true} _ = refl
guard-ok {b = false} ()

seq-reply-fresh : ∀ {n} (Γ : GCtx n) ds e k uk →
  replyRoot k ≡ true →
  checkP Γ (seq ds e k) ≡ ok uk →
  freshBody ds e ≡ true
seq-reply-fresh Γ ds e k uk rr eq rewrite rr
  with checkDefs zero ds
... | fail msg = stuck eq
  where
  stuck : ∀ {A : Set} → fail msg ≡ ok uk → A
  stuck ()
... | ok _
  with not (isGlam e ∧ sharpCxt (comps Γ))
... | false = stuck eq
  where
  stuck : ∀ {A : Set} → fail "glam reply under g1" ≡ ok uk → A
  stuck ()
... | true
  with boundaryOk (inB? (comps Γ) e)
... | fail msg = stuck eq
  where
  stuck : ∀ {A : Set} → fail msg ≡ ok uk → A
  stuck ()
... | ok _
  with decideB (length ds) run Γ e
... | fail msg = stuck eq
  where
  stuck : ∀ {A : Set} → fail msg ≡ ok uk → A
  stuck ()
... | ok _
  with freshBody ds e
... | true = refl
... | false = stuck eq
  where
  stuck : ∀ {A : Set} → fail "reply result is not fresh" ≡ ok uk → A
  stuck ()
