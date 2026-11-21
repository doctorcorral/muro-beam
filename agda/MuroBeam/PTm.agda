------------------------------------------------------------------------
-- checkP, lowerP, and the process-layer safety theorems.
-- Grade decisions go through muro's decide, sat, and checkGrade.
-- No new lattice. No multiplicative application.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.PTm where

open import Data.Bool.Base using (Bool; true; false; not; _∧_)
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

replyTok : Result ⊤
replyTok = guard "reply" (sat g1 (finᶜ 1))

------------------------------------------------------------------------
-- Thin the context the child sees. keep keeps the grade. skip drops it.
------------------------------------------------------------------------

thinCtx : ∀ {m n} → Thin m n → GCtx n → Result (GCtx m)
thinCtx t[]             []       = ok []
thinCtx (skip th)       (_ ∷ Γ)  = thinCtx th Γ
thinCtx (keep th)       (p ∷ Γ)  = thinCtx th Γ >>= λ Γ' → ok (p ∷ Γ')

-- A kept protocol slot has to move. `markProto` rewrites only the
-- parent root, and only a moved slot. A copy leaves that rewrite
-- with an empty move list, so `checkP` refuses the copy.
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
-- `slot`, so the guard there cannot see it.
protoKept : ∀ {m n} → Thin m n → PTm n → Bool
protoKept th (await x _)   = keptAt (toℕ x) th
protoKept th (ignore x _)  = keptAt (toℕ x) th
protoKept th (nignore x _) = keptAt (toℕ x) th
protoKept _ _              = true

-- A protocol consumer at this index is one computational use, and that
-- use is not added to the child's. The slot itself must move.
-- Anything else moved must be quiet in the parent. A copy is held on
-- each side and the parent use remains.
slot : ∀ {n} → ℕ → Grade → Grade → Spent → Spent → PTm n → Result Spent
slot i c t v u tm with isProtoAt i tm
... | true =
  guard "protocol slot is not moved" (isMove c) >>
  guard "protocol" (isOneCount (compOf u)) >>
  hold run c t v >>
  ok v
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

merge : ∀ {m n k} → ℕ → Thin m n → GCtx n → Uses m → Uses n → PTm k → Result (Uses n)
merge _ t[]       []           []        []       _  = ok []
merge i (skip th) (_ ∷ Γ)      cu        (u ∷ pu) tm =
  merge (suc i) th Γ cu pu tm >>= λ rest → ok (u ∷ rest)
merge i (keep th) (gp c t ∷ Γ) (v ∷ cu)  (u ∷ pu) tm =
  slot i c t v u tm >>= λ w →
  merge (suc i) th Γ cu pu tm >>= λ rest → ok (w ∷ rest)

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
checkSpawn : ∀ {m n} → Thin m n → GCtx n → Uses m → Uses n → PTm n → Result (Uses n)
checkSpawn th Γ cu pu pa =
  guard "protocol slot is not moved" (protoKept th pa) >>
  merge zero th Γ cu pu pa

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

checkP : ∀ {n} → GCtx n → PTm n → Result (Uses n)
checkP {n} Γ done = ok (zeros {n})
checkP Γ (send _ x k) =
  sendGate (pcomp (lookup Γ x)) >>
  checkP Γ k >>= λ uk →
  ok (addU (oneS x (charge run)) uk)
checkP Γ (recv c t k) =
  checkP (gp c t ∷ Γ) k >>= λ uk →
  under run c t uk
-- The protocol form is legal only as this spawn parent. Its
-- continuation is checked with `checkP`, so a protocol buried under
-- the continuation is refused. The parent's one use is the shape
-- check inside `slot` and is not added again.
checkP Γ (spawn th ch (await x k)) =
  thinCtx th Γ >>= λ Γ' →
  checkP Γ' ch >>= λ cu →
  checkP Γ k >>= λ uk →
  checkSpawn th Γ cu (addU (oneS x (charge run)) uk) (await x k)
checkP Γ (spawn th ch (ignore x k)) =
  thinCtx th Γ >>= λ Γ' →
  checkP Γ' ch >>= λ cu →
  checkP Γ k >>= λ uk →
  checkSpawn th Γ cu (addU (oneS x (charge run)) uk) (ignore x k)
checkP Γ (spawn th ch (nignore x k)) =
  thinCtx th Γ >>= λ Γ' →
  checkP Γ' ch >>= λ cu →
  checkP Γ k >>= λ uk →
  checkSpawn th Γ cu (addU (oneS x (charge run)) uk) (nignore x k)
checkP Γ (spawn th ch pa) =
  thinCtx th Γ >>= λ Γ' →
  checkP Γ' ch >>= λ cu →
  checkP Γ pa >>= λ pu →
  checkSpawn th Γ cu pu pa
checkP Γ (seq ds e k) =
  checkDefs zero ds >>= λ _ →
  guardGlam Γ e k >>= λ _ →
  boundaryOk (inB? (comps Γ) e) >>= λ _ →
  decideB (length ds) run Γ e >>= λ eu →
  guardReply ds e k >>= λ _ →
  checkP (gp (seqGrade k) g0 ∷ Γ) k >>= λ uk →
  under run (seqGrade k) g0 uk >>= λ ku →
  ok (addU eu ku)
checkP _ (await _ _)   = fail "protocol is not a spawn reply"
checkP _ (ignore _ _)  = fail "protocol is not a spawn reply"
checkP _ (nignore _ _) = fail "protocol is not a spawn reply"
-- Surface syntax has no tagged constructor (`SPtm`, `toP`), so `load`
-- never builds these five. `replyTok` is `sat g1 (finᶜ 1)`, which
-- holds, so a hand-built `awaitT`, `ignoreT`, `flushT`, `ncheckT`, or
-- `ndemonT` is accepted by `checkP` whenever its continuation is.
-- That is not a file. Parse refuses the words with `not surface`.
-- `markProto` writes `awaitT`, `ignoreT`, and `ncheckT` at runtime.
-- `arm1` writes `flushT`. `npeek1` writes `ndemonT` when the mailbox
-- does not hold the tag. Those runtime terms are not re-checked.
checkP Γ (awaitT _ k)  = replyTok >> checkP Γ k
checkP Γ (ignoreT _ k) = replyTok >> checkP Γ k
checkP Γ (flushT _ k)  = replyTok >> checkP Γ k
checkP Γ (ncheckT _ k) = replyTok >> checkP Γ k
checkP Γ (ndemonT _ k) = replyTok >> checkP Γ k

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
