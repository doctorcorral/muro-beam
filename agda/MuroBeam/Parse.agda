------------------------------------------------------------------------
-- Total parser for an image file. Scope-checked de Bruijn indices
-- land in Fin. `parse-show` is the round trip on character lists:
-- `toList ∘ fromList` is not a --safe lemma.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Parse where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; []; _∷_; _++_; reverse; reverseAcc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; Σ)
open import Data.String.Base using (String; toList)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (Result; ok; fail)
open import Muro.Grade using (Point; fin; inf; Grade; pt; iv)
open import MuroBeam.BTm using
  ( BTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch; gref )

open import MuroBeam.Image using
  ( Image; mk; format; boundary; term; defs
  ; showNat; showPoint; showGrade; showPair; showB; showDefs; render; renderWith
  ; readNatAtom; read-show
  ; AllD; Dig; D0; D1; D2; D3; D4; D5; D6; D7; D8; D9
  ; inc; toLSB; lsb-dig; allD-reverse )
  renaming ([] to anil; _∷_ to _∷a_)
open import MuroBeam.Lib using (++-assoc; ++-identityʳ)

------------------------------------------------------------------------
-- S-expressions. Atoms keep their characters. Frames grow on the right.
------------------------------------------------------------------------

data Sexp : Set where
  atom : List Char → Sexp
  nest : List Sexp → Sexp

data Tag : Set where
  tgze tgsu tgapp tgmatch tglam tgpi tgvar tgtyp tgref tiv tw : Tag
  timage tbound tdefs tentry tseq tdone tno : Tag

tag : List Char → Tag
tag ('g' ∷ 'z' ∷ 'e' ∷ []) = tgze
tag ('g' ∷ 's' ∷ 'u' ∷ []) = tgsu
tag ('g' ∷ 'a' ∷ 'p' ∷ 'p' ∷ []) = tgapp
tag ('g' ∷ 'm' ∷ 'a' ∷ 't' ∷ 'c' ∷ 'h' ∷ []) = tgmatch
tag ('g' ∷ 'l' ∷ 'a' ∷ 'm' ∷ []) = tglam
tag ('g' ∷ 'p' ∷ 'i' ∷ []) = tgpi
tag ('g' ∷ 'v' ∷ 'a' ∷ 'r' ∷ []) = tgvar
tag ('g' ∷ 't' ∷ 'y' ∷ 'p' ∷ []) = tgtyp
tag ('g' ∷ 'r' ∷ 'e' ∷ 'f' ∷ []) = tgref
tag ('i' ∷ 'v' ∷ []) = tiv
tag ('w' ∷ []) = tw
tag ('m' ∷ 'u' ∷ 'r' ∷ 'o' ∷ '-' ∷ 'b' ∷ 'e' ∷ 'a' ∷ 'm' ∷ '-' ∷ 'i' ∷ 'm' ∷ 'a' ∷ 'g' ∷ 'e' ∷ []) = timage
tag ('b' ∷ 'o' ∷ 'u' ∷ 'n' ∷ 'd' ∷ 'a' ∷ 'r' ∷ 'y' ∷ []) = tbound
tag ('d' ∷ 'e' ∷ 'f' ∷ 's' ∷ []) = tdefs
tag ('e' ∷ 'n' ∷ 't' ∷ 'r' ∷ 'y' ∷ []) = tentry
tag ('s' ∷ 'e' ∷ 'q' ∷ []) = tseq
tag ('d' ∷ 'o' ∷ 'n' ∷ 'e' ∷ []) = tdone
tag _ = tno

sexpPoint : Point → Sexp
sexpPoint (fin n) = atom (showNat n)
sexpPoint inf     = atom (toList "w")

sexpGrade : Grade → Sexp
sexpGrade (pt p)   = sexpPoint p
sexpGrade (iv a b) = nest (atom (toList "iv") ∷ sexpPoint a ∷ sexpPoint b ∷ [])

sexpPair : Grade → Grade → Sexp
sexpPair c t = nest (sexpGrade c ∷ sexpGrade t ∷ [])

sexpB : ∀ {n} → BTm n → Sexp
sexpB (gvar x) = nest (atom (toList "gvar") ∷ atom (showNat (toℕ x)) ∷ [])
sexpB (gtyp x) = nest (atom (toList "gtyp") ∷ atom (showNat (toℕ x)) ∷ [])
sexpB (glam c t b) = nest (atom (toList "glam") ∷ sexpPair c t ∷ sexpB b ∷ [])
sexpB (gpi c t b) = nest (atom (toList "gpi") ∷ sexpPair c t ∷ sexpB b ∷ [])
sexpB (gapp f a) = nest (atom (toList "gapp") ∷ sexpB f ∷ sexpB a ∷ [])
sexpB gze = atom (toList "gze")
sexpB (gsu e) = nest (atom (toList "gsu") ∷ sexpB e ∷ [])
sexpB (gmatch e z s) =
  nest (atom (toList "gmatch") ∷ sexpB e ∷ sexpB z ∷ sexpB s ∷ [])
sexpB (gref k) = nest (atom (toList "gref") ∷ atom (showNat k) ∷ [])

sexpList : List (BTm 0) → List Sexp
sexpList [] = []
sexpList (t ∷ ts) = sexpB t ∷ sexpList ts

-- Same split as `renderWith`. Top level, so a rewrite of `defs i`
-- reduces the nest. Empty defs is the four-sexp v1 nest.
entrySexp : BTm 0 → Sexp
entrySexp tm =
  nest (atom (toList "entry")
     ∷ nest (atom (toList "seq")
          ∷ sexpB tm
          ∷ nest (atom (toList "done") ∷ [])
          ∷ [])
     ∷ [])

sexpWith : List (BTm 0) → ℕ → ℕ → BTm 0 → Sexp
sexpWith [] fv bv tm =
  nest ( atom (toList "muro-beam-image")
       ∷ atom (showNat fv)
       ∷ nest (atom (toList "boundary") ∷ atom (showNat bv) ∷ [])
       ∷ entrySexp tm
       ∷ [])
sexpWith (d ∷ ds) fv bv tm =
  nest ( atom (toList "muro-beam-image")
       ∷ atom (showNat fv)
       ∷ nest (atom (toList "boundary") ∷ atom (showNat bv) ∷ [])
       ∷ nest (atom (toList "defs") ∷ sexpList (d ∷ ds))
       ∷ entrySexp tm
       ∷ [])

sexpImage : Image → Sexp
sexpImage i = sexpWith (defs i) (format i) (boundary i) (term i)

------------------------------------------------------------------------
-- de Bruijn. An index that does not fit the scope is refused.
------------------------------------------------------------------------

finFrom : ∀ {n} → ℕ → Maybe (Fin n)
finFrom {zero}  _       = nothing
finFrom {suc _} zero    = just fzero
finFrom {suc n} (suc k) with finFrom {n} k
... | just i  = just (fsuc i)
... | nothing = nothing

fin-to : ∀ {n} (i : Fin n) → finFrom (toℕ i) ≡ just i
fin-to {zero}  ()
fin-to {suc _} fzero = refl
fin-to {suc _} (fsuc i) rewrite fin-to i = refl

fromPointAtom : List Char → Result Point
fromPointAtom cs with readNatAtom cs
... | just n  = ok (fin n)
... | nothing = pointTag (tag cs)
  where
  pointTag : Tag → Result Point
  pointTag tw = ok inf
  pointTag _  = fail "junk"

fromPoint : Sexp → Result Point
fromPoint (atom cs) = fromPointAtom cs
fromPoint _         = fail "junk"

fromGrade : Sexp → Result Grade
fromGrade (atom cs) = pt <$> fromPointAtom cs
  where
  _<$>_ : ∀ {A B : Set} → (A → B) → Result A → Result B
  f <$> ok x   = ok (f x)
  _ <$> fail e = fail e
fromGrade (nest (atom k ∷ a ∷ b ∷ [])) with tag k
... | tiv = ivBoth (fromPoint a) (fromPoint b)
  where
  ivBoth : Result Point → Result Point → Result Grade
  ivBoth (ok p) (ok q)   = ok (iv p q)
  ivBoth (fail e) _      = fail e
  ivBoth (ok _) (fail e) = fail e
... | _ = fail "junk"
fromGrade _ = fail "junk"

fromPair : Sexp → Result (Grade × Grade)
fromPair (nest (c ∷ t ∷ [])) with fromGrade c | fromGrade t
... | ok gc | ok gt = ok (gc , gt)
... | fail e | _    = fail e
... | _ | fail e    = fail e
fromPair _ = fail "junk"

fromVar : ∀ {n} → (Fin n → BTm n) → List Sexp → Result (BTm n)
fromVar ctor (atom ds ∷ []) with readNatAtom ds
... | nothing = fail "junk"
... | just k with finFrom k
... | nothing = fail "out of scope"
... | just i  = ok (ctor i)
fromVar _ _ = fail "junk"

-- A `gref` index is a raw natural. The definition bound is checked
-- by `decideB`, not by the parser.
fromRef : ∀ {n} → List Sexp → Result (BTm n)
fromRef (atom ds ∷ []) with readNatAtom ds
... | nothing = fail "junk"
... | just k  = ok (gref k)
fromRef _ = fail "junk"

mutual
  fromB : ∀ {n} → Sexp → Result (BTm n)

  fromSu : ∀ {n} → List Sexp → Result (BTm n)
  fromSu (e ∷ []) with fromB e
  ... | ok t   = ok (gsu t)
  ... | fail e = fail e
  fromSu _ = fail "junk"

  fromApp : ∀ {n} → List Sexp → Result (BTm n)
  fromApp (f ∷ a ∷ []) with fromB f | fromB a
  ... | ok fv | ok av = ok (gapp fv av)
  ... | fail e | _    = fail e
  ... | _ | fail e    = fail e
  fromApp _ = fail "junk"

  fromMatch : ∀ {n} → List Sexp → Result (BTm n)
  fromMatch (e ∷ z ∷ s ∷ []) with fromB e | fromB z | fromB s
  ... | ok ev | ok zv | ok sv = ok (gmatch ev zv sv)
  ... | fail e | _ | _        = fail e
  ... | _ | fail e | _        = fail e
  ... | _ | _ | fail e        = fail e
  fromMatch _ = fail "junk"

  fromBind : ∀ {n} → (Grade → Grade → BTm (suc n) → BTm n) → List Sexp → Result (BTm n)
  fromBind {n} ctor (p ∷ b ∷ []) with fromPair p
  ... | fail e = fail e
  ... | ok (c , t) with fromB {suc n} b
  ... | fail e   = fail e
  ... | ok body  = ok (ctor c t body)
  fromBind _ _ = fail "junk"

  fromB (atom cs) with tag cs
  ... | tgze = ok gze
  ... | _    = fail "junk"
  fromB (nest []) = fail "junk"
  fromB (nest (atom cs ∷ xs)) with tag cs
  ... | tgsu    = fromSu xs
  ... | tgapp   = fromApp xs
  ... | tgmatch = fromMatch xs
  ... | tglam   = fromBind glam xs
  ... | tgpi    = fromBind gpi xs
  ... | tgvar   = fromVar gvar xs
  ... | tgtyp   = fromVar gtyp xs
  ... | tgref   = fromRef xs
  ... | _       = fail "junk"
  fromB (nest (_ ∷ _)) = fail "junk"

fromDone : Sexp → Result ⊤
fromDone (nest (atom k ∷ [])) with tag k
... | tdone = ok tt
... | _     = fail "junk"
fromDone _ = fail "junk"

fromSeq : Sexp → Result (BTm 0)
fromSeq (nest (atom k ∷ t ∷ d ∷ [])) with tag k
... | tseq = seqBoth (fromB t) (fromDone d)
  where
  seqBoth : Result (BTm 0) → Result ⊤ → Result (BTm 0)
  seqBoth (ok tm) (ok _)   = ok tm
  seqBoth (fail e) _       = fail e
  seqBoth (ok _) (fail e)  = fail e
... | _ = fail "junk"
fromSeq _ = fail "junk"

fromEntry : Sexp → Result (BTm 0)
fromEntry (nest (atom k ∷ b ∷ [])) with tag k
... | tentry = fromSeq b
... | _      = fail "junk"
fromEntry _ = fail "junk"

fromBound : Sexp → Result ℕ
fromBound (nest (atom k ∷ atom v ∷ [])) with tag k
... | tbound = boundNat (readNatAtom v)
  where
  boundNat : Maybe ℕ → Result ℕ
  boundNat (just n) = ok n
  boundNat nothing  = fail "junk"
... | _ = fail "junk"
fromBound _ = fail "junk"

defsTail : List Sexp → Result (List (BTm 0))
defsTail [] = ok []
defsTail (s ∷ ss) with fromB s
... | fail e = fail e
... | ok t with defsTail ss
... | fail e = fail e
... | ok ts = ok (t ∷ ts)

defsBody : List Sexp → Result (List (BTm 0))
defsBody [] = fail "junk"
defsBody (s ∷ ss) with fromB s
... | fail e = fail e
... | ok t with defsTail ss
... | fail e = fail e
... | ok ts = ok (t ∷ ts)

fromDefs : Sexp → Result (List (BTm 0))
fromDefs (nest (atom k ∷ xs)) with tag k
... | tdefs = defsBody xs
... | _ = fail "junk"
fromDefs _ = fail "junk"

fromImage : Sexp → Result Image
fromImage (nest (atom k ∷ atom v ∷ b ∷ rest)) with tag k
... | timage = imageRest (readNatAtom v) (fromBound b) rest
  where
  build : Maybe ℕ → Result ℕ → Result (List (BTm 0)) → Result (BTm 0) → Result Image
  build (just fv) (ok bv) (ok ds) (ok tm) = ok (mk fv bv ds tm)
  build nothing _ _ _ = fail "junk"
  build (just _) (fail msg) _ _ = fail msg
  build (just _) (ok _) (fail msg) _ = fail msg
  build (just _) (ok _) (ok _) (fail msg) = fail msg
  imageRest : Maybe ℕ → Result ℕ → List Sexp → Result Image
  imageRest fv bv (e ∷ []) = build fv bv (ok []) (fromEntry e)
  imageRest fv bv (ds ∷ e ∷ []) = build fv bv (fromDefs ds) (fromEntry e)
  imageRest _ _ _ = fail "junk"
... | _ = fail "junk"
fromImage _ = fail "junk"

------------------------------------------------------------------------
-- One state machine. Every recursive call is on a tail of the input.
------------------------------------------------------------------------

atom? : Char → Bool
atom? '('  = false
atom? ')'  = false
atom? ' '  = false
atom? '\n' = false
atom? _    = true

Stk : Set
Stk = List (List Sexp)

data Mode : Set where
  top  : Mode
  need : Stk → Mode
  rd   : List Char → Stk → Mode
  sep  : Stk → Mode

mutual
  parseGo : Mode → List Char → Result (Sexp × List Char)

  parseGo top [] = fail "truncated"
  parseGo top ('(' ∷ cs) = parseGo (need ([] ∷ [])) cs
  parseGo top (')' ∷ _) = fail "junk"
  parseGo top (' ' ∷ _) = fail "junk"
  parseGo top ('\n' ∷ _) = fail "junk"
  parseGo top (c ∷ cs) = parseGo (rd (c ∷ []) []) cs

  parseGo (need []) [] = fail "truncated"
  parseGo (need []) ('(' ∷ _) = fail "junk"
  parseGo (need []) (')' ∷ _) = fail "junk"
  parseGo (need []) (' ' ∷ _) = fail "junk"
  parseGo (need []) ('\n' ∷ _) = fail "junk"
  parseGo (need []) (_ ∷ _) = fail "junk"

  parseGo (need (fr ∷ stk)) [] = fail "truncated"
  parseGo (need (fr ∷ stk)) (c ∷ cs) with atom? c
  ... | true  = parseGo (rd (c ∷ []) (fr ∷ stk)) cs
  ... | false = needStop c fr stk cs

  parseGo (rd acc []) [] = ok (atom acc , [])
  parseGo (rd acc []) ('(' ∷ _) = fail "junk"
  parseGo (rd acc []) (')' ∷ cs) = ok (atom acc , ')' ∷ cs)
  parseGo (rd acc []) (' ' ∷ cs) = ok (atom acc , ' ' ∷ cs)
  parseGo (rd acc []) ('\n' ∷ cs) = ok (atom acc , '\n' ∷ cs)
  parseGo (rd acc []) (c ∷ cs) with atom? c
  ... | true  = parseGo (rd (acc ++ c ∷ []) []) cs
  ... | false = fail "junk"

  parseGo (rd acc (fr ∷ stk)) [] = fail "truncated"
  parseGo (rd acc (fr ∷ stk)) (c ∷ cs) with atom? c
  ... | true  = parseGo (rd (acc ++ c ∷ []) (fr ∷ stk)) cs
  ... | false = rdStop acc c fr stk cs

  parseGo (sep []) _ = fail "junk"
  parseGo (sep (_ ∷ _)) [] = fail "truncated"
  parseGo (sep (_ ∷ _)) ('(' ∷ _) = fail "junk"
  parseGo (sep (fr ∷ [])) (')' ∷ cs) = ok (nest fr , cs)
  parseGo (sep (fr ∷ o ∷ stk)) (')' ∷ cs) =
    parseGo (sep ((o ++ nest fr ∷ []) ∷ stk)) cs
  parseGo (sep (fr ∷ stk)) (' ' ∷ cs) = parseGo (need (fr ∷ stk)) cs
  parseGo (sep (_ ∷ _)) ('\n' ∷ _) = fail "junk"
  parseGo (sep (_ ∷ _)) (_ ∷ _) = fail "junk"

  -- Delimiters are the `atom?` false branch, so a proof that a
  -- character is an atom makes the reader clause reduce.
  needStop : Char → List Sexp → Stk → List Char → Result (Sexp × List Char)
  needStop '(' fr stk cs = parseGo (need ([] ∷ fr ∷ stk)) cs
  needStop ')' fr [] cs = ok (nest fr , cs)
  needStop ')' fr (o ∷ stk) cs =
    parseGo (sep ((o ++ nest fr ∷ []) ∷ stk)) cs
  needStop ' ' _ _ _ = fail "junk"
  needStop '\n' _ _ _ = fail "junk"
  needStop _ _ _ _ = fail "junk"

  rdStop : List Char → Char → List Sexp → Stk → List Char → Result (Sexp × List Char)
  rdStop _ '(' _ _ _ = fail "junk"
  rdStop acc ')' fr [] cs = ok (nest (fr ++ atom acc ∷ []) , cs)
  rdStop acc ')' fr (o ∷ stk) cs =
    parseGo (sep ((o ++ nest (fr ++ atom acc ∷ []) ∷ []) ∷ stk)) cs
  rdStop acc ' ' fr stk cs =
    parseGo (need ((fr ++ atom acc ∷ []) ∷ stk)) cs
  rdStop _ '\n' _ _ _ = fail "junk"
  rdStop _ _ _ _ _ = fail "junk"

finish : Result (Sexp × List Char) → Result Image
finish (fail e) = fail e
finish (ok (s , '\n' ∷ [])) = fromImage s
finish (ok (_ , [])) = fail "truncated"
finish (ok _) = fail "junk"

parseCs : List Char → Result Image
parseCs cs = finish (parseGo top cs)

parseR : String → Result Image
parseR s = parseCs (toList s)

parse : String → Maybe Image
parse s with parseR s
... | ok i   = just i
... | fail _ = nothing

------------------------------------------------------------------------
-- What the printer emits, the machine reads back.
------------------------------------------------------------------------

data AllA : List Char → Set where
  []  : AllA []
  _∷_ : ∀ {c cs} → atom? c ≡ true → AllA cs → AllA (c ∷ cs)

data Delim : List Char → Set where
  dend : Delim []
  dsp  : ∀ xs → Delim (' ' ∷ xs)
  drp  : ∀ xs → Delim (')' ∷ xs)
  dnl  : ∀ xs → Delim ('\n' ∷ xs)

dig-atom : ∀ {c} → Dig c → atom? c ≡ true
dig-atom D0 = refl
dig-atom D1 = refl
dig-atom D2 = refl
dig-atom D3 = refl
dig-atom D4 = refl
dig-atom D5 = refl
dig-atom D6 = refl
dig-atom D7 = refl
dig-atom D8 = refl
dig-atom D9 = refl

toA : ∀ {cs} → AllD cs → AllA cs
toA anil       = []
toA (d ∷a ds) = dig-atom d ∷ toA ds

after : List Sexp → Stk → List Char → Result (Sexp × List Char)
after fr stk rest = parseGo (sep (fr ∷ stk)) rest

specRd : ∀ acc cs fr stk rest → AllA cs → Delim rest →
  parseGo (rd acc (fr ∷ stk)) (cs ++ rest)
  ≡ after (fr ++ atom (acc ++ cs) ∷ []) stk rest

rdEmpty : ∀ acc fr stk rest → Delim rest →
  parseGo (rd acc (fr ∷ stk)) rest
  ≡ after (fr ++ atom acc ∷ []) stk rest
rdEmpty acc fr stk [] dend = refl
rdEmpty acc fr stk (' ' ∷ _) (dsp _) = refl
rdEmpty acc fr [] (')' ∷ _) (drp _) = refl
rdEmpty acc fr (_ ∷ _) (')' ∷ _) (drp _) = refl
rdEmpty acc fr stk ('\n' ∷ _) (dnl _) = refl

specRd acc [] fr stk rest [] d rewrite ++-identityʳ acc = rdEmpty acc fr stk rest d
specRd acc (c ∷ cs) fr stk rest (p ∷ ps) d with atom? c | p
... | true | refl =
  trans (specRd (acc ++ c ∷ []) cs fr stk rest ps d)
        (cong (λ zs → after (fr ++ atom zs ∷ []) stk rest)
              (++-assoc acc (c ∷ []) cs))
... | false | ()

specAtom : ∀ c cs fr stk rest → atom? c ≡ true → AllA cs → Delim rest →
  parseGo (need (fr ∷ stk)) ((c ∷ cs) ++ rest)
  ≡ after (fr ++ atom (c ∷ cs) ∷ []) stk rest
specAtom c cs fr stk rest p ps d with atom? c | p
... | true | refl = specRd (c ∷ []) cs fr stk rest ps d
... | false | ()

------------------------------------------------------------------------
-- A shown natural is a nonempty digit atom.
------------------------------------------------------------------------

record Split (xs : List Char) : Set where
  constructor sp
  field
    ch : Char
    tl : List Char
    eq : xs ≡ ch ∷ tl
    dg : Dig ch
    rs : AllD tl

open Split

inc-split : ∀ {xs} → AllD xs → Split (inc xs)
inc-split anil = sp '1' [] refl D1 anil
inc-split (D0 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('1' ∷ ys)
  on {ys} ads = sp '1' ys refl D1 ads
inc-split (D1 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('2' ∷ ys)
  on {ys} ads = sp '2' ys refl D2 ads
inc-split (D2 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('3' ∷ ys)
  on {ys} ads = sp '3' ys refl D3 ads
inc-split (D3 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('4' ∷ ys)
  on {ys} ads = sp '4' ys refl D4 ads
inc-split (D4 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('5' ∷ ys)
  on {ys} ads = sp '5' ys refl D5 ads
inc-split (D5 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('6' ∷ ys)
  on {ys} ads = sp '6' ys refl D6 ads
inc-split (D6 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('7' ∷ ys)
  on {ys} ads = sp '7' ys refl D7 ads
inc-split (D7 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('8' ∷ ys)
  on {ys} ads = sp '8' ys refl D8 ads
inc-split (D8 ∷a ds) = on ds
  where
  on : ∀ {ys} → AllD ys → Split ('9' ∷ ys)
  on {ys} ads = sp '9' ys refl D9 ads
inc-split (D9 ∷a ds) with inc-split ds
... | sp c cs eq d tl rewrite eq = sp '0' (c ∷ cs) refl D0 (d ∷a tl)

lsb-split : ∀ n → Split (toLSB n)
lsb-split zero    = sp '0' [] refl D0 anil
lsb-split (suc n) = inc-split (lsb-dig n)

revAcc-cons : ∀ {A : Set} (a : A) acc (xs : List A) →
  Σ A (λ d → Σ (List A) (λ ds → reverseAcc (a ∷ acc) xs ≡ d ∷ ds))
revAcc-cons a acc [] = a , acc , refl
revAcc-cons a acc (x ∷ xs) = revAcc-cons x (a ∷ acc) xs

show-split : ∀ n → Split (showNat n)
show-split n with lsb-split n
... | sp c cs eq d tl rewrite eq = fromRev c cs (d ∷a tl)
  where
  fromRev : ∀ c cs → AllD (c ∷ cs) → Split (reverse (c ∷ cs))
  fromRev c cs ad with revAcc-cons c [] cs
  ... | h , hs , eq2 with subst AllD eq2 (allD-reverse ad)
  ... | dig ∷a rest = subst Split (sym eq2) (sp h hs refl dig rest)

specNat : ∀ n fr stk rest → Delim rest →
  parseGo (need (fr ∷ stk)) (showNat n ++ rest)
  ≡ after (fr ++ atom (showNat n) ∷ []) stk rest
specNat n fr stk rest d with show-split n
... | sp c cs eq dg tl rewrite eq =
  specAtom c cs fr stk rest (dig-atom dg) (toA tl) d

------------------------------------------------------------------------
-- Round trip on character lists. `parse (showImage i) ≡ just i` needs
-- `toList ∘ fromList`, and that lemma is not --safe. `parse-show` is
-- `parseCs ∘ render`.
------------------------------------------------------------------------

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl
infixl 3 _∎

pin-img : toList "muro-beam-image" ≡
  'm' ∷ 'u' ∷ 'r' ∷ 'o' ∷ '-' ∷ 'b' ∷ 'e' ∷ 'a' ∷ 'm' ∷ '-' ∷ 'i' ∷ 'm' ∷ 'a' ∷ 'g' ∷ 'e' ∷ []
pin-img = refl

pin-gsu : toList "(gsu " ≡ '(' ∷ 'g' ∷ 's' ∷ 'u' ∷ ' ' ∷ []
pin-gsu = refl

pin-bd : toList " (boundary " ≡
  ' ' ∷ '(' ∷ 'b' ∷ 'o' ∷ 'u' ∷ 'n' ∷ 'd' ∷ 'a' ∷ 'r' ∷ 'y' ∷ ' ' ∷ []
pin-bd = refl

fromPoint-ok : ∀ p → fromPoint (sexpPoint p) ≡ ok p
fromPoint-ok (fin n) rewrite read-show n = refl
fromPoint-ok inf = refl

fromGrade-ok : ∀ g → fromGrade (sexpGrade g) ≡ ok g
fromGrade-ok (pt (fin n)) rewrite read-show n = refl
fromGrade-ok (pt inf) = refl
fromGrade-ok (iv a b) rewrite fromPoint-ok a | fromPoint-ok b = refl

fromPair-ok : ∀ c t → fromPair (sexpPair c t) ≡ ok (c , t)
fromPair-ok c t rewrite fromGrade-ok c | fromGrade-ok t = refl

fromB-ok : ∀ {n} (t : BTm n) → fromB (sexpB t) ≡ ok t
fromB-ok gze = refl
fromB-ok (gsu e) rewrite fromB-ok e = refl
fromB-ok (gapp f a) rewrite fromB-ok f | fromB-ok a = refl
fromB-ok (gmatch e z s) rewrite fromB-ok e | fromB-ok z | fromB-ok s = refl
fromB-ok (glam c t b) rewrite fromPair-ok c t | fromB-ok b = refl
fromB-ok (gpi c t b) rewrite fromPair-ok c t | fromB-ok b = refl
fromB-ok (gvar x) rewrite read-show (toℕ x) | fin-to x = refl
fromB-ok (gtyp x) rewrite read-show (toℕ x) | fin-to x = refl
fromB-ok (gref k) rewrite read-show k = refl

tail-ok : ∀ ts → defsTail (sexpList ts) ≡ ok ts
tail-ok [] = refl
tail-ok (t ∷ ts) rewrite fromB-ok t | tail-ok ts = refl

fromDefs-ok : ∀ t ts →
  fromDefs (nest (atom (toList "defs") ∷ sexpList (t ∷ ts))) ≡ ok (t ∷ ts)
fromDefs-ok t ts rewrite fromB-ok t | tail-ok ts = refl

fromImage-ok : ∀ i → fromImage (sexpImage i) ≡ ok i
fromImage-ok i = on (defs i) refl
  where
  -- `ok i` does not mention `defs i`. Rewrite reduces the sexp, and
  -- record η puts the split list back on the right.
  image-η : ∀ ds → defs i ≡ ds →
            mk (format i) (boundary i) ds (term i) ≡ i
  image-η _ refl = refl

  open-ok : ∀ ds → defs i ≡ ds →
            fromImage (sexpImage i) ≡ ok (mk (format i) (boundary i) ds (term i))
  open-ok [] eq rewrite eq | read-show (format i) | read-show (boundary i) | fromB-ok (term i) = refl
  open-ok (t ∷ ts) eq rewrite eq | read-show (format i) | read-show (boundary i)
                                  | fromDefs-ok t ts | fromB-ok (term i) = refl

  on : (ds : List (BTm 0)) → defs i ≡ ds → fromImage (sexpImage i) ≡ ok i
  on ds eq = trans (open-ok ds eq) (cong ok (image-η ds eq))

push : ∀ fr stk xs ys zs →
  parseGo (need (fr ∷ stk)) ((xs ++ ys) ++ zs)
  ≡ parseGo (need (fr ∷ stk)) (xs ++ (ys ++ zs))
push fr stk xs ys zs = cong (parseGo (need (fr ∷ stk))) (++-assoc xs ys zs)

eatKw : ∀ c cs fr stk more → atom? c ≡ true → AllA cs →
  parseGo (need (fr ∷ stk)) ((c ∷ cs) ++ (' ' ∷ more))
  ≡ parseGo (need ((fr ++ (atom (c ∷ cs) ∷ [])) ∷ stk)) more
eatKw c cs fr stk more p ps =
  specAtom c cs fr stk (' ' ∷ more) p ps (dsp more)

gap : ∀ fr stk cs →
  after fr stk (' ' ∷ cs) ≡ parseGo (need (fr ∷ stk)) cs
gap _ _ _ = refl

shut : ∀ inner fr stk rest →
  after inner (fr ∷ stk) (')' ∷ rest)
  ≡ after (fr ++ (nest inner ∷ [])) stk rest
shut _ _ _ _ = refl

shut1 : ∀ fr cs →
  after fr [] (')' ∷ cs) ≡ ok (nest fr , cs)
shut1 _ _ = refl

specPoint : ∀ p fr stk rest → Delim rest →
  parseGo (need (fr ∷ stk)) (showPoint p ++ rest)
  ≡ after (fr ++ sexpPoint p ∷ []) stk rest
specPoint (fin n) = specNat n
specPoint inf fr stk rest d = specAtom 'w' [] fr stk rest refl [] d

specGrade : ∀ g fr stk rest → Delim rest →
  parseGo (need (fr ∷ stk)) (showGrade g ++ rest)
  ≡ after (fr ++ sexpGrade g ∷ []) stk rest
specGrade (pt p) = specPoint p
specGrade (iv a b) fr stk rest d = chain
  where
  kw = toList "iv "
  spb = toList " " ++ (showPoint b ++ toList ")")
  body = showPoint a ++ spb
  kwF = atom (toList "iv") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGrade (iv a b) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'i' ('v' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showPoint a ++ spb) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showPoint a) spb rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showPoint a ++ (spb ++ rest))
      ≡⟨ specPoint a kwF (fr ∷ stk) (spb ++ rest) (dsp ((showPoint b ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpPoint a ∷ []) (fr ∷ stk) (spb ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpPoint a ∷ []) ∷ fr ∷ stk)) ((showPoint b ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpPoint a ∷ []) (fr ∷ stk) (showPoint b) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpPoint a ∷ []) ∷ fr ∷ stk)) (showPoint b ++ (toList ")" ++ rest))
      ≡⟨ specPoint b (kwF ++ sexpPoint a ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpPoint a ∷ sexpPoint b ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpPoint a ∷ sexpPoint b ∷ []) fr stk rest ⟩
    after (fr ++ sexpGrade (iv a b) ∷ []) stk rest
      ∎

specPair : ∀ c t fr stk rest → Delim rest →
  parseGo (need (fr ∷ stk)) (showPair c t ++ rest)
  ≡ after (fr ++ sexpPair c t ∷ []) stk rest
specPair c t fr stk rest d = chain
  where
  spc = toList " " ++ (showGrade t ++ toList ")")
  body = showGrade c ++ spc
  chain =
    parseGo (need (fr ∷ stk)) (showPair c t ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) (body ++ rest)
      ≡⟨ push [] (fr ∷ stk) (showGrade c) spc rest ⟩
    parseGo (need ([] ∷ fr ∷ stk)) (showGrade c ++ (spc ++ rest))
      ≡⟨ specGrade c [] (fr ∷ stk) (spc ++ rest) (dsp ((showGrade t ++ toList ")") ++ rest)) ⟩
    after (sexpGrade c ∷ []) (fr ∷ stk) (spc ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((sexpGrade c ∷ []) ∷ fr ∷ stk)) ((showGrade t ++ toList ")") ++ rest)
      ≡⟨ push (sexpGrade c ∷ []) (fr ∷ stk) (showGrade t) (toList ")") rest ⟩
    parseGo (need ((sexpGrade c ∷ []) ∷ fr ∷ stk)) (showGrade t ++ (toList ")" ++ rest))
      ≡⟨ specGrade t (sexpGrade c ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (sexpGrade c ∷ sexpGrade t ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (sexpGrade c ∷ sexpGrade t ∷ []) fr stk rest ⟩
    after (fr ++ sexpPair c t ∷ []) stk rest
      ∎

specB : ∀ {n} (t : BTm n) fr stk rest → Delim rest →
  parseGo (need (fr ∷ stk)) (showB t ++ rest)
  ≡ after (fr ++ sexpB t ∷ []) stk rest
specB gze fr stk rest d =
  specAtom 'g' ('z' ∷ 'e' ∷ []) fr stk rest refl (refl ∷ refl ∷ []) d
specB (gvar x) fr stk rest d = chain
  where
  kw = toList "gvar "
  body = showNat (toℕ x) ++ toList ")"
  kwF = atom (toList "gvar") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB (gvar x) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('v' ∷ 'a' ∷ 'r' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showNat (toℕ x) ++ toList ")") ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showNat (toℕ x)) (toList ")") rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showNat (toℕ x) ++ (toList ")" ++ rest))
      ≡⟨ specNat (toℕ x) kwF (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ atom (showNat (toℕ x)) ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ atom (showNat (toℕ x)) ∷ []) fr stk rest ⟩
    after (fr ++ sexpB (gvar x) ∷ []) stk rest
      ∎
specB (gtyp x) fr stk rest d = chain
  where
  kw = toList "gtyp "
  body = showNat (toℕ x) ++ toList ")"
  kwF = atom (toList "gtyp") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB (gtyp x) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('t' ∷ 'y' ∷ 'p' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showNat (toℕ x) ++ toList ")") ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showNat (toℕ x)) (toList ")") rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showNat (toℕ x) ++ (toList ")" ++ rest))
      ≡⟨ specNat (toℕ x) kwF (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ atom (showNat (toℕ x)) ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ atom (showNat (toℕ x)) ∷ []) fr stk rest ⟩
    after (fr ++ sexpB (gtyp x) ∷ []) stk rest
      ∎
specB (gsu e) fr stk rest d = chain
  where
  kw = toList "gsu "
  body = showB e ++ toList ")"
  kwF = atom (toList "gsu") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB (gsu e) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('s' ∷ 'u' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showB e ++ toList ")") ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showB e) (toList ")") rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showB e ++ (toList ")" ++ rest))
      ≡⟨ specB e kwF (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpB e ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpB e ∷ []) fr stk rest ⟩
    after (fr ++ sexpB (gsu e) ∷ []) stk rest
      ∎
specB (gapp f a) fr stk rest d = chain
  where
  kw = toList "gapp "
  mid = toList " " ++ (showB a ++ toList ")")
  body = showB f ++ mid
  kwF = atom (toList "gapp") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB (gapp f a) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('a' ∷ 'p' ∷ 'p' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showB f ++ mid) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showB f) mid rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showB f ++ (mid ++ rest))
      ≡⟨ specB f kwF (fr ∷ stk) (mid ++ rest) (dsp ((showB a ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpB f ∷ []) (fr ∷ stk) (mid ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpB f ∷ []) ∷ fr ∷ stk)) ((showB a ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpB f ∷ []) (fr ∷ stk) (showB a) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpB f ∷ []) ∷ fr ∷ stk)) (showB a ++ (toList ")" ++ rest))
      ≡⟨ specB a (kwF ++ sexpB f ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpB f ∷ sexpB a ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpB f ∷ sexpB a ∷ []) fr stk rest ⟩
    after (fr ++ sexpB (gapp f a) ∷ []) stk rest
      ∎
specB (gmatch e z s) fr stk rest d = chain
  where
  kw = toList "gmatch "
  spS = toList " " ++ (showB s ++ toList ")")
  spZ = toList " " ++ (showB z ++ spS)
  body = showB e ++ spZ
  kwF = atom (toList "gmatch") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB (gmatch e z s) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('m' ∷ 'a' ∷ 't' ∷ 'c' ∷ 'h' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showB e ++ spZ) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showB e) spZ rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showB e ++ (spZ ++ rest))
      ≡⟨ specB e kwF (fr ∷ stk) (spZ ++ rest) (dsp ((showB z ++ spS) ++ rest)) ⟩
    after (kwF ++ sexpB e ∷ []) (fr ∷ stk) (spZ ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpB e ∷ []) ∷ fr ∷ stk)) ((showB z ++ spS) ++ rest)
      ≡⟨ push (kwF ++ sexpB e ∷ []) (fr ∷ stk) (showB z) spS rest ⟩
    parseGo (need ((kwF ++ sexpB e ∷ []) ∷ fr ∷ stk)) (showB z ++ (spS ++ rest))
      ≡⟨ specB z (kwF ++ sexpB e ∷ []) (fr ∷ stk) (spS ++ rest) (dsp ((showB s ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpB e ∷ sexpB z ∷ []) (fr ∷ stk) (spS ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpB e ∷ sexpB z ∷ []) ∷ fr ∷ stk)) ((showB s ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpB e ∷ sexpB z ∷ []) (fr ∷ stk) (showB s) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpB e ∷ sexpB z ∷ []) ∷ fr ∷ stk)) (showB s ++ (toList ")" ++ rest))
      ≡⟨ specB s (kwF ++ sexpB e ∷ sexpB z ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpB e ∷ sexpB z ∷ sexpB s ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpB e ∷ sexpB z ∷ sexpB s ∷ []) fr stk rest ⟩
    after (fr ++ sexpB (gmatch e z s) ∷ []) stk rest
      ∎
specB (glam c t b) fr stk rest d = chain
  where
  kw = toList "glam "
  mid = toList " " ++ (showB b ++ toList ")")
  body = showPair c t ++ mid
  kwF = atom (toList "glam") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB (glam c t b) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('l' ∷ 'a' ∷ 'm' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showPair c t ++ mid) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showPair c t) mid rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showPair c t ++ (mid ++ rest))
      ≡⟨ specPair c t kwF (fr ∷ stk) (mid ++ rest) (dsp ((showB b ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (mid ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) ((showB b ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (showB b) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) (showB b ++ (toList ")" ++ rest))
      ≡⟨ specB b (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpPair c t ∷ sexpB b ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpPair c t ∷ sexpB b ∷ []) fr stk rest ⟩
    after (fr ++ sexpB (glam c t b) ∷ []) stk rest
      ∎
specB (gpi c t b) fr stk rest d = chain
  where
  kw = toList "gpi "
  mid = toList " " ++ (showB b ++ toList ")")
  body = showPair c t ++ mid
  kwF = atom (toList "gpi") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB (gpi c t b) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('p' ∷ 'i' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showPair c t ++ mid) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showPair c t) mid rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showPair c t ++ (mid ++ rest))
      ≡⟨ specPair c t kwF (fr ∷ stk) (mid ++ rest) (dsp ((showB b ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (mid ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) ((showB b ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (showB b) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) (showB b ++ (toList ")" ++ rest))
      ≡⟨ specB b (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpPair c t ∷ sexpB b ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpPair c t ∷ sexpB b ∷ []) fr stk rest ⟩
    after (fr ++ sexpB (gpi c t b) ∷ []) stk rest
      ∎
specB {n} (gref k) fr stk rest d = chain
  where
  kw = toList "gref "
  body = showNat k ++ toList ")"
  kwF = atom (toList "gref") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showB {n} (gref k) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('r' ∷ 'e' ∷ 'f' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showNat k ++ toList ")") ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showNat k) (toList ")") rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showNat k ++ (toList ")" ++ rest))
      ≡⟨ specNat k kwF (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ atom (showNat k) ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ atom (showNat k) ∷ []) fr stk rest ⟩
    after (fr ++ sexpB {n} (gref k) ∷ []) stk rest
      ∎

imgTail : List Char
imgTail = 'u' ∷ 'r' ∷ 'o' ∷ '-' ∷ 'b' ∷ 'e' ∷ 'a' ∷ 'm' ∷ '-' ∷ 'i' ∷ 'm' ∷ 'a' ∷ 'g' ∷ 'e' ∷ []

imgA : AllA imgTail
imgA = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

bdTail : List Char
bdTail = 'o' ∷ 'u' ∷ 'n' ∷ 'd' ∷ 'a' ∷ 'r' ∷ 'y' ∷ []

bdA : AllA bdTail
bdA = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

-- One definition, then a space, then the rest. The last term ends on
-- `rest`, which the caller delimits.
specDefs : ∀ t ts fr stk rest → Delim rest →
  parseGo (need (fr ∷ stk)) (showDefs (t ∷ ts) ++ rest)
  ≡ after (fr ++ sexpList (t ∷ ts)) stk rest
specDefs t [] fr stk rest d = specB t fr stk rest d
specDefs t (t2 ∷ ts) fr stk rest d = chain
  where
  restTerms = showDefs (t2 ∷ ts)
  mid = toList " " ++ restTerms
  chain =
    parseGo (need (fr ∷ stk)) (showDefs (t ∷ t2 ∷ ts) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need (fr ∷ stk)) ((showB t ++ mid) ++ rest)
      ≡⟨ push fr stk (showB t) mid rest ⟩
    parseGo (need (fr ∷ stk)) (showB t ++ (mid ++ rest))
      ≡⟨ specB t fr stk (mid ++ rest) (dsp (restTerms ++ rest)) ⟩
    after (fr ++ sexpB t ∷ []) stk (mid ++ rest)
      ≡⟨ gap (fr ++ sexpB t ∷ []) stk (restTerms ++ rest) ⟩
    parseGo (need ((fr ++ sexpB t ∷ []) ∷ stk)) (showDefs (t2 ∷ ts) ++ rest)
      ≡⟨ specDefs t2 ts (fr ++ sexpB t ∷ []) stk rest d ⟩
    after ((fr ++ (sexpB t ∷ [])) ++ sexpList (t2 ∷ ts)) stk rest
      ≡⟨ cong (λ zs → after zs stk rest)
           (++-assoc fr (sexpB t ∷ []) (sexpList (t2 ∷ ts))) ⟩
    after (fr ++ sexpList (t ∷ t2 ∷ ts)) stk rest
      ∎

image-go : ∀ i → parseGo top (render i) ≡ ok (sexpImage i , '\n' ∷ [])
image-go i = onDefs (defs i) refl
  where
  -- `rewrite` does not reach a `where` block, and `render i` stays
  -- stuck on `defs i` there. The chains are on a concrete list.
  -- `subst` puts `defs i` back.
  goal : List (BTm 0) → Set
  goal zs =
    parseGo top (renderWith zs (format i) (boundary i) (term i))
    ≡ ok (sexpWith zs (format i) (boundary i) (term i) , '\n' ∷ [])

  empty-go : goal []
  empty-go = chain
    where
      fmt = showNat (format i)
      bv = showNat (boundary i)
      tm = showB (term i)
      nl = toList "\n"
      w3 = toList " (done))))" ++ nl
      w2 = toList ") (entry (seq " ++ (tm ++ w3)
      w1 = toList " (boundary " ++ (bv ++ w2)
      ak = atom (toList "muro-beam-image")
      ab = atom (toList "boundary")
      ae = atom (toList "entry")
      asq = atom (toList "seq")
      ad = atom (toList "done")
      fFmt = ak ∷ atom fmt ∷ []
      bdN = nest (ab ∷ atom bv ∷ [])
      fImg = ak ∷ atom fmt ∷ bdN ∷ []
      entryTail = toList " (entry (seq " ++ (tm ++ w3)
      seqLit = toList "(seq " ++ (tm ++ w3)
      termRest = tm ++ w3
      doneLit = toList "(done))))" ++ nl
      doneBody = toList "done))))" ++ nl
      closes = ')' ∷ ')' ∷ ')' ∷ ')' ∷ nl
      afterDone = ')' ∷ ')' ∷ ')' ∷ nl
      afterSeq = ')' ∷ ')' ∷ nl
      afterEntry = ')' ∷ nl
      seqFr = asq ∷ sexpB (term i) ∷ []
      seqFull = asq ∷ sexpB (term i) ∷ nest (ad ∷ []) ∷ []
      enFr = ae ∷ []
      enFull = ae ∷ nest seqFull ∷ []
      chain =
        parseGo top (renderWith [] (format i) (boundary i) (term i))
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ [])) (toList "muro-beam-image " ++ (fmt ++ w1))
          ≡⟨ eatKw 'm' imgTail [] [] (fmt ++ w1) refl imgA ⟩
        parseGo (need ((ak ∷ []) ∷ [])) (fmt ++ w1)
          ≡⟨ specNat (format i) (ak ∷ []) [] w1 (dsp (toList "(boundary " ++ (bv ++ w2))) ⟩
        after fFmt [] w1
          ≡⟨ gap fFmt [] (toList "(boundary " ++ (bv ++ w2)) ⟩
        parseGo (need (fFmt ∷ [])) (toList "(boundary " ++ (bv ++ w2))
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ fFmt ∷ [])) (toList "boundary " ++ (bv ++ w2))
          ≡⟨ eatKw 'b' bdTail [] (fFmt ∷ []) (bv ++ w2) refl bdA ⟩
        parseGo (need ((ab ∷ []) ∷ fFmt ∷ [])) (bv ++ w2)
          ≡⟨ specNat (boundary i) (ab ∷ []) (fFmt ∷ []) w2 (drp entryTail) ⟩
        after (ab ∷ atom bv ∷ []) (fFmt ∷ []) w2
          ≡⟨ shut (ab ∷ atom bv ∷ []) fFmt [] entryTail ⟩
        after fImg [] entryTail
          ≡⟨ gap fImg [] (toList "(entry (seq " ++ (tm ++ w3)) ⟩
        parseGo (need (fImg ∷ [])) (toList "(entry (seq " ++ (tm ++ w3))
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ fImg ∷ [])) (toList "entry (seq " ++ (tm ++ w3))
          ≡⟨ eatKw 'e' ('n' ∷ 't' ∷ 'r' ∷ 'y' ∷ []) [] (fImg ∷ []) seqLit refl (refl ∷ refl ∷ refl ∷ refl ∷ []) ⟩
        parseGo (need (enFr ∷ fImg ∷ [])) seqLit
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ enFr ∷ fImg ∷ [])) (toList "seq " ++ termRest)
          ≡⟨ eatKw 's' ('e' ∷ 'q' ∷ []) [] (enFr ∷ fImg ∷ []) termRest refl (refl ∷ refl ∷ []) ⟩
        parseGo (need ((asq ∷ []) ∷ enFr ∷ fImg ∷ [])) termRest
          ≡⟨ specB (term i) (asq ∷ []) (enFr ∷ fImg ∷ []) w3 (dsp doneLit) ⟩
        after seqFr (enFr ∷ fImg ∷ []) w3
          ≡⟨ gap seqFr (enFr ∷ fImg ∷ []) doneLit ⟩
        parseGo (need (seqFr ∷ enFr ∷ fImg ∷ [])) doneLit
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ seqFr ∷ enFr ∷ fImg ∷ [])) doneBody
          ≡⟨ specAtom 'd' ('o' ∷ 'n' ∷ 'e' ∷ []) [] (seqFr ∷ enFr ∷ fImg ∷ []) closes refl (refl ∷ refl ∷ refl ∷ []) (drp afterDone) ⟩
        after (ad ∷ []) (seqFr ∷ enFr ∷ fImg ∷ []) closes
          ≡⟨ shut (ad ∷ []) seqFr (enFr ∷ fImg ∷ []) afterDone ⟩
        after seqFull (enFr ∷ fImg ∷ []) afterDone
          ≡⟨ shut seqFull enFr (fImg ∷ []) afterSeq ⟩
        after enFull (fImg ∷ []) afterSeq
          ≡⟨ shut enFull fImg [] afterEntry ⟩
        after (fImg ++ (nest enFull ∷ [])) [] afterEntry
          ≡⟨ shut1 (fImg ++ (nest enFull ∷ [])) nl ⟩
        ok (sexpWith [] (format i) (boundary i) (term i) , nl)
          ∎

  cons-go : (d : BTm 0) (ds : List (BTm 0)) → goal (d ∷ ds)
  cons-go d ds = chain
    where
      fmt = showNat (format i)
      bv = showNat (boundary i)
      tm = showB (term i)
      nl = toList "\n"
      w3 = toList " (done))))" ++ nl
      entryAfter = toList ") (entry (seq " ++ (tm ++ w3)
      defsTxt = showDefs (d ∷ ds)
      w2 = toList ") (defs " ++ (defsTxt ++ entryAfter)
      w1 = toList " (boundary " ++ (bv ++ w2)
      ak = atom (toList "muro-beam-image")
      ab = atom (toList "boundary")
      adef = atom (toList "defs")
      ae = atom (toList "entry")
      asq = atom (toList "seq")
      ad = atom (toList "done")
      fFmt = ak ∷ atom fmt ∷ []
      bdN = nest (ab ∷ atom bv ∷ [])
      fImg = ak ∷ atom fmt ∷ bdN ∷ []
      openDefs = toList " (defs " ++ (defsTxt ++ entryAfter)
      kwDefs = toList "defs " ++ (defsTxt ++ entryAfter)
      defsFr = adef ∷ sexpList (d ∷ ds)
      fImgD = fImg ++ (nest defsFr ∷ [])
      entryRest = toList " (entry (seq " ++ (tm ++ w3)
      entryLit = toList "(entry (seq " ++ (tm ++ w3)
      seqLit = toList "(seq " ++ (tm ++ w3)
      termRest = tm ++ w3
      doneLit = toList "(done))))" ++ nl
      doneBody = toList "done))))" ++ nl
      closes = ')' ∷ ')' ∷ ')' ∷ ')' ∷ nl
      afterDone = ')' ∷ ')' ∷ ')' ∷ nl
      afterSeq = ')' ∷ ')' ∷ nl
      afterEntry = ')' ∷ nl
      seqFr = asq ∷ sexpB (term i) ∷ []
      seqFull = asq ∷ sexpB (term i) ∷ nest (ad ∷ []) ∷ []
      enFr = ae ∷ []
      enFull = ae ∷ nest seqFull ∷ []
      chain =
        parseGo top (renderWith (d ∷ ds) (format i) (boundary i) (term i))
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ [])) (toList "muro-beam-image " ++ (fmt ++ w1))
          ≡⟨ eatKw 'm' imgTail [] [] (fmt ++ w1) refl imgA ⟩
        parseGo (need ((ak ∷ []) ∷ [])) (fmt ++ w1)
          ≡⟨ specNat (format i) (ak ∷ []) [] w1 (dsp (toList "(boundary " ++ (bv ++ w2))) ⟩
        after fFmt [] w1
          ≡⟨ gap fFmt [] (toList "(boundary " ++ (bv ++ w2)) ⟩
        parseGo (need (fFmt ∷ [])) (toList "(boundary " ++ (bv ++ w2))
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ fFmt ∷ [])) (toList "boundary " ++ (bv ++ w2))
          ≡⟨ eatKw 'b' bdTail [] (fFmt ∷ []) (bv ++ w2) refl bdA ⟩
        parseGo (need ((ab ∷ []) ∷ fFmt ∷ [])) (bv ++ w2)
          ≡⟨ specNat (boundary i) (ab ∷ []) (fFmt ∷ []) w2 (drp openDefs) ⟩
        after (ab ∷ atom bv ∷ []) (fFmt ∷ []) w2
          ≡⟨ shut (ab ∷ atom bv ∷ []) fFmt [] openDefs ⟩
        after fImg [] openDefs
          ≡⟨ gap fImg [] (toList "(defs " ++ (defsTxt ++ entryAfter)) ⟩
        parseGo (need (fImg ∷ [])) (toList "(defs " ++ (defsTxt ++ entryAfter))
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ fImg ∷ [])) kwDefs
          ≡⟨ eatKw 'd' ('e' ∷ 'f' ∷ 's' ∷ []) [] (fImg ∷ []) (defsTxt ++ entryAfter) refl (refl ∷ refl ∷ refl ∷ []) ⟩
        parseGo (need ((adef ∷ []) ∷ fImg ∷ [])) (defsTxt ++ entryAfter)
          ≡⟨ specDefs d ds (adef ∷ []) (fImg ∷ []) entryAfter (drp entryRest) ⟩
        after defsFr (fImg ∷ []) entryAfter
          ≡⟨ shut defsFr fImg [] entryRest ⟩
        after fImgD [] entryRest
          ≡⟨ gap fImgD [] entryLit ⟩
        parseGo (need (fImgD ∷ [])) entryLit
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ fImgD ∷ [])) (toList "entry (seq " ++ (tm ++ w3))
          ≡⟨ eatKw 'e' ('n' ∷ 't' ∷ 'r' ∷ 'y' ∷ []) [] (fImgD ∷ []) seqLit refl (refl ∷ refl ∷ refl ∷ refl ∷ []) ⟩
        parseGo (need (enFr ∷ fImgD ∷ [])) seqLit
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ enFr ∷ fImgD ∷ [])) (toList "seq " ++ termRest)
          ≡⟨ eatKw 's' ('e' ∷ 'q' ∷ []) [] (enFr ∷ fImgD ∷ []) termRest refl (refl ∷ refl ∷ []) ⟩
        parseGo (need ((asq ∷ []) ∷ enFr ∷ fImgD ∷ [])) termRest
          ≡⟨ specB (term i) (asq ∷ []) (enFr ∷ fImgD ∷ []) w3 (dsp doneLit) ⟩
        after seqFr (enFr ∷ fImgD ∷ []) w3
          ≡⟨ gap seqFr (enFr ∷ fImgD ∷ []) doneLit ⟩
        parseGo (need (seqFr ∷ enFr ∷ fImgD ∷ [])) doneLit
          ≡⟨ refl ⟩
        parseGo (need ([] ∷ seqFr ∷ enFr ∷ fImgD ∷ [])) doneBody
          ≡⟨ specAtom 'd' ('o' ∷ 'n' ∷ 'e' ∷ []) [] (seqFr ∷ enFr ∷ fImgD ∷ []) closes refl (refl ∷ refl ∷ refl ∷ []) (drp afterDone) ⟩
        after (ad ∷ []) (seqFr ∷ enFr ∷ fImgD ∷ []) closes
          ≡⟨ shut (ad ∷ []) seqFr (enFr ∷ fImgD ∷ []) afterDone ⟩
        after seqFull (enFr ∷ fImgD ∷ []) afterDone
          ≡⟨ shut seqFull enFr (fImgD ∷ []) afterSeq ⟩
        after enFull (fImgD ∷ []) afterSeq
          ≡⟨ shut enFull fImgD [] afterEntry ⟩
        after (fImgD ++ (nest enFull ∷ [])) [] afterEntry
          ≡⟨ shut1 (fImgD ++ (nest enFull ∷ [])) nl ⟩
        ok (sexpWith (d ∷ ds) (format i) (boundary i) (term i) , nl)
          ∎

  onDefs : (ds : List (BTm 0)) → defs i ≡ ds →
           parseGo top (render i) ≡ ok (sexpImage i , '\n' ∷ [])
  onDefs [] eq = subst goal (sym eq) empty-go
  onDefs (d ∷ ds) eq = subst goal (sym eq) (cons-go d ds)

parse-show : ∀ i → parseCs (render i) ≡ ok i
parse-show i = trans (cong finish (image-go i)) (fromImage-ok i)
