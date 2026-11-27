------------------------------------------------------------------------
-- Image format. v1 is the text muro emits (manual/mbi.md at 3f1cae2):
-- one line, tokens separated by one space, a trailing newline, and
-- `(seq <term> (done))` with no definitions. v2 is that line plus a
-- `(defs <term> …)` section between the boundary and the entry. v3
-- (B4a) is the v1/v2 grammar; the number only asks the loader for the
-- host console at pid 1 (`MuroBeam.Load.loadIO`, `MuroBeam.Port`).
-- An empty definition list is printed in the v1 shape, with no defs
-- section. The format number is the number that was read, not a
-- forced 1, so a v1, v2, or v3 file round-trips to the same bytes. Grades are
-- points or `(iv a b)`. `w` is ω.
-- `gze` is bare. De Bruijn indices and `gref` indices are decimal,
-- with no leading zero except 0.
--
-- `showImage` is `fromList` of `render`. The round trip is proved on
-- `render` in `MuroBeam.Parse`. `toList ∘ fromList` is not a --safe
-- lemma in the standard library.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module MuroBeam.Image where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Char.Base using (Char)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; length; reverse; reverseAcc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.String.Base using (String; fromList; toList)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Grade using (Point; fin; inf; Grade; pt; iv)
open import MuroBeam.BTm using
  ( BTm; Arm; arm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch; gref; gcon; gcase )
open import MuroBeam.PSyntax using (Thin; t[]; keep; skip)

------------------------------------------------------------------------
-- Surface process term. `awaitT`, `ignoreT`, `flushT`, `ncheckT`,
-- and `ndemonT` are not here. `markProto` writes `awaitT`,
-- `ignoreT`, and `ncheckT` once a moved reply has an object index.
-- `arm1` turns `ignoreT` into `flushT`. `npeek1` turns `ncheckT`
-- into `ndemonT` when the mailbox does not hold the tag. A `seq`
-- in the file carries no
-- definition list: the image `(defs …)` section is the root seq's
-- list, and load attaches it. A nested seq has an empty list.
------------------------------------------------------------------------

data SPtm (n : ℕ) : Set where
  sdone    : SPtm n
  ssend    : ℕ → Fin n → SPtm n → SPtm n
  srecv    : Grade → Grade → SPtm (suc n) → SPtm n
  sspawn   : ∀ {m} → Thin m n → SPtm m → SPtm n → SPtm n
  sseq     : BTm n → SPtm (suc n) → SPtm n
  sawait   : Fin n → SPtm n → SPtm n
  signore  : Fin n → SPtm n → SPtm n
  snignore : Fin n → SPtm n → SPtm n

-- `(seq <btm> (done))` is the pure entry. Anything else is a process.
isLegacy : SPtm 0 → Bool
isLegacy (sseq _ sdone) = true
isLegacy _               = false

------------------------------------------------------------------------
-- The file. The loader accepts format 1, 2, and 3, and boundary
-- version 1. Format 3 is the format-1/2 grammar with the host console
-- at pid 1 (B4a, `MuroBeam.Port`); the parser and printer read and
-- reprint the number and do not treat it differently. `defs` is the
-- code segment. `entry` is the process.
-- A legacy entry is `sseq term sdone`, and the checked program is
-- `seq defs term done`. A `(defs …)` section on any other entry is
-- refused: the section attaches only to that root seq.
------------------------------------------------------------------------

format-version : ℕ
format-version = 1

record Image : Set where
  constructor mk
  field
    format   : ℕ
    boundary : ℕ
    defs     : List (BTm 0)
    entry    : SPtm 0

open Image public

------------------------------------------------------------------------
-- Decimal. Least-significant digit first, by adding one, then reverse.
-- The recursion is structural. `read-show` is the inverse, and a
-- positive numeral does not start with 0.
------------------------------------------------------------------------

dval : Char → ℕ
dval '0' = 0
dval '1' = 1
dval '2' = 2
dval '3' = 3
dval '4' = 4
dval '5' = 5
dval '6' = 6
dval '7' = 7
dval '8' = 8
dval '9' = 9
dval _   = 0

data Dig : Char → Set where
  D0 : Dig '0'
  D1 : Dig '1'
  D2 : Dig '2'
  D3 : Dig '3'
  D4 : Dig '4'
  D5 : Dig '5'
  D6 : Dig '6'
  D7 : Dig '7'
  D8 : Dig '8'
  D9 : Dig '9'

data NZD : Char → Set where
  Z1 : NZD '1'
  Z2 : NZD '2'
  Z3 : NZD '3'
  Z4 : NZD '4'
  Z5 : NZD '5'
  Z6 : NZD '6'
  Z7 : NZD '7'
  Z8 : NZD '8'
  Z9 : NZD '9'

data AllD : List Char → Set where
  []  : AllD []
  _∷_ : ∀ {c cs} → Dig c → AllD cs → AllD (c ∷ cs)

inc : List Char → List Char
inc []          = '1' ∷ []
inc ('0' ∷ cs)  = '1' ∷ cs
inc ('1' ∷ cs)  = '2' ∷ cs
inc ('2' ∷ cs)  = '3' ∷ cs
inc ('3' ∷ cs)  = '4' ∷ cs
inc ('4' ∷ cs)  = '5' ∷ cs
inc ('5' ∷ cs)  = '6' ∷ cs
inc ('6' ∷ cs)  = '7' ∷ cs
inc ('7' ∷ cs)  = '8' ∷ cs
inc ('8' ∷ cs)  = '9' ∷ cs
inc ('9' ∷ cs)  = '0' ∷ inc cs
inc (_ ∷ _)     = '1' ∷ []

toLSB : ℕ → List Char
toLSB zero    = '0' ∷ []
toLSB (suc n) = inc (toLSB n)

showNat : ℕ → List Char
showNat n = reverse (toLSB n)

digit? : Char → Bool
digit? '0' = true
digit? '1' = true
digit? '2' = true
digit? '3' = true
digit? '4' = true
digit? '5' = true
digit? '6' = true
digit? '7' = true
digit? '8' = true
digit? '9' = true
digit? _   = false

nz? : Char → Bool
nz? '1' = true
nz? '2' = true
nz? '3' = true
nz? '4' = true
nz? '5' = true
nz? '6' = true
nz? '7' = true
nz? '8' = true
nz? '9' = true
nz? _   = false

allDigit? : List Char → Bool
allDigit? []       = true
allDigit? (c ∷ cs) = digit? c ∧ allDigit? cs

-- "0", or a numeral whose first digit is 1–9.
canon? : List Char → Bool
canon? []             = false
canon? ('0' ∷ [])     = true
canon? ('0' ∷ _ ∷ _)  = false
canon? (c ∷ cs)       = nz? c ∧ allDigit? cs

go : ℕ → List Char → ℕ
go acc []       = acc
go acc (c ∷ cs) = go (acc * 10 + dval c) cs

mval : List Char → ℕ
mval = go 0

val : List Char → ℕ
val []       = 0
val (c ∷ cs) = dval c + val cs * 10

readNatAtom : List Char → Maybe ℕ
readNatAtom ds with canon? ds
... | true  = just (mval ds)
... | false = nothing

------------------------------------------------------------------------
-- Arithmetic for the numeral inverse. Local, so the book does not
-- import Data.Nat.Properties.
------------------------------------------------------------------------

+-idʳ : ∀ n → n + 0 ≡ n
+-idʳ zero    = refl
+-idʳ (suc n) rewrite +-idʳ n = refl

+-suc : ∀ a b → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b rewrite +-suc a b = refl

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-idʳ n)
+-comm (suc m) n rewrite +-comm m n = sym (+-suc n m)

*-zeroʳ : ∀ n → n * 0 ≡ 0
*-zeroʳ zero    = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl

*-one : ∀ n → n * 1 ≡ n
*-one zero    = refl
*-one (suc n) rewrite *-one n = refl

*-suc : ∀ a b → a * suc b ≡ a + a * b
*-suc zero    b = refl
*-suc (suc a) b rewrite *-suc a b =
  trans (cong suc (sym (+-assoc b a (a * b))))
  (trans (cong (λ z → suc (z + a * b)) (+-comm b a))
         (cong suc (+-assoc a b (a * b))))

*-comm : ∀ a b → a * b ≡ b * a
*-comm zero    b = sym (*-zeroʳ b)
*-comm (suc a) b rewrite *-comm a b | *-suc b a = refl

distrib : ∀ a b c → (a + b) * c ≡ a * c + b * c
distrib zero    b c = refl
distrib (suc a) b c rewrite distrib a b c | +-assoc c (a * c) (b * c) = refl

*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc zero    b c = refl
*-assoc (suc a) b c rewrite distrib b (a * b) c | *-assoc a b c = refl

pow10 : ℕ → ℕ
pow10 zero    = 1
pow10 (suc n) = pow10 n * 10

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_∎ : ∀ {A : Set} (x : A) → x ≡ x
_ ∎ = refl

infixl 3 _∎

go-acc : ∀ n xs → go n xs ≡ n * pow10 (length xs) + mval xs
go-acc n [] rewrite *-one n | +-idʳ n = refl
go-acc n (c ∷ cs) =
  let p = pow10 (length cs) in
  go (n * 10 + dval c) cs
    ≡⟨ go-acc (n * 10 + dval c) cs ⟩
  (n * 10 + dval c) * p + mval cs
    ≡⟨ cong (_+ mval cs) (distrib (n * 10) (dval c) p) ⟩
  ((n * 10) * p + dval c * p) + mval cs
    ≡⟨ +-assoc ((n * 10) * p) (dval c * p) (mval cs) ⟩
  (n * 10) * p + (dval c * p + mval cs)
    ≡⟨ cong (λ z → z + (dval c * p + mval cs)) (*-assoc n 10 p) ⟩
  n * (10 * p) + (dval c * p + mval cs)
    ≡⟨ cong (λ z → n * z + (dval c * p + mval cs)) (*-comm 10 p) ⟩
  n * (p * 10) + (dval c * p + mval cs)
    ≡⟨ refl ⟩
  n * pow10 (suc (length cs)) + (dval c * p + mval cs)
    ≡⟨ cong (n * pow10 (suc (length cs)) +_) (sym (go-acc (dval c) cs)) ⟩
  n * pow10 (length (c ∷ cs)) + mval (c ∷ cs)
    ∎

mval-revAcc : ∀ acc xs →
  mval (reverseAcc acc xs) ≡ val xs * pow10 (length acc) + mval acc
mval-revAcc acc [] = refl
mval-revAcc acc (c ∷ cs) =
  let k = length acc
      p = pow10 k
      a = dval c
      b = val cs
  in
  mval (reverseAcc (c ∷ acc) cs)
    ≡⟨ mval-revAcc (c ∷ acc) cs ⟩
  b * pow10 (length (c ∷ acc)) + mval (c ∷ acc)
    ≡⟨ cong (b * pow10 (suc k) +_) (go-acc (dval c) acc) ⟩
  b * (p * 10) + (a * p + mval acc)
    ≡⟨ sym (+-assoc (b * (p * 10)) (a * p) (mval acc)) ⟩
  (b * (p * 10) + a * p) + mval acc
    ≡⟨ cong (_+ mval acc) (cong (_+ a * p) (sym (*-assoc b p 10))) ⟩
  ((b * p) * 10 + a * p) + mval acc
    ≡⟨ cong (_+ mval acc) (+-comm ((b * p) * 10) (a * p)) ⟩
  (a * p + (b * p) * 10) + mval acc
    ≡⟨ cong (_+ mval acc) (cong (a * p +_) (*-assoc b p 10)) ⟩
  (a * p + b * (p * 10)) + mval acc
    ≡⟨ cong (_+ mval acc) (cong (a * p +_) (cong (b *_) (*-comm p 10))) ⟩
  (a * p + b * (10 * p)) + mval acc
    ≡⟨ cong (_+ mval acc) (cong (a * p +_) (sym (*-assoc b 10 p))) ⟩
  (a * p + (b * 10) * p) + mval acc
    ≡⟨ cong (_+ mval acc) (sym (distrib a (b * 10) p)) ⟩
  (a + b * 10) * p + mval acc
    ≡⟨ refl ⟩
  val (c ∷ cs) * pow10 (length acc) + mval acc
    ∎

mval≡val : ∀ xs → mval (reverse xs) ≡ val xs
mval≡val xs rewrite mval-revAcc [] xs | *-one (val xs) | +-idʳ (val xs) = refl

------------------------------------------------------------------------
-- Digits of the LSB strings, and a nonzero high digit after zero.
------------------------------------------------------------------------

inc-dig : ∀ {c cs} → Dig c → AllD cs → AllD (inc (c ∷ cs))
inc-dig D0 ds = D1 ∷ ds
inc-dig D1 ds = D2 ∷ ds
inc-dig D2 ds = D3 ∷ ds
inc-dig D3 ds = D4 ∷ ds
inc-dig D4 ds = D5 ∷ ds
inc-dig D5 ds = D6 ∷ ds
inc-dig D6 ds = D7 ∷ ds
inc-dig D7 ds = D8 ∷ ds
inc-dig D8 ds = D9 ∷ ds
inc-dig D9 ds = D0 ∷ inc-all ds
  where
  inc-all : ∀ {xs} → AllD xs → AllD (inc xs)
  inc-all []       = D1 ∷ []
  inc-all (d ∷ ds) = inc-dig d ds

lsb-dig : ∀ n → AllD (toLSB n)
lsb-dig zero    = D0 ∷ []
lsb-dig (suc n) = step (lsb-dig n)
  where
  step : ∀ {xs} → AllD xs → AllD (inc xs)
  step []       = D1 ∷ []
  step (d ∷ ds) = inc-dig d ds

val-inc : ∀ {xs} → AllD xs → val (inc xs) ≡ suc (val xs)
val-inc []         = refl
val-inc (D0 ∷ _)   = refl
val-inc (D1 ∷ _)   = refl
val-inc (D2 ∷ _)   = refl
val-inc (D3 ∷ _)   = refl
val-inc (D4 ∷ _)   = refl
val-inc (D5 ∷ _)   = refl
val-inc (D6 ∷ _)   = refl
val-inc (D7 ∷ _)   = refl
val-inc (D8 ∷ _)   = refl
val-inc (D9 ∷ ds) rewrite val-inc ds = refl

val-lsb : ∀ n → val (toLSB n) ≡ n
val-lsb zero    = refl
val-lsb (suc n) rewrite val-inc (lsb-dig n) | val-lsb n = refl

-- A positive LSB numeral ends in a digit 1–9. That digit is the
-- high digit of `showNat`.
data LastNZ : List Char → Set where
  here  : ∀ {c} → NZD c → LastNZ (c ∷ [])
  there : ∀ {b cs} → Dig b → LastNZ cs → LastNZ (b ∷ cs)

inc-last : ∀ {xs} → AllD xs → LastNZ xs → LastNZ (inc xs)
inc-last [] ()
inc-last (D0 ∷ []) (here ())
inc-last (D1 ∷ []) (here _) = here Z2
inc-last (D2 ∷ []) (here _) = here Z3
inc-last (D3 ∷ []) (here _) = here Z4
inc-last (D4 ∷ []) (here _) = here Z5
inc-last (D5 ∷ []) (here _) = here Z6
inc-last (D6 ∷ []) (here _) = here Z7
inc-last (D7 ∷ []) (here _) = here Z8
inc-last (D8 ∷ []) (here _) = here Z9
inc-last (D9 ∷ []) (here _) = there D0 (here Z1)
inc-last (D0 ∷ d ∷ ds) (there _ nz) = there D1 nz
inc-last (D1 ∷ d ∷ ds) (there _ nz) = there D2 nz
inc-last (D2 ∷ d ∷ ds) (there _ nz) = there D3 nz
inc-last (D3 ∷ d ∷ ds) (there _ nz) = there D4 nz
inc-last (D4 ∷ d ∷ ds) (there _ nz) = there D5 nz
inc-last (D5 ∷ d ∷ ds) (there _ nz) = there D6 nz
inc-last (D6 ∷ d ∷ ds) (there _ nz) = there D7 nz
inc-last (D7 ∷ d ∷ ds) (there _ nz) = there D8 nz
inc-last (D8 ∷ d ∷ ds) (there _ nz) = there D9 nz
inc-last (D9 ∷ d ∷ ds) (there _ nz) = there D0 (inc-last (d ∷ ds) nz)

pos-last : ∀ n → LastNZ (toLSB (suc n))
pos-last zero    = here Z1
pos-last (suc n) = inc-last (lsb-dig (suc n)) (pos-last n)

revAcc-++ : ∀ {A : Set} acc (xs ys : List A) →
  reverseAcc acc (xs ++ ys) ≡ reverseAcc (reverseAcc acc xs) ys
revAcc-++ acc []       ys = refl
revAcc-++ acc (x ∷ xs) ys = revAcc-++ (x ∷ acc) xs ys

rev-snoc : ∀ {A : Set} (xs : List A) (y : A) →
  reverse (xs ++ y ∷ []) ≡ y ∷ reverse xs
rev-snoc xs y rewrite revAcc-++ [] xs (y ∷ []) = refl

dig? : ∀ {c} → Dig c → digit? c ≡ true
dig? D0 = refl
dig? D1 = refl
dig? D2 = refl
dig? D3 = refl
dig? D4 = refl
dig? D5 = refl
dig? D6 = refl
dig? D7 = refl
dig? D8 = refl
dig? D9 = refl

nz-ok : ∀ {c} → NZD c → nz? c ≡ true
nz-ok Z1 = refl
nz-ok Z2 = refl
nz-ok Z3 = refl
nz-ok Z4 = refl
nz-ok Z5 = refl
nz-ok Z6 = refl
nz-ok Z7 = refl
nz-ok Z8 = refl
nz-ok Z9 = refl

all? : ∀ {xs} → AllD xs → allDigit? xs ≡ true
all? []       = refl
all? (d ∷ ds) rewrite dig? d | all? ds = refl

allD-revAcc : ∀ {acc xs} → AllD acc → AllD xs → AllD (reverseAcc acc xs)
allD-revAcc ad []         = ad
allD-revAcc ad (d ∷ ds)   = allD-revAcc (d ∷ ad) ds

allD-reverse : ∀ {xs} → AllD xs → AllD (reverse xs)
allD-reverse ad = allD-revAcc [] ad

front : ∀ {z} (cs : List Char) → AllD (cs ++ z ∷ []) → AllD cs
front {z} cs ad = strip z cs ad refl
  where
  strip : ∀ z cs {ys} → AllD ys → ys ≡ cs ++ z ∷ [] → AllD cs
  strip z []       _       refl = []
  strip z (c ∷ cs) (d ∷ ad) refl = d ∷ strip z cs ad refl

record Snoc (xs : List Char) : Set where
  constructor snoc
  field
    pre : List Char
    hd  : Char
    nz  : NZD hd
    eq  : xs ≡ pre ++ hd ∷ []

toSnoc : ∀ {xs} → LastNZ xs → Snoc xs
toSnoc (here nz) = snoc [] _ nz refl
toSnoc (there {b} {cs} _ nz) with toSnoc nz
... | snoc pre hd nz' eq rewrite eq = snoc (b ∷ pre) hd nz' refl

canon-nz : ∀ {c cs} → NZD c → allDigit? cs ≡ true → canon? (c ∷ cs) ≡ true
canon-nz Z1 eq rewrite eq = refl
canon-nz Z2 eq rewrite eq = refl
canon-nz Z3 eq rewrite eq = refl
canon-nz Z4 eq rewrite eq = refl
canon-nz Z5 eq rewrite eq = refl
canon-nz Z6 eq rewrite eq = refl
canon-nz Z7 eq rewrite eq = refl
canon-nz Z8 eq rewrite eq = refl
canon-nz Z9 eq rewrite eq = refl

canon-snoc : ∀ pre hd → NZD hd → AllD (pre ++ hd ∷ []) →
            canon? (reverse (pre ++ hd ∷ [])) ≡ true
canon-snoc pre hd nz ad =
  subst (λ zs → canon? zs ≡ true) (sym (rev-snoc pre hd))
        (canon-nz nz (all? (allD-reverse (front pre ad))))

canon-rev : ∀ {xs} → AllD xs → LastNZ xs → canon? (reverse xs) ≡ true
canon-rev ad nz with toSnoc nz
... | snoc pre hd nz' eq =
  subst (λ zs → canon? (reverse zs) ≡ true) (sym eq)
        (canon-snoc pre hd nz' (subst AllD eq ad))

read-show : ∀ n → readNatAtom (showNat n) ≡ just n
read-show zero = refl
read-show (suc n)
  rewrite canon-rev (lsb-dig (suc n)) (pos-last n)
        | mval≡val (toLSB (suc n))
        | val-lsb (suc n)
  = refl

------------------------------------------------------------------------
-- Printer.
------------------------------------------------------------------------

showPoint : Point → List Char
showPoint (fin n) = showNat n
showPoint inf     = toList "w"

showGrade : Grade → List Char
showGrade (pt p)   = showPoint p
showGrade (iv a b) =
  toList "(iv " ++ showPoint a ++ toList " " ++ showPoint b ++ toList ")"

showPair : Grade → Grade → List Char
showPair c t =
  toList "(" ++ showGrade c ++ toList " " ++ showGrade t ++ toList ")"

mutual
  showB : ∀ {n} → BTm n → List Char
  showB (gvar x) = toList "(gvar " ++ showNat (toℕ x) ++ toList ")"
  showB (gtyp x) = toList "(gtyp " ++ showNat (toℕ x) ++ toList ")"
  showB (glam c t b) =
    toList "(glam " ++ showPair c t ++ toList " " ++ showB b ++ toList ")"
  showB (gpi c t b) =
    toList "(gpi " ++ showPair c t ++ toList " " ++ showB b ++ toList ")"
  showB (gapp f a) =
    toList "(gapp " ++ showB f ++ toList " " ++ showB a ++ toList ")"
  showB gze = toList "gze"
  showB (gsu e) = toList "(gsu " ++ showB e ++ toList ")"
  showB (gmatch e z s) =
    toList "(gmatch " ++ showB e ++ toList " " ++ showB z
      ++ toList " " ++ showB s ++ toList ")"
  showB (gref k) = toList "(gref " ++ showNat k ++ toList ")"
  showB (gcon t es) =
    toList "(gcon " ++ showNat t ++ showBArgs es ++ toList ")"
  showB (gcase e as) =
    toList "(gcase " ++ showB e ++ showBArms as ++ toList ")"

  showBArgs : ∀ {n} → List (BTm n) → List Char
  showBArgs [] = []
  showBArgs (e ∷ es) = toList " " ++ showB e ++ showBArgs es

  showBArm : ∀ {n} → Arm n → List Char
  showBArm (arm t k b) =
    toList "(garm " ++ showNat t ++ toList " " ++ showNat k
      ++ toList " " ++ showB b ++ toList ")"

  showBArms : ∀ {n} → List (Arm n) → List Char
  showBArms [] = []
  showBArms (a ∷ as) = toList " " ++ showBArm a ++ showBArms as

-- Right-associated, so a parser proof can split off one term.
showDefs : List (BTm 0) → List Char
showDefs [] = []
showDefs (t ∷ []) = showB t
showDefs (t ∷ t2 ∷ ts) = showB t ++ (toList " " ++ showDefs (t2 ∷ ts))

showThin : ∀ {m n} → Thin m n → List Char
showThin t[]        = toList "t[]"
showThin (keep th)  = toList "(keep " ++ showThin th ++ toList ")"
showThin (skip th)  = toList "(skip " ++ showThin th ++ toList ")"

showS : ∀ {n} → SPtm n → List Char
showS sdone = toList "(done)"
showS (ssend j x k) =
  toList "(send " ++ showNat j ++ toList " " ++ showNat (toℕ x)
  ++ toList " " ++ showS k ++ toList ")"
showS (srecv c t k) =
  toList "(recv " ++ showPair c t ++ toList " " ++ showS k ++ toList ")"
showS (sspawn th ch pa) =
  toList "(spawn " ++ showThin th ++ toList " " ++ showS ch
  ++ toList " " ++ showS pa ++ toList ")"
showS (sseq e k) =
  toList "(seq " ++ showB e ++ toList " " ++ showS k ++ toList ")"
showS (sawait x k) =
  toList "(await " ++ showNat (toℕ x) ++ toList " " ++ showS k ++ toList ")"
showS (signore x k) =
  toList "(ignore " ++ showNat (toℕ x) ++ toList " " ++ showS k ++ toList ")"
showS (snignore x k) =
  toList "(nignore " ++ showNat (toℕ x) ++ toList " " ++ showS k ++ toList ")"

-- Empty `defs` omits the section. A cons prints the defs section.
-- The format number is the field, not this choice: a v1 file has
-- empty `defs` and reprints without a section, and a format-2
-- record with an empty list reprints number 2.
renderWith : List (BTm 0) → ℕ → ℕ → BTm 0 → List Char
renderWith [] fv bv tm =
  toList "(muro-beam-image " ++ showNat fv
  ++ toList " (boundary " ++ showNat bv
  ++ toList ") (entry (seq " ++ showB tm
  ++ toList " (done))))"
  ++ toList "\n"
renderWith (d ∷ ds) fv bv tm =
  toList "(muro-beam-image " ++ showNat fv
  ++ toList " (boundary " ++ showNat bv
  ++ toList ") (defs " ++ showDefs (d ∷ ds)
  ++ toList ") (entry (seq " ++ showB tm
  ++ toList " (done))))"
  ++ toList "\n"

-- A process entry. The legacy `(seq <btm> (done))` line stays
-- `renderWith`, so its bytes do not move.
renderGen : List (BTm 0) → ℕ → ℕ → SPtm 0 → List Char
renderGen [] fv bv p =
  toList "(muro-beam-image " ++ showNat fv
  ++ toList " (boundary " ++ showNat bv
  ++ toList ") (entry " ++ showS p
  ++ toList "))"
  ++ toList "\n"
renderGen (d ∷ ds) fv bv p =
  toList "(muro-beam-image " ++ showNat fv
  ++ toList " (boundary " ++ showNat bv
  ++ toList ") (defs " ++ showDefs (d ∷ ds)
  ++ toList ") (entry " ++ showS p
  ++ toList "))"
  ++ toList "\n"

renderAt : List (BTm 0) → ℕ → ℕ → SPtm 0 → List Char
renderAt ds fv bv (sseq tm k) with isLegacy (sseq tm k)
... | true  = renderWith ds fv bv tm
... | false = renderGen ds fv bv (sseq tm k)
renderAt ds fv bv p = renderGen ds fv bv p

render : Image → List Char
render i = renderAt (defs i) (format i) (boundary i) (entry i)

showImage : Image → String
showImage i = fromList (render i)
