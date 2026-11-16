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
open import Muro.Grade using
  ( Point; fin; inf; Grade; pt; iv
  ; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch )

open import MuroBeam.Image using
  ( Image; mk; format; boundary; term
  ; showNat; showPoint; showGrade; showPair; showGTm; render
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
  tgze tgsu tgapp tgmatch tglam tgpi tgvar tgtyp tiv tw : Tag
  timage tbound tentry tseq tdone tno : Tag

tag : List Char → Tag
tag ('g' ∷ 'z' ∷ 'e' ∷ []) = tgze
tag ('g' ∷ 's' ∷ 'u' ∷ []) = tgsu
tag ('g' ∷ 'a' ∷ 'p' ∷ 'p' ∷ []) = tgapp
tag ('g' ∷ 'm' ∷ 'a' ∷ 't' ∷ 'c' ∷ 'h' ∷ []) = tgmatch
tag ('g' ∷ 'l' ∷ 'a' ∷ 'm' ∷ []) = tglam
tag ('g' ∷ 'p' ∷ 'i' ∷ []) = tgpi
tag ('g' ∷ 'v' ∷ 'a' ∷ 'r' ∷ []) = tgvar
tag ('g' ∷ 't' ∷ 'y' ∷ 'p' ∷ []) = tgtyp
tag ('i' ∷ 'v' ∷ []) = tiv
tag ('w' ∷ []) = tw
tag ('m' ∷ 'u' ∷ 'r' ∷ 'o' ∷ '-' ∷ 'b' ∷ 'e' ∷ 'a' ∷ 'm' ∷ '-' ∷ 'i' ∷ 'm' ∷ 'a' ∷ 'g' ∷ 'e' ∷ []) = timage
tag ('b' ∷ 'o' ∷ 'u' ∷ 'n' ∷ 'd' ∷ 'a' ∷ 'r' ∷ 'y' ∷ []) = tbound
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

sexpG : ∀ {n} → GTm n → Sexp
sexpG (gvar x) = nest (atom (toList "gvar") ∷ atom (showNat (toℕ x)) ∷ [])
sexpG (gtyp x) = nest (atom (toList "gtyp") ∷ atom (showNat (toℕ x)) ∷ [])
sexpG (glam c t b) = nest (atom (toList "glam") ∷ sexpPair c t ∷ sexpG b ∷ [])
sexpG (gpi c t b) = nest (atom (toList "gpi") ∷ sexpPair c t ∷ sexpG b ∷ [])
sexpG (gapp f a) = nest (atom (toList "gapp") ∷ sexpG f ∷ sexpG a ∷ [])
sexpG gze = atom (toList "gze")
sexpG (gsu e) = nest (atom (toList "gsu") ∷ sexpG e ∷ [])
sexpG (gmatch e z s) =
  nest (atom (toList "gmatch") ∷ sexpG e ∷ sexpG z ∷ sexpG s ∷ [])

sexpImage : Image → Sexp
sexpImage i =
  nest ( atom (toList "muro-beam-image")
       ∷ atom (showNat (format i))
       ∷ nest (atom (toList "boundary") ∷ atom (showNat (boundary i)) ∷ [])
       ∷ nest (atom (toList "entry")
            ∷ nest (atom (toList "seq")
                 ∷ sexpG (term i)
                 ∷ nest (atom (toList "done") ∷ [])
                 ∷ [])
            ∷ [])
       ∷ [])

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

fromVar : ∀ {n} → (Fin n → GTm n) → List Sexp → Result (GTm n)
fromVar ctor (atom ds ∷ []) with readNatAtom ds
... | nothing = fail "junk"
... | just k with finFrom k
... | nothing = fail "out of scope"
... | just i  = ok (ctor i)
fromVar _ _ = fail "junk"

mutual
  fromG : ∀ {n} → Sexp → Result (GTm n)

  fromSu : ∀ {n} → List Sexp → Result (GTm n)
  fromSu (e ∷ []) with fromG e
  ... | ok t   = ok (gsu t)
  ... | fail e = fail e
  fromSu _ = fail "junk"

  fromApp : ∀ {n} → List Sexp → Result (GTm n)
  fromApp (f ∷ a ∷ []) with fromG f | fromG a
  ... | ok fv | ok av = ok (gapp fv av)
  ... | fail e | _    = fail e
  ... | _ | fail e    = fail e
  fromApp _ = fail "junk"

  fromMatch : ∀ {n} → List Sexp → Result (GTm n)
  fromMatch (e ∷ z ∷ s ∷ []) with fromG e | fromG z | fromG s
  ... | ok ev | ok zv | ok sv = ok (gmatch ev zv sv)
  ... | fail e | _ | _        = fail e
  ... | _ | fail e | _        = fail e
  ... | _ | _ | fail e        = fail e
  fromMatch _ = fail "junk"

  fromBind : ∀ {n} → (Grade → Grade → GTm (suc n) → GTm n) → List Sexp → Result (GTm n)
  fromBind {n} ctor (p ∷ b ∷ []) with fromPair p
  ... | fail e = fail e
  ... | ok (c , t) with fromG {suc n} b
  ... | fail e   = fail e
  ... | ok body  = ok (ctor c t body)
  fromBind _ _ = fail "junk"

  fromG (atom cs) with tag cs
  ... | tgze = ok gze
  ... | _    = fail "junk"
  fromG (nest []) = fail "junk"
  fromG (nest (atom cs ∷ xs)) with tag cs
  ... | tgsu    = fromSu xs
  ... | tgapp   = fromApp xs
  ... | tgmatch = fromMatch xs
  ... | tglam   = fromBind glam xs
  ... | tgpi    = fromBind gpi xs
  ... | tgvar   = fromVar gvar xs
  ... | tgtyp   = fromVar gtyp xs
  ... | _       = fail "junk"
  fromG (nest (_ ∷ _)) = fail "junk"

fromDone : Sexp → Result ⊤
fromDone (nest (atom k ∷ [])) with tag k
... | tdone = ok tt
... | _     = fail "junk"
fromDone _ = fail "junk"

fromSeq : Sexp → Result (GTm 0)
fromSeq (nest (atom k ∷ t ∷ d ∷ [])) with tag k
... | tseq = seqBoth (fromG t) (fromDone d)
  where
  seqBoth : Result (GTm 0) → Result ⊤ → Result (GTm 0)
  seqBoth (ok tm) (ok _)   = ok tm
  seqBoth (fail e) _       = fail e
  seqBoth (ok _) (fail e)  = fail e
... | _ = fail "junk"
fromSeq _ = fail "junk"

fromEntry : Sexp → Result (GTm 0)
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

fromImage : Sexp → Result Image
fromImage (nest (atom k ∷ atom v ∷ b ∷ e ∷ [])) with tag k
... | timage = assemble (readNatAtom v) (fromBound b) (fromEntry e)
  where
  assemble : Maybe ℕ → Result ℕ → Result (GTm 0) → Result Image
  assemble (just fv) (ok bv) (ok tm)  = ok (mk fv bv tm)
  assemble nothing _ _                = fail "junk"
  assemble (just _) (fail msg) _      = fail msg
  assemble (just _) (ok _) (fail msg) = fail msg
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

fromG-ok : ∀ {n} (t : GTm n) → fromG (sexpG t) ≡ ok t
fromG-ok gze = refl
fromG-ok (gsu e) rewrite fromG-ok e = refl
fromG-ok (gapp f a) rewrite fromG-ok f | fromG-ok a = refl
fromG-ok (gmatch e z s) rewrite fromG-ok e | fromG-ok z | fromG-ok s = refl
fromG-ok (glam c t b) rewrite fromPair-ok c t | fromG-ok b = refl
fromG-ok (gpi c t b) rewrite fromPair-ok c t | fromG-ok b = refl
fromG-ok (gvar x) rewrite read-show (toℕ x) | fin-to x = refl
fromG-ok (gtyp x) rewrite read-show (toℕ x) | fin-to x = refl

fromImage-ok : ∀ i → fromImage (sexpImage i) ≡ ok i
fromImage-ok i rewrite read-show (format i) | read-show (boundary i) | fromG-ok (term i) = refl

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

specG : ∀ {n} (t : GTm n) fr stk rest → Delim rest →
  parseGo (need (fr ∷ stk)) (showGTm t ++ rest)
  ≡ after (fr ++ sexpG t ∷ []) stk rest
specG gze fr stk rest d =
  specAtom 'g' ('z' ∷ 'e' ∷ []) fr stk rest refl (refl ∷ refl ∷ []) d
specG (gvar x) fr stk rest d = chain
  where
  kw = toList "gvar "
  body = showNat (toℕ x) ++ toList ")"
  kwF = atom (toList "gvar") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGTm (gvar x) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('v' ∷ 'a' ∷ 'r' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showNat (toℕ x) ++ toList ")") ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showNat (toℕ x)) (toList ")") rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showNat (toℕ x) ++ (toList ")" ++ rest))
      ≡⟨ specNat (toℕ x) kwF (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ atom (showNat (toℕ x)) ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ atom (showNat (toℕ x)) ∷ []) fr stk rest ⟩
    after (fr ++ sexpG (gvar x) ∷ []) stk rest
      ∎
specG (gtyp x) fr stk rest d = chain
  where
  kw = toList "gtyp "
  body = showNat (toℕ x) ++ toList ")"
  kwF = atom (toList "gtyp") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGTm (gtyp x) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('t' ∷ 'y' ∷ 'p' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showNat (toℕ x) ++ toList ")") ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showNat (toℕ x)) (toList ")") rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showNat (toℕ x) ++ (toList ")" ++ rest))
      ≡⟨ specNat (toℕ x) kwF (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ atom (showNat (toℕ x)) ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ atom (showNat (toℕ x)) ∷ []) fr stk rest ⟩
    after (fr ++ sexpG (gtyp x) ∷ []) stk rest
      ∎
specG (gsu e) fr stk rest d = chain
  where
  kw = toList "gsu "
  body = showGTm e ++ toList ")"
  kwF = atom (toList "gsu") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGTm (gsu e) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('s' ∷ 'u' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showGTm e ++ toList ")") ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showGTm e) (toList ")") rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showGTm e ++ (toList ")" ++ rest))
      ≡⟨ specG e kwF (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpG e ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpG e ∷ []) fr stk rest ⟩
    after (fr ++ sexpG (gsu e) ∷ []) stk rest
      ∎
specG (gapp f a) fr stk rest d = chain
  where
  kw = toList "gapp "
  mid = toList " " ++ (showGTm a ++ toList ")")
  body = showGTm f ++ mid
  kwF = atom (toList "gapp") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGTm (gapp f a) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('a' ∷ 'p' ∷ 'p' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showGTm f ++ mid) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showGTm f) mid rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showGTm f ++ (mid ++ rest))
      ≡⟨ specG f kwF (fr ∷ stk) (mid ++ rest) (dsp ((showGTm a ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpG f ∷ []) (fr ∷ stk) (mid ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpG f ∷ []) ∷ fr ∷ stk)) ((showGTm a ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpG f ∷ []) (fr ∷ stk) (showGTm a) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpG f ∷ []) ∷ fr ∷ stk)) (showGTm a ++ (toList ")" ++ rest))
      ≡⟨ specG a (kwF ++ sexpG f ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpG f ∷ sexpG a ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpG f ∷ sexpG a ∷ []) fr stk rest ⟩
    after (fr ++ sexpG (gapp f a) ∷ []) stk rest
      ∎
specG (gmatch e z s) fr stk rest d = chain
  where
  kw = toList "gmatch "
  spS = toList " " ++ (showGTm s ++ toList ")")
  spZ = toList " " ++ (showGTm z ++ spS)
  body = showGTm e ++ spZ
  kwF = atom (toList "gmatch") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGTm (gmatch e z s) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('m' ∷ 'a' ∷ 't' ∷ 'c' ∷ 'h' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showGTm e ++ spZ) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showGTm e) spZ rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showGTm e ++ (spZ ++ rest))
      ≡⟨ specG e kwF (fr ∷ stk) (spZ ++ rest) (dsp ((showGTm z ++ spS) ++ rest)) ⟩
    after (kwF ++ sexpG e ∷ []) (fr ∷ stk) (spZ ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpG e ∷ []) ∷ fr ∷ stk)) ((showGTm z ++ spS) ++ rest)
      ≡⟨ push (kwF ++ sexpG e ∷ []) (fr ∷ stk) (showGTm z) spS rest ⟩
    parseGo (need ((kwF ++ sexpG e ∷ []) ∷ fr ∷ stk)) (showGTm z ++ (spS ++ rest))
      ≡⟨ specG z (kwF ++ sexpG e ∷ []) (fr ∷ stk) (spS ++ rest) (dsp ((showGTm s ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpG e ∷ sexpG z ∷ []) (fr ∷ stk) (spS ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpG e ∷ sexpG z ∷ []) ∷ fr ∷ stk)) ((showGTm s ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpG e ∷ sexpG z ∷ []) (fr ∷ stk) (showGTm s) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpG e ∷ sexpG z ∷ []) ∷ fr ∷ stk)) (showGTm s ++ (toList ")" ++ rest))
      ≡⟨ specG s (kwF ++ sexpG e ∷ sexpG z ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpG e ∷ sexpG z ∷ sexpG s ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpG e ∷ sexpG z ∷ sexpG s ∷ []) fr stk rest ⟩
    after (fr ++ sexpG (gmatch e z s) ∷ []) stk rest
      ∎
specG (glam c t b) fr stk rest d = chain
  where
  kw = toList "glam "
  mid = toList " " ++ (showGTm b ++ toList ")")
  body = showPair c t ++ mid
  kwF = atom (toList "glam") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGTm (glam c t b) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('l' ∷ 'a' ∷ 'm' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showPair c t ++ mid) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showPair c t) mid rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showPair c t ++ (mid ++ rest))
      ≡⟨ specPair c t kwF (fr ∷ stk) (mid ++ rest) (dsp ((showGTm b ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (mid ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) ((showGTm b ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (showGTm b) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) (showGTm b ++ (toList ")" ++ rest))
      ≡⟨ specG b (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpPair c t ∷ sexpG b ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpPair c t ∷ sexpG b ∷ []) fr stk rest ⟩
    after (fr ++ sexpG (glam c t b) ∷ []) stk rest
      ∎
specG (gpi c t b) fr stk rest d = chain
  where
  kw = toList "gpi "
  mid = toList " " ++ (showGTm b ++ toList ")")
  body = showPair c t ++ mid
  kwF = atom (toList "gpi") ∷ []
  chain =
    parseGo (need (fr ∷ stk)) (showGTm (gpi c t b) ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ([] ∷ fr ∷ stk)) ((kw ++ body) ++ rest)
      ≡⟨ eatKw 'g' ('p' ∷ 'i' ∷ []) [] (fr ∷ stk) (body ++ rest) refl (refl ∷ refl ∷ []) ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) ((showPair c t ++ mid) ++ rest)
      ≡⟨ push kwF (fr ∷ stk) (showPair c t) mid rest ⟩
    parseGo (need (kwF ∷ fr ∷ stk)) (showPair c t ++ (mid ++ rest))
      ≡⟨ specPair c t kwF (fr ∷ stk) (mid ++ rest) (dsp ((showGTm b ++ toList ")") ++ rest)) ⟩
    after (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (mid ++ rest)
      ≡⟨ refl ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) ((showGTm b ++ toList ")") ++ rest)
      ≡⟨ push (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (showGTm b) (toList ")") rest ⟩
    parseGo (need ((kwF ++ sexpPair c t ∷ []) ∷ fr ∷ stk)) (showGTm b ++ (toList ")" ++ rest))
      ≡⟨ specG b (kwF ++ sexpPair c t ∷ []) (fr ∷ stk) (')' ∷ rest) (drp rest) ⟩
    after (kwF ++ sexpPair c t ∷ sexpG b ∷ []) (fr ∷ stk) (')' ∷ rest)
      ≡⟨ shut (kwF ++ sexpPair c t ∷ sexpG b ∷ []) fr stk rest ⟩
    after (fr ++ sexpG (gpi c t b) ∷ []) stk rest
      ∎

imgTail : List Char
imgTail = 'u' ∷ 'r' ∷ 'o' ∷ '-' ∷ 'b' ∷ 'e' ∷ 'a' ∷ 'm' ∷ '-' ∷ 'i' ∷ 'm' ∷ 'a' ∷ 'g' ∷ 'e' ∷ []

imgA : AllA imgTail
imgA = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

bdTail : List Char
bdTail = 'o' ∷ 'u' ∷ 'n' ∷ 'd' ∷ 'a' ∷ 'r' ∷ 'y' ∷ []

bdA : AllA bdTail
bdA = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

image-go : ∀ i → parseGo top (render i) ≡ ok (sexpImage i , '\n' ∷ [])
image-go i = chain
  where
  fmt = showNat (format i)
  bv = showNat (boundary i)
  tm = showGTm (term i)
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
  seqFr = asq ∷ sexpG (term i) ∷ []
  seqFull = asq ∷ sexpG (term i) ∷ nest (ad ∷ []) ∷ []
  enFr = ae ∷ []
  enFull = ae ∷ nest seqFull ∷ []
  chain =
    parseGo top (render i)
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
      ≡⟨ specG (term i) (asq ∷ []) (enFr ∷ fImg ∷ []) w3 (dsp doneLit) ⟩
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
    ok (sexpImage i , nl)
      ∎

parse-show : ∀ i → parseCs (render i) ≡ ok i
parse-show i = trans (cong finish (image-go i)) (fromImage-ok i)
