{-# OPTIONS --sized-types #-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec as V
open import Data.Fin using (Fin; suc; zero; fromℕ≤; fromℕ<)
open import Data.Empty
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Data.Sum
open import Data.Product
open import Function --hiding (⟨_⟩)

fromℕ<-irr : ∀ {m n} → .(m Data.Nat.< n) → Fin n
fromℕ<-irr {zero}  {suc n} m≤n = zero
fromℕ<-irr {suc m} {suc n} m≤n = suc (fromℕ<-irr (Data.Nat.≤-pred m≤n))

open import Ord
open import OrdProp

record OFin (u : Ordinal) : Set where
  constructor _bounded_
  field
    v : Ordinal
    .v<u : v <ₒ u

infixr 5 _∷_
data Ix : (d : ℕ) → (s : Vec Ordinal d) → Set where
  []   : Ix 0 []
  _∷_  : ∀ {d s x} → OFin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)


ix-lookup : ∀ {d s} → Ix d s → (i : Fin d) → OFin (lookup s i)
ix-lookup [] ()
ix-lookup (x ∷ ix) zero = x
ix-lookup (x ∷ ix) (suc i) = ix-lookup ix i


ix-tabulate : ∀ {d s} → ((i : Fin d) → OFin (lookup s i)) → Ix d s
ix-tabulate {s = []} f = []
ix-tabulate {s = x ∷ s} f = f zero ∷ ix-tabulate (f ∘ suc)


ix→v : ∀ {d s} → Ix d s → Vec Ordinal d
ix→v [] = []
ix→v (x ∷ xs) = OFin.v x ∷ ix→v xs


data Ar {a} (X : Set a) (d : ℕ) (s : Vec Ordinal d) : Set a where
  imap : (Ix d s → X) → Ar X d s


-- Sanity check
sel : ∀ {a}{X : Set a}{d s} → Ar X d s → Ix d s → X
sel (imap x) ix = x ix

0>≯ₒx : ∀ {o} → 0ₒ >ₒ o → ⊥
0>≯ₒx ()

0≯ₑ0 : ∀ {k k>0 x o x>ₑo} → ω^ 0ₒ · k ⟨ k>0 ⟩ >ₑ (x ∷ o ⟨ x>ₑo ⟩) → ⊥
0≯ₑ0 (ss ())

k<1∧k>0 : ∀ {k} → k < 1 → k > 0 → ⊥
k<1∧k>0 (s≤s ()) (s≤s k>0)

ω^k<ω⇒k≡0 : ∀ {k m}.{m>0}{o}.{pf} → (ω^ k · m ⟨ m>0 ⟩ ∷ o ⟨ pf ⟩ <ₒ ωₒ) → k ≡ 0ₒ
ω^k<ω⇒k≡0 (e< z<) = refl
ω^k<ω⇒k≡0 {(ω^ _ · _ ⟨ k>0 ⟩ ∷ _ ⟨ _ ⟩)} (e< (k< refl x₁)) = ⊥-elim-irr (k<1∧k>0 x₁ k>0)
ω^k<ω⇒k≡0 {m>0 = m>0} (k< refl x₁) = ⊥-elim-irr (k<1∧k>0 x₁ m>0) 

ω^k+o<ω⇒o≡0 : ∀ {k m}.{m>0}{o}.{pf} → ω^ k · m ⟨ m>0 ⟩ ∷ o ⟨ pf ⟩ <ₒ ωₒ → o ≡ 0ₒ
ω^k+o<ω⇒o≡0 {k} {o = 0ₒ} x<w = refl
ω^k+o<ω⇒o≡0 {0ₒ} {o = x ∷ o ⟨ x₁ ⟩} {pf} (e< z<) = ⊥-elim-irr (0≯ₑ0 pf)
ω^k+o<ω⇒o≡0 {ω^ .0ₒ · _ ⟨ k>0 ⟩ ∷ _ ⟨ _ ⟩} {o = _ ∷ _ ⟨ _ ⟩} (e< (k< refl x)) = ⊥-elim-irr (k<1∧k>0 x k>0)
ω^k+o<ω⇒o≡0 {m>0 = m>0} {o = x ∷ o ⟨ x₁ ⟩} (k< x₂ x₃) =  ⊥-elim-irr (k<1∧k>0 x₃ m>0)

o-n : (o : Ordinal) → .(o <ₒ ωₒ) → ℕ
o-n 0ₒ o<w = 0
o-n (ω^ e · k ⟨ k>0 ⟩ ∷ o ⟨ pf ⟩) o<w = k


n-od<w : ∀ {d} → n→o d <ₒ ωₒ
n-od<w {zero} = z<
n-od<w {suc d} = e< z<

conv-< : ∀ {v d} → (pf : v <ₒ n→o d) → o-n v (<ₒ-trans pf n-od<w) < d
conv-< {0ₒ} {zero} ()
conv-< {0ₒ} {suc v} z< = s≤s z≤n
conv-< {x ∷ d ⟨ x₁ ⟩} {zero} ()
conv-< {x ∷ d ⟨ x₁ ⟩} {suc v} (k< x₂ x₃) = x₃

ofin-fin : ∀ {d} → OFin (n→o d) → Fin d
ofin-fin (v bounded v<u) = fromℕ<-irr (conv-< v<u)

shape : ∀ {a}{X : Set a}{d s} → Ar X d s → Ar Ordinal 1 (n→o d ∷ [])
shape {s = s} x = imap (λ iv → lookup s (ofin-fin (ix-lookup iv zero)))


ofin-cong : ∀ {o}{x y : Ordinal} → x ≡ y → .(x<o : x <ₒ o) → .(y<o : y <ₒ o) → x bounded x<o ≡ y bounded y<o
ofin-cong refl x<o y<o = refl

open import Codata.Stream
open import Codata.Thunk
open import Size
open import Codata.Stream.Bisimilarity as B


-- Iso between the Array X 1 ω and Stream X
to : ∀ {a}{X : Set a}{i} → Stream X i → Ar X 1 (ωₒ ∷ [])
to (x ∷ xs) = imap str-content
  where str-content : _
        str-content ((0ₒ bounded _) ∷ []) = x
        str-content (((ω^ exp · suc k ⟨ k>0 ⟩ ∷ v ⟨ x₂ ⟩) bounded v<u) ∷ []) = {!!}

-- Nat is the same as OFin ω
n-o-bounded : ∀ n → n→o n <ₒ ωₒ
n-o-bounded zero = z<
n-o-bounded (suc n) = e< z<

nat-ofinω : ∀ (n : ℕ) → OFin ωₒ
nat-ofinω n = n→o n bounded n-o-bounded n

ofinω-nat : ∀ (o : OFin ωₒ) → ℕ
ofinω-nat (0ₒ bounded v<u) = 0
ofinω-nat ((ω^ e · k ⟨ k>0 ⟩ ∷ v ⟨ x₂ ⟩) bounded v<u) = k

on-no : ∀ {o} → nat-ofinω (ofinω-nat o) ≡ o
on-no {0ₒ bounded v<u} = P.refl
on-no {(ω^ exp · suc k ⟨ k>0 ⟩ ∷ v ⟨ x₂ ⟩) bounded v<u} = ofin-cong (cong₂ (λ x y → ω^ x · suc k ⟨ _ ⟩ ∷ y ⟨ _ ⟩)
                                                                         (P.sym $ ω^k<ω⇒k≡0 (recompute (_ <ₒ? _) v<u ))
                                                                         (P.sym $ ω^k+o<ω⇒o≡0 (recompute (_ <ₒ? _) v<u)))
                                                                   (e< z<) v<u

tox : ∀ {a}{X : Set a} → Stream X ∞ → ℕ → X
tox (x ∷ xs) zero = x
tox (x ∷ xs) (suc i) = tox (xs .force) i

fromx : ∀ {a}{X : Set a}{i} → (ℕ → X) → Stream X i
fromx f = f 0 ∷ λ where .force → fromx (f ∘ suc)

tox∘fromx : ∀ {a}{X : Set a}{f : ℕ → X} i → tox (fromx f) i ≡ f i
tox∘fromx zero = P.refl
tox∘fromx (suc i) = tox∘fromx i

fromx∘tox : ∀ {a}{X : Set a} (s : Stream X ∞) {i} → i ⊢ fromx (tox s) ≈ s
fromx∘tox (x ∷ xs) = P.refl ∷ λ where .force → fromx∘tox (xs .force)


ext-bsim : ∀ {a}{X : Set a} {f g : ℕ → X} → (∀ i → f i ≡ g i)
         → ∀ {sz} → sz ⊢ fromx f ≈ fromx g
ext-bsim f≡g = (f≡g 0) ∷ λ where .force → ext-bsim (f≡g ∘ suc)


-- A quick experiment with the nested array as a container interpreted as
-- a dependent function Π A B, rather than A → B.

data DAr {a} (d : ℕ) (s : Vec Ordinal d) (X : Ix d s → Set a) : Set a where
  imap : ((ix : Ix _ _) → X ix) → DAr d s X


rational-indexed-array : DAr 3 (ωₒ ∷ ωₒ ∷ ωₒ ∷ [])
                               λ where
                                   (i ∷ _ ∷ _ ∷ []) → let
                                                         i' = ofinω-nat i
                                                         k = 2 ^ i'
                                                         k' = n→o k
                                                          -- Well, actually, this thing can be just Ar.
                                                       in DAr 2 (k' ∷ k' ∷ []) λ _ → ℕ
rational-indexed-array = imap (λ where (l ∷ i ∷ j ∷ [] ) → imap (λ _ → 1))


-- -- Explore the idea to map ordinals to ℕ
-- open import Data.Fin using (Fin; inject≤)
-- 
-- -- XXX well, we just don't have infinite list of primes, so
-- -- we are using a workaround for now.
-- pr_length = 5
-- primes : Vec ℕ pr_length
-- primes = 2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ []
-- 
-- ntup→n : ∀ {n} → n ≤ pr_length → Vec ℕ n → ℕ
-- ntup→n n<pl v = foldr _ _*_ 1 $ tabulate λ i →  V.lookup primes (inject≤ i n<pl) ^ V.lookup v i
-- 
-- 
-- data ONice : Ordinal → Set where
--   [] : ONice []
--   OT : ∀ {o k ot oot k>} → ONice o → ONice (ω^ o · k ⟨ k> ⟩ ∷ ot ⟨ oot ⟩)

module Examples where
  hd : ∀ {a}{X : Set a}{n} → Ar X 1 (n ∷ []) → X
  --hd (imap a) = a ((0ₒ bounded z<) ∷ [])

  1+n<ω : ∀ o → o <ₒ ωₒ → 1ₒ +ₒ o <ₒ ωₒ
  1+n<ω 0ₒ o = e< z<
  1+n<ω (ω^ .0ₒ · k ⟨ k>0 ⟩ ∷ o ⟨ x₂ ⟩) (e< z<) = e< z<
  1+n<ω (ω^ .(_ ∷ _ ⟨ _ ⟩) · k ⟨ k>0 ⟩ ∷ o ⟨ x₂ ⟩) (e< (k< x₁ x₃)) = e< (k< x₁ x₃)
  1+n<ω (ω^ e · k ⟨ k>0 ⟩ ∷ o ⟨ x₂ ⟩) (k< refl k<1) =
    -- We have a contradiction k>0 k<1 which we can use explicitly
    -- but we can also do it like so:
    k< P.refl k<1

  e>0 : ∀ .{p}{n} → ω^ 0ₒ · 1 ⟨ p ⟩ >ₑ n → n ≡ 0ₒ
  e>0 zz = P.refl

  1+n-1≡n : ∀ n → .(n≥1 : n ≥ₒ 1ₒ) → 1ₒ +ₒ (n -ₒ 1ₒ){n≥1} ≡ n
  1+n-1≡n 0ₒ n≥1 = ⊥-elim-irr (0≥1⇒⊥ n≥1)
    where
      0≥1⇒⊥ : 0ₒ ≥ₒ 1ₒ → ⊥
      0≥1⇒⊥ (inj₁ x₁) = contradiction z< (<⇒≮ x₁)
      0≥1⇒⊥ (inj₂ ())
  1+n-1≡n (ω^ 0ₒ · suc zero ⟨ k>0 ⟩ ∷ n ⟨ x₂ ⟩) n≥0 with n ≟ₒ 0ₒ
  ... | yes refl = P.refl
  ... | no ¬p = contradiction (e>0 (recompute (_ >ₑ? _) x₂)) ¬p
  1+n-1≡n (ω^ 0ₒ · suc (suc k) ⟨ k>0 ⟩ ∷ n ⟨ x₂ ⟩) n≥1 = P.refl
  1+n-1≡n (ω^ x₁ ∷ exp ⟨ x₃ ⟩ · k ⟨ k>0 ⟩ ∷ n ⟨ x₂ ⟩) n≥1 = P.refl


  tl : ∀ {a}{X : Set a}{n} → .(n≥1 : n ≥ₒ 1ₒ) → Ar X 1 (n ∷ []) → Ar X 1 ((n -ₒ 1ₒ) {n≥1} ∷ [])
  tl n≥1 (imap a) = imap λ where
    (o bounded o<n-1 ∷ []) → a (((1ₒ +ₒ o) bounded subst (_>ₒ 1ₒ +ₒ o) (b+a-b≡b n≥1) (a+b>a+c {a = 1ₒ} o<n-1) ) ∷ [])


  o≢0⇒o≥1 : ∀ o → ¬ o ≡ 0ₒ → o ≥ₒ 1ₒ
  o≢0⇒o≥1 0ₒ o≢0 = contradiction P.refl o≢0
  o≢0⇒o≥1 (ω^ 0ₒ · suc zero ⟨ k>0 ⟩ ∷ n ⟨ x₂ ⟩) o≢0 with n ≟ₒ 0ₒ
  ... | yes refl = inj₂ P.refl
  ... | no ¬p = inj₁ (t< P.refl P.refl (n≢0⇒n>ₒ0 ¬p ))
  o≢0⇒o≥1 (ω^ 0ₒ · suc (suc k) ⟨ k>0 ⟩ ∷ o ⟨ x₂ ⟩) o≢0 = inj₁ (k< P.refl (s≤s (s≤s z≤n)))
  o≢0⇒o≥1 (ω^ x₁ ∷ exp ⟨ x₃ ⟩ · k ⟨ k>0 ⟩ ∷ o ⟨ x₂ ⟩) o≢0 = inj₁ (e< z<)

{-
  k+x≮k : ∀ {k x} → x > 0 → ¬ k + x < k
  k+x≮k {zero} {x} x>0 x<0 = contradiction x>0 $ <⇒≯ x<0
  k+x≮k {suc k} {x} x>0 pf = contradiction (≤-pred pf) (k+x≮k {k = k} x>0)

  k+x≢k : ∀ {k x} → x > 0 → ¬ k + x ≡ k
  k+x≢k {zero} {.0} () P.refl
  k+x≢k {suc k} {x} x>0 t = contradiction (suc-injective t) (k+x≢k x>0)


  a+b<a+c⇒b<c : ∀ {a b c} → a +ₒ b <ₒ a +ₒ c → b <ₒ c
  a+b<a+c⇒b<c {0ₒ} {b} {c} a+b<a+c = a+b<a+c
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {0ₒ} {0ₒ} a+b<a+c = contradiction a+b<a+c l≮ₒl
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {0ₒ} {x₃ ∷ c₁ ⟨ x₄ ⟩} a+b<a+c = z<
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {0ₒ} a+b<a+c = contradiction a+b<a+c (<⇒≮ (a+ₒb>a foo)) 
    where
      foo : ¬ (x₃ ∷ b₁ ⟨ x₄ ⟩) ≡ 0ₒ
      foo ()
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} a+b<a+c
              with OrdTerm.exp x₁ <ₒ? OrdTerm.exp x₃
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} a+b<a+c | yes ex1<ex3 with  OrdTerm.exp x₁ <ₒ? OrdTerm.exp x₅
  ... | yes ex1<ex5 = a+b<a+c
  ... | no ¬ex1<ex5 with OrdTerm.exp x₁ ≟ₒ OrdTerm.exp x₅
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp x₅) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (e< a+b<a+c) | yes ex1<ex3 | no ¬ex1<ex5 | yes P.refl = e< a+b<a+c
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp x₅) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (k< x₁ x₇) | yes ex1<ex3 | no ¬ex1<ex5 | yes P.refl
    = contradiction (subst (OrdTerm.exp x₅ <ₒ_) x₁ ex1<ex3) l≮ₒl
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp x₅) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (t< x₁ x₇ a+b<a+c) | yes ex1<ex3 | no ¬ex1<ex5 | yes P.refl
    = contradiction (subst (OrdTerm.exp x₅ <ₒ_) x₁ ex1<ex3) l≮ₒl
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (e< a+b<a+c) | yes ex1<ex3 | no ¬ex1<ex5 | no ¬ex1=ex5
    = contradiction a+b<a+c (<⇒≮ ex1<ex3)
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (k< x₇ x₈) | yes ex1<ex3 | no ¬ex1<ex5 | no ¬ex1=ex5
    = contradiction (subst (OrdTerm.exp x₁ <ₒ_) x₇ ex1<ex3) l≮ₒl
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (t< x₇ x₈ a+b<a+c) | yes ex1<ex3 | no ¬ex1<ex5 | no ¬ex1=ex5
    = contradiction (subst (OrdTerm.exp x₁ <ₒ_) x₇ ex1<ex3) l≮ₒl
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} a+b<a+c | no ¬ex1<ex3
        with OrdTerm.exp x₁ <ₒ? OrdTerm.exp x₅ | OrdTerm.exp x₁ ≟ₒ OrdTerm.exp x₃
  ... | yes ex1<ex5 | yes refl = e< ex1<ex5
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (e< a+b<a+c) | no ¬ex1<ex3 | yes ex1<ex5 | no ¬ex1=ex3
    = e< (<ₒ-trans (≮ₒ∧≢ₒ⇒>ₒ ¬ex1<ex3 ¬ex1=ex3) a+b<a+c)
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (k< x₇ x₈) | no ¬ex1<ex3 | yes ex1<ex5 | no ¬ex1=ex3
    = e< (subst (_>ₒ OrdTerm.exp x₃) x₇ (≮ₒ∧≢ₒ⇒>ₒ ¬ex1<ex3 ¬ex1=ex3))
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (t< x₇ x₈ a+b<a+c) | no ¬ex1<ex3 | yes ex1<ex5 | no ¬ex1=ex3
    = contradiction (subst (_<ₒ OrdTerm.exp x₅) x₇ ex1<ex5) l≮ₒl
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp x₃) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} a+b<a+c | no ¬ex1<ex3 | no ¬ex3<ex5 | yes P.refl
    with OrdTerm.exp x₃ ≟ₒ OrdTerm.exp x₅
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp ω^ OrdTerm.exp x₅ · k₁ ⟨ k>1 ⟩) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {ω^ .(OrdTerm.exp x₅) · k₁ ⟨ k>1 ⟩ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (e< a+b<a+c) | no ¬ex1<ex3 | no ¬ex3<ex5 | yes P.refl | yes P.refl = contradiction a+b<a+c l≮ₒl
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp ω^ OrdTerm.exp x₅ · k₁ ⟨ k>1 ⟩) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {ω^ .(OrdTerm.exp x₅) · k₁ ⟨ k>1 ⟩ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (k< x₁ x₃) | no ¬ex1<ex3 | no ¬ex3<ex5 | yes P.refl | yes P.refl = k< x₁ (+-cancelˡ-< k x₃)
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp ω^ OrdTerm.exp x₅ · k₁ ⟨ k>1 ⟩) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {ω^ .(OrdTerm.exp x₅) · k₁ ⟨ k>1 ⟩ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (t< x₁ x₃ a+b<a+c) | no ¬ex1<ex3 | no ¬ex3<ex5 | yes P.refl | yes P.refl = t< P.refl (+-cancelˡ-≡ k x₃) a+b<a+c
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp x₃) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (e< a+b<a+c) | no ¬ex1<ex3 | no ¬ex3<ex5 | yes P.refl | no ¬ex3=ex5 = contradiction a+b<a+c l≮ₒl
  a+b<a+c⇒b<c {ω^ .(exp) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (k< x₁ x₇) | no ¬ex1<ex3 | no ¬ex3<ex5 | yes P.refl | no ¬ex3=ex5 = contradiction x₇ (k+x≮k (recompute (_ >? _) k>1))
  a+b<a+c⇒b<c {ω^ .(exp) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (t< x₁ x₇ a+b<a+c) | no ¬ex1<ex3 | no ¬ex3<ex5 | yes P.refl | no ¬ex3=ex5 = contradiction x₇ (k+x≢k (recompute (_ >? _) k>1))
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} a+b<a+c | no ¬ex1<ex3 | no ¬ex3<ex5 | no ¬ex1=ex3
    with OrdTerm.exp x₁ ≟ₒ OrdTerm.exp x₅
  a+b<a+c⇒b<c {ω^ .(OrdTerm.exp x₅) · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (a+b<a+c) | no ¬ex1<ex3 | no ¬ex3<ex5 | no ¬ex1=ex3 | yes P.refl = e< (≮ₒ∧≢ₒ⇒>ₒ ¬ex1<ex3 ¬ex1=ex3)
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (e< a+b<a+c) | no ¬ex1<ex3 | no ¬ex3<ex5 | no ¬ex1=ex3 | no ¬ex1=ex5
    = contradiction a+b<a+c l≮ₒl
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (k< x₇ x₈) | no ¬ex1<ex3 | no ¬ex3<ex5 | no ¬ex1=ex3 | no ¬ex1=ex5
    = contradiction x₈ (<-asym x₈)
  a+b<a+c⇒b<c {x₁ ∷ a₁ ⟨ x₂ ⟩} {x₃ ∷ b₁ ⟨ x₄ ⟩} {x₅ ∷ c₁ ⟨ x₆ ⟩} (t< x₇ x₈ a+b<a+c) | no ¬ex1<ex3 | no ¬ex3<ex5 | no ¬ex1=ex3 | no ¬ex1=ex5
    = a+b<a+c⇒b<c {a = a₁} a+b<a+c

-}


  cons : ∀ {a}{X : Set a}{n} → X → Ar X 1 (n ∷ []) → Ar X 1 (1ₒ +ₒ n ∷ [])
  cons {n = n} x (imap xs) = imap helper
    where
      helper : _
      helper (o bounded o<1+n ∷ []) with o ≟ₒ 0ₒ
      ... | yes p = x
      ... | no ¬p = xs (((o -ₒ 1ₒ){o≢0⇒o≥1 _ ¬p} bounded a+b<a+c⇒b<c {a = 1ₒ} (subst (_<ₒ 1ₒ +ₒ n) (P.sym (b+a-b≡b (o≢0⇒o≥1 _ ¬p)) ) o<1+n) ) ∷ [])

  _^^_ : ∀ {X : Set}{m n} → Ar X 1 (m ∷ []) → Ar X 1 (n ∷ []) → Ar X 1 (m +ₒ n ∷ [])
  _^^_ {X}{m = m}{n = n} a b with (m ≟ₒ 0ₒ)
  ... | yes refl = b
  ... | no ¬p = subst (λ x → Ar X 1 (x ∷ [])) {!!} $ cons (hd a) ((tl (o≢0⇒o≥1 m ¬p) a) ^^ b)

  conc :  ∀ {a}{X : Set a}{m n} → Ar X 1 (m ∷ []) → Ar X 1 (n ∷ []) → Ar X 1 (m +ₒ n ∷ [])
  conc {m = m}{n}(imap a) (imap b) = imap body
    where
      body : _
      body (x bounded x<m+n ∷ []) with x <ₒ? m
      ... | yes p = a ((x bounded p) ∷ [])
      ... | no ¬p = b (((x -ₒ m) bounded (a+b<a+c⇒b<c {a = m} $ subst (_<ₒ m +ₒ n) (P.sym $ b+a-b≡b (o-≮⇒≥ ¬p)) (x<m+n))) ∷ [])


  x≮0 : ∀ {x} → x <ₒ 0ₒ → ⊥
  x≮0 ()
  
  atake : ∀ {a}{X : Set a}{m n} → Ar X 1 (m +ₒ n ∷ []) → Ar X 1 (m ∷ [])
  atake {n = n} (imap a) = imap body
    where
      body : _
      body (o bounded o<m ∷ []) with n ≟ₒ 0ₒ
      ... | yes refl =  a (o bounded subst (o <ₒ_) (P.sym a+0≡a) o<m ∷ [])
      ... | no ¬p = a ((o bounded <ₒ-trans o<m (a+ₒb>a ¬p)) ∷ [])

  adrop : ∀ {a}{X : Set a}{m n} → Ar X 1 (m +ₒ n ∷ []) → Ar X 1 (n ∷ [])
  adrop {m = m} (imap a) = imap body
    where
      body : _
      body (o bounded o<n ∷ []) = a ((m +ₒ o) bounded a+b>a+c {a = m} o<n ∷ [])

  unimap : ∀ {a}{X : Set a}{d}{s : Vec _ d} → Ar X d s → Ix d s → X
  unimap (imap a) = a

  -- The joy of irrelevant arguments :)
  ofin-eq : ∀ {n}{x y : OFin n} →  OFin.v x ≡ OFin.v y → x ≡ y
  ofin-eq refl = P.refl


  conc-thmₗ : ∀ {l}{X : Set l}{m n}{a : Ar X 1 (m ∷ [])}{b : Ar X 1 (n ∷ [])}
            → ∀ ix → unimap (adrop {m = m} (conc a b)) ix ≡ unimap b ix
  conc-thmₗ {m = m} {a = imap a} {b = imap b} (o bounded o<n ∷ []) with m +ₒ o <ₒ? m
  ... | yes p = ⊥-elim $ x≮0 $ a+b<a+c⇒b<c {a = m} $ subst (m +ₒ o <ₒ_) (P.sym a+0≡a) p
  ... | no ¬p = cong b (cong (_∷ []) (ofin-eq $ [b+a]-b≡b {b = m}))

  conc-thmᵣ : ∀ {l}{X : Set l}{m n}{a : Ar X 1 (m ∷ [])}{b : Ar X 1 (n ∷ [])}
            → ∀ ix → unimap (atake {n = n} (conc a b)) ix ≡ unimap a ix
  conc-thmᵣ {m = m}{n = n} {imap a} {imap b} (o bounded o<m ∷ []) with n ≟ₒ 0ₒ
  conc-thmᵣ {m = m}{n = _} {imap a} {imap b} (o bounded o<m ∷ []) | yes P.refl with o <ₒ? m
  ... | yes _ = P.refl
  ... | no ¬o<m = ⊥-elim-irr (¬o<m o<m)
  conc-thmᵣ {m = m}{n = n} {imap a} {imap b} (o bounded o<m ∷ []) | no ¬n≡0 with o <ₒ? m
  ... | yes _ = P.refl
  ... | no ¬o<m = ⊥-elim-irr (¬o<m o<m)

  minₒ : Ordinal → Ordinal → Ordinal
  minₒ a b with a <ₒ? b
  minₒ a b | yes a<b = a
  minₒ a b | no ¬a<b = b

  min[ab]≤a : ∀ {a b} → a ≥ₒ minₒ a b
  min[ab]≤a {a}{b} with a <ₒ? b
  ... | yes p = inj₂ P.refl
  ... | no ¬p = o-≮⇒≥ ¬p

  min[ab]≤b : ∀ {a b} → b ≥ₒ minₒ a b
  min[ab]≤b {a}{b} with a <ₒ? b
  ... | no ¬p = inj₂ P.refl
  ... | yes p = inj₁ p

  a≮b∧b≮a⇒a≡b : ∀ {a b} → ¬ a <ₒ b → ¬ b <ₒ a → a ≡ b
  a≮b∧b≮a⇒a≡b a≮b b≮a with (o-≮⇒≥ a≮b) | (o-≮⇒≥ b≮a)
  a≮b∧b≮a⇒a≡b a≮b b≮a | inj₁ a>b | inj₁ b>a = contradiction a>b b≮a
  a≮b∧b≮a⇒a≡b a≮b b≮a | inj₁ a>b | inj₂ b=a = P.sym b=a
  a≮b∧b≮a⇒a≡b a≮b b≮a | inj₂ a=b | _        = a=b


  min-comm : ∀ {a b} → minₒ a b ≡ minₒ b a
  min-comm {a}{b} with a <ₒ? b | b <ₒ? a
  ... | yes a<b | yes b<a = contradiction a<b (<⇒≮ b<a)
  ... | yes a<b | no ¬b<a = P.refl
  ... | no ¬a<b | yes b<a = P.refl
  ... | no ¬a<b | no ¬b<a = P.sym $ a≮b∧b≮a⇒a≡b ¬a<b ¬b<a

  <-≤-trans : ∀ {a b c} → a <ₒ b → c ≥ₒ b → a <ₒ c
  <-≤-trans {a} {b} {c} a<b (inj₁ c>b) = <ₒ-trans a<b c>b
  <-≤-trans {a} {b} {c} a<b (inj₂ refl) = a<b

  azip : ∀ {a}{X : Set a}{m n} → Ar X 1 (m ∷ []) → Ar X 1 (n ∷ []) → Ar (X × X) 1 (minₒ m n ∷ [])
  azip {m = m}{n} (imap a) (imap b) = imap body
    where
      body : _
      body (o bounded o<min[mn] ∷ []) = (a ((o bounded <-≤-trans o<min[mn] min[ab]≤a) ∷ [])) ,
                                        (b ((o bounded <-≤-trans o<min[mn] (min[ab]≤b {a = m})) ∷ []))

  flp : ∀ {a}{X : Set a}{m} → Ar (X × X) 1 (m ∷ []) → Ar X 2 (m ∷ n→o 2 ∷ [])
  flp {m = m} (imap a) = imap body
    where
      body : _
      body (x ∷ (i bounded v<u) ∷ []) with (recompute (_ <ₒ? _) v<u)
      body (x ∷ (_ bounded v<u) ∷ []) | z<     = proj₁ (a (x ∷ []))
      body (x ∷ (_ bounded v<u) ∷ []) | k< _ _ = proj₂ (a (x ∷ []))

  ¬k>0∧k<1 : ∀ {k} → k > 0 → k < 1 → ⊥
  ¬k>0∧k<1 {zero} = λ ()
  ¬k>0∧k<1 {suc k} k>0 (s≤s ())


  o<ω⇒eo≡0 : ∀ {a b}.{pf} → a ∷ b ⟨ pf ⟩ <ₒ ωₒ → OrdTerm.exp a ≡ 0ₒ
  o<ω⇒eo≡0 {ω^ .0ₒ · k ⟨ k>0 ⟩} {b} (e< z<) = P.refl
  o<ω⇒eo≡0 {ω^ ω^ e · k₁ ⟨ k>1 ⟩ ∷ _ ⟨ _ ⟩ · k ⟨ _ ⟩} {b} (e< (k< refl x₂)) = ⊥-elim-irr (¬k>0∧k<1 k>1 x₂)
  o<ω⇒eo≡0 {ω^ exp · k ⟨ k>0 ⟩} {b} (k< x₁ x₂) = ⊥-elim-irr (¬k>0∧k<1 k>0 x₂)


  i+k<ω : ∀ {i k} → i <ₒ ωₒ → k <ₒ ωₒ → i +ₒ k <ₒ ωₒ
  i+k<ω {0ₒ} {k}  i<ω k<ω = k<ω
  i+k<ω {x₁ ∷ i ⟨ x₂ ⟩} {0ₒ} i<ω k<ω = i<ω
  i+k<ω {x₁ ∷ i ⟨ x₂ ⟩} {x₃ ∷ k ⟨ x₄ ⟩} i<ω k<ω with OrdTerm.exp x₁ <ₒ? OrdTerm.exp x₃
  i+k<ω {x₁ ∷ i ⟨ x₂ ⟩} {x₃ ∷ k ⟨ x₄ ⟩} i<ω k<ω | yes x1<x3 = k<ω
  i+k<ω {x₁ ∷ i ⟨ x₂ ⟩} {x₃ ∷ k ⟨ x₄ ⟩} i<ω k<ω | no ¬x1<x3 with OrdTerm.exp x₁ ≟ₒ OrdTerm.exp x₃
  i+k<ω {x₁ ∷ i ⟨ x₂ ⟩} {x₃ ∷ k ⟨ x₄ ⟩} i<ω k<ω | no ¬x1<x3 | yes P.refl  = e< (subst (_<ₒ 1ₒ) (P.sym $ o<ω⇒eo≡0 k<ω) z<)
  i+k<ω {x₁ ∷ i ⟨ x₂ ⟩} {x₃ ∷ k ⟨ x₄ ⟩} i<ω k<ω | no ¬x1<x3 | no ¬ex1=ex3 = e< (subst (_<ₒ 1ₒ) (P.sym $ o<ω⇒eo≡0 i<ω) z<)

  conv : Ar ℕ 1 (ωₒ ∷ []) → Ar ℕ 1 (ωₒ ∷ [])
  conv (imap a) = imap body
    where
      body : _
      body (i bounded i<ω ∷ []) = a (i bounded i<ω ∷ []) + a ((i +ₒ n→o 1) bounded i+k<ω i<ω (n-o-bounded 1) ∷ [])


  rec : Ar ℕ 1 (ωₒ ∷ [])
  rec = imap body
    where
      body : _
      body ((x bounded i<ω) ∷ []) with x <ₒ? 1ₒ
      ... | yes x<1 = 1
      ... | no ¬x<1 = unimap rec {!!}
      --body (((x₁ ∷ i ⟨ x₂ ⟩) bounded i<ω) ∷ []) = unimap rec {!!}


ARel : (ℕ → ℕ → Set) → (ℕ → ℕ) → (ℕ → ℕ) → Set
ARel _~_ a b = ∀ i → a i ~ b i


