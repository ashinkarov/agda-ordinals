--{-# OPTIONS --irrelevant-projections #-}

-- FIXME
-- Get rid of this when everyhting is proven. I
-- only use this to include this module in transfinite.agda.
--{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.List hiding ([_])
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Sum
open import Function

data Ordinal : Set

record OrdTerm : Set where
  inductive
  constructor ω^_·_⟨_⟩
  field
    exp : Ordinal
    k : ℕ
    .k>0 : k > 0

infixl 10 _>ₑ_
-- OrdTerm's exponent is larger than the highest exponent in Ordinal
data _>ₑ_ : OrdTerm → Ordinal → Set
data _<ₒ_ : Ordinal → Ordinal → Set

infixl 10 _<ₒ_
_>ₒ_ : Ordinal → Ordinal → Set
infixl 10 _>ₒ_
a >ₒ b = b <ₒ a

data Ordinal where
  [] : Ordinal
  _∷_⟨_⟩ : (x : OrdTerm) → (xs : Ordinal) → .(x >ₑ xs) → Ordinal 

data _>ₑ_ where
  zz : ∀ {t} → t >ₑ []
  ss : ∀ {t o l}.{pf} → OrdTerm.exp t >ₒ OrdTerm.exp o → t >ₑ (o ∷ l ⟨ pf ⟩)

pattern 0ₒ = []
pattern 1ₒ = ω^ 0ₒ · 1 ⟨ s≤s z≤n ⟩ ∷ [] ⟨ zz ⟩ 
pattern ωₒ = ω^ 1ₒ · 1 ⟨ s≤s z≤n ⟩ ∷ [] ⟨ zz ⟩ 

-- XXX Equality of ordinals might be asking a bit too much...
data _<ₒ_ where
  z< : ∀ {t l}.{pf} → 0ₒ <ₒ t ∷ l ⟨ pf ⟩
  e< : ∀ {t t₁ l l₁}.{pf pf₁}
     → OrdTerm.exp t <ₒ OrdTerm.exp t₁
     → t ∷ l ⟨ pf ⟩ <ₒ t₁ ∷ l₁ ⟨ pf₁ ⟩
  k< : ∀ {t t₁ l l₁}.{pf pf₁}
     → OrdTerm.exp t ≡ OrdTerm.exp t₁
     → OrdTerm.k t < OrdTerm.k t₁
     → t ∷ l ⟨ pf ⟩ <ₒ t₁ ∷ l₁ ⟨ pf₁ ⟩
  t< : ∀ {t t₁ l l₁}.{pf pf₁}
     → OrdTerm.exp t ≡ OrdTerm.exp t₁
     → OrdTerm.k t ≡ OrdTerm.k t₁
     → l <ₒ l₁
     → t ∷ l ⟨ pf ⟩ <ₒ t₁ ∷ l₁ ⟨ pf₁ ⟩


--n→o : (n : ℕ) → n > 0 →  Ordinal
--n→o n n>0 = ω^ 0ₒ · n ⟨ n>0 ⟩ ∷ [] ⟨ zz ⟩ 

n→o : ℕ → Ordinal
n→o zero = 0ₒ
n→o (suc x) = ω^ 0ₒ · (suc x) ⟨ s≤s z≤n ⟩ ∷ [] ⟨ zz ⟩



ot=pk : ∀ {l r} → l ≡ r → OrdTerm.k l ≡ OrdTerm.k r
ot=pk refl = refl

ot=pe : ∀ {l r} → l ≡ r → OrdTerm.exp l ≡ OrdTerm.exp r
ot=pe refl = refl

o=ph : ∀ {t l t₁ l₁}.{pf pf₁} → t ∷ l ⟨ pf ⟩ ≡ t₁ ∷ l₁ ⟨ pf₁ ⟩ → t ≡ t₁
o=ph refl = refl

o=pt : ∀ {t l t₁ l₁}.{pf pf₁} → t ∷ l ⟨ pf ⟩ ≡ t₁ ∷ l₁ ⟨ pf₁ ⟩ → l ≡ l₁
o=pt refl = refl


cong-ot : ∀ {k₁ k₂ e₁ e₂} → k₁ ≡ k₂  → e₁ ≡ e₂ → .(pf₁ : k₁ > 0) → .(pf₂ : k₂ > 0)
        → ω^ e₁ · k₁ ⟨ pf₁ ⟩ ≡ ω^ e₂ · k₂ ⟨ pf₂ ⟩
cong-ot refl refl _ _ = refl

cong-o : ∀ {x y l r} → x ≡ y → l ≡ r → .(pf : x >ₑ l) → .(pf₁ : y >ₑ r)
       → x ∷ l ⟨ pf ⟩ ≡ y ∷ r ⟨ pf₁ ⟩
cong-o refl refl _ _ = refl

infixl 10 _≟ₒ_
_≟ₒ_ : Decidable (_≡_ {A = Ordinal})

infixl 10 _≟ₜ_
_≟ₜ_ : Decidable (_≡_ {A = OrdTerm})
ω^ exp · k ⟨ _ ⟩ ≟ₜ ω^ exp₁ · k₁ ⟨ _ ⟩ with k ≟ k₁
ω^ exp · k ⟨ _ ⟩ ≟ₜ ω^ exp₁ · k₁ ⟨ _ ⟩ | no ¬p = no λ l=r → contradiction (ot=pk l=r) ¬p
ω^ exp · k ⟨ _ ⟩ ≟ₜ ω^ exp₁ · k₁ ⟨ _ ⟩ | yes p with exp ≟ₒ exp₁
ω^ exp · k ⟨ _ ⟩ ≟ₜ ω^ exp₁ · k₁ ⟨ _ ⟩ | yes p | no ¬p = no λ l=r → contradiction (ot=pe l=r) ¬p
ω^ exp · k ⟨ _ ⟩ ≟ₜ ω^ .exp · .k ⟨ _ ⟩ | yes refl | yes refl = yes refl

0ₒ ≟ₒ 0ₒ = yes refl
0ₒ ≟ₒ (x ∷ b ⟨ x₁ ⟩) = no (λ ())
x ∷ a ⟨ x₁ ⟩ ≟ₒ 0ₒ = no (λ ())
x ∷ xs ⟨ _ ⟩ ≟ₒ y ∷ ys ⟨ _ ⟩ with x ≟ₜ y
x ∷ xs ⟨ _ ⟩ ≟ₒ y ∷ ys ⟨ _ ⟩ | no ¬p = no λ l=r → contradiction (o=ph l=r) ¬p
x ∷ xs ⟨ _ ⟩ ≟ₒ y ∷ ys ⟨ _ ⟩ | yes p with xs ≟ₒ ys
x ∷ xs ⟨ _ ⟩ ≟ₒ y ∷ ys ⟨ _ ⟩ | yes p | no ¬p = no λ l=r → contradiction (o=pt l=r) ¬p
x ∷ xs ⟨ _ ⟩ ≟ₒ .x ∷ .xs ⟨ _ ⟩ | yes refl | yes refl = yes refl

l≮ₒl : ∀ {l} → ¬ l <ₒ l
l≮ₒl (e< l<l) = l≮ₒl l<l
l≮ₒl {t ∷ _ ⟨ _ ⟩} (k< x x₁) = contradiction x₁ (n≮n (OrdTerm.k t))
l≮ₒl (t< x x₁ l<l) = l≮ₒl l<l

<ₒ⇒≢ : ∀ {x y} → x <ₒ y → ¬ x ≡ y
<ₒ⇒≢ z< ()
<ₒ⇒≢ (e< x<y) refl = l≮ₒl x<y
<ₒ⇒≢ {(t ∷ _ ⟨ _ ⟩)} (k< x x₁) refl = contradiction x₁ (n≮n (OrdTerm.k t))
<ₒ⇒≢ {(_ ∷ l ⟨ _ ⟩)} (t< x x₁ x<y) refl = l≮ₒl x<y

<⇒≮ : ∀ {x y} → x <ₒ y → ¬ y <ₒ x
<⇒≮ z< ()
<⇒≮ (e< x<y) (e< y<x) = <⇒≮ x<y y<x
<⇒≮ (e< x<y) (k< x x₁) = contradiction x (≢-sym (<ₒ⇒≢ x<y)) 
<⇒≮ (e< x<y) (t< x x₁ y<x) = contradiction x (≢-sym (<ₒ⇒≢ x<y)) 
<⇒≮ (k< x x₁) (e< y<x) = contradiction (sym x) (<ₒ⇒≢ y<x)
<⇒≮ (k< x x₁) (k< x₂ x₃) = <-asym x₃ x₁
<⇒≮ (k< x x₁) (t< x₂ x₃ y<x) = <⇒≢ x₁ (sym x₃)
<⇒≮ (t< x x₁ x<y) (e< y<x) = contradiction x (≢-sym (<ₒ⇒≢ y<x))
<⇒≮ (t< x x₁ x<y) (k< x₂ x₃) = <⇒≢ x₃ (sym x₁)
<⇒≮ (t< x x₁ x<y) (t< x₂ x₃ y<x) = <⇒≮ x<y y<x

≮ₒ∧≢ₒ⇒>ₒ : ∀ {a b} → ¬ a <ₒ b → ¬ a ≡ b → a >ₒ b
a≮b⇒a≢b⇒a>b : ∀ {a b} → ¬ a < b → ¬ a ≡ b → a > b


-- Make <ₒ decidable
infixl 10 _<ₒ?_
_<ₒ?_ : Decidable (_<ₒ_)
0ₒ <ₒ? 0ₒ = no λ ()
0ₒ <ₒ? (x ∷ b ⟨ x₁ ⟩) = yes z<
x ∷ a ⟨ x₁ ⟩ <ₒ? 0ₒ = no λ ()
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ with OrdTerm.exp x <ₒ? OrdTerm.exp x₂
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | yes p = yes (e< p)
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp x₂
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p with OrdTerm.k x <? OrdTerm.k x₂
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p | yes p₁ = yes (k< p p₁)
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p | no ¬p₁ with OrdTerm.k x ≟ OrdTerm.k x₂
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p | no ¬p₁ | yes p₁ with a <ₒ? b
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p | no ¬p₁ | yes p₁ | yes p₂ = yes (t< p p₁ p₂)
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p | no ¬p₁ | yes p₁ | no ¬p₂ with a ≟ₒ b
ω^ e · k ⟨ _ ⟩ ∷ a ⟨ x₁ ⟩ <ₒ? ω^ .e · .k ⟨ _ ⟩ ∷ .a ⟨ x₃ ⟩ | no ¬p | yes refl | no ¬p₁ | yes refl | no ¬p₂ | yes refl =
  no λ l<r → l≮ₒl l<r
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p | no ¬p₁ | yes p₁ | no ¬p₂ | no ¬p₃ = 
  no λ l<r → <⇒≮ (t< (sym p) (sym p₁) (≮ₒ∧≢ₒ⇒>ₒ ¬p₂ ¬p₃)) l<r
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | yes p | no ¬p₁ | no ¬p₂ =
  no λ l<r → <⇒≮ (k< (sym p) (a≮b⇒a≢b⇒a>b ¬p₁ ¬p₂)) l<r
x ∷ a ⟨ x₁ ⟩ <ₒ? x₂ ∷ b ⟨ x₃ ⟩ | no ¬p | no ¬p₁ =
  -- Maybe we can make this a bit less recursive.
  no λ l<r → <⇒≮ (e< (≮ₒ∧≢ₒ⇒>ₒ ¬p ¬p₁)) l<r

infixl 10 _>ₒ?_
_>ₒ?_ : Decidable (_>ₒ_)
a >ₒ? b = b <ₒ? a


a+b>0 : ∀ {a b} → a > 0 → a + b > 0
a+b>0 (s≤s a>0) = s≤s z≤n


a≤b⇒b≡c⇒a≤c : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
a≤b⇒b≡c⇒a≤c a≤b refl = a≤b

a<b⇒a≡c⇒c<b : ∀ {a b c} → a < b → a ≡ c → c < b
a<b⇒a≡c⇒c<b a<b refl = a<b


b+a>0 : ∀ {a b} → b > 0 → a + b > 0
b+a>0 {a = a} b>0 = ≤-stepsˡ a b>0


a+b>ₑo : ∀ {k e p o} →  ω^ e · k ⟨ p ⟩ >ₑ o → ∀ m → ω^ e · m + k ⟨ b+a>0 p ⟩ >ₑ o
a+b>ₑo zz m = zz
a+b>ₑo (ss x) m = ss x

a<ₒb⇒b≡c⇒a<ₒc : ∀ {a b c} → a <ₒ b → b ≡ c → a <ₒ c
a<ₒb⇒b≡c⇒a<ₒc a<b refl = a<b

a<ₒb⇒a≡c⇒c<ₒb : ∀ {a b c} → a <ₒ b → a ≡ c → c <ₒ b
a<ₒb⇒a≡c⇒c<ₒb a<b refl = a<b

<ₒ-trans : ∀ {a b c} → a <ₒ b → b <ₒ c → a <ₒ c
<ₒ-trans z< (k< x x₁) = z<
<ₒ-trans z< (t< x x₁ b<c) = z<
<ₒ-trans (k< x x₁) (k< x₂ x₃) = k< (trans x x₂) (<-trans x₁ x₃)
<ₒ-trans (k< x x₁) (t< x₂ x₃ b<c) = k< (trans x x₂) (a≤b⇒b≡c⇒a≤c x₁ x₃)
<ₒ-trans (t< x x₁ a<b) (k< x₂ x₃) = k< (trans x x₂) (a<b⇒a≡c⇒c<b x₃ (sym x₁))
<ₒ-trans (t< x x₁ a<b) (t< x₂ x₃ b<c) = t< (trans x x₂) (trans x₁ x₃) (<ₒ-trans a<b b<c)
<ₒ-trans z< (e< y) = z<
<ₒ-trans (e< x) (e< y) = e< (<ₒ-trans x y)
<ₒ-trans (e< x) (k< x₁ x₂) = e< (a<ₒb⇒b≡c⇒a<ₒc x x₁)
<ₒ-trans (e< x) (t< x₁ x₂ y) = e< (a<ₒb⇒b≡c⇒a<ₒc x x₁)
<ₒ-trans (k< x x₁) (e< y) = e< (a<ₒb⇒a≡c⇒c<ₒb y (sym x))
<ₒ-trans (t< x x₁ x₂) (e< y) = e< (a<ₒb⇒a≡c⇒c<ₒb y (sym x))



a≮b⇒a≢b⇒a>b {zero} {zero} a≮b a≢b = contradiction refl a≢b
a≮b⇒a≢b⇒a>b {zero} {suc b} a≮b a≢b = contradiction (s≤s z≤n) a≮b
a≮b⇒a≢b⇒a>b {suc a} {zero} a≮b a≢b = s≤s z≤n
a≮b⇒a≢b⇒a>b {suc a} {suc b} a≮b a≢b = s≤s (a≮b⇒a≢b⇒a>b (λ z₁ → a≮b (s≤s z₁)) (helper a≢b))
  where
   helper : ¬ suc a ≡ suc b → ¬ a ≡ b
   helper ¬sa≡sb a≡b = contradiction (cong suc a≡b) ¬sa≡sb


≮ₒ∧≢ₒ⇒>ₒ {0ₒ} {0ₒ} ¬a<b ¬a≡b = contradiction refl ¬a≡b
≮ₒ∧≢ₒ⇒>ₒ {0ₒ} {x ∷ b ⟨ x₁ ⟩} ¬a<b ¬a≡b = contradiction z< ¬a<b
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {0ₒ} ¬a<b ¬a≡b = z<
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b with OrdTerm.exp x <ₒ? OrdTerm.exp x₂
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | yes p = contradiction (e< p) ¬a<b
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp x₂
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | yes p with OrdTerm.k x <? OrdTerm.k x₂
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | yes p | yes p₁ = contradiction (k< p p₁) ¬a<b
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | yes p | no ¬p₁ with OrdTerm.k x ≟ OrdTerm.k x₂
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | yes p | no ¬p₁ | yes p₁ with a <ₒ? b
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | yes p | no ¬p₁ | yes p₁ | yes p₂ = contradiction (t< p p₁ p₂) ¬a<b
≮ₒ∧≢ₒ⇒>ₒ {(ω^ _ · _ ⟨ pf ⟩) ∷ a ⟨ x₁ ⟩} {(ω^ _ · _ ⟨ pf₁ ⟩) ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | yes p | no ¬p₁ | yes p₁ | no ¬p₂ =
  t< (sym p) (sym p₁) (≮ₒ∧≢ₒ⇒>ₒ ¬p₂ (helper ¬a≡b (cong-ot p₁ p pf pf₁)))
  where
    helper : ∀ {x y l r}.{pf pf₁}
           → ¬ x ∷ l ⟨ pf ⟩ ≡ y ∷ r ⟨ pf₁ ⟩
           → x ≡ y
           → ¬ l ≡ r
    helper {pf = pf} {pf₁ = pf₁} ¬xl≡yr x≡y l≡r = contradiction (cong-o x≡y l≡r pf pf₁) ¬xl≡yr
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | yes p | no ¬p₁ | no ¬p₂ = k< (sym p) (a≮b⇒a≢b⇒a>b ¬p₁ ¬p₂)
≮ₒ∧≢ₒ⇒>ₒ {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} ¬a<b ¬a≡b | no ¬p | no ¬p₁ = e< (≮ₒ∧≢ₒ⇒>ₒ ¬p ¬p₁)

-- Make >ₑ decidable.
infixl 10 _>ₑ?_
_>ₑ?_ : Decidable (_>ₑ_)
a >ₑ? 0ₒ = yes zz
a >ₑ? (x ∷ b ⟨ x₁ ⟩) with OrdTerm.exp a >ₒ? OrdTerm.exp x
(a >ₑ? (x ∷ b ⟨ x₁ ⟩)) | yes p = yes (ss p)
(a >ₑ? (x ∷ b ⟨ x₁ ⟩)) | no ¬p = no λ { (ss q) → contradiction q ¬p }

-- XXX I am not sure whether I can get rid of the recompute.
>ₑ-trans : ∀ {t x l}.{pf} → t >ₑ x ∷ l ⟨ pf ⟩ → t >ₑ l
>ₑ-trans {l = 0ₒ} t>xl = zz
>ₑ-trans {x = y} {x ∷ xs ⟨ px ⟩} {pf} (ss t>y) with recompute (y >ₑ? x ∷ xs ⟨ px ⟩) pf
>ₑ-trans {x = y} {x ∷ xs ⟨ px ⟩} {pf} (ss t>y) | ss y>x = ss (<ₒ-trans y>x t>y)


-- Definition of ordinal addition.
infixl 16 _+ₒ_
_+ₒ_ : Ordinal → Ordinal → Ordinal
x>ₑa+b : ∀ {x xs ys} → x >ₑ xs → x >ₑ ys → x >ₑ xs +ₒ ys 

0ₒ +ₒ b = b
a +ₒ 0ₒ = a
x ∷ xs ⟨ _ ⟩ +ₒ y ∷ ys ⟨ _ ⟩ with OrdTerm.exp x <ₒ? OrdTerm.exp y
x ∷ xs ⟨ _ ⟩ +ₒ b | yes p = b
x ∷ xs ⟨ _ ⟩ +ₒ y ∷ ys ⟨ _ ⟩ | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp y
ω^ e · k ⟨ k>0 ⟩ ∷ xs ⟨ _ ⟩ +ₒ ω^ .e · k₁ ⟨ k₁>0 ⟩ ∷ ys ⟨ pf ⟩ | no ¬p | yes refl =
  ω^ e · k + k₁ ⟨ a+b>0 k>0 ⟩ ∷ ys ⟨ a+b>ₑo pf k ⟩
x ∷ xs ⟨ pf ⟩ +ₒ b | no ¬p | no ¬p₁ =
  x ∷ xs +ₒ b ⟨ x>ₑa+b pf (ss (≮ₒ∧≢ₒ⇒>ₒ ¬p ¬p₁)) ⟩

x>ₑa+b {x} zz zz = zz
x>ₑa+b {x} zz (ss x₁) = ss x₁
x>ₑa+b {x} (ss x₁) zz = ss x₁
x>ₑa+b {x} {o ∷ l ⟨ _ ⟩} {o₁ ∷ l₁ ⟨ _ ⟩} (ss x₁) (ss x₂) with OrdTerm.exp o <ₒ? OrdTerm.exp o₁
x>ₑa+b {x} {o ∷ l ⟨ _ ⟩} {o₁ ∷ l₁ ⟨ _ ⟩} (ss x₁) (ss x₂) | yes p = ss x₂
x>ₑa+b {x} {o ∷ l ⟨ _ ⟩} {o₁ ∷ l₁ ⟨ _ ⟩} (ss x₁) (ss x₂) | no ¬p with OrdTerm.exp o ≟ₒ OrdTerm.exp o₁
x>ₑa+b {x} {ω^ .(OrdTerm.exp o₁) · k ⟨ k>0 ⟩ ∷ l ⟨ _ ⟩} {o₁ ∷ l₁ ⟨ _ ⟩} (ss x₁) (ss x₂) | no ¬p | yes refl = ss x₂
x>ₑa+b {x} {o ∷ l ⟨ _ ⟩} {o₁ ∷ l₁ ⟨ _ ⟩} (ss x₁) (ss x₂) | no ¬p | no ¬p₁ = ss x₁


module _ where
  --test₁ : Ordinal
  test₁ : (n→o 5) +ₒ (n→o 3) ≡ (n→o 8)
  test₁ = refl

  test₂ = ωₒ +ₒ 1ₒ
  
  test₃ : 1ₒ +ₒ ωₒ ≡ ωₒ
  test₃ = refl


a*b>0 : ∀ {a b} → a > 0 → b > 0 → a * b > 0
a*b>0 (s≤s a>0) (s≤s b>0) = s≤s z≤n

-- A fact about >ₑ
-- FIXME this is a specific case of >ₑ-pres, use it instead!
thm : ∀ {k e p o} →  ω^ e · k ⟨ p ⟩ >ₑ o
    → ∀ m → (m>0 : m > 0)
    → ω^ e · k * m ⟨ a*b>0 p m>0 ⟩ >ₑ o
thm zz m m>0 = zz
thm (ss x) m m>0 = ss x

-- Note the dot!  I wonder whether this should be a default case in
-- the standard library.
⊥-elim-irr : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim-irr ()

m<m+n-irr : ∀ m {n} → .(n > 0) → m < m + n
m<m+n-irr zero {suc n} pf with suc n >? 0
m<m+n-irr zero {suc n} pf | yes p = p
m<m+n-irr zero {suc n} pf | no ¬p = ⊥-elim-irr (¬p pf)
m<m+n-irr (suc m) {suc n} pf = s≤s (m<m+n-irr m pf)

a+ₒb>a : ∀ {a b} → ¬ b ≡ 0ₒ → a +ₒ b >ₒ a
a+ₒb>a {0ₒ} {0ₒ} b≢0 = contradiction refl b≢0
a+ₒb>a {0ₒ} {x ∷ b ⟨ x₁ ⟩} b≢0 = z<
a+ₒb>a {x ∷ a ⟨ x₁ ⟩} {0ₒ} b≢0 = contradiction refl b≢0
a+ₒb>a {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} b≢0 with OrdTerm.exp x <ₒ? OrdTerm.exp x₂
a+ₒb>a {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} b≢0 | yes p = e< p
a+ₒb>a {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} b≢0 | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp x₂
a+ₒb>a {ω^ .e · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩} {ω^ e · k₁ ⟨ k>1 ⟩ ∷ b ⟨ x₃ ⟩} b≢0 | no ¬p | yes refl = k< refl (m<m+n-irr k k>1)
a+ₒb>a {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} b≢0 | no ¬p | no ¬p₁ = t< refl refl (a+ₒb>a b≢0)


-- Zero is a neutral elment.
a+0≡a : ∀ {a} → a +ₒ 0ₒ ≡ a
a+0≡a {0ₒ} = refl
a+0≡a {_ ∷ _ ⟨ _ ⟩} = refl

-- A fact about ordinal comprarison.
xthm : ∀ {x xs y ys}.{pf pf₁}
    → x ∷ xs ⟨ pf ⟩ <ₒ y ∷ ys ⟨ pf₁ ⟩
    → ¬ OrdTerm.exp x >ₒ OrdTerm.exp y
xthm (e< l<r) ex>ey = <⇒≮ l<r ex>ey 
xthm (k< x x₁) ex>ey = <ₒ⇒≢ ex>ey (sym x)
xthm (t< x x₁ l<r) ex>ey = <ₒ⇒≢ ex>ey (sym x)


inc-k : ∀ {exp k₁ k₂ c b}.{p₁ pf₁ p₂ pf₂}
      → (ω^ exp · k₁ ⟨ p₁ ⟩ ∷ c ⟨ pf₁ ⟩) <ₒ (ω^ exp · k₂ ⟨ p₂ ⟩ ∷ b ⟨ pf₂ ⟩)
      → ∀ k → .(k>0 : k > 0)
      → (ω^ exp · k + k₁ ⟨ a+b>0 k>0 ⟩ ∷ c ⟨ a+b>ₑo pf₁ k ⟩)
        <ₒ (ω^ exp · k + k₂ ⟨ a+b>0 k>0 ⟩ ∷ b ⟨ a+b>ₑo pf₂ k ⟩)
inc-k (e< l<r) k k>0 = contradiction l<r l≮ₒl
inc-k (k< x x₁) k k>0 = k< refl (+-monoʳ-< k x₁)
inc-k (t< x x₁ l<r) k k>0 = t< refl (cong (k +_) x₁) l<r


-- The >ₒ is preserved under addition on the left.
a+b>a+c : ∀ {a b c} → b >ₒ c → a +ₒ b >ₒ a +ₒ c
a+b>a+c {0ₒ} {x ∷ b ⟨ x₁ ⟩} {0ₒ} b>c = b>c
a+b>a+c {0ₒ} {x ∷ b ⟨ x₁ ⟩} {x₂ ∷ c ⟨ x₃ ⟩} b>c = b>c
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {0ₒ} b>c with OrdTerm.exp x <ₒ? OrdTerm.exp x₂
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {0ₒ} b>c | yes p = e< p
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {0ₒ} b>c | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp x₂
a+b>a+c {ω^ .exp · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ b ⟨ x₃ ⟩} {0ₒ} b>c | no ¬p | yes refl =
  k< refl  (m<m+n-irr k k>1)
-- XXX stupid Agda doesn't reduce a + 0 to a, even though it is a pattern in
-- the definition of +ₒ
a+b>a+c {x ∷ 0ₒ ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {0ₒ} b>c | no ¬p | no ¬p₁ = t< refl refl (a+b>a+c {a = 0ₒ} b>c)
a+b>a+c {x ∷ (x₄ ∷ a ⟨ x₅ ⟩) ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {0ₒ} b>c | no ¬p | no ¬p₁ = t< refl refl (a+b>a+c {a = x₄ ∷ a ⟨ x₅ ⟩} b>c)
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c with OrdTerm.exp x <ₒ? OrdTerm.exp x₂
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | yes p with OrdTerm.exp x <ₒ? OrdTerm.exp x₄
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | yes p | yes p₁ = b>c
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | yes p | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp x₄
a+b>a+c {ω^ .exp · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ c ⟨ x₅ ⟩} b>c | yes p | no ¬p | yes refl = e< p
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | yes p | no ¬p | no ¬p₁ = e< p
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp x₂
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | yes p with OrdTerm.exp x <ₒ? OrdTerm.exp x₄
a+b>a+c {ω^ .exp · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | yes refl | yes p₁ =
  contradiction p₁ (xthm b>c)
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | yes p | no ¬p₁ with OrdTerm.exp x ≟ₒ OrdTerm.exp x₄
a+b>a+c {ω^ .exp · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩} {ω^ exp · k₂ ⟨ k>2 ⟩ ∷ b ⟨ x₃ ⟩} {ω^ .exp · k₁ ⟨ k>1 ⟩ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | yes refl | no ¬p₁ | yes refl = inc-k b>c k k>0
a+b>a+c {ω^ .exp · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | yes refl | no ¬p₁ | no ¬p₂ =
  k< refl (m<m+n-irr k k>1)
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | no ¬p₁ with OrdTerm.exp x <ₒ? OrdTerm.exp x₄
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | no ¬p₁ | yes p =
  contradiction (<ₒ-trans (≮ₒ∧≢ₒ⇒>ₒ ¬p ¬p₁) p) (xthm b>c) -- contra
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | no ¬p₁ | no ¬p₂ with OrdTerm.exp x ≟ₒ OrdTerm.exp x₄
a+b>a+c {ω^ .exp · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | no ¬p₁ | no ¬p₂ | yes refl =
  contradiction (≮ₒ∧≢ₒ⇒>ₒ ¬p ¬p₁) (xthm b>c) --contra as well
a+b>a+c {x ∷ a ⟨ x₁ ⟩} {x₂ ∷ b ⟨ x₃ ⟩} {x₄ ∷ c ⟨ x₅ ⟩} b>c | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = t< refl refl (a+b>a+c {a = a} b>c)


-- Definition of multiplication together with the
-- theorem about the recursive call (similarly to +ₒ)
infixl 19 _*ₒ_
_*ₒ_ : Ordinal → Ordinal → Ordinal
x>ₑa*b : ∀{e k e₁ k₁ a b}.{p p₁}
       → ω^ e₁ · k₁ ⟨ p ⟩ >ₑ b
       → .(pf :  ω^ e · k ⟨ p₁ ⟩ >ₑ a)
       → ¬ e₁ ≡ 0ₒ
       → ω^ e +ₒ e₁ · k₁ ⟨ p ⟩ >ₑ (ω^ e · k ⟨ p₁ ⟩ ∷ a ⟨ pf ⟩) *ₒ b

0ₒ *ₒ _ = 0ₒ
_ *ₒ 0ₒ = 0ₒ
x ∷ a ⟨ x₁ ⟩ *ₒ x₂ ∷ b ⟨ x₃ ⟩ with OrdTerm.exp x₂ ≟ₒ 0ₒ
ω^ e · k ⟨ p ⟩ ∷ a ⟨ x₁ ⟩ *ₒ ω^ e₁ · k₁ ⟨ p₁ ⟩ ∷ _ ⟨ x₃ ⟩ | yes ≡0 =
  -- (ω^α·x + rest) * ω^0·y = ω^α·(x*y) + rest
  ω^ e · k * k₁  ⟨ a*b>0 p p₁ ⟩ ∷ a ⟨ thm x₁ k₁ p₁ ⟩
ω^ e · k ⟨ p ⟩ ∷ a ⟨ x₁ ⟩ *ₒ ω^ e₁ · k₁ ⟨ p₁ ⟩ ∷ b ⟨ x₃ ⟩ | no ≢0 =
  -- ω^α·x * ω^β·y | β > 0 =  ω^(α+b)·y 
  ω^ (e +ₒ e₁) · k₁ ⟨ p₁ ⟩
  ∷ ω^ e · k ⟨ p ⟩ ∷ a ⟨ x₁ ⟩ *ₒ b ⟨ x>ₑa*b x₃ x₁ ≢0 ⟩


n≢0⇒n>ₒ0 : ∀ {n} → ¬ n ≡ 0ₒ → n >ₒ 0ₒ 
n≢0⇒n>ₒ0 {0ₒ} n≢0 = contradiction refl n≢0
n≢0⇒n>ₒ0 {x ∷ n ⟨ x₁ ⟩} n≢0 = z<

m+n>m : ∀ {m n} → ¬ n ≡ 0ₒ → m +ₒ n >ₒ m
m+n>m {m} {n} n≢0 = let
  pf = a+b>a+c {a = m}  (n≢0⇒n>ₒ0 n≢0)
  eq = cong₂ _>ₒ_ (refl {x = m +ₒ n}) (a+0≡a {a = m})
  in subst (λ x → x) eq pf 

x>ₑa*b {a = 0ₒ} {0ₒ} >b >a ≢0 = zz
x>ₑa*b {a = 0ₒ} {x ∷ _ ⟨ _ ⟩} _ _ ≢0 with OrdTerm.exp x ≟ₒ 0ₒ
x>ₑa*b {a = 0ₒ} {_ ∷ _ ⟨ _ ⟩} _ _ ≢0 | yes p = ss (m+n>m ≢0)
x>ₑa*b {e = e}{a = 0ₒ} {_ ∷ _ ⟨ _ ⟩} (ss x) _ ≢0 | no ¬p = ss (a+b>a+c {a = e} x)
x>ₑa*b {a = _ ∷ _ ⟨ _ ⟩} {0ₒ} _ _ ≢0 = zz
x>ₑa*b {a = x ∷ _ ⟨ _ ⟩} {_ ∷ _ ⟨ _ ⟩} _ _ ≢0 with OrdTerm.exp x ≟ₒ 0ₒ
x>ₑa*b {a = _ ∷ _ ⟨ _ ⟩} {x₂ ∷ _ ⟨ _ ⟩} _ _ ≢0 | yes p with OrdTerm.exp x₂ ≟ₒ 0ₒ
x>ₑa*b {a = _ ∷ _ ⟨ _ ⟩} {_ ∷ _ ⟨ _ ⟩} _ _ ≢0 | yes p | yes p₁ = ss (m+n>m ≢0)
x>ₑa*b {e = e}{a = _ ∷ _ ⟨ _ ⟩} {_ ∷ _ ⟨ _ ⟩} (ss x) _ ≢0 | yes p | no ¬p = ss (a+b>a+c {a = e} x)
x>ₑa*b {a = _ ∷ _ ⟨ _ ⟩} {x₂ ∷ _ ⟨ _ ⟩} _ _ ≢0 | no ¬p with  OrdTerm.exp x₂ ≟ₒ 0ₒ
x>ₑa*b {a = _ ∷ _ ⟨ _ ⟩} {_ ∷ _ ⟨ _ ⟩} _ _ ≢0 | no ¬p | yes p = ss (m+n>m ≢0)
x>ₑa*b {e = e}{a = _ ∷ _ ⟨ _ ⟩} {_ ∷ _ ⟨ _ ⟩} (ss x) _ ≢0 | no ¬p | no ¬p₁ = ss (a+b>a+c {a = e} x)


_-safe-_ : (a : ℕ) → (b : ℕ) .{≥ : a ≥ b} → ℕ
a -safe- b = a ∸ b

-- Definition of ≥ for ordinals.
infixl 10 _≥ₒ_
_≥ₒ_ : Ordinal → Ordinal → Set
a ≥ₒ b = a >ₒ b ⊎ a ≡ b

0≱ₒs : ∀ {t o pf} → 0ₒ ≥ₒ t ∷ o ⟨ pf ⟩ → ⊥
0≱ₒs {t} {o} (inj₁ ())
0≱ₒs {t} {o} (inj₂ ())

>⇒≥ : ∀ {a b} → a > b → a ≥ b
>⇒≥ a>b = <⇒≤ a>b

-- The >ₑ relation does not depend on the `k` coefficient.
>ₑ-pres : ∀ {e x px o} → ω^ e · x ⟨ px ⟩ >ₑ o
        → ∀ {y py} → ω^ e · y ⟨ py ⟩ >ₑ o
>ₑ-pres zz = zz
>ₑ-pres (ss x) = ss x

-- A fact about ordinal comparison.
a>ₒb⇒ha≡hb⇒ta>ₒtb : ∀ {x l pl y r pr} → x ∷ l ⟨ pl ⟩ ≥ₒ y ∷ r ⟨ pr ⟩
                   → ¬ OrdTerm.exp x >ₒ OrdTerm.exp y
                   → ¬ OrdTerm.k x > OrdTerm.k y
                   → l ≥ₒ r
a>ₒb⇒ha≡hb⇒ta>ₒtb (inj₂ refl) ¬e> ¬k> = inj₂ refl
a>ₒb⇒ha≡hb⇒ta>ₒtb (inj₁ (e< x)) ¬e> ¬k> = contradiction x ¬e>
a>ₒb⇒ha≡hb⇒ta>ₒtb (inj₁ (k< x x₁)) ¬e> ¬k> = contradiction x₁ ¬k>
a>ₒb⇒ha≡hb⇒ta>ₒtb (inj₁ (t< x x₁ x₂)) ¬e> ¬k> = inj₁ x₂

-- Left subtraction.
infixl 16 _-ₒ_
_-ₒ_ : (a b : Ordinal) → .{≥ : a ≥ₒ b} →  Ordinal
(a -ₒ 0ₒ) {a≥b} = a
(0ₒ -ₒ (x ∷ b ⟨ x₁ ⟩)) {a≥b} = ⊥-elim-irr (0≱ₒs a≥b)
((x ∷ l ⟨ pl ⟩) -ₒ (y ∷ r ⟨ pr ⟩)) {a≥b} with OrdTerm.exp x >ₒ? OrdTerm.exp y
((x ∷ l ⟨ pl ⟩) -ₒ (y ∷ r ⟨ pr ⟩)) {a≥b} | yes p = x ∷ l ⟨ pl ⟩
((x ∷ l ⟨ pl ⟩) -ₒ (y ∷ r ⟨ pr ⟩)) {a≥b} | no ¬p with OrdTerm.k x >? OrdTerm.k y
  -- Exponents can only be equal, as a ≥ b and exp a ≯ exp b.
((ω^ e · k ⟨ k>0 ⟩ ∷ l ⟨ pl ⟩) -ₒ (y ∷ r ⟨ pr ⟩)) {a≥b} | no ¬p | yes p =
  ω^ e · ((k -safe- OrdTerm.k y) {>⇒≥ p}) ⟨ m<n⇒0<n∸m p ⟩
  ∷ l ⟨ >ₑ-pres pl ⟩
((x ∷ l ⟨ pl ⟩) -ₒ (y ∷ r ⟨ pr ⟩)) {a≥b} | no ¬p | no ¬p₁ =
  (l -ₒ r) {a>ₒb⇒ha≡hb⇒ta>ₒtb a≥b ¬p ¬p₁}


o-0<suc : ∀ {x l pl} → 0ₒ <ₒ x ∷ l ⟨ pl ⟩
o-0<suc = z<

-- Juggling comparison operators.
o-≮⇒≥ : ∀ {a b} → ¬ a <ₒ b → a ≥ₒ b
o-≮⇒≥ {0ₒ} {0ₒ} ¬a<b = inj₂ refl
o-≮⇒≥ {0ₒ} {x ∷ b ⟨ x₁ ⟩} ¬a<b = contradiction z< ¬a<b
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {0ₒ} ¬a<b = inj₁ z<
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b with OrdTerm.exp x <ₒ? OrdTerm.exp y
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | yes p = contradiction (e< p) ¬a<b
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp y
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p with OrdTerm.k x <? OrdTerm.k y
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p | yes p₁ = contradiction (k< p p₁) ¬a<b
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p | no ¬p₁ with OrdTerm.k x ≟ OrdTerm.k y
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p | no ¬p₁ | yes p₁ with a <ₒ? b
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p | no ¬p₁ | yes p₁ | yes p₂ = contradiction (t< p p₁ p₂) ¬a<b
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p | no ¬p₁ | yes p₁ | no ¬p₂ with o-≮⇒≥ ¬p₂
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p | no ¬p₁ | yes p₁ | no ¬p₂ | inj₁ x₂ = inj₁ (t< (sym p) (sym p₁) x₂)
o-≮⇒≥ {ω^ e · k ⟨ k>0 ⟩ ∷ a ⟨ x₁ ⟩}
       {ω^ .e · .k ⟨ k>1 ⟩ ∷ .a ⟨ x₃ ⟩}
                                    ¬a<b | no ¬p | yes refl | no ¬p₁ | yes refl | no ¬p₂ | inj₂ refl =
  inj₂ (cong-o refl refl x₁ x₃)
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | yes p | no ¬p₁ | no ¬p₂ = inj₁ (k< (sym p) (a≮b⇒a≢b⇒a>b ¬p₁ ¬p₂))
o-≮⇒≥ {x ∷ a ⟨ x₁ ⟩} {y ∷ b ⟨ x₃ ⟩} ¬a<b | no ¬p | no ¬p₁ = inj₁ (e< (≮ₒ∧≢ₒ⇒>ₒ ¬p ¬p₁))



-- XXX get rid of this.
module _ where
-- private
  a = ω^ (n→o 5) · 1 ⟨ s≤s z≤n ⟩ ∷ 1ₒ ⟨ ss z< ⟩

  b = ωₒ *ₒ ωₒ *ₒ ωₒ +ₒ ωₒ *ₒ ωₒ +ₒ ωₒ

  c = b *ₒ (ωₒ +ₒ 1ₒ)

-- A simple fact about ordinal comparison
xhelper : ∀ {x₂ b₁}.{pl}{x a₁}.{pr} → (x₂ ∷ b₁ ⟨ pl ⟩) <ₒ (x ∷ a₁ ⟨ pr ⟩)
       → (OrdTerm.exp x₂ <ₒ OrdTerm.exp x → ⊥)
       → (OrdTerm.k x₂ < OrdTerm.k x → ⊥)
       → (x₂ ≡ x) × (b₁ <ₒ a₁)
xhelper x<l ¬e< ¬k< with o-≮⇒≥ ¬e<
xhelper x<l ¬e< ¬k< | inj₁ x = contradiction (e< x) (<⇒≮ x<l)
xhelper (e< x<l) ¬e< ¬k< | inj₂ refl = ⊥-elim-irr (l≮ₒl x<l)
xhelper (k< x x₁) ¬e< ¬k< | inj₂ refl = ⊥-elim-irr (¬k< x₁)
xhelper (t< refl refl x<l) ¬e< ¬k< | inj₂ refl = refl , x<l


-- One of the +ₒ subcases made explicit.
x+y|ex>ey : ∀ {x xs oy}.{px}
          → (pf : x >ₑ oy)
          → x ∷ xs ⟨ px ⟩ +ₒ oy ≡ x ∷ xs +ₒ oy ⟨  x>ₑa+b px pf ⟩
x+y|ex>ey {x} {xs} {0ₒ} {px} pf = cong-o refl (sym a+0≡a) px (x>ₑa+b px pf) 
x+y|ex>ey {x} {xs} {x₁ ∷ oy ⟨ x₂ ⟩} pf with OrdTerm.exp x <ₒ? OrdTerm.exp x₁
x+y|ex>ey {x} {xs} {x₁ ∷ oy ⟨ x₂ ⟩} (ss x₃) | yes p = contradiction x₃ (<⇒≮ p)
x+y|ex>ey {x} {xs} {x₁ ∷ oy ⟨ x₂ ⟩} pf | no ¬p with OrdTerm.exp x ≟ₒ OrdTerm.exp x₁
x+y|ex>ey {ω^ .exp · k ⟨ k>0 ⟩} {xs} {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ oy ⟨ x₂ ⟩} (ss x) | no ¬p | yes refl = ⊥-elim-irr (l≮ₒl x)
x+y|ex>ey {x} {xs} {x₁ ∷ oy ⟨ x₂ ⟩} (ss x₃) | no ¬p | no ¬p₁ = refl



x>ₑa⇒x>ₑa-b : ∀ {x a b}.{pf} → x >ₑ a → x >ₑ (a -ₒ b) {pf}
x>ₑa⇒x>ₑa-b {x} {.0ₒ} {0ₒ} zz = zz
x>ₑa⇒x>ₑa-b {x} {.0ₒ} {x₁ ∷ b₁ ⟨ x₂ ⟩} {pf} zz = ⊥-elim-irr (0≱ₒs pf)
x>ₑa⇒x>ₑa-b {x} {.(_ ∷ _ ⟨ _ ⟩)} {0ₒ} (ss x₁) = ss x₁
x>ₑa⇒x>ₑa-b {x} {(o ∷ _ ⟨ _ ⟩)} {x₂ ∷ b₁ ⟨ x₃ ⟩} (ss x₁) with OrdTerm.exp o >ₒ? OrdTerm.exp x₂
x>ₑa⇒x>ₑa-b {x} {o ∷ _ ⟨ _ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} (ss x₁) | yes p = ss x₁
x>ₑa⇒x>ₑa-b {x} {o ∷ _ ⟨ _ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} (ss x₁) | no ¬p with OrdTerm.k o >? OrdTerm.k x
x>ₑa⇒x>ₑa-b {x} {o ∷ _ ⟨ _ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} (ss x₁) | no ¬p | yes p with OrdTerm.k x₂ <? OrdTerm.k o
x>ₑa⇒x>ₑa-b {x} {o ∷ _ ⟨ _ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} (ss x₁) | no ¬p | yes p | yes p₁ = ss x₁
x>ₑa⇒x>ₑa-b {x} {o ∷ xs ⟨ _ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} pf | no ¬p | yes p | no ¬p₁ =
  x>ₑa⇒x>ₑa-b {b = b₁} (>ₑ-trans pf)
x>ₑa⇒x>ₑa-b {x} {o ∷ _ ⟨ _ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} (ss x₁) | no ¬p | no ¬p₁ with OrdTerm.k x₂ <? OrdTerm.k o
x>ₑa⇒x>ₑa-b {x} {o ∷ _ ⟨ _ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} (ss x₁) | no ¬p | no ¬p₁ | yes p = ss x₁
x>ₑa⇒x>ₑa-b {x} {o ∷ xs ⟨ pp ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} pf | no ¬p | no ¬p₁ | no ¬p₂ =
  x>ₑa⇒x>ₑa-b {b = b₁} (>ₑ-trans pf)


a-a≡0 : ∀ {a} → (a -ₒ a) {inj₂ refl} ≡ 0ₒ
a-a≡0 {0ₒ} = refl
a-a≡0 {x ∷ a ⟨ x₁ ⟩} with OrdTerm.exp x >ₒ? OrdTerm.exp x
a-a≡0 {x ∷ a ⟨ x₁ ⟩} | yes p = contradiction p l≮ₒl 
a-a≡0 {x ∷ a ⟨ x₁ ⟩} | no ¬p with OrdTerm.k x >? OrdTerm.k x
a-a≡0 {x ∷ a ⟨ x₁ ⟩} | no ¬p | yes p = ⊥-elim-irr (<-irrefl refl p)
a-a≡0 {x ∷ a ⟨ x₁ ⟩} | no ¬p | no ¬p₁ = a-a≡0 {a = a}


-- Sanity check for left subtraction.
b+a-b≡b : ∀ {a b} → (≥ : a ≥ₒ b) → b +ₒ (a -ₒ b) {≥} ≡ a
b+a-b≡b {0ₒ} {0ₒ} a≥b = refl
b+a-b≡b {0ₒ} {x ∷ b₁ ⟨ x₁ ⟩} a≥b = ⊥-elim-irr (0≱ₒs a≥b) 
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {0ₒ} a≥b = refl
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b with OrdTerm.exp x >ₒ? OrdTerm.exp x₂
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | yes p with OrdTerm.exp x₂ <ₒ? OrdTerm.exp x
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | yes p | yes p₁ = refl
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | yes p | no ¬p with OrdTerm.exp x₂ ≟ₒ OrdTerm.exp x
b+a-b≡b {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ a₁ ⟨ x₁ ⟩} {ω^ .exp · k ⟨ k>0 ⟩ ∷ b₁ ⟨ x₃ ⟩} a≥b | yes p | no ¬p | yes refl = ⊥-elim-irr (l≮ₒl p)
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | yes p | no ¬p | no ¬p₁ = contradiction p ¬p
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | no ¬p with OrdTerm.k x >? OrdTerm.k x₂
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | no ¬p | yes p with OrdTerm.exp x₂ <ₒ? OrdTerm.exp x
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | no ¬p | yes p | yes p₁ = contradiction p₁ ¬p
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} a≥b | no ¬p | yes p | no ¬p₁ with OrdTerm.exp x₂ ≟ₒ OrdTerm.exp x
b+a-b≡b {ω^ exp · k₁ ⟨ k>1 ⟩ ∷ a₁ ⟨ x₁ ⟩} {ω^ .exp · k ⟨ k>0 ⟩ ∷ b₁ ⟨ x₃ ⟩} a≥b | no ¬p | yes p | no ¬p₁ | yes refl =
  cong-o (cong-ot (m+[n∸m]≡n (helper a≥b))
         refl
         (subst (_> 0) (sym (m+[n∸m]≡n (helper a≥b))) k>1) k>1)
         refl
         (>ₑ-pres x₁)
         x₁
  where
    helper : ∀ {e k k₁}.{pk pk₁}{a b}.{pa pb}
           → (ω^ e · k ⟨ pk ⟩ ∷ a ⟨ pa ⟩) ≥ₒ (ω^ e · k₁ ⟨ pk₁ ⟩ ∷ b ⟨ pb ⟩)
           → k ≥ k₁
    helper (inj₁ (e< x)) = ⊥-elim-irr (l≮ₒl x)
    helper (inj₁ (k< x x₁)) = <⇒≤ x₁
    helper (inj₁ (t< x x₁ x₂)) rewrite x₁ = ≤-refl
    helper (inj₂ refl) = ≤-refl  
b+a-b≡b {ω^ exp · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₁ ⟩} {ω^ exp₁ · k₁ ⟨ k>1 ⟩ ∷ b₁ ⟨ x₃ ⟩} (inj₁ x) | no ¬p | yes p | no ¬p₁ | no ¬p₂ =
  contradiction (e< (≮ₒ∧≢ₒ⇒>ₒ ¬p₁ ¬p₂) ) (<⇒≮ x ) 
b+a-b≡b {ω^ exp · k ⟨ k>0 ⟩ ∷ a₁ ⟨ x₁ ⟩} {ω^ exp₁ · k₁ ⟨ k>1 ⟩ ∷ b₁ ⟨ x₃ ⟩} (inj₂ y) | no ¬p | yes p | no ¬p₁ | no ¬p₂ =
  contradiction (sym (ot=pk (o=ph y))) (<⇒≢ p)
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {x₂ ∷ b₁ ⟨ x₃ ⟩} (inj₁ x₄) | no ¬p | no ¬p₁ with (proj₁ (xhelper x₄ ¬p ¬p₁))
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {.x ∷ b₁ ⟨ x₃ ⟩} (inj₁ x₄) | no ¬p | no ¬p₁ | refl = let
  a>b = proj₂ (xhelper x₄ ¬p ¬p₁)
  r = b+a-b≡b {a = a₁} {b = b₁} (inj₁ a>b)
  xb+a =  x+y|ex>ey {xs = b₁} (x>ₑa⇒x>ₑa-b {b = b₁} (recompute (x >ₑ? a₁) x₁)) 
  in trans xb+a (cong-o refl r (x>ₑa+b x₃ (x>ₑa⇒x>ₑa-b {b = b₁} x₁)) x₁)
b+a-b≡b {x ∷ a₁ ⟨ x₁ ⟩} {.x ∷ .a₁ ⟨ x₃ ⟩} (inj₂ refl) | no ¬p | no ¬p₁ rewrite (a-a≡0 {a = a₁}) = refl



module _ where
  x = ω^ (n→o 5) · 6 ⟨ s≤s z≤n ⟩ ∷ (ωₒ *ₒ (n→o 3)) ⟨ ss (k< refl (s≤s (s≤s z≤n))) ⟩
  y = ω^ (n→o 2) · 7 ⟨ s≤s z≤n ⟩ ∷ (1ₒ) ⟨ ss z< ⟩ 
  p = ω^ (n→o 3) · 6 ⟨ s≤s z≤n ⟩ ∷ [] ⟨ zz ⟩
  q = ωₒ *ₒ (n→o 3)

  div-thm₁ : y *ₒ p +ₒ q ≡ x
  div-thm₁ = refl


>⇒≢ : ∀ {x} → x > 0 → x ≢ 0
>⇒≢ (s≤s x>0) = λ ()

a≥b⇒ea≥eb : ∀ {k c}.{p₁}{ra}.{pa}{l d}.{p₂}{rb}.{pb}
           → ω^ k · c ⟨ p₁ ⟩ ∷ ra ⟨ pa ⟩  ≥ₒ ω^ l · d ⟨ p₂ ⟩ ∷ rb ⟨ pb ⟩
           → k ≥ₒ l
a≥b⇒ea≥eb (inj₁ (e< x₁)) = inj₁ x₁
a≥b⇒ea≥eb (inj₁ (k< x₁ x₂)) = inj₂ (sym x₁)
a≥b⇒ea≥eb (inj₁ (t< x₁ x₂ x₃)) = inj₂ (sym x₁)
a≥b⇒ea≥eb (inj₂ refl) = inj₂ refl

a≥b⇒ka≥kb : ∀ {k c}.{p₁}{ra}.{pa}{l d}.{p₂}{rb}.{pb}
           → ω^ k · c ⟨ p₁ ⟩ ∷ ra ⟨ pa ⟩  ≥ₒ ω^ l · d ⟨ p₂ ⟩ ∷ rb ⟨ pb ⟩
           → k ≡ l
           → c ≥ d
a≥b⇒ka≥kb (inj₁ (e< x₁)) refl = ⊥-elim-irr (l≮ₒl x₁)
a≥b⇒ka≥kb (inj₁ (k< x₁ x₂)) k≡l = <⇒≤ x₂
a≥b⇒ka≥kb (inj₁ (t< x₁ x₂ x₃)) refl rewrite x₂ = ≤-refl
a≥b⇒ka≥kb (inj₂ refl) _ = ≤-refl

a≥b⇒ra≥rb : ∀ {k c}.{p₁}{ra}.{pa}{l d}.{p₂}{rb}.{pb}
           → ω^ k · c ⟨ p₁ ⟩ ∷ ra ⟨ pa ⟩  ≥ₒ ω^ l · d ⟨ p₂ ⟩ ∷ rb ⟨ pb ⟩
           → k ≡ l
           → c ≡ d
           → ra ≥ₒ rb
a≥b⇒ra≥rb (inj₁ (e< x₁)) refl refl = contradiction x₁ l≮ₒl
a≥b⇒ra≥rb {d = d} (inj₁ (k< x₁ x₂)) refl refl = contradiction x₂ (n≮n d)
a≥b⇒ra≥rb (inj₁ (t< x₁ x₂ x₃)) refl refl = inj₁ x₃
a≥b⇒ra≥rb (inj₂ x₂) refl refl = inj₂ (o=pt x₂)


ra≥rb⇒a≥b : ∀ {k c}.{p₁}{ra}.{pa}{l d}.{p₂}{rb}.{pb}
           → k ≡ l
           → c ≡ d
           → ra ≥ₒ rb
           → ω^ k · c ⟨ p₁ ⟩ ∷ ra ⟨ pa ⟩  ≥ₒ ω^ l · d ⟨ p₂ ⟩ ∷ rb ⟨ pb ⟩
ra≥rb⇒a≥b k≡l c≡d (inj₁ x₁) = inj₁ (t< (sym k≡l) (sym c≡d) x₁)
ra≥rb⇒a≥b refl refl (inj₂ refl) = inj₂ refl           

ka≥kb⇒a≥b : ∀ {k c}.{p₁}{ra}.{pa}{l d}.{p₂}{rb}.{pb}
           → k ≡ l
           → c ≥ d
           → ra ≥ₒ rb
           → ω^ k · c ⟨ p₁ ⟩ ∷ ra ⟨ pa ⟩  ≥ₒ ω^ l · d ⟨ p₂ ⟩ ∷ rb ⟨ pb ⟩
ka≥kb⇒a≥b k≡l c≥d ra≥rb with m≤n⇒m<n∨m≡n c≥d
ka≥kb⇒a≥b k≡l c≥d ra≥rb | inj₁ x₁ = inj₁ (k< (sym k≡l) x₁)
ka≥kb⇒a≥b k≡l c≥d ra≥rb | inj₂ y₁ = ra≥rb⇒a≥b k≡l (sym y₁) ra≥rb


a>1⇒a-1>0 : ∀ {a} → a > 1 → a ∸ 1 > 0
a>1⇒a-1>0 (s≤s a>1) = a>1

c-d<c : ∀ {c d} → .(d ≢ 0) → .(c ≢ 0) → c ∸ d < c
c-d<c {c} {zero} d≢0 c≢0 = ⊥-elim-irr (d≢0 refl)
c-d<c {zero} {suc d} d≢0 c≢0 = ⊥-elim-irr (c≢0 refl)
c-d<c {suc c₁} {suc d} d≢0 c≢0 = s≤s (m∸n≤m c₁ d)


d*[c/d-1]<c : ∀ {d c}
            → (d≢0 : d ≢ 0)
            → .(c≢0 : c ≢ 0)
            → let c/d = (c / d) {fromWitnessFalse d≢0} in
              d * c/d ≡ c
            → c/d > 1
            → d * (c/d ∸ 1) < c
d*[c/d-1]<c {d}{c} d≢0 c≢0 d*c/d≡c c/d>1
   rewrite (*-distribˡ-∸ d ((c / d) {fromWitnessFalse d≢0}) 1)
           | d*c/d≡c
           | *-identityʳ d = c-d<c d≢0 c≢0

a>0⇒a≯1⇒a≡1 : ∀ {a} → a > 0 → ¬ a > 1 → a ≡ 1
a>0⇒a≯1⇒a≡1 {suc zero} a>0 a≯1 = refl
a>0⇒a≯1⇒a≡1 {suc (suc a₁)} a>0 a≯1 = contradiction (s≤s (s≤s z≤n)) a≯1

≥⇒≮ : ∀ {a b} → a ≥ₒ b → ¬ a <ₒ b
≥⇒≮ (inj₁ x) = <⇒≮ x
≥⇒≮ (inj₂ refl) a<b = contradiction a<b l≮ₒl

d*c/d≡c⇒c/d≡1⇒c≡d : ∀ {c d}
                   → (≢0 : d ≢ 0)
                   → let c/d = (c / d){fromWitnessFalse ≢0} in
                     d * c/d ≡ c
                   → c/d ≡ 1
                   → c ≡ d
d*c/d≡c⇒c/d≡1⇒c≡d {d = d} d≢0 d*c/d≡c c/d≡1
                   rewrite c/d≡1 | *-identityʳ d  = sym d*c/d≡c
                   


infixl 19 _divmodₒ_
_divmodₒ_ : (a b : Ordinal) → .{≢0 : b ≢ 0ₒ} → Ordinal × Ordinal
_divmodₒ_ a b {≢0} with a <ₒ? b
(a divmodₒ b) {≢0} | yes p = 0ₒ , a
(0ₒ divmodₒ 0ₒ) {≢0} | no ¬p = ⊥-elim-irr (≢0 refl)
(0ₒ divmodₒ (x ∷ b ⟨ x₁ ⟩)) {≢0} | no ¬p = 0ₒ , (x ∷ b ⟨ x₁ ⟩)
((x ∷ a ⟨ x₁ ⟩) divmodₒ 0ₒ) {≢0} | no ¬p = ⊥-elim-irr (≢0 refl)
((ω^ k · c ⟨ c>0 ⟩ ∷ ra ⟨ x₁ ⟩) divmodₒ (ω^ l · d ⟨ d>0 ⟩ ∷ rb ⟨ x₃ ⟩)) {≢0} | no ¬p with a≥b⇒ea≥eb (o-≮⇒≥ ¬p)
((ω^ k · c ⟨ c>0 ⟩ ∷ ra ⟨ x₁ ⟩) divmodₒ (ω^ l · d ⟨ d>0 ⟩ ∷ rb ⟨ x₃ ⟩)) {≢0} | no ¬p | inj₂ k≡l =
  -- when k = l, we have:
  -- ω^k·c+ra // w^l·d+rb
  --   p = c div d
  --   bp = w^l·(d*(c div d)) + ⋯
  --   a - bp = ω^k·c - ω^k(d*(c div d)) + ⋯
  --   => if c = d*(c div d) and ra ≥ rb then
  --         [p, a-bp]
  --       else
  --         [p-1, a-b(p-1)]
  let
    d>0 = recompute (d >? 0) d>0
    c/d = (c / d) {fromWitnessFalse (>⇒≢ d>0)}
    c/d>0 = m≥n⇒m/n>0 (a≥b⇒ka≥kb (o-≮⇒≥ ¬p) k≡l) -- (>⇒≢ d>0)
    p = ω^ 0ₒ · c/d ⟨ c/d>0 ⟩ ∷ [] ⟨ zz ⟩
    a = ω^ k · c ⟨ c>0 ⟩ ∷ ra ⟨ x₁ ⟩
    b = ω^ l · d ⟨ d>0 ⟩ ∷ rb ⟨ x₃ ⟩
  in case d * c/d ≟ c of λ where
       (yes d*c/d≡c) → case ra <ₒ? rb of λ where
          (yes ra<rb) →
               -- The result of the division in this case is p-1
               (p -ₒ 1ₒ) { ka≥kb⇒a≥b refl c/d>0 (inj₂ refl) }
               ,
               -- The remainder is (a -ₒ b *ₒ p-1) which
               -- I build manually so that the proofs become simpler.
               (case c/d >? 1 of λ where
                 (yes c/d>1) → let
                      c/d-1>0 = a>1⇒a-1>0 c/d>1
                      c/d-1 = ω^ 0ₒ · (c/d -safe- 1) {<⇒≤ c/d>1} ⟨ c/d-1>0 ⟩ ∷ [] ⟨ zz ⟩
                      in (a -ₒ b *ₒ c/d-1) { inj₁ (k< (sym k≡l) (d*[c/d-1]<c (>⇒≢ d>0) (>⇒≢ c>0) d*c/d≡c c/d>1)) }
                 -- contradiction
                 --   c/d≤1 ∧ c/d>0 ⇒ c/d≡1 ⇒ c ≡ d
                 --   k ≡ l ∧ c ≡ d ⇒ a ≥ b iff ra ≥ rb
                 --   however ra < rb ⇒ contradiction
                 (no c/d≯1) → contradiction
                                ra<rb
                                (≥⇒≮ (a≥b⇒ra≥rb
                                          (o-≮⇒≥ ¬p)
                                          k≡l
                                          (d*c/d≡c⇒c/d≡1⇒c≡d (>⇒≢ d>0) d*c/d≡c (a>0⇒a≯1⇒a≡1 c/d>0 c/d≯1)) )))
          (no  ra≮rb) → p , (a -ₒ b *ₒ p)
                             { ra≥rb⇒a≥b k≡l (sym d*c/d≡c) (o-≮⇒≥ ra≮rb) }
       (no  d*c/d≢c) → p , (a -ₒ b *ₒ p)
                           { inj₁ (k< (sym k≡l) (≤∧≢⇒< (subst (_≤ c)
                                                               (*-comm c/d d)
                                                               (m/n*n≤m c d {fromWitnessFalse (>⇒≢ d>0)}))
                                                d*c/d≢c)) }

((ω^ k · c ⟨ c>0 ⟩ ∷ ra ⟨ x₁ ⟩) divmodₒ (ω^ l · d ⟨ d>0 ⟩ ∷ rb ⟨ x₃ ⟩)) {≢0} | no ¬p | inj₁ k>l =
  -- ω^k·c+ra // ω^l·d+rb | k > l
  -- p = ω^(k-l)·c
  -- bp = (ω^l·d+rb)*ω^(k-l)·c  | k-l > 0
  --    = ω^(l+(k-l))·c + (ω^l·d+rb) * 0
  --    = ω^k·c
  -- a-bp = ra
  -- p', q' = ra // b
  -- => p+p′, q
  -- proof:
  --    b*p'+q' = ra
  --    b*(p+p')+q' ≟ a
  --    bp + bp' + q' ≟ a | left distributivity
  --    bp + ra ≟ ra      | first assumption
  --    bp + ra = ra      | as bp = ω^k·c
  let
    k-l = (k -ₒ l) { inj₁ k>l }
    p = ω^ k-l · c ⟨ c>0 ⟩ ∷ [] ⟨ zz ⟩
    b = ω^ l · d ⟨ d>0 ⟩ ∷ rb ⟨ x₃ ⟩
    p' , q' = (ra divmodₒ b) { λ () }
  in (p +ₒ p') , q'
  

-- XXX Write more tests or better prove that
-- ∀ x y y≢0 → div-check x y y≢0
module divtests where
  div-check : (x y : Ordinal) → (≢0 : y ≢ 0ₒ) → Set
  div-check x y ≢0 = let p , q = (x divmodₒ y) {≢0} in
                     q <ₒ y × y *ₒ p +ₒ q ≡ x
            
  -- ω^2·3+5 / ω^2·3+1 = (1ₒ , (n-o 4))
  divtest₁ : div-check  (ω^ (n→o 2) · 3 ⟨ s≤s z≤n ⟩ ∷ (n→o 5)  ⟨ ss z< ⟩)
                       (ω^ (n→o 2) · 3 ⟨ s≤s z≤n ⟩ ∷ 1ₒ ⟨ ss z< ⟩)
                       λ () 
  divtest₁ = e< z< , refl

  -- ω^2·4+1 / ω^2·2+3  = (1ₒ , (ω^2·2 + 1))
  divtest₂ : div-check  (ω^ (n→o 2) · 4 ⟨ s≤s z≤n ⟩ ∷ (n→o 1)  ⟨ ss z< ⟩)
                       (ω^ (n→o 2) · 2 ⟨ s≤s z≤n ⟩ ∷ (n→o 3) ⟨ ss z< ⟩)
                       λ ()
  divtest₂ = (t< refl refl (k< refl (s≤s (s≤s z≤n)))) , refl 

