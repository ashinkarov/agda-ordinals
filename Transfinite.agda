
open import Data.Nat
open import Data.Vec
open import Data.Fin using (Fin; suc; zero; fromℕ≤; fromℕ<)
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import Function

fromℕ<-irr : ∀ {m n} → .(m Data.Nat.< n) → Fin n
fromℕ<-irr {zero}  {suc n} m≤n = zero
fromℕ<-irr {suc m} {suc n} m≤n = suc (fromℕ<-irr (Data.Nat.≤-pred m≤n))





open import Ord

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

ω^k<ω⇒k≡0 : ∀ {k m}.{m>0}{o}.{pf} → ω^ k · m ⟨ m>0 ⟩ ∷ o ⟨ pf ⟩ <ₒ ωₒ → k ≡ 0ₒ
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


