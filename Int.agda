{-# OPTIONS --cubical --safe #-}

module Int where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.HITs.S1.Base using (S¹; base; loop) renaming (ΩS¹ to ℤ)

import S1Induction as S¹

infixl 6 _+_
infix 7 -_

_+_ : ℤ → ℤ → ℤ
_+_ = _∙_

-_ : ℤ → ℤ
-_ = _⁻¹

0ℤ 1ℤ -1ℤ : ℤ
0ℤ = refl
1ℤ = loop
-1ℤ = - 1ℤ

sucℤ predℤ : ℤ → ℤ
sucℤ n = 1ℤ + n
predℤ n = -1ℤ + n

pos neg : ℕ → ℤ
pos zero = 0ℤ
pos (suc n) = sucℤ (pos n)
neg zero = 0ℤ
neg (suc n) = predℤ (neg n)

private
  variable
    a : Level
    A : Type a

-- recursion principle of ℤ
rec : ∀ (x : A) (p : A ≡ A) → ℤ → A
rec x p n = subst (S¹.rec p) n x

∙-path : ∀ {x : A} (p : x ≡ x) → (x ≡ x) ≡ (x ≡ x)
∙-path {x = x} p = isoToPath lemma
  where
    open Iso
    lemma : Iso (x ≡ x) (x ≡ x)
    lemma .fun q = p ∙ q
    lemma .inv q = p ⁻¹ ∙ q
    lemma .rightInv q = assoc p (p ⁻¹) q ∙ cong (_∙ q) (rCancel p) ∙ lUnit q ⁻¹
    lemma .leftInv  q = assoc (p ⁻¹) p q ∙ cong (_∙ q) (lCancel p) ∙ lUnit q ⁻¹

+-path : ℤ → ℤ ≡ ℤ
+-path n = ∙-path n

_*_ : ℤ → ℤ → ℤ
m * n = rec 0ℤ (+-path n) m

+-assoc : ∀ l m n → l + (m + n) ≡ (l + m) + n
+-assoc l m n = assoc l m n

private
  import Cubical.Data.Int.Base as Int
  import Cubical.Data.Int.Properties as Int
  
  fromℤ : ℤ → Int.ℤ
  fromℤ n = rec (Int.pos 0) Int.sucPathℤ n
  
  _ : fromℤ (pos 3 * pos 5) ≡ Int.pos 15
  _ = refl
  
  _ : fromℤ (pos 3 * neg 5) ≡ Int.negsuc 14
  _ = refl
  
  _ : fromℤ (neg 3 * pos 5) ≡ Int.negsuc 14
  _ = refl
  
  _ : fromℤ (neg 3 * neg 5) ≡ Int.pos 15
  _ = refl
