{-# OPTIONS --cubical --safe #-}

module S1Induction where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.HITs.S1.Base using (S¹; base; loop) renaming (ΩS¹ to ℤ)

private
  variable
    ℓ : Level

elim : ∀ {A : S¹ → Type ℓ} {x : A base} → PathP (λ i → A (loop i)) x x → (p : S¹) → A p
elim l base     = l i0
elim l (loop i) = l i

rec : ∀ {A : Type ℓ} {x : A} → x ≡ x → S¹ → A
rec = elim
