{-# OPTIONS --without-K #-}

module Magmas.Core.Ordinary.Construction.Fundamental where

open import Agda.Primitive
open import Magmas.Common
open import Magmas.Core.Ordinary.Magma
  renaming (module Magma to M)
  hiding (idn◂)
  hiding (cmp◂)
  hiding (inv◂)
open import Magmas.Core.Ordinary.Monoidal.Diagonal
open import Prelude.Path
  renaming (module ≡ to ↝)
  renaming (_≡_ to _↝_)
  using ()
open import Prelude.Size

module ℼ where
  open Map

  mutual
    ℼ[_] : ∀ ..{s}{n r}..{ℓ} → Set ℓ → Magma {s} n r ℓ
    M.obj  ℼ[ A ] = A
    M.hom  ℼ[ A ] x y = ℼ[ x ↝ y ]
    M.idn◂ ℼ[ A ] = idn◂ A
    M.cmp◂ ℼ[ A ] = cmp◂ A
    M.inv◂ ℼ[ A ] = inv◂ A

    ap¹
      : ∀ ..{s}{n r}..{ℓ} {A B : Set ℓ}
      → (f : A T.⇒ B)
      → {a₀ a₁ : A}
      → Map {s}{n}{r} ℼ[ a₀ ↝ a₁ ] ℼ[ f a₀ ↝ f a₁ ]
    ap· (ap¹ f) = ↝.ap¹ f
    ap* (ap¹ f) = ap¹ (↝.ap¹ f)

    ap²
      : ∀ ..{s}{n r}..{ℓ} {A B C : Set ℓ}
      → (f : (A T.⊗ B) T.⇒ C)
      → {a₀ a₁ : A} {b₀ b₁ : B}
      → Map {s}{n}{r} (ℼ[ a₀ ↝ a₁ ] ⊗ ℼ[ b₀ ↝ b₁ ]) ℼ[ f (a₀ , b₀) ↝ f (a₁ , b₁) ]
    ap· (ap² f) = ↝.ap² f
    ap* (ap² f) = ap² (↝.ap² f)

    idn◂
      : ∀ ..{s}{n r}..{ℓ} (A : Set ℓ) ..{s′ : Size.< s}
      → {a : A}
      → Map {s′}{n}{r} M.𝟙 ℼ[ a ↝ a ]
    idn◂ A = Δ.ʲ[ ↝.idn ]

    cmp◂
      : ∀ ..{s}{n r}..{ℓ} (A : Set ℓ) ..{s′ : Size.< s}
      → {a b c : A}
      → Map {s′}{n}{r} (ℼ[ b ↝ c ] ⊗ ℼ[ a ↝ b ]) ℼ[ a ↝ c ]
    ap· (cmp◂ A) = ↝.cmp
    ap* (cmp◂ A) = ap² ↝.cmp

    inv◂
      : ∀ ..{s}{n r}..{ℓ} (A : Set ℓ) ..{s′ : Size.< s}
      → {a b : A}
      → Map {s′}{n}{r} ℼ[ a ↝ b ] ℼ[ b ↝ a ]
    ap· (inv◂ A) = ↝.inv
    ap* (inv◂ A) = ap¹ ↝.inv

open ℼ public
  using (ℼ[_])
