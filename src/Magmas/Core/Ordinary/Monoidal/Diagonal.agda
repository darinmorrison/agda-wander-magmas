{-# OPTIONS --without-K #-}

module Magmas.Core.Ordinary.Monoidal.Diagonal where

open import Agda.Primitive
open import Magmas.Common
open import Magmas.Core.Ordinary.Magma
open import Prelude.Size

module Δ where
  open Magma
  open Map

  ʲ[_]
    : ∀ ..{s}{n r}..{ℓ₀ ℓ₁}
    → {X : Magma {s} n r ℓ₀}
    → {A : Magma {s} n r ℓ₁}
    → (a : obj A)
    → Map X A
  ap· ʲ[ a ] = T.Δ.ʲ[ a ]
  ap* (ʲ[_] {A = A} a) = ʲ[ ap· (idn◂ A) * ]
