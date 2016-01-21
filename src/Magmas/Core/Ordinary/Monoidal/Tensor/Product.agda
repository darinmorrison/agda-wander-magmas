{-# OPTIONS --without-K #-}

module Magmas.Core.Ordinary.Monoidal.Tensor.Product where

open import Agda.Primitive
open import Magmas.Common
import Magmas.Core.Ordinary.Magma
open import Prelude.Size

module ⊗ where
  open Magmas.Core.Ordinary.Magma
  open Map
  open Magma public
    using (_⊗_)
  open Magma.⊗ public

  δ
    : ∀ ..{s ℓ}
    → {A : Magma {s} ℓ}
    → Map A (A ⊗ A)
  δ = ⟨ idn , idn ⟩

  module ⊢ where
    α⇒
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {C : Magma {s} ℓ₂}
      → Map ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
    ap· α⇒ = T.⊗.α⇒
    ap* α⇒ = α⇒

    α⇐
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {C : Magma {s} ℓ₂}
      → Map (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
    ap· α⇐ = T.⊗.α⇐
    ap* α⇐ = α⇐

    β
      : ∀ ..{s ℓ₀ ℓ₁}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → Map (A ⊗ B) (B ⊗ A)
    ap· β = T.⊗.β
    ap* β = β

open ⊗ public
  using (_⊗_)
