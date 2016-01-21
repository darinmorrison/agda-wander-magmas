{-# OPTIONS --without-K #-}

open import Agda.Primitive
open import Magmas.Common
open import Magmas.Core.Ordinary.Magma
open import Prelude.Size

module Magmas.Core.Ordinary.Monoidal.Tensor.Product.Indexed where

module Π where
  open Magma
  open Map

  infix 0 Π
  infix 0 ι
  infix 0 π

  mutual
    Π
      : ∀ ..{s ℓ₀ ℓ₁}
      → (I : Set ℓ₀) (A : I → Magma {s} ℓ₁)
      → Magma {s} _
    obj  (Π I A) = ∀ i → obj (A i)
    hom  (Π I A) φ ψ = Π I λ i → hom (A i) (φ i) (ψ i)
    idn◂ (Π I A) = ι[ i ]↦ idn◂ (A i)
    cmp◂ (Π I A) = ι[ i ]↦ cmp◂ (A i) ⟔ ⊗.⟨ π[ i ] ⊗ π[ i ] ⟩
    inv◂ (Π I A) = ι[ i ]↦ inv◂ (A i) ⟔ π[ i ]

    ι : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {X : Magma {s} ℓ₀}
      → {I : Set ℓ₁}
      → {A : I → Magma {s} ℓ₂}
      → (∀ i → Map X (A i))
      → Map X (Π I A)
    ap· (ι Ψ) x i = ap· (Ψ i) x
    ap* (ι Ψ) = ι λ i → ap* (Ψ i)

    π : ∀ ..{s ℓ₀ ℓ₁}
      → {I : Set ℓ₀}
      → {A : I → Magma {s} ℓ₁}
      → {i : I}
      → Map (Π I A) (A i)
    ap· π ψ = ψ _
    ap* π = π

  map
    : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {I : Set ℓ₀}
    → {J : Set ℓ₁}
    → {A : I → Magma {s} ℓ₂}
    → {B : J → Magma {s} ℓ₃}
    → (f : J → I)
    → (∀ j → Map (A (f j)) (B j))
    → Map (Π I A) (Π J B)
  ap· (map f F) ψ j = ap· (F j) (ψ (f j))
  ap* (map f F) = map f (λ j → ap* (F j))

  [_▸_]
    : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {I : Set ℓ₀}
    → {J : Set ℓ₁}
    → {A : I → Magma {s} ℓ₂}
    → {B : J → Magma {s} ℓ₃}
    → (f : J → I)
    → (∀ {j} → Map (A (f j)) (B j))
    → Map (Π I A) (Π J B)
  [ f ▸ F ] = [ f ▸[ x ]↦ F {x} ]

  module ⊢ where
    ⊗
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {I : Set ℓ₀}
      → {A : I → Magma {s} ℓ₁}
      → {B : I → Magma {s} ℓ₂}
      → Map (Π I A ⊗ Π I B) ([ I ∋ i ] A i ⊗ B i)
    ⊗ = ι[ i ]↦ ⊗.⟨ π[ i ] ⊗ π[ i ] ⟩

  syntax Π I (λ i → A) = [ I ∋ i ] A
  syntax ι (λ i → K) = ι[ i ]↦ K
  syntax π {i = i} = π[ i ]
  syntax map f (λ i → F) = [ f ▸[ i ]↦ F ]

open Π public
  using (Π)
