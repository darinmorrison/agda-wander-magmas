{-# OPTIONS --without-K #-}

module Magmas.Core.Ordinary.Monoidal.Exponential where

open import Agda.Primitive
open import Magmas.Common
open import Magmas.Core.Ordinary.Magma
open import Magmas.Core.Ordinary.Monoidal.Diagonal
open import Magmas.Core.Ordinary.Monoidal.Tensor.Product
open import Magmas.Core.Ordinary.Monoidal.Tensor.Product.Indexed
open import Magmas.Core.Ordinary.Monoidal.Unit.Terminal
open import Prelude.Size

module ⇒ where
  open Magma
  open Magma.⊗
    using (⟨_,_⟩)
    using (⟨_⊗_⟩)
  open Map

  infix 1 _⇒_

  mutual
    _⇒_
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁}
      → Magma {s} n 0 ℓ₀
      → Magma {s} n 0 ℓ₁
      → Magma {s} n 0 _
    obj  (A ⇒ B) =
      Map A B
    hom  (A ⇒ B) F G =
      Π.[ obj A ∋ x ]
      Π.[ obj A ∋ y ]
      hom A x y ⇒ hom B (ap· F x) (ap· G y)
    idn◂ (A ⇒ B) {a = F} =
      Π.ι[ _ ]↦ Π.ι[ _ ]↦ Δ.ʲ[ ap* F ]
    cmp◂ (A ⇒ B) {b = G} =
      Π.[ T.idn ▸
        Π.[ T.idn ▸
          λ⇑[ cmp◂ B
            ⟔ ⊗.⊢.β ⟔ ⟨ idn ⊗ cmp◂ B ⟩
            ⟔ ⊗.⊢.α⇒ ⟔ ⟨ ⊗.⊢.β ⟔ ap ⊗ ap* G ⟔ inv◂ A ⦃ T.≡.idn ⦄ ⟩
            ⟔ ⊗.⊢.α⇐ ⟔ ap· ⟨«⊗»⟩ (idn , ⊗.δ)
          ] ⟔ ⟨«,»⟩
        ] ⟔ Π.⊢.⊗
      ] ⟔ Π.⊢.⊗
    inv◂ (A ⇒ B) {_}{F}{G} =
      Π.[ T.idn ▸
        Π.[ T.idn ▸
          λ⇑[ inv◂ B ⦃ T.≡.idn ⦄
            ⟔ cmp◂ B
            ⟔ ⊗.⊢.β  ⟔ ⟨ cmp◂ B ⊗ idn ⟩
            ⟔ ⊗.⊢.α⇐ ⟔ ⟨ ap ⊗ ⟨ ap* F , ap* G ⟩ ⟩
            ⟔ ⊗.⊢.α⇐ ⟔ ⟨ idn ⊗ ⟨ idn , inv◂ A ⦃ T.≡.idn ⦄ ⟩ ⟩
          ]
        ]
      ]

    ⟨_⇒_⟩
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {A₀ : Magma {s} n 0 ℓ₀}
      → {A₁ : Magma {s} n 0 ℓ₁}
      → {B₀ : Magma {s} n 0 ℓ₂}
      → {B₁ : Magma {s} n 0 ℓ₃}
      → Map A₁ A₀
      → Map B₀ B₁
      → Map (A₀ ⇒ B₀) (A₁ ⇒ B₁)
    ap· ⟨ F ⇒ G ⟩ K = G ⟔ K ⟔ F
    ap* ⟨ F ⇒ G ⟩ = Π.[ ap· F ▸ Π.[ ap· F ▸ ⟨ ap* F ⇒ ap* G ⟩ ] ]

    apλ
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} n 0 ℓ₀}
      → {B : Magma {s} n 0 ℓ₁}
      → {C : Magma {s} n 0 ℓ₂}
      → Map (A ⊗ B) C
      → obj A T.⇒ Map B C
    ap· (apλ F a) = T.λ⇑ (ap· F) a
    ap* (apλ {A = A} F a) = apλ (ap* F) (ap· (idn◂ A) *)

    λ⇑[_]
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} n 0 ℓ₀}
      → {B : Magma {s} n 0 ℓ₁}
      → {C : Magma {s} n 0 ℓ₂}
      → Map (A ⊗ B) C
      → Map A (B ⇒ C)
    ap· λ⇑[ F ] = apλ F
    ap* λ⇑[ F ] = Π.ι[ _ ]↦ Π.ι[ _ ]↦ idn ⟔ λ⇑[ ap* F ]

    λ⇓[_]
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} n 0 ℓ₀}
      → {B : Magma {s} n 0 ℓ₁}
      → {C : Magma {s} n 0 ℓ₂}
      → Map A (B ⇒ C)
      → Map (A ⊗ B) C
    ap· λ⇓[ F ] = T.λ⇓ (ap· T.⟔ ap· F)
    ap* λ⇓[ F ] = λ⇓[ Π.π ⟔ Π.π ⟔ ap* F ]

    ap
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁}
      → {A : Magma {s} n 0 ℓ₀}
      → {B : Magma {s} n 0 ℓ₁}
      → Map ((A ⇒ B) ⊗ A) B
    ap· ap = T.ap T.⟔ T.⟨ ap· ⊗ T.idn ⟩
    ap* ap = ap ⟔ ⟨ Π.π ⟔ Π.π ⊗ idn ⟩

    ♯
      : ∀ ..{s}{n}..{ℓ}
      → {A : Magma {s} n 0 ℓ}
      → Map A (𝟙 {s} ⇒ A)
    ap· ♯ a = Δ.ʲ[ a ]
    ap* ♯ = Π.ι[ _ ]↦ Π.ι[ _ ]↦ idn ⟔ ♯

    ♭
      : ∀ ..{s}{n}..{ℓ}
      → {A : Magma {s} n 0 ℓ}
      → Map (𝟙 {s} ⇒ A) A
    ap· ♭ F = ap· F *
    ap* ♭ = ♭ ⟔ Π.π ⟔ Π.π

    ⟨«,»⟩
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂}
      → {X : Magma {s} n 0 ℓ₀}
      → {A : Magma {s} n 0 ℓ₁}
      → {B : Magma {s} n 0 ℓ₂}
      → Map ((X ⇒ A) ⊗ (X ⇒ B)) (X ⇒ A ⊗ B)
    ap· ⟨«,»⟩ (F , G) = ⟨ F , G ⟩
    ap* ⟨«,»⟩ = Π.[ T.idn ▸ Π.[ T.idn ▸ ⟨«,»⟩ ] ⟔ Π.⊢.⊗ ] ⟔ Π.⊢.⊗

    «idn»
      : ∀ ..{s}{n}..{ℓ₀}
      → {A : Magma {s} n 0 ℓ₀}
      → Map (𝟙 {s}) (A ⇒ A)
    «idn» = Δ.ʲ[ idn ]

    ⟨«⇒»⟩
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {X : Magma {s} n 0 ℓ₀}
      → {Y : Magma {s} n 0 ℓ₁}
      → {A : Magma {s} n 0 ℓ₂}
      → {B : Magma {s} n 0 ℓ₃}
      → Map ((Y ⇒ X) ⊗ (A ⇒ B)) ((X ⇒ A) ⇒ (Y ⇒ B))
    ap· ⟨«⇒»⟩ (F , G) =
      ⟨ F ⇒ G ⟩
    ap* ⟨«⇒»⟩ =
      Π.ι[ _ ]↦ Π.ι[ _ ]↦
        λ⇑[ Π.ι[ _ ]↦ Π.ι[ _ ]↦
          λ⇓[ ⟨«⇒»⟩ ] ⟔ ⟨ ⟨ Π.π ⟔ Π.π ⊗ Π.π ⟔ Π.π ⟩ ⊗ Π.π ⟔ Π.π ⟩
        ]

    «cmp»
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} n 0 ℓ₀}
      → {B : Magma {s} n 0 ℓ₁}
      → {C : Magma {s} n 0 ℓ₂}
      → Map (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C))
    «cmp» = ⟨«⇒»⟩ ⟔ ⟨ Δ.ʲ[ idn ] , idn ⟩

    «fst»
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} n 0 ℓ₀}
      → {B : Magma {s} n 0 ℓ₁}
      → {R : Magma {s} n 0 ℓ₂}
      → Map (A ⇒ R) (A ⊗ B ⇒ R)
    «fst» = ⟨ ⊗.fst ⇒ idn ⟩

    «snd»
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} n 0 ℓ₀}
      → {B : Magma {s} n 0 ℓ₁}
      → {R : Magma {s} n 0 ℓ₂}
      → Map (B ⇒ R) (A ⊗ B ⇒ R)
    «snd» = ⟨ ⊗.snd ⇒ idn ⟩

    ⟨«⊗»⟩
      : ∀ ..{s}{n}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {X : Magma {s} n 0 ℓ₀}
      → {Y : Magma {s} n 0 ℓ₁}
      → {A : Magma {s} n 0 ℓ₂}
      → {B : Magma {s} n 0 ℓ₃}
      → Map ((X ⇒ A) ⊗ (Y ⇒ B)) (X ⊗ Y ⇒ A ⊗ B)
    ⟨«⊗»⟩ = ⟨«,»⟩ ⟔ ⟨ «fst» ⊗ «snd» ⟩

open ⇒ public
  using (_⇒_)
