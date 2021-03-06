{-# OPTIONS --without-K #-}

module Magmas.Core.Ordinary.Magma where

open import Agda.Primitive
open import Magmas.Common
open import Prelude.Size

private
  module Boot where
    infixl 1 _⟔_
    infix  2 _⊗_

    mutual
      record Magma ..{s} (n r : Nat∞) ..ℓ : Set (lsuc ℓ) where
        no-eta-equality
        coinductive
        field
          obj
            : Set ℓ
          hom
            : ..{s′ : Size.< s}
            → (x : obj)
            → (y : obj)
            → Magma {s′} (pred n) (pred r) ℓ
        field
          idn◂
            : ..{s′ : Size.< s}
            → ∀ {a : obj}
            → Map 𝟙↑[ lzero ] (hom a a)
          cmp◂
            : ..{s′ : Size.< s}
            → ∀ {a b c}
            → Map (hom b c ⊗ hom a b) (hom a c)
          inv◂
            : ..{s′ : Size.< s}
            → ∀ {a b}
            → ⦃ ρ≜ : r T.≡ 0 ⦄
            → Map (hom a b) (hom b a)

      obj∞ = Magma.obj
      hom∞ = Magma.hom
      idn∞ = Magma.idn◂
      cmp∞ = Magma.cmp◂
      inv∞ = Magma.inv◂

      record Map ..{s}{n r}..{ℓ₀ ℓ₁}
        (A : Magma {s} n r ℓ₀)
        (B : Magma {s} n r ℓ₁)
        : Set (lsuc (ℓ₀ ⊔ ℓ₁))
        where
        no-eta-equality
        coinductive
        open Magma
        field
          ap·
            : obj A → obj B
          ap*
            : ∀ ..{s′ : Size.< s} {x y}
            → Map (hom A x y) (hom B (ap· x) (ap· y))

      ap·∞ = Map.ap·
      ap*∞ = Map.ap*

      idn
        : ∀ ..{s}{n r}..{ℓ}
        → {A : Magma {s} n r ℓ}
        → Map A A
      Map.ap· idn = T.idn
      Map.ap* idn =   idn

      _⟔_
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁ ℓ₂}
        → {A : Magma {s} n r ℓ₀}
        → {B : Magma {s} n r ℓ₁}
        → {C : Magma {s} n r ℓ₂}
        → Map B C
        → Map A B
        → Map A C
      Map.ap· (G ⟔ F) = Map.ap· G T.⟔ Map.ap· F
      Map.ap* (G ⟔ F) = Map.ap* G   ⟔ Map.ap* F

      𝟙↑[_]
        : ∀ ..{s}{n r}..ℓ
        → Magma {s} n r ℓ
      Magma.obj  𝟙↑[ ℓ ] = T.𝟙↑
      Magma.hom  𝟙↑[ ℓ ] _ _ = 𝟙↑[ ℓ ]
      Magma.idn◂ 𝟙↑[ ℓ ] = !↑
      Magma.cmp◂ 𝟙↑[ ℓ ] = !↑
      Magma.inv◂ 𝟙↑[ ℓ ] = !↑

      !↑
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁}
        → {A : Magma {s} n r ℓ₀}
        → Map A 𝟙↑[ ℓ₁ ]
      Map.ap· !↑ = T.!
      Map.ap* !↑ = !↑

      _⊗_
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁}
        → Magma {s} n r ℓ₀
        → Magma {s} n r ℓ₁
        → Magma {s} n r _
      Magma.obj  (A ⊗ B) =
        obj∞ A T.⊗ obj∞ B
      Magma.hom  (A ⊗ B) (a₀ , b₀) (a₁ , b₁) =
        hom∞ A a₀ a₁ ⊗ hom∞ B b₀ b₁
      Magma.idn◂ (A ⊗ B) =
        ⟨ idn∞ A , idn∞ B ⟩
      Magma.cmp◂ (A ⊗ B) =
        ⟨ cmp∞ A ⊗ cmp∞ B ⟩ ⟔ xchg
      Magma.inv◂ (A ⊗ B) =
        ⟨ inv∞ A ⊗ inv∞ B ⟩

      ⟨_,_⟩
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁ ℓ₂}
        → {X : Magma {s} n r ℓ₀}
        → {A : Magma {s} n r ℓ₁}
        → {B : Magma {s} n r ℓ₂}
        → Map X A
        → Map X B
        → Map X (A ⊗ B)
      Map.ap· ⟨ F , G ⟩ = T.⟨ ap·∞ F , ap·∞ G ⟩
      Map.ap* ⟨ F , G ⟩ =   ⟨ ap*∞ F , ap*∞ G ⟩

      fst
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁}
        → {A : Magma {s} n r ℓ₀}
        → {B : Magma {s} n r ℓ₁}
        → Map (A ⊗ B) A
      Map.ap· fst = T.fst
      Map.ap* fst =   fst

      snd
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁}
        → {A : Magma {s} n r ℓ₀}
        → {B : Magma {s} n r ℓ₁}
        → Map (A ⊗ B) B
      Map.ap· snd = T.snd
      Map.ap* snd =   snd

      ⟨_⊗_⟩
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
        → {X : Magma {s} n r ℓ₀}
        → {Y : Magma {s} n r ℓ₁}
        → {A : Magma {s} n r ℓ₂}
        → {B : Magma {s} n r ℓ₃}
        → Map X A
        → Map Y B
        → Map (X ⊗ Y) (A ⊗ B)
      ⟨ F ⊗ G ⟩ = ⟨ F ⟔ fst , G ⟔ snd ⟩

      xchg
        : ∀ ..{s}{n r}..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
        → {A : Magma {s} n r ℓ₀}
        → {B : Magma {s} n r ℓ₁}
        → {C : Magma {s} n r ℓ₂}
        → {D : Magma {s} n r ℓ₃}
        → Map ((A ⊗ B) ⊗ (C ⊗ D)) ((A ⊗ C) ⊗ (B ⊗ D))
      xchg = ⟨ ⟨ fst ⊗ fst ⟩ , ⟨ snd ⊗ snd ⟩ ⟩

module Magma where
  open Boot.Magma public

  module Map where
    open Boot
    open Boot.Map public
    open Boot public
      using (idn)
      using (_⟔_)

    _⟓_
      : ∀ ..{s}{n r}..{ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} n r ℓ₀}
      → {B : Magma {s} n r ℓ₁}
      → {C : Magma {s} n r ℓ₂}
      → Map A B
      → Map B C
      → Map A C
    F ⟓ G = G ⟔ F

    cmp : _
    cmp = _⟔_

    seq : _
    seq = _⟓_

  module 𝟙↑ where
    open Boot public
      using (!↑)

  module 𝟙 where
    open Boot

    𝟙 : ∀ ..{s}{n r} → Magma {s} n r lzero
    𝟙 = 𝟙↑[ _ ]

    ! : ∀ ..{s}{n r}..{ℓ} {A : Magma {s} n r ℓ} → Map A (𝟙 {s})
    ! = !↑

  open 𝟙 public
    using (𝟙)

  module ⊗ where
    open Boot public
      using (fst)
      using (snd)
      using (⟨_,_⟩)
      using (⟨_⊗_⟩)
      using (xchg)

  open Boot public
    hiding (module Map)
    using (Magma)
    using (Map)
    using (𝟙↑[_])
    using (_⊗_)

open Boot public
  hiding (module Magma)
  using (Magma)

open Magma public
  using (idn◂)
  using (cmp◂)
  using (inv◂)
  using (Map)
  using (_⊗_)
  using (obj)
  using (hom)
