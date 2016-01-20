{-# OPTIONS --without-K #-}

module Magma where

open import Agda.Primitive
open import Prelude.Conatural
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Size

open Nat∞
  using (∞)
  using ([∞])
  using (pred)

private
  module T where
    open import Prelude.Monoidal public
    open 𝟙↑ public
      using (!)
    open ⊗ public
      using (⟨_,_⟩)
      using (⟨_⊗_⟩)
      using (fst)
      using (snd)
    open ⇒ public
      using (λ⇑)
      using (λ⇓)
      using (_⟔_)
      using (_⟓_)
      using (idn)
      using (ap)
open T.𝟙↑
  using (*)
open T.⊗
  using (_,_)

infixl 1 _⟔_
infix  2 _⊗_

mutual
  record Magma ..{s}..ℓ : Set (lsuc ℓ) where
    no-eta-equality
    coinductive
    field
      obj
        : Set ℓ
      hom
        : ..{s′ : Size.< s}
        → (x : obj)
        → (y : obj)
        → Magma {s′} ℓ
    field
      idn◂
        : ..{s′ : Size.< s}
        → ∀ {a : obj}
        → Map 𝟙 (hom a a)
      cmp◂
        : ..{s′ : Size.< s}
        → ∀ {a b c}
        → Map (hom b c ⊗ hom a b) (hom a c)
      inv◂
        : ..{s′ : Size.< s}
        → ∀ {a b}
        → Map (hom a b) (hom b a)

  obj∞ = Magma.obj
  hom∞ = Magma.hom
  idn∞ = Magma.idn◂
  cmp∞ = Magma.cmp◂
  inv∞ = Magma.inv◂

  record Map ..{s ℓ₀ ℓ₁}
    (A : Magma {s} ℓ₀)
    (B : Magma {s} ℓ₁)
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
    : ∀ ..{s ℓ}
    → {A : Magma {s} ℓ}
    → Map A A
  Map.ap· idn = T.idn
  Map.ap* idn =   idn

  _⟔_
    : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
    → {A : Magma {s} ℓ₀}
    → {B : Magma {s} ℓ₁}
    → {C : Magma {s} ℓ₂}
    → Map {ℓ₀ = ℓ₁}{ℓ₂} B C
    → Map {ℓ₀ = ℓ₀}{ℓ₁} A B
    → Map {ℓ₀ = ℓ₀}{ℓ₂} A C
  Map.ap· (G ⟔ F) = Map.ap· G T.⟔ Map.ap· F
  Map.ap* (G ⟔ F) = Map.ap* G   ⟔ Map.ap* F

  𝟙↑[_]
    : ∀ ..{s}..ℓ
    → Magma {s} ℓ
  Magma.obj  𝟙↑[ ℓ ] = T.𝟙↑
  Magma.hom  𝟙↑[ ℓ ] _ _ = 𝟙↑[ ℓ ]
  Magma.idn◂ 𝟙↑[ ℓ ] = !↑
  Magma.cmp◂ 𝟙↑[ ℓ ] = !↑
  Magma.inv◂ 𝟙↑[ ℓ ] = !↑

  !↑
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Magma {s} ℓ₀}
    → Map {ℓ₀ = ℓ₀}{ℓ₁ = ℓ₁} A 𝟙↑[ ℓ₁ ]
  Map.ap· !↑ = T.!
  Map.ap* !↑ = !↑

  𝟙 : ∀ ..{s}
    → Magma {s} lzero
  𝟙 = 𝟙↑[ lzero ]

  _⊗_
    : ∀ ..{s ℓ₀ ℓ₁}
    → Magma {s} (ℓ₀)
    → Magma {s} (ℓ₁)
    → Magma {s} (ℓ₀ ⊔ ℓ₁)
  Magma.obj  (A ⊗ B) =
    obj∞ A T.⊗ obj∞ B
  Magma.hom  (A ⊗ B) (a₀ , b₀) (a₁ , b₁) =
    hom∞ A a₀ a₁ ⊗ hom∞ B b₀ b₁
  Magma.idn◂ (A ⊗ B) =
    ⟨ idn∞ A , idn∞ B ⟩
  Magma.cmp◂ (A ⊗ B) =
    ⟨ cmp∞ A ⊗ cmp∞ B ⟩ ⟔ int
  Magma.inv◂ (A ⊗ B) =
    ⟨ inv∞ A ⊗ inv∞ B ⟩

  ⟨_,_⟩
    : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
    → {X : Magma {s} ℓ₀}
    → {A : Magma {s} ℓ₁}
    → {B : Magma {s} ℓ₂}
    → Map {ℓ₀ = ℓ₀}{ℓ₁ = ℓ₁} X A
    → Map {ℓ₀ = ℓ₀}{ℓ₁ = ℓ₂} X B
    → Map {ℓ₀ = ℓ₀}{ℓ₁ = ℓ₁ ⊔ ℓ₂} X (A ⊗ B)
  Map.ap· ⟨ F , G ⟩ = T.⟨ ap·∞ F , ap·∞ G ⟩
  Map.ap* ⟨ F , G ⟩ =   ⟨ ap*∞ F , ap*∞ G ⟩

  fst
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Magma {s} ℓ₀}
    → {B : Magma {s} ℓ₁}
    → Map (A ⊗ B) A
  Map.ap· fst = T.fst
  Map.ap* fst =   fst

  snd
    : ∀ ..{s ℓ₀ ℓ₁}
    → {A : Magma {s} ℓ₀}
    → {B : Magma {s} ℓ₁}
    → Map (A ⊗ B) B
  Map.ap· snd = T.snd
  Map.ap* snd =   snd

  ⟨_⊗_⟩
    : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {X : Magma {s} ℓ₀}
    → {Y : Magma {s} ℓ₁}
    → {A : Magma {s} ℓ₂}
    → {B : Magma {s} ℓ₃}
    → Map X A
    → Map Y B
    → Map (X ⊗ Y) (A ⊗ B)
  ⟨ F ⊗ G ⟩ = ⟨ F ⟔ fst , G ⟔ snd ⟩

  int
    : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
    → {A : Magma {s} ℓ₀}
    → {B : Magma {s} ℓ₁}
    → {C : Magma {s} ℓ₂}
    → {D : Magma {s} ℓ₃}
    → Map ((A ⊗ B) ⊗ (C ⊗ D)) ((A ⊗ C) ⊗ (B ⊗ D))
  int = ⟨ ⟨ fst ⊗ fst ⟩ , ⟨ snd ⊗ snd ⟩ ⟩

module Δ where
  open Magma
  open Map

  ʲ[_]
    : ∀ ..{s ℓ₀ ℓ₁}
    → {X : Magma {s} ℓ₀}
    → {A : Magma {s} ℓ₁}
    → (a : obj A)
    → Map X A
  ap· ʲ[ a ] = T.Δ.ʲ[ a ]
  ap* (ʲ[_] {A = A} a) = ʲ[ ap· (idn◂ A) * ]

module ⊗ where
  open Magma
  open Map

  δ
    : ∀ ..{s ℓ}
    → {A : Magma {s} ℓ}
    → Map A (A ⊗ A)
  δ = ⟨ idn , idn ⟩

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

module Π where
  open Magma
  open Map

  infix 0 Π
  infix 0 ι
  infix 0 π
  infix 0 [Π]

  mutual
    Π
      : ∀ ..{s ℓ₀ ℓ₁}
      → (I : Set ℓ₀) (A : I → Magma {s} ℓ₁)
      → Magma {s} (ℓ₀ ⊔ ℓ₁)
    obj  (Π I A) = ∀ i → obj (A i)
    hom  (Π I A) φ ψ = Π I λ i → hom (A i) (φ i) (ψ i)
    idn◂ (Π I A) = ι▸[ i ] idn◂ (A i)
    cmp◂ (Π I A) = ι▸[ i ] cmp◂ (A i) ⟔ ⟨ π[ i ] ⊗ π[ i ] ⟩
    inv◂ (Π I A) = ι▸[ i ] inv◂ (A i) ⟔ π[ i ]

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

    [Π]
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {I : Set ℓ₀}
      → {J : Set ℓ₁}
      → {A : I → Magma {s} ℓ₂}
      → {B : J → Magma {s} ℓ₃}
      → (f : J → I)
      → (∀ j → Map (A (f j)) (B j))
      → Map (Π I A) (Π J B)
    ap· ([Π] f F) ψ j = ap· (F j) (ψ (f j))
    ap* ([Π] f F) = [Π] f (λ j → ap* (F j))

    syntax Π I (λ i → A) = Π[ I ∋ i ] A
    syntax ι (λ i → K) = ι▸[ i ] K
    syntax π {i = i} = π[ i ]
    syntax [Π] f (λ i → F) = Π[ f ▸[ i ] F ]

    Π[_▸_]
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {I : Set ℓ₀}
      → {J : Set ℓ₁}
      → {A : I → Magma {s} ℓ₂}
      → {B : J → Magma {s} ℓ₃}
      → (f : J → I)
      → (∀ {j} → Map (A (f j)) (B j))
      → Map (Π I A) (Π J B)
    Π[ f ▸ F ] = Π[ f ▸[ x ] F {x} ]

    ⊢⊗
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {I : Set ℓ₀}
      → {A : I → Magma {s} ℓ₁}
      → {B : I → Magma {s} ℓ₂}
      → Map (Π I A ⊗ Π I B) (Π[ I ∋ i ] A i ⊗ B i)
    ⊢⊗ = ι▸[ i ] ⟨ π[ i ] ⊗ π[ i ] ⟩

open Π public
  using (Π)

module ⇒ where
  open Magma
  open Map
  open ⊗
  open Π

  infix 1 _⇒_

  mutual
    _⇒_
      : ∀ ..{s ℓ₀ ℓ₁}
      → Magma {s} ℓ₀
      → Magma {s} ℓ₁
      → Magma {s} _
    obj  (A ⇒ B) =
      Map A B
    hom  (A ⇒ B) F G =
      Π[ obj A ∋ x ]
      Π[ obj A ∋ y ]
      hom A x y ⇒ hom B (ap· F x) (ap· G y)
    idn◂ (A ⇒ B) {a = F} =
      ι▸[ _ ] ι▸[ _ ] Δ.ʲ[ ap* F ]
    cmp◂ (A ⇒ B) {b = G} =
      Π[ T.idn ▸
        Π[ T.idn ▸
          λ⇑[ cmp◂ B
            ⟔ β  ⟔ ⟨ idn ⊗ cmp◂ B ⟩
            ⟔ α⇒ ⟔ ⟨ β ⟔ ap ⊗ ap* G ⟔ inv◂ A ⟩
            ⟔ α⇐ ⟔ ap· ⟨«⊗»⟩ (idn , δ)
            ] ⟔ ⟨«,»⟩
         ] ⟔ Π.⊢⊗
       ] ⟔ Π.⊢⊗
    inv◂ (A ⇒ B) {_}{F}{G} =
      Π[ T.idn ▸
        Π[ T.idn ▸
          λ⇑[ inv◂ B
            ⟔ cmp◂ B
            ⟔ β  ⟔ ⟨ cmp◂ B ⊗ idn ⟩
            ⟔ α⇐ ⟔ ⟨ ap ⊗ ⟨ ap* F , ap* G ⟩ ⟩
            ⟔ α⇐ ⟔ ⟨ idn ⊗ ⟨ idn , inv◂ A ⟩ ⟩
            ]
          ]
        ]

    ⟨_⇒_⟩
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {A₀ : Magma {s} ℓ₀}
      → {A₁ : Magma {s} ℓ₁}
      → {B₀ : Magma {s} ℓ₂}
      → {B₁ : Magma {s} ℓ₃}
      → Map A₁ A₀
      → Map B₀ B₁
      → Map (A₀ ⇒ B₀) (A₁ ⇒ B₁)
    ap· ⟨ F ⇒ G ⟩ K = G ⟔ K ⟔ F
    ap* ⟨ F ⇒ G ⟩ = Π[ ap· F ▸ Π[ ap· F ▸ ⟨ ap* F ⇒ ap* G ⟩ ] ]

    apλ
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {C : Magma {s} ℓ₂}
      → Map (A ⊗ B) C
      → (a : obj A)
      → Map B C
    ap· (apλ F a) = T.λ⇑ (ap· F) a
    ap* (apλ {A = A} F a) = apλ (ap* F) (ap· (idn◂ A) *)

    λ⇑[_]
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {C : Magma {s} ℓ₂}
      → Map (A ⊗ B) C
      → Map A (B ⇒ C)
    ap· λ⇑[ F ] = apλ F
    ap* λ⇑[ F ] = ι▸[ _ ] ι▸[ _ ] idn ⟔ λ⇑[ ap* F ]

    λ⇓[_]
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {C : Magma {s} ℓ₂}
      → Map A (B ⇒ C)
      → Map (A ⊗ B) C
    ap· λ⇓[ F ] = T.λ⇓ (ap· T.⟔ ap· F)
    ap* λ⇓[ F ] = λ⇓[ π[ _ ] ⟔ π[ _ ] ⟔ ap* F ]

    ap
      : ∀ ..{s ℓ₀ ℓ₁}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → Map ((A ⇒ B) ⊗ A) B
    ap· ap = T.ap T.⟔ T.⟨ ap· ⊗ T.idn ⟩
    ap* ap = ap ⟔ ⟨ π[ _ ] ⟔ π[ _ ] ⊗ idn ⟩

    ⟨«,»⟩
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {X : Magma {s} ℓ₀}
      → {A : Magma {s} ℓ₁}
      → {B : Magma {s} ℓ₂}
      → Map ((X ⇒ A) ⊗ (X ⇒ B)) (X ⇒ A ⊗ B)
    ap· ⟨«,»⟩ (F , G) = ⟨ F , G ⟩
    ap* ⟨«,»⟩ = Π[ T.idn ▸ Π[ T.idn ▸ ⟨«,»⟩ ] ⟔ Π.⊢⊗ ] ⟔ Π.⊢⊗

    «♯»
      : ∀ ..{s ℓ}
      → {A : Magma {s} ℓ}
      → Map A (𝟙 {s} ⇒ A)
    ap· «♯» a = Δ.ʲ[ a ]
    ap* «♯» = ι▸[ _ ] ι▸[ _ ] idn ⟔ «♯»

    «♭»
      : ∀ ..{s ℓ}
      → {A : Magma {s} ℓ}
      → Map (𝟙 {s} ⇒ A) A
    ap· «♭» F = ap· F *
    ap* «♭» = «♭» ⟔ π ⟔ π

    «idn»
      : ∀ ..{s ℓ₀}
      → {A : Magma {s} ℓ₀}
      → Map (𝟙 {s}) (A ⇒ A)
    «idn» = Δ.ʲ[ idn ]

    «cmp»
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {C : Magma {s} ℓ₂}
      → Map (B ⇒ C) ((A ⇒ B) ⇒ (A ⇒ C))
    ap· «cmp» G =
      ⟨ idn ⇒ G ⟩
    ap* «cmp» =
      ι▸[ _ ] ι▸[ _ ] λ⇑[ ι▸[ _ ] ι▸[ _ ] λ⇓[ «cmp» ] ⟔ ⟨ π ⟔ π ⊗ π ⟔ π ⟩ ]

    «fst»
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {R : Magma {s} ℓ₂}
      → Map (A ⇒ R) (A ⊗ B ⇒ R)
    «fst» = ⟨ fst ⇒ idn ⟩

    «snd»
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂}
      → {A : Magma {s} ℓ₀}
      → {B : Magma {s} ℓ₁}
      → {R : Magma {s} ℓ₂}
      → Map (B ⇒ R) (A ⊗ B ⇒ R)
    «snd» = ⟨ snd ⇒ idn ⟩

    ⟨«⊗»⟩
      : ∀ ..{s ℓ₀ ℓ₁ ℓ₂ ℓ₃}
      → {X : Magma {s} ℓ₀}
      → {Y : Magma {s} ℓ₁}
      → {A : Magma {s} ℓ₂}
      → {B : Magma {s} ℓ₃}
      → Map ((X ⇒ A) ⊗ (Y ⇒ B)) (X ⊗ Y ⇒ A ⊗ B)
    ⟨«⊗»⟩ = ⟨«,»⟩ ⟔ ⟨ «fst» ⊗ «snd» ⟩

open ⇒ public
  using (_⇒_)
