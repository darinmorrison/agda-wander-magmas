{-# OPTIONS --without-K #-}

module Magmas.Common where

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

open T.𝟙↑ public
  using (*)

open T.⊗ public
  using (_,_)
