{-# OPTIONS --safe --cubical-compatible #-}
module Mahlo.Probe.SuperIR where
-- 对比：对一个「给定」的算子封闭的宇宙（超宇宙式）——严格正
data Nat′ : Set where z : Nat′
module _ (F : Set → Set) where
  mutual
    data U : Set where
      nat : U
      pi  : (a : U) → (T a → U) → U
      cl  : U → U
    T : U → Set
    T nat = Nat′
    T (pi a b) = (x : T a) → T (b x)
    T (cl a) = F (T a)
  