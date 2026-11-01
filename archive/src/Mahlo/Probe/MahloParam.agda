{-# OPTIONS --safe --cubical-compatible #-}
module Mahlo.Probe.MahloParam where
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat renaming (Nat to ℕ)

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

-- V := Set，T := id。Setzer 的 Û_{f,g} 变成对给定算子 (f,g) 参数化的 IR 子宇宙。
-- Res0_= : s(Res0(r,s)) = f(s r, λx. s(s x))      Res1_= : s(Res1(r,s,t)) = g(s r, λx. s(s x), t)
module Sub
  (f : (u : Set) → (u → Set) → Set)
  (g : (u : Set) (v : u → Set) → f u v → Set)
  where
  mutual
    data U : Set where
      n̂    : U
      π̂    : (a : U) → (T a → U) → U
      ŵ    : (a : U) → (T a → U) → U
      res0 : (a : U) → (b : T a → U) → U
      res1 : (a : U) → (b : T a → U) → f (T a) (λ x → T (b x)) → U
    T : U → Set                          -- 这就是 s_{f,g}
    T n̂          = ℕ
    T (π̂ a b)    = (x : T a) → T (b x)
    T (ŵ a b)    = W (T a) (λ x → T (b x))
    T (res0 a b)   = f (T a) (λ x → T (b x))
    T (res1 a b c) = g (T a) (λ x → T (b x)) c

-- 用法示例：Lemma 5.10 那种 f := 常量 N̂_V、g := 依赖 (u₀,v₀) 的谓词 —— 这里用任意给定的 E 演示
module Example (E : (u : Set) → (u → Set) → ℕ → Set) where
  open Sub (λ u v → ℕ) (λ u v n → E u v n) public
