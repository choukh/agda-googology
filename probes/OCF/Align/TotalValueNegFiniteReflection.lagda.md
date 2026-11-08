# 值序反射到前驱嵌入：有限源的完整正面边界

本文件虽沿用配对检查的 Neg 前缀，结论是正面的。源为任意自然数，
目标为任意 Free 层树；目标可以有退化极限，不要求严格性。
这不是一般 SV 源的反射定理，也不把值比较送入任意反馈函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegFiniteReflection where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Free.Level
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueBuildIf
open import OCF.Align.TotalValueEmbeddingOps using (identity; widen; successor)
import OCF.Free.TotalOrbitBuild as A

num : ℕ → Ordᴵ
num zero = zero
num (suc n) = suc (num n)

-- 从给定后继值证明抽出真实目标前驱，不进行裸层号比较。
predecessor : ∀ {a : Ordᶜ zero} (b : Ordᴵ) → suc a ≼ A.read b →
  Σ Ordᴵ (λ c → c ≺ᴵ b × a ≼ A.read c)
predecessor zero ()
predecessor (suc b) (s≼s p) = b , via (≅ᴵ-refl b) zero , p
predecessor (lim f st) (≼l n p) with predecessor (f n) p
... | c , via e q , v = c , via e (lim n q) , v

finite-reflection : ∀ n {b} → A.read (num n) ≼ A.read b →
  BoundedEmbedding (num n) b
finite-reflection zero p = widen (identity zero) z⊑
finite-reflection (suc n) {b} p with predecessor b p
... | c , via e q , v = widen (successor (finite-reflection n v)) (s⊑ e q)

-- 任意稀疏或重复的目标限列只要实际含给定有限值，就可消费该证明。
constant-target : ∀ n → BoundedEmbedding (num n)
  (lim (λ _ → num n) (λ _ → ⊑ᴵ-refl))
constant-target n = finite-reflection n (≼l zero (≼-refl _))
```

极限源的逐支嵌入如何在原目标中保持跨分支相容，仍未在此解决。
不能套用累计拼接后把所得累计目标当作原目标。
