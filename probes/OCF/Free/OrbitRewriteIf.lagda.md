# 固定同一实际轨道的程序改写合同

本关系只比较字面相同的闭包界 c 和同一 η/e 处的程序分支。
它不要求两个同值层号上的任意函数相容，也不要求新证书任意选择。
改写须把原证书的实际轨道运到新程序，并同时证明最终输出同形。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.OrbitRewriteIf where

open import Data.Product using (Σ)
open import OCF.Free.Level using (Ordᴵ; _⊑ᴵ_; _≅_)
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)

data Pointwise : Z → Z → Set where
  pz : Pointwise Z.zero Z.zero
  ps : ∀ {x y} → Pointwise x y → Pointwise (Z.suc x) (Z.suc y)
  pl : ∀ {f g} → (∀ n → Pointwise (f n) (g n)) →
    Pointwise (Z.lim f) (Z.lim g)
  pc : ∀ {c t t′ o₀ o₀′} {g g′ o o′ : (η : Ordᴵ) → c ⊑ᴵ η → Z} →
    Pointwise t t′ → (∀ η e → Pointwise (g η e) (g′ η e)) →
    Pointwise o₀ o₀′ → (∀ η e → Pointwise (o η e) (o′ η e)) →
    Pointwise (Z.ĉᴸ c t g o₀ o) (Z.ĉᴸ c t′ g′ o₀′ o′)

record OrbitTransport : Set where
  field
    move : ∀ {x y} → Pointwise x y → (G : Goodᴺ x) →
      Σ (Goodᴺ y) (λ H → forceᴺ x G ≅ forceᴺ y H)
```

得到的是随原证书运输的 H，不是对任意新 H 的值无关性。
合同首次编译后冻结，构造和审查共用这个精确域。
