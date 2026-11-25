# K2 第 4 层：规范 Ω₁ 的加法链闭项保值

本篇是验收文件，允许导入带记号闭包的 `Value`、`RR4ChainAdd`。
[Base](YiK2Base.lagda.md) 不导入本篇，也不读本篇的关系或参照。
这里读的是已合法的 Raw 0 闭项；没有给任意高层 LF 建值解释。

先证 Raw 0 的加法和可数折叠与已有可数树的运算逐结构互模拟，
再将真正生成的链与 RR4 的加法链逐项按值比较，最后调用其规范 Ω₁ 保值定理。
最终验收是序数值互相 `≼`，不要求与原 EBO 基本列逐项一致。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2Value where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.YiK2Base
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4ChainAdd as A
import OCF.Align.RR4MonoFragment as M
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open L using (_≅_; z≅; s≅; l≅; ≅-refl⁰; ≅-trans; add-≅)
open V using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≅→≈ᵛ; +-mono; ψ⁰-mono⁰; l≼; ≼l)

read : R → L.Ordᶜ L.zero
read G.zero = L.zero
read (G.suc x) = L.suc (read x)
read (G.lim f) = L.lim (λ n → read (f n))
read (G.lc () c t g)
read (G.em () t)
read G.top = L.suc L.zero

read-add : ∀ x y → read (x +ʳ y) ≅ (read x L.+ read y)
read-add x G.zero = ≅-refl⁰ (read x)
read-add x (G.suc y) = s≅ (read-add x y)
read-add x (G.lim f) = l≅ (λ n → read-add x (f n))
read-add x (G.lc () c t g)
read-add x (G.em () t)
read-add x G.top = s≅ (≅-refl⁰ (read x))

read-copies : ∀ x (y : L.Ordᶜ L.zero) → read x ≅ y → ∀ n →
  read (copies x n) ≅ iter (y L.+_) L.zero n
read-copies x y e zero = z≅
read-copies x y e (suc n) =
  ≅-trans (read-add x (copies x n))
    (add-≅ {σ = λ q → q} {σ′ = λ q → q} e (read-copies x y e n))

read-ψ : ∀ x → read (ψᶜ x) ≅ L.ψ⁰ (read x)
read-ψ G.zero = s≅ z≅
read-ψ (G.suc x) = l≅ (read-copies (ψᶜ x) (L.ψ⁰ (read x)) (read-ψ x))
read-ψ (G.lim f) = l≅ (λ n → read-ψ (f n))
read-ψ (G.lc () c t g)
read-ψ (G.em () t)
read-ψ G.top = l≅ (read-copies one (L.suc L.zero) (s≅ z≅))

-- 两个参数的关系都只出现在验收中，程序不读取值关系。
read-add-≈ : ∀ x y → read (x +ʳ y) ≈ᵛ (read x L.+ read y)
read-add-≈ x y = ≅→≈ᵛ (read-add x y)

read-ψ-≈ : ∀ x → read (ψᶜ x) ≈ᵛ L.ψ⁰ (read x)
read-ψ-≈ x = ≅→≈ᵛ (read-ψ x)

rchain : ℕ → R
rchain n = proj₁ (Canonical.chain start n)

chain-forward : ∀ n → read (rchain n) ≼ A.chain⁺ A.idᵇ n
chain-forward zero = ≼-refl (L.suc L.zero)
chain-forward (suc n) =
  ≼-trans (proj₁ (read-add-≈ (rchain n) (ψᶜ (rchain n))))
    (+-mono (chain-forward n)
      (≼-trans (proj₁ (read-ψ-≈ (rchain n)))
        (≼-trans (ψ⁰-mono⁰ (chain-forward n))
          (M.step≽ A.idᵇ (A.chain⁺ A.idᵇ n)))))

chain-backward : ∀ n → A.chain⁺ A.idᵇ n ≼ read (rchain n)
chain-backward zero = ≼-refl (L.suc L.zero)
chain-backward (suc n) =
  ≼-trans
    (+-mono (chain-backward n)
      (≼-trans (M.step≼ A.idᵇ (A.chain⁺ A.idᵇ n))
        (≼-trans (ψ⁰-mono⁰ (chain-backward n))
          (proj₂ (read-ψ-≈ (rchain n))))))
    (proj₂ (read-add-≈ (rchain n) (ψᶜ (rchain n))))

closed-additive : read closed ≈ᵛ A.F⁺ A.idᵇ
closed-additive =
  l≼ (λ n → ≼l n (≼-trans (proj₁ (read-ψ-≈ (rchain n)))
    (ψ⁰-mono⁰ (chain-forward n)))) ,
  l≼ (λ n → ≼l n (≼-trans (ψ⁰-mono⁰ (chain-backward n))
    (proj₂ (read-ψ-≈ (rchain n)))))

same-on-Ω₁ : read closed ≈ᵛ L.ψ⁰ V.Ω₁
same-on-Ω₁ =
  ≼-trans (proj₁ closed-additive) (proj₁ A.same-on-Ω₁) ,
  ≼-trans (proj₂ A.same-on-Ω₁) (proj₂ closed-additive)
```

这是规范 Ω₁ 根折叠闭项的无条件值定理；`closed-legal` 在 Base 已给出。
`same-on-Ω₁` 不为 [Stop](YiK2Stop.lagda.md) 的无坐标源生成坐标，
也不说明所有同值 Ω 结点的折叠值一致，不外推为完整 ψ 的保持或 EBO 下界。
