# 对角线: 对任何一层的一个定义

> 不含记号. 结论写在 [DomFold](DomFold.lagda.md).
>
> - `Tψₙ n k`: $\psi_k(\Omega_{\Omega_{n+2}})$. `Tψ₀ₙ`: $\psi_0(\Omega_{\Omega_{n+2}})$ 的**闭项**, 对一切 $n$, 无条件: 一棵带链的符号树, 输入是 `Ωₙ n` 与定理 `Cf-Ωₙ n`. 它的值要把链读回成分支, 这要证书, 所以**闭项不等于定义了序数**. 与 `EBOᵀ` 同档 (判断).
> - `ψ₁ᶠ`: 任何带证书的层号折叠到第 1 层, 对任何 `DomX`.
> - `Diag`: $\psi_0(\Omega_{\Omega_{h+2}})=\sup_k\psi_0(\Omega_{u_k})$, $u_0$ = `base`, $u_{k+1}=\psi_{h+1}(\Omega_{u_k})$, $h$ = `ht`. 这是 EBO 的基本列 (**受记号影响**, 测试在 [DomFoldAccept](DomFoldAccept.lagda.md)). **`GoodFeed` 是模块参数, 没有证: 这是条件定义.** 对 `X₀` 是 $\psi_0(\Omega_{\Omega_2})$, 取代 [GuardTightUp](GuardTightUp.lagda.md) 的 `Diag` (不用路径与表); 对 `X₁` 就是 $\psi_0(\Omega_{\Omega_3})$ 的链点 $u_{k+1}=\psi_2(\Omega_{u_k})$. 不逐层写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DomFoldDiag where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.GuardTightLv
open import OCF.Align.DomFoldDom
open import OCF.Align.DomFoldNext
import OCF.Align.DomFoldBase as DBase
import OCF.Align.DomFoldTree as DTree

-- 第 n 层的树, 任何目标 k: 一个定义, 对 n 与 k 没有分情况
Tψₙ : ∀ n k → DTree.T⁰ (Xₙ (suc n)) k
Tψₙ n k = DTree.Tn (Xₙ (suc n)) (Ωₙ n) (Cf-Ωₙ n) (DBase.Tc-id (Xₙ (suc n)) (Ωₙ n)) k

-- ψ₀(Ω_{Ω_{n+2}})
Tψ₀ₙ : ∀ n → DTree.T⁰ (Xₙ (suc n)) 0
Tψ₀ₙ n = Tψₙ n 0

-- ψ₁(Ω_L), 任何定义域
ψ₁ᶠ : (X : DomX) (L : Lv.LG (DomX.𝔻 X)) → Lv.Cfˢ (DomX.𝔻 X) L → DBase.Tc X L → DTree.T⁰ X 1
ψ₁ᶠ X L cf tc = DTree.Tn X L cf tc 1

module DiagOf (X : DomX) where
  open DomX X
  open Lv 𝔻
  open DBase X using (Tc; Tc-id)
  open DTree X

  GL : Set
  GL = Σ LG λ x → Cfˢ x

  -- ψ_{h+1}(Ω_x), 读回. 没有条件. 读回给的是层号, 不是好层号.
  feed : GL → LG
  feed (x , cf) = rb (Tn x cf (Tc-id x) (suc ht))

  record GoodFeed : Set where
    field
      cfF : ∀ u → Cfˢ (feed u)

  module Diag (G : GoodFeed) where
    open GoodFeed G

    us : ℕ → GL
    us zero = base
    us (suc k) = feed (us k) , cfF (us k)

    -- ψ₀(Ω_{Ω_{h+2}}). 一个定义, 对 k 没有分情况.
    Tdiag : T⁰ 0
    Tdiag = ol (λ k → Tn (proj₁ (us k)) (proj₂ (us k)) (Tc-id (proj₁ (us k))) 0)
```
