# NegValX (二): 对接口 `ValX`: 两边都值合法时 "本身 ≤ 拷贝" 不可能

> 不含记号. 入口 [NegValX](NegValX.lagda.md). 对构造一路 ValX 的接口 [ValXIf](ValXIf.lagda.md) (定稿 2026-11-06 08:05, 本路不改它), 实例 `I₁`. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **`self≤copy-excl` (定理, 对一切 `X : ValX`).** 对 [NegValXSelf](NegValXSelf.lagda.md) 的世界 $B$ (前提同那里: 合法, $2\lhd B$, $g\,B=2$) 与一切目标证据: 若 $\Omega_1$ 本身结点 $X_n$ 与拷贝结点 $Y_n$ (同一分支 $g$) 都值合法 (`MoX`), 则 `¬ LeX Xn Yn`. 证明: `X-mono` (同一世界, 同一目标, 界 $0\le0$) 给出第 0 层的 `Le`, `sound₀` 落到 `TLRuleSpec._≤_`, 与 `self≰copy` 矛盾.
>
> **推论 `by-level-excl`.** 若 `LeX` 含 "按层比较" 的一条 (同层两个结点, 分支逐点 `LeX`, 就 `LeX`; 这里只要它对本身与拷贝成立: `ByLevel`), 且 $X_n$, $Y_n$ 都值合法, 则 `X` 不存在. 所以 ValX 的关系若在 `XS` 上按层比较 `Ω≤Ω`, 它的 `MoX` 必须排除 $X_n$ 或 $Y_n$.
>
> **前提实例.** 世界: `inst-ω`, `inst-B₁` ([NegValXSelf](NegValXSelf.lagda.md) §3). `MoX Xn`, `MoX Yn`: 取决于构造一路的 `MoX`; 对 ValC 式的值合法 (分支对坐标值单调, 分支值合法), 前提由 `g-up` 支持: $g$ 的值只有 $0$ 与 $2$ (`g-cases`), $c\le c'$ 且 $g\,c=2$ 推出 $g\,c'=2$ (判断: 这样的 `MoX` 下两者都值合法; 本篇不依赖构造一路的定义, 没有编译这一句). `ByLevel` 被 ValC 的 `Ω≤Ω` 推广到 `XS` 时满足 (判断, 依据构造一路 08:05 的计划 "Ω≤Ω 按层, 推广到 XS"). 接口一侧: 实例要构造一路给出; 在那之前本篇的定理对 "不存在的 `X`" 空真, 但 `self≤copy-excl` 的陈述对任一实例都有内容.
>
> **只否定什么.** 只否定: `ValX` 的实例里同时有 `MoX Xn`, `MoX Yn`, `LeX Xn Yn`. **不否定**: `LeX Yn Xn` ("拷贝 ≤ 本身", `copy≤self` 说明折叠后方向一致); 按 (层, 策略) 比较的关系; `X-mono` 本身.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValXIfSelf where

open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValXIf I₁
open import OCF.Lean.NegValXSelf
```

```agda
module _ (X : ValX) where
  open ValX X

  module OnB (B : Cd) (lB : LgB B) (e2 : hs (hs hz) ⊲ B) (gB : g B ≡ Big) (pt : hz ⊲ B) where
    open Self B lB e2 gB

    self≤copy-excl : MoX Xn → MoX Yn → ¬ LeX Xn Yn
    self≤copy-excl mx my p =
      self≰copy pt (sound₀ (X-mono B lB hz pt pt ndX ndY
        (Mo-hz hz) (Mo-hz hz) (le-refl hz hz) (le-refl hz hz) mx my p))

  -- 按层比较 (只要求对本身与拷贝, 分支相同时)
  ByLevel : Set
  ByLevel = (∀ c → LeX (g c) (g c)) → LeX Xn Yn

  by-level-excl : ByLevel → MoX Xn → MoX Yn → ⊥
  by-level-excl bl mx my =
    OnB.self≤copy-excl B₁ Lg-B₁ (hsuc (hlim 0 hself)) refl pt₁ mx my (bl (λ c → leX-refl (g c)))
```

## 结论 (按档)

- **[定理, 对一切 `X : ValX` (实例 `I₁`), 一切满足前提的世界]** `OnB.self≤copy-excl`: `MoX Xn → MoX Yn → ¬ LeX Xn Yn`. `by-level-excl`: `ByLevel → MoX Xn → MoX Yn → ⊥` (世界取 `TX` 进入一次 $\Omega_1$ 分支后的 $B_1$).
- **[判断]** ValC 式 `MoX` 下 `MoX Xn`, `MoX Yn` 成立; 按层比较的 `Ω≤Ω` 推广到 `XS` 时 `ByLevel` 成立. 两者都要构造一路的定义才能编译.
