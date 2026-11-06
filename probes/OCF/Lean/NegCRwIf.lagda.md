# C 线重写成一个折叠, 否定一路 (三): 接口 `CRwIf` 的盲区

> 不含记号. 入口 [NegCRw](NegCRw.lagda.md). 只读导入构造一路的接口 [CRwIf](CRwIf.lagda.md) ("接口定稿 2026-11-06 00:49") 与 [CRwBase](CRwBase.lagda.md), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** `CRwIf` 只管世界的移动: 可入 `Adm₀`, 进入后的世界 `nxt₀`, 回灌 `sh₀`, 四条律 (`adm-sh`, `nx-up`, `lg-nx`, `adm↓`). 律里成对的下标都带字面 $\lhd$ 证据 (检查过: 只有 $(B,B')$ 与 $(B,\mathrm{nxt}_0\,B\,e\,a)$). 本篇问: 律约束了什么, 没约束什么.
>
> **结果 (都对一切实例 `I`).**
>
> 1. **`constShOf` (盲).** 把回灌换成与坐标无关的 $\mathrm{sh}_0'\,B\,c=\mathrm{sh}_0\,B\,0$, 其余不动, 仍是实例. 所以律不要求回灌依赖坐标: 留下或坍缩的 $\Omega_1$ 结点在一切坐标处取输入的**同一个**分支, 也满足接口 (对实例 `I₁` 的后果在折叠写出后检查).
> 2. **`stayOf` (盲).** 把进入后的世界换成不动的 $\mathrm{nxt}_0'\,B\,e\,a=B$, 其余不动, 仍是实例. 所以律不要求进入后世界盖住坐标 ($e\lhd\mathrm{nxt}_0\,B\,e\,a$ 不是律); 律只要求世界不缩小.
> 3. **`trivIf` (平凡实例).** `Adm₀ = ⊤`, 世界不动, 回灌恒等: 是实例. 4 条律对它都空洞地成立.
> 4. **`adm-nonempty` (边界).** 对一切实例, 合法世界里可入的坐标存在 (由 `adm-sh`); 所以 `Adm₀` 不能处处为空. 这是律唯一强制的 "进入" 能力.
>
> **前提实例.** 1, 2 的输入实例: 构造一路的 `I₁` (定稿时尚未写出; 写出后在 [NegCRwInst](NegCRwInst.lagda.md) 里代入), 或本篇的 `trivIf`. 4 的合法世界: `hz` (`LgB hz = ⊤`).
>
> **只否定什么.** 不否定接口; 只说律**不**约束: 回灌依赖坐标 (1), 进入后世界盖住坐标 (2). 这两条是否该进接口, 取决于折叠在这些实例上产出什么 (`NegCRwInst` 检查). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegCRwIf where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf
```

## §1 回灌换成常值

```agda
constShOf : CRwIf → CRwIf
constShOf I = record
  { Adm₀ = Adm₀ ; nxt₀ = nxt₀ ; sh₀ = λ B c → sh₀ B hz
  ; adm-sh = λ c lB → adm-sh hz lB ; nx-up = nx-up ; lg-nx = lg-nx ; adm↓ = adm↓ }
  where open CRwIf I

constSh-const : ∀ I B c c′ → CRwIf.sh₀ (constShOf I) B c ≡ CRwIf.sh₀ (constShOf I) B c′
constSh-const I B c c′ = refl
```

## §2 世界不动

```agda
stayOf : CRwIf → CRwIf
stayOf I = record
  { Adm₀ = Adm₀ ; nxt₀ = λ B e a → B ; sh₀ = sh₀
  ; adm-sh = adm-sh ; nx-up = λ a → hself ; lg-nx = λ a lB → lB
  ; adm↓ = λ q a′ → proj₁ (adm↓ q a′) , q }
  where open CRwIf I
```

## §3 平凡实例, 可入非空

```agda
trivIf : CRwIf
trivIf = record
  { Adm₀ = λ _ _ → ⊤ ; nxt₀ = λ B e a → B ; sh₀ = λ B c → c
  ; adm-sh = λ c lB → tt ; nx-up = λ a → hself ; lg-nx = λ a lB → lB
  ; adm↓ = λ q a′ → tt , q }

adm-nonempty : ∀ I → Σ Cd (CRwIf.Adm₀ I hz)
adm-nonempty I = CRwIf.sh₀ I hz hz , CRwIf.adm-sh I hz tt
```
