# 只对可入层号给分量的否定 (二): 拷贝的认同要相干

> 不含记号. 入口 [NegColimA](NegColimA.lagda.md). 对着接口 [ColimAIf](ColimAIf.lagda.md) ("接口定稿 2026-11-05 11:12 (编译通过)", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 接口 §4 的 `CrossA` 以 `CohA W` 为前提. 本篇说明这个前提去不掉, 而且合法性 `LgGA` 不提供它:
>
> - **`cross-needs-coh`** (定理): 接口最小实例 $(x_0, w_\omega)$ 里, 层号 `finH 1` 有两个证据 `p₂` (经坐标 2, 即 `κ₂` 的路径) 与 `p₃` (经坐标 3, 即拷贝 `κ₂′` 的路径). 世界 `W×` 按证据走的坐标给分量: 经坐标 2 的是 $1$, 其余是 $0$. 它合法 (`lg×`), 不相干 (`¬coh×`); 在 `p₂` 的分量里 $1$ 有界, 在 `p₃` 的分量里不有界. 所以 "同一层号的两个证据之间搬界" 对合法世界不成立 (`¬CrossLg`).
> - 读法: 拷贝 `κ₂` 与 `κ₂′` 是 `LevA wω x₀` 的两个种类 (各带一条路径), 读 $\beta$ 的两个不同分量. 没有相干, 它们的界互不推出, 这就是 `CohWNeg.no-cross`, `ColimWKS.sum-no-cross→` 的形状在 `ColimAIf` 里的位置. `ColimAIf` 把它从 `cmpK` 挪到了认同上 (接口判决 §1 第 2 条), 这条定理说挪过去以后它确实在那里.
>
> **为什么是构造一路需要的律.** 取并的目的就是拷贝读同一个界 (`ColimW` 判决第 1 条); 在 `ColimAIf` 里这就是 `CrossA`. 本篇说明构造一路必须把 `CohA` 当作不变量带着走: 每次更新都要保它 (`RaiseA′.cohA`, `RaiseA1.coh1`), 这正是 [NegColimALoop](NegColimALoop.lagda.md) 的入口: 单个增量的更新保 `CohA` 推出可入层号上的 `LoopFix₀`.
>
> **对 `AdmWNegCopy.copy→⊥` 的四组前提 (判断, 写明差别).** `copy→⊥` 要一个**种类**在两个证据下有界 (`bd₀`, `bd₁`). `LevA` 的种类带路径, 一个种类只有一个证据, 所以这组前提在 `LevC′` 的层号种类上不出现 (接口选 2 的理由). 能实例化的只有底种类 (坐标是 `A`, 只有一个分量), 那是 `ColimWCopy.shapeA` 的形状: 它推出的 "`LocalLg` 不成立" 只说一个字面上不合法的公共上界 ($\lim(a_0,a_1,a_1,\dots)$) 不合法, 不是障碍. 两个证据的问题在这里以 `cross-needs-coh` 的形式出现, 不以 `copy→⊥` 的形式.
>
> **只否定什么.** 只否定: 不带 `CohA` 前提的 `CrossA` (即使世界合法). **不否定**: 接口的 `CrossA` (带 `CohA`, 构造一路沿 `CohA` 搬运即得); `GlobA`; `LevC′` 是 `KS`; 相干世界的存在 (`W₀A` 相干, `NegColimALoop.coh₀`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegColimACross where

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.ColimWIf using (AdmL; S₁; finH; x₀)
open import OCF.Align.ColimWNeg using (wω)
open import OCF.Align.ColimAIf
open Adm x₀ wω
```

## §1 两个证据, 一个按证据走的世界

```agda
-- 层号 finH 1: 经坐标 2 (κ₂ 的路径) 与经坐标 3 (κ₂′ 的路径)
p₂ p₃ : AdmL x₀ wω (finH 1)
p₂ = hLim {c = finH 2} e₂ hself
p₃ = hLim {c = finH 3} e₃ (hsuc hself)

-- 证据经过的坐标
crd : ∀ {y} → AdmL x₀ wω y → HB S₀
crd (hLim {c = c} _ _) = c

two : HB S₀ → Bool
two (hs (hs hz)) = true
two _ = false

pk : ∀ {T : KS} → Bool → HB T
pk true = hs hz
pk false = hz

W× : GWA x₀ wω
W× = azero , λ y p → pk (two (crd p))

lg× : LgGA W×
lg× = tt , λ y p → lgpk (two (crd p))
  where
  lgpk : ∀ {T : KS} (b : Bool) → LgB {T} (pk b)
  lgpk true = tt
  lgpk false = tt
```

## §2 拷贝的界不互推

```agda
bd₂ : BdLA (just (finH 1 , p₂)) (hs hz) W×
bd₂ = hself

¬bd₃ : ¬ BdLA (just (finH 1 , p₃)) (hs hz) W×
¬bd₃ ()

¬coh× : ¬ CohA W×
¬coh× c with c (finH 1) p₂ p₃
... | ()

-- 去掉 CohA 前提的 CrossA (即使只对合法世界)
CrossLg : Set
CrossLg = ∀ {W} → LgGA W → ∀ y (p p′ : AdmL x₀ wω y) (c : HB (LevA wω y)) →
  BdLA (just (y , p)) c W → BdLA (just (y , p′)) c W

¬CrossLg : ¬ CrossLg
¬CrossLg cr = ¬bd₃ (cr lg× (finH 1) p₂ p₃ (hs hz) bd₂)

cross-needs-coh : LgGA W× × ¬ CohA W× × BdLA (just (finH 1 , p₂)) (hs hz) W× × ¬ BdLA (just (finH 1 , p₃)) (hs hz) W×
cross-needs-coh = lg× , ¬coh× , bd₂ , ¬bd₃
```
