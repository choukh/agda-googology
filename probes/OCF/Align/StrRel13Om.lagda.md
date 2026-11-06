# 结构关系, 第十三轮 (四): $\Omega^{\mathsf H}$ 处 `StrRel12` 的三个前提都不成立 (否定)

> 不读记号. 入口 [StrRel13](StrRel13.lagda.md). 实例 $\Lambda=\Omega^{\mathsf H}$ (`hΩ emb`). 交接单第 2 项要的是 `MonoStep Ωᴴ`: 左边 $\Omega_\Omega$ 在树世界 $0$ 里, 经路径 `z⊲ one` 到运行世界 $1$, 状态 `Y₀`; 右边在树世界 $1$ 里, 路径 `self`, 状态 $(Y_0\oplus\mathrm{Step}\,Y_0)\oplus 0$. 若走 `StrRel12.sem∀`, 要三件: (a) 运行路径对是 `CP`, (b) 两棵树按 `Rel Ωᴴ` 相关, (c) 外层动作 `Act` 的 `HAW`. 本文证明三件在 `StrRel12` 的族里都不成立:
>
> 1. **`¬cpTop`**: 路径对 (`z⊲ one`, `self`) 不是 `CP` (左边走一步, 右边不走, `Al` 没有对应的构造子). 把左边的路径并进树 (`nw`, `ΔΩ-nw` 说两种写法的折叠逐字相同) 也不行: **`¬relTop`**, `nw` 包着的树与不带 `nw` 的树不相关. 所以 `MonoStep Ωᴴ` 的顶层比较在 `sem∀` 的定义域之外, 与跨坐标层无关.
> 2. **`¬selfΩ`**: 同一个世界 $0$ 里, $\Omega_\Omega$ 也不与自己相关. `StrRel12Om.¬ΩR` 用的是世界 $0$ 对 $1$; 这里两边都是 $0$, `CP` 分支对 $(1,2)$ 仍然对齐 (`cp12′`: 右边多走一步, `aR`), 两个节点的坐标层是 `emb 1` 与 `emb 2`. 所以在 `κᴸ` 对一切 `CP` 分支对量化的写法下, 跨坐标层的节点规则连自比都离不开.
> 3. **`¬hawΩ`**: `HAW Ωᴴ tt tt Act Act` 不成立. 这是 `StrRel12` §3 那一步判断的编译形式: 在目标 $\Omega^{\mathsf H}$ (世界 $0$) 上 `Act` 输出 $\omega\cdot(\Omega_\Omega ⨾ 0)$, 要两份相关, 归到 `¬selfΩ`.
>
> **前提可满足.** `¬hawΩ` 只用了 `HAW` 的一个实例: 路径 `self`, 世界 $0$, 上下文 `n0`, 空状态, 目标 `tg self hself tt`, 全部写出.
>
> **范围.** 只否定 `StrRel12` 的族 (`StrRel12Rel.Rel`, `StrRel12Al.CP`, `StrRel12Sem.HAW`) 在 $\Omega^{\mathsf H}$ 处的这三件. 不否定 `MonoStep Ωᴴ` 本身.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel13Om where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (z≤; s≤; ≤-refl)
open import OCF.Align.HtFeedTree using (hself; Ωd; n0; nw; _⨾_; accᴸ)
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel4Walk using (aS; aP; aR)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel12Al using (CP; cp-self)
open import OCF.Align.StrRel12Rel using (Rel; n0ᴸ; ⨾ᴸ; nlᴸ; prᴸ; κᴸ)
import OCF.Align.StrRel12Sem as Sm

module P = At Ωᴴ Lg-Ωᴴ
module S = Sm Ωᴴ Lg-Ωᴴ

one two : A
one = asuc azero
two = asuc one
```

## 1 顶层: 路径对不是 `CP`, 并进树也不相关

```agda
¬cpTop : ¬ CP {V = azero} {V′ = one} tt tt (z⊲ one) tt C.self tt
¬cpTop ((() , _) , _)

-- 左边的路径并进树: 折叠逐字相同
ΔΩ-nw : P.ΔΩ ≡ P.Run accᴸ (nw (z⊲ one) (Ωd Ωᴴ {azero})) C.self tt hself P.Act n0 P.Y₀
ΔΩ-nw = refl

¬relTop : ¬ Rel Ωᴴ {one} {one} tt tt (nw (z⊲ one) (Ωd Ωᴴ {azero})) (Ωd Ωᴴ {one})
¬relTop (prᴸ ())
```

## 2 同一世界里 $\Omega_\Omega$ 也不自相关

```agda
-- 分支世界对 (1, 2), 两边都从 0 起: 右边多走一步
cp12′ : CP {V = azero} {V′ = azero} tt tt (C.suc C.self) tt (C.suc (C.suc C.self)) tt
cp12′ = (aR (aP (aS C.self tt) z≤ ad) , ad , refl , refl) , s≤ z≤ , tt , tt
  where
  ad : Adm azero azero one two
  ad = one , ≤-refl one , s≤ z≤

¬selfΩ : ¬ Rel Ωᴴ {azero} {azero} tt tt (Ωd Ωᴴ) (Ωd Ωᴴ)
¬selfΩ (⨾ᴸ _ (κᴸ h)) with h (C.suc C.self) (C.suc (C.suc C.self)) tt tt cp12′
... | ()
¬selfΩ (prᴸ ())

¬selfΩ⨾ : ¬ Rel Ωᴴ {azero} {azero} tt tt (Ωd Ωᴴ ⨾ n0) (Ωd Ωᴴ ⨾ n0)
¬selfΩ⨾ (⨾ᴸ h _) = ¬selfΩ h
¬selfΩ⨾ (prᴸ (⨾ᴸ () _))
¬selfΩ⨾ (prᴸ (prᴸ ()))
```

## 3 外层动作的前提

```agda
cp0 : CP {V = azero} {V′ = azero} tt tt C.self tt C.self tt
cp0 = cp-self tt tt (≤-refl azero) tt tt

¬hawΩ : ¬ S.HAW Ωᴴ {azero} {azero} tt tt P.Act P.Act
¬hawΩ ha with ha C.self C.self tt tt cp0 n0 n0 n0ᴸ P.Y₀ P.Y₀ ((λ T T′ tc → n0ᴸ) , n0ᴸ)
                 (P.tg C.self hself tt) (P.tg C.self hself tt) cp0
... | nlᴸ g = ¬selfΩ⨾ (g 0)
```
