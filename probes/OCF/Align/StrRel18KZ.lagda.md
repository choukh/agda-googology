# 结构关系, 第十八轮 (三): (c) 的变体 `kZ` 排除 `NegSR17RkT` 的反例

> 不读记号. 入口 [StrRel18](StrRel18.lagda.md). 接口 [StrRel18If](StrRel18If.lagda.md) §2. 实例 $\Lambda_2=2$.
>
> **(否定, 定理) `¬domKZ-P`**: `NegSR17RkT` 的反例 (节点 `r₀`, 分支 `n1`, 产生时动作 `Az`, 产生状态 `YP`, 右边在 $T_1$ 上保留) **不满足** (c) 的变体 `kZ`: 右边保留分支在输入 `n0` 时运行的状态, 在第 $0$ 层目标上的读数是 $\omega\cdot(1⨾0)⨾0$ (值 $\omega$, 因为 `cv` 保留差分量 `dN`), 而左边产生时的累计 $z_P$ 的值是 "右边的再折叠输出 $+1$", 至少 $\omega+1$ (`ω≤R`: 右边的再折叠输出的链的第一项是 $\omega$ 个非零项的和).
>
> 与 `StrRel18Obs` 合起来 (定理): `kZ` 含 `rkAt` 那一对 (`domKZ₁`), 排除 `Az` 的反例 (本文); `kD` 两者都含 (`domKD₁`, `domKD-P`, 所以 `¬RkSoundTKD`); `kJ` 连 `rkAt` 那一对也排除 (`¬domKJ`). **`kZ` 是三个变体里唯一同时做到两件事的.** 但 `RkSoundTK kZ` 仍推出 `RkLeft tt ReL` (`obsKZ`): (c) 碰不到第一个障碍.
>
> **只否定什么.** 只说这一组参数不满足 `kZ` 的前提, 所以 `NegSR17RkT` 的反例不是 `RkSoundTK kZ` 的反例. 不说 `RkSoundTK kZ` 成立. 没有推出 LPO/WLPO 或判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel18KZ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤l; l≤; ≤-refl; ≤-trans; irr; ⊲→≤)
open import OCF.Align.HtFeedTree using (hz; hself; D₀; n0; n1; _⨾_; nl; accL; sum; sum-fst; pt)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel13Val using (Λ₂; r₀)
open import OCF.Align.StrRel15Fin using (T₁)
open import OCF.Align.StrRel16Lem using (module V0)
open import OCF.Align.NegSR17RkT using (Az; uN; YP; zP; RefR₀; sumDrp)
open import OCF.Align.StrRel18If Λ₂ tt using (DomKv; kZ)

open V0 Λ₂ tt using (vsum⁺)
```

## 1 $\omega$ 不超过右边的再折叠输出

```agda
c1 : ℕ → D₀ azero
c1 _ = n1 ⨾ n0

ωs : ℕ → A
ωs = pt azero c1

go : ∀ (e : ℕ → D₀ azero) → (∀ m b → asuc b ≤ sum b (e m)) → ∀ k → ωs k ≤ pt azero e k
go e h zero = ≤-refl azero
go e h (suc k) = ≤-trans (s≤ (go e h k)) (h k (pt azero e k))

liftω : ∀ (e : ℕ → D₀ azero) → (∀ m b → asuc b ≤ sum b (e m)) → alim ωs ≤ sum azero (nl e)
liftω e h = l≤ (λ k → ≤l k (go e h k))

-- 右边的再折叠输出是链的极限; 链的第一项是 ω⋅(1 ⨾ 0) 的运行, 每个 n1 调用分支动作, 输出以 n1 结尾
ω≤R : alim ωs ≤ sum azero RefR₀
ω≤R = ≤-trans (liftω _ (λ m b → s≤ (⊲→≤ (sum-fst b _)))) (≤l 1 (≤-refl _))
```

## 2 否定

```agda
¬domKZ-P : ¬ DomKv kZ tt YP (accL Λ₂) (accL hz) r₀ uN C.self hself Az n0 YP T₁
¬domKZ-P h = irr (alim ωs) (≤-trans (s≤ (≤-trans ω≤R (sumDrp RefR₀ azero))) (vsum⁺ (h C.self tt n0) (≤-refl azero)))
```
