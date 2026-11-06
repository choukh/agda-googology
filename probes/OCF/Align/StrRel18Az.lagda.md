# 结构关系, 第十八轮 (一): 决定性实验: $\Omega$-极限处, 保留输出的分支动作读第 $0$ 层累计

> 不读记号. 入口 [StrRel18](StrRel18.lagda.md). 接口 [StrRel18If](StrRel18If.lagda.md) §1.
>
> 设定: $\Lambda_\kappa=\mathrm{h\Omega}\,(\lambda\_\to1)$ (`NegSR16Kap.Λκ`, 含 $\Omega$-极限而层有限的最小例子). $\Omega_{\Lambda_\kappa}$ (`Ωd Λκ`) 里 `nκ` 的分支在坐标 $0$ 上是节点 `r` (层 $\Lambda_\kappa$, 坐标层 $1$, 分支 `n1`). 折叠自己的 `RKi` 以动作 `Act`, 状态 $Y$ 在第 $\Lambda_\kappa$ 层目标 `TΛ` 上运行它: 坐标层 $1$ 在 $\Lambda_\kappa$ 之下, **保留** (`kindK`), 输出是新节点 `K Y` (`chkK`), 它的分支 `brK Y` 是 `BNi` 在第 $\Lambda_\kappa$ 层目标上的输出, 字面地以 $\omega\cdot(\Omega_{\Lambda_\kappa}⨾\ldots)$ 起头 (`brK-shape`), 含 `nκ`.
>
> 1. **(定理, 正面) `noZ-Act`, `noZ-Air`**: `Act` 满足 `NoZ`; 原来的节点 `r` (分支 `n1`) 的分支动作也满足 (都是 `refl`).
> 2. **(否定, 定理) `¬noZ-AiK`**: 保留输出 `K Y` 的分支动作 (以 `Act` 再运行, 也满足 `NoZ` 的动作) **不满足 `NoZ`**: 在第 $0$ 层目标上, 累计 `n0` 与 `n1` 给出字面不同的输出. 机制: 分支里的 `nκ` 在第 $0$ 层目标上回灌, 第 $0$ 格的世界是 $W+\text{累计}$ (`HtFeedFold.κc` 的字面), 累计多一步, `Walk` 就多走一格.
> 3. **(否定, 定理) `¬AiNoZ`**: 接口的律 `AiNoZ` 不成立 (第 2 条的实例).
>
> **读法 (判断).** 修补方向 (a) 要求语义里的动作不读累计, 并要求这一点沿节点的分支动作传下去 (`AiNoZ`), 因为节点再折叠时链的动作就是它的分支动作. 第 2 条说: 在有 $\Omega$-极限的 $\Lambda$ 上, 折叠自己产生的保留节点 (从 $\Omega_{\Lambda_\kappa}$ 的节点, 动作 `Act`) 的分支动作读累计. 所以 (a) 的限制在 $\Omega$-极限处不被折叠的节点满足: **(a) 作为对一切节点的不变量, 在 $\Omega$-极限处是空的.** 只对分支不含 `nκ` 的节点 (例如有限的 $\Lambda$) 它才可能成立 (那一半本文没有证).
>
> **只否定什么.** 只否定字面的 `NoZ` 沿保留节点传递 (`AiNoZ`), 实例 $\Lambda_\kappa$. 不说输出的值依赖累计 (`NoZ` 是命题相等; 判断: `Walk` 多走一格, 值更大). 不否定 `RkSoundTᶻ` (那要值的反例, 见否定一路). 没有推出 LPO/WLPO 或判定.
>
> **前提可满足.** `noZ-Act` 是 `Act` 满足前提的证明; `kindK` 是 `refl`; 状态 $Y$ 任意 (定理对一切产生状态).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel18Az where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hΩ; hself; sL; StH; Vs; D; D₀; n0; n1; _⨾_; nl; ni; nκ; nw; Ωd; accL; outS; inS; ⊲ᴴ↑)
open import OCF.Align.NegSR16Kap using (Λκ; lΛκ)
open import OCF.Align.StrRel18If Λκ lΛκ using (NoZ; AiNoZ)
import OCF.Align.StrRel16If as If³

open If³ Λκ lΛκ using (module P)
open P using (Tg; tg; τ₀; St; st; d; z; yc; Run; Act; Step; Ig; LW; Ai; BNi; RKi; rkT; kk; rise; keep; Y₀)
```

## 1 节点与目标

```agda
-- Ωd Λκ 里 nκ 的分支在坐标 0 上的节点: 层 Λκ, 坐标层 1, 分支 n1
r : StH azero (hs hz) Λκ
r = sL C.self hself

u₁ : ∀ {W′} → azero ⊲ W′ → Lg W′ → Vs Λκ r W′ → D Λκ W′
u₁ _ _ _ = n1

chkΩ : Ωd Λκ {azero} ≡ n1 ⨾ nκ tt (λ {c} _ _ → ni (sL {c = c} C.self hself) (λ _ _ _ → n1))
chkΩ = refl

-- 第 Λκ 层的目标
TΛ : Tg azero Λκ azero
TΛ = tg C.self hself tt

hk : LW (hs hz) azero
hk = kk r C.self hself

-- 坐标层 1 在 Λκ 之下: 保留
kindK : rkT hk hself tt ≡ keep r
kindK = refl
```

## 2 保留输出与它的分支

```agda
brK : St azero → D Λκ azero → ∀ {W′} → azero ⊲ W′ → Lg W′ → Vs Λκ r W′ → D Λκ W′
brK Y w p lW′ y = yc (BNi (accL Λκ) (accL (hs hz)) r u₁ C.self hself Act w Y hk (⊲-tr C.self p) lW′ (outS r y))
                     (tg C.self (⊲ᴴ↑ p hself) lW′)

-- 产生时的状态 Y 与上下文 w 任意
K : St azero → D Λκ azero → D Λκ azero
K Y w = RKi (accL Λκ) (accL (hs hz)) r u₁ C.self tt hself Act w Y TΛ (keep r)

chkK : ∀ Y w → K Y w ≡ ni r (brK Y w)
chkK Y w = refl

-- 分支的字面: ω⋅(Ω_Λκ ⨾ …), 含 nκ
brK-shape : ∀ Y w (y : Vs Λκ r azero) → Σ (D Λκ azero) (λ R → brK Y w C.self tt y ≡ nl (λ _ → Ωd Λκ ⨾ R))
brK-shape Y w y = _ , refl
```

**`K` 就是闭项的折叠里出现的节点.** 闭项的第一步 $\Omega_{\Lambda_\kappa}$ (`Ωd Λκ`, 动作 `Act`, 状态 $Y_0$, 上下文 `n0`) 在第 $\Lambda_\kappa$ 层目标 `TΛ` 上的输出是 `a ⨾ (b ⨾ nκ tt fκ)` (`inFold`), `nκ` 在坐标 $0$ (路径 `self`) 上的分支 `fκ self tt` 字面地是某个 `K Y w` (`cellK`).

```agda
uκ : ∀ {c} → azero ⊲ c → Lg c → D Λκ c
uκ {c} _ _ = ni (sL {c = c} C.self hself) (λ _ _ _ → n1)

fκ : ∀ {c} → azero ⊲ c → Lg c → D Λκ c
fκ {c} p lc = yc (P.Kb (accL Λκ) uκ C.self hself Act (n0 ⨾ nw C.self n1) (Y₀ P.⊕⟨ tt ⟩ Step Y₀) C.self tt p lc) (tg C.self (⊲ᴴ↑ p hself) lc)

inFold : Σ (D Λκ azero) (λ a → Σ (D Λκ azero) (λ b →
           yc (Run (accL Λκ) (Ωd Λκ) C.self tt hself Act n0 Y₀) TΛ ≡ a ⨾ (b ⨾ nκ tt fκ)))
inFold = _ , _ , refl

cellK : Σ (St azero) (λ Y → Σ (D Λκ azero) (λ w → fκ C.self tt ≡ K Y w))
cellK = _ , _ , refl
```

## 3 `NoZ` 的正面: `Act`, 原来的节点

```agda
noZ-Act : ∀ {L W} (lW : Lg W) → NoZ {L} {W} lW Act
noZ-Act lW p lW₁ w Y z′ T = refl

AiR : Ig (hs hz) azero
AiR = Ai (accL Λκ) (accL (hs hz)) r u₁ C.self hk hself Act n0

noZ-Air : NoZ tt AiR
noZ-Air p lW₁ w Y z′ T = refl
```

## 4 保留节点的分支动作读累计

保留节点 `K Y` 以 `Act` 再运行 (世界 $0$, 路径 `self`, 上下文 `n0`) 时, 它的链的动作是

```agda
hkK : LW (hs hz) azero
hkK = kk r C.self hself

AiK : St azero → D Λκ azero → Ig (hs hz) azero
AiK Y w = Ai (accL Λκ) (accL (hs hz)) r (brK Y w) C.self hkK hself Act n0
```

观察: 第 $0$ 层目标上的输出是 $\omega\cdot(\ldots)$; 取第 $0$ 项, 它是 $(\Omega_{\Lambda_\kappa}$ 的运行$)⨾\ldots$; 再取 $\Omega_{\Lambda_\kappa}$ 的运行的右段 (`nκ` 的回灌, 也是 $\omega\cdot\ldots$) 的第 $0$ 项 (第 $0$ 格), 它是 `Walk` 的输出加一段; `Walk` 那一段在累计为 `n0` 时是 `n0`, 在累计为 `n1` 时是 `n0 ⨾ …`.

```agda
hd lf rt : ∀ {t m} → D t m → D t m
hd (nl e) = e 0
hd x = x
lf (a ⨾ b) = a
lf x = x
rt (a ⨾ b) = b
rt x = x

obs : D₀ azero → D₀ azero
obs x = lf (hd (rt (lf (hd x))))

outZ : St azero → D Λκ azero → D₀ azero → D₀ azero
outZ Y w zz = yc (AiK Y w C.self tt n0 (st (d Y₀) zz)) (τ₀ tt)

obs0 : ∀ Y w → obs (outZ Y w n0) ≡ n0
obs0 Y w = refl

obs1 : ∀ Y w → Σ (D₀ azero) (λ X → obs (outZ Y w n1) ≡ n0 ⨾ X)
obs1 Y w = _ , refl

-- 一切产生状态与上下文
¬noZ-AiK : ∀ (Y : St azero) (w : D Λκ azero) → ¬ NoZ tt (AiK Y w)
¬noZ-AiK Y w h with cong obs (h C.self tt n0 Y₀ n1 (τ₀ tt))
... | ()

¬AiNoZ : ¬ AiNoZ
¬AiNoZ h = ¬noZ-AiK Y₀ n0 (h (accL Λκ) (accL (hs hz)) r (brK Y₀ n0) C.self hkK hself Act n0 tt (noZ-Act tt))

-- 闭项里的那个节点: 它的分支动作读累计
¬noZ-fold : ¬ NoZ tt (Ai (accL Λκ) (accL (hs hz)) r (brK (proj₁ cellK) (proj₁ (proj₂ cellK))) C.self hkK hself Act n0)
¬noZ-fold = ¬noZ-AiK (proj₁ cellK) (proj₁ (proj₂ cellK))
```
