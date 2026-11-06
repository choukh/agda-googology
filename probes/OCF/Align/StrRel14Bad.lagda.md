# 结构关系, 第十四轮 (六): `CP` 分支对的定义域里有 "左升右留" 的节点对

> 不读记号. 入口 [StrRel14](StrRel14.lagda.md); 说明见 [StrRel14Rk](StrRel14Rk.lagda.md) 文件头第 3 条. 实例 $\Lambda=\Omega^{\mathsf H}$ (`hΩ emb`). 记 $\omega_0=\lim_n 0$ (`alim (λ _ → azero)`, 合法: 相邻项是 `self`).
>
> - `cpBad`: 分支世界对 $(\omega_0, 0)$ 是 `CP` 对 (两边路径都是 `self`; 顶端值 $\omega_0\le 0$; 对齐 `aS`; 自洽). 所以 `StrRel12Rel.κᴸ` 关于 `Ωd Ωᴴ {ω₀}` 与 `Ωd Ωᴴ {0}` 的前提要求这两个世界上的分支节点 `ni (sL self hself) (λ _ _ _ → n1)` 相关; 它们的坐标层是 `emb ω₀` $=\mathrm{hl}(\lambda\_.\,0)$ 与 `emb 0` $=0$.
> - `tcBad`: 目标层 $t=\mathrm{hl}(\lambda\_.\,0)$, 左目标在世界 $\omega_0$ (路径 `self`), 右目标在世界 $\omega_0$ (路径 $0\lhd\omega_0$); 这一对是 `TC` (对齐 `aS`).
> - `rkBadL`, `rkBadR`: 在这对目标上, 左节点 `rkT` 是 `rise`, 右节点是 `keep (sl 0 hself)`. `rk-mono` 在坐标层字面 $k\sqsubseteq_\infty k'$ 时排除这一种; 这里 $k=\mathrm{hl}(\lambda\_.\,0)$, $k'=0$, 两者值相等, $k'\sqsubset k$ 字面成立, 没有 $k\sqsubseteq_\infty k'$.
>
> **范围 (只说这些).** 这是一个实例, 不是否定定理: 它说 `κᴸ` (与 `HAW` 的目标对) 只带值上的 $c\le c'$ 时, 律的定义域含坐标层值相等而字面倒序的节点对, 那里两边种类是 "左升右留"; 不说这一对在值上不可比, 不说闭项 $T_\Omega$ 的折叠会走到这一对 (闭项从世界 $1$ 起, 世界 $0$ 不在它的路径上, 判断).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel14Bad where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (z≤; l≤; ≤-refl)
open import OCF.Align.HtFeedTree using (H; hz; hl; hLim; hself; sl; sL; StH; _⊲[_]_; ⊲ᴴ↑)
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ; emb)
open import OCF.Align.HtFeedClosed using (module At)
open import OCF.Align.StrRel4Walk using (aS)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel12Al using (CP)
import OCF.Align.StrRel12Sem as Sm

module P = At Ωᴴ Lg-Ωᴴ
module S = Sm Ωᴴ Lg-Ωᴴ

ω₀ : A
ω₀ = alim (λ _ → azero)

lω : Lg ω₀
lω = (λ _ → C.self) , (λ _ → tt)

t₀ : H
t₀ = hl (λ _ → hz)
```

## 1 一对 `CP` 分支世界, 两个分支节点

```agda
cpBad : CP {V = ω₀} {V′ = azero} lω tt C.self lω C.self tt
cpBad = (aS C.self tt , ad , refl , refl) , l≤ (λ _ → z≤) , ((λ _ → refl) , (λ _ → tt)) , tt
  where
  ad : Adm ω₀ azero ω₀ azero
  ad = azero , ≤-refl ω₀ , z≤

rL : StH ω₀ (emb ω₀) Ωᴴ
rL = sL C.self hself

rR : StH azero (emb azero) Ωᴴ
rR = sL C.self hself
```

## 2 一对 `TC` 目标, 两边的种类

```agda
TL : P.Tg ω₀ t₀ ω₀
TL = P.tg C.self (hLim C.self hself) lω

TR : P.Tg azero t₀ ω₀
TR = P.tg (C.lim 0 C.self) (hLim C.self hself) lω

tcBad : S.TC lω tt TL TR
tcBad = (aS (C.lim 0 C.self) lω , ad , refl , refl) , ≤-refl ω₀ , ((λ _ → refl) , (λ _ → tt)) , ((λ _ → refl) , (λ _ → tt))
  where
  ad : Adm ω₀ azero ω₀ ω₀
  ad = azero , ≤-refl ω₀ , z≤

-- 节点的坐标位置 (折叠里的 kk r q₀ ll, 树世界即运行世界, ll = hself), 搬到目标世界
kL : emb ω₀ ⊲[ ω₀ ] Ωᴴ
kL = hLim C.self hself

kR : emb azero ⊲[ ω₀ ] Ωᴴ
kR = hLim (C.lim 0 C.self) hself

kL≡ : kL ≡ ⊲ᴴ↑ (P.wm TL) (P.kk rL C.self hself)
kL≡ = refl

kR≡ : kR ≡ ⊲ᴴ↑ (P.wm TR) (P.kk rR C.self hself)
kR≡ = refl

rkBadL : P.rkT kL (P.tm TL) (P.lm TL) ≡ P.rise
rkBadL = refl

rkBadR : P.rkT kR (P.tm TR) (P.lm TR) ≡ P.keep (sl 0 hself)
rkBadR = refl
```
