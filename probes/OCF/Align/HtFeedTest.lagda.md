# 高度是树: 有限测试

> 入口 [HtFeed](HtFeed.lagda.md). **有限测试, 不是证明.** 比较器 `same d w` (`CumUpAcceptF`): 深度 $d$, 宽度 $w$, 只读形状. 盲区: 不读第 $w$ 项以后, 不读深度 $d$ 以下, 不读值.
>
> 看的是改写是否忠实: 在三族共有的那一站 ($\psi_0(\Omega_\Omega)$), 新折叠与 `SumOne`, `SumHt` 的输出到深度 6 形状相同; 新折叠自己的相邻两站在深度 4 分开 (对照: 深度 3 不分开, 比较器在浅处没有分辨力).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtFeedTest where

open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumUpAcceptF using (same)
import OCF.Align.SumOneClosed as O
import OCF.Align.SumHtClosed as SH
open import OCF.Align.HtFeedClosed
open import OCF.Align.HtFeedHt using (emb; Lg-Ωᴴ)
import OCF.Align.HtFeedGrow as Gr

module E = Gr.ΩSt emb Lg-Ωᴴ

-- 同一个 ψ₀(Ω_Ω): 高度 Ω 的 TΛ 对 SumOne 的 T₀ (输入字面同形)
a6 : same 6 2 (ord T-Ω) (O.ord O.T₀) ≡ true
a6 = refl

-- 同一个 ψ₀(Ω_Ω) 的站: ΩSt emb 的 Xκ 对 SumHt 的 T 1 0 (积木同形)
b6 : same 6 2 (ord (E.Tψ E.Xκ)) (SH.ord (SH.T 1 0)) ≡ true
b6 = refl

-- 前两段对 SumHt 的 T 0 2
c4 : same 4 2 (ord (E.Tψ (E.Xn 2))) (SH.ord (SH.T 0 2)) ≡ true
c4 = refl

-- 对照: 新折叠的相邻站, 深度 3 不分开, 深度 4 分开
d3 : same 3 2 (ord T-Ω+1) (ord T-Ω) ≡ true
d3 = refl
d4 : same 4 2 (ord T-Ω+1) (ord T-Ω) ≡ false
d4 = refl
e4 : same 4 2 (ord T-Ω·2) (ord T-Ω+1) ≡ false
e4 = refl
```
