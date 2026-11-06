# 结构关系, 第十一轮: `Ωᴴ` 处同层节点规则收不下 $\Omega_\Omega$ 的自比 (否定)

> 不读记号. 入口 [StrRel11](StrRel11.lagda.md). `Hs.MonoStep Ωᴴ` 在实例 `Ωᴴ` 里比较两次折叠: 左边 `Ωd Ωᴴ {azero}` 在路径 `z⊲ one` 上, 右边 `Ωd Ωᴴ {one}` 在 `self` 上. 若想走 "结构关系 ⇒ 语义" (`StrRel11Le.SemL`) 的路线, 要的第一件是两棵树相关. `Ωd Ωᴴ` 的 `nκ` 在分支世界 $c$ 上是坐标层为 `emb c` 的节点. `κᴸ` 要求一切对齐的分支世界对 $(c, c')$ 上分支相关; 两边底世界是 $0$ 与 $1$ 时, $(1, 2)$ 就是对齐的一对, 坐标层 `emb 1` $\ne$ `emb 2`, 同层的节点规则 `niᴸ` 用不上. 所以 `¬rel-Ω`: 在 `StrRel11Le` 的关系族里两棵树不相关. 范围: 只否定这一族规则 (节点规则要求两边坐标层相同); 不否定别的关系, 不否定 `MonoStep Ωᴴ` 本身.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel11Om where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (z≤; ≤-refl)
open import OCF.Align.HtFeedTree using (Ωd)
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.StrRel4Walk using (aS; aP)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel11Tg Ωᴴ Lg-Ωᴴ using (APair)
open import OCF.Align.StrRel11Le Ωᴴ Lg-Ωᴴ using (Rel; ⨾ᴸ; prᴸ; κᴸ)

one two : A
one = asuc azero
two = asuc one

-- 分支世界对 (1, 2) 对齐: 两边各走一步, 领先量 1
ap12 : APair {V = azero} {V′ = one} tt tt (C.suc C.self) tt (C.suc C.self) tt
ap12 = aP (aS C.self tt) z≤ ad , ad , refl , refl
  where
  ad : Adm azero one one two
  ad = one , ≤-refl one , ≤-refl two

¬rel-Ω : ¬ Rel Ωᴴ {azero} {one} tt tt (Ωd Ωᴴ) (Ωd Ωᴴ)
¬rel-Ω (⨾ᴸ _ (κᴸ h)) with h (C.suc C.self) (C.suc C.self) tt tt ap12
... | ()
¬rel-Ω (prᴸ ())
```

`h … ap12` 的类型是 `Rel Ωᴴ tt tt (ni (sL {c = one} C.self hself) _) (ni (sL {c = two} C.self hself) _)`: 两个节点的坐标层是 `emb one = hs hz` 与 `emb two = hs (hs hz)`, `niᴸ` 的下标合一冲突, 没有别的规则 (左边不是 `n0`, 右边不是 `⨾`, 不是 `nw`), 所以是空的.

## 读法 (判断)

这条否定把 `Ωᴴ` 处 `MonoStep` 的第一个障碍说成了规则的形状: 要一条**跨坐标层**的节点规则, 把坐标层 $k$ 的节点与坐标层 $k'$ 的节点相关, 其中 $(k, k')$ 来自对齐的分支世界对 $(c, c')$ ($k=$ `emb c`, $k'=$ `emb c'`, $c\le c'$ 只是值上的). 它的可靠性在 `hz` 目标上就是 "层 $k$ 的链 $\le$ 层 $k'$ 的链", 在别的目标上还要处理 `rkT` 一边 `keep` 一边 `rise` (层 $t$ 夹在 $k$ 与 $k'$ 之间, 不再被 `StrRel11Rk.rk-agree` 排除, 因为坐标层不同). 这正是 "高度 $k$ 到 $k'$ 的单调" 在实例之内的形式, 对一切可数的 $k\le k'$, 含极限高度 (`MonoL` 未做的那一类). 所以 `Ωᴴ` 处的 `MonoStep` 以 "一切可数高度上的实例内单调" 为前提, 不只是两世界语义的移植.
