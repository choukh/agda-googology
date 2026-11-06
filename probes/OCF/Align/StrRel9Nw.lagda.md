# 结构关系, 第九轮 (四): 一条统一的 `nw` 规则

> 入口见 [StrRel9](StrRel9.lagda.md). `nwΣᴸ` 的证明只用到两件事: 前段对 `(p, p′)` 在**前段的顶端世界**上对齐, 并且前段底端 (内层树世界) 处有领先量. 把这两件事写成前提, 得到一条语义层面的规则 `snd-nwA`:
>
> $$\mathrm{Al}_{W,W'}(p,p'),\ \ \mathrm{Adm}(V,V';W,W'),\ \ l_V\equiv \texttt{lg⊲}\,p\,l_W,\ \ \mathrm{SemL}\,l_V\,l_{V'}\,x\,x' \ \Rightarrow\ \mathrm{SemL}\,l_W\,l_{W'}\,(\mathrm{nw}\,p\,x)\,(\mathrm{nw}\,p'\,x').$$
>
> 证明: 外层语义给出 $\mathrm{Adm}(W,W';L,L')$, 用它把前段对齐的领先量从 $(W,W')$ 推到运行世界 $(L,L')$ (`Al-map`, `adm-tr`), 再与运行路径的对齐拼接 (`cat`). 两个实例:
>
> - `nwΣ′`: `cv` 的前段 `sum-fst U z` (对齐由 `genᴾ` 在 `adm-self` 上生成), 重新得到 `StrRel9Snd.nwΣᴸ` 的语义.
> - `ctx-nw`: 折叠在 `⨾` 与 `nl` 里给上下文接上的 `nw q x` (`Run` 的 `w ⨾ nw q₀ x`), 前段就是运行路径本身; 三条前提正好是外层 `SemL` 的前提 (`hq`, `ad`, `e`). 所以多层时上下文 (即节点分支收到的坐标) 的关系可以由同一条规则维持.
>
> 它也说明 `StrRel8Neg.¬nwˡ` 缺的是什么: 那里左边有前段 `suc self`, 右边没有, 不存在 `Al` 把左边多出的底部位置配上 (`StrRel7.¬Al-lft`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel9Nw where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.SumOneTree using (D; nw; sum; sum-fst; Lg-sum)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁; toV0)
open import OCF.Align.KNestAdm using (Adm; adm-tr)
open import OCF.Align.KNestSound using (adv-sum)
open import OCF.Align.StrRel4Walk using (Al)
open import OCF.Align.StrRel4Gen using (Al-map; lg-tr; lgsf; cat; adm-self)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; vsᴾ; genᴾ)
open import OCF.Align.StrRel5Nest using (stepA; OA)
open import OCF.Align.StrRel9Snd using (Le; SemL; sndᴸ)
```

## 1 规则

```agda
snd-nwA : ∀ {V V′ W W′} {p : V ⊲ W} {p′ : V′ ⊲ W′} {lW : Lg W} {lW′ : Lg W′} {lV : Lg V} {lV′ : Lg V′}
            {x : D one V} {x′ : D one V′} →
          Al W W′ p lW p′ lW′ → Adm V V′ W W′ → lV ≡ lg⊲ p lW → lV′ ≡ lg⊲ p′ lW′ →
          SemL lV lV′ x x′ → SemL lW lW′ (nw p x) (nw p′ x′)
snd-nwA {p = p} {p′} {lW} {lW′} H adV eV eV′ s lL lL′ l₁ l₁′ le q q′ hq e e′ ad =
  s lL lL′ l₁ l₁′ le (⊲-tr p q) (⊲-tr p′ q′)
    (cat (Al-map (λ a → adm-tr a ad) H) hq e e′)
    (trans eV (trans (cong (lg⊲ p) e) (sym (lg-tr p q lL))))
    (trans eV′ (trans (cong (lg⊲ p′) e′) (sym (lg-tr p′ q′ lL′))))
    (adm-tr adV ad)
```

## 2 实例

```agda
-- cv 的前段
nwΣ′ : ∀ {U U′ Z Z′} {lU : Lg U} {lU′ : Lg U′} {z : D azero Z} {z′ : D azero Z′} {x : D one U} {x′ : D one U′} →
       U ≤ U′ → z ⊑ᴾ z′ → SemL lU lU′ x x′ →
       SemL (Lg-sum U z lU) (Lg-sum U′ z′ lU′) (nw (sum-fst U z) x) (nw (sum-fst U′ z′) x′)
nwΣ′ {U} {U′} {lU = lU} {lU′} {z} {z′} hU hz s =
  snd-nwA (genᴾ hz lU lU′ hU (adm-self (sum U z) (sum U′ z′)))
          (adv-sum z z′ (adm-self U U′) (toV0 z z′ (vsᴾ hz z≤)))
          (sym (lgsf U z lU)) (sym (lgsf U′ z′ lU′)) s

-- 上下文里的 nw: 前段是运行路径, 三条前提就是外层 SemL 的前提
ctx-nw : ∀ {V V′ L L′} {q : V ⊲ L} {q′ : V′ ⊲ L′} {lL : Lg L} {lL′ : Lg L′} {lV : Lg V} {lV′ : Lg V′}
           {x : D one V} {x′ : D one V′} →
         Al L L′ q lL q′ lL′ → lV ≡ lg⊲ q lL → lV′ ≡ lg⊲ q′ lL′ → Adm V V′ L L′ →
         Le lV lV′ x x′ → SemL lL lL′ (nw q x) (nw q′ x′)
ctx-nw hq e e′ ad h = snd-nwA hq ad e e′ (sndᴸ h)
```
