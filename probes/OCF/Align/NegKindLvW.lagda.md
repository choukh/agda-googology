# 按级回灌, 否定一路 (三): 同一级的两份拷贝, 没有到该级世界的映射

> 不含记号. 入口 [NegKindLv](NegKindLv.lagda.md). 本篇**不依赖**构造一路的接口 `KindLvIf` (接口定稿之前写的部分). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> "按级回灌" 的一种写法: 对级为 $y$ 的种类, 先把折叠的世界投到第 $y$ 级的世界 (`Wd (Lev (hs y))`, 新种类的坐标就是 `HB (Lev y)`), 在那里读回, 再写回. 层号对角所在的 `KΛc = sup ℕ Kc` 里, 每一站都把上一站整个作为分量 `inj₁ tt` 嵌进来 (`LvKtIf.nxt`), 所以第 $s$ 站的每个种类在第 $s+1, s+2, \dots$ 站都有拷贝, 坐标类型相同, 界在世界的不同分量里, 互不相干. 本篇 (同 `HtTowerNStage.no-wmatch`, `NegDnFoldCopy.no-wmatch₀`, 落在 `KΛc` 上):
>
> - **`no-wmatchΛH` (定理).** `Lev (hs hz) = step S₀` 的新种类 (坐标 `H₀`, 级 $0$) 在 `KΛc` 里有两份拷贝 `κ1H` (第 1 站的分量 `hs hz`) 与 `κ2H` (第 2 站经 `inj₁ tt` 嵌入的第 1 站). 没有世界映射 `wm : Wd KΛc → Wd (step S₀)`, 使 `κ2H` 的界送进新种类的界, 又把新种类的界送回 `κ1H` 的界. 两个前提各自可满足 (`sat1H`, `sat2H`).
> - **`no-wmatchΛA` (定理).** 底种类 (坐标 `A`) 的两份拷贝 `κ1A = (1 , (inj₁ tt , tt))` 与 `κ2A = (2 , (inj₁ tt , (inj₁ tt , tt)))` 同样. 前提实例 `sat1A`, `sat2A`.
>
> **只否定什么.** 只否定 "一个从 `KΛc` (或经第一分量从 `step KΛc`) 的世界到某一级的世界的映射, 同时在两个方向上保同一级的两份拷贝的界". **不否定**: 不经世界映射的按级回灌 (读回与写入都在折叠自己的世界 `Wd (step T)` 里做, 如 `GenFoldIf` 的做法); 反方向 (从第 $y$ 级的世界写进 `KΛc` 的世界, 每份拷贝取同一个界, 判断: 可写, 但那是 "一起升", 见 [NegKindLvUpd](NegKindLvUpd.lagda.md)); 只保一份拷贝的映射 (`sat*`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKindLvW where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNStage using (dWLev)
open import OCF.Align.LvKtIf using (Kc; KΛc)
open import OCF.Align.GenFoldIf using (K₁; w₀)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.NegGenFoldUpd using (z₁)
open import OCF.Align.NegKindLvUpd using (one⊀z)
```

## §1 两份拷贝

```agda
-- 第 1 站: 分量 hs hz 的新种类
κ1H : K KΛc
κ1H = 1 , (inj₂ (hs hz) , inj₂ tt)

-- 第 2 站: 经 inj₁ tt 嵌入的第 1 站里同一个种类
κ2H : K KΛc
κ2H = 2 , (inj₁ tt , (inj₂ (hs hz) , inj₂ tt))

E-κ1H : E KΛc κ1H ≡ H₀
E-κ1H = refl

E-κ2H : E KΛc κ2H ≡ H₀
E-κ2H = refl

-- 底种类的两份拷贝
κ1A κ2A : K KΛc
κ1A = 1 , (inj₁ tt , tt)
κ2A = 2 , (inj₁ tt , (inj₁ tt , tt))
```

## §2 反例世界

第 1 站的世界取基世界 `z₁` (分量 `hs hz` 的新种类的界是 $0$); 第 2 站的分量 `inj₁ tt` (第 1 站的拷贝) 里, 分量 `hs hz` 的新种类的界取 $1$, 底分量的界取 $1$.

```agda
w1⋆ : Wd K₁
w1⋆ (inj₁ tt) = asuc azero
w1⋆ (inj₂ (hs hz)) = azero , hs hz
w1⋆ (inj₂ c) = dWLev c

w⋆ : Wd KΛc
w⋆ zero = azero
w⋆ (suc zero) = z₁
w⋆ (suc (suc zero)) = λ { (inj₁ tt) → w1⋆ ; (inj₂ c) → dWLev c }
w⋆ (suc (suc (suc s))) = w₀ (genKc (suc (suc (suc s))))
```

## §3 没有同时保两份拷贝的世界映射

```agda
no-wmatchΛH : ∀ (wm : Wd KΛc → Wd (step S₀)) →
  (∀ {c w} → Bd KΛc κ2H c w → Bd (step S₀) (inj₂ tt) c (wm w)) →
  (∀ {c w} → Bd (step S₀) (inj₂ tt) c (wm w) → Bd KΛc κ1H c w) → ⊥
no-wmatchΛH wm h2 h1 = one⊀z {S₀} (h1 {hs hz} {w⋆} (h2 {hs hz} {w⋆} hself))

no-wmatchΛA : ∀ (wm : Wd KΛc → Wd S₀) →
  (∀ {c w} → Bd KΛc κ2A c w → Bd S₀ tt c (wm w)) →
  (∀ {c w} → Bd S₀ tt c (wm w) → Bd KΛc κ1A c w) → ⊥
no-wmatchΛA wm h2 h1 with h1 {asuc azero} {w⋆} (h2 {asuc azero} {w⋆} C.self)
... | ()
```

`step KΛc` (最终坍缩的层所在的种类结构) 的旧种类就是 `KΛc` 的种类, 世界的第一分量就是 `KΛc` 的世界, 所以同一条对 `step KΛc` 成立:

```agda
no-wmatchΛ⁺H : ∀ (wm : Wd (step KΛc) → Wd (step S₀)) →
  (∀ {c w} → Bd (step KΛc) (inj₁ κ2H) c w → Bd (step S₀) (inj₂ tt) c (wm w)) →
  (∀ {c w} → Bd (step S₀) (inj₂ tt) c (wm w) → Bd (step KΛc) (inj₁ κ1H) c w) → ⊥
no-wmatchΛ⁺H wm h2 h1 = no-wmatchΛH (λ w → wm (w , hz)) h2 h1
```

## §4 前提各自可满足

```agda
sat1H : Σ (Wd KΛc → Wd (step S₀)) (λ wm →
  (∀ {c w} → Bd KΛc κ1H c w → Bd (step S₀) (inj₂ tt) c (wm w)) ×
  (∀ {c w} → Bd (step S₀) (inj₂ tt) c (wm w) → Bd KΛc κ1H c w))
sat1H = (λ w → w 1 (inj₂ (hs hz))) , (λ e → e) , (λ e → e)

sat2H : Σ (Wd KΛc → Wd (step S₀)) (λ wm →
  (∀ {c w} → Bd KΛc κ2H c w → Bd (step S₀) (inj₂ tt) c (wm w)) ×
  (∀ {c w} → Bd (step S₀) (inj₂ tt) c (wm w) → Bd KΛc κ2H c w))
sat2H = (λ w → w 2 (inj₁ tt) (inj₂ (hs hz))) , (λ e → e) , (λ e → e)

sat1A : Σ (Wd KΛc → Wd S₀) (λ wm →
  (∀ {c w} → Bd KΛc κ1A c w → Bd S₀ tt c (wm w)) × (∀ {c w} → Bd S₀ tt c (wm w) → Bd KΛc κ1A c w))
sat1A = (λ w → w 1 (inj₁ tt)) , (λ e → e) , (λ e → e)

sat2A : Σ (Wd KΛc → Wd S₀) (λ wm →
  (∀ {c w} → Bd KΛc κ2A c w → Bd S₀ tt c (wm w)) × (∀ {c w} → Bd S₀ tt c (wm w) → Bd KΛc κ2A c w))
sat2A = (λ w → w 2 (inj₁ tt) (inj₁ tt)) , (λ e → e) , (λ e → e)
```

## §5 结论 (按档)

- **[定理, 否定]** **`no-wmatchΛH`** (坐标是高度的种类的两份拷贝), **`no-wmatchΛ⁺H`** (`step KΛc`), **`no-wmatchΛA`** (底拷贝).
- **[定理, 前提实例]** `sat1H`, `sat2H`, `sat1A`, `sat2A`: 只保一份拷贝的映射存在.
- **[判断]** 对 "按级回灌" 的含义: 读回若要在 "第 $y$ 级的世界" 里做, 就得先选定一份拷贝 (例如按种类携带的路径), 别的拷贝的界看不见; 它与 "每个种类按自己的级" 相容 (每个种类本来就带着自己的分量路径), 但同一级的不同拷贝回灌各自独立, 不能由一个级世界统一给出.
