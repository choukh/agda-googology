# 有内容的下降, 否定一路 (四): 第 1 站的读回级里, 同一种类的两份拷贝各有各的界

> 不含记号. 入口 [NegDnFold](NegDnFold.lagda.md). 对着接口 [DnFoldIf](DnFoldIf.lagda.md) ("接口定稿 2026-11-05 16:13 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 嫌疑 (i) 的一般形: `HtTowerNStage.no-wmatch` (同一种类在并里的两份拷贝读世界的不同分量). 这里把它落在接口自己的对象上: 第 1 站读回所在的级 `Lev X₀` (`FaithTower` 在 $s=0$ 说的那个 `T`, `X₀ = Shape.X dn dnL 0` 与下降无关, 定义相等于 `KcFoldTower.One.X₁`) 是对坐标 $y$ 的并. 坐标 $y=0$ 那一支是 `S₁`, 坐标 $y=1$ 那一支是 `step S₁`; 两支里都有 `Ht` 的底种类 κA 的拷贝 (`k1`, `k2`, 坐标都是 `A`).
>
> - **`no-wmatch₀` (定理).** 没有世界映射 `Wd (Lev X₀) → Wd₂` 同时把 `k1` 的界送进 `Ht` 的 κA 的界, 又把 κA 的界送回 `k2` 的界. 反例世界 `w⋆`: `k1` 的界 $1$, `k2` 的界 $0$, 坐标取 $1$.
> - **两半各自可满足 (`sat1`, `sat2`)**: 只管一份拷贝时, 取那一支的分量.
>
> **只否定什么.** 只否定 "把读回级的世界折成 `Ht` 的一个世界, 底种类的两份拷贝的界同时保持" (一个方向保 `k1`, 另一个方向保 `k2`). 这是逐种类翻译并搬运合法性 (`LvRdEmb.Emb` 的 `π`, `bd→`, `bd←`) 在第 1 站会要的东西. **不否定** 接口的 `DnEv`: 接口明写 "数据树没有合法性, 翻译可以是任何函数", 翻译不搬世界, 所以不要这种映射 (判断). 也不否定反方向 `Wd₂ → Wd (Lev X₀)` 的对角世界 (每份拷贝取同一个界, 判断: 可写).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegDnFoldCopy where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂)
open import OCF.Align.LvKtCode using (w0; cdLev)
open import OCF.Align.LvKtIf
open import OCF.Align.KcFoldIf
open import OCF.Align.KcFoldTower using (module Shape; module One)
open import OCF.Align.DnFoldIf
```

## §1 第 1 站读回的级

```agda
X₀ : HB (Kc 1)
X₀ = One.X₁ (λ s b lb → (λ _ → hz) , (λ _ _ → tt)) (λ b lb → (λ _ → hz) , (λ _ _ → tt))

-- 与任何下降的塔的 Shape.X 0 定义相等
X₀-is : ∀ dn dnL → Shape.X dn dnL 0 ≡ X₀
X₀-is dn dnL = refl

T₀ : KS
T₀ = Lev X₀

-- 两份底种类的拷贝: 坐标 0 那一支 (S₁) 与坐标 1 那一支 (step S₁)
k1 k2 : K T₀
k1 = hz , inj₁ tt
k2 = hs hz , inj₁ (inj₁ tt)

E-k1 : E T₀ k1 ≡ A
E-k1 = refl

E-k2 : E T₀ k2 ≡ A
E-k2 = refl
```

## §2 两份拷贝的界不能同时折进 `Ht` 的一个世界

```agda
w⋆ : Wd T₀
w⋆ hz = asuc azero , hz
w⋆ (hs hz) = (azero , hz) , hz
w⋆ y = w0 (cdLev (hs hz ⊞ injL (hs hz) (up {S₀} y)))

no-wmatch₀ : ∀ (wm : Wd T₀ → Wd₂) →
  (∀ {c w} → Bd T₀ k1 c w → c ⊲ proj₁ (wm w)) →
  (∀ {c w} → c ⊲ proj₁ (wm w) → Bd T₀ k2 c w) → ⊥
no-wmatch₀ wm h1 h2 with h2 {asuc azero} {w⋆} (h1 {asuc azero} {w⋆} C.self)
... | ()

-- 两半各自可满足
sat1 : Σ (Wd T₀ → Wd₂) (λ wm → (∀ {c w} → Bd T₀ k1 c w → c ⊲ proj₁ (wm w)) × (∀ {c w} → c ⊲ proj₁ (wm w) → Bd T₀ k1 c w))
sat1 = (λ w → w hz) , (λ e → e) , (λ e → e)

sat2 : Σ (Wd T₀ → Wd₂) (λ wm → (∀ {c w} → Bd T₀ k2 c w → c ⊲ proj₁ (wm w)) × (∀ {c w} → c ⊲ proj₁ (wm w) → Bd T₀ k2 c w))
sat2 = (λ w → proj₁ (w (hs hz))) , (λ e → e) , (λ e → e)
```

## §3 结论 (按档)

- **[定理]** `X₀-is` (第 1 站读回的级与下降无关), `E-k1`, `E-k2`.
- **[定理]** **`no-wmatch₀`**; `sat1`, `sat2` (两半各自可满足).
- **[判断]** 接口的 `DnEv` (翻译是任意函数, 数据树没有合法性) 不需要这种世界映射, 所以嫌疑 (i) 不落在接口上; 它落在 "逐种类翻译并搬运合法性" 的写法上, 那种写法在第 1 站就要两份拷贝同时保界. 接口的 `EvSys` 里也没有比较一切种类结构的律 (`lgEv` 只说单个输出合法).
