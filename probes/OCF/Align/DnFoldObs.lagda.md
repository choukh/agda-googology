# 有内容的下降 (七): 第一个障碍的编译陈述, 桥的可入判定的完全性

> 不含记号. 入口 [DnFold](DnFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 种类下标的定义域不同 (类型事实).** 第 1 站读回所在级的下面一级 `Lev X₀` 的种类的第一个分量是**裸的** `H₀` (`levIdx`); 带世界的层 `LvH a (μ′ X₀)` 的种类的第一个分量是 `H₀` 的元素**带它在外层世界 $a$ 里可入的证据** (`lvhIdx`). 数据树过 κH 层的结点也带当前世界的证据 (`sLH-adm`). 所以从 `Lev` 到带世界的层, 保留种类下标就要判定可入; 否定一路证了这与裸判定等价 (`NegDnFoldAdm.Keep.keep→dec`), 外层世界的 `A`-分量为 $\omega$ 时撞分离子 (`keepS₁-sep`). 本路的桥 (`DnFoldBr`) 取有限的外层世界 $(N,N)$, 判定对下标的构造子递归.
> - **§2 有限下标都留下 (定理).** `decH (d + k) (finH₀ k)` 总给出证据 (`decH-fin′`, 即 $k\le N$ 时 `decH N (finH₀ k)` 给出证据), `decA` 同 (`decA-fin′`); 所以桥对有限 $\le N$ 的下标不丢 (丢的只有无穷下标与 $>N$ 的下标, 见 `DnFoldK` 的测试).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldObs where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; StH; sL; κH)
open import OCF.Align.DnFoldIf using (LvH)
open import OCF.Align.DnFoldDc using (finA; finH₀)
open import OCF.Align.DnFoldMu using (μ′)
open import OCF.Align.DnFoldBr using (eqA; decA; eqH; decH)
open import OCF.Align.DnFoldK using (X₀; IsL)
```

## §1 种类下标的定义域

```agda
levIdx : K (Lev X₀) → H₀
levIdx = proj₁

lvhIdx : ∀ (a : Wd₂) → K (LvH a (μ′ X₀)) → Σ H₀ (λ y → Bd S₁ κH y a)
lvhIdx a = proj₁

sLH-adm : ∀ {W k} {g : H₀ → Ht} → StH W k (hΩ κH g) → Σ H₀ (λ y → Bd S₁ κH y W × k ⊲[ W ] g y)
sLH-adm (sL e P) = _ , e , P
```

## §2 有限下标都留下

```agda
eqH-self : ∀ k → IsL (eqH (finH₀ k) k)
eqH-self zero = tt
eqH-self (suc k) with eqH (finH₀ k) k | eqH-self k
... | inj₁ e | _ = tt
... | inj₂ t | ()

decH-fin′ : ∀ d k {w : A} → IsL (decH (d + k) (finH₀ k) {w})
decH-fin′ zero k with eqH (finH₀ k) k | eqH-self k
... | inj₁ e | _ = tt
... | inj₂ t | ()
decH-fin′ (suc d) k {w} with eqH (finH₀ k) (suc (d + k))
... | inj₁ e = tt
... | inj₂ t with decH (d + k) (finH₀ k) {w} | decH-fin′ d k {w}
...   | inj₁ p | _ = tt
...   | inj₂ t′ | ()

eqA-self : ∀ k → IsL (eqA (finA k) k)
eqA-self zero = tt
eqA-self (suc k) with eqA (finA k) k | eqA-self k
... | inj₁ e | _ = tt
... | inj₂ t | ()

decA-fin′ : ∀ d k → IsL (decA (d + k) (finA k))
decA-fin′ zero k with eqA (finA k) k | eqA-self k
... | inj₁ e | _ = tt
... | inj₂ t | ()
decA-fin′ (suc d) k with eqA (finA k) (suc (d + k))
... | inj₁ e = tt
... | inj₂ t with decA (d + k) (finA k) | decA-fin′ d k
...   | inj₁ p | _ = tt
...   | inj₂ t′ | ()
```
