# LHRec (零): 层号 `LH` 在 `CRwBase` 上重写

> 不含记号. 入口 [LHRec](LHRec.lagda.md). 构造一路 LHRec, 否定一路 NegLHRec 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 [CRwBase](CRwBase.lagda.md).
>
> **重写.** 参考 `OCF.Align.LFReTy` (只作参考, 不导入): 层号 `LH` 与它的种类结构 `Lv : LH → KS` 在一个归纳-递归块里一次封闭. 与参考的差: 种类结构用 `CRwBase.KS` (不带 `≤w-rf`, `LgE`, `lgBd`); `lΩ k g` 的种类结构写成 `XL k g` (指标分量 `step (Lv k)`, 第 $c$ 个分量 `Lv (g c)`), 下标类型 `IxL k` $=\top\uplus$ `HB (Lv k)` (自写的数据类型不严格正, 编译器拒绝). 形状同参考, 读法: `lΩ k g` 是共尾度 $\Omega_{k+1}$ 的层号, 坐标是第 $k$ 层的值 `HB (Lv k)`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LHRecTy where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import OCF.Lean.CRwBase

data LH : Set
Lv : LH → KS
-- lΩ k g 的种类结构的分量: 指标分量 (inj₁), 或第 c 个分量 (inj₂ c, c 是第 k 层的值)
FXL : (k : LH) → (HB (Lv k) → LH) → ⊤ ⊎ HB (Lv k) → KS

data LH where
  lz : LH
  ls : LH → LH
  ll : (ℕ → LH) → LH
  lΩ : (k : LH) → (HB (Lv k) → LH) → LH

Lv lz = S⊥
Lv (ls x) = step (Lv x)
Lv (ll f) = sup ℕ (λ n → Lv (f n))
Lv (lΩ k g) = sup (⊤ ⊎ HB (Lv k)) (FXL k g)

FXL k g (inj₁ _) = step (Lv k)
FXL k g (inj₂ c) = Lv (g c)

-- 分量下标的简写
IxL : LH → Set
IxL k = ⊤ ⊎ HB (Lv k)

ixL : ∀ {k} → IxL k
ixL = inj₁ tt
```

