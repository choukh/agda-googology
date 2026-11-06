# LHRec (二): 层号的算术, $\Omega_x$, 塔 `twL`, $\Lambda$ (都在 `LH` 上)

> 不含记号. 入口 [LHRec](LHRec.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [LHRecTy](LHRecTy.lagda.md).
>
> **重写.** 参考 `OCF.Align.LFReTy` (`lvl`, `node`, `upL`) 与 `LFReTower` (`Ω̂`, `tw`, `Λ`), 只作参考, 不导入. 与参考的差: 参考把层号读成高度 `HB SL` 再做 $\Omega$; 这里**直接在 `LH` 上**做: 层号加法 `⊕L` (右边逐构造子, `lΩ k g` 的指标层 $k$ 不动), `ΩL x` 是层号 $\Omega_x$ (后继处 $\Omega_{x+1}=\sup_{c}(\Omega_x\oplus c)$, $c$ 过第 $x$ 层的值, 经 `upL` 读成层号; 两种极限处逐点). `twL 0 = 0`, `twL (n+1) = ΩL (twL n)`, `ΛL = ll twL`. 这里没有层号的合法性 (那要层号上带世界的第一位置; 本路的证书不用它).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LHRecLay where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
```

## §1 读回层, 结点, 值读成层号

`lvl k κ`: 第 $k$ 层的种类 $\kappa$ 的坐标所在的层. `node k κ h`: 以 $\kappa$ 为共尾度的层号结点 (指标层是 `lvl k κ`). `upL k c`: 第 $k$ 层的值 $c$ 读成层号. 到底的那一步类型字面对上.

```agda
lvl : (k : LH) → K (Lv k) → LH
lvl lz ()
lvl (ls x) (inj₁ κ) = lvl x κ
lvl (ls x) (inj₂ _) = x
lvl (ll f) (n , κ) = lvl (f n) κ
lvl (lΩ k g) (inj₁ _ , inj₁ κ) = lvl k κ
lvl (lΩ k g) (inj₁ _ , inj₂ _) = k
lvl (lΩ k g) (inj₂ c , κ) = lvl (g c) κ

node : (k : LH) (κ : K (Lv k)) → (E (Lv k) κ → LH) → LH
node lz () h
node (ls x) (inj₁ κ) h = node x κ h
node (ls x) (inj₂ _) h = lΩ x h
node (ll f) (n , κ) h = node (f n) κ h
node (lΩ k g) (inj₁ _ , inj₁ κ) h = node k κ h
node (lΩ k g) (inj₁ _ , inj₂ _) h = lΩ k h
node (lΩ k g) (inj₂ c , κ) h = node (g c) κ h

upL : (k : LH) → HB (Lv k) → LH
upL k hz = lz
upL k (hs c) = ls (upL k c)
upL k (hl f) = ll (λ n → upL k (f n))
upL k (hΩ κ h) = node k κ (λ c → upL k (h c))
```

## §2 加法, $\Omega$, 塔, $\Lambda$

```agda
infixl 6 _⊕L_
_⊕L_ : LH → LH → LH
x ⊕L lz = x
x ⊕L ls y = ls (x ⊕L y)
x ⊕L ll f = ll (λ n → x ⊕L f n)
x ⊕L lΩ k g = lΩ k (λ c → x ⊕L g c)

ΩL : LH → LH
ΩL lz = ls lz
ΩL (ls x) = lΩ x (λ c → ΩL x ⊕L upL x c)
ΩL (ll f) = ll (λ n → ΩL (f n))
ΩL (lΩ k g) = lΩ k (λ c → ΩL (g c))

twL : ℕ → LH
twL zero = lz
twL (suc n) = ΩL (twL n)

ΛL : LH
ΛL = ll twL
```

**不动点的形状.** `ΩL ΛL` 字面是 `ll (twL ∘ suc)` (同 `LFReTower.fix-form`).

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

fixL : ΩL ΛL ≡ ll (λ n → twL (suc n))
fixL = refl
```
