# 头按自己的级读回, 否定一路 (四): 嵌入 `emb2` 的像

> 不含记号. 入口 [NegLeanLv](NegLeanLv.lagda.md). 只读导入构造一路的 [LeanLvEmb](LeanLvEmb.lagda.md) (22:13 版), 不改它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路的计划: 头 $n\ge3$ 用头 2 的级层 $S_1$ (层号 `st 2`), 读回经嵌入 `emb2 (n-2) : Emb (Lv (st 2)) (Lv (st n))` 放进头 $n$ 的坐标. 沿嵌入的读回 (`nbJ`) 输出的 $\Omega$-结点的种类都在 `j` 的像里. 本篇问: 这个像漏掉了 `Lv (st 3)` 的哪些种类.
>
> **结果 (定理).** `kTop3 : K (Lv (st 3))` 的坐标字面就是 `HB (Lv (st 2))` (**`kTop3-co`**, `refl`): 它是 `Lv (st 3)` 里级为 `st 2` 的种类 (在 `st 3` 的分支 $1$, 再分支 $1$ 处的新种类; `kTop3-lv`). **`miss-top`**: 对一切 $\kappa$ : `K (Lv (st 2))`, `j (emb2 1) κ ≢ kTop3`. 更一般地 **`img-left`**: `j (emb2 1)` 的像里每个种类, 若在 `st 3` 的分支 $c=0$ 或 $c=$ 后继处, 都落在那个分支的左分量 (`inj₁ tt`, 即 `step (Lv _)` 那一份). 由 `NegLeanLvPre.lvK-not-self`, `Lv (st 2)` 自己没有级为 `st 2` 的种类.
>
> **读法 [判断].** 头 3 的读回若是 "沿 $S_1\sim$ `st 2` 读进 `Lv (st 2)`, 再经 `emb2 1`", 它的输出里没有 `kTop3` (以及 `img-left` 排除的那些右分量里的种类) 的 $\Omega$-结点. 这是 `NegLeanFbInst.rdX-one-kind` 高一层的版本: 头 3 的界只按 `Lv (st 2)` 的那一份拷贝里的种类增长, 不含坐标为 `HB (Lv (st 2))` 的种类. 要把这条读法变成定理, 要对构造一路的读回写 "输出的种类都在像里" 的不变式 (见 [NegLeanLvInst](NegLeanLvInst.lagda.md), 若它已写好).
>
> **只否定什么.** 只说 `emb2 1` 的像不含 `kTop3` (以及 `img-left`). 不否定嵌入, 不否定读回的合法或停机, 不说值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegLeanLvEmb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanLvIf
open import OCF.Lean.LeanFbSt using (st)
open import OCF.Lean.LeanLvEmb using (emb2)
open import OCF.Lean.NegLeanLvPre using (lvK)
```

## §1 `Lv (st 3)` 里级为 `st 2` 的种类

`st 3 = lΩ lz g₃`; 分支 $c=1$ 是 `lΩ (ls lz) h`, 它的分支 $e=1$ 是 `ls (st 2)`, 新种类的坐标是 `HB (Lv (st 2))`.

```agda
kTop3 : K (Lv (st 3))
kTop3 = inj₂ (hs hz) , (inj₂ (hs hz) , inj₂ tt)

kTop3-co : E (Lv (st 3)) kTop3 ≡ HB (Lv (st 2))
kTop3-co = refl

kTop3-lv : lvK (st 3) kTop3 ≡ st 2
kTop3-lv = refl
```

## §2 像里没有它

`obs`: 种类是否在 `st 3` 的分支 $0$ 或后继分支的**右**分量里.

```agda
obs : K (Lv (st 3)) → Bool
obs (inj₁ _ , _) = false
obs (inj₂ hz , (inj₁ _ , _)) = false
obs (inj₂ hz , (inj₂ _ , _)) = true
obs (inj₂ (hs c) , (inj₁ _ , _)) = false
obs (inj₂ (hs c) , (inj₂ _ , _)) = true
obs (inj₂ (hl f) , _) = false
obs (inj₂ (hΩ (() , _) g) , _)

E1 : Emb (Lv (st 2)) (Lv (st 3))
E1 = emb2 1

img-left : ∀ κ → obs (j E1 κ) ≡ false
img-left (inj₁ _ , κ) = refl
img-left (inj₂ hz , κ) = refl
img-left (inj₂ (hs c) , κ) = refl
img-left (inj₂ (hl f) , κ) = refl
img-left (inj₂ (hΩ (() , _) g) , κ)

miss-top : ∀ κ → ¬ (j E1 κ ≡ kTop3)
miss-top κ e = f≢t (trans (sym (img-left κ)) (cong obs e))
  where
  f≢t : ¬ (false ≡ true)
  f≢t ()
```

## §3 结论 (按档)

- **[定理]** `kTop3-co`, `kTop3-lv` (`refl`); **`img-left`**, **`miss-top`** (`emb2 1` 的像不含 `kTop3`, 也不含 `st 3` 分支 $0$ 与后继分支的右分量里的任何种类).
- **[判断]** 沿 `emb2` 的读回输出的种类都在像里 (要对实例写不变式); 若如此, 头 3 的界里没有 `kTop3` 的 $\Omega$-结点.
