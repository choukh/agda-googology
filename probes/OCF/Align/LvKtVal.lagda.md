# 层号换类型 (三): 值的结论, 两站与一切站一致, 前提可满足, 接口的盲

> 不含记号. 入口 [LvKt](LvKt.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 交付的 (b) 部分. 只有输入一侧的定理与条件定理; **没有无条件的值定理, 没有序数值验收.**
>
> - **[定理] 两站与一切站一致** (`two-B1`, `two-B2`, `two-H0`, `two-H1`): 回灌整个读回时, `Tower` 的第 1, 2 站层号与第 0, 1 站输出就是 `Two` 逐站写的那些 (`refl`).
> - **[定理] 输入一侧 (对任一塔)**: `B-fst` (旧层号嵌入后是新层号的第一位置), `Bᴧ-fst` (层号对角相邻项), `cum-strict` (输出对角严格高于每个部分和), `lim-fst` (加极限站不降).
> - **[条件定理] 值一侧**: 前提 `FstMono T⁺` / `FstMono< T⁺` (同 `LvTopVal`, 未证也未否定): `val-cum`, `val-cum<`, `val-lim`.
> - **[定理, 盲] 接口不决定值; 前提可满足**: `foldTrivK K ck : FoldAllK K ck` 对一切种类结构; 条件版 `FullK` 用它实例化得一个合法闭项 (`Ttriv`, `Lg-Ttriv`), 各站输出都是 $0$ (`triv-Hs`), 读回都是 $0$, 所以层号是 $b_0$ 的逐站嵌入 (`triv-B1`). 前提可满足, 不说明值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKtVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; asuc; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.TpMonoIf using (_⊑_; _⊏_; FstMono; FstMono<; plim; T⁺)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.LvKtCode
open import OCF.Align.LvKtIf
open import OCF.Align.LvKtTower
```

## §1 两站与一切站一致

回灌整个读回 (`φ = id`). `Two` 的第 1 站覆盖证据取塔的覆盖步.

```agda
module Agree (Cov : ∀ s → HB (Kc s) → Set) (F : ∀ s → FoldAtK (Kc s) (ckc s) (Cov s))
             (b₀ : HB S₀) (lb₀ : LgB b₀) (cov0 : Cov 0 b₀)
             (covS : ∀ s b x → Cov s b → Cov (suc s) (emb b ⊞ injL b x)) where
  module T = Tower Cov F (λ _ _ x → x) (λ _ _ _ l → l) b₀ lb₀ cov0 covS
  module W = Two (Cov 0) (F 0) (Cov 1) (F 1) b₀ lb₀ cov0 (λ r → covS 0 b₀ r cov0)

  two-B1 : T.B 1 ≡ W.B1
  two-B1 = refl

  two-B2 : T.B 2 ≡ W.B2
  two-B2 = refl

  two-H0 : T.Hs 0 ≡ W.H0
  two-H0 = refl

  two-H1 : T.Hs 1 ≡ W.H1
  two-H1 = refl
```

## §2 输入一侧与条件的值 (对任一塔)

```agda
module ValT (Cov : ∀ s → HB (Kc s) → Set) (F : ∀ s → FoldAtK (Kc s) (ckc s) (Cov s))
            (φ : ∀ s (b : HB (Kc s)) → HB (Lev b) → HB (Lev b)) (lφ : ∀ s b x → LgB x → LgB (φ s b x))
            (b₀ : HB S₀) (lb₀ : LgB b₀) (cov0 : Cov 0 b₀)
            (covS : ∀ s b x → Cov s b → Cov (suc s) (emb b ⊞ injL b (φ s b x))) where
  open Tower Cov F φ lφ b₀ lb₀ cov0 covS

  Bᴧ-fst : ∀ s {w} → Bᴧ s ⊲[ w ] Bᴧ (suc s)
  Bᴧ-fst s = ⊞-fst (Bᴧ s) (ιΛ (suc s) (inc s))

  cum-strict : ∀ k → cum k ⊏ Λ∞
  cum-strict k = plim (suc k) (⊞-fst (cum k) (Hs (suc k)))

  val-cum : FstMono T⁺ → ∀ k → T⁺ (cum k) (lcum k) ≤ TΛ∞
  val-cum fm k = fm (cum k) (lcum k) Λ∞ lΛ∞ (hlim (suc k) (⊞-fst (cum k) (Hs (suc k))))

  val-cum< : FstMono< T⁺ → ∀ k → asuc (T⁺ (cum k) (lcum k)) ≤ TΛ∞
  val-cum< fm k = fm (cum k) (lcum k) Λ∞ lΛ∞ (cum-strict k)

  module ValL (CovL : HB KΛc → Set) (FL : FoldAtK KΛc ckΛ CovL) (covL : CovL ΛB) where
    open Lim CovL FL covL

    lim-fst : Λ∞ ⊑ Λ∞ω
    lim-fst = ⊞-fst Λ∞ Hω

    val-lim : FstMono T⁺ → TΛ∞ ≤ TΛ∞ω
    val-lim fm = fm Λ∞ lΛ∞ Λ∞ω lΛ∞ω lim-fst
```

## §3 盲, 前提可满足

```agda
foldTrivK : (K : KS) (ck : CdK K) → FoldAllK K ck
foldTrivK K ck = record
  { rt = λ la lb c cv w lw → hz ; lrt = λ la lb c cv w lw → tt
  ; H = λ la lb c cv w lw → hz ; lgH = λ la lb c cv w lw → tt }

FAtriv : FoldTower
FAtriv s = foldTrivK (Kc s) (ckc s)

FLtriv : FoldLimK
FLtriv = foldTrivK KΛc ckΛ

module FT = FullK FAtriv FLtriv hz tt

-- 条件版在可满足的前提下的闭项 (前提的实例; 不说明值)
Ttriv : A
Ttriv = FT.TΛ∞ω

Lg-Ttriv : Lg Ttriv
Lg-Ttriv = FT.Lg-TΛ∞ω

triv-Hs : ∀ s → FT.Hs s ≡ hz
triv-Hs s = refl

triv-B1 : FT.B 1 ≡ emb hz ⊞ injL hz hz
triv-B1 = refl
```
