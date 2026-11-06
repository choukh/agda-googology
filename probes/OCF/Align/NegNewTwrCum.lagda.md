# 新塔, 否定一路 (一): 部分和对角的字面第一位置

> 不含记号. 入口 [NegNewTwr](NegNewTwr.lagda.md). 对着接口 [NewTwrIf](NewTwrIf.lagda.md) ("接口定稿 2026-11-05 17:39 (首次编译通过)", 变更记录: 无). 本篇是对一切并 `sup ℕ F` 的一般引理, 不导入接口; 用到它的定理在 [NegNewTwrShape](NegNewTwrShape.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> 接口文件 "塔的形状" 一段规定层号对角是部分和 $\mathrm{B}^\Lambda_{s+1}=\mathrm{B}^\Lambda_s\boxplus\iota_{s+1}(\cdots)$ (照 `LvKtTower.Tower.Bᴧ`, 为了不撞 `NegLvKtTrap.diag-trap`). `NegLvKtTrap.stage-not-below` 在一个**玩具**增量 (`δ`) 上说: 第 $s+1$ 站的增量不是对角的字面第一位置. 本篇把它推广到**任意**增量:
>
> - **`split⊞` (定理).** $a\boxplus b$ 的第一位置要么是 $a$ 的第一位置, 要么字面地等于 $a\boxplus b'$, $b'$ 是 $b$ 的第一位置.
> - **`CumTrap.Bad.not-below` (定理, 否定).** 部分和 `cum` 的起点纯于第 0 个分量, 第 $n$ 个增量纯于第 $n+1$ 个分量. 若第 $m$ 个增量含 $\Omega$-结点, 则对一切 $j>m+1$, 纯于第 $j$ 个分量且含 $\Omega$-结点的高度**不是** $\mathrm{hl}\,\mathrm{cum}$ 的字面第一位置, 也不是任何部分和的第一位置 (`below`). 证明只看构造子 (`Trap.two-pure`, `pure⊲`), 不判定任何高度.
>
> **只否定什么.** 只否定字面第一位置 (`⊲[ w ]`). 不否定值的比较 ("对角的值不低于第 $j$ 站的增量" 可以成立, 那是值的定理); 不否定 $j\le m+1$ 的站 (第 $m+1$ 站的增量可以是第一位置, 对照 `NegLvKtTrap.stage0-below`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegNewTwrCum where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _<?_)
open import Data.Nat.Properties using (≤-refl; <-irrefl; ≤-trans; m≤n⇒m<n∨m≡n; ≮⇒≥)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Align.HtTowerTy
open import OCF.Align.NegLvKtTrap using (OmFree; module Trap)
```

## §1 `⊞` 的第一位置

```agda
split⊞ : ∀ {S : KS} {w} (a b : HB S) {x} → x ⊲[ w ] a ⊞ b →
  (x ⊲[ w ] a) ⊎ Σ (HB S) (λ b′ → (b′ ⊲[ w ] b) × (x ≡ a ⊞ b′))
split⊞ a hz p = inj₁ p
split⊞ a (hs b) hself = inj₂ (hs b , hself , refl)
split⊞ a (hs b) (hsuc p) with split⊞ a b p
... | inj₁ q = inj₁ q
... | inj₂ (b′ , q , e) = inj₂ (b′ , hsuc q , e)
split⊞ a (hl f) hself = inj₂ (hl f , hself , refl)
split⊞ a (hl f) (hlim n p) with split⊞ a (f n) p
... | inj₁ q = inj₁ q
... | inj₂ (b′ , q , e) = inj₂ (b′ , hlim n q , e)
split⊞ a (hΩ κ g) hself = inj₂ (hΩ κ g , hself , refl)
split⊞ a (hΩ κ g) (hLim e p) with split⊞ a (g _) p
... | inj₁ q = inj₁ q
... | inj₂ (b′ , q , eq) = inj₂ (b′ , hLim e q , eq)

free⊞ : ∀ {S : KS} (a b : HB S) → OmFree a → OmFree b → OmFree (a ⊞ b)
free⊞ a hz fa fb = fa
free⊞ a (hs b) fa fb = free⊞ a b fa fb
free⊞ a (hl f) fa fb = λ n → free⊞ a (f n) fa (fb n)
free⊞ a (hΩ κ g) fa ()
```

## §2 部分和对角: 后站的含 $\Omega$-结点的纯高度不是第一位置

```agda
module CumTrap (F : ℕ → KS) where
  open Trap ℕ F

  pureR : ∀ j (a b : HB (sup ℕ F)) → Pure j (a ⊞ b) → Pure j b
  pureR j a hz h = tt
  pureR j a (hs b) h = pureR j a b h
  pureR j a (hl f) h = λ n → pureR j a (f n) (h n)
  pureR j a (hΩ κ g) (e , h) = e , (λ c → pureR j a (g c) (h c))

  pureL : ∀ j (a b : HB (sup ℕ F)) {w : Wd (sup ℕ F)} → Pure j (a ⊞ b) → Pure j a
  pureL j a b {w} h = pure⊲ {w = w} (⊞-fst a b) h

  module Diag (c₀ : HB (sup ℕ F)) (δ : ℕ → HB (sup ℕ F)) where
    cum : ℕ → HB (sup ℕ F)
    cum zero = c₀
    cum (suc n) = cum n ⊞ δ n

    cum-mono : ∀ {w} {k} n → k ≤ n → cum k ⊲[ w ] cum n
    cum-mono zero z≤n = hself
    cum-mono (suc n) q with m≤n⇒m<n∨m≡n q
    ... | inj₂ refl = hself
    ... | inj₁ (s≤s q′) = ⊲ᴮ-tr (cum-mono n q′) (⊞-fst (cum n) (δ n))

    -- 起点纯于 0, 第 n 个增量纯于 n+1; 第 m 个增量含 Ω-结点; j > m+1
    module Bad (w : Wd (sup ℕ F)) (p₀ : Pure 0 c₀) (pδ : ∀ n → Pure (suc n) (δ n))
               (j m : ℕ) (mj : suc m < j) (nf : ¬ OmFree (δ m)) where
      j≢ : ∀ {k} → k < j → ¬ (k ≡ j)
      j≢ lt refl = <-irrefl refl lt

      cum-impure : ∀ n → m < n → ¬ Pure j (cum n)
      cum-impure n mn h =
        nf (two-pure (j≢ mj) (δ m) (pδ m) (pureR j (cum m) (δ m) (pure⊲ {w = w} (cum-mono n mn) h)))

      below : ∀ n {x} → x ⊲[ w ] cum n → Pure j x → ¬ OmFree x → ⊥
      below zero {x} p px nx = nx (two-pure (j≢ (≤-trans (s≤s z≤n) mj)) x (pure⊲ p p₀) px)
      below (suc n) p px nx with split⊞ (cum n) (δ n) p
      ... | inj₁ q = below n q px nx
      ... | inj₂ (b′ , q , refl) with m <? n
      ...   | yes mn = cum-impure n mn (pureL j (cum n) b′ {w} px)
      ...   | no ¬mn = below n hself (pureL j (cum n) b′ {w} px) (λ fc → nx (free⊞ (cum n) b′ fc fb′))
        where
        nj : suc n < j
        nj = ≤-trans (s≤s (s≤s (≮⇒≥ ¬mn))) mj
        fb′ : OmFree b′
        fb′ = two-pure (j≢ nj) b′ (pure⊲ q (pδ n)) (pureR j (cum n) b′ px)

      not-below : ∀ {x} → x ⊲[ w ] hl cum → Pure j x → ¬ OmFree x → ⊥
      not-below hself px nx = cum-impure (suc m) ≤-refl (px (suc m))
      not-below (hlim n p) px nx = below n p px nx
```

## §3 结论 (按档)

- **[定理]** `split⊞`, `free⊞`, `pureR`, `pureL`, `cum-mono`.
- **[定理, 否定]** **`CumTrap.Diag.Bad.below`**, **`not-below`**: 部分和对角 (一切 `sup ℕ F`, 一切起点与增量) 里, 只要第 $m$ 个增量含 $\Omega$-结点, 第 $j>m+1$ 站的任何含 $\Omega$-结点的纯高度都不是对角的字面第一位置. 前提可满足: 见 [NegNewTwrShape](NegNewTwrShape.lagda.md) 的 `tw-not-below` 与实例 `nfT`.
- 这是 `NegLvKtTrap.stage-not-below` (玩具增量) 的推广; 那里的判断 "只要第 0 项含第 0 站的 $\Omega$-结点, 同一论证适用" 在这里换成定理, 条件改为 "某个更早的增量含 $\Omega$-结点" (起点可以无 $\Omega$-结点, 新塔的起点 $b_0$ 正是这样).
