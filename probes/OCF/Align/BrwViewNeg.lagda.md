# 布劳威尔树的 View (三): "严格递增" 的 $\mathbb N$-极限推出 LPO

> 不含记号. 入口 [BrwView](BrwView.lagda.md). 作者的解释里 $\mathbb N$-极限写作 "严格递增". 这里证: **在第 0 层, 只要某个合法对象的值是 0/1 序列的部分和的极限, 要求 View 的 $\mathbb N$-极限值上严格递增 (`asuc (val (f n)) ≤ val (f (suc n))`) 就推出 LPO.** 原因: 零、后继、严格的极限三种读法里, 只有零的值 $\le0$; 读法就判定了 "序列全为假" 还是 "有一项为真".
>
> - `strict→LPO`: 对任意载体、任意值映射, 只要有这样一族对象 (`Enc`), 严格的 View 推出 LPO.
> - `strict-D`: 第 0 层差树 `D azero W` (值 `sum azero`) 有这样一族: `nl (λ n → 若 α n 则 n1 否则 n0)`.
> - `strict-A`: 带合法性的第 0 层布劳威尔树 `A` 自己也有 (`Lg` 只要相邻项是第一位置, 不要严格). 所以这不是差树的毛病: `A` 本身的极限就不是严格的.
>
> 所以记录 `BrwView` 的步进 `Stp` 取目标树自己合法性里的那一条 (第 0 层是 `_⊲_`, 不严格). 这否定的是 "第 0 层的 View 带值上严格递增的 $\mathbb N$-极限" 这一个字段形状 (在 `--safe` 下不能给出, 除非 LPO), 不否定别的形状.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwViewNeg where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤lim⁻)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; sum; pt; Lg-sum)
open import OCF.Align.BrwViewDef
open import OCF.Align.BrwViewZero using (⊥-Set; ⊥-tg; ⊥-bΩ)
```

## §1 严格的签名

```agda
Sig₀ˢ : Sig
Sig₀ˢ = record
  { Ix = ⊤ ; B = λ _ → A ; _≼_ = _≤_ ; Stp = λ a b → asuc a ≤ b
  ; Kd = λ _ → ⊥ ; Cd = ⊥-Set ; LgC = λ _ → ⊤ ; tg = ⊥-tg
  ; bz = azero ; bs = asuc ; bl = alim ; bΩ = ⊥-bΩ }

LPO : Set
LPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ Σ ℕ (λ n → α n ≡ true)
```

## §2 0/1 序列的部分和

```agda
pk : ∀ {W} → Bool → D azero W
pk true = n1
pk false = n0

Σα : ∀ {W} → (ℕ → Bool) → A
Σα {W} α = alim (pt {W} azero (λ n → pk (α n)))

one≤ : ∀ {W} (α : ℕ → Bool) (n : ℕ) → α n ≡ true → asuc azero ≤ Σα {W} α
one≤ {W} α n e = ≤l (suc n) (go (α n) e)
  where
  go : ∀ b → b ≡ true → asuc azero ≤ sum (pt {W} azero (λ m → pk (α m)) n) (pk {W} b)
  go true refl = s≤ z≤

find : ∀ {W} (α : ℕ → Bool) (n : ℕ) → asuc azero ≤ pt {W} azero (λ m → pk (α m)) n → Σ ℕ (λ m → α m ≡ true)
find α zero ()
find {W} α (suc n) h = go (α n) refl h
  where
  go : ∀ b → α n ≡ b → asuc azero ≤ sum (pt {W} azero (λ m → pk (α m)) n) (pk {W} b) → Σ ℕ (λ m → α m ≡ true)
  go true e _ = n , e
  go false e h′ = find α n h′

no1≤0 : ¬ (asuc azero ≤ azero)
no1≤0 ()
```

## §3 严格的 View 推出 LPO

`Enc`: 每个 $\alpha$ 有一个合法对象, 值与 $\Sigma\alpha$ 互相 $\le$.

```agda
module _ {W : A} (X : ⊤ → Set) (val : ∀ {i} → X i → A) (Lgl : ∀ {i} → X i → Set) where
  open Sig Sig₀ˢ using (_≈_)

  Enc : Set
  Enc = ∀ (α : ℕ → Bool) → Σ (X tt) (λ x → Lgl x × (val x ≈ Σα {W} α))

  strict→LPO : BrwView Sig₀ˢ X val Lgl → Enc → LPO
  strict→LPO V enc α with enc α
  ... | x , lx , (h₁ , h₂) = decide (BrwView.view V x lx)
    where
    pos : asuc azero ≤ val x → Σ ℕ (λ m → α m ≡ true)
    pos p with ≤lim⁻ (≤-trans p h₁)
    ... | n , q = find α n q

    allF : val x ≤ azero → ∀ n → α n ≡ false
    allF p n with α n in e
    ... | false = refl
    ... | true = ⊥-elim (no1≤0 (≤-trans (one≤ α n e) (≤-trans h₂ p)))

    decide : View Sig₀ˢ X val Lgl tt (val x) → (∀ n → α n ≡ false) ⊎ Σ ℕ (λ n → α n ≡ true)
    decide (vz (p , _)) = inj₁ (allF p)
    decide (vs y _ (_ , q)) = inj₂ (pos (≤-trans (s≤ z≤) q))
    decide (vl f _ st (_ , q)) = inj₂ (pos (≤-trans (s≤ z≤) (≤-trans (st 0) (≤-trans (≤l 1 (≤-refl _)) q))))
    decide (vΩ () g _ _)
```

## §4 两个实例

```agda
-- 第 0 层差树
strict-D : ∀ W → BrwView Sig₀ˢ (λ _ → D azero W) (λ x → sum azero x) (λ _ → ⊤) → LPO
strict-D W V = strict→LPO {W} _ _ _ V (λ α → nl (λ n → pk (α n)) , tt , (≤-refl _ , ≤-refl _))

-- 第 0 层布劳威尔树自己
strict-A : BrwView Sig₀ˢ (λ _ → A) (λ a → a) Lg → LPO
strict-A V = strict→LPO {azero} _ _ _ V (λ α → Σα {azero} α , Lg-sum {azero} azero (nl (λ n → pk (α n))) tt , (≤-refl _ , ≤-refl _))
```
