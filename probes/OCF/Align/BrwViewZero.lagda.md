# 布劳威尔树的 View (二): 第 0 层的差树, 无条件

> 不含记号. 入口 [BrwView](BrwView.lagda.md). 第 0 层的差树 `D azero W` ([SumOneTree](SumOneTree.lagda.md)), 值 `sum azero`, 目标 `A`, 值前序 `TLRuleSpec._≤_`, $\mathbb N$-极限的步进是 `A` 的合法性 `Lg` 里那一条 (`_⊲_`, 字面第一位置). 第 0 层没有 $\Omega$-极限 (种类 `⊥`).
>
> **View 直接读差树的结构, 不经 `toA`.** `vw x vx q y`: 已走过前缀 $x$ (它的 View 是 $vx$), 再走 $y$ (沿 $q$ 抬升). 对 $y$ 分情况:
>
> | $y$ | 读法 | 部分 |
> |---|---|---|
> | `n0` | 前缀的读法 $vx$ | 前缀的部分 |
> | `n1` | 后继 | $x$ |
> | `y₁ ⨾ y₂` | 先走 $y_1$, 前缀变成 $x ⨾ y_1$, 再走 $y_2$ | |
> | `nl d` | $\mathbb N$-极限 | 部分和 $x ⨾ (d_0 ⨾ \dots ⨾ d_{n-1})$ |
> | `nw p y` | 同 $y$, 路径接上 | |
>
> 值一致在前四种情形里是**字面的** (`refl` 级), 只有 `nl` 要一条 $\equiv$ (`ps-pt`: 部分和树的值就是 `pt`). 步进是 `sum-fst`, 无前提. 所以第 0 层的 View 是**无条件定理** `view₀`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwViewZero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl; ≤l; l≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; Lg-sum)
open import OCF.Align.BrwViewDef
```

## §1 签名

```agda
⊥-Set : ⊥ → Set
⊥-Set ()

⊥-tg : ∀ {k : ⊥} → ⊥-Set k → ⊤
⊥-tg {()}

⊥-bΩ : ∀ (k : ⊥) → ((c : ⊥-Set k) → A) → A
⊥-bΩ ()

Sig₀ : Sig
Sig₀ = record
  { Ix = ⊤ ; B = λ _ → A ; _≼_ = _≤_ ; Stp = _⊲_
  ; Kd = λ _ → ⊥ ; Cd = ⊥-Set ; LgC = λ _ → ⊤ ; tg = ⊥-tg
  ; bz = azero ; bs = asuc ; bl = alim ; bΩ = ⊥-bΩ }

open Sig Sig₀ using (_≈_)
```

## §2 读法

```agda
module _ (W : A) where
  X₀ : ⊤ → Set
  X₀ _ = D azero W

  val₀ : ∀ {i} → X₀ i → A
  val₀ x = sum azero x

  Lgl₀ : ∀ {i} → X₀ i → Set
  Lgl₀ _ = ⊤

  V₀ : A → Set
  V₀ = View Sig₀ X₀ val₀ Lgl₀ tt

  -- 部分和的树
  ps : ∀ {W₀} → (ℕ → D azero W₀) → ℕ → D azero W₀
  ps d zero = n0
  ps d (suc n) = ps d n ⨾ d n

  ps-pt : ∀ {W₀} b (d : ℕ → D azero W₀) n → sum b (ps d n) ≡ pt b d n
  ps-pt b d zero = refl
  ps-pt b d (suc n) = cong (λ a → sum a (d n)) (ps-pt b d n)

  ≈r : ∀ a → a ≈ a
  ≈r a = ≤-refl a , ≤-refl a

  lim≡ : ∀ (f g : ℕ → A) → (∀ n → f n ≡ g n) → alim f ≈ alim g
  lim≡ f g e = l≤ (λ n → ≤l n (subst (λ a → f n ≤ a) (e n) (≤-refl (f n)))) ,
               l≤ (λ n → ≤l n (subst (λ a → g n ≤ a) (sym (e n)) (≤-refl (g n))))

  vw : ∀ {W₀} (x : D azero W) → V₀ (sum azero x) → W₀ ⊲ W → (y : D azero W₀) → V₀ (sum (sum azero x) y)
  vw x vx q n0 = vx
  vw x vx q n1 = vs x tt (≈r _)
  vw x vx q (y₁ ⨾ y₂) = vw (x ⨾ nw q y₁) (vw x vx q y₁) q y₂
  vw x vx q (nl d) =
    vl (λ n → x ⨾ nw q (ps d n)) (λ _ → tt)
       (λ n → sum-fst (sum (sum azero x) (ps d n)) (d n))
       (lim≡ _ _ (λ n → sym (ps-pt (sum azero x) d n)))
  vw x vx q (ni () u)
  vw x vx q (nκ () u)
  vw x vx q (nw p y) = vw x vx (⊲-tr p q) y

  view₀ : BrwView Sig₀ X₀ val₀ Lgl₀
  view₀ = record { view = λ x _ → vw n0 (vz (≈r azero)) C.self x }
```

**合法性.** 这里的 `Lgl₀` 是 `⊤`: 第 0 层差树的合法性由形状给, 值总是 `Lg` (`Lg-sum`, 无前提). View 的 $\mathbb N$-极限步进 `Stp = _⊲_` 正是 `Lg (alim _)` 要的那一条, 所以 View 给出的值的读法与 `Lg` 的读法一致:

```agda
  Lg-val₀ : ∀ (x : D azero W) → Lg (val₀ {tt} x)
  Lg-val₀ x = Lg-sum azero x tt
```
