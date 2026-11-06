# 沿 View 递归 (三): 经 View 读出布劳威尔树, 值一致

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). 有了 `BrwViewᵂ`, 就能沿 View 递归. 这里给一般的递归原理 `rec` 和一个检验: **经 View 读出目标布劳威尔树** `rd` (零读成 `bz`, 后继读成 `bs`, $\mathbb N$-极限读成 `bl`, $\Omega$-极限读成 `bΩ`, 部分递归地读), 并证 `rd o ≈ val o` (`rd≈`).
>
> - `rd` 的 $\Omega$-极限要在**每个**坐标上读部分, 而部分只在合法坐标上合法. 所以 `rd` 要 `allC` (一切坐标合法). 第 0 层 (没有 $\Omega$-极限) 与第 1 层 (`LgC = ⊤`) 都满足; 高度树 `H` 不满足, 但它的 View 是恒等, 不用读.
> - 值一致要目标树的四条单调 (`Cong`): 传递, 后继、极限、$\Omega$-极限逐点单调. 这是目标树自己的性质, 不是 View 的.
> - 递归对 `Acc` 的证明结构递归; 一步 `step` 不递归, 只看 View 的种类与部分的读数. 证明同形.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfRead where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
open import OCF.Align.BrwWfDef
```

## §1 递归原理

```agda
module _ {S : Sig} {X : Sig.Ix S → Set} {val : ∀ {i} → X i → Sig.B S i} {Lgl : ∀ {i} → X i → Set}
         (W : BrwViewᵂ S X val Lgl) where
  open Sig S
  open BrwViewᵂ W
  open BrwView bv

  rec′ : (P : Obj S X val Lgl → Set) →
         (∀ {i} (x : X i) (lx : Lgl x) → (∀ {o} → Part S X val Lgl (view x lx) o → P o) → P (i , x , lx)) →
         ∀ o → Acc (_◁_ S X val Lgl bv) o → P o
  rec′ P st (i , x , lx) (acc rs) = st x lx (λ p → rec′ P st _ (rs p))

  rec : (P : Obj S X val Lgl → Set) →
        (∀ {i} (x : X i) (lx : Lgl x) → (∀ {o} → Part S X val Lgl (view x lx) o → P o) → P (i , x , lx)) →
        ∀ o → P o
  rec P st o = rec′ P st o (wf o)
```

## §2 读出布劳威尔树

```agda
  module Read (allC : ∀ {i} {k : Kd i} (c : Cd k) → LgC c) where
    Bo : Obj S X val Lgl → Set
    Bo o = B (proj₁ o)

    step : ∀ {i v} (w : View S X val Lgl i v) → (∀ {o} → Part S X val Lgl w o → Bo o) → B i
    step (vz _) r = bz
    step (vs y ly _) r = bs (r p-s)
    step (vl f lf _ _) r = bl (λ n → r (p-l n))
    step (vΩ k g lg _) r = bΩ k (λ c → r (p-Ω c (allC c)))

    rd′ : ∀ o → Acc (_◁_ S X val Lgl bv) o → Bo o
    rd′ = rec′ Bo (λ x lx r → step (view x lx) r)

    rd : ∀ o → Bo o
    rd o = rd′ o (wf o)
```

## §3 值一致

```agda
  record Cong : Set where
    field
      tr   : ∀ {i j k} {a : B i} {b : B j} {c : B k} → a ≼ b → b ≼ c → a ≼ c
      bs-m : ∀ {i} {a b : B i} → a ≼ b → bs a ≼ bs b
      bl-m : ∀ {i} {f g : ℕ → B i} → (∀ n → f n ≼ g n) → bl f ≼ bl g
      bΩ-m : ∀ {i} (k : Kd i) {f g : (c : Cd k) → B (tg c)} → (∀ c → f c ≼ g c) → bΩ k f ≼ bΩ k g

  module ReadOk (allC : ∀ {i} {k : Kd i} (c : Cd k) → LgC c) (C : Cong) where
    open Read allC
    open Cong C

    vo : (o : Obj S X val Lgl) → B (proj₁ o)
    vo (i , x , lx) = val x

    tr≈ : ∀ {i j k} {a : B i} {b : B j} {c : B k} → a ≈ b → b ≈ c → a ≈ c
    tr≈ (p , q) (p′ , q′) = tr p p′ , tr q′ q

    sym≈ : ∀ {i j} {a : B i} {b : B j} → a ≈ b → b ≈ a
    sym≈ (p , q) = q , p

    step≈ : ∀ {i v} (w : View S X val Lgl i v) (r : ∀ {o} → Part S X val Lgl w o → Bo o) →
            (∀ {o} (p : Part S X val Lgl w o) → r p ≈ vo o) → step w r ≈ v
    step≈ (vz e) r h = sym≈ e
    step≈ (vs y ly e) r h = tr≈ (bs-m (proj₁ (h p-s)) , bs-m (proj₂ (h p-s))) (sym≈ e)
    step≈ (vl f lf st e) r h = tr≈ (bl-m (λ n → proj₁ (h (p-l n))) , bl-m (λ n → proj₂ (h (p-l n)))) (sym≈ e)
    step≈ (vΩ k g lg e) r h =
      tr≈ (bΩ-m k (λ c → proj₁ (h (p-Ω c (allC c)))) , bΩ-m k (λ c → proj₂ (h (p-Ω c (allC c))))) (sym≈ e)

    rd≈′ : ∀ o (a : Acc (_◁_ S X val Lgl bv) o) → rd′ o a ≈ vo o
    rd≈′ (i , x , lx) (acc rs) = step≈ (view x lx) _ (λ p → rd≈′ _ (rs p))

    rd≈ : ∀ o → rd o ≈ vo o
    rd≈ o = rd≈′ o (wf o)
```

**读法.** `rd≈` 说: 只用 View (不看对象的字面结构, 不看 `val` 的定义) 递归地读出的布劳威尔树, 与原来的值互相 $\preccurlyeq$. 这是纲领 1 的解释 "中间层有内部的、值一致的布劳威尔树 View" 在**递归**意义下成立: 不只每一步值一致, 整棵读出的树也值一致.
