# 第二层的同步扩展观察关系

关系保留原 D₂ 的 ni、nε κ₀ 及 nw。回调只沿成对后缀调用：
每步同事件种类、payload Shape；不是任意两份历史的自然性。
有 HistLow 相关基底时，History.transplant 推出相应未来历史相关。
关系自身也允许不同基底，以表达 drp₂ 内部保存旧基底的上下文；
这不意味着任意函数对这种上下文相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCtxValueIf where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (D₁; D₂)
open import OCF.Align.EventReturnCoordIf using (E₀)
open import OCF.Align.EventReturnCtxIf using (R₁)
open import OCF.Align.EventReturnHistory using (Suffix)

data R₂ (a : A) (H H′ : Hist) : D₂ (a , H) → D₂ (a , H′) → Set where
  rz : R₂ a H H′ n0 n0
  ro : R₂ a H H′ n1 n1
  ra : ∀ {x y x′ y′} → R₂ a H H′ x x′ → R₂ a H H′ y y′ →
    R₂ a H H′ (x ⨾ y) (x′ ⨾ y′)
  rl : ∀ {f g} → (∀ n → R₂ a H H′ (f n) (g n)) → R₂ a H H′ (nl f) (nl g)
  rw : ∀ {b J J′} {x : D₂ (b , J)} {y : D₂ (b , J′)}
    (p : b ⊲ a) (s : Suf J H) (s′ : Suf J′ H′) → R₂ b J J′ x y →
    R₂ a H H′ (nw (p , s) x) (nw (p , s′) y)
  rk : ∀ {u : ∀ {c} → a ⊲ c → Lg c → D₂ (c , H)}
         {v : ∀ {c} → a ⊲ c → Lg c → D₂ (c , H′)} →
    (∀ {c} (p : a ⊲ c) lc → R₂ c H H′ (u p lc) (v p lc)) →
    R₂ a H H′ (nκ tt u) (nκ tt v)
  ri₀ : ∀ {u : ∀ {W} → (a , H) ≤ W → LgWε W → D₀ W → D₂ W}
           {v : ∀ {W} → (a , H′) ≤ W → LgWε W → D₀ W → D₂ W} →
    (∀ {b J J′} (p : a ⊲ b) (s : Suf H J) (s′ : Suf H′ J′) → Suffix s s′ →
      (lb : Lg b) {x : D₀ (b , J)} {y : D₀ (b , J′)} → E₀ x y →
      R₂ b J J′ (u (p , s) (lb , tt) x) (v (p , s′) (lb , tt) y)) →
    R₂ a H H′ (ni (ss (hsuc hself)) u) (ni (ss (hsuc hself)) v)
  ri₁ : ∀ {u : ∀ {W} → (a , H) ≤ W → LgWε W → D₁ W → D₂ W}
           {v : ∀ {W} → (a , H′) ≤ W → LgWε W → D₁ W → D₂ W} →
    (∀ {b J J′} (p : a ⊲ b) (s : Suf H J) (s′ : Suf H′ J′) → Suffix s s′ →
      (lb : Lg b) {x : D₁ (b , J)} {y : D₁ (b , J′)} → R₁ b J J′ x y →
      R₂ b J J′ (u (p , s) (lb , tt) x) (v (p , s′) (lb , tt) y)) →
    R₂ a H H′ (ni (ss hself) u) (ni (ss hself) v)
  re : ∀ {u : ∀ {W} → (a , H) ≤ W → LgWε W → D₂ W}
          {v : ∀ {W} → (a , H′) ≤ W → LgWε W → D₂ W} →
    (∀ {b J J′} (p : a ⊲ b) (s : Suf H J) (s′ : Suf H′ J′) → Suffix s s′ →
      (lb : Lg b) → R₂ b J J′ (u (p , s) (lb , tt)) (v (p , s′) (lb , tt))) →
    R₂ a H H′ (nε κ₀ tt u) (nε κ₀ tt v)
```
