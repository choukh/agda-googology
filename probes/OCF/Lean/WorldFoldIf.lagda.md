# 世界索引树的可数折叠接口

接口定稿：2026-11-06。本接口规定一个具体实验折叠的全部构造子方程，
不把它称为 ψ，也不预设序数值正确。坐标链由前一步输出生成，
每个坐标显式带源世界为第一位置的证据；没有裸下标比较。
`legal` 只验收输出可数树；内部 View、输入 Ω-单调性、值下界均不在接口内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldFoldIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl; _⊲_; hself; _⊞_; ⊞-fst; LgB)
open import OCF.Lean.NegFab6Idx using (W; wz; ws; wl; wn)

partial : (ℕ → Cd) → ℕ → Cd
partial f zero = f zero
partial f (suc n) = partial f n ⊞ f (suc n)

series : (ℕ → Cd) → Cd
series f = hl (partial f)

State : Cd → Set
State B = Σ Cd (λ e → B ⊲ e)

orbit : ∀ B → ((e : Cd) → B ⊲ e → Cd) → ℕ → State B
orbit B h zero = B , hself
orbit B h (suc n) = let s = orbit B h n; d = hs (h (proj₁ s) (proj₂ s))
                    in (B ⊞ d) , ⊞-fst B d

feedback : ∀ B → ((e : Cd) → B ⊲ e → Cd) → Cd
feedback B h = series (λ n → let s = orbit B h n in h (proj₁ s) (proj₂ s))

record CountableFold : Set₁ where
  field
    fold : ∀ {B} → W B → Cd
    legal : ∀ {B} (a : W B) → LgB (fold a)
    zero-law : ∀ {B} → fold (wz {B}) ≡ hz
    suc-law : ∀ {B} (a : W B) → fold (ws a) ≡ hs (fold a)
    lim-law : ∀ {B} (f : ℕ → W B) → fold (wl f) ≡ series (λ n → fold (f n))
    node-law : ∀ {B} (g : (e : Cd) → B ⊲ e → W (hs e)) →
      fold (wn g) ≡ feedback B (λ e p → fold (g e p))
```

翻译账：节点沿用原玩具；输出部分和由可数合法性需要引入；
回灌加后继是本实验选择，尚没有树侧唯一性或值语义支持。
