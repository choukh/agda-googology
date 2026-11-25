# YiLvFold：对目标层与派发参数化的折叠

**判决 (编译定理)：一套定义给出一切目标层 `m` 的折叠 `ψ m`，证书无关；对任意派发 `way`，输出合法、带嵌套证据、保持第一位置
(目标层 `Plain`，定义域 `OnlyP × Legal × Seedᶠ`)。** 合法性不依赖派发是否正确；值依赖，本篇没有值。
派发只读裸层号，所以输出是树的函数；不否定读位置或读证书的派发。实例 [YiLvFoldFin](YiLvFoldFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (CP; self; suc; lim; fst; CP-tr; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase
```

## 1 一个互递归块

`ψ` 对树递归，目标层 `m` 是参数，递归调用里可以换 (链由结点自己的层 `k` 的折叠推进)。结点处问 `way m k`：
`keep s refl` 则保留在槽位 `s`，第一支与分支各自折叠；`fold` 则链在 `Raw k` 里，观察取目标层 `m`。
"层号相等" 与 "层号在目标层之上" 是同一个子句。带 `n` 的函数是结点处按派发结果分情况的那一半。

```agda
module Fold (way : ∀ m k → Way m k) where

  ψ : (m x : LF) → .(Dom x) → Raw m
  ψn : ∀ m k → Way m k → (c : Raw k) .(w : Lgl k c) .(b : Nested k c) (t : LF)
    (g : (η : Raw k) → .(Gd k c η) → LF) → .(Dom (lc k c w b t g)) → Raw m
  ψ-pos : ∀ m x .(d : Dom x) → Pos m (ψ m x d)
  ψn-pos : ∀ m k (y : Way m k) c .(w : Lgl k c) .(b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) .(d : Dom (lc k c w b t g)) →
    Pos m (ψn m k y c w b t g d)
  ψ-legal : ∀ m → Plain m → ∀ x (d : Dom x) → Lgl m (ψ m x d)
  ψn-legal : ∀ m → Plain m → ∀ k (y : Way m k) c .(w : Lgl k c) .(b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) (d : Dom (lc k c w b t g)) →
    Lgl m (ψn m k y c w b t g d)
  ψ-nested : ∀ m x (d : Dom x) → Nested m (ψ m x d)
  ψn-nested : ∀ m k (y : Way m k) c .(w : Lgl k c) .(b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) (d : Dom (lc k c w b t g)) →
    Nested m (ψn m k y c w b t g d)
  ψ-position : ∀ m x y (dx : Dom x) (dy : Dom y) → CP x y →
    Cp m (ψ m x dx) (ψ m y dy)
  ψn-position : ∀ m x k (y : Way m k) c .(w : Lgl k c) .(b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) (dx : Dom x)
    (dy : Dom (lc k c w b t g)) → CP x t →
    Dn m (ψ m x dx) (ψn m k y c w b t g dy)

  ψ m zero d = cO m
  ψ m (suc x) d = successor m (ψ m x d)
  ψ m (lim f) d = G.lim (λ n → ψ m (f n) (dom-at f d n))
  ψ m (lc k c w b t g) d = ψn m k (way m k) c w b t g d

  ψn m .(lev m s) (keep s refl) c w b t g d =
    nodeAt m s (rawAlg m) c
      (ψ m t (Node.first (lev m s) c w b t g d))
      (λ η e → ψ m (g η e) (Node.branch (lev m s) c w b t g d η e))
  ψn m k fold c w b t g d =
    Chain.collapse k (Node.plain k c w b t g d) c
      (λ η e → ψ k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-legal k (Node.plain k c w b t g d) (g η e)
        (Node.branch k c w b t g d η e))
      (λ η e → ψ-nested k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-pos k (g η e) (Node.branch k c w b t g d η e))
      m
      (λ η e → ψ m (g η e) (Node.branch k c w b t g d η e))
      (startᴸ k c w b)

  ψ-pos m zero d = cO-pos m
  ψ-pos m (suc x) d = tt
  ψ-pos m (lim f) d = tt
  ψ-pos m (lc k c w b t g) d = ψn-pos m k (way m k) c w b t g d

  ψn-pos m .(lev m s) (keep s refl) c w b t g d = node-ps m s (rawAlg m) c _ _
  ψn-pos m k fold c w b t g d = tt

  ψ-legal m pl zero d = cO-Lgl m
  ψ-legal m pl (suc x) d =
    copies-step m pl (ψ m x d) , copies-legal m pl (ψ m x d) (ψ-legal m pl x d)
  ψ-legal m pl (lim f) d =
    (λ n → ψ-position m (f n) (f (suc n)) (dom-at f d n) (dom-at f d (suc n))
      (dom-step f d n)) ,
    (λ n → ψ-legal m pl (f n) (dom-at f d n))
  ψ-legal m pl (lc k c w b t g) d = ψn-legal m pl k (way m k) c w b t g d

  ψn-legal m pl .(lev m s) (keep s refl) c w b t g d =
    node-lgl m s (rawAlg m) c _ _
      (λ η e → ψ-position m t (g η e)
        (Node.first (lev m s) c w b t g d) (Node.branch (lev m s) c w b t g d η e)
        (Node.to-branch (lev m s) c w b t g d η e))
      (λ η e η′ e′ q → ψ-position m (g η e) (g η′ e′)
        (Node.branch (lev m s) c w b t g d η e)
        (Node.branch (lev m s) c w b t g d η′ e′)
        (Node.directed (lev m s) c w b t g d η e η′ e′ q))
      (ψ-legal m pl t (Node.first (lev m s) c w b t g d))
      (λ η e → ψ-legal m pl (g η e) (Node.branch (lev m s) c w b t g d η e))
  ψn-legal m pl k fold c w b t g d =
    ChainLegal.collapse-legal k (Node.plain k c w b t g d) c
      (λ η e → ψ k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-legal k (Node.plain k c w b t g d) (g η e)
        (Node.branch k c w b t g d η e))
      (λ η e → ψ-nested k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-pos k (g η e) (Node.branch k c w b t g d η e))
      (startᴸ k c w b) (Node.seed k c w b t g d)
      m
      (λ η e → ψ m (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-legal m pl (g η e) (Node.branch k c w b t g d η e))
      (λ η e η′ e′ q → ψ-position m (g η e) (g η′ e′)
        (Node.branch k c w b t g d η e) (Node.branch k c w b t g d η′ e′)
        (Node.directed k c w b t g d η e η′ e′ q))

  ψ-nested m zero d = cO-Nested m
  ψ-nested m (suc x) d = copies-nested m (ψ m x d) (ψ-nested m x d)
  ψ-nested m (lim f) d = λ n → ψ-nested m (f n) (dom-at f d n)
  ψ-nested m (lc k c w b t g) d = ψn-nested m k (way m k) c w b t g d

  ψn-nested m .(lev m s) (keep s refl) c w b t g d =
    node-ns m s (rawAlg m) c _ _
      (proj₁ (Node.low (lev m s) c w b t g d))
      (proj₂ (Node.low (lev m s) c w b t g d))
      (ψ-nested m t (Node.first (lev m s) c w b t g d))
      (λ η e → ψ-nested m (g η e) (Node.branch (lev m s) c w b t g d η e))
  ψn-nested m k fold c w b t g d =
    ChainLegal.collapse-nested k (Node.plain k c w b t g d) c
      (λ η e → ψ k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-legal k (Node.plain k c w b t g d) (g η e)
        (Node.branch k c w b t g d η e))
      (λ η e → ψ-nested k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-pos k (g η e) (Node.branch k c w b t g d η e))
      (startᴸ k c w b) (Node.seed k c w b t g d)
      m
      (λ η e → ψ m (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-nested m (g η e) (Node.branch k c w b t g d η e))

  ψ-position m .zero zero dx dy self = inj₁ refl
  ψ-position m .(suc y) (suc y) dx dy self = inj₁ refl
  ψ-position m x (suc y) dx dy (suc p) =
    inj₂ (zero , ψ-position m x y dx dy p)
  ψ-position m .(lim f) (lim f) dx dy self = inj₁ refl
  ψ-position m x (lim f) dx dy (lim n p) =
    inj₂ (n , ψ-position m x (f n) dx (dom-at f dy n) p)
  ψ-position m .(lc k c w b t g) (lc k c w b t g) dx dy self = inj₁ refl
  ψ-position m x (lc k c w b t g) dx dy (fst p) =
    inj₂ (ψn-position m x k (way m k) c w b t g dx dy p)

  ψn-position m x .(lev m s) (keep s refl) c w b t g dx dy p =
    node-dn m s (rawAlg m) c _ _
      (ψ-position m x t dx (Node.first (lev m s) c w b t g dy) p)
  ψn-position m x k fold c w b t g dx dy p =
    zero , ψ-position m x (g c (Node.seed k c w b t g dy)) dx
      (Node.branch k c w b t g dy c (Node.seed k c w b t g dy))
      (CP-tr p (Node.to-branch k c w b t g dy c (Node.seed k c w b t g dy)))
```

## 2 行

都是 `refl`。保留行与链行写在 `ψn` 上；`node-row` 把结点接到派发结果。`next` 是链行里的那条链：
下一点是这一点加上结点自己的层 `k` 的折叠 (回灌)，观察是目标层 `m` 的折叠。

```agda
  zero-row : ∀ m (d : Dom zero) → ψ m zero d ≡ cO m
  zero-row m d = refl

  suc-row : ∀ m x (d : Dom (suc x)) → ψ m (suc x) d ≡ successor m (ψ m x d)
  suc-row m x d = refl

  lim-row : ∀ m f (d : Dom (lim f)) →
    ψ m (lim f) d ≡ G.lim (λ n → ψ m (f n) (dom-at f d n))
  lim-row m f d = refl

  node-row : ∀ m k c (w : Lgl k c) (b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) (d : Dom (lc k c w b t g)) →
    ψ m (lc k c w b t g) d ≡ ψn m k (way m k) c w b t g d
  node-row m k c w b t g d = refl

  keep-row : ∀ m s c (w : Lgl (lev m s) c) (b : Nested (lev m s) c) t
    (g : (η : Raw (lev m s)) → .(Gd (lev m s) c η) → LF)
    (d : Dom (lc (lev m s) c w b t g)) →
    ψn m (lev m s) (keep s refl) c w b t g d ≡
    nodeAt m s (rawAlg m) c
      (ψ m t (Node.first (lev m s) c w b t g d))
      (λ η e → ψ m (g η e) (Node.branch (lev m s) c w b t g d η e))
  keep-row m s c w b t g d = refl

  next : ∀ k c .(w : Lgl k c) .(b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) →
    .(Dom (lc k c w b t g)) → Pt k c → Pt k c
  next k c w b t g d =
    Chain.next k (Node.plain k c w b t g d) c
      (λ η e → ψ k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-legal k (Node.plain k c w b t g d) (g η e)
        (Node.branch k c w b t g d η e))
      (λ η e → ψ-nested k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-pos k (g η e) (Node.branch k c w b t g d η e))

  out : ∀ m k c .(w : Lgl k c) .(b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) →
    .(Dom (lc k c w b t g)) → Pt k c → Raw m
  out m k c w b t g d (pt η e) = ψ m (g η e) (Node.branch k c w b t g d η e)

  next-additive : ∀ k c (w : Lgl k c) (b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) (d : Dom (lc k c w b t g)) p →
    at (next k c w b t g d p) ≡ plus k (at p) (out k k c w b t g d p)
  next-additive k c w b t g d (pt η e) = refl

  next-grow : ∀ k c .(w : Lgl k c) .(b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) .(d : Dom (lc k c w b t g)) p →
    Dn k (at p) (at (next k c w b t g d p))
  next-grow k c w b t g d =
    Chain.grows k (Node.plain k c w b t g d) c
      (λ η e → ψ k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-legal k (Node.plain k c w b t g d) (g η e)
        (Node.branch k c w b t g d η e))
      (λ η e → ψ-nested k (g η e) (Node.branch k c w b t g d η e))
      (λ η e → ψ-pos k (g η e) (Node.branch k c w b t g d η e))

  fold-row : ∀ m k c (w : Lgl k c) (b : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) (d : Dom (lc k c w b t g)) →
    ψn m k fold c w b t g d ≡
    G.lim (λ n → out m k c w b t g d
      (iterate (next k c w b t g d) (startᴸ k c w b) n))
  fold-row m k c w b t g d = refl

  certificate-free : ∀ m x (d d′ : Dom x) → ψ m x d ≡ ψ m x d′
  certificate-free m x d d′ = refl
```
