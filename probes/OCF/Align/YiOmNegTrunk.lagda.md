# YiOmNeg 第 3 项：不引用任何一支内部的树

**判决：编译定理 (刻画与封闭)，读法是判断。** `Trunk`：`Raw (tw 2)` 里结点只在主干槽位上、嵌入只来自层号 0 与第一支的树。它对已有的加法 `plus (tw 2)` 封闭；
它的结点的槽位层号都是 0；读回只含层号 0 的结点与原子 `tw 3` (`trunk-read`)；满足 [YiOmNegTop](YiOmNegTop.lagda.md) 的联系的保留像不在其中 (`no-trunk`)。
不否定替代行本身；`Trunk` 的结点的槽位都在主干上 (`trunk-own-zero`)，按 "链由结点自己那一层的折叠推进" 的规则，目标不会落在某一支里，碰不到 [YiOmNegBranch](YiOmNegBranch.lagda.md) (这一句是判断)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmNegTrunk where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiLvFoldAdd using (plus)
open import OCF.Align.YiOmIf
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂)
open import OCF.Align.YiOmNegSlot using (NodeAt)
open import OCF.Align.YiOmNegTop using (TopKeep; e₂)
```

## 1 谓词

主干上的两个位置 (`root₂`, `first₂`) 层号都是 0，下界与坐标是第 0 层的值。孩子有三种：层号 0 的值，第一支 `tw 1` 的树，某一支的树；前两种不引用任何一支。

```agda
Trunk : Raw K₂ω → Set
Trunk G.zero = ⊤
Trunk (G.suc a) = Trunk a
Trunk (G.lim f) = ∀ n → Trunk (f n)
Trunk (G.lc (inj₁ (inj₁ _)) c t g) = Trunk t × (∀ η .(e : Gd zero c η) → Trunk (g η e))
Trunk (G.lc (inj₁ (inj₂ ())) c t g)
Trunk (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) = Trunk t × (∀ η .(e : Gd zero c η) → Trunk (g η e))
Trunk (G.lc (inj₂ (inj₁ (inj₂ ()))) c t g)
Trunk (G.lc (inj₂ (inj₂ _)) c t g) = ⊥
Trunk (G.em (inj₁ _) T) = ⊤
Trunk (G.em (inj₂ (inj₁ _)) T) = ⊤
Trunk (G.em (inj₂ (inj₂ _)) T) = ⊥
Trunk G.top = ⊤

trunk-own-zero : ∀ q c t g → Trunk (G.lc q c t g) → lev K₂ω q ≡ zero
trunk-own-zero (inj₁ (inj₁ _)) c t g tr = refl
trunk-own-zero (inj₂ (inj₁ (inj₁ _))) c t g tr = refl
```

## 2 对加法封闭

加法是 [YiLvFoldAdd](YiLvFoldAdd.lagda.md) 的 `plus`。层号是 Ω 结点时它在 `em` 与 `top` 上取固定的值 (`x`，`suc x`)，其余逐构造子；
构造路若在 `tw 2` 上另写加法，本条要对那个加法重证。

```agda
trunk-plus : ∀ x y → Trunk x → Trunk y → Trunk (plus K₂ω x y)
trunk-plus x G.zero tx ty = tx
trunk-plus x (G.suc a) tx ty = trunk-plus x a tx ty
trunk-plus x (G.lim f) tx ty = λ n → trunk-plus x (f n) tx (ty n)
trunk-plus x (G.lc (inj₁ (inj₁ _)) c t g) tx (tt′ , tg) =
  trunk-plus x t tx tt′ , (λ η e → trunk-plus x (g η e) tx (tg η e))
trunk-plus x (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) tx (tt′ , tg) =
  trunk-plus x t tx tt′ , (λ η e → trunk-plus x (g η e) tx (tg η e))
trunk-plus x (G.em i T) tx ty = tx
trunk-plus x G.top tx ty = tx
```

## 3 读回

`Sh x`：`x` 的 Ω 结点层号都是 0，除非整棵子树字面就是 `tw 3`。`Trunk` 的树读回都是这样的：越过 `tw 3` 的层号只以 `tw 3` 这一个原子出现。

```agda
Sh : LF → Set
Sh zero = ⊤
Sh (suc x) = Sh x
Sh (lim f) = ∀ n → Sh (f n)
Sh (lc k c w b t g) =
  (lc k c w b t g ≡ tw 3) ⊎ ((k ≡ zero) × Sh t × (∀ η .(e : Gd k c η) → Sh (g η e)))

sh0 : ∀ (a : Raw zero) .(nb : Nested zero a) → Sh (up zero a nb)
sh0 G.zero nb = tt
sh0 (G.suc a) nb = sh0 a nb
sh0 (G.lim f) nb = λ n → sh0 (f n) (nb n)
sh0 (G.lc () c t g) nb
sh0 (G.em () T) nb
sh0 G.top nb = tt

sh1 : ∀ (a : Raw (suc zero)) .(nb : Nested (suc zero) a) → Sh (up (suc zero) a nb)
sh1 G.zero nb = tt
sh1 (G.suc a) nb = sh1 a nb
sh1 (G.lim f) nb = λ n → sh1 (f n) (nb n)
sh1 (G.lc (inj₁ _) c t g) nb =
  inj₂ (refl , sh1 t (proj₁ (proj₂ (proj₂ nb))) ,
    (λ η e → sh1 (g η e) (proj₂ (proj₂ (proj₂ nb)) η e)))
sh1 (G.lc (inj₂ ()) c t g) nb
sh1 (G.em _ T) nb = sh0 T nb
sh1 G.top nb = inj₂ (refl , tt , (λ η e → sh0 η (proj₂ (proj₂ e))))

trunk-read : ∀ ξ .(nb : Nested K₂ω ξ) → Trunk ξ → Sh (up K₂ω ξ nb)
trunk-read G.zero nb tr = tt
trunk-read (G.suc a) nb tr = trunk-read a nb tr
trunk-read (G.lim f) nb tr = λ n → trunk-read (f n) (nb n) (tr n)
trunk-read (G.lc (inj₁ (inj₁ _)) c t g) nb (tt′ , tg) =
  inj₂ (refl , trunk-read t (proj₁ (proj₂ (proj₂ nb))) tt′ ,
    (λ η e → trunk-read (g η e) (proj₂ (proj₂ (proj₂ nb)) η e) (tg η e)))
trunk-read (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) nb (tt′ , tg) =
  inj₂ (refl , trunk-read t (proj₁ (proj₂ (proj₂ nb))) tt′ ,
    (λ η e → trunk-read (g η e) (proj₂ (proj₂ (proj₂ nb)) η e) (tg η e)))
trunk-read (G.em (inj₁ _) T) nb tr = sh0 T nb
trunk-read (G.em (inj₂ (inj₁ _)) T) nb tr = sh1 T nb
trunk-read G.top nb tr = inj₁ refl
```

## 4 保留像不在其中

`Trunk` 的树读回若是结点，层号是 0。[YiOmNegTop](YiOmNegTop.lagda.md) 的记录要求坐标 2 的那一支读回成层号 1 的结点 (守卫是闭的相关证明)，
所以任何满足那条联系的 `top` 的像都不在 `Trunk` 里。这是定理；它相对于那条联系，不是相对于某个已写出的折叠。

```agda
node0 : ∀ (a : Raw zero) .(nb : Nested zero a) L → NodeAt L (up zero a nb) → L ≡ zero
node0 G.zero nb L ()
node0 (G.suc a) nb L ()
node0 (G.lim f) nb L ()
node0 (G.lc () c t g) nb L h
node0 (G.em () T) nb L h
node0 G.top nb L ()

node1 : ∀ (a : Raw (suc zero)) .(nb : Nested (suc zero) a) L →
  NodeAt L (up (suc zero) a nb) → L ≡ zero
node1 G.zero nb L ()
node1 (G.suc a) nb L ()
node1 (G.lim f) nb L ()
node1 (G.lc (inj₁ _) c t g) nb L h = sym h
node1 (G.lc (inj₂ ()) c t g) nb L h
node1 (G.em _ T) nb L h = node0 T nb L h
node1 G.top nb L h = sym h

trunk-node-zero : ∀ ξ .(nb : Nested K₂ω ξ) L → Trunk ξ → NodeAt L (up K₂ω ξ nb) → L ≡ zero
trunk-node-zero G.zero nb L tr ()
trunk-node-zero (G.suc a) nb L tr ()
trunk-node-zero (G.lim f) nb L tr ()
trunk-node-zero (G.lc (inj₁ (inj₁ _)) c t g) nb L tr h = sym h
trunk-node-zero (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) nb L tr h = sym h
trunk-node-zero (G.em (inj₁ _) T) nb L tr h = node0 T nb L h
trunk-node-zero (G.em (inj₂ (inj₁ _)) T) nb L tr h = node1 T nb L h
trunk-node-zero G.top nb L tr h = sym h

one≢zero : _≡_ {A = LF} (suc zero) zero → ⊥
one≢zero ()

no-trunk : (F : TopKeep) → Trunk (G.lc root₂ raw1 (TopKeep.t F) (TopKeep.g F)) → ⊥
no-trunk F (tt′ , tg) =
  one≢zero (trunk-node-zero (g (G.suc one) e₂) (proj₁ (branch-node one e₂)) (suc zero)
    (tg (G.suc one) e₂) (proj₂ (branch-node one e₂)))
  where open TopKeep F
```

读法 (判断，不是定理)。替代行只要把 `top` 的像取在 `Trunk` 里，链 `ξ₀ = top`，`ξₙ₊₁ = ξₙ + Φ(ξₙ)` 就留在 `Trunk` 里 (§2，前提是 `Φ` 保持 `Trunk`，未证)；
这时各链点的读回只含层号 0 的结点与原子 `tw 3`，折到第 0 层时除这个原子外只走第 0 层的链。`Trunk` 里只有 ℕ 极限与层号 0 的 Ω 极限，
没有层号 ≥ 1 的结点，所以闭项的读法留在 `tw 3` 的读法之上不远处，到不了 ψ₀(Ω_{Ω₁+1})；具体的界没有算。
