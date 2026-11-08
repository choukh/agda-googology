# 读回包的编码与后继闭包

本篇补上 `UniformReaderStep` 没有交付的编码闭包。泛目标节点构造是显式
字段，不从整体编码函数反推。编码按原树结构递归；后继节点把自身读回层
的输出作为 `HB T` 坐标送回原分支。有限初值来自既有 `trKg`，不声称
极限层、全部事件迁回、内部 View 或序数值验收已完成。
`render` 的路径须对所有世界成立；本篇没有把它扩大为仅在当前世界
准入的 Ω 路径。该全世界范围可由下面的有限初值与后继闭包实填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformReaderReify where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
  using (Ht; D; Wd₂; LgW₂; n0; n1; _⨾_; nl; ni; ss; outS)
  renaming (Sk to move)
open import OCF.Align.LvRdEmb
open import OCF.Align.LvRdPkg using (NdI; pkgF; trKg)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldRead using (ly)
open import OCF.Align.FamFoldLift using (≤r)
import OCF.Align.UniformReaderStep as Old

record RenderingReader (T : KS) (L : Ht) : Set₁ where
  field
    nodes : ∀ {V} → Emb T V → NdI V L
    render : ∀ {J} → (∀ {W} → L ⊲[ W ] J) → (κ : K T) →
             (E T κ → (W : Wd₂) → D J W) → (W : Wd₂) → D J W

module Read {T L} (P : RenderingReader T L) where
  open RenderingReader P

  encodeAt : ∀ {J} → (∀ {W} → L ⊲[ W ] J) → HB T → (W : Wd₂) → D J W
  encodeAt p hz W = n0
  encodeAt p (hs a) W = encodeAt p a W ⨾ n1
  encodeAt p (hl f) W = nl (λ n → encodeAt p (f n) W)
  encodeAt p (hΩ κ g) W = render p κ (λ e W′ → encodeAt p (g e) W′) W

  context : Old.ContextReader T L
  context = record { nodes = nodes ; encode = λ {W} a → encodeAt hself a W }

  read : ∀ {W} → LgW₂ W → HB T → D L W → HB T
  read = OCF.Align.LvRdPkg.RG.rdG (nodes (idE T))

  legal : ∀ {W} (lW : LgW₂ W) b d → LgB b → LgB (read lW b d)
  legal = OCF.Align.LvRdPkg.RG.lgG (nodes (idE T))

module Successor {T L} (P : RenderingReader T L) where
  render : ∀ {J} → (∀ {W} → hs L ⊲[ W ] J) → (κ : K (step T)) →
           (E (step T) κ → (W : Wd₂) → D J W) → (W : Wd₂) → D J W
  render p (inj₁ κ) g W = RenderingReader.render P
    (⊲ᴮ-tr (hsuc hself) p) κ g W
  render p (inj₂ tt) g W = ni (move (ss hself) p)
    (λ {W′} _ lW′ y → g (Read.read P lW′ hz (outS (move (ss hself) p) y)) W′)

  next : RenderingReader (step T) (hs L)
  next = record { nodes = Old.Extend.next (Read.context P) ; render = render }
```

## 实填初值及可反复调用的结构一步

这里 `family` 的后继确实调用新 `Successor.next`，不是每层重新调用旧包。
所有种类的编码均由同一 `encodeAt` 递归。

```agda
finite-base : ∀ n → RenderingReader (Sk (suc n)) (ly (suc (suc n)))
finite-base n = record
  { nodes = Old.ContextReader.nodes (Old.finite n)
  ; render = λ p κ g W → trKg (pkgF n) ≤r κ (move (ss hself) p) g W }

family : ∀ n → RenderingReader (Sk (suc n)) (ly (suc (suc n)))
family zero = finite-base zero
family (suc n) = Successor.next (family n)

encoded : ∀ n → HB (Sk (suc n)) → (W : Wd₂) → D (ly (suc (suc n))) W
encoded n = Read.encodeAt (family n) hself

round : ∀ n {W} → LgW₂ W → HB (Sk (suc n)) → HB (Sk (suc n))
round n {W} lW a = Read.read (family n) lW hz (encoded n a W)

round-legal : ∀ n {W} (lW : LgW₂ W) a → LgB (round n lW a)
round-legal n {W} lW a = Read.legal (family n) lW hz (encoded n a W) tt

round-one : ∀ n {W} (lW : LgW₂ W) → round n lW (hs hz) ≡ hs hz
round-one n lW = refl

-- 新种类编码的完整方程。原 g 接收读回值，不取固定底支。
new-equation : ∀ {T L} (P : RenderingReader T L)
  (g : HB T → HB (step T)) W →
  Read.encodeAt (Successor.next P) hself (hΩ (inj₂ tt) g) W ≡
  ni (ss hself) (λ {W′} _ lW′ y →
    Read.encodeAt (Successor.next P) hself (g (Read.read P lW′ hz y)) W′)
new-equation P g W = refl

-- 与已编译的后继读回实接：全部原回调都读取本包生成的编码。
feedback : ∀ {T L} (P : RenderingReader T L) {W} (lW : LgW₂ W) (b : HB (step T))
  (u : ∀ {W′} → W OCF.Align.HtTowerFTree.≤ W′ → LgW₂ W′ → D L W′ → D (hs L) W′) →
  Read.read (Successor.next P) lW b (ni (ss hself) u) ≡
  nodeH (idE (step T)) b (λ x h →
    Read.read (Successor.next P) lW h
      (u OCF.Align.HtTowerFTree.≤rf lW (Read.encodeAt P hself x W)))
feedback P lW b u = refl
```

`round-legal` 是实际编码再读回的合法性，不是 `round a` 与 `a` 的值同一。
未来世界仍是原双槽 `Wd₂`；全种类事件的生成和迁回相容是独立未填任务。
