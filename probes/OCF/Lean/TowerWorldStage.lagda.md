# 含高层坐标的具体实例

对任意旧种类结构 S 和固定低层世界 w，加入一个坐标为 HB S 的新种类。
种类与坐标与 `step S` 相同，唯可入改成尾部 B ⊲ c 并要求 c 合法。
不是把 `KS.step` 的 Bd 原样冒充此接口。旧种类坐标仍按 w 的界可入。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerWorldStage where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerWorldIf

module Stage (S : KS) (w : Wd S) where
  K′ = K S ⊎ ⊤
  E′ : K′ → Set
  E′ (inj₁ k) = E S k
  E′ (inj₂ _) = HB S
  L′ : ∀ k → E′ k → Set
  L′ (inj₁ k) c = Bd S k c w
  L′ (inj₂ _) c = LgB c
  A′ : HB S → ∀ k → E′ k → Set
  A′ B (inj₁ k) c = Bd S k c w
  A′ B (inj₂ _) c = (B ⊲[ w ] c) × LgB c
  nx : ∀ B k c → A′ B k c → HB S
  nx B (inj₁ k) c a = B
  nx B (inj₂ _) c a = hs c
  admit-legal : ∀ {B k c} → A′ B k c → L′ k c
  admit-legal {k = inj₁ k} a = a
  admit-legal {k = inj₂ _} a = proj₂ a
  signature : Signature
  signature = record
    { World = HB S ; _≤w_ = λ a b → a ⊲[ w ] b
    ; reflw = λ a → hself ; transw = ⊲ᴮ-tr
    ; Kind = K′ ; Coord = E′ ; LegalCoord = L′
    ; Admit = A′ ; admitted-legal = admit-legal ; next = nx }
  grow : ∀ B k c (a : A′ B k c) → B ⊲[ w ] nx B k c a
  grow B (inj₁ k) c a = hself
  grow B (inj₂ _) c a = hsuc (proj₁ a)
  next-up : NextUp signature
  next-up = record { up = grow }
  open Trees signature
  coordinate-tree : ∀ {B} → HB S → Tree B
  coordinate-tree hz = zero
  coordinate-tree (hs a) = suc (coordinate-tree a)
  coordinate-tree (hl f) = lim (λ n → coordinate-tree (f n))
  coordinate-tree (hΩ k g) = node (inj₁ k) (λ v p c a → coordinate-tree (g c))
  high-node : ∀ {B} → Tree B
  high-node = node (inj₂ tt) (λ v p c a → coordinate-tree c)
```

`high-node` 不是常值分支：其坐标里的 Ω-节点被保留为旧种类节点。
取 S = step S⊥ 时，坐标已能含 Ω-节点，而非只有可数树构造子。
本实例仍固定低层世界 w；不宣称解决 `frozen-no-pos` 指出的塔中低层
世界移动，也没有折叠或值验收。跨 step 保留节点仍需把更高层坐标
反向读到更低层坐标，`Keep.coordinate` 没有因此自动产生。
