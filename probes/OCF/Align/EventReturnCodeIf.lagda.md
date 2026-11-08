# 迁回实际输入编码：逐枝合同

`Code` 是原 D₁ 的子语言关系，不是任意高阶函数的外延性。
两边可在不同历史表，底世界 a 相同；κ 分支比较只用同一个
`a ⊲ c` 证据与同一个合法证明。没有判两个裸高度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCodeIf where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (D₁; toD₁; drp₁; rd₁)

data Shape {S : KS} : HB S → HB S → Set where
  sz : Shape hz hz
  ss : ∀ {a b} → Shape a b → Shape (hs a) (hs b)
  sl : ∀ {f g} → (∀ n → Shape (f n) (g n)) → Shape (hl f) (hl g)
  so : ∀ {κ f g} → (∀ e → Shape (f e) (g e)) → Shape (hΩ κ f) (hΩ κ g)

data Code (a : A) (H H′ : Hist) : D₁ (a , H) → D₁ (a , H′) → Set where
  cz : Code a H H′ n0 n0
  co : Code a H H′ n1 n1
  ca : ∀ {x y x′ y′} → Code a H H′ x x′ → Code a H H′ y y′ →
       Code a H H′ (x ⨾ y) (x′ ⨾ y′)
  cl : ∀ {f g} → (∀ n → Code a H H′ (f n) (g n)) → Code a H H′ (nl f) (nl g)
  ck : ∀ {u : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H)}
         {v : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H′)} → (∀ {c} (p : a ⊲ c) (lc : Lg c) → Code c H H′ (u p lc) (v p lc)) →
       Code a H H′ (nκ tt u) (nκ tt v)

record EncodedMigration : Set₁ where
  field
    encoded : ∀ {a H H′} x → Code a H H′ (toD₁ x) (toD₁ x)
    migrated : ∀ {a H H′ H″ x y} → Code a H H′ x y → Code a H″ H′ (drp₁ x) y
    observed : ∀ {a H H′ x y b b′} → (la : Lg a) → Code a H H′ x y → Shape b b′ →
               Shape (rd₁ (la , tt) b x) (rd₁ (la , tt) b′ y)
```

`observed` 只消费显式 Code，不允许由普通读回同值反推任意 continuation
相容。后续若把它喂入 ni，仍须原 ni 分支自身的关系保持证明。
