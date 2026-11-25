# YiOmNeg 第 2 项：保留模式下 `top : Raw (tw 2)` 的那一行

**判决：编译定理。** 最小记录 `TopKeep` (输出是主干槽位上的保留结点；它在坐标 `suc s` 的那一支读回成层号 `read0 s` 的结点) 推出 `LegalCopy`，
因而推出 `IrrSearch` 与 `IrrDecide`；在排中律的实例 `GdDec` 下有模型。分支函数若拿相关的守卫，同一条联系直接有实例 (`rel-branch-node`)。
否定的是 "在当前的块里无条件地写出这一行"；不否定守卫相关的写法，也不否定不保留各支的替代行 ([YiOmNegTrunk](YiOmNegTrunk.lagda.md))。接口 [YiOmIf](YiOmIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmNegTop where

open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiOmIf
open import OCF.Align.YiIrrNegWide using (IrrSearch)
open import OCF.Align.YiIrrNegWideDecide using (IrrDecide)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; br)
open import OCF.Align.YiOmNegSlot
```

## 1 最小记录

`Φ` 是 `Raw (tw 2)` 上目标为 `tw 2` 自己的折叠。`top` 读回是 `tw 3`，根是层号 0 的结点，在目标之下，保留在主干槽位 `root₂` 上：
下界是 1，分支函数 `g` 的类型由块定死，守卫无关。`tw 3` 的第 `suc s` 支是 `Ω̂ (suc (read0 s))`，一个层号 `read0 s` 的结点，
层号在 `tw 2` 的位置上 (守卫相关时是 `br (suc s) e (inj₁ tt)`)，所以它的像也保留。联系只写成 "像带嵌套证据，读回是层号 `read0 s` 的结点"：
不说槽位在哪一支，不说下界与分支。它被两种更强的写法推出：像是槽位上的保留结点 (`kept→reads`)；像是整支的嵌入 (`kid→reads`)。

```agda
ReadsNode : LF → Raw K₂ω → Set
ReadsNode L ξ = Σ (Nested K₂ω ξ) λ nb → NodeAt L (up K₂ω ξ nb)

record TopKeep : Set where
  field
    Φ : (ξ : Raw K₂ω) → .(Lgl K₂ω ξ) → .(Nested K₂ω ξ) → Raw K₂ω
    t : Raw K₂ω
    g : (η : R) → .(Gd zero raw1 η) → Raw K₂ω
    top-row : Φ G.top tt tt ≡ G.lc root₂ raw1 t g
    branch-node : ∀ s (e : Gd zero raw1 (G.suc s)) → ReadsNode (read0 s) (g (G.suc s) e)

kept→reads : ∀ L (y : Raw K₂ω) → Kept K₂ω L y → Nested K₂ω y → ReadsNode L y
kept→reads L .(G.lc r c t g) (r , refl , c , t , g , refl) nb =
  nb , upN-node K₂ω r c (proj₁ nb) (proj₁ (proj₂ nb))
    (up K₂ω t (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → up K₂ω (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))

kid→reads : ∀ s (e : Gd zero raw1 (G.suc s)) → ReadsNode (read0 s) (kid-rel (G.suc s) e G.top)
kid→reads s e = tt , refl
```

## 2 记录推出 `LegalCopy`

分支函数在守卫只无关地成立的坐标上也要交出一棵树。树是数据，读回是结点这件事无关地成立，`node₂-copy` 从树的头取出层号的拷贝。

```agda
top-keep→copy : TopKeep → LegalCopy
top-keep→copy F s e =
  node₂-copy (read0 s) (g (G.suc s) e) (proj₁ (branch-node s e)) (proj₂ (branch-node s e))
  where open TopKeep F

top-keep→irr-search : TopKeep → IrrSearch
top-keep→irr-search F = copy→irr-search (top-keep→copy F)

top-keep→irr-decide : TopKeep → IrrDecide
top-keep→irr-decide F = copy→irr-decide (top-keep→copy F)
```

## 3 记录不可反驳；守卫相关时联系有实例

`GdData` (由 `GdDec` 给出) 之下取分支为整支的嵌入。所以定理 §2 说的是 "这一行拿不到数据"，不是矛盾。
分支函数若拿相关的守卫 (块里孩子的写法)，联系无条件成立；它只是填不进结点的分支字段。

```agda
data→top-keep : GdData → TopKeep
data→top-keep d = record
  { Φ = λ ξ l nb → G.lc root₂ raw1 G.zero (λ η e → kid-rel η (d η e) G.top)
  ; t = G.zero
  ; g = λ η e → kid-rel η (d η e) G.top
  ; top-row = refl
  ; branch-node = λ s e → tt , refl }

dec→top-keep : GdDec → TopKeep
dec→top-keep dec = data→top-keep (dec→data dec)

g-rel : (η : R) → Gd zero raw1 η → Raw K₂ω
g-rel η e = kid-rel η e G.top

rel-branch-node : ∀ s (e : Gd zero raw1 (G.suc s)) → ReadsNode (read0 s) (g-rel (G.suc s) e)
rel-branch-node s e = tt , refl

-- 守卫相关时槽位上的保留结点也满足联系: 坐标 2 的那一支, 槽位是它的根.
e₂ : Gd zero raw1 (G.suc one)
e₂ = inj₂ (inj₁ refl) , tt , tt

slot-node₂ : Raw K₂ω
slot-node₂ = G.lc (br (G.suc one) e₂ (inj₁ tt)) G.zero G.zero (λ _ _ → G.zero)

slot-node₂-reads : ReadsNode (read0 one) slot-node₂
slot-node₂-reads = (tt , tt , tt , (λ _ _ → tt)) , refl
```
