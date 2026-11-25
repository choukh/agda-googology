# YiCarry V1：Raw 的伴随下界证书

`LglB k a` 同时保存原 `Lgl k a` 和 `Nested k a`：后者要求 Raw 中
每个 lc 的下界合法，并递归检查下界本身、第一支、全部原守卫分支及
em 的低层内容。它不检查层参数 k 的树，也不把 top 展开。
选择同时带 Lgl，是因为链点还须过原 Gd；这样合法性和新增证据可分别投影，
无需用嵌套下界条件重建原合法性。原块不读这个伴随证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryBounds where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import OCF.Align.LevelFixCore
  using (LF; Raw; Pre; Low; Kid; KidR; Lgl)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiK2Base as K

LglLow : (k : LF) (r : Pre k) → Low k r → Set
LglLow (F.suc k) (inj₁ _) c = Lgl k c
LglLow (F.suc k) (inj₂ r) c = LglLow k r c
LglLow (F.lim f) (n , r) c = LglLow (f n) r c
LglLow (F.lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c = Lgl k c
LglLow (F.lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c = LglLow k r c
LglLow (F.lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c = LglLow t₀ r c
LglLow (F.lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c =
  LglLow (g₀ η e) r c

Nested : (k : LF) → Raw k → Set
NestedLow : (k : LF) (r : Pre k) → Low k r → Set
NestedKid : (k : LF) (i : Kid k) → KidR k i → Set

Nested k G.zero = ⊤
Nested k (G.suc a) = Nested k a
Nested k (G.lim f) = ∀ n → Nested k (f n)
Nested k (G.lc r c t g) =
  LglLow k r c × NestedLow k r c × Nested k t ×
  (∀ η e → Nested k (g η e))
Nested k (G.em i a) = NestedKid k i a
Nested k G.top = ⊤

NestedLow (F.suc k) (inj₁ _) c = Nested k c
NestedLow (F.suc k) (inj₂ r) c = NestedLow k r c
NestedLow (F.lim f) (n , r) c = NestedLow (f n) r c
NestedLow (F.lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c = Nested k c
NestedLow (F.lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c = NestedLow k r c
NestedLow (F.lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c = NestedLow t₀ r c
NestedLow (F.lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c =
  NestedLow (g₀ η e) r c

NestedKid (F.suc k) _ a = Nested k a
NestedKid (F.lim f) n a = Nested (f n) a
NestedKid (F.lc k c t g) (inj₁ _) a = Nested k a
NestedKid (F.lc k c t g) (inj₂ (inj₁ _)) a = Nested t a
NestedKid (F.lc k c t g) (inj₂ (inj₂ (η , e))) a = Nested (g η e) a

LglB : (k : LF) → Raw k → Set
LglB k a = Lgl k a × Nested k a

top-B : ∀ k → LglB k G.top
top-B k = tt , tt

cO-nested : ∀ k → Nested k (V.cO k)
cO-nested F.zero = tt
cO-nested (F.suc k) = tt
cO-nested (F.lim f) = tt
cO-nested (F.lc k c t g) = tt

cO-B : ∀ k → LglB k (V.cO k)
cO-B k = V.Lgl-cO k , cO-nested k

raw0-nested : ∀ (a : Raw F.zero) → Nested F.zero a
raw0-nested G.zero = tt
raw0-nested (G.suc a) = raw0-nested a
raw0-nested (G.lim f) = λ n → raw0-nested (f n)
raw0-nested (G.lc () c t g)
raw0-nested (G.em () a)
raw0-nested G.top = tt

add-B : ∀ a b → LglB F.zero a → LglB F.zero b →
  LglB F.zero (K._+ʳ_ a b)
add-B a b (la , ba) (lb , bb) =
  K.add-legal a b la lb , raw0-nested (K._+ʳ_ a b)

ψᶜ-B : ∀ a → LglB F.zero a → LglB F.zero (K.ψᶜ a)
ψᶜ-B a (la , ba) = K.ψᶜ-legal a la , raw0-nested (K.ψᶜ a)
```

第 0 层 Raw 没有 lc／em 槽位，故嵌套条件对每个 Raw 0 自动成立；
加法与 ψᶜ 的新条件保持由此给出，原合法性部分仍用已有保持定理。
这些是全域定理，不是有限测试，也没有给高层的 ψ 定义。

## 原 Chain 的伴随证书由更新规则保持

沿原 Chain 的 next 与 chain 证明，不另给一条假定全部点都好的列。
lawful／monotone 是原 Chain 的显式前提；规范恒等分支有旧实例。

```agda
module ChainB (c : K.R)
  (body : (η : K.R) → F.Gd F.zero c η → K.R)
  (lawful : ∀ η e → Lgl F.zero (body η e))
  (monotone : ∀ η e η′ e′ → F.Gd F.zero η η′ →
    F.Cp F.zero (body η e) (body η′ e′)) where

  module Old = K.Chain c body lawful monotone

  next-B : ∀ (p : K.Point c) → LglB F.zero (proj₁ p) →
    LglB F.zero (proj₁ (Old.next p))
  next-B p@(η , e) b =
    add-B η (Old.out p) b
      (ψᶜ-B (body η e) (lawful η e , raw0-nested (body η e)))

  chain-B : ∀ (initial : K.Point c) → LglB F.zero (proj₁ initial) →
    ∀ n → LglB F.zero (proj₁ (Old.chain initial n))
  chain-B initial b zero = b
  chain-B initial b (suc n) = next-B (Old.chain initial n) (chain-B initial b n)
```
