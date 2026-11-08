# 第一typed层的精确验收关系

验收专用，先有已编译的GeneralOmegaSeededRun树侧闭包再建立本桥。
Read不是任意函数同余：Ω字段显式消费可数坐标的结构对应。它只比较
固定类型中的值，不选择层或更新槽，不增添裸下标判等律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteTypedIf where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaSeededIf using (module Prototype)
import OCF.Lean.GeneralOmegaSeededRun
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

U = step S⊥
Ωtree : HB U
Ωtree = hΩ (inj₂ tt) up
module P = Prototype U Ωtree
Ω₁ : L.Ordᶜ (L.suc L.zero)
Ω₁ = L.Ω (L.suc L.zero)
stepᴵ : L.Ordᶜ (L.suc L.zero) → L.Ordᶜ (L.suc L.zero)
stepᴵ a = L.ψ {i = L.suc L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero (λ q → L.suc q) a
old-chain : ℕ → L.Ordᶜ (L.suc L.zero)
old-chain = iter stepᴵ Ω₁

data Read : L.Ordᶜ (L.suc L.zero) → HB U → Set where
  rz : Read L.zero hz
  rs : ∀ {a b} → Read a b → Read (L.suc a) (hs b)
  rl : ∀ {f g} → (∀ n → Read (f n) (g n)) → Read (L.lim f) (hl g)
  ro : ∀ {f g} → (∀ x c → B.read c L.≅ x → Read (f x) (g c)) →
    Read (L.limᵢ L.zero f) (hΩ (inj₂ tt) g)
  ru : ∀ {x c} → B.read c L.≅ x → Read (L.up L.zero x) (up c)

floor : Read Ω₁ Ωtree
floor = ro (λ x c p → ru p)

read : HB U → L.Ordᶜ (L.suc L.zero)
read hz = L.zero
read (hs a) = L.suc (read a)
read (hl f) = L.lim (λ n → read (f n))
read (hΩ (inj₁ ()) g)
read (hΩ (inj₂ tt) g) = L.limᵢ L.zero (λ x → read (g (B.forget x)))
```

Ωtree正是原第一层地板，floor给非空且含Ω的实例。old-chain的起点
是Ω₁，迭代没有累加；不与seed1的Reify.Orbit混同。后续必须证明
Read的语义及Typed保持，才可把此关系当作原记号的验收桥。
