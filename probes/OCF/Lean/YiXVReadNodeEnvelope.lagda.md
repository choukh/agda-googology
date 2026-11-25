# YiXVReadNodeEnvelope
> 验收文件。档位：编译定理。节点下标树内的实际目标不能保留，原折叠在这些目标上展开为对角链。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadNodeEnvelope where
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVLvlLiteral as Literal
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadAffineNodeModels as Model
model : S.zero P.≤ᵀ S.zero
model = P.here
no-retain : ∀ {y i : S.Tr S.zero} → y P.≤ᵀ i → T.lvl i L.≺ᴵ T.lvl y → ⊥
no-retain P.here v = L.≺ᴵ-irrefl v
no-retain {y} {i} (P.below p) v = L.clash₁ (L.≅ᴵ-refl (T.lvl y)) (L.≅ᴵ-refl (T.lvl i))
  (L.via (L.≅ᴵ-refl (T.lvl y)) (Literal.step (P.raw p))) v

module Node {κ} (i : S.Tr S.zero) (q : T.lvl i L.<ᴵ κ)
  (f : L.U (T.lvl i) (L.<→◃ q) → L.Ordᶜ κ) where
  high : L.Ordᶜ (T.lvl i) → L.Ordᶜ κ
  high X = f (L.into (L.<→◃ q) X)
  P : L.Ordᶜ (T.lvl i) → L.Ordᶜ (T.lvl i)
  P X = L.ψ q (λ r → r) (high X)
  d : ℕ → L.Ordᶜ (T.lvl i)
  d = iter P (L.Ω (T.lvl i))
  η₀ : L.Ordᶜ (T.lvl i) → L.Ordᶜ L.zero
  η₀ X = L.ψ⁰ (high X)
  bot-shape : L.ψ⁰ (L.limᵢ q f) ≡ L.lim (λ n → η₀ (d n))
  bot-shape = refl
  module Target {y a} (pc : T.lvl y L.<ᴵ a) (ρ : L.Simᴵ κ a) where
    η : L.Ordᶜ (T.lvl i) → L.Ordᶜ (T.lvl y)
    η X = L.ψ pc ρ (high X)
    diagonal : y P.≤ᵀ i → L.ψ pc ρ (L.limᵢ q f) ≡ L.lim (λ n → η (d n))
    diagonal t with L.<ᴵ-dec (ρ q) pc
    ... | injᵃ v = ⊥-elim (no-retain t v)
    ... | injᵇ v = refl
    ... | injᶜ e = refl

module Actual = Node S.zero L.zero Model.f
module Target = Actual.Target (L.suc L.zero) (λ q → L.suc q)
actual : L.ψ (L.suc L.zero) (λ q → L.suc q) (L.limᵢ L.zero Model.f) ≡
  L.lim (λ n → Target.η (Actual.d n))
actual = Target.diagonal model
```
