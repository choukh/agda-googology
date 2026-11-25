# `LowSlot` 的量化域: 编译否定, 必要条件, 以及换成多目标系统后的终点

> 验收文件 (读记号). 判决: 编译定理. 否定: `YiWREnd` 的 `Inv₀`, `Inv₁` 之下 `LowSlot` 不成立 (`¬lowslot₀`, `¬lowslot₁`; 反例是层号 1 上的标准底, 上下文 K = 1, y = 0, 不在塔的根状态上, 读作不变式太宽). 必要条件: 对任何 `Inv`, `LowSlot` 推出每个带 `Inv` 的状态满足 `YiSOLow.SlotBd` (`slot-needed`).
> 条件定理: 域 `Domˢ` 含塔各项的 Ω 树, 根状态满足 `SlotBd` (`RootBd`), 加 `YiSOLow` 的三条前提与出口条件, 推出 `toL EBO-tree′ ≼ readRW EBOᴮ` (`End.ebo-endᴬ`; 不经 `Wire`, 第 0 层目标是多目标系统的一个目标). 域取全体时 `Wire.LowSlot` 在 `Inv₂` 下实填 (`Full.lowslot₂`, `ebo-end₂`), 塔第 1 项目标 `h₁ 1` 的实例是 `lowslot-tw1`.
> 判断 (未编译): 域取全体时 `RebRow` 在值上不成立 (材料 y 高于孩子层号的 Ω 树时只进第 0 层的尾项), 所以 `Full` 的前提读作不可满足, `Wire.LowSlot` 字面上对一切 y 的量化太宽; 要用的是带域的 `End`. 不给出什么: 三条前提, `RootBd` (n ≥ 1), 域, 出口条件都没有实填.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSOEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWPath using (Ok; Ok-tw; z≤; posW)
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiBSBase using (Rb; rb-tw)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiGIBlock using (chLᵍ)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiKVRel using (⊴r)
import OCF.Lean.YiLLLeafNeg as N
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_; l≼; ≼-trans)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiGTGen using (nextψ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiGIInst using (exitᵍ; gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiGIEnd using (hs; reference)
open import OCF.Lean.YiGLDom using (dom-top; dom-keel)
open import OCF.Lean.YiWRZero using (Stᶻ; Φᶻ; stepᶻ; slotFold)
open import OCF.Lean.YiWREnd
open import OCF.Lean.YiSOLow
open ExSuff gradedᵍ domsᵍ using (Exit₀; Keel⁻)

stˢ : ∀ {a} → Stᶻ a → Stˢ a
stˢ (o , r , B , β) = o , r , B
```

## `Inv₀`, `Inv₁` 之下 `LowSlot` 不成立

层号 1 (`nd sS (λ _ → zero)`), 标准底, 底值 `next⁺ 1`, 上下文 K = 1: `Inv₀` 与 `Inv₁` 成立 (前提可满足). 槽位层是第 0 层, 读法只能是空; y = 0 时 `LowSlot` 给出 ψ₀(1) 对着树 1 的关系, 而对着树 1 的参照都不高于 1 (`YiLLLeafNeg.Fin.one-ref`).

```agda
module Neg where
  a₁ : L
  a₁ = nd sS (λ _ → zero)

  s₁ : Stᶻ a₁
  s₁ = (tt , λ _ → tt) , (tt , λ _ → tt) , B₀ a₁ , O.next⁺ (O.Ωt zero)

  K₁ : E.T
  K₁ = E.natT 1

  inv₀ : Inv₀ s₁ K₁
  inv₀ = nextψ zero [] [] (E.natT 1) refl (O.Ωt zero) (H.pos⁰ (suc zero) ◃s)

  inv₁ : Inv₁ s₁ K₁
  inv₁ = inv₀ , λ i u → ⊴r

  p₁ : Pos a₁
  p₁ = inj₂ (tt , inj₁ tt)

  bad : GR.R zero (E.ψ [] (K₁ ++ []) ∷ []) (suc zero) → ⊥
  bad m = N.conflict (N.one<ψ [] E.[]<) (N.Fin.one-ref m)

  ¬lowslot₀ : W₀.LowSlot → ⊥
  ¬lowslot₀ ls = bad (ls s₁ K₁ inv₀ p₁ {κ = []} (GR.c0 refl) {η = []} {y = zero} H.mz)

  ¬lowslot₁ : W₁.LowSlot → ⊥
  ¬lowslot₁ ls = bad (ls s₁ K₁ inv₁ p₁ {κ = []} (GR.c0 refl) {η = []} {y = zero} H.mz)

open Neg public using (¬lowslot₀; ¬lowslot₁)
```

## 必要条件

`LowSlot` 在 y = 0 上就是 `SlotBd`; 所以能用的 `Inv` 必须推出它.

```agda
module Needed (Inv : ∀ {a} → Stᶻ a → E.T → Set)
    (inv-zero : ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) (β : O.Tr⁺ zero) {K} → Inv (o , r , B , β) K → GR.R zero (E.ψ [] K ∷ []) (proj₁ β))
    (inv-step : ∀ {a} (s : Stᶻ a) K → Inv s K → (c : CH a) → ∀ {t x} → GR.R a t x
              → GR.R zero (apᴱ K t) (proj₁ (Φᶻ s x)) → Inv (stepᶻ s c x) (K ++ t))
    (inv-root : ∀ n → Inv (rootᴮ n) []) where
  open Wire Inv inv-zero inv-step inv-root

  slot-needed : LowSlot → ∀ {a} (s : Stᶻ a) K → Inv s K → SlotBd (stˢ s) K
  slot-needed ls {a} (o , r , B , β) K inv p {κ} nu =
    subst (λ z → GR.R (at a p) (E.ψ κ z ∷ []) (proj₁ (B (at a p) (posW a p)))) (++-identityʳ K)
      (ls (o , r , B , β) K inv p nu {η = []} {y = zero} (mz′ a))
```

## 终点: 多目标系统直接给出

根状态 `rootᴮ n` 去掉底值, 目标第 0 层, 路径 `z≤`, 底值 `betaᴮ n`, 目标读法空, 上下文空: `lowAll` 的这一份就是 `Wire.folded`. `RootBd`: 根状态的每个槽位上, 底 `baseᴮ n` 支配该槽位每个读法 κ 的 Ω_κ (ψ_κ(0)).

```agda
rootˢ : ∀ n → Stˢ (tw n)
rootˢ n = Ok-tw n , rb-tw n , baseᴮ n

RootBd : Set
RootBd = ∀ n → SlotBd (rootˢ n) []

root-bd0 : SlotBd (rootˢ 0) []
root-bd0 ()

module End (𝒟 : Domˢ) where
  open Domˢ 𝒟
  open Sys 𝒟

  RootIn : Set
  RootIn = ∀ n → Dm (rootˢ n) (proj₁ (O.Ωt (tw n)))

  module _ (nm : NodeMis) (sr : SelfRow) (rr : RebRow) (rb : RootBd) (ri : RootIn) where
    open Main nm sr rr

    folded : ∀ n → GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)
    folded n = lowAll (tw n) (Ok-tw n) (rb-tw n) (baseᴮ n) (good-tw n) [] (rb n) (dom-top (dom-keel n)) (ri n)
      zero (z≤ (tw n)) (betaᴮ n) [] (GR.c0 refl) (H.pos⁰ (proj₁ (betaᴮ n)) (proj₂ (betaᴮ n)))

    ebo-endᴬ : (∀ n → H.Exᴴ (folded n)) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
    ebo-endᴬ ex = ≼-trans reference (l≼ (λ n → ≼-trans (Exit₀.exit exitᵍ (folded n) (ex n) (hs n)) (upperᴮ n)))
```

## 域取全体: `Wire.LowSlot` 实填

`Inv₂`: 第 0 层的底条件, `Good`, `SlotBd`. `inv-step` 的槽位一项是 `slot-step`, 即 x 在孩子各槽位上的 `Keepᵗ`. 这一节的三条前提对一切树陈述 (判断: `RebRow` 那时在值上不成立, 见文首).

```agda
module Full (nm : Sys.NodeMis allˢ) (sr : Sys.SelfRow allˢ) (rr : Sys.RebRow allˢ) (rb : RootBd) where
  open Sys.Main allˢ nm sr rr

  Inv₂ : ∀ {a} → Stᶻ a → E.T → Set
  Inv₂ {a} (o , r , B , β) K = GR.R zero (E.ψ [] K ∷ []) (proj₁ β) × Good a r × SlotBd (o , r , B) K

  inv₂-step : ∀ {a} (s : Stᶻ a) K → Inv₂ s K → (c : CH a) → ∀ {t x} → GR.R a t x
    → GR.R zero (apᴱ K t) (proj₁ (Φᶻ s x)) → Inv₂ (stepᶻ s c x) (K ++ t)
  inv₂-step {nd s h} (o , r , B , β) K (_ , gd , bd) c rx q =
    q , good-ch s h r gd c , slot-step (o , r , B) K bd c (lowAll (nd s h) o r B gd K bd rx tt)

  inv₂-root : ∀ n → Inv₂ (rootᴮ n) []
  inv₂-root n = H.pos⁰ (proj₁ (betaᴮ n)) (proj₂ (betaᴮ n)) , good-tw n , rb n

  module W₂ = Wire Inv₂ (λ o r B β bd → proj₁ bd) inv₂-step inv₂-root

  lowslot₂ : W₂.LowSlot
  lowslot₂ (o , r , B , β) K (_ , gd , bd) p nu ry = core o r B gd K bd p nu ry tt

  ebo-end₂ : W₂.ExitCondition (W₂.chain←slot lowslot₂) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ
  ebo-end₂ = W₂.ebo-endˢ lowslot₂
```

塔第 1 项, 目标 `h₁ 1` (孩子 1 的层号, 即层号 1), 路径 `inc 1 self`: `LowSlot` 与 `inv-step` 在这一格上的实例.

```agda
  p11 : Pos (tw 1)
  p11 = inj₂ (suc zero , inj₁ tt)

  at-p11 : at (tw 1) p11 ≡ nd sS (λ _ → zero)
  at-p11 = refl

  lowslot-tw1 : ∀ {κ} → GR.Nu (tw 1) p11 κ → ∀ {η y} → GR.R (tw 1) η y
    → GR.R (at (tw 1) p11) (E.ψ κ ([] ++ η) ∷ []) (slotFold (rootᴮ 1) p11 y)
  lowslot-tw1 nu ry = lowslot₂ (rootᴮ 1) [] (inv₂-root 1) p11 nu ry

  step-tw1 : (c : Tr zero) → ∀ {t x} → GR.R (tw 1) t x → GR.R zero (apᴱ [] t) (proj₁ (Φᶻ (rootᴮ 1) x))
    → Inv₂ (stepᶻ (rootᴮ 1) c x) ([] ++ t)
  step-tw1 c rx q = inv₂-step (rootᴮ 1) [] (inv₂-root 1) c rx q
```
