# 读记号的旧名字落到五参数接口

> 验收文件 (读记号). 判决: 编译定理, 无前提. 分级实例取 `YiMIGraded.gradedᴹ` 在换基折叠上、上下文 (头 κ, 前缀 K) 的取值 (读法域 `Rd` 与底的条件 `Bd` 任意; `Rd = GR.Rd`, `Bd = Bdᴱ` 时就是 `gradedᴱ`). `YiWREnd.Wire.LowSlot` 与 "槽位点上的 `LowAt`" 互推 (`slot→`, `→slot`); `YiSOLow.Keepᵗ` 的全称形式与 "一切 (目标, 路径, 底值, 头) 上的 `LowAt`" 互推 (`keepᵗ→`, `→keepᵗ`); `Main.lowAll` 是 `Low Iˢ Dˢ` (`lowAll→`), `Main.core` 是它在槽位点上的取值 (`core′`). 主线分级实例的 `LowKeep` 是朝第 0 层系统的 `KeepSys` 的限制 (`zero→lowKeep`), 由 `W₀.ChainRel` 给出 (`chain→lowKeep`), 经孩子的路径不在它的 `Wl` 里 (`wl-inc`, 所以 `YiBLFold.Pack` 一族不是它的实例); `YiSOUp.UpQ` 与上折的 `Hold` 互推 (`upQ→`, `→upQ`).
> 不给出什么: 不证 `LowSlot` 或 `lowAll` 的前提; `lowAll` 推出 `LowSlot` 已在 `YiSOEnd.Full.lowslot₂`, 这里不重证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMIRead where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWOps using (Tr⁺)
open import OCF.Lean.YiRWPath using (Ok; _≤_; posW; inc)
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiBSBase using (Rb)
import OCF.Lean.YiBSFold as BS
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiGIBlock using (blkᵍ)
open import OCF.Lean.YiAbsGIface using (Doms)
open import OCF.Lean.YiBLFold using (foldᴮ; rowsᴮ; Bsᴮ)
open import OCF.Lean.YiWRZero using (Stᶻ; Φᶻ; stepᶻ; slotFold)
open import OCF.Lean.YiWREnd using (module Wire; rootᴮ; apᴱ)
open import OCF.Lean.YiSOLow using (Stˢ; Keepᵗ; SlotBd; Good; Domˢ; module Sys; nu-rd)
open import OCF.Lean.YiMIGraded using (gradedᴹ)
open import OCF.Lean.YiMIIface
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiWREnd using (gradedᴮ; domsᴮ; weakᴮ; limᴮ; nodeᴮ; zeroᴮ; succᴮ; embᴮ; leRᴮ; genᴮ; Inv₀; module W₀)
open import OCF.Lean.YiGIInst using (Wlᵍ; wz)
open import OCF.Lean.YiMIConv using (module ToZero)
open import OCF.Lean.YiSOUp using (UpQ; UpMis; module UpAll)
```

## 实例

```agda
module RC (Rd : L → E.T → Set) (Bd : ∀ {ℓ j} → Bsᴮ ℓ → j ≤ ℓ → Tr⁺ j → E.T × E.T → Set) (𝔻 : Doms blkᵍ foldᴮ) where
  open MI (gradedᴹ foldᴮ rowsᴮ proj₁ GR.Nu Rd (E.T × E.T) proj₁ proj₂ Bd) 𝔻 public

  stᶻ : ∀ {a} → Stᶻ a → Bsᴮ a
  stᶻ (o , r , B , β) = o , r , B
```

## `LowSlot`

五个参数: 目标是槽位层 `at a p`, 路径 `posW a p`, 底值是底在槽位层上的值, 上下文 (κ, K) 的头是槽位读法 κ (`Nu a p κ`), 域全体; 不变式 `Inv s K` 与 `Nu a p κ`. 状态的第 0 层底值不进这一点的像.

```agda
  module Slot (Inv : ∀ {a} → Stᶻ a → E.T → Set)
      (inv-zero : ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) (β : Tr⁺ zero) {K} → Inv (o , r , B , β) K → GR.R zero (E.ψ [] K ∷ []) (proj₁ β))
      (inv-step : ∀ {a} (s : Stᶻ a) K → Inv s K → (c : CH a) → ∀ {t x} → GR.R a t x
                → GR.R zero (apᴱ K t) (proj₁ (Φᶻ s x)) → Inv (stepᶻ s c x) (K ++ t))
      (inv-root : ∀ n → Inv (rootᴮ n) []) where
    open Wire Inv inv-zero inv-step inv-root using (LowSlot)

    SlotLow : Set
    SlotLow = ∀ {a} (s : Stᶻ a) K → Inv s K → (p : Pos a) → ∀ {κ} → GR.Nu a p κ
      → LowAt (stᶻ s) (posW a p) (proj₂ (proj₂ (stᶻ s)) (at a p) (posW a p)) (κ , K) ⊤ᴰ

    slot→ : LowSlot → SlotLow
    slot→ ls (o , r , B , β) K iv p nu _ ry = ls (o , r , B , β) K iv p nu ry

    →slot : SlotLow → LowSlot
    →slot sl (o , r , B , β) K iv p nu ry = sl (o , r , B , β) K iv p nu tt ry
```

## `Keepᵗ` 与 `lowAll`

`Keepᵗ` 对状态与前缀 K 全称量化目标 j, 路径 w, 底值 β, 头 κ, 不变式是 `Rd j κ` 与 "底值对着 ψ_κ(K)". `KeepLow st K D`: 同一组点上的 `LowAt`, 域 D.

```agda
  KeepLow : ∀ {a} → Stˢ a → E.T → (Tr a → Set) → Set
  KeepLow {a} st K D = ∀ j (w : j ≤ a) (β : Tr⁺ j) κ → GR.Rd j κ → GR.R j (E.ψ κ K ∷ []) (proj₁ β)
    → LowAt st w β (κ , K) D

  keepᵗ→ : ∀ {a} (st : Stˢ a) K (D : Tr a → Set) → (∀ {t x} → GR.R a t x → D x → Keepᵗ st K t x) → KeepLow st K D
  keepᵗ→ (o , r , B) K D kt j w β κ rd rβ d ry = kt ry d j w β κ rd rβ

  →keepᵗ : ∀ {a} (st : Stˢ a) K (D : Tr a → Set) → KeepLow st K D → ∀ {t x} → GR.R a t x → D x → Keepᵗ st K t x
  →keepᵗ (o , r , B) K D kl ry d j w β κ rd rβ = kl j w β κ rd rβ d ry
```

`lowAll`: 不变式 `Iˢ` = `Good` × `SlotBd` × 头的读法 × 底值的界, 域 `Dm`. `core` 是槽位点上的取值 (`SlotBd` 给出底值的界, `nu-rd` 给出读法).

```agda
  module All (𝒟 : Domˢ) (nm : Sys.NodeMis 𝒟) (sr : Sys.SelfRow 𝒟) (rr : Sys.RebRow 𝒟) where
    open Domˢ 𝒟 using (Dm)
    open Sys.Main 𝒟 nm sr rr using (lowAll; core)

    Iˢ : Pt → Set
    Iˢ π = Good (src π) (proj₁ (proj₂ (bs π))) × SlotBd (bs π) (proj₂ (cx π))
         × GR.Rd (tgt π) (proj₁ (cx π)) × GR.R (tgt π) (E.ψ (proj₁ (cx π)) (proj₂ (cx π)) ∷ []) (proj₁ (bv π))

    Dˢ : (π : Pt) → Tr (src π) → Set
    Dˢ π = Dm (bs π)

    lowAll→ : Low Iˢ Dˢ
    lowAll→ (pt {src = a} {tgt = j} (o , r , B) w β (κ , K)) (gd , bd , rd , rβ) d ry = lowAll a o r B gd K bd ry d j w β κ rd rβ

    core→ core′ : ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K → (p : Pos a) → ∀ {κ}
      → GR.Nu a p κ → LowAt (o , r , B) (posW a p) (B (at a p) (posW a p)) (κ , K) (Dm (o , r , B))
    core→ o r B gd K bd p nu d ry = core o r B gd K bd p nu ry d
    core′ {a} o r B gd K bd p {κ} nu =
      lowAll→ (pt (o , r , B) (posW a p) (B (at a p) (posW a p)) (κ , K)) (gd , bd , nu-rd a p nu , bd p nu)
```

## 上折 `upAll`

`UpQ d u y` 对底值 b 与头 κ 全称量化; 五个参数: 像是上折 `Up j′ d b` (从 j′ 折进 ℓ), 上下文 (κ, K′), 域全体, 不变式 `Rd ℓ κ` 与 "底值对着 ψ_κ(K′)". 与抽象的 `UpKeep` 的差别: 那里上下文是 `cl ℓ (t ⊕ ·)`, 头固定为 0.

```agda
  UpHold : ∀ {ℓ j′} → O.Dn ℓ j′ → Set
  UpHold {ℓ} {j′} d = ∀ (b : Tr⁺ ℓ) κ K′ → GR.Rd ℓ κ → GR.R ℓ (E.ψ κ K′ ∷ []) (proj₁ b)
    → Hold (λ y → proj₁ (O.Up j′ d b y)) (λ u → E.ψ κ (K′ ++ u) ∷ []) ⊤ᴰ

  upQ→ : ∀ {ℓ j′} (d : O.Dn ℓ j′) → (∀ {u y} → GR.R j′ u y → UpQ d u y) → UpHold d
  upQ→ d uq b κ K′ rd rb _ ry = uq ry b κ K′ rd rb

  →upQ : ∀ {ℓ j′} (d : O.Dn ℓ j′) → UpHold d → ∀ {u y} → GR.R j′ u y → UpQ d u y
  →upQ d uh ry b κ K′ rd rb = uh b κ K′ rd rb tt ry

  upAll→ : UpMis → ∀ {ℓ} (j′ : L) (d : O.Dn ℓ j′) → UpHold d
  upAll→ um j′ d = upQ→ d (UpAll.upAll um j′ d)
```

## 主线分级实例里的 `LowKeep` 是朝第 0 层系统的限制

`gradedᴮ`/`domsᴮ` 里 `Wl` 只含 `z≤`, `Bd` 是 `Inv₀`: 所以它的 `LowKeep` 是 `YiWRZero.lowᶻ` 的系统 (上下文 ψ₀(K ++ ·), 不变式 `Inv₀`) 上的 `KeepSys` 限制到 Ω 树 (`zero→lowKeep`). `YiWREnd.W₀` 的 `ChainRel` 给出这个 `KeepSys` (`chain→keep`), 于是给出 `LowKeep` (`chain→lowKeep`).

```agda
module MainKeep where
  open ToZero gradedᴮ domsᴮ E.T apᴱ Inv₀ _≤ᵀ_ weakᴮ limᴮ nodeᴮ zeroᴮ succᴮ embᴮ leRᴮ genᴮ using (lowᶻ→)
  open import OCF.Lean.YiWRZero using (module Zero)
  open Zero gradedᴮ domsᴮ E.T apᴱ Inv₀ using (sysᶻ)
  open MI gradedᴮ domsᴮ
  open Laws gradedᴮ domsᴮ using (LowKeep)

  zero→lowKeep : KeepSys sysᶻ (λ _ → ⊤ᴰ) → LowKeep
  zero→lowKeep ks (o , r , B) _ β K _ wz bd _ ry = ks (o , r , B , β) K bd tt ry

  chain→keep : W₀.ChainRel → KeepSys sysᶻ (λ _ → ⊤ᴰ)
  chain→keep cr = lowᶻ→ W₀.restᴱ (W₀.aboveᴱ cr)

  chain→lowKeep : W₀.ChainRel → LowKeep
  chain→lowKeep cr = zero→lowKeep (chain→keep cr)

  wl-inc : ∀ {j s h} (c : Ch s) (v : j ≤ h c) → Wlᵍ (inc {h = h} c v) → ⊥
  wl-inc c v ()
```
