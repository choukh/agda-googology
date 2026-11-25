# 经典清退：值序二分一类的前提在排中律下成立

> 验收文件，档位：条件定理（条件：排中律，模块参数 `lem`）。`Tri` 取现成的 `YiChainNegLEM.lem→tri`；由它得 `Cplˣ`、`Cplᵖ`、`CplˣS`、`VMᴸ`、`Crux`、`EmbV`、`EmbVˢ`、`VMˢ`、`VMᶜ`、`MonoTᶻ`、`ChainP`、`Add1ˣ`、`AddωS`，不读推导的 `VM¬¬`、`VMⁱ`、`EmbV¬¬`、`EmbVⁱ`，另有 LPO、WLPO、MP、MPⁱ。
> 读法：这些前提的否定（`tri→LPO`、`cplˣ→LPO`、`embV→LPO`、`add1→LPO`、`vm¬¬→MP` 等）在排中律下不再挡验收侧的证法；对派发、折叠、表的否定（如 `YiCompatDlLPO.lpo-tw`）仍约束定义，结论为矛盾的（如 `YiCompatDlNeg.no-tw`）不受影响。
> 值：旧块塔第 3 项的闭项 `T₃ᵐ` 不低于 BTBO 的参照 `D.BTBOᴵ`（`btbo-T₃ᵐ`；`D.BTBOᴵ` 经 `BTBOFull.BTBO≈` 与已发表的 BTBO 同值，读法 ψ₀(Ω_Ω)）。不构造 `Compat` 的实例，不涉及现主线 `EBOᶻ` 与换基候选 `EBOᴮ`。入口 `Classical`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCIClear where

open import Data.Nat.Base using (ℕ)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Value using (_≼_)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiVmConExact using (Tri; Cplᵖ; tri→cplˣ; tri→vm; ˣ→ᵖ; cpl→embV; cpl→crux)
open import OCF.Align.YiVmConLPO using (Cplˣ)
open import OCF.Align.YiMonoVM using (VMᴸ; Crux; EmbV; MonoTᶻ; vm→monoᶻ)
import OCF.Align.YiMonoVM as MonoVM
open import OCF.Lean.YiLowBase using (EmbVˢ; VMˢ; embˢ→vmˢ)
open import OCF.Lean.YiLowChain using (VMᶜ; vmᴸ→vmᶜ)
open import OCF.Lean.YiChainNegLEM using (lem→tri; lem→chainP)
import OCF.Lean.YiLeanValFin as MV
import OCF.Align.YiIrrFoldValue as IV
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOFull using (BTBO≈)
import OCF.Barrier as B
import OCF.Lean.YiUniNegBase as U
import OCF.Align.Level as L
open import OCF.Align.Value using (z≼; s≼s; ≼l; l≼; ≼-trans)
open import OCF.Align.YiVmConExact using (_≼ˣ_; ˣ→≼)
open import OCF.Align.YiVmNegIrr using (MP; MPⁱ; VM¬¬; VMⁱ; EmbV¬¬; EmbVⁱ)
open import OCF.Lean.YiChainNegAdd using (Add1ˣ; AddωS; CplˣS; ω′)
```

右加数不超过和（第 0 层，无前提），供左加封闭用。

```agda
≼+ˡ : ∀ (c z : L.Ordᶜ L.zero) → z ≼ c L.+ z
≼+ˡ c L.zero = z≼
≼+ˡ c (L.suc z) = s≼s (≼+ˡ c z)
≼+ˡ c (L.lim f) = l≼ (λ n → ≼l n (≼+ˡ c (f n)))
≼+ˡ c (L.limᵢ () f)
≼+ˡ c (L.up () x)
```

`WLPO` 取仓库里几份同名定义的共同形状（`YiLamNLim`、`YiPhiNegB`、`NegThirdPre` 等，`¬ A` 与 `A → ⊥` 定义相等）。

```agda
LEM : Set₁
LEM = (A : Set) → A ⊎ ¬ A

WLPO : Set
WLPO = (α : ℕ → Bool) → ((n : ℕ) → α n ≡ false) ⊎ ¬ ((n : ℕ) → α n ≡ false)

module Classical (lem : LEM) where
```

## 1 前提

```agda
  tri : Tri
  tri = lem→tri lem

  cplˣ : Cplˣ
  cplˣ = tri→cplˣ tri

  cplᵖ : Cplᵖ
  cplᵖ x y d = ˣ→ᵖ (tri→cplˣ tri x y d)

  vm : VMᴸ
  vm = tri→vm tri

  crux : Crux
  crux = cpl→crux cplᵖ

  embV : EmbV
  embV = cpl→embV cplᵖ

  embVˢ : EmbVˢ
  embVˢ x hx y hy _ _ d = embV x hx y hy d

  vmˢ : VMˢ
  vmˢ = embˢ→vmˢ embVˢ

  vmᶜ : VMᶜ
  vmᶜ = vmᴸ→vmᶜ vm

  monoᶻ : MonoTᶻ
  monoᶻ = vm→monoᶻ vm

  chainP : MV.ChainP
  chainP = lem→chainP lem

  cplˣS : CplˣS
  cplˣS x y _ _ d = cplˣ x y d

  addˣ : ∀ c x z → x ≼ˣ z → x ≼ˣ (c L.+ z)
  addˣ c x z d = cplˣ x (c L.+ z) (≼-trans (ˣ→≼ d) (≼+ˡ c z))

  add1 : Add1ˣ
  add1 x z d = addˣ (L.suc L.zero) x z d

  addω : AddωS
  addω x z _ d = addˣ ω′ x z d
```

不读推导的两种写法（`¬ ¬` 与无关参数）：排中律把前提还原成推导。

```agda
  ⊥ᵢ : .⊥ → ⊥
  ⊥ᵢ ()

  ¬¬e : ∀ {A : Set} → ¬ ¬ A → A
  ¬¬e {A} nn with lem A
  ... | inj₁ a  = a
  ... | inj₂ na = ⊥-elim (nn na)

  irrE : ∀ {A : Set} → .A → A
  irrE {A} a with lem A
  ... | inj₁ x  = x
  ... | inj₂ na = ⊥-elim (⊥ᵢ (na a))

  mp : MP
  mp α nn = ¬¬e nn

  mpⁱ : MPⁱ
  mpⁱ α e = irrE e

  vm¬¬ : VM¬¬
  vm¬¬ x hx y hy nn = vm x hx y hy (¬¬e nn)

  vmⁱ : VMⁱ
  vmⁱ x hx y hy d = vm x hx y hy (irrE d)

  embV¬¬ : EmbV¬¬
  embV¬¬ x hx y hy nn = embV x hx y hy (¬¬e nn)

  embVⁱ : EmbVⁱ
  embVⁱ x hx y hy d = embV x hx y hy (irrE d)
```

## 2 全知原则

```agda
  notTrue : ∀ (b : Bool) → ¬ (b ≡ true) → b ≡ false
  notTrue false _ = refl
  notTrue true  h = ⊥-elim (h refl)

  lpo : B.LPO
  lpo α with lem (Σ ℕ λ k → α k ≡ true)
  ... | inj₁ e  = inj₁ e
  ... | inj₂ ne = inj₂ (λ k → notTrue (α k) (λ t → ne (k , t)))

  lpoᵁ : U.LPO
  lpoᵁ α = lem (U.Found α)

  wlpo : WLPO
  wlpo α = lem ((n : ℕ) → α n ≡ false)
```

## 3 值：旧块塔第 3 项的闭项不低于 BTBO 的参照

`T₃ᵐ`：旧块（`OCF.Align`）塔第 3 项的闭项，此前无前提的下界到 ψ₀(Ω_{ω+1})（`YiMonoOne.T₃ᵐ-Ωω+1`）。11-11 重写块的 `T₃` 与 `T⁺` 已有无前提的 BTBO 下界（`YiBtboLower.btbo`、`btbo⁺`），经 `chainP` 的条件版（`YiLeanValFin.btbo-p`、`YiNextValFin.btbo⁺-from-main`）不再给新东西，这里不重复。

```agda
  btbo-T₃ᵐ : D.BTBOᴵ ≼ IV.read T₃ᵐ
  btbo-T₃ᵐ = MonoVM.btbo-vm vm

  src-btbo-T₃ᵐ : tr₀ Ord-Ord.BTBO ≼ IV.read T₃ᵐ
  src-btbo-T₃ᵐ = ≼-trans (proj₁ BTBO≈) btbo-T₃ᵐ
```
