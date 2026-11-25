# YiPsumInst：逐项的折叠的定义域、接口的四条律、规范闭实例

**判决 (编译定理)：方案取 `canonˢ` (派发先过结构规范化) 时，`YiPsumFold.Ψᵗ` 的前提 `Dm` 对一切 `ZpL` 且 `CohP` 的层号成立 (`dm-gen`，由 `YiPsumZp.preCoh`)。
在这个域 `Domᵗ` 上接口的四条律成立 (`rawFoldᵗ`)，派发完全性不丢；ω+n、ω·2、ω·2+1 在域里，闭项 `closedᵗ K` 合法，保留模式下 ω 层 `top` 的输出是各支的逐项极限 (`body₀ᵗ-row`)。** 没有 `Funext`。
域比 `YiRawFold.Φᵐ` 的小：不含证书不一致的层号，也不含某一步在极限处取第 `n ≥ 1` 支的层号。原方案 `orig` 的情形在 [YiPsumOrig](YiPsumOrig.lagda.md)，`tw 3` 在 [YiPsumTw3](YiPsumTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPsumInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiIrrIf using (R; Legal; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt) renaming (at to atᵖ)
open import OCF.Align.YiLvIf using (Plain; lev; Kept)
open import OCF.Align.YiLvFoldAdd using (plus)
open import OCF.Align.YiLvFoldFin
  using (IsKeep; fin; ω; ω-plain; ω-legal; fin-plain; fin-legal)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFold
  using (own; Complete; complete-mix; tplain; startᴿ; nextᴿ; bodyᴿ; obsᴿ)
open import OCF.Align.YiRawFoldInst
  using (ω-coh; ω+; ω+-plain; ω+-legal; ω+-coh; ω2; ω2-plain; ω2-legal; ω2-coh)
open import OCF.Align.YiPsumBase
open import OCF.Align.YiPsumFold
open import OCF.Align.YiPsumZp

module C = Termwise canonˢ
```

## 1 定义域

`canonˢ` 在每一层的两种派发都是某个派发过了 `pre`，所以 `preCoh` 逐层给出 `CohS`。`ownTᶜ k` 是 `inS (pre (suc k) …)`，由 `pre-inS` 它就是 `pre k (inS …)`，这一步是定义性的。

```agda
cohS-here : ∀ k pl L → (∀ {m} (x : Ext m k) → CohX k L (pre k L x)) →
  (∀ r → CohX k L (ownᶜ k pl L r)) × CohX k L (ownTᶜ k pl L)
cohS-here k pl L h = (λ r → h (own k pl L r)) , h (inS (own (suc k) pl L (inj₁ tt)))

cohS-gen : ∀ K pl L → ZpL K L → CohL K L → C.CohS K pl L
cohS-gen zero pl L z c = tt
cohS-gen (suc k) pl L z c =
  proj₁ (cohS-here (suc k) pl L (preCoh (suc k) pl L z c)) ,
  proj₂ (cohS-here (suc k) pl L (preCoh (suc k) pl L z c)) ,
  cohS-gen k pl L z c
cohS-gen (lim f) pl L z c =
  proj₁ (cohS-here (lim f) pl L (preCoh (lim f) pl L z c)) ,
  proj₂ (cohS-here (lim f) pl L (preCoh (lim f) pl L z c)) ,
  (λ n → cohS-gen (f n) (pl n) (proj₂ L n) (proj₂ z n) (proj₂ c n))

Domᵗ : ∀ K → Plain K → Legal K → Set
Domᵗ K pl L = ZpL K L × CohP K pl L

dm-gen : ∀ K pl L → Domᵗ K pl L → C.Dm K pl L
dm-gen K pl L d = proj₂ d , cohS-gen K pl L (proj₁ d) (cohP→L K pl L (proj₂ d))

-- 域里有的: 有限层号, ω+n, ω·2, ω·2+1. 每一步是 suc self.
zp-fin : ∀ n → ZpL (fin n) (fin-legal n)
zp-fin zero = tt
zp-fin (suc n) = zp-fin n

zp-ω+ : ∀ n → ZpL (ω+ n) (ω+-legal n)
zp-ω+ zero = (λ n → tt) , zp-fin
zp-ω+ (suc n) = zp-ω+ n

dom-ω+ : ∀ n → Domᵗ (ω+ n) (ω+-plain n) (ω+-legal n)
dom-ω+ n = zp-ω+ n , ω+-coh n

dom-ω2 : Domᵗ ω2 ω2-plain ω2-legal
dom-ω2 = ((λ n → tt) , zp-ω+) , ω2-coh

dom-ω2+1 : Domᵗ (suc ω2) ω2-plain ω2-legal
dom-ω2+1 = dom-ω2
```

## 2 接口的四条律，在域 `Domᵗ` 上

入口的派发：目标第 0 层一律折叠；另两种目标是接口的 `dispatch` 先过 `pre`。目标是 `K` 自己时槽位因此是规范位置，不是位置自己
(`YiPsumBase.self-not-cohX`：取位置自己的派发不一致；`YiRawFoldNoLim.side-lim-illegal`：那时逐项的极限不合法)。
`YiRawIf.RawFold` 的 `Φ` 与 `legal` 对一切 `Plain` 且 `Legal` 的 `K` 量化；这里折叠的定义要 `Dm`，所以律写成 `RawFoldOn Domᵗ`，字段与 `RawFold` 逐条相同。

```agda
entry : ∀ K → Plain K → Legal K → (τ : Tgt K) → Ext (tlev K τ) K
entry K pl L base = low
entry K pl L self = pre K L (mix (dispatch K pl L self))
entry K pl L (at q) = pre K L (mix (dispatch K pl L (at q)))

entry-complete : ∀ K pl L τ → Complete (entry K pl L τ)
entry-complete K pl L base r (() , e)
entry-complete K pl L self =
  pre-complete K L (mix (dispatch K pl L self)) (complete-mix K pl L self)
entry-complete K pl L (at q) =
  pre-complete K L (mix (dispatch K pl L (at q))) (complete-mix K pl L (at q))

entry-sound : ∀ K pl L τ r → IsKeep (wayOf (entry K pl L τ) r) → At (tlev K τ) (lev K r)
entry-sound K pl L base r ()
entry-sound K pl L self = pre-sound K L (dispatch K pl L self) (dispatch-sound K pl L self)
entry-sound K pl L (at q) = pre-sound K L (dispatch K pl L (at q)) (dispatch-sound K pl L (at q))

entry-cohX : ∀ K pl L → Domᵗ K pl L → ∀ τ → CohX K L (entry K pl L τ)
entry-cohX K pl L d base = cohX-low K pl L
entry-cohX K pl L d self =
  preCoh K pl L (proj₁ d) (cohP→L K pl L (proj₂ d)) (mix (dispatch K pl L self))
entry-cohX K pl L d (at q) =
  preCoh K pl L (proj₁ d) (cohP→L K pl L (proj₂ d)) (mix (dispatch K pl L (at q)))

record RawFoldOn (Dom : ∀ K → Plain K → Legal K → Set) : Set where
  field
    Φ : ∀ K (pl : Plain K) (L : Legal K) → .(Dom K pl L) → (τ : Tgt K) (ξ : Raw K) →
      .(Lgl K ξ) → .(Nested K ξ) → Raw (tlev K τ)
    keep-law : ∀ K pl L .(d : Dom K pl L) τ r c t g
      (l : Lgl K (G.lc r c t g)) (nb : Nested K (G.lc r c t g)) →
      At (tlev K τ) (lev K r) →
      Kept (tlev K τ) (lev K r) (Φ K pl L d τ (G.lc r c t g) l nb)
    fold-law : ∀ K pl L .(d : Dom K pl L) τ r c t g
      (l : Lgl K (G.lc r c t g)) (nb : Nested K (G.lc r c t g)) →
      (At (tlev K τ) (lev K r) → ⊥) →
      IsLim (Φ K pl L d τ (G.lc r c t g) l nb)
    position : ∀ K pl L .(d : Dom K pl L) τ ξ ξ′ (l : Lgl K ξ) (nb : Nested K ξ)
      (l′ : Lgl K ξ′) (nb′ : Nested K ξ′) → Cp K ξ ξ′ →
      Cp (tlev K τ) (Φ K pl L d τ ξ l nb) (Φ K pl L d τ ξ′ l′ nb′)
    legal : ∀ K pl L (d : Dom K pl L) τ ξ (l : Lgl K ξ) (nb : Nested K ξ) →
      Lgl (tlev K τ) (Φ K pl L d τ ξ l nb)

Φᵗ : ∀ K (pl : Plain K) (L : Legal K) → .(Domᵗ K pl L) → (τ : Tgt K) (ξ : Raw K) →
  .(Lgl K ξ) → .(Nested K ξ) → Raw (tlev K τ)
Φᵗ K pl L d τ ξ l nb = C.Ψᵗ (tlev K τ) K pl L (dm-gen K pl L d) (entry K pl L τ) ξ l nb

rawFoldᵗ : RawFoldOn Domᵗ
rawFoldᵗ = record
  { Φ = Φᵗ
  ; keep-law = λ K pl L d τ r c t g l nb a →
      C.keepᵗ (tlev K τ) (tplain K pl τ) K pl L (dm-gen K pl L d) (entry K pl L τ) r c t g l nb
        (entry-complete K pl L τ r a)
  ; fold-law = λ K pl L d τ r c t g l nb na →
      C.foldᵗ (tlev K τ) K pl L (dm-gen K pl L d) (entry K pl L τ) r c t g l nb
        (λ h → na (entry-sound K pl L τ r h))
  ; position = λ K pl L d τ ξ ξ′ l nb l′ nb′ p →
      C.Ψᵗ-cp (tlev K τ) K pl L (dm-gen K pl L d) (entry K pl L τ) ξ′ l nb l′ nb′ p
  ; legal = λ K pl L d τ ξ l nb →
      C.Ψᵗ-legal (tlev K τ) (tplain K pl τ) K pl L (dm-gen K pl L d) (entry K pl L τ)
        (entry-cohX K pl L d τ) ξ l nb }

-- 结点自己那一层的两种派发也完全 (折叠问到的其余来源是 inS, inL, 见 YiRawFold 的 complete-S, complete-L).
complete-ownᶜ : ∀ k pl L r → Complete (ownᶜ k pl L r)
complete-ownᶜ k pl L r =
  pre-complete k L (own k pl L r) (λ r′ a → dispatch-complete k pl L (at r) r′ a)
```

## 3 闭项

`closedᵗ K` 是目标第 0 层在 `top` 处的折叠，读法与 `YiRawFoldInst.closed` 相同 (ψ₀(Ω_K)，读法)，没有值定理。

```agda
closedᵗ : ∀ K (pl : Plain K) (L : Legal K) → .(Domᵗ K pl L) → R
closedᵗ K pl L d = Φᵗ K pl L d base G.top tt tt

closedᵗ-legal : ∀ K pl L (d : Domᵗ K pl L) → Lgl zero (closedᵗ K pl L d)
closedᵗ-legal K pl L d = RawFoldOn.legal rawFoldᵗ K pl L d base G.top tt tt

closedᵗ-nested : ∀ K pl L (d : Domᵗ K pl L) → Nested zero (closedᵗ K pl L d)
closedᵗ-nested K pl L d = C.Ψᵗ-nested zero K pl L (dm-gen K pl L d) low G.top tt tt

Ωω+1ᵗ Ωω+2ᵗ Ωω2ᵗ Ωω2+1ᵗ : R
Ωω+1ᵗ = closedᵗ (ω+ 1) ω-plain ω-legal (dom-ω+ 1)
Ωω+2ᵗ = closedᵗ (ω+ 2) ω-plain ω-legal (dom-ω+ 2)
Ωω2ᵗ = closedᵗ ω2 ω2-plain ω2-legal dom-ω2
Ωω2+1ᵗ = closedᵗ (suc ω2) ω2-plain ω2-legal dom-ω2+1

Ωω+1ᵗ-legal : Lgl zero Ωω+1ᵗ
Ωω+1ᵗ-legal = closedᵗ-legal (ω+ 1) ω-plain ω-legal (dom-ω+ 1)

Ωω+2ᵗ-legal : Lgl zero Ωω+2ᵗ
Ωω+2ᵗ-legal = closedᵗ-legal (ω+ 2) ω-plain ω-legal (dom-ω+ 2)

Ωω2ᵗ-legal : Lgl zero Ωω2ᵗ
Ωω2ᵗ-legal = closedᵗ-legal ω2 ω2-plain ω2-legal dom-ω2

Ωω2+1ᵗ-legal : Lgl zero Ωω2+1ᵗ
Ωω2+1ᵗ-legal = closedᵗ-legal (suc ω2) ω2-plain ω2-legal dom-ω2+1

-- 极限层号上闭项是各支闭项的极限 (各支的 Dm 是无关参数, 写哪一份都一样).
closedᵗ-lim : ∀ f pl L .(d : Domᵗ (lim f) pl L) → closedᵗ (lim f) pl L d ≡
  G.lim (λ n → C.Ψᵗ zero (f n) (pl n) (proj₂ L n)
    (C.dL f pl L (dm-gen (lim f) pl L d) n) low G.top tt tt)
closedᵗ-lim f pl L d = refl
```

## 4 ω+1 上 `top_ω` 处推进用的输出：逐项，合法

`YiRawFoldInst.ω+1-body₀` 的同一处。`Ωω+1ᵗ` 的链在 `Raw ω` 里，第 0 点是 `top`，推进用的输出是目标 ω 的折叠在 `top` 上的值。
这里它是各支折叠 `sideᶜ n` 的逐项极限；`sideᶜ-step`：相邻两支的输出之间有字面的第一位置，对一切 `n`。

```agda
dm-ω : C.Dm ω ω-plain ω-legal
dm-ω = dm-gen ω ω-plain ω-legal (dom-ω+ 0)

rootᵗ : NdR zero ω
rootᵗ = C.ndTᵗ zero ω ω-plain ω-legal dm-ω low

sideᶜ : ℕ → Raw ω
sideᶜ n = C.Ψᵗ ω (fin n) (fin-plain n) (fin-legal n) (C.dL fin ω-plain ω-legal dm-ω n)
  (inL (ownTᶜ ω ω-plain ω-legal) n) G.top tt tt

Ωω+1ᵗ-row : Ωω+1ᵗ ≡ G.lim (λ n → obsᴿ rootᵗ (iterate (nextᴿ ω-plain rootᵗ) (startᴿ rootᵗ) n))
Ωω+1ᵗ-row = refl

body₀ᵗ-row : bodyᴿ rootᵗ (startᴿ rootᵗ) ≡ G.lim sideᶜ
body₀ᵗ-row = refl

body₀ᵗ-legal : Lgl ω (G.lim sideᶜ)
body₀ᵗ-legal =
  C.Ψᵗ-legal ω ω-plain ω ω-plain ω-legal dm-ω (ownTᶜ ω ω-plain ω-legal)
    (C.topS ω ω-plain ω-legal (proj₂ dm-ω)) G.top tt tt

sideᶜ-step : ∀ n → Cp ω (sideᶜ n) (sideᶜ (suc n))
sideᶜ-step = proj₁ body₀ᵗ-legal

-- 下一个链点: top 加上这个逐项极限.
point₁ᵗ : atᵖ (iterate (nextᴿ ω-plain rootᵗ) (startᴿ rootᵗ) 1) ≡ plus ω G.top (G.lim sideᶜ)
point₁ᵗ = refl

-- 槽位是规范位置: 第 3 支里根下一格 (层号 1) 的结点保留在槽位 (2 , 根), 与 YiRawFoldInst.test-slot-ω 同一格.
test-slotᶜ : slotOf (wayOf (ownTᶜ ω ω-plain ω-legal) (3 , inj₂ (inj₁ tt))) (1 , inj₁ tt) ≡
  (2 , inj₁ tt)
test-slotᶜ = refl
```
