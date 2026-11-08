# 全可数高度原pointFloor的typed读回实例

仅做验收，不反改原候选。并层保持原全部分量，没有把pointFloor
换成累计floor；两者的有向原观察界由既有PointSimulation另行提供。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedFloor where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf

up-read : ∀ {B lB ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b →
  Read (hs B) lB (λ q → L.suc (σ q)) a (up b)
up-read rz = rz
up-read (rs p) = rs (up-read p)
up-read (rl p) = rl (λ n → up-read (p n))
up-read (ro κ q eq self p) = ro (inj₁ κ) q (cong L.suc eq) self (λ x c r → up-read (p x c r))
up-read (ru-s p) = ru-s (up-read p)
up-read (ru-l p) = ru-l (up-read p)
up-read (rc e p) = rc e (up-read p)
iota-read : ∀ f (lB : LgB (hl f)) n {ℓ} {σ : L.Simᴵ ℓ (height (f n) (proj₂ lB n))} {a b} →
  Read (f n) (proj₂ lB n) σ a b → Read (hl f) lB (λ q → L.lim n (σ q)) a (ι n b)
iota-read f lB n rz = rz
iota-read f lB n (rs p) = rs (iota-read f lB n p)
iota-read f lB n (rl p) = rl (λ i → iota-read f lB n (p i))
iota-read f lB n (ro κ q eq self p) = ro (n , κ) q (cong (L.lim n) eq) self (λ x c r → iota-read f lB n (p x c r))
iota-read f lB n (ru-s p) = ru-s (iota-read f lB n p)
iota-read f lB n (ru-l p) = ru-l (iota-read f lB n p)
iota-read f lB n (rc e p) = rc e (iota-read f lB n p)

floor-read : ∀ B lB → Read B lB (canonical B lB) (L.Ω (height B lB)) (pointFloor B)
floor-read hz lB = rs rz
floor-read (hs B) lB = ro (inj₂ tt) L.zero refl (L.Ω-refl (height (hs B) lB))
  (λ x e p → ru-s (up-read p))
floor-read (hl f) lB = rl (λ n → ru-l (iota-read f lB n (floor-read (f n) (proj₂ lB n))))
floor-read (hΩ () f) lB
self : ∀ {B lB ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b → a L.≅ a
self rz = L.z≅
self (rs p) = L.s≅ (self p)
self (rl p) = L.l≅ (λ n → self (p n))
self (ro κ q eq r p) = r
self (ru-s p) = L.upˡ (L.upʳ (self p))
self (ru-l p) = L.upˡ (L.upʳ (self p))
self (rc e p) = L.≅-trans e (L.≅-sym e)
coord-cong : ∀ B lB κ {x y c} → x L.≅ y → Coord B lB κ y c → Coord B lB κ x c
coord-cong hz lB () e r
coord-cong (hs B) lB (inj₁ κ) e r = coord-cong B lB κ e r
coord-cong (hs B) lB (inj₂ _) e r = rc e r
coord-cong (hl f) lB (n , κ) e r = coord-cong (f n) (proj₂ lB n) κ e r
coord-cong (hΩ () f) lB κ e r
coord-self : ∀ B lB κ {x c} → Coord B lB κ x c → x L.≅ x
coord-self hz lB () r
coord-self (hs B) lB (inj₁ κ) r = coord-self B lB κ r
coord-self (hs B) lB (inj₂ _) r = self r
coord-self (hl f) lB (n , κ) r = coord-self (f n) (proj₂ lB n) κ r
coord-self (hΩ () f) lB κ r
coord-tr⁻ : ∀ B lB κ {x c} → Coord B lB κ x c → Coord B lB κ (L.tr⁻ (L.≅ᴵ-refl (rank B lB κ)) x) c
coord-tr⁻ B lB κ r = coord-cong B lB κ (L.tr⁻-≅ (L.≅ᴵ-refl (rank B lB κ)) (coord-self B lB κ r)) r
instance-reading : PointReading
instance-reading = record { floor-read = floor-read ; self = self ; coord-tr⁻ = coord-tr⁻ }

omega-read : Read omega omega-legal (canonical omega omega-legal)
  (L.Ω (height omega omega-legal)) (pointFloor omega)
omega-read = floor-read omega omega-legal
```

原全B地板已有读回证书，ω是具体非有限实例。此篇不宣称point-observe
保持Read，不给出原ψ⁰完整值界；尤其不能把逐点地板证书直接当作
内部反馈种子的比较。当前新增参照层与关系均仅在Align验收目录。
