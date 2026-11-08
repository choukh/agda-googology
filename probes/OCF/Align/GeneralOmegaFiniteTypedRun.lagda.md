# 原K动作与全部无累加typed轨道

验收专用。低Ω穿透保留原tr⁻；用Read的坐标字段搬运结构证据，
不要求两棵坐标树字面相等，也不抹除原低Ω。后继列两边都从0份起。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteTypedRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
open import OCF.Align.GeneralOmegaFiniteTypedIf
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

add-low : ∀ {a b c} {x : L.Ordᶜ L.zero} → Read a b → B.read c L.≅ x →
  Read (L.add a (λ q → L.suc q) x) (b ⊞ up c)
add-low {c = hz} p L.z≅ = p
add-low {c = hs c} p (L.s≅ q) = rs (add-low p q)
add-low {c = hl f} p (L.l≅ q) = rl (λ n → add-low p (q n))

add : ∀ {a b c d} → Read a b → Read c d → Read (a L.+ c) (b ⊞ d)
add p rz = p
add p (rs q) = rs (add p q)
add p (rl q) = rl (λ n → add p (q n))
add p (ro q) = ro (λ x c e → add p (q x c e))
add p (ru q) = add-low p q

mul : ∀ {a b} → Read a b → ∀ n → Read (iter (a L.+_) L.zero n) (P.leftMul b n)
mul p zero = rz
mul p (suc n) = add p (mul p n)

low : ∀ {c} {x : L.Ordᶜ L.zero} → B.read c L.≅ x →
  Read (L.ψ {i = L.suc L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero (λ q → L.suc (L.suc q)) x) (P.Typed (up c))
low {c = hz} L.z≅ = floor
low {c = hs c} (L.s≅ p) = rl (mul (low p))
low {c = hl f} (L.l≅ p) = rl (λ n → low (p n))

typed : ∀ {a b} → Read a b → Read (stepᴵ a) (P.Typed b)
typed rz = floor
typed (rs p) = rl (mul (typed p))
typed (rl p) = rl (λ n → typed (p n))
typed (ro p) = ro (λ x c q → typed (p (L.tr⁻ L.z≅ x) c
  (L.≅-sym (L.tr⁻-≅ L.z≅ (L.≅-sym q)))))
typed (ru p) = low p

orbit : ∀ n → Read (old-chain n) (P.NoSum n)
orbit zero = floor
orbit (suc n) = typed (orbit n)

pure : ∀ c → B.read c L.≅ read (up c)
pure hz = L.z≅
pure (hs c) = L.s≅ (pure c)
pure (hl f) = L.l≅ (λ n → pure (f n))

sound : ∀ {a b} → Read a b → a L.≅ read b
sound rz = L.z≅
sound (rs p) = L.s≅ (sound p)
sound (rl p) = L.l≅ (λ n → sound (p n))
sound (ro p) = L.lᵢ≅ L.z≅ (λ x y q → sound (p x (B.forget y)
  (L.≅-trans (B.reference-roundtrip y) (L.≅-sym q))))
sound (ru {c = c} p) = L.upˡ (L.≅-trans (L.≅-sym p) (pure c))

whole : L.ψ⁰ (L.Ω (L.suc (L.suc L.zero))) L.≅
  L.lim (λ n → L.ψ⁰ (read (P.NoSum n)))
whole = L.l≅ (λ n → L.ψ⁰-≅ (L.upˡ (sound (orbit n))))
```

whole比较原ψ₀(Ω₂)的整个基本列与树侧NoSum的全部外ψ⁰观察值。
这不是新GeneralOmegaConsume.run的输出下界：还缺该外ψ⁰观察与
原更高源真实回调之间的模拟，不能用NoSum≤Sum的高层值关系替代。
