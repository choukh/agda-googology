# typed读回在零高度的完整反映

验收专用。原F 0没有Ω种类，故零高度Read可反映成纯可数树的
结构对应。反向只在旧Ord0构造，不把同余送给任意高层分支。
这里实填RootObservation的零高度基例，不代替一般内部目标观察。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedZero where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (leftMul)
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
open import OCF.Lean.BoundedDiagonalSame using (same-add)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; read-shape)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableNextValueOrbit using (observe-sound)

zero-sound : ∀ {ℓ} {σ : L.Simᴵ ℓ (height hz tt)} {a b} →
  Read hz tt σ a b → a L.≅ B.read b
zero-sound rz = L.z≅
zero-sound (rs p) = L.s≅ (zero-sound p)
zero-sound (rl p) = L.l≅ (λ n → zero-sound (p n))
zero-sound (ro () q eq self p)
zero-sound (ru-s p) = L.upˡ (zero-sound p)
zero-sound (ru-l p) = L.upˡ (zero-sound p)
zero-sound (rc e p) = L.≅-trans e (zero-sound p)

read-zero : ∀ c → Read hz tt (canonical hz tt) (B.read c) c
read-zero hz = rz
read-zero (hs c) = rs (read-zero c)
read-zero (hl f) = rl (λ n → read-zero (f n))
read-zero (hΩ () f)
zero-reflect : ∀ {a : L.Ordᶜ L.zero} {b : Cd} →
  a L.≅ B.read b → Read hz tt (canonical hz tt) a b
zero-reflect {b = b} e = rc e (read-zero b)

left-shape : ∀ {a b : Cd} → Same a b → ∀ n → Same (leftMul a n) (leftMul b n)
left-shape p zero = zz
left-shape p (suc n) = same-add p (left-shape p n)
point-runtime : ∀ c → Same (point-observe hz tt hz hself c) (observe hz tt hz hself c)
point-runtime hz = ss zz
point-runtime (hs c) = ll (left-shape (point-runtime c))
point-runtime (hl f) = ll (λ n → point-runtime (f n))
point-runtime (hΩ () f)

root-zero : ∀ {ℓ} {σ : L.Simᴵ ℓ (height hz tt)} {a b} → Read hz tt σ a b →
  L.ψ⁰ a L.≅ B.read (point-observe hz tt hz hself b)
root-zero {b = b} r = L.≅-trans (L.ψ⁰-≅ (zero-sound r))
  (L.≅-trans (observe-sound b) (L.≅-sym (read-shape (point-runtime b))))
```

read-zero给所有纯Cd的实际实例，包括任意ℕ树。root-zero保持原
ψ⁰、原逐点辅助解释与原源树，没有把高层Read或整个γ₂化简成零层。
