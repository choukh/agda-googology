# 真实最高反馈输出的跨注入归并

emit n c是normal(suc n)的原输出回调。这里把它归并为原低层at对
model n⊞c求值；没有把额外求值后的coordinate n c当作emit。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformEmit where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteRun using (coherent)
open import OCF.Align.BoundedCompletionFinitePlaceRun using (coherent-up)
open import OCF.Align.BoundedCompletionFinitePlacePER using (rel-trans)
open import OCF.Align.BoundedCompletionFiniteValueIf using (coordinate)
open import OCF.Align.BoundedCompletionFiniteValueFirst using (emit)
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
open import OCF.Align.BoundedCompletionTerminalRel using (terminal-rel)
import OCF.Align.BoundedNativeTerminalReady as T

up-add : ∀ c {a b d e} → Rel c a b → Rel c d e →
  Rel (hs c) (up (a ⊞ d)) (up b ⊞ up e)
up-add c p rz = up-rel c p
up-add c p (rs q) = rs (up-add c p q)
up-add c p (rl q) = rl (λ n → up-add c p (q n))
up-add c p (ro q) = ro (λ x y r → up-add c p (q x y r))

coordinate-rel : ∀ n {a b} → Rel (num n) a b →
  Rel (num n) (coordinate n a) (coordinate n b)
coordinate-rel n r = coherent (suc n) n {B = num (suc n)} {B′ = num (suc n)}
  (legal-num (suc n)) (legal-num (suc n)) hself hself (hsuc hself) (hsuc hself)
  (rel-add (up-rel (num n) (Θ.model-rel n)) (up-rel (num n) r))

chain-rel : ∀ n k → Rel (num n) (chain (coordinate n) k) (chain (coordinate n) k)
chain-rel n zero = rs rz
chain-rel n (suc k) = rel-add (chain-rel n k) (coordinate-rel n (chain-rel n k))

emit-rel : ∀ n c → Rel (num n) c c → Rel hz
  (at n zero {B = num n} (legal-num n) hself (z⊲ᴮ (num n)) (Θ.model n ⊞ c))
  (emit n c)
emit-rel n c rc = rel-trans hz
  (coherent-up n zero {B = num n} {B′ = num (suc n)}
    (legal-num n) (legal-num (suc n)) hself hself (z⊲ᴮ (num n)) (z⊲ᴮ (num (suc n)))
    (rel-add (Θ.model-rel n) rc))
  (coherent (suc n) zero {B = num (suc n)} {B′ = num (suc n)}
    (legal-num (suc n)) (legal-num (suc n)) hself hself
    (z⊲ᴮ (num (suc n))) (z⊲ᴮ (num (suc n)))
    (up-add (num n) (Θ.model-rel n) rc))

emit-terminal : ∀ n c → Rel (num n) c c → ∀ seed → Same
  (T.fold seed (at n zero {B = num n} (legal-num n) hself (z⊲ᴮ (num n)) (Θ.model n ⊞ c)))
  (T.fold seed (emit n c))
emit-terminal n c rc seed = terminal-rel (emit-rel n c rc) (pure-reflexive seed)
```

chain-rel实例化全部原坐标，故emit-terminal能用于任意真实反馈项。
该桥保持完整输出回调，没有把坐标动作与输出动作混同。
