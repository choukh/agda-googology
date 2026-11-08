# 全实际旧坐标的 act 到 Ω 零规则模拟

boost仅为验收模型：零叶换最低Ω，后继仍按原从一份起的重复，Ω仍保留。
本篇不将它叫作Level折叠；先对全部实际旧轨道证明其原末段输出上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformUpperStableBoost where
open import Data.Nat using (zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueClosure
open import OCF.Align.BoundedCompletionTerminalValueAct using (act-mono; old-coordinate-self)
open import OCF.Align.UniformUpperStableIf
open import OCF.Align.UniformUpperStableAdd using (repeated)
import OCF.Align.UniformUpperStableRun as Run
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Align.BoundedNativeTerminalReady as T

boost : HB U → HB U
boost hz = floor
boost (hs a) = hl (mul (boost a))
boost (hl f) = hl (λ n → boost (f n))
boost (hΩ (inj₁ ()) g)
boost (hΩ (inj₂ _) g) = hΩ (inj₂ tt) (λ c → boost (g c))

positive : ∀ a → VRel floor (boost a)
positive hz = floor-self
positive (hs a) = vli 0 (positive a)
positive (hl f) = vli 0 (positive (f 0))
positive (hΩ (inj₁ ()) g)
positive (hΩ (inj₂ _) g) = vor (λ c → positive (g c))
boost-mono : ∀ {a b} → VRel a b → VRel (boost a) (boost b)
boost-mono {b = b} vz = positive b
boost-mono (vs p) = repeat-rel (boost-mono p)
boost-mono (vr p) = vli 0 (boost-mono p)
boost-mono (vl p) = vl (λ n → boost-mono (p n))
boost-mono (vli n p) = vli n (boost-mono p)
boost-mono (vo p) = vo (λ r → boost-mono (p r))
boost-mono (vor p) = vor (λ c → boost-mono (p c))

Good : HB U → Set
Good hz = ⊤
Good (hs a) = Good a
Good (hl f) = ∀ n → Good (f n)
Good (hΩ (inj₁ ()) g)
Good (hΩ (inj₂ _) g) =
  (∀ {c d} → c ≤ᵛ d → VRel (g c) (g d)) × (∀ c → Good (g c))
self : ∀ {a} → Good a → VRel a a
self {a = hz} g = vz
self {a = hs a} g = vs (self g)
self {a = hl f} g = vl (λ n → vli n (self (g n)))
self {a = hΩ (inj₁ ()) f} g
self {a = hΩ (inj₂ _) f} (mo , g) = vo mo

good-add : ∀ {a b} → Good a → Good b → Good (a ⊞ b)
good-add {b = hz} a b = a
good-add {b = hs b} a g = good-add a g
good-add {b = hl f} a g = λ n → good-add a (g n)
good-add {b = hΩ (inj₁ ()) f} a g
good-add {b = hΩ (inj₂ _) f} a (mo , g) =
  (λ r → add-rel (self a) (mo r)) , (λ c → good-add a (g c))
good-mul : ∀ {a} → Good a → ∀ n → Good (mul a n)
good-mul a zero = a
good-mul a (suc n) = good-add (good-mul a n) a
act-good : ∀ {a} → Good a → Good (Old.act a)
act-good {a = hz} g = tt
act-good {a = hs a} g = good-mul (act-good g)
act-good {a = hl f} g = λ n → act-good (g n)
act-good {a = hΩ (inj₁ ()) f} g
act-good {a = hΩ (inj₂ _) f} (mo , g) = (λ r → act-mono (mo r)) , (λ c → act-good (g c))
up-good : ∀ (c : Cd) → Good (up c)
up-good hz = tt
up-good (hs c) = up-good c
up-good (hl f) = λ n → up-good (f n)
floor-good : Good floor
floor-good = up-mono , up-good
coordinate-good : ∀ n → Good (Old.Pure.ce n)
coordinate-good zero = floor-good
coordinate-good (suc n) = good-add (coordinate-good n) (act-good (coordinate-good n))

unit-below : ∀ b → Core (hs hz) (boost b)
unit-below hz = unit
unit-below (hs b) = pick 0 (unit-below b)
unit-below (hl f) = pick 0 (unit-below (f 0))
unit-below (hΩ (inj₁ ()) g)
unit-below (hΩ (inj₂ _) g) = uniform (λ c → unit-below (g c))

compare : ∀ {a b} → Good a → Good b → VRel a b → Core (Old.act a) (boost b)
compare {b = b} ga gb vz = unit-below b
compare ga gb (vs p) = repeated (act-mono (self ga)) (boost-mono (self gb)) (compare ga gb p)
compare ga gb (vr p) = pick 0 (compare ga gb p)
compare ga gb (vl p) = all (λ n → compare (ga n) gb (p n))
compare ga gb (vli n p) = pick n (compare ga (gb n) p)
compare ga gb (vo p) = omega (λ r → compare (proj₂ ga _) (proj₂ gb _) (p r))
compare ga gb (vor p) = uniform (λ c → compare ga (proj₂ gb c) (p c))

actual : ∀ n {u v} → u ≤ᵛ v →
  T.fold u (Old.act (Old.Pure.ce n)) ≤ᵛ T.fold v (boost (Old.Pure.ce n))
actual n uv = Run.eval (compare (coordinate-good n) (coordinate-good n) (old-coordinate-self n)) uv
```

actual覆盖完整旧坐标族及任意有序种子，不是常值样本。Good由原坐标
的实际生成直接证明，没有未实例化前提。尚需boost整轨道的参照校准，
以及输出部分和的共尾界；不能将此一步模拟冒称Old2的具名上界。
