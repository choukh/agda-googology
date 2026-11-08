# 所有可数层的一步编码实例

统一定理按原Native c与其坐标关系实例化，c可以是任意可数树，
不限有限数。这里给的是编码比较；实际下降解释器的比较仍是另一个义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseActual where
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionUniformIf using (Value; CoordValue)
open import OCF.Align.BoundedCompletionUniformClosure using (floor-value)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
import OCF.Lean.GeneralRebaseIf as I
import OCF.Lean.GeneralRebaseRun as R
import OCF.Align.BoundedWorldRebaseIf as Old

enc : ∀ c → HB (Native c) → HB (Native (hs c)) → HB (Native (hs c))
enc c = I.Layer.enc (Native c) (CoordValue c)

to-generic : ∀ c {a b} → Value (hs c) a b → I.Layer.R⁺ (Native c) (CoordValue c) a b
to-generic c = R.restrict-coordinates λ
  { (inj₁ κ) x y p → p
  ; (inj₂ _) x y p → p }
from-generic : ∀ c {a b} → I.Layer.R⁺ (Native c) (CoordValue c) a b → Value (hs c) a b
from-generic c = R.restrict-coordinates λ
  { (inj₁ κ) x y p → p
  ; (inj₂ _) x y p → p }

mono : ∀ c {a b u v} → Value (hs c) a b → Value c u v →
  Value (hs c) (enc c u a) (enc c v b)
mono c p uv = from-generic c (R.Layer.mono (Native c) (CoordValue c) (to-generic c p) uv)
inflate : ∀ c {a b} → Value (hs c) a b → ∀ m → Value (hs c) a (enc c m b)
inflate c p m = from-generic c (R.Layer.inflate (Native c) (CoordValue c) (to-generic c p) m)

floor-self : ∀ n → Value (num (suc n))
  (enc (num n) (floor n) (floor (suc n)))
  (enc (num n) (floor n) (floor (suc n)))
floor-self n = mono (num n) (floor-value (suc n)) (floor-value n)
floor-inflate : ∀ n → Value (num (suc n)) (floor (suc n))
  (enc (num n) (floor n) (floor (suc n)))
floor-inflate n = inflate (num n) (floor-value (suc n)) (floor n)

old-encoding : ∀ b a → Same (Old.enc b a) (enc hz b a)
old-encoding b hz = zz
old-encoding b (hs a) = ss (old-encoding b a)
old-encoding b (hl f) = ll (λ n → old-encoding b (f n))
old-encoding b (hΩ (inj₁ (inj₁ ())) g)
old-encoding b (hΩ (inj₁ (inj₂ _)) g) = oo (λ c → old-encoding b (g c))
old-encoding b (hΩ (inj₂ _) g) = oo (λ e → old-encoding (b ⊞ e) (g (b ⊞ e)))
```

floor-self与floor-inflate在每个有限n都有原地板的真实非零实例；没有以
条件接口替代实例。old-encoding逐全部分支核对旧双槽编码是此一步
定义的实例，不要求函数外延。任意c的编码比较不蕴含任意c的运行覆盖，
尤其不把它当作实际EBO全阶段覆盖或新的ψ₀具名强度。
