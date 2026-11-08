# 任意可数层的递归Good经重定位仍成立

Good既给关系自证，也给每个实际准入分支的递归证书。通过同一个
结构参数域实例，编码的关系比较与递归证书保持一起推广到任意c。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseDomainActual where
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Lean.RebaseLayerIf using (vz)
open import OCF.Lean.RebaseLayerGoodIf
open import OCF.Lean.RebaseLayerGoodClosure using (self; good-add; floor-good)
open import OCF.Lean.GeneralRebaseSampleRun using (relabel)
import OCF.Lean.GeneralRebaseDomainIf as I
import OCF.Lean.GeneralRebaseDomainRun as R

domain : ∀ c → I.Layer.Domain (Native c) (Admit c) (Coord c) (Good c)
domain c = record { add-closed = good-add c }
enc : ∀ c → HB (Native c) → HB (Native (hs c)) → HB (Native (hs c))
enc c = I.Layer.enc (Native c) (Admit c) (Coord c) (Good c)
to-generic : ∀ c {a b} → Value (hs c) a b →
  I.Layer.R⁺ (Native c) (Admit c) (Coord c) (Good c) a b
to-generic c = relabel
  (λ { (inj₁ κ) e p → p; (inj₂ _) e p → p })
  (λ { (inj₁ κ) x y p → p; (inj₂ _) x y p → p })
from-generic : ∀ c {a b} → I.Layer.R⁺ (Native c) (Admit c) (Coord c) (Good c) a b →
  Value (hs c) a b
from-generic c = relabel
  (λ { (inj₁ κ) e p → p; (inj₂ _) e p → p })
  (λ { (inj₁ κ) x y p → p; (inj₂ _) x y p → p })

mono : ∀ c {a b u v} → Value (hs c) a b → Value c u v → Good c u → Good c v →
  Value (hs c) (enc c u a) (enc c v b)
mono c p uv pu pv = from-generic c
  (R.Layer.mono (Native c) (Admit c) (Coord c) (Good c) (domain c) (to-generic c p) uv pu pv)
inflate : ∀ c {a b} → Value (hs c) a b → ∀ m → Good c m → Value (hs c) a (enc c m b)
inflate c p m pm = from-generic c
  (R.Layer.inflate (Native c) (Admit c) (Coord c) (Good c) (domain c) (to-generic c p) m pm)

preserve : ∀ c {a b} → Good c b → Good (hs c) a → Good (hs c) (enc c b a)
preserve c {a = hz} gb ga = vz
preserve c {a = hs a} {b} gb ga =
  mono c {a = hs a} {b = hs a} (self (hs c) {a = hs a} ga) (self c {a = b} gb) gb gb ,
  preserve c {a = a} {b = b} gb (proj₂ ga)
preserve c {a = hl f} {b} gb ga =
  mono c {a = hl f} {b = hl f} (self (hs c) {a = hl f} ga) (self c {a = b} gb) gb gb ,
  (λ n → preserve c {a = f n} {b = b} gb (proj₂ ga n))
preserve c {a = hΩ (inj₁ κ) g} {b} gb ga =
  mono c {a = hΩ (inj₁ κ) g} {b = hΩ (inj₁ κ) g}
    (self (hs c) {a = hΩ (inj₁ κ) g} ga) (self c {a = b} gb) gb gb ,
  (λ e se → preserve c {a = g e} {b = b} gb (proj₂ ga e se))
preserve c {a = hΩ (inj₂ j) g} {b} gb ga =
  mono c {a = hΩ (inj₂ j) g} {b = hΩ (inj₂ j) g}
    (self (hs c) {a = hΩ (inj₂ j) g} ga) (self c {a = b} gb) gb gb ,
  (λ e se → preserve c {a = g (b ⊞ e)} {b = b ⊞ e}
    (good-add c gb se) (proj₂ ga _ (good-add c gb se)))

floor-encoded-good : ∀ n → Good (num (suc n))
  (enc (num n) (floor n) (floor (suc n)))
floor-encoded-good n = preserve (num n) {a = floor (suc n)} {b = floor n}
  (floor-good n) (floor-good (suc n))
```

每个有限层均有原非零地板实例；preserve按任意c的一条定义成立。
这不证明原at保持Good或合法性，亦不修改旧Seed0/Seed1。高层运行器
仍应消费这个域，之后才可把关系比较接到终点值验收。
