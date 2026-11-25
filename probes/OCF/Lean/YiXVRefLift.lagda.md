# YiXVRefLift
> 验收文件。档位：编译定理。原提升保持辅助合法性、比较；显式结构路径给提升 Ω 上界与零前缀嵌入 Ω 上界。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVRefLift where
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVNeutral as N
good : ∀ {κ ν} (r : κ L.◃ ν) {X} → A.Gd X → A.Gd (L.lift r X)
good {ν = L.suc ν} L.zero gx = A.Basics.up (L.suc ν) L.zero gx
good {ν = L.suc ν} (L.suc r) gx = A.Basics.up (L.suc ν) L.zero (good r gx)
good {ν = L.lim f s} (L.self n) gx = A.Basics.up (L.lim f s) (L.self n) gx
good {ν = L.lim f s} (L.lim n r) gx = A.Basics.up (L.lim f s) (L.self n) (good r gx)
mono : ∀ {κ ν} (r : κ L.◃ ν) {X Y} → A.Le X Y → A.Le (L.lift r X) (L.lift r Y)
mono {ν = L.suc ν} L.zero t = A.Basics.up-mono (L.suc ν) L.zero t
mono {ν = L.suc ν} (L.suc r) t = A.Basics.up-mono (L.suc ν) L.zero (mono r t)
mono {ν = L.lim f s} (L.self n) t = A.Basics.up-mono (L.lim f s) (L.self n) t
mono {ν = L.lim f s} (L.lim n r) t = A.Basics.up-mono (L.lim f s) (L.self n) (mono r t)
Ω : ∀ {κ ν} (r : κ L.◃ ν) → A.Le (L.lift r (L.Ω κ)) (L.Ω ν)
Ω {κ} {ν = L.suc ν} L.zero = D.pack (good L.zero (proj₁ (O.model κ))) (proj₁ (O.model (L.suc ν)))
  (D.aa (D.rfl (good L.zero (proj₁ (O.model κ)))))
  where module D = A.Layer (L.suc ν) A.Gd< A.Le<
Ω {κ} {ν = L.suc ν} (L.suc r) = D.trans (A.Basics.up-mono (L.suc ν) L.zero (Ω r)) (Ω L.zero)
  where module D = A.Layer (L.suc ν) A.Gd< A.Le<
Ω {ν = L.lim f s} (L.self n) = D.pack (good (L.self n) (proj₁ (O.model (f n))))
  (proj₁ (O.model (L.lim f s))) (D.lr n (D.rfl (good (L.self n) (proj₁ (O.model (f n))))))
  where module D = A.Layer (L.lim f s) A.Gd< A.Le<
Ω {ν = L.lim f s} (L.lim n r) = D.trans (A.Basics.up-mono (L.lim f s) (L.self n) (Ω r)) (Ω (L.self n))
  where module D = A.Layer (L.lim f s) A.Gd< A.Le<
embedded : ∀ {κ ν} → L.Simᴵ κ ν → L.Ordᶜ κ → L.Ordᶜ ν
embedded σ X = L.add L.zero σ X
embedded-good : ∀ {κ ν} {σ : L.Simᴵ κ ν} {X} → A.Gd X → A.Gd (embedded σ X)
embedded-good gx = Add.good A.Layer.gz gx
embedded-mono : ∀ {κ ν} {σ : L.Simᴵ κ ν} {X Y} → A.Le X Y → A.Le (embedded σ X) (embedded σ Y)
embedded-mono t = Add.mono A.Layer.gz t
embedded-Ω : ∀ {κ ν} (r : κ L.◃ ν) (σ : L.Simᴵ κ ν) → A.Le (embedded σ (L.Ω κ)) (L.Ω ν)
embedded-Ω {κ} {ν} r σ = D.trans
  (D.pack (embedded-good (proj₁ (O.model κ))) (good r (proj₁ (O.model κ)))
    (D.ce (L.≅-trans (N.neutral L.z≅ (L.Ω-≅ (L.≅ᴵ-refl κ)))
      (L.≅-sym (L.lift-≅ r (L.Ω-≅ (L.≅ᴵ-refl κ)))))))
  (Ω r)
  where module D = A.Layer ν A.Gd< A.Le<
actual : A.Le (embedded (λ q → L.suc q) (L.Ω (L.suc L.zero))) (L.Ω (L.suc (L.suc L.zero)))
actual = embedded-Ω L.zero (λ q → L.suc q)
```
