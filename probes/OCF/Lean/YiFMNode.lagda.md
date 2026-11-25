# 第 2 层较小余尾的结点与两种抬高办法
> 验收文件（读记号）。`node⁺` 是闭的非零树，`node-new` 对着 ψ₁(Ω₁)；尚无该树的旧族推导。
> 来源：分支推导调用 `YiLTFold.Self.PF`，首层换族调用 `YiFMFin`；不改树、折叠或合法性。
> 编译否定只涉及两种指定抬高：仅抬内层会变成 ℕ 共尾；同时抬两层不能以 `mc` 搬分支。
> 正规 Ω 叶的较小余尾可由 `regular-back` 吸收；这里不否定一般关系族等价。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFMNode where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiHCFam as HF
import OCF.Lean.YiGIRel as G
import OCF.Lean.YiLTFold as LF
open import OCF.Lean.YiFMFin using (new-old¹; old-new¹; p²; nu-new²)
open import OCF.Lean.YiCLFam using (fn; okf)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤¬>)

t : E.T
t = E.ψ (E.natT 1) (E.Ωt (E.natT 1)) ∷ []

fold¹ : Tr (fn 1) → O.Tr⁺ (fn 1)
fold¹ = TB.ψ (fn 1) (okf 1) (MT.rbᶻ (fn 1)) (F.B₀ (fn 1))
  (fn 1) P.self (O.Ωt (fn 1))

g : Tr (fn 1) → Tr (fn 2)
g c = proj₁ (O.upz tt (fold¹ c))

node⁺ : O.Tr⁺ (fn 2)
node⁺ = O.Ω⁺ p² (λ c → O.upz tt (fold¹ c))

at-g : ∀ η c → G.R (fn 1) η c → G.R (fn 2) (E.ψ (E.natT 1) η ∷ []) (g c)
at-g η c m = H.mU H.mz (old-new¹ (LF.Self.PF 0 (okf 1) (MT.rbᶻ (fn 1))
  (F.B₀ (fn 1)) (O.Ωt (fn 1)) (HF.Mβ 0) (new-old¹ m)))

node-new : G.R (fn 2) t (proj₁ node⁺)
node-new = H.mΩ refl nu-new² (λ η c m → at-g η c m)

regular-back : ∀ {h : Tr (fn 1) → Tr (fn 2)}
  → (∀ η c → HF.M 1 η c → HF.M 2 η (h c))
  → HF.M 2 (E.Ωt (E.natT 1)) (Ω p² h)
regular-back r = H.mc {t = E.Ωt (E.natT 2)}
  (inj₁ (E.hd< (E.lv< (E.tl< E.[]<))))
  (H.mΩ {t = E.Ωt (E.natT 2)} refl refl r)

inner↑ : E.T
inner↑ = E.ψ (E.natT 1) (E.Ωt (E.natT 2)) ∷ []

both↑ : E.T
both↑ = E.ψ (E.natT 2) (E.Ωt (E.natT 2)) ∷ []

cof-t : E.cof t ≡ E.cΩ []
cof-t = refl

cof-inner↑ : E.cof inner↑ ≡ E.cω
cof-inner↑ = refl

no-inner↑-slot : E.cof inner↑ ≡ E.cΩ (E.natT 1) → ⊥
no-inner↑-slot ()

cof-both↑ : E.cof both↑ ≡ E.cΩ (E.natT 1)
cof-both↑ = refl

fsT-t : ∀ η → E.fsT t η ≡ E.ψ (E.natT 1) η ∷ []
fsT-t η = refl

fsT-both↑ : ∀ η → E.fsT both↑ η ≡ E.ψ (E.natT 2) η ∷ []
fsT-both↑ η = refl

no-both↑-branch-mc : ∀ η → E.fsT both↑ η ≤ᵀ E.fsT t η → ⊥
no-both↑-branch-mc η le = ≤¬> le (E.hd< (E.lv< (E.tl< E.[]<)))
```
