# 后继下标的记号侧基本列

验收文件；编译定理。`note` 只说记号：ψ₀(Ω_η) 的基本列是 ψ₀ 作用于 Ω_η 的 γ 链，条件为 η 是后继形状。
来源：复用 `YiANFam.cofG`、`fsnG`；Ω 后继叶的 `cof` 与 `fsT` 按 `YiMENote` 的首层展开法。
这里不提供树回灌链的保持，不能由它与 `YiTSStep` 单独宣称已得 `StepS`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTSNote where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsT; fsn; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofG; fsnG)

cofΩS : ∀ η → cof η ≡ c1 → cof (E.Ωt η) ≡ cΩ (pred η)
cofΩS []       ()
cofΩS (w ∷ ws) e = cong (E.cofψ0 (w ∷ ws)) e

fsTΩS : ∀ η → cof η ≡ c1 → ∀ ζ → fsT (E.Ωt η) ζ ≡ ζ
fsTΩS []       () ζ
fsTΩS (w ∷ ws) e ζ = cong (λ c → E.fsT0 (w ∷ ws) c ζ) e

gt0 : ∀ ν → cmpᵀ (sucT ν) [] ≡ gt
gt0 []       = refl
gt0 (_ ∷ _) = refl

note : ∀ η → cof η ≡ c1 →
       (cof (ψᴺ 0 (E.Ωt η)) ≡ cω) ×
       (∀ k → fsn (ψᴺ 0 (E.Ωt η)) k ≡ ψᴺ 0 (γT (E.Ωt η) (pred η) k))
note η e = cofG [] (E.Ωt η) (gt0 (pred η)) (cofΩS η e) ,
  λ k → trans (fsnG [] (E.Ωt η) k (gt0 (pred η)) (cofΩS η e))
                (cong (ψᴺ 0) (fsTΩS η e (γT (E.Ωt η) (pred η) k)))

fs-00 : fsn (ψᴺ 0 (Ωᴺ 1)) 0 ≡ ψᴺ 0 (Ωᴺ 0)
fs-00 = refl

fs-01 : fsn (ψᴺ 0 (Ωᴺ 1)) 1 ≡ ψᴺ 0 (ψᴺ 0 (Ωᴺ 0))
fs-01 = refl

fs-02 : fsn (ψᴺ 0 (Ωᴺ 1)) 2 ≡ ψᴺ 0 (ψᴺ 0 (ψᴺ 0 (Ωᴺ 0)))
fs-02 = refl

fs-10 : fsn (ψᴺ 0 (Ωᴺ 2)) 0 ≡ ψᴺ 0 (Ωᴺ 1)
fs-10 = refl

fs-11 : fsn (ψᴺ 0 (Ωᴺ 2)) 1 ≡ ψᴺ 0 (ψᴺ 1 (Ωᴺ 1))
fs-11 = refl

fs-12 : fsn (ψᴺ 0 (Ωᴺ 2)) 2 ≡ ψᴺ 0 (ψᴺ 1 (ψᴺ 1 (Ωᴺ 1)))
fs-12 = refl
```
