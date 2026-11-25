# F2 的可数层号定理确实允许目标第 1 层
验收文件；编译定理：复用 YiLSFold.M.MS 得 lower-one，有限层 4 的前提全部实填。
结论是 YiLSRel.Rel 与 Align.Level 的参照，尚未接到 EboLean 的 YiANFam.M 1。
不重证 MS，不改折叠；可直接搬运的有限层关系见 YiPVSmall。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPVF2 where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
import OCF.Lean.YiLSFold as V
import OCF.Lean.YiLSRel as R
import OCF.Align.Level as L

one : F.L
one = F.suc F.zero
lower-one : ∀ {ℓ κ} (nl : V.NL ℓ) (ε : F.Ev ℓ) (ρ : F.Rt ℓ) (base : F.Base ℓ)
  → V.OKB ℓ base → R.Corr κ ℓ → (w : F._≤_ one ℓ)
  → (p : L.suc L.zero L.<ᴵ L.suc κ)
  → R.Rel one (L.ψ p (λ q → L.suc q) (L.Ω κ))
    (F.ψs ℓ ε ρ base one w (F.bs base one w) (F.ns base one w) (F.Ωt ℓ))
lower-one nl ε ρ base ok c w p =
  V.M.MS nl (ε , ρ , base) ok w (V.can (ε , ρ , base) w) refl
    (V.START nl c) p (R.cs R.cz) (λ q → L.suc q)

four : F.L
four = F.suc (F.suc (F.suc one))
four-nl : V.NL four
four-nl = V.n+ (V.n+ (V.n+ (V.n+ V.n0)))
four-corr : R.Corr (L.natᴵ 4) four
four-corr = R.cs (R.cs (R.cs (R.cs R.cz)))
four-one : F._≤_ one four
four-one = F.ins (F.ins (F.ins F.self))
four-p : L.suc L.zero L.<ᴵ L.suc (L.natᴵ 4)
four-p = L.suc (L.suc (L.suc L.zero))
four-instance : R.Rel one (L.ψ four-p (λ q → L.suc q) (L.Ω (L.natᴵ 4)))
  (F.ψs four tt tt (F.B₀ four) one four-one (F.Ωt one) (F.Ωt-nz one) (F.Ωt four))
four-instance = lower-one four-nl tt tt (F.B₀ four) (V.ok-B₀ four) four-corr four-one four-p
```
