# 龙骨实际层号上的原 Covers（验收文件）
编译定理：龙骨 Ω 根的全孩子域不满足原 Covers，且不能供给原 Evidence；这两项分开证明。
层序取字面路径前序的严格部分；Answer 总能还原双向路径之一，不是序数值序。
复用 YiTBObs.no-total；根来自主线 tw，不把任意合法 Ω 结点并入域。
不否定实际请求的更小子域；表有 nothing 与记号依赖另见 YiCVHits。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCVDomain where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as N
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Maybe.Base using (Maybe; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiTBObs as Obs
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiTDIface as I
import OCF.Lean.YiTDOrder as Order

infix 4 _≺_
_≺_ : L → L → Set
x ≺ y = (x ≤ y) × (y ≤ x → ⊥)

trans≺ : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
trans≺ (p , np) (q , nq) = (p ∙ q) , λ r → np (q ∙ r)

frame : I.Frame
frame = record
  { A = L
  ; _<_ = _≺_
  ; trans = trans≺
  ; irrefl = λ { (p , np) → np p } }

open I.On frame public

roots : Nodes
roots = record
  { Node = ℕ
  ; Child = λ n → Tr (tw n)
  ; label = CW.hᵗ }

root-scope : ∀ n (c d : Tr (tw n)) → Scope roots (CW.hᵗ n c) (CW.hᵗ n d)
root-scope n c d = n , c , d , refl , refl

root-bound : ∀ n (c d : Tr (tw n)) →
  (CW.hᵗ n c ≤ tw (N.suc n)) × (CW.hᵗ n d ≤ tw (N.suc n))
root-bound n c d = inc c self , inc d self

root-present : Scope roots zero zero
root-present = root-scope 0 zero zero

root-mt-table : (n : ℕ) (c d : Tr (tw n)) → Maybe ((CW.hᵗ n d ≤ CW.hᵗ n c) ⊎ (CW.hᵗ n c ≤ CW.hᵗ n d))
root-mt-table n c d = proj₁ (MT.rbᶻ (tw (N.suc n))) c d

root-cw-table : (n : ℕ) (c d : Tr (tw n)) → Maybe ((CW.hᵗ n d ≤ CW.hᵗ n c) ⊎ (CW.hᵗ n c ≤ CW.hᵗ n d))
root-cw-table n c d = proj₁ (CW.rbᵗ (N.suc n)) c d

distinct-scope : Scope roots (CW.hᵗ 0 (suc zero)) (CW.hᵗ 0 (suc (suc zero)))
distinct-scope = root-scope 0 (suc zero) (suc (suc zero))

distinct-labels : CW.hᵗ 0 (suc zero) ≡ CW.hᵗ 0 (suc (suc zero)) → ⊥
distinct-labels e = Obs.1≢2 (cong Obs.d e)

mt-distinct-hole : root-mt-table 0 (suc zero) (suc (suc zero)) ≡ nothing
mt-distinct-hole = refl

cw-distinct-hole : root-cw-table 0 (suc zero) (suc (suc zero)) ≡ nothing
cw-distinct-hole = refl

no-nd-zero : ∀ {s h} → nd s h ≤ zero → ⊥
no-nd-zero ()

nonzero⊕ : ∀ {s h} b → nd s h ⊕ b ≡ zero → ⊥
nonzero⊕ zero ()
nonzero⊕ (nd _ _) ()

no-root0-top : ∀ c → CW.hᵗ 0 c ≡ tw 1 → ⊥
no-root0-top zero ()
no-root0-top (suc c) ()
no-root0-top (lim f r) ()

no-root-cover : Covers roots → ⊥
no-root-cover cover with cover zero (tw 1)
... | 0 , c , d , ex , ey = no-root0-top d ey
... | N.suc n , c , d , ex , ey = nonzero⊕ (↑ (tw (N.suc n)) c) ex

answer-path : ∀ {x y} → Answer x y → (y ≤ x) ⊎ (x ≤ y)
answer-path (inj₁ (p , _)) = inj₂ p
answer-path (inj₂ (inj₁ refl)) = inj₁ self
answer-path (inj₂ (inj₂ (p , _))) = inj₁ p

no-root-paths : (∀ x y → Scope roots x y → (y ≤ x) ⊎ (x ≤ y)) → ⊥
no-root-paths provide = Obs.no-total λ c d →
  provide (TB.h₁ c) (TB.h₁ d) (root-scope 0 c d)

no-root-evidence : Evidence (Scope roots) → ⊥
no-root-evidence E = no-root-paths λ x y q →
  answer-path (Evidence.answer E x y (Evidence.provide E x y q))

no-global : Evidence Global → ⊥
no-global E = no-root-paths λ x y _ →
  answer-path (Evidence.answer E x y (Evidence.provide E x y tt))

evidence-excludes-cover : (N : Nodes) → Evidence (Scope N) → Covers N → ⊥
evidence-excludes-cover N E cover =
  no-global (Order.Theorems.scoped→global frame E cover)

no-notation : Notation → ⊥
no-notation n = no-global (Order.Theorems.notation→global frame n)
```
