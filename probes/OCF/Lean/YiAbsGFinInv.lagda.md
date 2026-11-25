# 抽象理论 (十五): "槽位不保留" 的否定在有限层号关系族上的陈述

> 验收文件 (读记号, 读具体块). 判决: 编译定理, 无前提. `YiAbsGNeg.Inv.inv` 用在 `YiANFam.M` 上: 余尾为 Ω_{κ+1} 的记号项只能对着含 Ω 结点的树 (`invᶠ`; `Hᶠ n o`: o 在某个 Ω 结点之上, 或是孩子含 Ω 结点的嵌入之上).
> 推论 (`no-node→¬M`): 不含 Ω 结点的树与余尾为 Ω 的记号项没有 `M` 关系. 所以折叠把槽位丢掉 (输出不含结点) 而记号一侧按规则保留余尾时, 这一行不保持 `M`.
> 不否定什么: 只对 `M` 这一族 (六条规则生成的关系); 没有在候选 A 或龙骨原型的块上陈述.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGFinInv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiAbsLeg using (ChT⁺)
import OCF.Align.EboLeanDef as E
open E using (cof; c0; c1; cω; cΩ)
open import OCF.Lean.YiANFam using (fin; M)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGNeg
open import OCF.Lean.YiAbsGFin

data Hᶠ : (n : ℕ) → Tr (fin n) → Set where
  hn : ∀ {n} (p : Pos (fin n)) (g : Br (fin n) p → Tr (fin n)) → Hᶠ n (Ω p g)
  hw : ∀ {n x x′} → Hᶠ n x → fin n ⊢ x ◃ x′ → Hᶠ n x′
  hc : ∀ {n x y e} → Hᶠ n y → Hᶠ (suc n) (up x tt y e)

cof++ne : ∀ t a as → cof (t ++ (a ∷ as)) ≡ cof (a ∷ as)
cof++ne []           a as = refl
cof++ne (x ∷ [])     a as = refl
cof++ne (x ∷ x′ ∷ t) a as = cof++ne (x′ ∷ t) a as

module _ (κ : E.T) where
  private
    no0 : ∀ {c} → c ≡ c0 → c ≡ cΩ κ → ⊥
    no0 refl ()
    no1 : ∀ {c} → c ≡ c1 → c ≡ cΩ κ → ⊥
    no1 refl ()
    noω : ∀ {c} → c ≡ cω → c ≡ cΩ κ → ⊥
    noω refl ()

    hUs : (m : ℕ) → (∀ {s o} → M m s o → cof s ≡ cΩ κ → Hᶠ m o)
        → (c : ⊤) {t s : E.T} {x : Tr (fin (suc m))} (y : ChT⁺ (fin (suc m)) c)
        → cof (t ++ s) ≡ cΩ κ → (cof t ≡ cΩ κ → Hᶠ (suc m) x) → M m s (proj₁ y) → Hᶠ (suc m) (up x c (proj₁ y) (proj₂ y))
    hUs m rec c {t = t} {s = []}     {x = x} (y , e) w q ch =
      hw (q (subst (λ r → cof r ≡ cΩ κ) (++-identityʳ t) w)) (◃u x c y e)
    hUs m rec c {t = t} {s = a ∷ as} {x = x} (y , e) w q ch = hc (rec ch (trans (sym (cof++ne t a as)) w))

  invᶠ : ∀ n {s o} → M n s o → cof s ≡ cΩ κ → Hᶠ n o
  invᶠ zero    = Neg.Inv.inv gradedᶠ domsᶠ (genᶠ zero) κ (Hᶠ zero) no0 no1 noω hn hw (λ ())
  invᶠ (suc m) = Neg.Inv.inv gradedᶠ domsᶠ (genᶠ (suc m)) κ (Hᶠ (suc m)) no0 no1 noω hn hw
    (hUs m (λ r e → invᶠ m r e))

  no-node→¬M : ∀ n {s o} → (Hᶠ n o → ⊥) → cof s ≡ cΩ κ → M n s o → ⊥
  no-node→¬M n no e r = no (invᶠ n r e)
```
