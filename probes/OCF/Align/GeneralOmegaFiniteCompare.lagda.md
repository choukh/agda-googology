# 原有限比较与树侧分类的同一步对齐

验收辅助，共用冻结AmbientIf。原比较的两条路径都在nat(suc B)
之下，树侧分类沿同一个Within B m；不在裸Ordᴵ上增加任何判定。
除分派标签外，也保存相关坐标的真实运输，以免在keep分支偷用
任意函数同余，或在collapse分支换掉原低层HB。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteCompare where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaFiniteObserveIf as I
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaFiniteRank using (nat; ambient)
open import OCF.Align.GeneralOmegaFiniteAmbientIf using (rank; bound; canonical; Read; Coord)

cast : ∀ {i j} → i ≡ j → L.Ordᶜ (nat i) → L.Ordᶜ (nat j)
cast e = subst (λ k → L.Ordᶜ (nat k)) e

Cases : L.Ordᴵ → L.Ordᴵ → Set
Cases a b = (a L.≺ᴵ b) ⊎ ((b L.≺ᴵ a) ⊎ (a L.≅ᴵ b))
data Collapsed {a b} : Cases a b → Set where
  above : ∀ p → Collapsed (inj₂ (inj₁ p))
  same : ∀ e → Collapsed (inj₂ (inj₂ e))

decision : ∀ {B m} → I.Within B m → (κ : K (I.F B)) →
  Cases (nat (rank B κ)) (nat m)
decision p κ = L.<ᴵ-dec (L.suc (bound _ κ)) (ambient p)

keep-choice : ∀ {B m} (κ : K (I.F B)) (κ′ : K (I.F m)) →
  rank B κ ≡ rank m κ′ → Cases (nat (rank B κ)) (nat m)
keep-choice {B} {m} κ κ′ e = inj₁ (L.via
  (subst (λ k → nat (rank B κ) L.≅ᴵ nat k) e (L.≅ᴵ-refl _)) (bound m κ′))

data Match {B m} (p : I.Within B m) (κ : K (I.F B)) :
  I.View B m (E (I.F B) κ) → Set where
  kept : ∀ {κ′ fr} (e : rank B κ ≡ rank m κ′) →
    decision p κ ≡ keep-choice κ κ′ e →
    (∀ {x c} → Coord m κ′ x c → Coord B κ (cast (sym e) x) (fr c)) →
    Match p κ (I.keep κ′ fr)
  cut : ∀ {k q to} (e : rank B κ ≡ k) → Collapsed (decision p κ) →
    (∀ {x c} → Read k (canonical k) x c → Coord B κ (cast (sym e) x) (to c)) →
    Match p κ (I.collapse k q to)

raise-match : ∀ {B m} {p : I.Within B m} {κ v} → Match p κ v →
  Match (I.lower p) (inj₁ κ) (I.raise v)
raise-match (kept e d c) = kept e d c
raise-match (cut e d c) = cut e d c

new-collapse : ∀ {B m} (p : I.Within B m) →
  Collapsed (decision (I.lower p) (inj₂ tt))
new-collapse I.here = same (L.≅ᴵ-refl _)
new-collapse (I.lower p) = above (L.via (L.≅ᴵ-refl _) (ambient p))

match : ∀ {B m} (p : I.Within B m) κ → Match p κ (I.view p κ)
match I.here κ = kept refl refl (λ r → r)
match (I.lower p) (inj₁ κ) = raise-match (match p κ)
match (I.lower p) (inj₂ _) = cut refl (new-collapse p) (λ r → r)
```

match对全部有限路径与原kind实填；keep保存字面rank等式，collapse
反馈关系从原rank层读取。它只是统一分派与坐标证书，完整观察值
的模拟仍须递归原Bridge及其真实反馈轨道。
