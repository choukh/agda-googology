# 配对审计：有限塔每个新增秩的反馈坐标都有完整世界

这里只选择有限塔的后继新增种类，不假设前缀中任意种类的世界截面。
合法原始反馈坐标直接放在它所属的后继层，上下其它层填规范世界。
再用 BoundedFiniteWorld 放进真实 Ω 源。没有 PS 或 ClP 前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedMixedNegWorld where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLeg using (w₀L; lw₀L)
open import OCF.Lean.BoundedFoldIf
open import OCF.Lean.BoundedContextClosed using (num)
import OCF.Lean.BoundedFiniteWorld as FW

Sn : ℕ → KS
Sn n = T (up (num n))

data Rank : ∀ n → K (Sn n) → Set where
  fresh : ∀ n → Rank (suc n) (inj₂ tt)
  older : ∀ {n κ} → Rank n κ → Rank (suc n) (inj₁ κ)

LegalCoordinate : ∀ {n κ} → Rank n κ → E (Sn n) κ → Set
LegalCoordinate (fresh n) c = LgB c
LegalCoordinate (older r) c = LegalCoordinate r c

world : ∀ {n κ} (r : Rank n κ) → E (Sn n) κ → Wd (Sn n)
world (fresh n) c = w₀L (G (up (num n))) , c
world (older r) c = world r c , hz

legal-world : ∀ {n κ} (r : Rank n κ) c → LegalCoordinate r c → LgW (Sn n) (world r c)
legal-world (fresh n) c lc = lw₀L (G (up (num n))) , lc
legal-world (older r) c lc = legal-world r c lc , tt

admitted : ∀ {n κ} (r : Rank n κ) c → Bd (Sn n) κ c (world r c)
admitted (fresh n) c = hself
admitted (older r) c = admitted r c

component-world : ∀ {n κ} (r : Rank n κ) c → LegalCoordinate r c →
  Σ (Wd (Sn n)) (λ W → LgW (Sn n) W × Bd (Sn n) κ c W)
component-world r c lc = world r c , legal-world r c lc , admitted r c

whole-world : ∀ {n κ} (r : Rank n κ) c → LegalCoordinate r c →
  Σ (Wd (T FW.B)) (λ W → LgW (T FW.B) W × Bd (T FW.B) (inj₂ (num n) , κ) c W)
whole-world {n} {κ} r c lc =
  FW.Whole.world n (world r c) , FW.Whole.legal n (world r c) (legal-world r c lc) ,
  FW.Whole.admitted n (world r c) κ (admitted r c)

rank-pos : ∀ β {n κ} → Rank n κ → Pos β (up (num n)) κ
rank-pos β (fresh n) = tt
rank-pos β (older r) = rank-pos β r

module SafeWorld (β : Cd) {n κ} (r : Rank n κ) (pn : num n ⊲ β) where
  selected : K (Safe β FW.B)
  selected = (inj₂ (num n) , κ) , (pn , rank-pos β r)

  branch-legal : ∀ (g : E (Safe β FW.B) selected → HB (Safe β FW.B)) →
    LgB (hΩ selected g) → ∀ c → LegalCoordinate r c → LgB (g c)
  branch-legal g lg c lc = proj₂ lg
    (FW.Whole.legal n (world r c) (legal-world r c lc))
    (FW.Whole.admitted n (world r c) κ (admitted r c))
```

SafeWorld 的种类证据始终携带 num n⊲β；本定理没有比较裸下标。
LegalCoordinate 在所选秩处就是现有 LgB，不增加坐标语法限制。
范围：解决每个有限组件的新增秩反馈入界，不包含原始 fold 的步进保持或输出合法性。
翻译账：只按后继层结构组装世界，没有新增树构造子或记号规则。

```agda
open import OCF.Lean.LHRecFl using (flL; Lg-flL)

-- 第 2 有限组件内的旧秩 0，反馈坐标为非纯前缀地板。
example : Σ (Wd (T FW.B)) (λ W → LgW (T FW.B) W ×
  Bd (T FW.B) (inj₂ (num 2) , inj₁ (inj₂ tt)) (flL P) W)
example = whole-world (older (fresh 0)) (flL P) (Lg-flL P)

module ExampleSafe = SafeWorld (num 2) (older (fresh 0)) hself
example-constant : HB (Safe (num 2) FW.B)
example-constant = hΩ ExampleSafe.selected (λ _ → hz)
example-constant-legal : LgB example-constant
example-constant-legal = (λ lw b b′ p → hself) , (λ lw b → tt)
```
