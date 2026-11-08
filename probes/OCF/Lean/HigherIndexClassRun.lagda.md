# 含 Ω 高度的带证原生分类及公共界决定

指标旧种类沿已有 first-index 回到前缀；经过指标分支时，Position
提供 hLim 所需的实际可入证据。后续比较由原 cmpB 在同一合法世界、
同一合法 B 中执行，不新增三歧或全局判等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexClassRun where
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (ls; lz)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; frC; toC; frto)
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Lean.BoundedIndexContext using (first-index)
open import OCF.Lean.HigherIndexClassIf

tofr : ∀ {T S} (c : Ctx T S) κ e → toC c κ (frC c κ e) ≡ e
tofr here κ e = refl
tofr (viaS c) κ e = tofr c (inj₁ κ) e
tofr (viaL c n) κ e = tofr c (n , κ) e

raise : ∀ {w c d A} → c ⊲[ w ] d → Class w c A → Class w d A
raise p (base κ to fr a b) = base κ to fr a b
raise p (rank i q to fr a b) = rank i (⊲ᴮ-tr q p) to fr a b

classify : ∀ w c κ → Position w c κ → Class w c (E (Native c) κ)
classify w hz κ p = base κ (λ e → e) (λ e → e) (λ e → refl) (λ e → refl)
classify w (hs c) (inj₁ κ) p = raise (hsuc hself) (classify w c κ p)
classify w (hs c) (inj₂ _) p = rank c hself (λ e → e) (λ e → e) (λ e → refl) (λ e → refl)
classify w (hl f) (n , κ) p = raise (hlim n hself) (classify w (f n) κ p)
classify w (hΩ (inj₁ ()) g) κ p
classify w (hΩ (inj₂ _) g) (inj₁ _ , κ) p =
  base (ek first-index κ) (frC first-index κ) (toC first-index κ)
    (frto first-index κ) (tofr first-index κ)
classify w (hΩ (inj₂ _) g) (inj₂ e , κ) (bd , p) =
  raise (hLim bd hself) (classify w (g e) κ p)

instance-classification : Classification
instance-classification = record { classify = classify }

-- 路径直接给目标上下文，坐标仍为原类型。
along : ∀ {w i t} → hs i ⊲[ w ] t → K (Native t)
along p = ek (path-context prefix (ls lz) p) (inj₂ tt)
fr-along : ∀ {w i t} (p : hs i ⊲[ w ] t) → E (Native t) (along p) → HB (Native i)
fr-along p = frC (path-context prefix (ls lz) p) (inj₂ tt)

data Decision (w : Wd U) (B t : HB U) (A : Set) : Set where
  keep : (κ : K (Native t)) → (E (Native t) κ → A) → Decision w B t A
  same : (HB (Native t) → A) → Decision w B t A
  above : (i : HB U) → hs i ⊲[ w ] B → t ⊲[ w ] i →
    (HB (Native i) → A) → Decision w B t A

pick : ∀ {w B t i A} → (HB (Native i) → A) → hs i ⊲[ w ] B →
  (t ⊲[ w ] hs i) ⊎ (hs i ⊲[ w ] t) → Decision w B t A
pick to pi (inj₂ q) = keep (along q) (λ e → to (fr-along q e))
pick to pi (inj₁ hself) = keep (inj₂ tt) to
pick to pi (inj₁ (hsuc hself)) = same to
pick to pi (inj₁ (hsuc q@(hsuc _))) = above _ pi q to
pick to pi (inj₁ (hsuc q@(hlim _ _))) = above _ pi q to
pick to pi (inj₁ (hsuc q@(hLim _ _))) = above _ pi q to

decide : ∀ {w B t A} → t ⊲[ w ] B → LgW U w → LgB B → Class w B A → Decision w B t A
decide {w} {t = t} pt lw lB (base κ to fr a b) =
  keep (ek ctx κ) (λ e → to (frC ctx κ e))
  where
  ctx : Ctx (Native t) (Native hz)
  ctx = path-context prefix (ls lz) (z⊲ᴮ {w = w} t)
decide pt lw lB (rank i pi to fr a b) = pick to pi (cmpB pi pt lw lB)
```

特别是 hLim 已不再荒谬；它是高层坐标中的真实分支路径。本篇给的是
分类和决定的总函数，尚不把原 Cd 运行器硬套到新类型，也没有下降值
或终点强度定理。下一义务是把 Position 穿过实际回灌/世界更新。
