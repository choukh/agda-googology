# 配对审计：实际累加扩界有世界扩张器

任意上下文的世界截面并非本定理的前提。对实际 B⊞R 递归，把旧世界
同时放进所有含 B 前缀的分支；Ω 的指标分量用规范合法世界。
因此不需要判断两个不可数坐标相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedGrowthNegAdd where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (pw; here; viaS; viaL; rfL; w₀L; lw₀L)
open import OCF.Lean.BoundedContextRun using (node-context; path-context)
open import OCF.Lean.BoundedGrowthIf
open import OCF.Lean.BoundedGrowthRun using (pw-compose)

node-world : ∀ P k κ (h : E (Lv k) κ → LH) →
  (∀ e → Wd (Lv (P ⊕L h e))) → Wd (Lv (P ⊕L node k κ h))
node-world P lz () h v
node-world P (ls k) (inj₁ κ) h v = node-world P k κ h v
node-world P (ls k) (inj₂ _) h v (inj₁ _) = w₀L k , hz
node-world P (ls k) (inj₂ _) h v (inj₂ e) = v e
node-world P (ll f) (n , κ) h v = node-world P (f n) κ h v
node-world P (lΩ k g) (inj₁ _ , inj₁ κ) h v = node-world P k κ h v
node-world P (lΩ k g) (inj₁ _ , inj₂ _) h v (inj₁ _) = w₀L k , hz
node-world P (lΩ k g) (inj₁ _ , inj₂ _) h v (inj₂ e) = v e
node-world P (lΩ k g) (inj₂ c , κ) h v = node-world P (g c) κ h v

node-legal : ∀ P k κ h v → (∀ e → LgW (Lv (P ⊕L h e)) (v e)) →
  LgW (Lv (P ⊕L node k κ h)) (node-world P k κ h v)
node-legal P lz () h v l
node-legal P (ls k) (inj₁ κ) h v l = node-legal P k κ h v l
node-legal P (ls k) (inj₂ _) h v l (inj₁ _) = lw₀L k , tt
node-legal P (ls k) (inj₂ _) h v l (inj₂ e) = l e
node-legal P (ll f) (n , κ) h v l = node-legal P (f n) κ h v l
node-legal P (lΩ k g) (inj₁ _ , inj₁ κ) h v l = node-legal P k κ h v l
node-legal P (lΩ k g) (inj₁ _ , inj₂ _) h v l (inj₁ _) = lw₀L k , tt
node-legal P (lΩ k g) (inj₁ _ , inj₂ _) h v l (inj₂ e) = l e
node-legal P (lΩ k g) (inj₂ c , κ) h v l = node-legal P (g c) κ h v l

node-project : ∀ P k κ h v e →
  pw (node-context P k κ h e) (node-world P k κ h v) ≡ v e
node-project P lz () h v e
node-project P (ls k) (inj₁ κ) h v e = node-project P k κ h v e
node-project P (ls k) (inj₂ _) h v e = refl
node-project P (ll f) (n , κ) h v e = node-project P (f n) κ h v e
node-project P (lΩ k g) (inj₁ _ , inj₁ κ) h v e = node-project P k κ h v e
node-project P (lΩ k g) (inj₁ _ , inj₂ _) h v e = refl
node-project P (lΩ k g) (inj₂ c , κ) h v e = node-project P (g c) κ h v e

module Add (P k : LH) (B : HB (Lv k)) (W : Wd (Lv (P ⊕L upL k B))) where
  future : ∀ R → Wd (Lv (P ⊕L upL k (B ⊞ R)))
  future hz = W
  future (hs R) = future R , hz
  future (hl f) = λ n → future (f n)
  future (hΩ κ h) = node-world P k κ (λ e → upL k (B ⊞ h e)) (λ e → future (h e))

  legal : LgW (Lv (P ⊕L upL k B)) W → ∀ R →
    LgW (Lv (P ⊕L upL k (B ⊞ R))) (future R)
  legal l hz = l
  legal l (hs R) = legal l R , tt
  legal l (hl f) = λ n → legal l (f n)
  legal l (hΩ κ h) = node-legal P k κ (λ e → upL k (B ⊞ h e))
    (λ e → future (h e)) (λ e → legal l (h e))

  project : ∀ w R → pw (path-context P k (⊞-fst {w = w} B R)) (future R) ≡ W
  project w hz = refl
  project w (hs R) rewrite pw-compose (viaS here) (path-context P k (⊞-fst {w = w} B R)) (future R , hz) = project w R
  project w (hl f) rewrite pw-compose (viaL {F = λ n → Lv (P ⊕L upL k (B ⊞ f n))} here 0) (path-context P k (⊞-fst {w = w} B (f 0))) (future (hl f)) = project w (f 0)
  project w (hΩ κ h)
    rewrite pw-compose (node-context P k κ (λ e → upL k (B ⊞ h e)) (bot (Lv k) κ))
      (path-context P k (⊞-fst {w = w} B (h (bot (Lv k) κ)))) (future (hΩ κ h))
          | node-project P k κ (λ e → upL k (B ⊞ h e)) (λ e → future (h e)) (bot (Lv k) κ)
    = project w (h (bot (Lv k) κ))

  growth : ∀ w R → LgW (Lv (P ⊕L upL k B)) W →
    WorldGrowth P k w B (B ⊞ R) (⊞-fst B R) W
  growth w R l = record
    { future = future R
    ; legal-future = legal l R
    ; extends = subst (λ V → _≤w_ (Lv (P ⊕L upL k B)) W V)
        (sym (project w R)) (rfL (P ⊕L upL k B) W) }
```

累加项 R 可含任意 Ω 分支；世界扩张甚至不要求 R 合法。若要新界合法，
仍应另用 Lg-⊞ 提供 B 与 R 的合法性。project 精确保留旧世界，不只保可入性。
本篇没有给任意 C、任意路径的世界截面，也没有折叠或强度定理。

翻译账：新世界扩张由现有树加法的右递归与世界投影要求导出，未增加记号式
构造子、阶段专属闭包前提或标签证书。它挑战的是“动态扩界必须先有任意
上下文截面”的判断；仅实际累加形状已足够给出本轮正面实例。
