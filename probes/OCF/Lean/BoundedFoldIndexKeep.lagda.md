# 指标拷贝在实际输入世界中的双向可入律

这里验证 raw 树折叠所需的 Bd/Pr，不把 KS 世界和路径证书的世界混同。
源是 upL 遇到 Ω 时引入的 node，目标是 ΩL 前缀；ext 正好从目标
投影这个指标世界。所有映射通过两处选定上下文，不比较裸下标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedFoldIndexKeep where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; pw; toC; frC; bdTo; bdFr; prFr)
open import OCF.Lean.BoundedIndexContext using (omega-context)
open import OCF.Lean.BoundedFoldWorld using (assemble; module Relative)

tofr : ∀ {T S} (c : Ctx T S) κ e → toC c κ (frC c κ e) ≡ e
tofr here κ e = refl
tofr (viaS c) κ e = tofr c (inj₁ κ) e
tofr (viaL c i) κ e = tofr c (i , κ) e

prTo : ∀ {T S} (c : Ctx T S) κ {W e d} →
  Pr S κ (pw c W) e d → Pr T (ek c κ) W (toC c κ e) (toC c κ d)
prTo here κ p = p
prTo (viaS c) κ p = prTo c (inj₁ κ) p
prTo (viaL c i) κ p = prTo c (i , κ) p

index-context : ∀ P k κ (h : E (Lv k) κ → LH) →
  Ctx (Lv (P ⊕L node k κ h)) (step (Lv (lvl k κ)))
index-context P lz () h
index-context P (ls k) (inj₁ κ) h = index-context P k κ h
index-context P (ls k) (inj₂ _) h = viaL here (inj₁ tt)
index-context P (ll f) (n , κ) h = index-context P (f n) κ h
index-context P (lΩ k g) (inj₁ _ , inj₁ κ) h = index-context P k κ h
index-context P (lΩ k g) (inj₁ _ , inj₂ _) h = viaL here (inj₁ tt)
index-context P (lΩ k g) (inj₂ e , κ) h = index-context P (g e) κ h

index-project : ∀ P k κ h u v →
  pw (index-context P k κ h) (assemble P k κ h u v) ≡ u
index-project P lz () h u v
index-project P (ls k) (inj₁ κ) h u v = index-project P k κ h u v
index-project P (ls k) (inj₂ _) h u v = refl
index-project P (ll f) (n , κ) h u v = index-project P (f n) κ h u v
index-project P (lΩ k g) (inj₁ _ , inj₁ κ) h u v = index-project P k κ h u v
index-project P (lΩ k g) (inj₁ _ , inj₂ _) h u v = refl
index-project P (lΩ k g) (inj₂ e , κ) h u v = index-project P (g e) κ h u v

module Keep (k : LH) (κ : K (Lv k)) (h : E (Lv k) κ → HB (Lv k)) where
  open Relative k
  src = index-context P k κ (λ e → upL k (h e))
  dst = omega-context k κ
  S = T (hΩ κ h)
  D = Lv P
  I = step (Lv (lvl k κ))

  projected : ∀ v W → pw src (ext (hΩ κ h) v W) ≡ pw dst v
  projected v W = index-project P k κ (λ e → upL k (h e)) _ _

  back : ∀ j → E D (ek dst j) → E S (ek src j)
  back j e = toC src j (frC dst j e)

  -- 目标可入坐标映回原始源坐标。
  target-bd : ∀ j {v W e} → Bd D (ek dst j) e v →
    Bd S (ek src j) (back j e) (ext (hΩ κ h) v W)
  target-bd j {v} {W} {e} b = bdTo src j
    (subst (λ u → Bd I j (frC dst j e) u) (sym (projected v W)) (bdFr dst j b))

  target-pr : ∀ j {v W e d} → Pr D (ek dst j) v e d →
    Pr S (ek src j) (ext (hΩ κ h) v W) (back j e) (back j d)
  target-pr j {v} {W} {e} {d} p = prTo src j
    (subst (λ u → Pr I j u (frC dst j e) (frC dst j d))
      (sym (projected v W)) (prFr dst j p))

  -- 每个源可入坐标都有真实目标坐标，且映回完全相同。
  source-bd : ∀ j {v W c} → Bd S (ek src j) c (ext (hΩ κ h) v W) →
    Σ (E D (ek dst j)) (λ d → (back j d ≡ c) × Bd D (ek dst j) d v)
  source-bd j {v} {W} {c} b = toC dst j (frC src j c) ,
    trans (cong (toC src j) (OCF.Lean.LHRecLeg.frto dst j (frC src j c))) (tofr src j c) ,
    bdTo dst j (subst (λ u → Bd I j (frC src j c) u) (projected v W) (bdFr src j b))
```

三条律直接针对已有 ext，并非把需要的相容性留作前提。没有要求源
原世界 W 与目标 v 相容；ext 会重设指标槽。尚未包括全部 B 的所有
keep 情形、同层/上层反馈合法性，或动态路径证书的 Ad/nx 比较。
