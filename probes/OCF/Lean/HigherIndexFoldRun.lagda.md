# 高指标树的实际结构递归折叠

旧指标先累加合法化Cd再扩低世界；新指标按原J₁回灌含Ω的合法化高度。
分量沿同一个合法公共界作keep/same/above。全部递归都作用在原源子树。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexFoldRun where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.CRw as C
open import OCF.Lean.LHRecTy using (ls; lz; FXL)
open import OCF.Lean.LHRecLeg using (Ctx; viaL; ek; frC; J₁)
import OCF.Lean.LHRecLeg as Leg
open import OCF.Lean.LHRecIf using (LHRecIf)
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_; upL)
open import OCF.Lean.HigherIndexClassIf
open import OCF.Lean.HigherIndexClassRun using (raise; classify; decide; keep; same; above)
open import OCF.Lean.HigherIndexFoldIf

index-context : ∀ {β} t → Ctx (Native t) (step U)
index-context {β} t = viaL {F = FXL lz (λ c → ΩL lz ⊕L upL lz c)} (path-context prefix k (z⊲ᴮ {w = tt , β} t)) (inj₂ (hs hz))

fold : ∀ β → LgB β → ∀ B → LgB B → ∀ t → t ⊲[ tt , β ] B →
  (a : HB Source) → Path β B a → HB (Native t)
fold β lβ B lB t pt hz p = hs hz
fold β lβ B lB t pt (hs a) p = Ops.repeat _ (fold β lβ B lB t pt a p)
fold β lβ B lB t pt (hl f) p = hl (λ n → fold β lβ B lB t pt (f n) (p n))
fold β lβ B lB t pt (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) p
fold β lβ B lB t pt (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) p =
  hΩ (ek ctx (inj₁ (inj₂ tt))) branch
  where
  ctx = index-context {β} t
  branch : _ → HB (Native t)
  branch raw = fold (hs e) le B lB t (⊲ᴮ↑ (tt , hsuc (⊞-fst β (C.leg c))) pt)
    (f e) (p e (⊞-fst β (C.leg c)) le)
    where
    c : Cd
    c = frC ctx (inj₁ (inj₂ tt)) raw
    e : Cd
    e = β ⊞ C.leg c
    le : LgB e
    le = Lg-⊞ β (C.leg c) lβ (C.Lg-leg c)
fold β lβ B lB t pt (hΩ (inj₁ _ , inj₂ _) f) p =
  hΩ (ek ctx (inj₂ tt)) branch
  where
  ctx = index-context {β} t
  branch : _ → HB (Native t)
  branch raw = fold β lβ (hs e) le t (⊲ᴮ-tr pt (hsuc (⊞-fst B (Leg.leg k c))))
    (f e) (p e ad)
    where
    c : HB U
    c = frC ctx (inj₂ tt) raw
    e : HB U
    e = B ⊞ Leg.leg k c
    le : LgB e
    le = Lg-⊞ B (Leg.leg k c) lB (Leg.Lg-leg k c)
    ad = LHRecIf.adm-sh J₁ k {W = (tt , β) , B} c ((tt , lβ) , lB)
fold β lβ B lB t pt (hΩ (inj₂ c , κ) f) ((pc , pos) , p)
  with decide pt (tt , lβ) lB (raise pc (classify (tt , β) c κ pos))
... | keep κ′ fr = hΩ κ′ (λ e → fold β lβ B lB t pt (f (fr e)) (p (fr e)))
... | same to = diagonal
  (λ e → fold β lβ B lB t pt (f (to e)) (p (to e)))
  (λ e → fold β lβ B lB t pt (f (to e)) (p (to e)))
... | above i pi q to = diagonal
  (λ e → fold β lβ B lB i (⊲ᴮ-tr (hsuc hself) pi) (f (to e)) (p (to e)))
  (λ e → fold β lβ B lB t pt (f (to e)) (p (to e)))

instance-local : LocalFold
instance-local = record { fold = fold }
```

index-context同时保留原指标分量的旧种类与新种类，避免将同一分量拆成
两个不相干副本。这里不宣称fold普遍保合法或值；Path实例另篇给出。
