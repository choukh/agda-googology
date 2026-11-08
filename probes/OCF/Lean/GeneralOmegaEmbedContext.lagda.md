# 保实际code的字面上下文

跨层证据不仅给种类位置，还证明实际回灌编码经反向坐标映射精确回到
原编码。下列所有基本注入均有实例，覆盖lΩ的指标与全部原分量。
这不预设分量层号函数对坐标Same保持。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedContext where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; ek; frC)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Lean.GeneralOmegaEmbedIf

record Embedding (x y : LH) : Set₁ where
  field
    ctx : Ctx (Lv y) (Lv x)
    code-back : ∀ κ d → frC ctx κ (code y (ek ctx κ) d) ≡ code x κ d
open Embedding public

identity : ∀ x → Embedding x x
identity x = record { ctx = here ; code-back = λ κ d → refl }
stepE : ∀ x → Embedding x (ls x)
stepE x = record { ctx = viaS here ; code-back = λ κ d → refl }
sumE : ∀ f n → Embedding (f n) (ll f)
sumE f n = record { ctx = viaL here n ; code-back = λ κ d → refl }
indexE : ∀ k g → Embedding (ls k) (lΩ k g)
indexE k g = record { ctx = viaL {F = FXL k g} here (inj₁ tt) ; code-back = λ { (inj₁ κ) d → refl ; (inj₂ _) d → refl } }
branchE : ∀ k g e → Embedding (g e) (lΩ k g)
branchE k g e = record { ctx = viaL {F = FXL k g} here (inj₂ e) ; code-back = λ κ d → refl }

put : ∀ {x y} → Embedding x y → HB (Lv x) → HB (Lv y)
put j hz = hz
put j (hs a) = hs (put j a)
put j (hl f) = hl (λ n → put j (f n))
put j (hΩ κ f) = hΩ (ek (ctx j) κ) (λ e → put j (f (frC (ctx j) κ e)))

map : ∀ {x y u v a b} (j : Embedding x u) (k : Embedding y v) →
  Coded x y a b → Coded u v (put j a) (put k b)
map j k cz = cz
map j k (cs p) = cs (map j k p)
map j k (cl p) = cl (λ n → map j k (p n))
map {x} {y} {u} {v} j k (co {κ} {κ′} {f} {g} p) = co callback where
  callback : ∀ {d e} → Same d e →
    Coded u v
      (put j (f (frC (ctx j) κ (code u (ek (ctx j) κ) d))))
      (put k (g (frC (ctx k) κ′ (code v (ek (ctx k) κ′) e))))
  callback {d} {e} q rewrite code-back j κ d | code-back k κ′ e = map j k (p q)
```

map用相同原关系的子证书递归；没有对任意g使用Same同余。若原树未有
Coded自证，此定理不声称其跨层输出相等。
