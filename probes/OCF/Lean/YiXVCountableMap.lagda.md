# YiXVCountableMap
> 验收文件。档位：编译定理。统一映射保持辅助合法性、比较，且映射零不大于任意合法输入的映射。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableMap where
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst; subst₂)
open import Data.Product using (proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Omega
import OCF.Lean.YiXVCountableNormalize as Norm
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableMapNode as Node
import OCF.Lean.YiXVCountableMapCompare as Compare

module Map {κ ν} (φ : L.Ordᶜ κ → L.Ordᶜ ν) (view : V.View κ ν φ) where
  module S = A.Layer κ A.Gd< A.Le<
  module D = A.Layer ν A.Gd< A.Le<
  proof : ∀ {X Y} → D.Le X Y → D.Step X Y
  proof (D.pack gx gy p) = p
  mutual
    good : ∀ {X} → S.Gd X → D.Gd (φ X)
    good S.gz = V.View.zero view
    good (S.gs {X} gx) = subst D.Gd (sym (V.View.suc view X)) (D.gs (good gx))
    good (S.gl {f} gf) = subst D.Gd (sym (V.View.lim view f)) (D.gl (λ n → good (gf n)))
    good (S.gn {q = q} {f = f} ex (S.sc mo db po) gb) = Node.Node.result φ view q f ex
      (λ X gx o → good (gb X gx o))
      (λ X Y gx gy o t → mono (mo X Y gx gy o t))
      (λ X gx o → mono (db X gx o)) (mono po)
    good (S.gu r {X} gx) = subst D.Gd (sym (V.View.up-shape view r X))
      (V.Child.good (V.View.up view r) (A.good-out (L.◃₁→◃ r) gx))

    right : ∀ {X} → S.Gd X → D.Le (φ L.zero) (φ X)
    right S.gz = D.rfl (V.View.zero view)
    right (S.gs {X} gx) = subst (D.Le (φ L.zero)) (sym (V.View.suc view X))
      (D.pack (V.View.zero view) (D.gs (good gx)) (D.ws (right gx)))
    right (S.gl {f} gf) = subst (D.Le (φ L.zero)) (sym (V.View.lim view f))
      (D.pack (V.View.zero view) (D.gl (λ n → good (gf n))) (D.lr 0 (right (gf 0))))
    right h@(S.gn {i = i} {q = q} {f = f} ex law gb) =
      subst (D.Le (φ L.zero)) (sym (V.View.node-shape view q f))
        (D.pack (V.View.zero view)
          (subst D.Gd (V.View.node-shape view q f) (good h))
          (D.aa end))
      where
      p = V.View.node view q
      j = V.Pull.index p
      gx = V.Pull.good p (proj₁ (Omega.model j))
      o = V.Pull.floor p (A.Layer.rfl j A.Gd< A.Le< (proj₁ (Omega.model j)))
      end = subst (D.Le (φ L.zero)) (sym (cong (λ u → φ (f u)) (V.Pull.input p (L.Ω j))))
        (right (gb (V.Pull.back p (L.Ω j)) (A.good-in (L.<→◃ q) gx) (A.le-in (L.<→◃ q) o)))
    right (S.gu r {X} gx) = subst (D.Le (φ L.zero)) (sym (V.View.up-shape view r X))
      (V.Child.right (V.View.up view r) (A.good-out (L.◃₁→◃ r) gx))

    mono : ∀ {X Y} → S.Le X Y → D.Le (φ X) (φ Y)
    mono (S.pack gx gy p) = D.pack (good gx) (good gy) (step gx gy p)

    step : ∀ {X Y} → S.Gd X → S.Gd Y → S.Step X Y → D.Step (φ X) (φ Y)
    step gx gy (S.ce e) = D.ce (V.View.cong view e)
    step gx gy S.rr = D.rr
    step gx gy S.zz = proof (right gy)
    step gx gy (S.ss {X} {Y} t) = subst₂ D.Step (sym (V.View.suc view X)) (sym (V.View.suc view Y)) (D.ss (mono t))
    step {X} gx gy (S.ws {Y = Y} t) = subst (D.Step (φ X)) (sym (V.View.suc view Y)) (D.ws (mono t))
    step {Y = Y} gx gy (S.ll {f} h) = subst (λ X → D.Step X (φ Y)) (sym (V.View.lim view f)) (D.ll (λ n → mono (h n)))
    step {X = X} gx gy (S.lr {f = f} n t) = subst (D.Step (φ X)) (sym (V.View.lim view f)) (D.lr n (mono t))
    step gx gy (S.nn {q = q} {r = r} {f = f} {g = g} h) = Compare.Map.result φ φ view view q r f g
      (λ X Y gX gY o t → mono (h X Y gX gY o t))
    step {X = X} gx (S.gn {i = i} {q = q} {f = f} ex (S.sc mo db po) gb) (S.aa t) =
      subst (D.Step (φ X)) (sym (V.View.node-shape view q f)) (D.aa end)
      where
      p = V.View.node view q
      j = V.Pull.index p
      end : D.Le (φ X) (φ (f (V.Pull.raw p (L.into (L.<→◃ (V.Pull.bound p)) (L.Ω j)))))
      end = subst (D.Le (φ X)) (sym (cong (λ u → φ (f u)) (V.Pull.input p (L.Ω j))))
        (D.trans (mono t) (mono (mo (L.Ω i) (V.Pull.back p (L.Ω j))
          (A.good-in (L.<→◃ q) (proj₁ (Omega.model i)))
          (A.good-in (L.<→◃ q) (V.Pull.good p (proj₁ (Omega.model j))))
          (A.le-in (L.<→◃ q) (A.Layer.rfl i A.Gd< A.Le< (proj₁ (Omega.model i))))
          (A.le-in (L.<→◃ q) (V.Pull.floor p
            (A.Layer.rfl j A.Gd< A.Le< (proj₁ (Omega.model j))))))))
    step gx gy (S.uu {X = X} {Y = Y} r t) = subst₂ D.Step
      (sym (V.View.up-shape view r X)) (sym (V.View.up-shape view r Y))
      (proof (V.Child.mono (V.View.up view r) (A.le-out (L.◃₁→◃ r) t)))
    step gx gy (S.uS r hx) = D.ce (V.View.cong view (Norm.suc r (A.self (A.good-out (L.◃₁→◃ r) hx))))
    step gx gy (S.uS⁻ r hx) = D.ce (V.View.cong view (L.≅-sym (Norm.suc r (A.self (A.good-out (L.◃₁→◃ r) hx)))))
    step gx gy (S.uZ r) = D.ce (V.View.cong view (Norm.up-left r L.z≅))
    step gx gy (S.uZ⁻ r) = D.ce (V.View.cong view (Norm.up-right r L.z≅))
    step gx gy (S.uL {f = f} r hf) = D.ce (V.View.cong view (Norm.lim r f (λ n → A.self (A.good-out (L.◃₁→◃ r) (hf n)))))
    step gx gy (S.uL⁻ {f = f} r hf) = D.ce (V.View.cong view (L.≅-sym (Norm.lim r f (λ n → A.self (A.good-out (L.◃₁→◃ r) (hf n))))))
    step gx gy (S.uN r q {f} hf) = D.ce (V.View.cong view (Norm.node r q f (A.self (A.good-out (L.◃₁→◃ r) hf))))
    step gx gy (S.uN⁻ r q {f} hf) = D.ce (V.View.cong view (L.≅-sym (Norm.node r q f (A.self (A.good-out (L.◃₁→◃ r) hf)))))
    step gx gy (S.tr t u) = D.tr (mono t) (mono u)

module Model = Map (λ (X : L.Ordᶜ L.ωᴵ) → X) (V.identity L.ωᴵ)
actual-good : A.Gd (L.Ω L.ωᴵ)
actual-good = Model.good A.omegaΩ
actual-le : A.Le (L.suc L.zero) (L.Ω L.ωᴵ)
actual-le = Model.mono A.omega-pos
```
