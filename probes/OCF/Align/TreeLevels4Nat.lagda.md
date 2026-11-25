# 第四轮：自然数形数据的原计值证书

本篇是辅助证明，不另立合法性标准。RN 只记录一段原 native 数据去掉
包装后是几个后继；rw / rc 保留原 owk / ocv，后面的读回定理逐个消去。
它没有闭包或高层构造子的实例，不把任意程序判为自然数。

这里的自然数与重复加法引理沿用 NoKCertSmall 的证明方式，另在本层
覆盖 ocv；只导入原 LevelNoKFold，不导入改过折叠的 NoKCertTree / Tc。
本篇单独不计候选进展，实际闭项的全称实例放在 TreeLevels4SeedZero。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels4Nat where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Align.LevelNoKU using (𝕌; XF; module U)
open import OCF.Align.LevelNoKBase XF using (Cov)
import OCF.Align.LevelNoKFold as O
import OCF.Align.NoKCertEval as E
import OCF.Free.Level as F
open O.TT using (o0; os; owk; ocv; repᵒ; _⊕_)
natZ : ℕ → E.Zᵁ
natZ zero = E.zero
natZ (suc n) = E.suc (natZ n)
natO : ℕ → E.Ord₀
natO zero = F.zero
natO (suc n) = F.suc (natO n)
gn : ∀ n → E.Goodᵁ (natZ n)
gn zero = E.gz
gn (suc n) = E.gs (gn n)
gn-force : ∀ n → E.forceᵁ _ (gn n) ≡ natO n
gn-force zero = refl
gn-force (suc n) = cong F.suc (gn-force n)
data RN : ∀ {π} → O.O U.zero π → ℕ → Set where
  r0 : ∀ {π} → RN {π} o0 0
  rs : ∀ {π} {a : O.O U.zero π} {n} → RN a n → RN (os a) (suc n)
  rw : ∀ {π ρ} (w : U.Wk π ρ) {a : O.O U.zero π} {n} → RN a n → RN (owk w a) n
  rc : ∀ {π ρ} (w : Cov π ρ) {a : O.O U.zero π} {n} → RN a n → RN (ocv w a) n
rd-n : ∀ {π} {x : O.O U.zero π} {n} → RN x n → E.rdZ x ≡ natZ n
rd-n r0 = refl
rd-n (rs p) = cong E.suc (rd-n p)
rd-n (rw {π = π} w {a = a} p) = rd-n {π} {a} p
rd-n (rc {π = π} w {a = a} p) = rd-n {π} {a} p
rn-add : ∀ {π ρ} {x : O.O U.zero π} {y : O.O U.zero ρ} {n} → RN x 1 → RN y n → RN (x ⊕ y) (suc n)
rn-add hx r0 = rw _ hx
rn-add hx (rs p) = rs (rn-add hx p)
rn-add hx (rw w p) = rw _ (rn-add hx p)
rn-add hx (rc w p) = rc _ (rn-add hx p)
rn-rep : ∀ {π} {x : O.O U.zero π} → RN x 1 → ∀ n → RN (repᵒ x n) n
rn-rep p zero = r0
rn-rep p (suc n) = rw _ (rn-add p (rn-rep p n))
force-subst : ∀ {a b} (e : a ≡ b) (G : E.Goodᵁ a) → E.forceᵁ b (subst E.Goodᵁ e G) ≡ E.forceᵁ a G
force-subst refl G = refl
```
