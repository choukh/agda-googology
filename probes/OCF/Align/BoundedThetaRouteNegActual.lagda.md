# 原θ-path的非零目标输出不合法

使用θ(leg raw)原输入和原θ-path，raw=lim(const1)合法。
不另造分量路径，不忽略θ的累加前缀，也不使用路径证明无关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedThetaRouteNegActual where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldRun using (fold)
open import OCF.Align.BoundedNativeLegalWorld using (canonical; canonical-legal)
open import OCF.Align.BoundedNativeViewNegCopies using (one; D; legal-D; one-to-D)
import OCF.Align.BoundedNativeFloor as N

raw : Cd
raw = hl (λ _ → one)
legal-raw : LgB raw
legal-raw = (λ n → hself) , (λ n → tt)
L : Cd
L = leg raw
legal-L : LgB L
legal-L = Lg-leg raw

source-world : Wd Source
source-world (inj₁ _) = tt , L
source-world (inj₂ c) = canonical c
legal-source-world : LgW Source source-world
legal-source-world (inj₁ _) = tt , legal-L
legal-source-world (inj₂ c) = canonical-legal c
legal-input : LgB (N.θ L)
legal-input = proj₂ N.legal-input legal-source-world hself

output : HB (Native L)
output = fold L legal-L L hself (N.θ L) (N.θ-path L L hself)

W : Wd (Native L)
W zero = (tt , hz) , hz
W (suc zero) = ((tt , one) , D) , hz
W (suc (suc n)) = canonical _
legal-W : LgW (Native L) W
legal-W zero = (tt , tt) , tt
legal-W (suc zero) = ((tt , tt) , legal-D) , tt
legal-W (suc (suc n)) = canonical-legal _

lim-one : HB (Native L) → HB (Native L)
lim-one (hl f) = f 1
lim-one _ = hz
part : HB (Native L)
part = lim-one output
select : HB (Native L) → HB (Native hz) → HB (Native L)
select (hΩ (suc zero , inj₁ (inj₂ _)) g) c = g c
select _ c = hz

part-legal : LgB output → LgB part
part-legal l = proj₂ l 1
no-lim-zero : ∀ {f : ℕ → HB (Native L)} → hl f ⊲[ W ] hz → ⊥
no-lim-zero ()
no-lim-one : ∀ {f : ℕ → HB (Native L)} → hl f ⊲[ W ] hs hz → ⊥
no-lim-one (hsuc p) = no-lim-zero p

no-branch-path : select part (hs hz) ⊲[ W ] select part D → ⊥
no-branch-path (hLim hself (hLim hself p)) = no-lim-one p

no-part : LgB part → ⊥
no-part l = no-branch-path (proj₁ l legal-W one-to-D hself one-to-D)
no-legal-output : LgB output → ⊥
no-legal-output l = no-part (part-legal l)
```

第二极限项包含完整θ累加前缀；右支的两层base Ω在该目标世界中只能取0，
位置要求最终会将左支ℕ极限送入1，矛盾。证书差异没有被等同。
结论只针对上述非零目标L、共同界L、原θ-path调用；不判定目标0、
末段Outer采样或最终countable-output的合法性。
翻译账：原定义的精确合法性否定，未新增规则或修改运行器。
