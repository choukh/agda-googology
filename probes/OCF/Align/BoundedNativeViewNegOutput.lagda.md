# 同一拷贝实例的实际运行器输出不合法

本篇另证输出事实，不从 View 的不存在反推。输入为真实第1分量地板，
原运行器保持最高种类到第1目标拷贝，内层底种类却落在第0拷贝。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeViewNegOutput where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf using (Path)
open import OCF.Align.BoundedNativeFoldRun using (fold)
open import OCF.Align.BoundedNativeViewNegCopies using (one; B; legal-B; pc; D; W; legal-W; one-to-D)

put : HB (Native one) → HB Source
put hz = hz
put (hs a) = hs (put a)
put (hl f) = hl (λ n → put (f n))
put (hΩ κ g) = hΩ (inj₂ one , κ) (λ c → put (g c))

put-path : ∀ a → Path B (put a)
put-path hz = tt
put-path (hs a) = put-path a
put-path (hl f) = λ n → put-path (f n)
put-path (hΩ κ g) = pc , (λ c ad → put-path (g c))

put-position : ∀ {a b V} → a ⊲[ V (inj₂ one) ] b → put a ⊲[ V ] put b
put-position hself = hself
put-position (hsuc p) = hsuc (put-position p)
put-position (hlim n p) = hlim n (put-position p)
put-position (hLim b p) = hLim b (put-position p)

put-legal : ∀ a → LgB a → LgB (put a)
put-legal hz l = l
put-legal (hs a) l = put-legal a l
put-legal (hl f) (st , l) = (λ n → put-position (st n)) , (λ n → put-legal (f n) (l n))
put-legal (hΩ κ g) (mo , l) =
  (λ lw b b′ p → put-position (mo (lw (inj₂ one)) b b′ p)) ,
  (λ lw b → put-legal (g _) (l (lw (inj₂ one)) b))

floor : HB (Native one)
floor = flL (ls (ls lz))
input : HB Source
input = put floor
legal-input : LgB input
legal-input = put-legal floor (Lg-flL (ls (ls lz)))

output : HB (Native B)
output = fold B legal-B B hself input (put-path floor)

branch : HB (Native hz) → HB (Native B)
branch c = fold B legal-B B hself (put (up c)) (put-path (up c))

no-repeat-zero : Ops.repeat (Native B) (hs hz) ⊲[ W ] hz → ⊥
no-repeat-zero ()
no-repeat-one : Ops.repeat (Native B) (hs hz) ⊲[ W ] hs hz → ⊥
no-repeat-one (hsuc p) = no-repeat-zero p

no-branch-path : branch (hs hz) ⊲[ W ] branch D → ⊥
no-branch-path (hLim hself p) = no-repeat-one p

no-legal-output : LgB output → ⊥
no-legal-output l = no-branch-path
  (proj₁ l legal-W one-to-D hself one-to-D)
```

原输入合法、Path证书、合法共同高度B、源与目标路径、合法目标世界均已实例化。
结论只针对这个目标 B=lim(const1) 的实际运行器输出；未证明目标0输出不合法，
也不否定采用不同树侧条件的原生下降。未修改原运行器或kind选择。
翻译账：独立的原定义合法性否定，无新记号规则或定义变更。
