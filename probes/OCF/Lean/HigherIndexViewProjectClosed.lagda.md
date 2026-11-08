# 固定世界闭项的精确Cd投影：ω

这是HigherIndexViewClosed.output在新有界语义中的校准，不是旧高层
≤ᵛ的Ω消去。证明覆盖所有自然数根分支，不是有限测试。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexViewProjectClosed where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Lean.LHRecTy using (Lv; lz)
open import OCF.Lean.LHRecFl using (flL; cxI; gcF)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.HigherIndexFoldIf using (g)
import OCF.Lean.HigherIndexViewClosed as C
import OCF.Lean.HigherIndexViewProjectRun as P

module T = P.Theory C.x C.W C.lW
read : HB (Lv C.x) → Cd
read a = T.project (C.Actual.restrict a)

self : ∀ (a : Cd) → Same a a
self hz = zz
self (hs a) = ss (self a)
self (hl f) = ll (λ n → self (f n))
self (hΩ () f)
trans : ∀ {a b c : Cd} → Same a b → Same b c → Same a c
trans zz zz = zz
trans (ss p) (ss q) = ss (trans p q)
trans (ll p) (ll q) = ll (λ n → trans (p n) (q n))
sum : ∀ {a b c d : Cd} → Same a b → Same c d → Same (a ⊞ c) (b ⊞ d)
sum p zz = p
sum p (ss q) = ss (sum p q)
sum p (ll q) = ll (λ n → sum p (q n))

read-add : ∀ a b → Same (read (a ⊞ b)) (read a ⊞ read b)
read-add a hz = self (read a)
read-add a (hs b) = ss (read-add a b)
read-add a (hl f) = ll (λ n → read-add a (f n))
read-add a (hΩ κ f) = read-add a (f (OCF.Lean.HigherIndexViewProjectIf.cap C.x κ C.W))
  where import OCF.Lean.HigherIndexViewProjectIf

inner : Cd → HB (Lv C.x)
inner = New.θ (cxI lz (λ d → g (up d)))
  (gcF (λ d → ι (inj₂ d) (flL (g (up d)))))

component-one : ∀ n → Same
  (read (ι (inj₂ (C.num n)) (flL (g (up (C.num n)))))) (hs hz)
component-one zero = ss zz
component-one (suc n) = ss zz

all-branches : ∀ n → Same (read (inner (C.num n))) (C.num n)
all-branches zero = zz
all-branches (suc n) = trans
  (read-add (inner (C.num n)) (ι (inj₂ (C.num n)) (flL (g (up (C.num n))))))
  (sum (all-branches n) (component-one n))

projection : Cd
projection = T.project C.output
projection-legal : LgB projection
projection-legal = T.legal C.output C.legal-output
projection-omega : Same projection C.ω
projection-omega = ll all-branches
value-lower : C.ω ≤ᵛ projection
value-lower = same-value (same-sym projection-omega)
value-upper : projection ≤ᵛ C.ω
value-upper = same-value projection-omega

-- 只在新定义的有界语义中声明原输出与纯ω等值。
bounded-equivalence : (C.output T.≼ᴮ T.pure C.ω) × (T.pure C.ω T.≼ᴮ C.output)
bounded-equivalence =
  ≤-trans value-upper (same-value (same-sym (T.pure-value C.ω))) ,
  ≤-trans (same-value (T.pure-value C.ω)) value-lower
```

精确结果：这个具体固定world实验的合法Cd投影与ω双向≤ᵛ，且逐枝Same。
它校准的是本实验，不能据此给原高层raw树或动态Support折叠封顶，也不
因此关闭动态路线。新定义的值尺度与旧高层≤ᵛ区别已在接口显式标明。
