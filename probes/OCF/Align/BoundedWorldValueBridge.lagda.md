# 原第三地板：两低槽的结构模拟

源层号固定3，所有目标0、1、2在共同字面界3中；没有裸下标比较。
输入关系为遗传分支关系Rel1，反馈中坐标用Rel0，底坐标用Same。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueBridge where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
open import OCF.Align.FrozenInnerOuter using (same-add; same-mul)
open import OCF.Align.BoundedCompletionFiniteRunIf using (Rel; rz; rs; rl; ro)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (rel-add)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedWorldValueIf
import OCF.Align.BoundedWorldValueRun as G
open import OCF.Align.BoundedWorldValueTwoSlot
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1If as I

rel-mul : ∀ {a b} → Rel hz a b → ∀ n → Rel hz
  (I.mul a n) (I.mul b n)
rel-mul p zero = p
rel-mul p (suc n) = rel-add (rel-mul p n) p

oldmid = F.Φ (num 3) tt (num 1) (hsuc (hsuc hself))
oldlow = F.Φ (num 3) tt hz (hsuc (hsuc (hsuc hself)))

mid-bridge : ∀ {a b u v} → Rel (num 1) a b → Rel hz u v → ∀ x z →
  Rel hz (oldmid (((tt , x) , u) , z) (up a)) (mid v b)
mid-bridge rz uv x z = rs rz
mid-bridge (rs p) uv x z = rl (rel-mul (mid-bridge p uv x z))
mid-bridge (rl p) uv x z = rl (λ n → mid-bridge (p n) uv x z)
mid-bridge (ro {κ = inj₁ (inj₁ ())} p) uv x z
mid-bridge (ro {κ = inj₁ (inj₂ _)} p) uv x z = ro (λ c d cd → mid-bridge (p c d cd) uv x z)
mid-bridge {u = u} {v} (ro {κ = inj₂ _} {f} {g} p) uv x z = rl D.sums
  where
  WR : Wd (step V) → HB U → Set
  WR W b = Rel hz (proj₂ (proj₁ W)) b
  branch : ∀ {W b c d} → WR W b → Rel hz c d →
    Rel hz (oldmid W (up (f c))) (mid b (g d))
  branch {W = ((tt , x′) , u′) , z′} r cd = mid-bridge (p _ _ cd) r x′ z′
  sim : Simulation WR (Rel hz) (Rel hz) (((tt , x) , u) , z) v u v
    (λ W e → (proj₁ (proj₁ W) , e) , proj₂ W) (λ _ e → e)
    (λ W e → oldmid W (up (f e))) (λ b e → mid b (g e))
    (λ W e → oldmid W (up (f e))) (λ b e → mid b (g e))
  sim = record { worlds-start = uv ; coordinates-start = uv
    ; add-coordinate = rel-add ; add-output = rel-add
    ; update = λ _ r → r ; advance = branch ; emit = branch }
  module D = G.Run sim

low-bridge : ∀ {a b u v x y} → Rel (num 1) a b → Rel hz u v → Same x y → ∀ z →
  Same (oldlow (((tt , x) , u) , z) (up a)) (low y v b)
low-bridge rz uv xy z = ss zz
low-bridge (rs p) uv xy z = ll (same-mul (low-bridge p uv xy z))
low-bridge (rl p) uv xy z = ll (λ n → low-bridge (p n) uv xy z)
low-bridge (ro {κ = inj₁ (inj₁ ())} p) uv xy z
low-bridge {u = u} {v} {x} {y} (ro {κ = inj₁ (inj₂ _)} {f} {g} p) uv xy z = ll D.sums
  where
  WR : Wd (step V) → Cd → Set
  WR W b = Same (proj₂ (proj₁ (proj₁ W))) b × Rel hz (proj₂ (proj₁ W)) v
  branch : ∀ {W b c d} → WR W b → Same c d →
    Same (oldlow W (up (f c))) (low b v (g d))
  branch {W = ((tt , x′) , u′) , z′} (r , s) cd = low-bridge (p _ _ cd) s r z′
  sim : Simulation WR Same Same (((tt , x) , u) , z) y x y
    (λ W e → ((tt , e) , proj₂ (proj₁ W)) , proj₂ W) (λ _ e → e)
    (λ W e → oldlow W (up (f e))) (λ b e → low b v (g e))
    (λ W e → oldlow W (up (f e))) (λ b e → low b v (g e))
  sim = record { worlds-start = xy , uv ; coordinates-start = xy
    ; add-coordinate = same-add ; add-output = same-add
    ; update = λ r cd → cd , proj₂ r ; advance = branch ; emit = branch }
  module D = G.Run sim
low-bridge {u = u} {v} {x} {y} (ro {κ = inj₂ _} {f} {g} p) uv xy z = ll D.sums
  where
  WR : Wd (step V) → HB U → Set
  WR W b = Same (proj₂ (proj₁ (proj₁ W))) y × Rel hz (proj₂ (proj₁ W)) b
  coord : ∀ {W b c d} → WR W b → Rel hz c d →
    Rel hz (oldmid W (up (f c))) (mid b (g d))
  coord {W = ((tt , x′) , u′) , z′} (r , s) cd = mid-bridge (p _ _ cd) s x′ z′
  branch : ∀ {W b c d} → WR W b → Rel hz c d →
    Same (oldlow W (up (f c))) (low y b (g d))
  branch {W = ((tt , x′) , u′) , z′} (r , s) cd = low-bridge (p _ _ cd) s r z′
  sim : Simulation WR (Rel hz) Same (((tt , x) , u) , z) v u v
    (λ W e → (proj₁ (proj₁ W) , e) , proj₂ W) (λ _ e → e)
    (λ W e → oldmid W (up (f e))) (λ b e → mid b (g e))
    (λ W e → oldlow W (up (f e))) (λ b e → low y b (g e))
  sim = record { worlds-start = xy , uv ; coordinates-start = uv
    ; add-coordinate = rel-add ; add-output = same-add
    ; update = λ r cd → proj₁ r , cd ; advance = coord ; emit = branch }
  module D = G.Run sim
```
