# 分层关系实际通过最后一层折叠

Rel0只在相关的可数坐标上约束Ω分支，正好够比较最后一层真实回灌。
本篇不将中间Ω树的点态Same冒充回调同余；输入直接要求Rel0，且初界
也带Same证据。结论是末段原fold输出的全可数Same。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionTerminalRel where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
open import OCF.Align.FrozenInnerOuter using (same-mul)
import OCF.Align.FrozenOutputSim as Sim
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteRunIf using (Rel; TreeRel; rz; rs; rl; ro)
import OCF.Align.BoundedNativeTerminalReady as T

WorldRel : Wd (Native hz) → Wd (Native hz) → Set
WorldRel w v = Same (proj₂ w) (proj₂ v)

terminal-rel : ∀ {a b} → Rel hz a b → ∀ {u v} → Same u v →
  Same (T.fold u a) (T.fold v b)
terminal-rel rz uv = ss zz
terminal-rel (rs p) uv = ll (same-mul (terminal-rel p uv))
terminal-rel (rl p) uv = ll (λ n → terminal-rel (p n) uv)
terminal-rel (ro {κ = inj₁ ()} p) uv
terminal-rel {a = hΩ (inj₂ _) f} {b = hΩ (inj₂ _) g} (ro p) {u} {v} uv = ll D.sums
  where
  branches-related : ∀ {w v x y} → WorldRel w v → Same x y →
    Same (T.fold (proj₂ w) (f x)) (T.fold (proj₂ v) (g y))
  branches-related wv xy = terminal-rel (p _ _ xy) wv

  module D = Sim.Sim WorldRel (tt , u) (tt , v) uv u v uv
    (λ w e → tt , e) (λ w e → tt , e) (λ wv xy → xy)
    (λ w e → T.fold (proj₂ w) (f e)) (λ w e → T.fold (proj₂ w) (g e))
    (λ w e → T.fold (proj₂ w) (f e)) (λ w e → T.fold (proj₂ w) (g e))
    branches-related branches-related
```

结果直接消费原末段函数与其Col，没有重定义输出或换常值采样。每次
反馈更新后的界都由WorldRel与真实坐标Same连接；不假设旧界不变。

下面将条件定理实证到全部有限层的原地板，不只给一个自反玩具。

```agda
open import Data.Nat using (zero)
open import Data.Product using (_×_)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor; pure-reflexive)
import OCF.Align.BoundedCompletionFiniteRunFloor as Floor

floor-terminal-same : ∀ n {B} (lB : LgB B) (pc : num n ⊲ B)
  (pt : hz ⊲ B) (u : Cd) → Same
  (T.fold u (at n zero lB pc pt (floor n)))
  (T.fold u (Floor.canonical n))
floor-terminal-same n lB pc pt u =
  terminal-rel (Floor.floor-zero-rel n lB pc pt) (pure-reflexive u)

floor-terminal-value : ∀ n {B} (lB : LgB B) (pc : num n ⊲ B)
  (pt : hz ⊲ B) (u : Cd) →
  (T.fold u (at n zero lB pc pt (floor n)) ≤ᵛ T.fold u (Floor.canonical n)) ×
  (T.fold u (Floor.canonical n) ≤ᵛ T.fold u (at n zero lB pc pt (floor n)))
floor-terminal-value n lB pc pt u =
  same-value (floor-terminal-same n lB pc pt u) ,
  same-value (same-sym (floor-terminal-same n lB pc pt u))
```

全部n可取B=num n、pc=hself、pt=零路径，或取其后继界，故前提有
实际实例。这里尚未证明这些raw可数输出合法、达到Old有限参照，或
位于C之下；该三项不能由结构同余自动推出。
