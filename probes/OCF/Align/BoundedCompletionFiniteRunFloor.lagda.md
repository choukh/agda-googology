# 全部真实有限地板的跨公共界同余

会坍缩的地板也由统一定理覆盖，不限源层低于目标的allkeep区域。
canonical仍调用原运行器，只把公共界取为该有限源高度本身。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteRunFloor where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
open import OCF.Align.BoundedCompletionFiniteRun using (coherent)

legal-num : ∀ n → LgB (num n)
legal-num zero = tt
legal-num (suc n) = legal-num n

floor-independent : ∀ n m {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pc : num n ⊲ B) (pc′ : num n ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′) →
  Rel (num m) (at n m lB pc pt (floor n)) (at n m lB′ pc′ pt′ (floor n))
floor-independent n m lB lB′ pc pc′ pt pt′ =
  coherent n m lB lB′ pc pc′ pt pt′ (floor-rel n)

canonical : ∀ n → HB (Native hz)
canonical n = at n zero (legal-num n) hself (z⊲ᴮ (num n)) (floor n)

floor-zero-rel : ∀ n {B} (lB : LgB B) (pc : num n ⊲ B) (pt : hz ⊲ B) →
  Rel hz (at n zero lB pc pt (floor n)) (canonical n)
floor-zero-rel n lB pc pt = floor-independent n zero lB (legal-num n)
  pc hself pt (z⊲ᴮ (num n))

floor-zero-same : ∀ n {B} (lB : LgB B) (pc : num n ⊲ B) (pt : hz ⊲ B) →
  Same (at n zero lB pc pt (floor n)) (canonical n)
floor-zero-same n lB pc pt = zero-same (floor-zero-rel n lB pc pt)

floor-zero-value : ∀ n {B} (lB : LgB B) (pc : num n ⊲ B) (pt : hz ⊲ B) →
  (at n zero lB pc pt (floor n) ≤ᵛ canonical n) ×
  (canonical n ≤ᵛ at n zero lB pc pt (floor n))
floor-zero-value n lB pc pt = same-value (floor-zero-same n lB pc pt) ,
  same-value (same-sym (floor-zero-same n lB pc pt))
```

前提真实可满足：全部n可取B=num n、pc=hself、pt=零路径；也可取
B=hs(num n)并把两条路径后继提升。定理并非只给同一个公共界的自反实例。

它比较原ι单组件地板，尚未把原θ的多组件累加重编码为一个组件。
canonical也仍是原Native下降，不是Old.Fold1有限参照。故到EBO的有限塔
值桥尚余两件事：实际θ混合输入覆盖本族，以及本族的规范参照值下界。
此处新增的是实际全部finite地板的参数无关定理，不改原树、折叠或证书。
