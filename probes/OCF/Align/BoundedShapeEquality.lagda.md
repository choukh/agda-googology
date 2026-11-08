# 字面公共界内的逐枝同形确定同一层

不同世界里两个 Shape 层不被认作相等。这里另外给出同一合法世界、
同一合法树中的两条字面位置时，Shape 才足以给出命题相等。它可以
用于统一运行器实际发生的层比较，不是全局判等或函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedShapeEquality where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (StH; ss; sl; sL; AccY; acc)
open import OCF.Align.GenFoldTree using (accL)
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)

reverse : ∀ {S : KS} {a b : HB S} → Shape a b → Shape b a
reverse sz = sz
reverse (ss p) = ss (reverse p)
reverse (sl p) = sl (λ n → reverse (p n))
reverse (so p) = so (λ e → reverse (p e))

position : ∀ {S : KS} {a b : HB S} → Shape a b →
  ∀ {W k} → k ⊲[ W ] a → Σ (HB S) (λ k′ → Shape k k′ × (k′ ⊲[ W ] b))
position p hself = _ , p , hself
position (ss p) (hsuc q) with position p q
... | k , s , q′ = k , s , hsuc q′
position (sl p) (hlim n q) with position (p n) q
... | k , s , q′ = k , s , hlim n q′
position (so p) (hLim {c = c} e q) with position (p c) q
... | k , s , q′ = k , s , hLim e q′

node : ∀ {S : KS} {a b : HB S} → Shape a b →
  ∀ {W k} → StH W k a → Σ (HB S) (λ k′ → Shape k k′ × StH W k′ b)
node (ss p) (ss q) with position p q
... | k , s , q′ = k , s , ss q′
node (sl p) (sl n q) with position (p n) q
... | k , s , q′ = k , s , sl n q′
node (so p) (sL {c = c} e q) with position (p c) q
... | k , s , q′ = k , s , sL e q′

-- 若父树与一个严格子位置同形，运输该位置会在子树里再次造出
-- 同形的严格子位置。沿原可达证明下降，不能无限继续。
no-child : ∀ {S : KS} {a : HB S} → AccY a →
  ∀ {W b} → Shape a b → StH W b a → ⊥
no-child (acc f) p r with node p r
... | k , q , r′ = no-child (f r) q r′

split : ∀ {S : KS} {W} {a b : HB S} → a ⊲[ W ] b → (a ≡ b) ⊎ StH W a b
split hself = inj₁ refl
split (hsuc p) = inj₂ (ss p)
split (hlim n p) = inj₂ (sl n p)
split (hLim e p) = inj₂ (sL e p)

bounded : ∀ {S : KS} {a b c : HB S} {W} → Shape a b →
  a ⊲[ W ] c → b ⊲[ W ] c → LgW S W → LgB c → a ≡ b
bounded {a = a} p ap bp lw lc with cmpB ap bp lw lc
... | inj₁ ba with split ba
...   | inj₁ refl = refl
...   | inj₂ r = ⊥-elim (no-child (accL a) p r)
bounded {b = b} p ap bp lw lc | inj₂ ab with split ab
...   | inj₁ refl = refl
...   | inj₂ r = ⊥-elim (no-child (accL b) (reverse p) r)
```

所有比较都在类型所列的同一字面公共界 c、同一世界 W 内进行。
前提例如在 S₀、世界 0、a=b=1、c=2 时都有直接构造；实际运行则
使用原 Λ 与原目标／节点位置，而非假设任意两树能取得这种界。
这个结论不能用于两份独立历史的动态层，除非另外交出这里的实际
共同界证据；Shape、序数值有上界或两个各自的源位置不能替代它。
