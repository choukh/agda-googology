# 逐边覆盖何时能推出解释像成链

这是纯树侧的条件定理，不是实际 EBO 比较图已经成链的结论。
除了每条有向边保持 CP，还须任意两顶点有沿边可达的共同后继。
这个额外条件给出一棵具体的合法公共界；没有它，逐边可比本身不足。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPrefixChain where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP; CP-tr)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiLevelCompare as C
open import OCF.Align.YiSpineCommon using (Common; Spinal; common→spinal)

data Path {Vertex : Set} (Edge : Vertex → Vertex → Set) (x : Vertex) : Vertex → Set where
  stay : Path Edge x x
  snoc : ∀ {y z} → Path Edge x y → Edge y z → Path Edge x z

record ChainHyp (Vertex : Set) (Edge : Vertex → Vertex → Set)
  (image : Vertex → Y.Level) : Set where
  field
    edge-position : ∀ {x y} → Edge x y → CP (Y.tree (image x)) (Y.tree (image y))
    common-future : ∀ x y → Σ Vertex (λ z → Path Edge x z × Path Edge y z)
open ChainHyp public

-- Proper 只沿真正的结构子项下降，不经过层号字段或任意 Ω 分支。
data FirstAcc (a : LF) : Set where
  first-acc : (∀ {b} → Y.Proper b a → FirstAcc b) → FirstAcc a

acc-below : ∀ {a b} → FirstAcc b → Y.Proper a b → FirstAcc a
acc-below (first-acc next) p = next p

cp-below : ∀ {a b} → FirstAcc b → CP a b → FirstAcc a
cp-below lawful V.self = lawful
cp-below lawful (V.suc p) = acc-below lawful (Y.under-suc p)
cp-below lawful (V.lim n p) = acc-below lawful (Y.under-lim n p)
cp-below lawful (V.fst p) = acc-below lawful (Y.under-first p)

proper-wf : ∀ a → FirstAcc a
proper-wf F.zero = first-acc (λ ())
proper-wf (F.suc a) = first-acc (λ { (Y.under-suc p) → cp-below (proper-wf a) p })
proper-wf (F.lim f) = first-acc (λ { (Y.under-lim n p) → cp-below (proper-wf (f n)) p })
proper-wf (F.lc k c t g) = first-acc (λ { (Y.under-first p) → cp-below (proper-wf t) p })

acc-irrefl : ∀ {a} → FirstAcc a → Y.Proper a a → ⊥
acc-irrefl (first-acc next) p = acc-irrefl (next p) p

proper-irrefl : ∀ {a} → Y.Proper a a → ⊥
proper-irrefl {a} = acc-irrefl (proper-wf a)

proper-cp : ∀ {a b} → Y.Proper a b → CP a b
proper-cp (Y.under-suc p) = V.suc p
proper-cp (Y.under-lim n p) = V.lim n p
proper-cp (Y.under-first p) = V.fst p

proper-then-cp : ∀ {a b c} → Y.Proper a b → CP b c → Y.Proper a c
proper-then-cp p V.self = p
proper-then-cp p (V.suc q) = Y.under-suc (CP-tr (proper-cp p) q)
proper-then-cp p (V.lim n q) = Y.under-lim n (CP-tr (proper-cp p) q)
proper-then-cp p (V.fst q) = Y.under-first (CP-tr (proper-cp p) q)

no-back : ∀ {a b} → Y.Proper a b → CP b a → ⊥
no-back p q = proper-irrefl (proper-then-cp p q)

proper-neq : ∀ {a b} → Y.Proper a b → a ≡ b → ⊥
proper-neq p refl = proper-irrefl p

cp-antisym : ∀ {a b} → CP a b → CP b a → a ≡ b
cp-antisym V.self q = refl
cp-antisym (V.suc p) q = ⊥-elim (no-back (Y.under-suc p) q)
cp-antisym (V.lim n p) q = ⊥-elim (no-back (Y.under-lim n p) q)
cp-antisym (V.fst p) q = ⊥-elim (no-back (Y.under-first p) q)

common-order : ∀ {a b} → Common a b → Y.Order (Y.tree a) (Y.tree b)
common-order {a} {b} (bound , pa , pb) =
  C.bounded-compare bound (Y.located a pa) (Y.located b pb)

common-cp-dec : ∀ {a b} → Common a b → Dec (CP (Y.tree a) (Y.tree b))
common-cp-dec {a} {b} c with common-order {a = a} {b = b} c
... | Y.below p = yes (proper-cp p)
... | Y.equal e = yes (subst (CP (Y.tree a)) e V.self)
... | Y.above p = no (no-back p)

common-eq-dec : ∀ {a b} → Common a b → Dec (Y.tree a ≡ Y.tree b)
common-eq-dec {a} {b} c with common-order {a = a} {b = b} c
... | Y.below p = no (proper-neq p)
... | Y.equal e = yes e
... | Y.above p = no (λ e → proper-neq p (sym e))

module Consequences {Vertex : Set} {Edge : Vertex → Vertex → Set}
  {image : Vertex → Y.Level} (H : ChainHyp Vertex Edge image) where

  path-position : ∀ {x y} → Path Edge x y → CP (Y.tree (image x)) (Y.tree (image y))
  path-position stay = V.self
  path-position (snoc p e) = CP-tr (path-position p) (edge-position H e)

  common : ∀ x y → Common (image x) (image y)
  common x y with common-future H x y
  ... | z , px , py = image z , path-position px , path-position py

  spinal : ∀ x y → Spinal (image x) (image y)
  spinal x y = common→spinal {a = image x} {b = image y} (common x y)

  cp-dec : ∀ x y → Dec (CP (Y.tree (image x)) (Y.tree (image y)))
  cp-dec x y = common-cp-dec {a = image x} {b = image y} (common x y)

  tree-eq-dec : ∀ x y → Dec (Y.tree (image x) ≡ Y.tree (image y))
  tree-eq-dec x y = common-eq-dec {a = image x} {b = image y} (common x y)
```

`edge-position` 比逐边 Common 更强：它还固定边的 CP 方向。
每条边的右端解释是该次位置证明的合法公共界；有限路径再给共同后继
解释这个最终公共界。本篇没有从无向连通或逐边覆盖推出共同后继。

## 两项前提可同时满足的自然数后继图模型

取自然数后继图，顶点解释为同一类型中的有限合法树。
n 与 m 的共同后继取 n+m，两个方向的有限路径都由构造给出。

```agda
data Up : ℕ → ℕ → Set where
  up : ∀ {n} → Up n (suc n)

nat-level : ℕ → Y.Level
nat-level zero = Y.zero
nat-level (suc n) = Y.suc (nat-level n)

zero-path : ∀ n → Path Up zero n
zero-path zero = stay
zero-path (suc n) = snoc (zero-path n) up

raise-path : ∀ {n m} → Path Up n m → Path Up (suc n) (suc m)
raise-path stay = stay
raise-path (snoc p up) = snoc (raise-path p) up

left-path : ∀ n m → Path Up n (n + m)
left-path zero m = zero-path m
left-path (suc n) m = raise-path (left-path n m)

right-path : ∀ n m → Path Up m (n + m)
right-path zero m = stay
right-path (suc n) m = snoc (right-path n m) up

nat-hyp : ChainHyp ℕ Up nat-level
edge-position nat-hyp up = V.suc V.self
common-future nat-hyp n m = (n + m) , left-path n m , right-path n m

nat-model-common : ∀ n m → Common (nat-level n) (nat-level m)
nat-model-common = Consequences.common nat-hyp

nat-model-spinal : ∀ n m → Spinal (nat-level n) (nat-level m)
nat-model-spinal = Consequences.spinal nat-hyp
```

## 实际图尚缺的条件

若将实际比较 (left,right) 定向为 right→left，仍须分别证明：

- 解释的 CP 方向与这个定向相符；逐边 Common 不会选择所需方向。
- 任意两实际顶点存在上述有限有向路径的共同后继，或另有共同出现于
  一棵合法脊柱的证明。实际 EBO 图的这项事实尚未证明。

上面的结构可及性还给 CP 反对称，并在给定合法 Common 时判定 CP 与
原树相等；Consequences 将它们提升到满足两项图条件的全部解释像。
比较仍只涉及树投影，不识别 Level 的合法性证明或记录。
要把这些树上的比较搬回原顶点或码，
还需相等反射／单射；要识别指定码序，还需方向和序的保真条件。
这些前提不由本定理或前缀定位自动给出。
本篇没有把条件结论称为实际图的全称结论，也没有否定实际图版本。
