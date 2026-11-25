# 上下文不变量的局部正面保持

只复用无记号树侧定义，不导入 C 线。界 B 本身是合法树。
已定位字段 k+1 的前驱 k 可加入环境而不换界；取后继树的前驱也保不变量。
这里的加入保持仍针对同一当前树，不冒充完整 γ 输出的保持。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCtxStep where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All as A using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Lgl)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixCore using (module G)
open import OCF.Align.LevelFixVal using (CP; Legal; CP-tr)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiLevelCompare using (compare)
open import OCF.Align.YiCtxBase

field-legal : ∀ {k t} → Field k t → Legal t → Legal k
field-legal at (lk , first , mono , same , lt , lg) = lk
field-legal (in-suc p) lawful = field-legal p lawful
field-legal (in-lim n p) (step , lawful) = field-legal p (lawful n)
field-legal (in-index p) (lk , first , mono , same , lt , lg) = field-legal p lk
field-legal (in-first p) (lk , first , mono , same , lt , lg) = field-legal p lt
field-legal (in-branch η e p) (lk , first , mono , same , lt , lg) = field-legal p (lg η e)

env-at : ∀ {E B} {u : Y.Level} → All (λ x → CP (Y.tree x) B) E → u ∈ E → CP (Y.tree u) B
env-at (p A.∷ ps) (here refl) = p
env-at (p A.∷ ps) (there q) = env-at ps q

compare-field-env : ∀ {E current k} (i : Inv E current) → Field k (Y.tree current) →
  ∀ {u} → u ∈ E → CP (F.suc k) (Y.tree u) ⊎ CP (Y.tree u) (F.suc k)
compare-field-env i f p = compare (Y.tree (bound (context i)))
  (field-pos i f) (env-at (env-pos (context i)) p) (Y.legal (bound (context i)))

move-all : ∀ {E a b} → CP a b → All (λ x → CP (Y.tree x) a) E → All (λ x → CP (Y.tree x) b) E
move-all p A.[] = A.[]
move-all p (q A.∷ qs) = CP-tr q p A.∷ move-all p qs

raise-ctx : ∀ {E} (c : Ctx E) (B′ : Y.Level) → CP (Y.tree (bound c)) (Y.tree B′) → Ctx E
raise-ctx c B′ p = ctx B′ (move-all p (env-pos c))

raise-inv : ∀ {E current} (i : Inv E current) (B′ : Y.Level) →
  CP (Y.tree (bound (context i))) (Y.tree B′) → Inv E current
raise-inv i B′ p = invariant (raise-ctx (context i) B′ p) (λ f → CP-tr (field-pos i f) p)

adjoin : ∀ {E} (c : Ctx E) (ν : Y.Level) → CP (Y.tree ν) (Y.tree (bound c)) → Ctx (ν ∷ E)
adjoin c ν p = ctx (bound c) (p A.∷ env-pos c)

field-level : (current : Y.Level) → ∀ {k} → Field k (Y.tree current) → Y.Level
field-level current {k} p = Y.level k (field-legal p (Y.legal current))

adjoin-field : ∀ {E current k} (i : Inv E current) (p : Field k (Y.tree current)) →
  Inv (field-level current p ∷ E) current
adjoin-field {current = current} i p = invariant
  (adjoin (context i) (field-level current p) (CP-tr (V.suc V.self) (field-pos i p)))
  (field-pos i)

pred-inv : ∀ {E} (current : Y.Level) → Inv E (Y.suc current) → Inv E current
pred-inv current i = invariant (context i) (λ p → field-pos i (in-suc p))

no-field-up₀ : ∀ (η : Raw F.zero) {k} → Field k (V.up F.zero η) → ⊥
no-field-up₀ G.zero ()
no-field-up₀ (G.suc η) (in-suc p) = no-field-up₀ η p
no-field-up₀ (G.lim f) (in-lim n p) = no-field-up₀ (f n) p
no-field-up₀ (G.lc () c t g) p
no-field-up₀ (G.em () t) p
no-field-up₀ G.top (in-suc ())

Ω₁ : Y.Level
Ω₁ = Y.Ω (Y.suc Y.zero)

one-fields : ∀ {k} → Field k (Y.tree Ω₁) → CP (F.suc k) (F.suc F.zero)
one-fields at = V.self
one-fields (in-index ())
one-fields (in-first (in-suc ()))
one-fields (in-branch η e p) = ⊥-elim (no-field-up₀ η p)

start : Inv (Y.zero ∷ []) Ω₁
start = invariant (ctx (Y.suc Y.zero) (V.suc V.self A.∷ A.[])) one-fields

adjoin-example : Inv (Y.zero ∷ Y.zero ∷ []) Ω₁
adjoin-example = adjoin-field start at

pred-source : Inv (Y.zero ∷ []) (Y.suc Ω₁)
pred-source = invariant (context start) (λ { (in-suc p) → field-pos start p })

pred-example : Inv (Y.zero ∷ []) Ω₁
pred-example = pred-inv Ω₁ pred-source
```

start 是最小正规 Ω 的实填起点，不是所有 Ω 塔根的全称起点。
raise-inv 只运输已给出的字面 CP 界扩展，不能制造缺少的扩展证据。
adjoin-field 给 γ 前驱入 Env 的那一半；新 γ 树是否保全部字段仍须单独证明。
