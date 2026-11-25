# (a) 依赖上下文：目标来自严格先前的有限 γ 历史

每条真实运行历史携带一个有限候选表 Env。根表只有 0；前驱步不增加；
基本列步若有比较，就把该步共尾层 ν 加入表。该 ν 是新 γ 链的目标，
不是该步已有目标 u。证明表覆盖输出中所有正参数 ψ 的目标，
因此它也覆盖下一次实际比较的目标。这里没有按当前 u 修补候选表。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiTargetHistory where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef
  using (T; PT; ψ; Ωt; natT; pred; cof; Cof; c0; c1; cω; cΩ;
         Cmp; lt; eq; gt; cmpᵀ; sucT; fsn; fsn0; fsn₊; fsnc; fsT; γT; ΩTower; EBOψ)
open import OCF.Align.YiSpineTrace using (Reach; tower; pred-step; fs-step)
open import OCF.Align.YiTargetBase
open import OCF.Align.YiTargetTransport
open import OCF.Align.YiTargetScan using (scan; scan₀; scan₊)

ScanBound : (T → Set) → Maybe (T × T) → Set
ScanBound P nothing = ⊤
ScanBound P (just (ν , u)) = P ν

nat-tags : ∀ {P} n → AllTags P (natT n)
nat-tags zero = tt
nat-tags (suc n) = tt , tt , tt , nat-tags n

tower-tags : ∀ {P} k → AllTags P (ΩTower k)
tower-tags zero = nat-tags 1
tower-tags (suc k) = omega (tower-tags k)

rep-tags : ∀ {P} (p : PT) → AllTags P (p ∷ []) → ∀ n → AllTags P (replicate n p)
rep-tags p h zero = tt
rep-tags p@(ψ u b) h@(hu , tu , tb , ts) (suc n) = hu , tu , tb , rep-tags p h n

fsn-tags : ∀ {P} a n → AllTags P a → ScanBound P (scan a) → AllTags P (fsn a n)
fsn₀-tags : ∀ {P} u c n → AllTags P u → ScanBound P (scan₀ u c) → AllTags P (fsn0 u c n)
fsn₊-tags : ∀ {P} u b c n → cof b ≡ c → P u → AllTags P u → AllTags P b →
  ScanBound P (scan₊ u b c) → AllTags P (fsn₊ u b c n)
fsnc-tags : ∀ {P} u b ν m n → P u → AllTags P u → AllTags P b → P ν → AllTags P ν →
  AllTags P (fsnc u b ν m n)

fsn-tags [] n h permitted = tt
fsn-tags (ψ u b ∷ y ∷ ys) n (h , tu , tb , ts) permitted =
  h , tu , tb , fsn-tags (y ∷ ys) n ts permitted
fsn-tags (ψ u b@(_ ∷ _) ∷ []) n (h , tu , tb , ts) permitted =
  fsn₊-tags u b (cof b) n refl h tu tb permitted
fsn-tags (ψ u@(_ ∷ _) [] ∷ []) n (h , tu , tb , ts) permitted =
  fsn₀-tags u (cof u) n tu permitted
fsn-tags (ψ [] [] ∷ []) n h permitted = tt

fsn₀-tags u c0 n tu permitted = tt
fsn₀-tags u c1 n tu permitted = nat-tags n
fsn₀-tags u cω n tu permitted = omega (fsn-tags u n tu permitted)
fsn₀-tags u (cΩ ν) n tu permitted = omega (fsT-tags u (natT n) tu (nat-tags n))

fsn₊-tags u b c0 n eb pu tu tb permitted = tt
fsn₊-tags u b c1 n eb pu tu tb permitted =
  rep-tags (ψ u (pred b)) (singleton (head-from pu (pred b)) tu (pred-tags b tb)) n
fsn₊-tags u b cω n eb pu tu tb permitted =
  singleton (head-from pu (fsn b n)) tu (fsn-tags b n tb permitted)
fsn₊-tags u b (cΩ ν) n eb pu tu tb permitted =
  fsnc-tags u b ν (cmpᵀ (sucT ν) u) n pu tu tb permitted (cof-tags b tb eb)

fsnc-tags u b ν gt n pu tu tb pν tν =
  singleton (head-from pu (fsT b (γT b ν n))) tu
    (fsT-tags b (γT b ν n) tb (gamma-tags b ν n pν tb tν))
fsnc-tags u b ν lt n pu tu tb pν tν =
  singleton (head-from pu (fsT b (natT n))) tu (fsT-tags b (natT n) tb (nat-tags n))
fsnc-tags u b ν eq n pu tu tb pν tν =
  singleton (head-from pu (fsT b (natT n))) tu (fsT-tags b (natT n) tb (nat-tags n))

added : Maybe (T × T) → List T
added nothing = []
added (just (ν , u)) = ν ∷ []

Env : ∀ {t} → Reach t → List T
Env (tower k) = [] ∷ []
Env (pred-step r e) = Env r
Env (fs-step {t} r e n) = added (scan t) ++ Env r

in-left : ∀ {a : T} {xs : List T} ys → a ∈ xs → a ∈ (xs ++ ys)
in-left ys (here e) = here e
in-left ys (there p) = there (in-left ys p)

in-right : ∀ {a : T} {ys : List T} xs → a ∈ ys → a ∈ (xs ++ ys)
in-right [] p = p
in-right (_ ∷ xs) p = there (in-right xs p)

scan-bound-map : ∀ {P Q} → (∀ {v} → P v → Q v) → ∀ m → ScanBound P m → ScanBound Q m
scan-bound-map f nothing h = tt
scan-bound-map f (just (ν , u)) h = f h

added-bound : ∀ m → ScanBound (λ u → u ∈ added m) m
added-bound nothing = tt
added-bound (just (ν , u)) = here refl

env-tags : ∀ {t} (r : Reach t) → AllTags (λ u → u ∈ Env r) t
env-tags (tower k) = singleton (head-from (here refl) (ΩTower k)) tt (tower-tags k)
env-tags (pred-step {t} r e) = pred-tags t (env-tags r)
env-tags (fs-step {t} r e n) = fsn-tags t n
  (tags-map (in-right (added (scan t))) t (env-tags r))
  (scan-bound-map (in-left (Env r)) (scan t) (added-bound (scan t)))
```

这是一条覆盖所有 Reach、所有基本列编号的结构归纳定理，不是有限运行测试。
Env 会保留已不活跃的历史目标并允许重复；因此是来源包络，未声称精确等于
某个固定层号的 Targets。候选表只由严格先前的展开步生成，依赖整个运行上下文。
