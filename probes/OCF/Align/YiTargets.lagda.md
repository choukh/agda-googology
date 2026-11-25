# Targets：实际目标的有限历史来源界

结论是 (a) 依赖上下文。Targets l u 直接采用已冻结 Actual，
不把任意语法子项当成实际发生。给定 Reach 历史 r，所有该时刻目标
都在 Env r 里；Env 的生成只看此前 γ 引入的共尾层，不读取当前目标。
全局 Targets l 包含在相应历史候选的并集中，本篇没有证明该并集有限。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiTargets where

open import Data.List.Base using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (nothing; just)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; sucT; cof; cω; cmpᵀ; gt)
open import OCF.Align.YiSpineTrace
  using (Reach; FsnCall; Actual; actual; source; reached; countable-limit; call; actual-gt)
open import OCF.Align.YiTargetBase using (AllTags)
open import OCF.Align.YiTargetScan using (scan; scan-call; call-tags)
open import OCF.Align.YiTargetHistory using (Env; env-tags; added)
open import OCF.Align.YiTargetOrigin using (Origin; scan-origin)
open import OCF.Align.YiSpineTrace using (tower; pred-step; fs-step)

Targets : T → T → Set
Targets l u = Actual l u

At : ∀ {t} → Reach t → T → T → Set
At {t} r l u = cof t ≡ cω × FsnCall t l u

targets-context : ∀ {l u} (a : Targets l u) → At (reached a) l u
targets-context a = countable-limit a , call a

context-target : ∀ {t l u} (r : Reach t) → At r l u → Targets l u
context-target {t} r (e , c) = actual t r e c

context-bound : ∀ {t l u} (r : Reach t) → At r l u → u ∈ Env r
context-bound {t} r (e , c) = call-tags {t = t} (env-tags r) c

target-in-env : ∀ {l u} (a : Targets l u) → u ∈ Env (reached a)
target-in-env a = context-bound (reached a) (targets-context a)

targets-below : ∀ {l u} → Targets l u → cmpᵀ l u ≡ gt
targets-below = actual-gt

-- 每个非根新增候选来自该历史中真正发生的一次γ比较；
-- 新增ν不是当时的旧目标v，而是该次比较左端ν+1的前驱。
added-call : ∀ {t} (r : Reach t) → cof t ≡ cω → ∀ {ν} → ν ∈ added (scan t) →
  Σ T (λ v → FsnCall t (sucT ν) v × cmpᵀ (sucT ν) v ≡ gt)
added-call {t} r e p with scan t in s
... | nothing with p
...   | ()
added-call {t} r e p | just (ν , v) with p
... | here refl = v , scan-call t s , actual-gt (actual t r e (scan-call t s))
... | there ()

added-target-blind : ∀ ν u v → added (just (ν , u)) ≡ added (just (ν , v))
added-target-blind ν u v = refl

-- Earlier 的来源项严格位于当前项以前；不准把当前项本身作为birth。
data Earlier (u : T) : ∀ {t} → Reach t → Set where
  born : ∀ {t} (r : Reach t) (e : cof t ≡ cω) n {v} →
    scan t ≡ just (u , v) → Origin t u → Earlier u (fs-step r e n)
  through-pred : ∀ {t} {r : Reach t} {e} → Earlier u r → Earlier u (pred-step r e)
  through-fs : ∀ {t} {r : Reach t} {e n} → Earlier u r → Earlier u (fs-step r e n)

carry-pred : ∀ {t u} (r : Reach t) e →
  u ≡ [] ⊎ Earlier u r → u ≡ [] ⊎ Earlier u (pred-step r e)
carry-pred r e (inj₁ p) = inj₁ p
carry-pred r e (inj₂ p) = inj₂ (through-pred p)

carry-fs : ∀ {t u} (r : Reach t) e n →
  u ≡ [] ⊎ Earlier u r → u ≡ [] ⊎ Earlier u (fs-step r e n)
carry-fs r e n (inj₁ p) = inj₁ p
carry-fs r e n (inj₂ p) = inj₂ (through-fs p)

env-origin : ∀ {t u} (r : Reach t) → u ∈ Env r → u ≡ [] ⊎ Earlier u r
env-origin (tower k) (here e) = inj₁ e
env-origin (tower k) (there ())
env-origin (pred-step r e) p = carry-pred r e (env-origin r p)
env-origin (fs-step {t} r e n) p with scan t in s
... | nothing = carry-fs r e n (env-origin r p)
... | just (ν , v) with p
...   | here refl = inj₂ (born r e n s (scan-origin t s))
...   | there q = carry-fs r e n (env-origin r q)

target-history-origin : ∀ {l u} (a : Targets l u) →
  u ≡ [] ⊎ Earlier u (reached a)
target-history-origin a = env-origin (reached a) (target-in-env a)

earlier-comparison : ∀ {t u} {r : Reach t} → Earlier u r → Σ T (λ v → Targets (sucT u) v)
earlier-comparison (born {t} r e n {v} s o) = v , actual t r e (scan-call t s)
earlier-comparison (through-pred p) = earlier-comparison p
earlier-comparison (through-fs p) = earlier-comparison p

target-came-from-comparison : ∀ {l u} (a : Targets l u) → (u ≡ [] → ⊥) →
  Σ T (λ v → Targets (sucT u) v)
target-came-from-comparison a nonzero with target-history-origin a
... | inj₁ e = ⊥-elim (nonzero e)
... | inj₂ p = earlier-comparison p
```

生成规则的全部参数是运行历史：根含0；pred保留；fsn步至多加入上一步
真实比较左端的前驱ν。目标u的来源定理不以“u已经在表中”为额外前提，
而从根对所有Reach归纳建立；候选表不按ν+1这个当前层号重新筛选。

这是上下文包络的正面定理，不是“任何只依赖层号的刻画都不可能”的否定。
同一层号跨所有历史的目标并集是否能再简化、是否包含无限字面反链仍未定；
本轮不把(a)说成排除了(b)。按作者第四项，不据此写树运算或 ψ。
