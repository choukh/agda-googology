# 两个原合法公共界内的比较分派对应

两边各有自己的完整合法source界。比较的四条路径必须由Paths配对，
合法步进必须由LegalShape配对。结果只同步原cmpB分支及输出路径，
不在两个裸高度之间增加比较，也不把两份合法证据当作相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeCompare where
open import Data.Nat using (ℕ; _<′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; ss; ll)
open import OCF.Lean.GeneralOmegaCountableShapeBase

compose-paths : ∀ {a b c d A B : Cd} {p : Same a b} {q : Same c d} {r : Same A B} {u v s t} →
  Paths p q u v → Paths q r s t → Paths p r (⊲ᴮ-tr u s) (⊲ᴮ-tr v t)
compose-paths h (phere q) = h
compose-paths h (pnext k) = pnext (compose-paths h k)
compose-paths h (plimit n k) = plimit n (compose-paths h k)

steps-paths : ∀ {f g : ℕ → Cd} (p : ∀ n → Same (f n) (g n))
  (sta : ∀ {w} n → f n ⊲[ w ] f (Data.Nat.suc n))
  (stb : ∀ {w} n → g n ⊲[ w ] g (Data.Nat.suc n)) →
  (∀ n → Paths (p n) (p (Data.Nat.suc n)) (sta n) (stb n)) →
  ∀ {n m} (lt : n <′ m) → Paths (p n) (p m) (stepsᴮ sta lt) (stepsᴮ stb lt)
steps-paths p sta stb h ≤′-refl = h _
steps-paths p sta stb h (≤′-step lt) = compose-paths (steps-paths p sta stb h lt) (h _)

data Compared {a a′ b b′ : Cd} (p : Same a a′) (q : Same b b′) :
  ((b ⊲ a) ⊎ (a ⊲ b)) → ((b′ ⊲ a′) ⊎ (a′ ⊲ b′)) → Set where
  cleft : ∀ {u v} → Paths q p u v → Compared p q (inj₁ u) (inj₁ v)
  cright : ∀ {u v} → Paths p q u v → Compared p q (inj₂ u) (inj₂ v)

cmp-shape : ∀ {A B a a′ b b′ : Cd}
  (r : Same A B) la lb (p : Same a a′) (q : Same b b′) {pa pa′ pb pb′} →
  LegalShape r la lb → Paths p r pa pa′ → Paths q r pb pb′ →
  Compared p q (cmpB pa pb tt la) (cmpB pa′ pb′ tt lb)
cmp-shape r la lb .r q legal (phere .r) hq = cleft hq
cmp-shape .(ss r) la lb p .(ss r) legal (pnext {q = r} hp) (phere .(ss r)) = cright (pnext hp)
cmp-shape .(ll r) la lb p .(ll r) legal (plimit {q = r} n hp) (phere .(ll r)) = cright (plimit n hp)
cmp-shape (ss r) la lb p q legal (pnext hp) (pnext hq) = cmp-shape r la lb p q legal hp hq
cmp-shape (ll r) (sta , la) (stb , lb) p q (st , sub) (plimit n hp) (plimit m hq)
  with <-cmp n m
... | tri< lt _ _ = cmp-shape (r m) (la m) (lb m) p q (sub m)
  (compose-paths hp (steps-paths r sta stb st (<⇒<′ lt))) hq
... | tri> _ _ lt = cmp-shape (r n) (la n) (lb n) p q (sub n) hp
  (compose-paths hq (steps-paths r sta stb st (<⇒<′ lt)))
... | tri≈ _ refl _ = cmp-shape (r n) (la n) (lb n) p q (sub n) hp hq
```

cmp-shape处理同分量与跨分量，后者明确消费两边原合法step的Paths。
规范Γ场景可由ShapeBase.canonical-leg-legal实填该前提；把此结果接入
种类分类、低层坐标和完整反馈仍须另证。

```agda
open import OCF.Lean.FrozenWorldLift using (zz; oo)

zero-paths : ∀ {A B : Cd} (p : Same A B) → Paths zz p (z⊲ᴮ A) (z⊲ᴮ B)
zero-paths zz = phere zz
zero-paths (ss p) = pnext (zero-paths p)
zero-paths (ll p) = plimit 0 (zero-paths (p 0))
zero-paths (oo {κ = ()} p)

legal-on-paths : ∀ {a b A B : Cd} {p : Same a b} {q : Same A B} {u v}
  (h : Paths p q u v) la lb → LegalShape q la lb →
  LegalShape p (lgB⊲ u tt la) (lgB⊲ v tt lb)
legal-on-paths (phere p) la lb legal = legal
legal-on-paths (pnext h) la lb legal = legal-on-paths h la lb legal
legal-on-paths (plimit n h) (sta , la) (stb , lb) (st , sub) =
  legal-on-paths h (la n) (lb n) (sub n)
```

zero-paths给规范目标零路径的实际对应，legal-on-paths只消费已给的
Paths与LegalShape提取子证，不在任意路径之间增添证明无关性。
