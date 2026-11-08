# 实际有限秩决定不依赖外部公共界

仅消去实际pick读取的有限终点路径。两个公共界可以不同，但每次比较
都有自己的字面公共界及两条路径。above保留各自的界证据；没有把它们
判成相等，也没有把整棵Path函数判成相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFiniteBridgeDecision where
import Data.Nat

open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Align.BoundedCompletionFiniteBridgePaths

data SameDecision {B B′ t A} : Decision B t A → Decision B′ t A → Set where
  kept : ∀ κ fr → SameDecision (keep κ fr) (keep κ fr)
  same-rank : ∀ to → SameDecision (same to) (same to)
  higher : ∀ i pi pi′ q to → SameDecision (above i pi q to) (above i pi′ q to)

pick-proof : ∀ {B B′ t i A} (to : HB (Native i) → A)
  (pi : hs i ⊲ B) (pi′ : hs i ⊲ B′)
  (s : (t ⊲ hs i) ⊎ (hs i ⊲ t)) →
  SameDecision (pick to pi s) (pick to pi′ s)
pick-proof to pi pi′ (inj₂ q) = kept _ _
pick-proof to pi pi′ (inj₁ hself) = kept _ _
pick-proof to pi pi′ (inj₁ (hsuc hself)) = same-rank _
pick-proof to pi pi′ (inj₁ (hsuc q@(hsuc _))) = higher _ _ _ _ _
pick-proof to pi pi′ (inj₁ (hsuc q@(hlim _ _))) = higher _ _ _ _ _
pick-proof to pi pi′ (inj₁ (hsuc (hLim {κ = ()} _ _)))

cross : ∀ i {B B′ t A} (to : HB (Native (num i)) → A)
  (pi : hs (num i) ⊲ B) (pi′ : hs (num i) ⊲ B′)
  (q : t ⊲ hs (num i)) (r : hs (num i) ⊲ t) →
  SameDecision (pick to pi (inj₁ q)) (pick to pi′ (inj₂ r))
cross i to pi pi′ q r with finite-antisym (Data.Nat.suc i) q r
... | refl rewrite finite-path-unique (Data.Nat.suc i) q hself
                 | finite-path-unique (Data.Nat.suc i) r hself = kept _ _

cross′ : ∀ i {B B′ t A} (to : HB (Native (num i)) → A)
  (pi : hs (num i) ⊲ B) (pi′ : hs (num i) ⊲ B′)
  (q : t ⊲ hs (num i)) (r : hs (num i) ⊲ t) →
  SameDecision (pick to pi (inj₂ r)) (pick to pi′ (inj₁ q))
cross′ i to pi pi′ q r with finite-antisym (Data.Nat.suc i) q r
... | refl rewrite finite-path-unique (Data.Nat.suc i) q hself
                 | finite-path-unique (Data.Nat.suc i) r hself = kept _ _

pick-independent : ∀ i m {B B′ A} (to : HB (Native (num i)) → A)
  (pi : hs (num i) ⊲ B) (pi′ : hs (num i) ⊲ B′)
  (s s′ : (num m ⊲ hs (num i)) ⊎ (hs (num i) ⊲ num m)) →
  SameDecision (pick to pi s) (pick to pi′ s′)
pick-independent i m to pi pi′ (inj₁ q) (inj₁ r)
  rewrite finite-path-unique (Data.Nat.suc i) r q = pick-proof to pi pi′ (inj₁ q)
pick-independent i m to pi pi′ (inj₂ q) (inj₂ r)
  rewrite finite-path-unique m r q = pick-proof to pi pi′ (inj₂ q)
pick-independent i m to pi pi′ (inj₁ q) (inj₂ r) = cross i to pi pi′ q r
pick-independent i m to pi pi′ (inj₂ r) (inj₁ q) = cross′ i to pi pi′ q r

actual-rank : ∀ i m {B B′ A} (lB : LgB B) (lB′ : LgB B′)
  (pi : hs (num i) ⊲ B) (pi′ : hs (num i) ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′)
  (to : HB (Native (num i)) → A) →
  SameDecision (pick to pi (cmpB pi pt tt lB))
    (pick to pi′ (cmpB pi′ pt′ tt lB′))
actual-rank i m lB lB′ pi pi′ pt pt′ to = pick-independent i m to pi pi′ _ _
```

进一步把这条律接到原 classify 的全部有限分量种类，而非要求调用者
另行假定它属于有限rank。

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _,_)

FiniteClass : ∀ {c A} → Class c A → Set
FiniteClass (base κ to fr a b) = ⊤
FiniteClass (rank i pi to fr a b) = Σ ℕ (λ n → i ≡ num n)

finite-raise : ∀ {c d A} (p : c ⊲ d) (cl : Class c A) →
  FiniteClass cl → FiniteClass (raise p cl)
finite-raise p (base κ to fr a b) fc = tt
finite-raise p (rank i pi to fr a b) fc = fc

finite-classify : ∀ n κ → FiniteClass (classify (num n) κ)
finite-classify zero κ = tt
finite-classify (suc n) (inj₁ κ) =
  finite-raise (hsuc hself) (classify (num n) κ) (finite-classify n κ)
finite-classify (suc n) (inj₂ _) = n , refl

class-independent : ∀ m {c B B′ A} (cl : Class c A) → FiniteClass cl →
  (lB : LgB B) (lB′ : LgB B′)
  (pc : c ⊲ B) (pc′ : c ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′) →
  SameDecision (decide pt lB (raise pc cl)) (decide pt′ lB′ (raise pc′ cl))
class-independent m (base κ to fr a b) fc lB lB′ pc pc′ pt pt′ = kept _ _
class-independent m (rank i pi to fr a b) (n , refl) lB lB′ pc pc′ pt pt′ =
  actual-rank n m lB lB′ (⊲ᴮ-tr pi pc) (⊲ᴮ-tr pi pc′) pt pt′ to

actual-component : ∀ n m κ {B B′} (lB : LgB B) (lB′ : LgB B′)
  (pc : num n ⊲ B) (pc′ : num n ⊲ B′)
  (pt : num m ⊲ B) (pt′ : num m ⊲ B′) →
  SameDecision (decide pt lB (raise pc (classify (num n) κ)))
    (decide pt′ lB′ (raise pc′ (classify (num n) κ)))
actual-component n m κ = class-independent m (classify (num n) κ) (finite-classify n κ)
```

`actual-component`覆盖每个有限源分量、每个有限目标、每个真实种类，
两次比较各有合法公共界。keep的kind及坐标函数字面相同，same亦然；
above的目标层及目标路径相同，只有指向各自公共界的证据保留不同。

这仍不是整fold的同余定理。diagonal两条反馈链若仅有Same关系，
原分支g需要相应同余证书才能接受不同但同形的坐标；不把函数外延或
任意g的Same保持偷放进本定理。下一桥应消费实际floor/θ生成族的分支性质。

前提可满足：任意n取源与目标都为num n，第一公共界取num n，两条
路径hself；第二公共界取hs(num n)，两条路径hsuc hself。两界都是
合法自然数树，全部实际κ均可代入。这不要求任意两棵裸Cd可比。
