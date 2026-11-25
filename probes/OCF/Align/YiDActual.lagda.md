# 实际需求诊断：纯可数派发不会以 Ω 为目标

本篇是第 4 层，显式读取冻结 Actual；不作为成品定义依赖。
先把 no-gamma-seed 的闭字段作逐项对照，再给全局非发生定理。
随后用一个保守的码界需求包络检查 InvD。包络不是树到码的函数，
也不是精确 Rep；它容纳所有保持 Small 码界、保持闭目标名字的对应。
最后写出这个覆盖合同，避免把尚未写出的完整 S4 对应当成已有结果。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDActual where

open import Data.Nat.Base using (ℕ; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxFork as W
import OCF.Align.YiRTransport as R
open import OCF.Align.YiRCountable using (Small; small-suc)
open import OCF.Align.YiDBase
import OCF.Align.YiDSeed as S
open import OCF.Align.YiSpineCommon using (Common)
open import OCF.Align.EboLeanDef
  using (T; ψ; sucT; Ωt; natT; fsn; fsn0; fsn₊; cof; Cof;
         c0; c1; cω; cΩ; cofA; cofψ0; cmpᵀ; lt; eq; gt)
open import OCF.Align.YiPrefixNames using (ω-code; ω-fs)
open import OCF.Align.YiSpineTrace using (Actual; first-call)
open import OCF.Align.YiTargets using (Targets; targets-below; target-in-env)

Ω-code : T
Ω-code = Ωt (sucT [])

-- 保留字面前缀，不能把基本列移位后仍宣称是同一个码。
a-code prefix-a-code : T
a-code = ψ [] [] ∷ ω-code
prefix-a-code = ψ [] [] ∷ a-code

-- 第 n 支是标准ω的第 n+1 支；没有把两个极限函数判等。
a-tail : ∀ n → F.suc (W.nat-read n) ≡ V.natF (suc n)
a-tail n = cong F.suc (W.nat-read-agrees n)

a-code-tail : ∀ n → fsn ω-code (suc n) ≡ natT (suc n)
a-code-tail n = ω-fs (suc n)

-- Ωprefix 中该闭字段是 1+a，极限列再移一项，仍只作逐项对照。
prefix-tail : ∀ n → V._+ᴸ_ (Y.tree W.one) (F.suc (W.nat-read n)) ≡
  V.natF (suc (suc n))
prefix-tail n = cong F.suc (go n)
  where
  go : ∀ n → V._+ᴸ_ (Y.tree W.one) (W.nat-read n) ≡ V.natF (suc n)
  go Data.Nat.Base.zero = refl
  go (suc n) = cong F.suc (go n)

a-fs : ∀ n → fsn a-code n ≡ natT (suc n)
a-fs n = cong (ψ [] [] ∷_) (ω-fs n)

prefix-a-fs : ∀ n → fsn prefix-a-code n ≡ natT (suc (suc n))
prefix-a-fs n = cong (ψ [] [] ∷_) (a-fs n)

-- 只认证这两个闭极限的每个有限列项，不生成任意Raw树的码。
-- 保留所有n，故不是有限样本；也不是整棵树/函数的相等。
data FiniteColumns : F.LF → T → Set where
  finite-columns : ∀ {f c} → cof c ≡ cω →
    (∀ n → Σ ℕ λ k → f n ≡ V.natF k × fsn c n ≡ natT k) →
    FiniteColumns (F.lim f) c

a-columns : FiniteColumns W.a a-code
a-columns = finite-columns refl (λ n → suc n , a-tail n , a-fs n)

prefix-a-columns : FiniteColumns W.prefix-a prefix-a-code
prefix-a-columns = finite-columns refl
  (λ n → suc (suc n) , prefix-tail n , prefix-a-fs n)

lt-not-gt : lt ≡ gt → ⊥
lt-not-gt ()

below-no-target : ∀ {c} → cmpᵀ c Ω-code ≡ lt → Targets c Ω-code → ⊥
below-no-target p a = lt-not-gt (trans (sym p) (targets-below a))

pair-lt : cmpᵀ (sucT a-code) Ω-code ≡ lt
pair-lt = refl

no-actual-pair : Actual (sucT a-code) Ω-code → ⊥
no-actual-pair = below-no-target pair-lt

prefix-pair-lt : cmpᵀ (sucT prefix-a-code) Ω-code ≡ lt
prefix-pair-lt = refl

no-prefix-actual-pair : Actual (sucT prefix-a-code) Ω-code → ⊥
no-prefix-actual-pair = below-no-target prefix-pair-lt
```

no-actual-pair 对全部 Reach 路径成立，不是有限塔搜索。
target-in-env 只有 Actual→Env 的方向；不能由 Ω 留在 Env、且种子中有字段，
反推这一对会被比较。旧 InvR 独立要求那个公共界，并没有使用或证明 Actual。
a-code 是字面 1+ω，prefix-a-code 是字面 2+ω；不约简为 ω，
因此本篇排除的是这两个逐项精确命名下的比较，不只是一个值读法。
有限列项用相同 natF k／natT k 对照，不声称 lim(n+1)=lim(n)，
不需 Funext，也不把有限列认证当作完整 S4 Rep 或新的序数值定理。

## 排除任意逐项对应码，包含标准形

上面两个展示码并非 NF，不能只凭选了这两个码就排除其它命名。
下面补强：若 c 是 ω 共尾，且第2支是至少2的有限码，则 c 及 c+1 都在 Ω 以下。
这条不要求 NF。cof 前提不能省：正规 Ω 的 fsn 哑值也会给有限码。

```agda
head-index : T → T
head-index [] = []
head-index (ψ u b ∷ xs) = u

head-zero : ∀ {u b xs k} → (ψ u b ∷ xs) ≡ natT (suc k) → u ≡ []
head-zero e = cong head-index e

head-bounds : ∀ u b xs → u ≡ [] →
  cmpᵀ (ψ u b ∷ xs) Ω-code ≡ lt × cmpᵀ (sucT (ψ u b ∷ xs)) Ω-code ≡ lt
head-bounds .[] b xs refl = refl , refl

single-not-long : ∀ p k → (p ∷ []) ≡ natT (suc (suc k)) → ⊥
single-not-long p k ()

argument-bounds : ∀ u b cb {k} → cofA u cb ≡ cω →
  fsn₊ u b cb 2 ≡ natT (suc (suc k)) →
  cmpᵀ (ψ u b ∷ []) Ω-code ≡ lt × cmpᵀ (sucT (ψ u b ∷ [])) Ω-code ≡ lt
argument-bounds u b c0 e ()
argument-bounds u b c1 e col = head-bounds u b [] (head-zero col)
argument-bounds u b cω e col = head-bounds u b [] (head-zero col)
argument-bounds u b (cΩ μ) e col with cmpᵀ (sucT μ) u
... | lt = head-bounds u b [] (head-zero col)
... | eq = head-bounds u b [] (head-zero col)
... | gt = head-bounds u b [] (head-zero col)

leaf-bounds : ∀ u cu {k} → cofψ0 u cu ≡ cω →
  fsn0 u cu 2 ≡ natT (suc (suc k)) →
  cmpᵀ (Ωt u) Ω-code ≡ lt × cmpᵀ (sucT (Ωt u)) Ω-code ≡ lt
leaf-bounds u c0 () col
leaf-bounds u c1 () col
leaf-bounds u cω {k} e col = ⊥-elim (single-not-long (ψ (fsn u 2) []) k col)
leaf-bounds u (cΩ μ) () col

finite-column-bounds : ∀ c {k} → cof c ≡ cω →
  fsn c 2 ≡ natT (suc (suc k)) →
  cmpᵀ c Ω-code ≡ lt × cmpᵀ (sucT c) Ω-code ≡ lt
finite-column-bounds [] () col
finite-column-bounds (ψ u b ∷ x ∷ xs) e col = head-bounds u b (x ∷ xs) (head-zero col)
finite-column-bounds (ψ u (x ∷ xs) ∷ []) e col = argument-bounds u (x ∷ xs) (cof (x ∷ xs)) e col
finite-column-bounds (ψ (x ∷ xs) [] ∷ []) e col = leaf-bounds (x ∷ xs) (cof (x ∷ xs)) e col
finite-column-bounds (ψ [] [] ∷ []) () col

height : F.LF → ℕ
height F.zero = Data.Nat.Base.zero
height (F.suc x) = suc (height x)
height (F.lim f) = Data.Nat.Base.zero
height (F.lc k c t g) = Data.Nat.Base.zero

height-nat : ∀ n → height (V.natF n) ≡ n
height-nat Data.Nat.Base.zero = refl
height-nat (suc n) = cong suc (height-nat n)

finite-name : ∀ {x m n} → x ≡ V.natF m → x ≡ V.natF n → m ≡ n
finite-name {m = m} {n} p q = trans (sym (height-nat m))
  (trans (cong height (trans (sym p) q)) (height-nat n))

column-value : ∀ {f : ℕ → F.LF} {c : T} {n m : ℕ} →
  (∀ i → Σ ℕ λ k → f i ≡ V.natF k × fsn c i ≡ natT k) →
  f n ≡ V.natF m → fsn c n ≡ natT m
column-value {n = n} cols named with cols n
... | k , tree-eq , code-eq = trans code-eq (cong natT (finite-name tree-eq named))

a-any-code-bounds : ∀ {c} → FiniteColumns W.a c →
  cmpᵀ c Ω-code ≡ lt × cmpᵀ (sucT c) Ω-code ≡ lt
a-any-code-bounds {c} (finite-columns e cols) =
  finite-column-bounds c e
    (column-value {f = λ n → F.suc (W.nat-read n)} {c = c} {n = 2} {m = 3} cols (a-tail 2))

prefix-any-code-bounds : ∀ {c} → FiniteColumns W.prefix-a c →
  cmpᵀ c Ω-code ≡ lt × cmpᵀ (sucT c) Ω-code ≡ lt
prefix-any-code-bounds {c} (finite-columns e cols) =
  finite-column-bounds c e
    (column-value {f = λ n → V._+ᴸ_ (Y.tree W.one) (F.suc (W.nat-read n))}
      {c = c} {n = 2} {m = 4} cols (prefix-tail 2))

no-any-actual-pair : ∀ {c} → FiniteColumns W.a c → Actual (sucT c) Ω-code → ⊥
no-any-actual-pair named = below-no-target (proj₂ (a-any-code-bounds named))

no-any-prefix-actual-pair : ∀ {c} → FiniteColumns W.prefix-a c → Actual (sucT c) Ω-code → ⊥
no-any-prefix-actual-pair named = below-no-target (proj₂ (prefix-any-code-bounds named))

-- 把原树字段也留在命题中：存在一个逐项对应码，其后继实际与Ω比较。
FieldActual : F.LF → Set
FieldActual k = Σ T λ c → FiniteColumns k c × Actual (sucT c) Ω-code

no-actual-field : FieldActual W.a → ⊥
no-actual-field (c , named , a) = no-any-actual-pair named a

no-prefix-actual-field : FieldActual W.prefix-a → ⊥
no-prefix-actual-field (c , named , a) = no-any-prefix-actual-pair named a
```

两个 no-any 定理覆盖所有满足逐项有限列对应的 c，标准形当然也在量词内；
并不需要先选择唯一的码。a-columns／prefix-a-columns 已给非空实例。
这把“所给非标准码不实际”加强成“任何这种逐项对应码都不实际”。

## 对全部种子字段作按需检查

CodeBound x c 仅说：若树 x 是 Small，候选派发码 c 在 Ω 以下。
它故意多收同一层内的候选，不能被当作精确命名。
目标仅使用本次历史 Env=[Ω,0] 中两个已明确的闭名字；原版与前缀版分别参数化。
ActualDemand 中每条需求都带一个真正的 Actual，未用“在 Env 中”替代发生性。

```agda
CodeBound : F.LF → T → Set
CodeBound x c = Small x → cmpᵀ c Ω-code ≡ lt

data TargetName (ν : Y.Level) : F.LF → T → Set where
  zero-target : TargetName ν F.zero []
  omega-target : TargetName ν (Y.tree ν) Ω-code

ActualDemand : Y.Level → Demand
ActualDemand ν x y = Σ T λ c → Σ T λ u →
  CodeBound x c × TargetName ν y u × Targets c u

target-code : ∀ ν {y u} → TargetName ν y u → y ≡ Y.tree ν →
  (Y.tree ν ≡ F.zero → ⊥) → u ≡ Ω-code
target-code ν zero-target e nonzero = ⊥-elim (nonzero (sym e))
target-code ν omega-target e nonzero = refl

no-small-demand : ∀ ν {x} → (Y.tree ν ≡ F.zero → ⊥) → Small x →
  ActualDemand ν x (Y.tree ν) → ⊥
no-small-demand ν nonzero s (c , u , b , name , a) =
  below-no-target (b s) (subst (Targets c) (target-code ν name refl nonzero) a)

ν-nonzero : Y.tree R.ν ≡ F.zero → ⊥
ν-nonzero ()

νp-nonzero : Y.tree S.νp ≡ F.zero → ⊥
νp-nonzero ()

seed-invD : InvD (ActualDemand R.ν) (R.ν ∷ Y.zero ∷ []) R.seed-tree
seed-invD = S.seed-check (no-small-demand R.ν ν-nonzero)

prefix-seed-invD : InvD (ActualDemand S.νp) (S.νp ∷ Y.zero ∷ []) S.seedp
prefix-seed-invD = S.prefix-seed-check (no-small-demand S.νp νp-nonzero)

no-counter-demand : ActualDemand R.ν (F.suc W.a) (Y.tree R.ν) → ⊥
no-counter-demand = no-small-demand R.ν ν-nonzero (small-suc (S.seed-fields W.field-a))

no-prefix-counter-demand : ActualDemand S.νp (F.suc W.prefix-a) (Y.tree S.νp) → ⊥
no-prefix-counter-demand = no-small-demand S.νp νp-nonzero
  (small-suc (S.seedp-fields W.prefix-field-a))

-- 根字段0的派发树为1，确实会与0比较；检查并非空需求。
root-demand : ActualDemand R.ν (F.suc F.zero) F.zero
root-demand = sucT [] , [] , (λ _ → refl) , zero-target , first-call

root-checked : Common (dispatch R.seed-tree K.at) Y.zero
root-checked = needed seed-invD K.at (there (here refl)) root-demand
```

两份 seed-invD 都检查该种子的所有 Field（包含每个合法 Raw 分支），
不为这些字段逐个生成码；SmallFields 的树侧定理已经覆盖全部字段。
向目标 Ω 的任何包络需求都被 below-no-target 排除；向0的需求用派发树自身作界。
因此旧 no-gamma-seed 的矛盾不再由这个 InvD 推出。

## 完整对应的覆盖义务明列

对任意关系 Q，若它保 Small 码界，且在当前 Env 中保留两个闭目标名字，
则每一条 Q 相关的 Actual 需求都由上述包络覆盖，故获得同样的逐对界。
不要求 Q 对原始树全定义。这里不构造完整 S4 的 Q，也不证 γ 保持。

```agda
RelatedDemand : (F.LF → T → Set) → Demand
RelatedDemand Q x y = Σ T λ c → Σ T λ u → Q x c × Q y u × Targets c u

related-check : ∀ {ν E t} (Q : F.LF → T → Set) →
  (∀ {x c} → Q x c → CodeBound x c) →
  (∀ {v u} → v ∈ E → Q (Y.tree v) u → TargetName ν (Y.tree v) u) →
  InvD (ActualDemand ν) E t → InvD (RelatedDemand Q) E t
related-check Q bounded named i = demanded (context i)
  (λ f p (c , u , qx , qy , a) → needed i f p (c , u , bounded qx , named p qy , a))
```

这是显式范围：seed 的包络 InvD 定理无额外前提；把它用于一个完整的树／码对应，
还须该对应实填 related-check 的两个保真条件。这里没有把这个尚未给出的实例
或完整的树侧实际运行覆盖记作已完成结果。
