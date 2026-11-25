# 第3站函数出生处封装
验收文件；外层、限制底与内层函数的定义等式及二次迭代为编译定理。
来源：SC7Seal、YiE3Cut19；不增加序数值下界。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Cut19 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
-- 来源：SC7Seal 与 YiE3Cut19；函数全部在出生处封装。
k = B.tw 2
-- perf: S-1，外层函数及其定义等式同块封装。
opaque
  outer-g : ∀ n → B.Tr (B.tw n) → B.Tr (B.tw (suc n))
  outer-g n c = proj₁ (O.upz {s = B.sΩ (B.tw n)} {h = FR.Step.child n} c (O.Ωt (FR.Step.child n c)))
  outer-g-eq : ∀ n c → outer-g n c ≡ FR.Step.g n c
  outer-g-eq n c = refl
  outer-feed : ∀ n → B.Tr (B.tw n) → B.Tr (B.tw n)
  outer-feed n c = proj₁ (TB.ψ (B.tw (suc n)) (P.Ok-tw (suc n)) (MT.rbᶻ (B.tw (suc n))) (GI.baseᴱ (suc n))
    (B.tw n) (P.ink P.self) (GI.baseᴱ (suc n) (B.tw n) (P.ink P.self)) (outer-g n c))
  outer-feed-eq : ∀ n c → outer-feed n c ≡ FR.Step.feed n c
  outer-feed-eq n c = refl
  outer-out : ∀ n → B.Tr (B.tw n) → O.Tr⁺ B.zero
  outer-out n c = TB.ψ (B.tw (suc n)) (P.Ok-tw (suc n)) (MT.rbᶻ (B.tw (suc n))) (GI.baseᴱ (suc n))
    B.zero (P.z≤ (B.tw (suc n))) (GI.betaᴱ (suc n)) (outer-g n c)
  outer-out-eq : ∀ n c → outer-out n c ≡ FR.Step.out n c
  outer-out-eq n c = refl
-- perf: S-1，限制底和分支函数均封装，形状在单独块中证明。
opaque
  base₀ : F.Base k
  base₀ i u = GI.baseᴱ 3 i (P.inc B.zero u)
  base₀-eq : base₀ ≡ (λ i u → GI.baseᴱ 3 i (P.inc B.zero u))
  base₀-eq = refl
  branch : B.Tr (B.tw 1) → B.Tr k
  branch d = proj₁ (TB.ψ k (P.Ok-tw 2) (MT.rbᶻ k) base₀ k P.self
    (GI.baseᴱ 3 k (P.ink P.self)) (outer-g 1 d))
  branch-eq : ∀ d → branch d ≡ proj₁ (TB.ψ k (P.Ok-tw 2) (MT.rbᶻ k) base₀ k P.self
    (GI.baseᴱ 3 k (P.ink P.self)) (outer-g 1 d))
  branch-eq d = refl
c₁ : B.Tr k
c₁ = B.Ω (inj₁ (inj₁ tt)) branch
a : B.Tr (B.tw 1) → B.L
a d = k B.⊕ B.↑ k (branch d)
h₁ = B.nd (B.sΩ (B.tw 1)) a
o₁ : P.Ok h₁
o₁ = proj₂ (P.Ok-tw 3) c₁
-- perf: S-13，计算律仅在本块显式开放依赖封装。
opaque
  unfolding branch base₀ outer-g
  c₁-actual : c₁ ≡ FR.Step.chain 2 1
  c₁-actual = refl
  h₁-actual : h₁ ≡ FR.Step.child 2 c₁
  h₁-actual = refl
-- perf: S-1，构造与规格同封，调用点使用导出等式。
opaque
  base₁ : F.Base h₁
  base₁ i u = GI.baseᴱ 3 i (P.inc c₁ u)
  base₁-eq : base₁ ≡ (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
  base₁-eq = refl
  inner-g : B.Tr (B.tw 1) → B.Tr h₁
  inner-g d = proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = a} d (O.Ωt (a d)))
  inner-g-eq : ∀ d → inner-g d ≡ proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = a} d (O.Ωt (a d)))
  inner-g-eq d = refl
-- perf: S-1/C-24，迭代的函数体不向后续 refl 开放。
opaque
  inner-feed : B.Tr (B.tw 1) → B.Tr (B.tw 1)
  inner-feed d = proj₁ (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ (B.tw 1) (P.ink P.self)
    (base₁ (B.tw 1) (P.ink P.self)) (inner-g d))
  inner-feed-eq : ∀ d → inner-feed d ≡ proj₁ (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ (B.tw 1) (P.ink P.self)
    (base₁ (B.tw 1) (P.ink P.self)) (inner-g d))
  inner-feed-eq d = refl
  inner-out : B.Tr (B.tw 1) → O.Tr⁺ B.zero
  inner-out d = TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁) (GI.betaᴱ 3) (inner-g d)
  inner-out-eq : ∀ d → inner-out d ≡ TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁) (GI.betaᴱ 3) (inner-g d)
  inner-out-eq d = refl
inner-chain : ℕ → B.Tr (B.tw 1)
inner-chain = O.iter inner-feed B.zero
inner-zero : inner-chain 0 ≡ B.zero
inner-zero = refl
inner-one : inner-chain 1 ≡ proj₁ (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ (B.tw 1) (P.ink P.self)
  (base₁ (B.tw 1) (P.ink P.self)) (inner-g B.zero))
inner-one = inner-feed-eq B.zero
-- perf: C-9，变量迭代引理由 YiE3Base.iter-two 搬来。
iter-two : {A : Set} (f : A → A) (z : A) → O.iter f z 2 ≡ f (f z)
iter-two f z = refl
inner-two : inner-chain 2 ≡ inner-feed (inner-feed B.zero)
inner-two = iter-two inner-feed B.zero
```
