# 变量形状上的内层折叠
验收文件；依赖环境输运、内层函数规格、迭代与整行均为编译定理。
来源：YiE4Cut20 的变量节点律；入口见 YiE4ParamInner。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Inner where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Cut20 as C
-- perf: C-9，依赖环境的重索引在变量等式上证明。
shift-ctx : (h h′ : B.L) (eq : h ≡ h′) (o : P.Ok h) (r : TB.Rb h) (bs : F.Base h)
  → (h , o , r , bs) ≡ (h′ , subst P.Ok eq o , subst TB.Rb eq r , subst F.Base eq bs)
shift-ctx h .h refl o r bs = refl
module Inner (k : B.L) (a : B.Tr k → B.L) (o : P.Ok (B.nd (B.sΩ k) a))
  (r : TB.Rb (B.nd (B.sΩ k) a)) (bs : F.Base (B.nd (B.sΩ k) a)) (β : O.Tr⁺ B.zero) where
  ℓ = B.nd (B.sΩ k) a
  -- perf: S-1，变量形状层上的三个函数在出生处连同整函数等式封装。
  opaque
    g : B.Tr k → B.Tr ℓ
    g d = proj₁ (O.upz {s = B.sΩ k} {h = a} d (O.Ωt (a d)))
    g-eq : g ≡ (λ d → proj₁ (O.upz {s = B.sΩ k} {h = a} d (O.Ωt (a d))))
    g-eq = refl
    feed : B.Tr k → B.Tr k
    feed d = proj₁ (TB.ψ ℓ o r bs k (P.ink P.self) (bs k (P.ink P.self)) (g d))
    feed-eq : feed ≡ (λ d → proj₁ (TB.ψ ℓ o r bs k (P.ink P.self) (bs k (P.ink P.self)) (g d)))
    feed-eq = refl
    out : B.Tr k → O.Tr⁺ B.zero
    out d = TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) β (g d)
    out-eq : out ≡ (λ d → TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) β (g d))
    out-eq = refl
  chain : ℕ → B.Tr k
  chain = O.iter feed B.zero
  two : chain 2 ≡ feed (feed B.zero)
  two = refl
  -- perf: C-24，行律调用变量节点消去；不计算具体链点。
  opaque
    unfolding g feed out
    row : Q.collapse (ℓ , o , r , bs) β ≡ O.limc⁺ (λ n → out (chain n))
    row = Relation.Binary.PropositionalEquality.trans (Q.collapse-eq ℓ o r bs β)
      (C.row0 {X = B.Tr k} {z = B.zero} (F.kp ℓ o (inj₁ (inj₁ tt)) (P.z≤ ℓ)) out feed)
```
