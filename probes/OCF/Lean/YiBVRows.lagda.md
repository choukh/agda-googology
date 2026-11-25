# Ω 行在变量上的展开
不读记号；编译定理：一致孩子路径下的 Ω 行，及有保留等式时的树构造子规格。
没有分支关系下界，没有以目标值界作前提；底、表、孩子函数与路径均保留。
这里的层号是变量孩子函数上的指定 Ω 形状；源树等式可在调用点实填。
来源：直接展开 YiTBRow 的两行；one/q1 字面复写 YiKVRel 的结构常量，隔离记号导入。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBVRows where
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
one : B.L
one = B.nd B.sS (λ _ → B.zero)
q1 : B.Pos one
q1 = inj₂ (tt , inj₁ tt)
module Node (h : B.Tr B.zero → B.L)
  (o : P.Ok (B.nd (B.sΩ B.zero) h))
  (r : TB.Rb (B.nd (B.sΩ B.zero) h))
  (base : F.Base (B.nd (B.sΩ B.zero) h))
  (w : ∀ d → P._≤_ one (h d)) (beta : O.Tr⁺ one) where
  layer : B.L
  layer = B.nd (B.sΩ B.zero) h
  p : B.Pos layer
  p = inj₁ (inj₁ tt)
  child-base : ∀ d → F.Base (h d)
  child-base d i u = base i (P.inc d u)
  child-out : B.Tr B.zero → O.Tr⁺ one
  child-out d = TB.ψ (h d) (proj₂ o d) (proj₂ r d) (child-base d) one (w d) beta (proj₁ (O.Ωt (h d)))
  keep : F.Keep one (B.Tr B.zero) B.zero
  keep = F.kp layer o p (P.inu w)
  feed : B.Tr B.zero → B.Tr B.zero
  feed d = proj₁ (TB.ψ layer o r base B.zero (P.ink P.self) (base B.zero (P.ink P.self))
    (proj₁ (O.upz d (O.Ωt (h d)))))
  row : TB.ψ layer o r base one (P.inu w) beta (proj₁ (O.Ωt layer))
      ≡ F.node⁺ keep child-out feed
  row = refl
  kept-row : keep ≡ just (q1 , (λ d → d) , refl)
    → proj₁ (TB.ψ layer o r base one (P.inu w) beta (proj₁ (O.Ωt layer)))
       ≡ B.Ω q1 (λ d → proj₁ (child-out d))
  kept-row e = subst (λ k → proj₁ (F.node⁺ keep child-out feed) ≡ proj₁ (F.node⁺ k child-out feed)) e refl
  source-spec : (x : B.Tr layer) → x ≡ proj₁ (O.Ωt layer)
    → TB.ψ layer o r base one (P.inu w) beta x ≡ F.node⁺ keep child-out feed
  source-spec .(proj₁ (O.Ωt layer)) refl = row
```
