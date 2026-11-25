# 一致槽位行的值与边界（验收文件）
编译定理：旧 `kp` 反例的同一对槽位上新行单调；`Ωt (tw 1)` 的新折叠值为 ω（正自然数列上确界）。
另一个小闭对象上，新输出的值为 1，严格低于现主线；该比较不声称是整个 `Ωt (tw 1)` 的比较。
构造的首个接口阻点是 `Pos zero` 为空；这不否定其他结点行，也不否定 B7。
来源：旧反例及值关系分别复用 `YiFWNode`、`YiFWValue`、`YiVWVal`；入口为 `main≰out`、`no-zero-target`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBNAccept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
import OCF.Lean.YiRWBlock as O
import OCF.Lean.YiRWOps as R
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiFWValue as FV
import OCF.Lean.YiFWNode as W
open import OCF.Lean.YiFWBlock
open import OCF.Lean.YiFWCompat
open import OCF.Lean.YiBNRow
import OCF.Lean.YiBNFold as BN

row-value : ∀ {S : Sg} (j : O.L) (q : O.Pos j) (p : P S) (G : B S p → T (Sig j))
  → FV.val j (row {S = S} {S′ = Sig j} q p G) V.≈ FV.val j (G (b₀ S p))
row-value {S} j q p G = V.Ω≼ (λ _ → V.≼-refl _) , V.≼Ω (O.fromBr j q O.zero) (V.≼-refl _)

q : O.Pos W.one
q = W.p
module C = BN.Fold q
β : Positive (Sig W.one)
β = suc zero , ◃s

old-pair-step : Lt (Sig W.one)
  (row {S = Sig W.parent} {S′ = Sig W.one} q W.pi (λ _ → suc zero))
  (row {S = Sig W.parent} {S′ = Sig W.one} q W.pc (λ _ → proj₁ (W.next⁺ β)))
old-pair-step = row-step {S = Sig W.parent} {S′ = Sig W.one} q {p = W.pi} {p′ = W.pc}
  W.eq-pi-pc (λ _ → suc zero) (λ _ → proj₁ (W.next⁺ β)) (λ _ → W.branch-output-step)

no-zero-target : O.Pos O.zero → ⊥
no-zero-target ()

closed-top₁ : proj₁ (C.φ (O.tw 1) β (embed (O.tw 1) (proj₁ (R.Ωt (O.tw 1)))) )
  ≡ Ω q (λ _ → proj₁ (W.next⁺ β))
closed-top₁ = refl

closed-top₁-legal : Lt (Sig W.one) zero
  (proj₁ (C.φ (O.tw 1) β (embed (O.tw 1) (proj₁ (R.Ωt (O.tw 1))))))
closed-top₁-legal = C.legal (O.tw 1) β (embed (O.tw 1) (proj₁ (R.Ωt (O.tw 1))))

nat : ℕ → T (Sig W.one)
nat zero = zero
nat (suc n) = suc (nat n)

one+nat : ∀ n → suc zero + nat n ≡ nat (suc n)
one+nat zero = refl
one+nat (suc n) = cong suc (one+nat n)

iter-one : ∀ n → R.iter (suc zero +_) (suc zero) n ≡ nat (suc n)
iter-one zero = refl
iter-one (suc n) = trans (cong (suc zero +_) (iter-one n)) (one+nat (suc n))

nat-value : ∀ n → FV.val W.one (nat n) ≡ FV.natV {W.one} n
nat-value zero = refl
nat-value (suc n) = cong V.suc (nat-value n)

next-one-value : FV.val W.one (proj₁ (W.next⁺ β)) V.≈ V.lim (λ n → FV.natV {W.one} (suc n))
next-one-value = V.l≈ (λ n → subst (λ x → FV.val W.one x V.≈ FV.natV {W.one} (suc n))
  (Relation.Binary.PropositionalEquality.sym (iter-one n))
  (subst (λ x → x V.≈ FV.natV {W.one} (suc n))
    (Relation.Binary.PropositionalEquality.sym (nat-value (suc n))) (V.≈-refl _)))

closed-top₁-value : FV.val W.one (proj₁ (C.φ (O.tw 1) β (embed (O.tw 1) (proj₁ (R.Ωt (O.tw 1))))))
  V.≈ V.lim (λ n → FV.natV {W.one} (suc n))
closed-top₁-value = V.Ω≼ (λ _ → proj₁ next-one-value) , V.≼Ω O.zero (proj₂ next-one-value)

root : O.Pos (O.tw 1)
root = inj₁ (inj₁ tt)

g : O.Tr O.zero → O.Tr (O.tw 1)
g O.zero = O.zero
g (O.suc _) = O.suc O.zero
g (O.lim _ _) = O.suc O.zero

small : O.Tr (O.tw 1)
small = O.Ω root g

out : T (Sig W.one)
out = proj₁ (C.φ (O.tw 1) β (embed (O.tw 1) small))

out-legal : Lt (Sig W.one) zero out
out-legal = C.legal (O.tw 1) β (embed (O.tw 1) small)

out-shape : out ≡ Ω q (λ _ → suc zero)
out-shape = refl

out-value : FV.val W.one out V.≈ V.suc (V.zero {O.zero})
out-value = V.Ω≼ (λ _ → V.s≼s V.z≼) , V.≼Ω O.zero (V.s≼s V.z≼)

main : O.Tr O.zero
main = proj₁ (MT.ψ₀ᶻ (O.tw 1) (P.Ok-tw 1) small)

main-two : V.suc (V.suc (V.zero {O.zero})) V.≼ V.val O.zero main
main-two = V.≼l 1 (V.≼l 0 (V.s≼s (V.s≼s V.z≼)))

out≤main : FV.val W.one out V.≼ V.val O.zero main
out≤main = V.≼-trans (proj₁ out-value) (V.≼l 0 (V.s≼s V.z≼))

two-not-one : V.suc (V.suc (V.zero {O.zero})) V.≼ V.suc (V.zero {O.zero}) → ⊥
two-not-one (V.s≼s ())

main≰out : V.val O.zero main V.≼ FV.val W.one out → ⊥
main≰out d = two-not-one (V.≼-trans main-two (V.≼-trans d (proj₁ out-value)))
```
