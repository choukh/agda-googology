# 实际局部降层不能直接传递高层值序

用已经运行且保有具体合法实例的 BoundedFoldClosed.F 构造反例。
两棵源树在同一 Safe 类型、同一字面源界中合法且有 ≤ᵛ；其降层结果
不保持该方向。否定的是无条件值单调，不是否定带路径或 Mo 的受限律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedDescentValueNoMono where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (T)
open import OCF.Lean.BoundedFoldRun using (chain)
import OCF.Lean.BoundedFoldClosed as C
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤Ω)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.BoundedFoldValueFeedback using (inflate)

upper : HB C.S
upper = hΩ (inj₂ tt , tt) C.j
lower-value : HB (T hz)
lower-value = C.F.fold hz (hsuc hself) upper
lower : HB C.S
lower = C.j (hs lower-value)

legal-upper : LgB upper
legal-upper =
  (λ lw b b′ p → C.j-position p) ,
  (λ lw b → C.j-legal _ (lgB⊲ b (proj₁ lw) (proj₂ lw)))
legal-chain : ∀ n → LgB (chain C.act n)
legal-chain zero = tt
legal-chain (suc n) = Lg-⊞ _ _ (legal-chain n) (C.act-legal _ (legal-chain n))
legal-lower-value : LgB lower-value
legal-lower-value = LegalSum.sum-legal (T hz) (λ n → C.act (chain C.act n))
  (λ n → C.act-legal _ (legal-chain n))
legal-lower : LgB lower
legal-lower = C.j-legal _ legal-lower-value

source-ordered : lower ≤ᵛ upper
source-ordered = ≤Ω (hs lower-value) (≤-refl lower)

not-descended-ordered : C.F.fold hz (hsuc hself) lower ≤ᵛ
  C.F.fold hz (hsuc hself) upper → ⊥
not-descended-ordered p = ¬s≤ᵛ lower-value (≤-trans (inflate (hs lower-value)) p)
```

反例的源值关系在右 Ω 规则使用坐标 hs lower-value；它没有相应当前世界的
可入证据。正是这项信息不能从裸 ≤ᵛ 或 LgB 恢复。故上一轮高 P 层的严格
下界不能仅凭“下一折叠合法”就传到 Cd；须给实际路径/有界值关系，或直接证明
该闭项的降层轨道比较。
