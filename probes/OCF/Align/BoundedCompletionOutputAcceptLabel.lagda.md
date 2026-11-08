# 双 Ω 参照的实际标签与成品下界

仅验收层使用记号。调用既有 Generic.lab，不为动态闭项添加标签证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputAcceptLabel where
open import Data.List using ([]; _∷_)
open import OCF.Lean.CRwBase using (hs)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Align.EBO as E
import OCF.Align.Level as L
import OCF.Align.Label as Labels
import OCF.Align.Correspond as Correspond
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionOutputAcceptPair as Value
import OCF.Align.BoundedCompletionValueAcceptPair as Actual
import OCF.Align.BoundedNativeCompletionClosed as C

S = Labels.St 0
module G = Labels.GS S
term : E.T
term = E.ψ [] (E.ψ (E.natT 1) [] ∷ E.ψ (E.natT 1) [] ∷ []) ∷ []
argument : G.𝔸 (E.ψ (E.natT 1) [] ∷ E.ψ (E.natT 1) [] ∷ [])
argument = G.a∷ (G.aψ (Labels.sγ 0) G.a[]) (G.a∷ (G.aψ (Labels.sγ 0) G.a[]) G.a[])
derivation : G.𝔸 term
derivation = G.a∷ (G.aψ (Labels.System.s0 S) argument) G.a[]

omega-agree : Value.Ω₁ L.≅ G.node (Labels.System.inA S (Labels.sγ 0)) L.zero
omega-agree = G.Ω-node (Labels.System.inA S (Labels.sγ 0)) (L.s≅ L.z≅)

reference-agree : Value.reference L.≅ G.⟦ derivation ⟧ᵃ
reference-agree = Labels.Tree.top‴ S (Labels.System.inA S (Labels.System.s0 S))
  (Labels.System.S0 S (Labels.System.s0 S))
  (L.add-≅ {σ = λ r → r} {σ′ = λ r → r} omega-agree omega-agree)

reference-label : Correspond.Lab Value.reference term
reference-label = G.lab Value.reference derivation reference-agree

strict-reference≤C : hs (B.forget Value.reference) ≤ᵛ C.tree
strict-reference≤C = ≤-trans Value.strict-reference≤pair Actual.pair≤C
```

带标签参照为 ψ₀(Ω₁+Ω₁)。已证其可数树后继不高于合法完成项 C；
这是具名下界，不是双 Ω 输出或 C 的精确值，也不是 ψ₀(Ω₂) 下界。

```agda
open import Data.Empty using (⊥)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

no-pair-upper-reference : Actual.pair-output ≤ᵛ B.forget Value.reference → ⊥
no-pair-upper-reference p = ¬s≤ᵛ (B.forget Value.reference)
  (≤-trans Value.strict-reference≤pair p)
```

因此不能把真实动态双 Ω 输出精确读成 ψ₀(Ω₁+Ω₁)：这一方向的上界
有编译否定。否定范围仅是该具体精确读法，不是否定更高的记号上界。
