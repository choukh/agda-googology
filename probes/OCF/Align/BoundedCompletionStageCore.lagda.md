# EBO第二站的实际整族值验收目标

验收专用，读取已有记号标签。第二站的目标为ψ₀(Ω_{Ω₁})；它的参照
使用已编译的NoCumsum.BTBOᴵ，而不是重新从良基证据展开大树。
整族为其真实基本列γ(n+1)，首项就是本轮已校准的ε₀。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageCore where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase using (Cd; hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
import OCF.Align.Level as L
import OCF.Align.EBO as E
import OCF.Align.NoCumsum as N
import OCF.Align.Label as Labels
import OCF.Align.Correspond as Correspond
import OCF.Align.OCFSpecBase as S
import OCF.Align.Value as V
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableBridge as B

family : ℕ → Cd
family n = B.forget (N.γ (suc n))
reference : Cd
reference = hl family

stage-term : E.EBOψ 2 ≡ E.ψ [] (E.Ωt (E.Ωt (E.natT 1))) ∷ []
stage-term = refl
reference-shape : reference ≡ B.forget N.BTBOᴵ
reference-shape = refl
family-label : ∀ n → Correspond.Lab (B.read (family n)) (Correspond.γᴱ (suc n))
family-label n = Correspond.Lab-≅ (B.reference-roundtrip (N.γ (suc n))) (Labels.γ-label n)
reference-label : Correspond.Lab (B.read reference) (E.EBOψ 2)
reference-label = Correspond.Lab-≅ (B.reference-roundtrip N.BTBOᴵ) Labels.BTBO-label

family≤reference : ∀ n → family n ≤ᵛ reference
family≤reference n = ≤l n (≤-refl _)
family-cover : ∀ {candidate : Cd} → (∀ n → family n ≤ᵛ candidate) → reference ≤ᵛ candidate
family-cover h = l≤ h
family-necessary : ∀ {candidate : Cd} → reference ≤ᵛ candidate → ∀ n → family n ≤ᵛ candidate
family-necessary p n = ≤-trans (family≤reference n) p

lower-sound : ∀ {candidate : Cd} → reference ≤ᵛ candidate → N.BTBOᴵ V.≼ B.read candidate
lower-sound p = Order.forward (B.reference-lower p)
lower-reflect : ∀ {candidate : Cd} → N.BTBOᴵ V.≼ B.read candidate → reference ≤ᵛ candidate
lower-reflect p = B.reference-lower-reflect (Order.backward p)

-- 全族在其真实上确界中逐项取得位置。
reference-covers-family : ∀ n → family n ≤ᵛ reference
reference-covers-family = family≤reference
```

这里只承载带标签的真实整族及第二站值判据，不导入候选C，以免WfFsn
实际参照连接同时加载整个构造闭包。首项与C的实际连接见StageFamily。
