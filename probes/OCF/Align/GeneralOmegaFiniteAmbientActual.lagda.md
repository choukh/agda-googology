# 全有限原地板的具名值验收与γ₂首回调

验收专用。统一保持律现在实填全部原floor n和zero-path n。
没有阶段专属动作，也不将全n命题换成第二站。闭项、合法性和FGH
仍是冻结的FiniteObserveClosed，记号只进入本篇证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteAmbientActual where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Lean.GeneralOmegaFiniteObserveClosed as C
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.GeneralOmegaGammaCoverFinite as F
import OCF.Align.GeneralOmegaGammaActual as G
open import OCF.Align.GeneralOmegaFiniteRank using (nat; ambient)
open import OCF.Align.GeneralOmegaFiniteAmbientIf
open import OCF.Align.GeneralOmegaFiniteAmbientRun using (preserve)

zero-sound : ∀ {ℓ} {σ : L.Simᴵ ℓ (nat 1)} {a b} → Read zero σ a b → a L.≅ B.read b
zero-sound rz = L.z≅
zero-sound (rs p) = L.s≅ (zero-sound p)
zero-sound (rl p) = L.l≅ (λ n → zero-sound (p n))
zero-sound (ro () q e sa p)
zero-sound (ru-s p) = L.upˡ (zero-sound p)
zero-sound (ru-l p) = L.upˡ (zero-sound p)
zero-sound (rc e p) = L.≅-trans e (zero-sound p)

stage-sound : ∀ n → L.ψ⁰ (L.Ω (nat n)) L.≅ B.read (C.stage n)
stage-sound n = L.≅-trans
  (L.ψ⁰≅ψ {p = ambient (C.zero-path n)} {σ = canonical n} (L.Ω-refl (nat n)))
  (zero-sound (preserve (C.zero-path n) (floor-read n)))

levels-agree : ∀ n → nat n ≡ F.nat-level n
levels-agree zero = refl
levels-agree (suc n) = cong L.suc (levels-agree n)
reference-equal : ∀ n → B.forget (L.ψ⁰ (L.Ω (nat n))) ≡ F.finite n
reference-equal n = cong (λ x → B.forget (L.ψ⁰ (L.Ω x))) (levels-agree n)

reference≤stage : ∀ n → F.finite n ≤ᵛ C.stage n
reference≤stage n = subst (λ a → a ≤ᵛ C.stage n) (reference-equal n)
  (B.reference-lower-reflect (V.≅→≼ (stage-sound n)))
stage≤reference : ∀ n → C.stage n ≤ᵛ F.finite n
stage≤reference n = subst (λ a → C.stage n ≤ᵛ a) (reference-equal n)
  (≤-trans (B.roundtrip≥ (C.stage n))
    (B.forget-mono (V.≅→≼ (L.≅-sym (stage-sound n)))))

first-callback≤raw : G.reference-branch zero ≤ᵛ C.raw
first-callback≤raw = ≤-trans F.first≤finite (l≤ (λ n → ≤l n (reference≤stage n)))
raw≤first-callback : C.raw ≤ᵛ G.reference-branch zero
raw≤first-callback = ≤-trans (l≤ (λ n → ≤l n (stage≤reference n))) F.finite≤first
first-callback≤tree : G.reference-branch zero ≤ᵛ C.tree
first-callback≤tree = ≤-trans first-callback≤raw C.raw-lower
```

已证每个原stage n与ψ₀(Ω_n)参照互相≤ᵛ；n=0的值为ω，未误作1。
原raw与γ₂首个完整回调（全部ψ₀(Ω_n)的极限）互相≤ᵛ，原合法tree
不低于该回调。尚未给tree的反向上界，也未覆盖γ₂其余回调，更未
覆盖完整EBO。旧全Ω消费者与此新有限候选之间仍无自动值比较。

翻译账：观察器规则受旧typed折叠启发；本轮证明没有反改树、
折叠或证书，但还不能称树自足。进展是对全部有限层和共同源界的
统一模拟，比较全部真实反馈，而不是按站定制支配。
