# 全域单调的最小反例与配对检查
> 验收文件（读记号），编译定理：项序有 1 + ω + 1 <ᵀ ω，两端有 HC、Ctbl，但参照值不满足该方向的 ≼。
> ¬Mono 否定共用陈述；W k 与 N k 的双向值比较及非相邻的 W 0、W 2 给肯定侧检查。
> 来源：复用 YiNXNote、YiCFMono、YiRefTw2 与 YiNFO.s≼-irrefl；不改树、折叠、合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXNote where
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-asym)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiNXNote using (W; N; hW; hN; nfN; W<N; W≼N; N≼W)
open import OCF.Lean.YiMXIface using (Mono)
forward : ∀ k → W k ≤ᵀ N k
forward k = inj₁ (W<N k)
reverse-impossible : ∀ k → N k ≤ᵀ W k → ⊥
reverse-impossible k (inj₁ p) = <ᵀ-asym (W<N k) p
reverse-impossible k (inj₂ ())
small-forward : Rt (hW 1) ≼ Rt (hN 1)
small-forward = W≼N 1 (hW 1) (hN 1)
small-backward : Rt (hN 1) ≼ Rt (hW 1)
small-backward = N≼W 1 (hN 1) (hW 1)

open import Data.Nat using (suc)
open import Data.Nat.Properties using (n≤1+n)
open import OCF.Lean.YiCFMono using (mono≤ⁿ; mono<ⁿ)
open import OCF.Lean.YiDCRel using (nat≤)
open import Data.List using ([]; _∷_)
open import OCF.Align.EboLeanDef using (T; ψ; 𝟏; natT; fsn; h1; hω; _<ᵀ_; hd<; ar<; []<)
open import OCF.Align.EboLeanBase using (NF; Ctbl; c∷; c[]; nf-ψ; n[])
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiANEnd using (natB; flatN)
open import OCF.Lean.YiNFOCase using (flatGB)
open import OCF.Lean.YiMHLean using (ctN)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiRefTw2 using (tree-≼)
open import OCF.Align.Value using (s≼s; z≼; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiNFO using (s≼-irrefl)
import OCF.Align.Level as L
bad pre : T
pre = 𝟏 ∷ ψ [] (natT 1) ∷ []
bad = 𝟏 ∷ ψ [] (natT 1) ∷ 𝟏 ∷ []
hnat : ∀ n → HC (natT n)
hnat n = hc (natB n) (ctN n)
hpre : HC pre
hpre = hω refl (λ n → subst HC (sym (cong (𝟏 ∷_) (rep1 n))) (hnat (suc n)))
hbad : HC bad
hbad = h1 refl hpre
hωt : HC ωᵀ
hωt = hω refl (λ n → subst HC (sym (rep1 n)) (hnat n))
bad<ω : bad <ᵀ ωᵀ
bad<ω = hd< (ar< []<)
ω≼pre : Rt hωt ≼ Rt hpre
ω≼pre = l≼ (λ n → ≼l n
  (≼-trans (tree-≼ (rep1 n) _ (hnat n))
    (≼-trans (mono≤ⁿ (natB n) (natB (suc n)) (ctN (suc n)) (hnat n) (hnat (suc n)) (nat≤ (n≤1+n n)))
      (tree-≼ (sym (cong (𝟏 ∷_) (rep1 n))) (hnat (suc n)) _))))

¬Mono : Mono → ⊥
¬Mono m = s≼-irrefl (Rt hωt) (≼-trans (s≼s ω≼pre) (m (inj₁ bad<ω) hbad hωt))

ct-bad : Ctbl bad
ct-bad = c∷ (c∷ (c∷ c[]))

ct-ω : Ctbl ωᵀ
ct-ω = c∷ c[]

bad-value : Rt hbad ≼ Rt hωt → ⊥
bad-value q = s≼-irrefl (Rt hωt) (≼-trans (s≼s ω≼pre) q)

nf-ω : NF ωᵀ
nf-ω = nf-ψ n[] (natB 1) (flatGB (flatN 1))

¬nf-bad : NF bad → ⊥
¬nf-bad ns = bad-value (mono≤ⁿ ns nf-ω ct-ω hbad hωt (inj₁ bad<ω))

N0<N2 : N 0 OCF.Align.EboLeanDef.<ᵀ N 2
N0<N2 = hd< (ar< (hd< (OCF.Align.EboLeanDef.lv< (OCF.Align.EboLeanDef.tl< []<))))

W0<W2 : W 0 OCF.Align.EboLeanDef.<ᵀ W 2
W0<W2 = hd< (ar< (hd< (OCF.Align.EboLeanDef.lv< []<)))

W0≼W2 : Rt (hW 0) ≼ Rt (hW 2)
W0≼W2 = ≼-trans (W≼N 0 (hW 0) (hN 0))
  (≼-trans (mono≤ⁿ (nfN 0) (nfN 2) (c∷ c[]) (hN 0) (hN 2) (inj₁ N0<N2))
    (N≼W 2 (hN 2) (hW 2)))

¬W2≼W0 : Rt (hW 2) ≼ Rt (hW 0) → ⊥
¬W2≼W0 q = s≼-irrefl (Rt (hN 0))
  (≼-trans (mono<ⁿ (nfN 0) (nfN 2) (c∷ c[]) (hN 0) (hN 2) N0<N2)
    (≼-trans (N≼W 2 (hN 2) (hW 2)) (≼-trans q (W≼N 0 (hW 0) (hN 0)))))
```
