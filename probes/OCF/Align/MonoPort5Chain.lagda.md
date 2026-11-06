# 第三站 (六): 外层链, `MonoStep 3`, $T_3<T_4$

> 不含记号. 入口 [MonoPort5](MonoPort5.lagda.md). 世界 $1$. `MonoStep (hs Λ)` 取 $\Lambda=2$ 时在实例 `At (hs 2)` (即实例 3) 里, 字面是两条链的极限的比较 (`MonoPortStep.step≡`), 链点是第 2 层的差树, 动作 `StepA` 只看状态. 外层链就是 [MonoPort5Chn](MonoPort5Chn.lagda.md) 的 `chainG` 取第 2 层、`Pt` = $\sqsubseteq_2$、一步用 `snd₂`.
>
> - `HA-Step`: `StepA` 在三个目标上都是 $\mathrm{nl}(\lambda\_.\,\Omega_e⨾\delta)$, 对 $\delta$ 结构单调 (要 $\Omega_1$, $\Omega_2$ 自比).
> - 起点: 两个状态 $Y^L\sqsubseteq Y^R$ 由单位律与 `n0 ⊑ z` 给出, 底 $b^L\le b^R$ 由 `val₀`.
> - **`mono₃ : MonoStep 3`**, **`grow₃₄ : asuc (TΛ 3) ≤ TΛ 4`**: 无前提, 不用 `Funext`, 不经规范形, 不用左边极限截断. `grow₀₄ : TΛ 0 + 4 ≤ TΛ 4` 拼上已有的 `MonoPortOne.grow₀₁₂` (高度 0 到 2, 那里用规范形) 与 `StrRelChain.grow₂₃ˢ`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort5Chain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D; Ωd; hz; hs; hself; ss; n0; n1; _⨾_; nl; ni; sum; sum-fst)
open import OCF.Align.HtFeedClosed using (one; TΛ)
open import OCF.Align.HtCrossInst using (module Hs; b₀)
import OCF.Align.MonoPortStep as St
import OCF.Align.HtCrossVInst as CV
import OCF.Align.StrRelChain as SC
import OCF.Align.MonoPortOne as One
open import OCF.Align.StrRelDef {one} tt using (val₀)
open import OCF.Align.MonoPort5Rel {one} tt
open import OCF.Align.MonoPort5Two {one} tt using (module C2; module K2; cl₂; snd₂)
open OutLaws O₃ using (L0; L⨾; Ltr; Lu1ʳ)

module Kc = St.Ch L2 tt
```

## §1 动作

```agda
rΩ₁ : Rf₁ (Ωd L1 {one})
rΩ₁ = R1.⨾⊑ R1.n1⊑ R1.n1⊑ R1.n1⊑ (R1.ni⊑ (ss hself) (λ _ _ _ → R1.n1⊑) (λ _ _ _ → R1.n1⊑) (λ _ _ _ → R1.n1⊑))

rΩ₂ : Rf₂ (Ωd L2 {one})
rΩ₂ = R2.⨾⊑ R2.n1⊑ R2.n1⊑ R2.n1⊑ (R2.ni⊑ (ss hself) (λ _ _ _ → R2.n1⊑) (λ _ _ _ → R2.n1⊑) (λ _ _ _ → R2.n1⊑))

StepA : K2.Act
StepA = Kc.StepA

HA-Step : K2.HA StepA StepA
HA-Step w w′ c c′ Y Y′ _ g g′ s cb =
  val₀ r₀ cb ,
  (r₀ ,
   (R1.nl⊑ (λ _ → R1.⨾⊑ rΩ₁ rΩ₁ rΩ₁ (proj₁ (proj₂ g))) (λ _ → R1.⨾⊑ rΩ₁ rΩ₁ rΩ₁ (proj₁ (proj₂ g′)))
           (λ _ → R1.⨾⊑ rΩ₁ rΩ₁ rΩ₁ (proj₁ (proj₂ (proj₂ s)))) ,
    R2.nl⊑ (λ _ → R2.⨾⊑ rΩ₂ rΩ₂ rΩ₂ (proj₂ (proj₂ g))) (λ _ → R2.⨾⊑ rΩ₂ rΩ₂ rΩ₂ (proj₂ (proj₂ g′)))
           (λ _ → R2.⨾⊑ rΩ₂ rΩ₂ rΩ₂ (proj₂ (proj₂ (proj₂ s))))))
  where
  r₀ = lm (λ _ → sq o1 (proj₁ (proj₂ s)))
```

## §2 外层链与起点

```agda
module CH2 = C2.Chain cl₂ _⊑₂_ snd₂ (λ h → proj₂ (proj₂ h)) (K2.cx tt) (λ _ _ _ _ → K2.cx tt) StepA StepA HA-Step HA-Step HA-Step

g0 : K2.Good P.Y₀
g0 = L0

rS : ∀ Y → K2.Good Y → P.Step Y ≼ P.Step Y
rS Y g = proj₂ (HA-Step n0 n0 azero azero Y Y (K2.cx tt) g g (K2.sr {Y} g) z≤)

gL : K2.Good Kc.Yᴸ
gL = K2.G⊕ {P.Y₀} {P.Step P.Y₀} g0 (rS P.Y₀ g0)

gR₀ : K2.Good Kc.Yʳ₀
gR₀ = K2.G⊕ {Kc.Yᴸ} {P.zeroD} gL L0

gR : K2.Good Kc.Yʳ
gR = K2.G⊕ {Kc.Yʳ₀} {P.Step Kc.Yʳ₀} gR₀ (rS Kc.Yʳ₀ gR₀)

-- 两个起点: x ≼ (x ⨾ 0) ⨾ y, 只用单位律与 0 ≼ y
sLR : K2.SRel Kc.Yᴸ Kc.Yʳ
sLR = val₀ (proj₁ r) (≤-refl azero) , r
  where
  r = Ltr (Lu1ʳ (Lu1ʳ gL)) (L⨾ gR₀ gR₀ gR₀ L0)

hb : Kc.bᴸ ≤ Kc.bʳ
hb = val₀ (proj₁ (proj₂ (HA-Step n0 n0 azero azero P.Y₀ Kc.Yʳ₀ (K2.cx tt) g0 gR₀ (z≤ , L0) z≤))) (⊲→≤ (sum-fst one (nl (λ _ → n1 ⨾ n0))))
```

## §3 定理

```agda
chainLe : Kc.ChainLe
chainLe = proj₁ (CH2.chainG Kc.Yᴸ Kc.Yʳ Kc.bᴸ Kc.bʳ gL gR sLR hb)

mono₃ : Hs.MonoStep (hs (hs (hs hz))) tt
mono₃ = subst (λ X → X) (sym Kc.step≡) chainLe

grow₃₄ : asuc (TΛ (hs (hs (hs hz))) tt) ≤ TΛ (hs (hs (hs (hs hz)))) tt
grow₃₄ = CV.HsS.hs-reduce<′ (hs (hs (hs hz))) tt tt mono₃

grow₀₄ : asuc (asuc (asuc (asuc (TΛ hz tt)))) ≤ TΛ (hs (hs (hs (hs hz)))) tt
grow₀₄ = ≤-trans (s≤ (≤-trans (s≤ One.grow₀₁₂) SC.grow₂₃ˢ)) grow₃₄
```
