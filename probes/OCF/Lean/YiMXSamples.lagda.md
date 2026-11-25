# 非相邻层的单项反例
> 验收文件（读记号），编译定理：A = ψ₀(ψ₁(Ω₃)) 有 HC，项序低于 N = ψ₀(Ω₂)，但 N 的后继值不高于 A。
> pathA 的十七次基本列取支给值下界；不是对任意层号的定理，也不改树、折叠或合法性。
> 来源：HC 使用 YiDCCheck.Two 的闭合两次折叠；fromOld 照 YiNXFull.fromM 改为旧基础关系；值工具复用 YiRefTw2。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXSamples where
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω; cof; cω; fsn; _<ᵀ_; hd<; ar<; lv<; tl<; []<)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiANEnd using (nat<)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s)
open import OCF.Lean.YiRefTw2 using (Rt; fs≼; hω-inv; tree-≼)
open import OCF.Lean.YiNXNote using (W; N; hW; hN; nfN; N≼W; W≼N)
open import OCF.Lean.YiNFO using (s≼-irrefl)
import OCF.Align.Level as L
import OCF.Lean.YiMEBase as Old
import OCF.Lean.YiDCCheck as DC
fromOld : ∀ {t x} → Old.M⁰ t x → HC t
fromOld Old.mz = h0 refl
fromOld (Old.m1 e m) = h1 e (fromOld m)
fromOld (Old.mL e f) = hω e (λ n → fromOld (f n))
fromOld (Old.mΩ {p = ()} _ _ _)
fromOld (Old.mU {c = ()} _ _)
fromOld (Old.mw m _) = fromOld m
module Two = DC.Two tt tt tt tt
opaque
  hA : HC (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))
  hA = fromOld Two.wit₂
A<N : ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)) <ᵀ N 1
A<N = hd< (ar< (hd< (lv< (nat< 1))))
N≼A : Rt (hN 1) ≼ Rt hA
N≼A = ≼-trans (N≼W 1 (hN 1) (hW 1))
  (≼-trans (tree-≼ refl (hW 1) (hω-inv hA refl 0)) (fs≼ hA refl 0))

trace : List ℕ → OCF.Align.EboLeanDef.T → OCF.Align.EboLeanDef.T
trace [] t = t
trace (n ∷ ns) t = trace ns (fsn t n)

Allω : List ℕ → OCF.Align.EboLeanDef.T → Set
Allω [] t = ⊤
Allω (n ∷ ns) t = (cof t ≡ cω) × Allω ns (fsn t n)

walk : ∀ ns {t} → Allω ns t → HC t → HC (trace ns t)
walk [] e h = h
walk (n ∷ ns) (e , es) h = walk ns es (hω-inv h e n)

walk≼ : ∀ ns {t} (e : Allω ns t) (h : HC t) → Rt (walk ns e h) ≼ Rt h
walk≼ [] e h = tree-≼ refl h h
walk≼ (n ∷ ns) (e , es) h = ≼-trans (walk≼ ns es (hω-inv h e n)) (fs≼ h e n)

pathA : List ℕ
pathA = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ []

pathA-ω : Allω pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))
pathA-ω = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt

lastA : trace pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) ≡ (OCF.Align.EboLeanDef.ψ [] (ψᴺ 1 (Ωᴺ 2)) ∷ OCF.Align.EboLeanDef.𝟏 ∷ [])
lastA = refl

N≺A : L.suc (Rt (hN 1)) ≼ Rt hA
N≺A = ≼-trans (s≼s (N≼W 1 (hN 1) (hW 1)))
  (≼-trans (tree-≼ (sym lastA) (h1 refl (hW 1)) (walk pathA pathA-ω hA))
    (walk≼ pathA pathA-ω hA))

¬A≼N : Rt hA ≼ Rt (hN 1) → ⊥
¬A≼N q = s≼-irrefl (Rt (hN 1)) (≼-trans N≺A q)
```
