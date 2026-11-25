# 实际第 1 槽位点上的零层输出界
不读记号；编译定理 `out11`：n=1、q=1 的实际零层输出不高于该槽位点。
证明只使用实际第 1 点的两个保留 Ω 分支及继承底的正值；辅助算术通过 `YiVWVal.val-+`。
未证明第 1→2 点的值增长，不给出 `Nslot`、`Tail` 或新增强度；重建对象对接见 `YiSLCheck`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSLOut where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ; mono)
open import OCF.Lean.YiMTTab using (rbᶻ)
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiSLStart as S

private
  k = tw 1
  β = S.baseᴱ 2 k (ink self)

  a0 : Λ ⊢ zero ◃ S.FΛ 0
  a0 = proj₂ (upz {s = sL} {h = tw} 0 (Ωt (tw 0)))
  a1 : Λ ⊢ zero ◃ S.FΛ 1
  a1 = proj₂ (upz {s = sL} {h = tw} 1 (Ωt (tw 1)))
  pre2nz : Λ ⊢ zero ◃ S.pre 2
  pre2nz = ◃t a0 (+-mono (S.FΛ 0) a1)

  positiveβ : V.suc (V.zero {k}) V.≼ V.val k (proj₁ β)
  positiveβ = V.≼-trans (V.≼Ω zero (V.s≼s V.z≼))
    (V.◁→≼ (V.val-mono k
      (mono Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) k (inc 2 (ink self)) (Ωt k) pre2nz)))

  -- 仅为实际分支里的零层 Up 递归给出算术接线；不陈述折叠保持律。
  next-suc : ∀ {j} (b : Tr⁺ j) → V.suc (V.zero {j}) V.≼ V.val j (proj₁ b)
    → V.suc (V.val j (proj₁ b)) V.≼ V.val j (proj₁ (next⁺ b))
  next-suc b pos = V.≼l 1
    (V.≼-trans (V.⊹-mono (V.val _ (proj₁ b)) pos)
      (proj₂ (V.val-+ (proj₁ b) (proj₁ b))))

  d : Dn k zero
  d = down (down stop (suc zero)) tt

  U : Tr zero → Tr⁺ k
  U y = Up zero d β y

  U-base : (y : Tr zero) → V.val k (proj₁ β) V.≼ V.val k (proj₁ (U y))
  U-base y with zl y
  ... | inj₁ refl = V.≼-refl _
  ... | inj₂ e = V.◁→≼ (V.val-mono k (Upm zero d β e))

  U-grow : (y : Tr zero) → V.val zero y V.≼ V.val k (proj₁ (U y))
  U-grow zero = V.z≼
  U-grow (suc y) = V.≼-trans (V.s≼s (U-grow y))
    (next-suc (U y) (V.≼-trans positiveβ (U-base y)))
  U-grow (lim f a) = V.l≼ (λ n → V.≼l n (U-grow (f n)))

  under-c1 : (y : Tr zero) → V.val zero y V.≼ V.val k (S.Step.chain 1 1)
  under-c1 y = V.≼Ω (suc zero) (V.≼Ω y
    (V.≼-trans (V.≼-suc (U-grow y)) (next-suc (U y) (V.≼-trans positiveβ (U-base y)))))

out11 : V.val zero (proj₁ (S.Step.out 1 (S.Step.chain 1 1))) V.≼ V.val (tw 1) (S.Step.chain 1 1)
out11 = under-c1 (proj₁ (S.Step.out 1 (S.Step.chain 1 1)))
```
