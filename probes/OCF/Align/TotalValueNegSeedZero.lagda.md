# 原闭包种子的实际第零支覆盖低零行

只展开参数一的原 Ωd 第零支；该分支的链起点仍为低层 Ω̇ 的零参数。
随后只调用已证 D-val 的零参数结论，不声称非零移位可以普遍删除。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueNegSeedZero (S : HtB) where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Eq using (toZ-≅)
open import OCF.Free.Floor using (Ev; flo; fz)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.ValLabLadder S using (Ωd; D-val; e₀; ev₀)
open import OCF.Align.TotalValueTailCongruence using (read-run-cong)
open import OCF.Align.ValueJudgeBase
import OCF.Align.TotalValueBuildHighChain S as H
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

seed-zero : ∀ {n m w ℓ} (r : n <ᴸ m) (ok : Ok w)
  (env : Eh h₀ m w (cap (κ Fl) n (flo (suc zero))))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) →
  H.value n ≼ A.read (R.run (toZ (ψ̄ᵠ ok env (Ωd r (suc zero)) ev p)))
seed-zero {n} {m} r ok env ev p = ≼l zero first-proof
  where
  head : Z → Z
  head (Z.lim f) = f zero
  head _ = Z.zero

  first-proof : H.value n ≼ A.read (R.run
    (head (toZ (ψ̄ᵠ ok env (Ωd r (suc zero)) ev p))))
  first-proof
    rewrite out-intoV r (qwk {χ′ = Z* (cap (κ Fl) n (flo (suc zero)))} (λ e → e) fc* (Ω̇ n zero)) =
    ≅→≼ (read-run-cong (toZ-≅ (D-val r ok _ ev₀ zero ev p z≅)))
```
