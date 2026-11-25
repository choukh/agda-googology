# YiVmCon：BTBO 下界约化到链点落在定义域 `≼ᵖ` 里

**验收文件，档位：条件定理与编译定理。** `btbo-p : ChainP → D.BTBOᴵ ≼ read T₃ᵐ`，前提 `ChainP` 是 "第 n 个参照项 `D.γ n` 与第 n 个链点的读回之间有 `≼ᵖ` 推导"；不需要 `VMᴸ` 或 `MonoT`。
`ChainP` 在 n = 0 是定理 (`chainP₀`)；n ≥ 1 未证。参照的对角链自身相邻两项在 `≼ˣ` 里 (`diag-in`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmConChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (proj₂)
import OCF.Align.RR5IrrCore as B
open B using (Lgl)
open import OCF.Align.YiIrrIf using (R; read0; read0-legal)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ; Ptᵐ; pointsᵐ; foldᵐ₃; rplain)
open Ptᵐ using (coordᵐ; lawfulᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiBtValAdm using (toIL-c)
open import OCF.Align.YiBtValFin using (lower-any)
open import OCF.Align.YiBtValBT using (module D; ZsL; ZsL→; inv)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-trans; ≅→≼)
open import OCF.Align.YiMonoVM using (HS-read; lvl≅)
open import OCF.Align.YiVmConExact using (_≼ᵖ_; _≼ˣ_; VMᵖ; ˣ→ᵖ; reflˣ; ⊑→≼ˣ)
```

`monoᵖ` 与 `YiMonoVM.vm→monoᶻ` 同形，只把 `VMᴸ` 换成定义域上的 `VMᵖ`。

```agda
monoᵖ : ∀ (x : L.Ordᶜ L.zero) (h : L.HS x) (a : R) (l : Lgl B.zero a) → ZsL (read0 a) → x ≼ᵖ read a →
  L.ψ⁰ (L.Ω (L.toLevel x h)) ≼ read (foldᵐ₃ a l)
monoᵖ x h a l z le =
  ≼-trans (VMᵖ x h (read a) (HS-read a l) le)
  (≼-trans (≅→≼ (L.ψ⁰-≅ (L.Ω-≅ (lvl≅ a (HS-read a l) (rplain a) (read0-legal a l)))))
    (lower-any (read0 a) (rplain a) (read0-legal a l) (toIL-c (read0 a) (rplain a) (read0-legal a l))
      (ZsL→ (read0 a) (rplain a) (read0-legal a l) z)))

ChainP : Set
ChainP = ∀ n → D.γ n ≼ᵖ read (coordᵐ (pointsᵐ n))

btbo-p : ChainP → D.BTBOᴵ ≼ read T₃ᵐ
btbo-p c = l≼ (λ n → ≼l n
  (monoᵖ (D.γ n) (D.cert n) (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n)) (proj₂ (inv n)) (c n)))

chainP₀ : D.γ 0 ≼ᵖ read (coordᵐ (pointsᵐ 0))
chainP₀ = ˣ→ᵖ (reflˣ (D.γ 0))

diag-in : ∀ n → D.γ n ≼ˣ D.γ (suc n)
diag-in n = ⊑→≼ˣ (D.γ n) (D.diag-step n)
```
