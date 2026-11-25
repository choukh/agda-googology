# YiXV：实际层号 2 链的上界合成
> 验收文件。编译定理 `Chain.upper₂`：对已实填的第 1 层回灌底，链及其部分和不高于参照 `ψ₀(Ω₂)`。
> 参数为该实际底的模拟及字面起点证据；规范实例见 `YiXVTwo`。不是任意层号的上界。
> 源行复用 `YiXVSelf`，参照增长用 `YiOverOps`、`YiOverTwo`，合成用 `YiCeilRead.limc≼lim`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVChain2 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read)
open import OCF.Lean.YiCeilRead using (ωx; next≼; limc≼lim)
open import OCF.Lean.YiXVStart using (B2; pre)
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVCarry as K
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVSelf as F
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
open import OCF.Lean.YiOverTwo using (Gd-γ; Inv-γ)
open import OCF.Align.YiLvValBase using (γ; ⟨_⟩)

module Chain (B : Base (suc zero)) (β : Tr (suc zero)) (nβ : suc zero ⊢ zero ◃ β)
  (seed : S.Sim.U B β (O.ψ₁ (O.Ω₁ L.+ O.Ω₁))) (seedC : H.Anchor.Closed B seed)
  (zeroU : S.Sim.U B zero O.Ω₁) (zeroC : H.Anchor.Closed B zeroU) where
  module A = S.Sim B
  module HC = H.Anchor B
  module Self = F.Fold B O.Ω₁ O.Gd-Ω β nβ seed seedC

  Γ : ℕ → R.T₁
  Γ = γ 1

  Ω≤Γ : (n : ℕ) → O.Ω₁ R.≤ₚ Γ n
  Ω≤Γ zero = O.Ω≤Ω
  Ω≤Γ (suc n) = R.trans (Ω≤Γ n) (O.≤ψ₁ (Gd-γ n) (Inv-γ n))

  jump : (n : ℕ) → O.ψ₁ (O.Ω₁ L.+ L.suc (Γ n)) R.≤ₚ Γ (suc (suc (suc n)))
  jump n = O.ψ₁-mono (R.trans (O.+ₚ (Ω≤Γ n) (Inv-γ n)) (O.step-γ (Gd-γ n) (Inv-γ n) (O.reflₚ (Gd-γ n))))

  ix : ℕ → ℕ
  ix zero = zero
  ix (suc n) = suc (suc (suc (ix n)))

  c : ℕ → Tr (suc zero)
  c = iter (λ x → Self.χ (suc x)) zero

  Bounds : (n : ℕ) → Set
  Bounds n = Σ (A.U (c n) (Γ (ix n))) HC.Closed

  bounds : (n : ℕ) → Bounds n
  bounds zero = zeroU , zeroC
  bounds (suc n) =
    A.uw (O.Gd-ψ₁ (O.Gd-+ O.Gd-Ω (O.gs (Gd-γ (ix n)))))
      (proj₁ (Self.result {x = suc (c n)} {X = L.suc (Γ (ix n))} (O.gs (Gd-γ (ix n))) (A.us {x = c n} {X = Γ (ix n)} (proj₁ (bounds n))) (proj₂ (bounds n))))
      (jump (ix n)) ,
    proj₂ (Self.result {x = suc (c n)} {X = L.suc (Γ (ix n))} (O.gs (Gd-γ (ix n))) (A.us {x = c n} {X = Γ (ix n)} (proj₁ (bounds n))) (proj₂ (bounds n)))

  rows : ℕ → Tr zero
  rows n = ψ⊥ (suc zero) tt tt B (suc (c n))

  row-bound : (n : ℕ) → read (rows n) ≼ L.ψ⁰ (Γ (suc (ix n)))
  row-bound n = ≼-trans
    (next≼ (ψ⊥ (suc zero) tt tt B (c n)) (nz⊥ (suc zero) tt tt B (c n))
      (proj₁ (A.upper {x = c n} {X = Γ (ix n)} (Gd-γ (ix n)) (proj₁ (bounds n)))))
    (R.mono⁰ (Inv-γ (ix n)))

  ref-step : (n : ℕ) → L.ψ⁰ (Γ n) ≼ L.ψ⁰ (Γ (suc n))
  ref-step n = R.mono⁰ (O.≤ψ₁ (Gd-γ n) (Inv-γ n))

  Gr : ℕ → T₀
  Gr n = L.ψ⁰ (Γ (suc (ix n)))

  Gr-mono : (n : ℕ) → Gr n ≼ Gr (suc n)
  Gr-mono n = ≼-trans (ref-step (suc (ix n)))
    (≼-trans (ref-step (suc (suc (ix n)))) (ref-step (suc (suc (suc (ix n))))))

  Gr-abs : (n : ℕ) → ωx (Gr n) ≼ Gr (suc n)
  Gr-abs n = ≼-trans (R.mono⁰ (Inv-γ (suc (ix n))))
    (≼-trans (ref-step (suc (suc (ix n)))) (ref-step (suc (suc (suc (ix n))))))

  ceiling : read (limc rows (λ n → nz⊥ (suc zero) tt tt B (suc (c n)))) ≼ L.lim Gr
  ceiling = limc≼lim rows (λ n → nz⊥ (suc zero) tt tt B (suc (c n))) Gr row-bound Gr-mono Gr-abs

  upper₂ : read (limc rows (λ n → nz⊥ (suc zero) tt tt B (suc (c n)))) ≼ L.ψ⁰ (L.Ω ⟨ 2 ⟩)
  upper₂ = ≼-trans ceiling (l≼ (λ n → ≼l (suc (ix n)) (≼-refl (Gr n))))
```
