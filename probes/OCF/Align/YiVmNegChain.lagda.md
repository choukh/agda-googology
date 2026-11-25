# YiVmNeg：链点上的子域

**验收文件，档位：编译定理与条件定理。** 供构造路用的子域陈述 `VMᶜʰ`：只在 BTBO 的对角链与旧树链点的读回 (同一下标 n) 上要 `VMᴸ`，前提仍是带数据的推导。`ch→btbo : VMᶜʰ → D.BTBOᴵ ≼ read T₃ᵐ` (条件定理)。
编译事实 `no-bound`：n ≥ 1 时，链上的值序成立的话，两边层号没有字面的公共上界；所以 `YiVmNegBound.bound-⊑` 在链上用不上。本文不否定 `VMᶜʰ`；`YiVmNegSeg`、`YiVmNegIrr` 的探针是布尔序列族，不在这个 ℕ 下标的子域里。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmNegChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
import OCF.Align.RR5IrrCore as B
open B using (Lgl)
open import OCF.Align.YiIrrIf using (R; read0; read0-legal)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ; Ptᵐ; pointsᵐ; obsᵐ; foldᵐ₃; rplain)
open Ptᵐ using (coordᵐ; lawfulᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiBtValAdm using (toIL; toIL-c)
open import OCF.Align.YiBtValFin using (lower-any)
open import OCF.Align.YiBtValBT using (module D; ZsL→; inv; +ʳ≽)
open import OCF.Align.YiMonoVM using (VMᴸ; HS-read; lvl≅)
open import OCF.Align.YiMonoBreak using (NZ; no-mono-⊑; inv-nz)
open import OCF.Align.YiVmNegBound using (bound-⊑; pred→⊑)
import OCF.Align.Level as L
open L using (Ordᴵ; _≺ᴵ_; _≅ᴵ_; _⊑ᴵ_)
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼)
```

## 1 子域与约化

```agda
pt : ℕ → R
pt n = coordᵐ (pointsᵐ n)

VMᶜʰ : Set
VMᶜʰ = ∀ n → D.γ n ≼ read (pt n) →
  L.ψ⁰ (L.Ω (L.toLevel (D.γ n) (D.cert n))) ≼ L.ψ⁰ (L.Ω (L.toLevel (read (pt n)) (HS-read (pt n) (lawfulᵐ (pointsᵐ n)))))

vm→ch : VMᴸ → VMᶜʰ
vm→ch vm n le = vm (D.γ n) (D.cert n) (read (pt n)) (HS-read (pt n) (lawfulᵐ (pointsᵐ n))) le

module FromCh (vm : VMᶜʰ) where

  mono : ∀ n → D.γ n ≼ read (pt n) →
    L.ψ⁰ (L.Ω (L.toLevel (D.γ n) (D.cert n))) ≼ read (foldᵐ₃ (pt n) (lawfulᵐ (pointsᵐ n)))
  mono n le =
    ≼-trans (vm n le)
    (≼-trans (≅→≼ (L.ψ⁰-≅ (L.Ω-≅ (lvl≅ a (HS-read a l) (rplain a) (read0-legal a l)))))
      (lower-any (read0 a) (rplain a) (read0-legal a l) (toIL-c (read0 a) (rplain a) (read0-legal a l))
        (ZsL→ (read0 a) (rplain a) (read0-legal a l) (proj₂ (inv n)))))
    where
    a = pt n
    l = lawfulᵐ (pointsᵐ n)

  chain : ∀ n → D.γ n ≼ read (pt n)
  chain zero = ≼-refl _
  chain (suc n) = +ʳ≽ (pt n) (obsᵐ (pointsᵐ n)) (mono n (chain n))

  btbo : D.BTBOᴵ ≼ read T₃ᵐ
  btbo = l≼ (λ n → ≼l n (mono n (chain n)))

ch→btbo : VMᶜʰ → D.BTBOᴵ ≼ read T₃ᵐ
ch→btbo vm = FromCh.btbo vm
```

## 2 链上没有公共上界

```agda
≅→⊑ᴵ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅→⊑ᴵ e = pred→⊑ (λ r → L.≺ᴵ-respʳ r e)

no-bound : ∀ n (a : R) (l : Lgl B.zero a) → NZ (read0 a) → D.γ (suc n) ≼ read a → ∀ {z} →
  L.toLevel (D.γ (suc n)) (D.cert (suc n)) ≺ᴵ z → L.toLevel (read a) (HS-read a l) ≺ᴵ z → ⊥
no-bound n a l nz le px py =
  no-mono-⊑ n a l nz (L.⊑ᴵ-trans (bound-⊑ (D.γ (suc n)) (D.cert (suc n)) (read a) (HS-read a l) px py le)
    (≅→⊑ᴵ (lvl≅ a (HS-read a l) (rplain a) (read0-legal a l))))

no-bound-pt : ∀ n → D.γ (suc n) ≼ read (pt (suc n)) → ∀ {z} →
  L.toLevel (D.γ (suc n)) (D.cert (suc n)) ≺ᴵ z →
  L.toLevel (read (pt (suc n))) (HS-read (pt (suc n)) (lawfulᵐ (pointsᵐ (suc n)))) ≺ᴵ z → ⊥
no-bound-pt n = no-bound n (pt (suc n)) (lawfulᵐ (pointsᵐ (suc n))) (proj₂ (inv-nz (suc n)))
```
