# 上折梯子：深层 self 分量的 N 关系
不读记号；编译定理：后继形状层号 j（孩子 k 不含 Ω 形状）上，右边是 `Up j d b y` 且 `Ωt j ≼ y`，左边固定为 `Up k (down d tt) b (Ωt k)`，则左边 ≼ 右边（`ladder`，对 `Ωt j ≼ y` 的推导归纳，不用传递性）；推论 `left-right` 的两个深层同形：第 3 层 `Up L1 … (Ωt L3) (Ωt L1) ≼ ψ_self(Ωt L3)`（`deep₃`）、第 4 层的两级上折（`deep₄`）。
这是前缀 3 起底的分量里 "纯上折" 一类所需的形状；"折叠后的上折" 一类未做，见回报。不否定什么。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRUp where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (self; Ok)
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
open import OCF.Lean.YiVRRel using (NoΩ)
open import OCF.Lean.YiRRRel

predN : ∀ {ℓ a y} → N ℓ (suc a) y → N ℓ a y
predN (s≼s d) = ≼s d
predN (≼s d) = ≼s (predN d)
predN (≼l n d) = ≼l n (predN d)
predN (≼w d) = ≼w (predN d)
predN (≼W z ez k) = ≼W z ez (λ z′ r → predN (k z′ r))
predN (≼u d) = ≼u (predN d)
```

## 梯子

右边沿推导往外走的各行 (`≼s`, `≼l`, `≼w`, `≼W`, `≼u`) 只是把上折的输出往外包; `w≼w` 一行在 `Ωt k` 处用 `≼W` 进入, 再对孩子的嵌入用 `Up≼`.

```agda
module Ladder {ℓ k : L} (νk : NoΩ k) (d : Dn ℓ (nd sS (λ _ → k))) (b : Tr⁺ ℓ) (hb : N ℓ (proj₁ b) (proj₁ b)) where
  j : L
  j = nd sS (λ _ → k)
  a : Tr ℓ
  a = proj₁ (Up k (down d tt) b (proj₁ (Ωt k)))

  rung : ∀ {y} {e} → N j (up zero tt (suc (proj₁ (Ωt k))) e) y → N ℓ a (proj₁ (Up j d b y))
  rung (≼s r) = ≼l 0 (rung r)
  rung (≼l n r) = ≼l n (rung r)
  rung {e = e} (≼w {p = p} {g = g} r) =
    ≼w (subst (λ t → N ℓ a (proj₁ (Up j d b (g t)))) (sym (mvFirst d p)) (rung {e = e} r))
  rung {e = e} (≼W {p = p} z ez k′) = ≼W (mvBr⁻ d p z) (mvE d p ez) (λ u r → rung {e = e} (k′ _ (mvN⁻ d p r)))
  rung (≼u {x = x} {c = c} {y = y₁} r) = ≼Up k (down d c) (Up j d b x) y₁ (rung r)
  rung (u≼u {x′ = x} dx dy) = Up≼ k (down d tt) b (Up j d b x) (≼Up j d b x hb) (predN dy)

  ladder : ∀ {y} → N j (proj₁ (Ωt j)) y → N ℓ a (proj₁ (Up j d b y))
  ladder (≼s r) = ≼l 0 (ladder r)
  ladder (≼l n r) = ≼l n (ladder r)
  ladder (≼w {p = p} {g = g} r) =
    ≼w (subst (λ t → N ℓ a (proj₁ (Up j d b (g t)))) (sym (mvFirst d p)) (ladder r))
  ladder (≼W {p = p} z ez k′) = ≼W (mvBr⁻ d p z) (mvE d p ez) (λ u r → ladder (k′ _ (mvN⁻ d p r)))
  ladder (≼u {x = x} {c = c} {y = y₁} r) = ≼Up k (down d c) (Up j d b x) y₁ (ladder r)
  ladder (w≼w {p = inj₂ (tt , inj₁ tt)} h) =
    ≼W (mvBr⁻ d (inj₂ (tt , inj₁ tt)) (proj₁ (Ωt k))) (mvE d (inj₂ (tt , inj₁ tt)) (entry k νk))
      (λ u r → rung (h (proj₁ (Ωt k)) _ (mvN⁻ d (inj₂ (tt , inj₁ tt)) r)))
```

## 深层的两个实例

```agda
L2 L3 L4 : L
L2 = nd sS (λ _ → L1)
L3 = nd sS (λ _ → L2)
L4 = nd sS (λ _ → L3)

o₃ : Ok L3
o₃ = tt , λ _ → tt , λ _ → tt , λ _ → tt

deep₃ : N L3 (proj₁ (Up L1 (down (down stop tt) tt) (Ωt L3) (proj₁ (Ωt L1))))
             (proj₁ (TB.ψ L3 o₃ (MT.rbᶻ L3) (F.B₀ L3) L3 self (Ωt L3) (proj₁ (Ωt L3))))
deep₃ = ≼W (proj₁ (Ωt L2)) (entry L2 tt)
  (λ z′ r → ≼l 0 (Ladder.ladder {k = L1} tt (down stop tt) (Ωt L3) (Ωt≼ L3 tt) r))

deep₄ : N L4 (proj₁ (Up L1 (down (down (down stop tt) tt) tt) (Ωt L4) (proj₁ (Ωt L1))))
             (proj₁ (Up L3 (down stop tt) (Ωt L4) (proj₁ (Ωt L3))))
deep₄ = ≼W (proj₁ (Ωt L2)) (entry L2 tt)
  (λ z′ r → ≼l 0 (Ladder.ladder {k = L1} tt (down (down stop tt) tt) (Ωt L4) (Ωt≼ L4 tt) r))
```
