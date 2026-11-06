# ValX (五): 实例 `I₁` 的回灌律, 接口的实例, 闭项

> 不含记号. 入口 [ValX](ValX.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. §1–§3 不用 UIP; §4 (接口的实例) 以 `Cd` 上的 UIP 为模块参数 (条件).
>
> - `shLaw₁`: 实例 `I₁` (回灌 $B\boxplus\mathrm{leg}\,c$, 新世界 $e+1$) 满足 `ShLaw` (定理). 关键是 `leg` 对第 0 层的值关系单调 (`leg-mono`): 在 ValC 的关系下 (ℕ-极限在左边只对严格增子列) 部分和保序; 否定一路 `NegValCInst.sh-not-mono≤` 的反例 ($\lim(1,1,\dots)\le1$) 在这个关系下不成立, 所以不冲突.
> - `MoX-Ω₁`: $\Omega_1$ 结点 `gt 1` 值合法.
> - **`TU2-above`**: 对一切 $n$, $\mathrm{TU}(y_n+1)+1\le\mathrm{TU2}$ (定理, 不用 UIP). 这是**结构的**: 由对角的定义 $y_{n+1}=y_n\boxplus\mathrm{TU}(y_n+1)$ 与 "跨底折叠的输出 $\ge1$" (`oneX`) 得出, 不用跨底单调.
> - `valX⁻` (条件: UIP): 接口 §5 的记录 `ValX⁻` 对 `I₁` 的实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ValXTm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; leg; Σ₀; W₀; TU; inU; PH-inU; yU; lg-yU; TU2)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁
open import OCF.Lean.ValXRel I₁
open import OCF.Lean.ValCIf I₁ using (toA; ValC⊥ᵖ)
open import OCF.Lean.ValXIf I₁ using (ValX⁻)
open import OCF.Align.CumReadCF using (asuc)
import OCF.Align.TLRuleSpec as TL
```

## §1 `leg` 对第 0 层的值关系单调; `I₁` 的回灌律

```agda
Σ₀≡ : ∀ (f : ℕ → Cd) n → Σ₀ f n ≡ Σ⁺ f n
Σ₀≡ f zero = refl
Σ₀≡ f (suc n) = cong (λ z → z ⊞ f (suc n)) (Σ₀≡ f n)

Σ₀-ge : ∀ (f : ℕ → Cd) n → LeAt hz (f n) (Σ₀ f n)
Σ₀-ge f n = subst (LeAt hz (f n)) (sym (Σ₀≡ f n)) (Ac0.Σ-ge hz f n)

leg-mono : ∀ {a b} → LeAt hz a b → LeAt hz (leg a) (leg b)
leg-mono Rel.z≤ = Rel.z≤
leg-mono (Rel.s≤s p) = Rel.s≤s (leg-mono p)
leg-mono (Rel.≤s p) = Rel.≤s (leg-mono p)
leg-mono {hl f} {hl g} (Rel.l≤l σ i h) =
  Rel.l≤l σ i (λ n → subst₂ (LeAt hz) (sym (Σ₀≡ (λ k → leg (f k)) n)) (sym (Σ₀≡ (λ k → leg (g k)) (σ n)))
    (Ac0.Σ-sub hz _ _ σ i (λ k → leg-mono (h k)) n))
leg-mono {b = hl g} (Rel.≤l n p) = Rel.≤l n (L.≤-trans hz (leg-mono p) (Σ₀-ge (λ k → leg (g k)) n))
leg-mono (Rel.≤Ω {κ = ()} _ _ _ _)
leg-mono (Rel.Ω≤Ω {κ = ()} _ _)

leg-infl : ∀ c → LeAt hz c (leg c)
leg-infl hz = Rel.z≤
leg-infl (hs c) = Rel.s≤s (leg-infl c)
leg-infl (hl f) = Rel.l≤l (λ n → n) idInc (λ n → L.≤-trans hz (leg-infl (f n)) (Σ₀-ge (λ k → leg (f k)) n))
leg-infl (hΩ () _)

shLaw₁ : ShLaw
shLaw₁ = record
  { shM = λ p q → L.⊞-mono hz p (leg-mono q)
  ; shI = λ {B} c → L.≤-trans hz (leg-infl c) (L.≤⊞ˡ hz B (leg c))
  ; nxM = λ a a′ q → Rel.s≤s q }

open import OCF.Lean.ValXBase I₁ shLaw₁
```

## §2 $\Omega_1$ 结点值合法

`gt 1` 是 $\Omega_1$ 种类的结点, 分支 $c\mapsto 0\boxplus\iota_0(\mathrm{up}\,c)$ (可数树 $c$ 嵌入).

```agda
embX : Cd → HX
embX c = ι {Cd} {λ c → Tw S⊥ (hs c)} hz (up c)

emb-mono : ∀ {c c′} → LeAt hz c c′ → embX c ≤X embX c′
emb-mono Rel.z≤ = z≤
emb-mono (Rel.s≤s p) = s≤s (emb-mono p)
emb-mono (Rel.≤s p) = ≤s (emb-mono p)
emb-mono (Rel.l≤l σ i h) = l≤l σ i (λ n → emb-mono (h n))
emb-mono (Rel.≤l n p) = ≤l n (emb-mono p)
emb-mono (Rel.≤Ω {κ = ()} _ _ _ _)
emb-mono (Rel.Ω≤Ω {κ = ()} _ _)

MoX-emb : ∀ c → MoX (embX c)
MoX-emb hz = tt
MoX-emb (hs c) = MoX-emb c
MoX-emb (hl f) = λ n → MoX-emb (f n)
MoX-emb (hΩ () _)

MoX-Ω₁ : MoX (gt (hs hz))
MoX-Ω₁ = (λ c c′ _ _ p → ⊞X-monoʳ hz (emb-mono p)) , (λ c _ → MoX-⊞ hz (embX c) tt (MoX-emb c))
```

## §3 `TU2` 高于每个对角点 (结构的)

```agda
sound₀ : ∀ {x y} → LeAt hz x y → toA x TL.≤ toA y
sound₀ Rel.z≤ = TL.z≤
sound₀ (Rel.s≤s p) = TL.s≤ (sound₀ p)
sound₀ (Rel.≤s p) = TL.≤-suc (sound₀ p)
sound₀ (Rel.l≤l σ i h) = TL.l≤ (λ n → TL.≤l (σ n) (sound₀ (h n)))
sound₀ (Rel.≤l n p) = TL.≤l n (sound₀ p)
sound₀ (Rel.≤Ω {κ = ()} _ _ _ _)
sound₀ (Rel.Ω≤Ω {κ = ()} _ _)

-- 跨底折叠的输出不低于 1 (闭项 TU)
one≤TU : ∀ m lm → LeAt hz (hs hz) (TU m lm)
one≤TU m lm = oneX (wf bX hz) tt (z⊲ᴮ W₀) hz (inU m lm) (PH-inU m lm)

TU2-above : ∀ n → LeAt hz (hs (TU (hs (yU n)) (lg-yU n))) TU2
TU2-above n =
  Rel.≤l (suc (suc n))
    (L.≤-trans hz (Rel.s≤s (L.≤⊞ˡ hz (yU n) (TU (hs (yU n)) (lg-yU n))))
                  (L.⊞-monoʳ hz (yU (suc n)) (one≤TU (hs (yU (suc n))) (lg-yU (suc n)))))

TU2-aboveᴬ : ∀ n → asuc (toA (TU (hs (yU n)) (lg-yU n))) TL.≤ toA TU2
TU2-aboveᴬ n = sound₀ (TU2-above n)
```

## §4 接口的实例 (条件: `Cd` 上的 UIP)

```agda
import OCF.Lean.ValCTm as VT
import OCF.Lean.ValXMono as VM

module Inst (uipC : ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′) where
  open VT I₁ uipC using (valC⊥ᵖ)
  open VM I₁ uipC shLaw₁ using (monoX; MoXΦ)

  valX⁻ : ValX⁻
  valX⁻ = record
    { V = valC⊥ᵖ
    ; LeX = _≤X_ ; MoX = MoX
    ; leX-refl = ≤X-refl ; leX-trans = ≤X-trans
    ; MoX-Ω₁ = MoX-Ω₁
    ; X-one≤ = λ B lB t pt b x nd → oneX (wf bX hz) lB pt b x nd
    ; X-Mo = λ B lB t pt mb tb x nd mx → MoXΦ (wf bX hz) lB pt mb tb x nd mx
    ; X-mono = λ B lB t pt pt′ {y = y} nd nd′ mb mb′ tb bb mx my p →
        monoX (wf bX hz) (wf bX hz) lB lB (L.≤-refl hz B) pt pt′ (mb , mb′ , tb , bb) y nd nd′ mx my p
    }
```

## 结论 (按档)

- **[定理, 不用 UIP]** `leg-mono`, `leg-infl`, **`shLaw₁`** (`I₁` 的回灌与世界的值律); `emb-mono`, `MoX-emb`, **`MoX-Ω₁`**; `one≤TU`; **`TU2-above`**, `TU2-aboveᴬ`: 对一切 $n$, $\mathrm{TU}(y_n+1)+1\le\mathrm{TU2}$ (落到 `TLRuleSpec._≤_`; 结构的, 只用对角的定义与 `oneX`).
- **[条件定理, 条件: `Cd` 上的 UIP]** `Inst.valX⁻`: 接口 §5 `ValX⁻` 对 `I₁` 的实例 (关系 `_≤X_`, 值合法 `MoX`; 跨底单调由 `ValXMono.monoX`).
