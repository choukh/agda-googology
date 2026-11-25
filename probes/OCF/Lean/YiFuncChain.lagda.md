# YiFunc 接线：`CRUX` 的两向实例与链上的 BTBO 下界

**验收文件，档位：编译定理与条件定理。** `crux₂`：`Q` 两个方向都有保值嵌入时，`CRUX` 对这个 `Q` 的结论成立 (含 ω+1 对 ω⁺+1，`crux-sω`)。`btbo-CS⁺ : CRUX → StrD → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺`：链上一步用 `func-str` 代替一般的 `FUNC`，多一个前提 `StrD` (参照层号 `D.L n` 沿极限分支严格)；`StrD` 在 n = 0 是定理 (`str₀`)。
不证一般的 `CRUX`，不证 n ≥ 1 的 `StrD`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFuncChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.Sum.Base using (inj₁; inj₂)
import OCF.Align.Level as L
open L using (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via)
import OCF.Align.Uniform as Un
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; ≼-trans)
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘; PEmb-suc; ω⁺ᴵ; ω⊑ω⁺)
open import OCF.Align.YiVmConExact using (XEmb; XEmb-⊑; XEmb-suc; V; V-≺; ≈→≅; ˣ→≼; Vt; tV; embˣ; ⊑ᵇ)
open XEmb
open import OCF.Lean.YiEmb2 using (VMˣ₂)
open import OCF.Lean.YiPEStep using (L⁺; KEY; shift-κ; PEmb-≅ʳ; PEmb-≅ˡ)
open import OCF.Lean.YiPEKey using (KEYsuc; SpineT; key-from)
open import OCF.Lean.YiPEBase using (EmbTⁿ; btbo-embⁿ; btbo-emb⁺)
open import OCF.Lean.YiFuncBase using (PEmb-res; ω⁺⊑ω)
open import OCF.Lean.YiFuncLim using (FB; CRUX; Str; ss; func-str; L⁺<)
open FB
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiLeanValFin using (κ)
open import OCF.Lean.YiLeanTw3 using (T₃)
open import OCF.Lean.YiLeanAccFin using (read)
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
```

## 1 保值嵌入的限制、搬运与顶值

```agda
XEmb-res : ∀ {a b c} (X : XEmb a b) (r : c ≺ᴵ a) → XEmb c (map (P X) r)
XEmb-res X r = record { P = PEmb-res (P X) r ; ex = λ s → ex X (L.≺ᴵ-trans s r) ; ex′ = λ s → ex′ X (L.≺ᴵ-trans s r) }

XEmb-≅ʳ : ∀ {a b b′} → XEmb a b → b ≅ᴵ b′ → XEmb a b′
XEmb-≅ʳ X e = record { P = PEmb-≅ʳ (P X) e ; ex = ex X ; ex′ = ex′ X }

XEmb-≅ˡ : ∀ {a a′ b} → a′ ≅ᴵ a → XEmb a b → XEmb a′ b
XEmb-≅ˡ e X = record { P = PEmb-≅ˡ e (P X) ; ex = λ r → ex X (L.≺ᴵ-respʳ r e) ; ex′ = λ r → ex′ X (L.≺ᴵ-respʳ r e) }

Vbound : ∀ {b} x → (∀ {c} → c <ᴵ x → L.suc (V c) ≼ V b) → V x ≼ V b
Vbound L.zero h = z≼
Vbound (L.suc x) h = h L.zero
Vbound (L.lim f s) h = l≼ (λ n → Vbound (f n) (λ q → h (L.lim n q)))

XV : ∀ {a b} → XEmb a b → V a ≼ V b
XV {a} X = Vbound a (λ q → ≼-trans (s≼s (ex′ X (via (L.≅ᴵ-refl _) q))) (V-≺ (bnd (P X) (via (L.≅ᴵ-refl _) q))))

LV : ∀ {a b} → XEmb a b → XEmb b a → V (L⁺ a) ≼ V (L⁺ b)
LV {a} {b} X Y = ≼-trans (Vt _ (Un.Uniform a)) (≼-trans (ˣ→≼ (VMˣ₂ X Y)) (tV _ (Un.Uniform b)))
```

## 2 两向实例

`R` 取 `embˣ` 给的保值嵌入；边界性质：`L⁺ (Q x)` 与 `L⁺ x` 两向值相等 (限制后的两个保值嵌入经 `VMˣ₂`)，与 `R` 的像同在 `L⁺ (suc c′)` 之下，由 `≈→≅` 得 `≅ᴵ`。

```agda
module Crux₂ {c c′ : Ordᴵ} (X : XEmb c c′) (Y : XEmb c′ c) where
  X₊ : XEmb (L.suc c) (L.suc c′)
  X₊ = XEmb-suc X (XV X) (XV Y)

  Y₊ : XEmb (L.suc c′) (L.suc c)
  Y₊ = XEmb-suc Y (XV Y) (XV X)

  Z : XEmb (L⁺ (L.suc c)) (L⁺ (L.suc c′))
  Z = embˣ _ (Un.Uniform (L.suc c)) _ (Un.Uniform (L.suc c′)) (VMˣ₂ X₊ Y₊)

  pair : ∀ {x} (r : x ≺ᴵ L.suc c) → XEmb x (map (PEmb-suc (P X)) r) × XEmb (map (PEmb-suc (P X)) r) x
  pair (via e L.zero) = XEmb-≅ˡ e X , XEmb-≅ʳ Y (L.≅ᴵ-sym e)
  pair (via e (L.suc q)) = XEmb-res X (via e q) , XEmb-≅ʳ (XEmb-res Y (bnd (P X) (via e q))) back
    where
    back = ≈→≅ (bnd (P Y) (bnd (P X) (via e q))) (via e q)
      (≼-trans (ex Y (bnd (P X) (via e q))) (ex X (via e q)))
      (≼-trans (ex′ X (via e q)) (ex′ Y (bnd (P X) (via e q))))

  fb : FB (PEmb-suc (P X))
  R fb = P Z
  bd fb {x} r r′ with pair r
  ... | Xr , Yr = ⊑ᵇ (inj₂ (L.≅ᴵ-sym (≈→≅ (bnd (P Z) r′) (L⁺< (bnd (PEmb-suc (P X)) r))
          (≼-trans (ex Z r′) (LV Xr Yr)) (≼-trans (LV Yr Xr) (ex′ Z r′)))))

crux₂ : ∀ {c c′} (X : XEmb c c′) (Y : XEmb c′ c) → FB (PEmb-suc (P X))
crux₂ X Y = Crux₂.fb X Y

crux-sω : FB (PEmb-suc (PEmb-⊑ ω⊑ω⁺))
crux-sω = crux₂ (XEmb-⊑ ω⊑ω⁺) (XEmb-⊑ ω⁺⊑ω)
```

## 3 链上的接线

一步与 `YiPEStep.FromFK` 相同，只把 `func (emb n)` 换成 `func-str cr (sd n) (emb n)`。

```agda
StrD : Set
StrD = ∀ n → Str (D.L n)

str₀ : Str (D.L 0)
str₀ = ss

module FromCS (cr : CRUX) (sd : StrD) (key : KEY) where
  emb : ∀ n → PEmb (D.L n) (κ n)
  emb zero = PEmb-⊑ L.⊑ᴵ-refl
  emb (suc n) = PEmb-∘ (func-str cr (sd n) (emb n)) (PEmb-∘ (key n) (shift-κ n))

emb-CS : CRUX → StrD → KEY → EmbTⁿ
emb-CS cr sd key n = n , FromCS.emb cr sd key n

btbo-CS : CRUX → StrD → KEYsuc → SpineT → D.BTBOᴵ ≼ read T₃
btbo-CS cr sd ks sp = btbo-embⁿ (emb-CS cr sd (key-from ks sp))

btbo-CS⁺ : CRUX → StrD → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺
btbo-CS⁺ cr sd ks sp = btbo-emb⁺ (emb-CS cr sd (key-from ks sp))
```
