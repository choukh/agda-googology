# 主线候选的值: 塔各项同值, 终点 ≥ BTBO

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理, 无前提: 塔各项的闭项上兄弟孩子那一行不触发 (`tw-norow`, `refl`), 所以 `twˢ n` 与 F2 的 `twᶜ n` 逐层相关 (`twˢ-R`), 与原主线同值 (`same-twˢ`); 由此搬来 `btbo-tw1ˢ`, `btbo-twˢ`, `tA≼tw2ˢ`, `bho-lowerˢ`.
> 终点: 第 1 支在塔第 1 项的孩子 c′ 的底上换了形 (`B1-new`, 原来是 `B1-old`, 这一分量新不低于旧, `B1-ge`); 第 1 支与 F2 上一个手造的底 `Bᶠ` 的 `Fn 1 Bᶠ` 相关 (`br1-R`), `Bᶠ` 满足 `OKB` 与起点条件, 由 `YiEBBtbo.btbo-B` 得 `btbo-EBOˢ`.
> 不是 "新终点 ≥ 原终点": 那要按值比较不同孩子层上的折叠 (`YiVRRead.GMono` 的带底形式), 没有证也没有否定. 终点的其余值定理在 [YiSMEnd](YiSMEnd.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSMValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiSMFold
open import OCF.Lean.YiSMRel using (ψ⁰; A; S; cL)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; +-R; +m-R; ι-R; ιm-R; cumΩ-R)
open import OCF.Lean.YiBRFold using (B₀-R; W→L)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; Λ-L; Λ-E; two; Ok-two)
open import OCF.Lean.YiBRValue using (readRW; rel≅; rel≅ᴹ; up≼; same-tw)
open import OCF.Lean.YiLSRead using (read; _⊢_⊴_; ⊴r; ⊴◃; ⊴-◃)
open import OCF.Lean.YiLSFold using (OKB; ψs-⊵)
import OCF.Lean.YiLSTw1 as T1
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiT2Mono using (btbo-tw)
open import OCF.Lean.YiEBShape using (dB; Fn; ok-dB)
open import OCF.Lean.YiEBBtbo using (Start; start-dB1; module Btbo)
open import OCF.Lean.YiEVTw2 using (tA≼tw2ᴿ)
open import OCF.Lean.YiMEAnchor using (bho-lowerᴹ; t₂; h₂)
open import OCF.Lean.YiMEBase using (Rt)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA)
open import OCF.Lean.YiRBFam using (ψ-⊵)
import OCF.Lean.YiKVRel as KV
open import OCF.Lean.YiKidGen using (◃→≼)
import OCF.Align.EboLeanDef as E
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
```

## 塔各项

不带证据的第 0 层折叠对 F2 的 `ψ₀`. 塔第 n+1 项的闭项与不带证据的折叠逐字相同: 顶层只经一致路径与下标层侧的路径进孩子, 经指定孩子的路径只作用在左项 `zero` 上.

```agda
ψ₀⁰-R : ∀ {ℓ ℓ′ o ε ρ} → RelE ℓ ℓ′ o ε ρ → {x : Tr ℓ} {x′ : F.Tr ℓ′} → RelT ℓ ℓ′ x x′
      → RelT zero F.zero (proj₁ (ψ₀ʳ ℓ o (rb-no ℓ) x)) (F.ψ₀ ℓ′ ε ρ x′)
ψ₀⁰-R re rx = proj₁ (A re (B₀ _) (F.B₀ _) (B₀-R (E→L re)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) rx)

tw-norow : (n : ℕ) → twˢ (suc n) ≡ proj₁ (ψ₀ʳ (tw (suc n)) (Ok-tw (suc n)) (rb-no (tw (suc n))) (proj₁ (Ωt (tw (suc n)))))
tw-norow n = refl

twˢ-R : (n : ℕ) → RelT zero F.zero (twˢ n) (F.twᶜ n)
twˢ-R zero    = ψ₀⁰-R (tw-E zero) (Ωt-R (tw-L zero))
twˢ-R (suc n) = ψ₀⁰-R (tw-E (suc n)) (Ωt-R (tw-L (suc n)))

same-twˢ : (n : ℕ) → readRW (twˢ n) L.≅ readRW (RW.twᶜ n)
same-twˢ n = L.≅-trans (rel≅ (twˢ-R n)) (L.≅-sym (same-tw n))

btbo-tw1ˢ : D.BTBOᴵ ≼ readRW (twˢ 1)
btbo-tw1ˢ = up≼ (twˢ-R 1) btbo-tw1

btbo-twˢ : (n : ℕ) → D.BTBOᴵ ≼ readRW (twˢ (suc n))
btbo-twˢ n = up≼ (twˢ-R (suc n)) (btbo-tw n)

tA≼tw2ˢ : (h : E.HC tA) → R2.Rt h ≼ readRW (twˢ 2)
tA≼tw2ˢ h = ≼-trans (tA≼tw2ᴿ h) (≅→≼ (L.≅-sym (same-twˢ 2)))

two-Rˢ : RelT zero F.zero (proj₁ (ψ₀ʳ two Ok-two (rb-no two) (proj₁ (Ωt two))))
           (F.ψ₀ (F.suc (F.suc F.zero)) tt tt (F.Ωt (F.suc (F.suc F.zero))))
two-Rˢ = ψ₀⁰-R (eS (eS ez)) (Ωt-R (lS (lS lz)))

bho-lowerˢ : (h : E.HC t₂) → Rt h ≼ readRW (proj₁ (ψ₀ʳ two Ok-two (rb-no two) (proj₁ (Ωt two))))
bho-lowerˢ h = ≼-trans (bho-lowerᴹ h) (≅→≼ (L.≅-sym (rel≅ᴹ two-Rˢ)))

inst-tw2 : R2.Rt hA ≼ readRW (twˢ 2)
inst-tw2 = tA≼tw2ˢ hA

inst-two : Rt h₂ ≼ readRW (proj₁ (ψ₀ʳ two Ok-two (rb-no two) (proj₁ (Ωt two))))
inst-two = bho-lowerˢ h₂
```

## 终点的各支, 第 1 支的底

`brˢ n` 是 `EBOˢ` 的第 n 支. 第 1 支是层号 `tw 1` 上 Ω 树以 `B1ˢ` 为底的折叠, 顶层同样不触发新的一行 (`br1-form`).

```agda
Fᴧ : ℕ → Tr Λ
Fᴧ n = proj₁ (upz {s = sL} {h = tw} n (Ωt (tw n)))

brˢ : ℕ → Tr zero
brˢ n = proj₁ (ψ Λ Ok-Λ rb-Λ (B₀ Λ) zero (z≤ Λ) (Ωt zero) (cum Fᴧ n))

brˢ≼ : (n : ℕ) → readRW (brˢ n) ≼ readRW EBOˢ
brˢ≼ n = ≼l n (≼-refl _)

B1ˢ : Base (tw 1)
B1ˢ j u = ψ Λ Ok-Λ rb-Λ (B₀ Λ) j (inc 1 u) (Ωt j) (cum Fᴧ 0)

β1ˢ : Tr⁺ zero
β1ˢ = ψ Λ Ok-Λ rb-Λ (B₀ Λ) zero (z≤ Λ) (Ωt zero) (cum Fᴧ 0)

br1-form : brˢ 1 ≡ proj₁ (ψ⁰ (tw 1) (Ok-tw 1) B1ˢ zero (z≤ (tw 1)) β1ˢ (proj₁ (Ωt (tw 1))))
br1-form = refl
```

孩子 c′ 的底在第 0 层经 `inc c′ v` 的分量: 新的是孩子 c′ 的 Ω 树从 1 折下来再加 ω, 原来是 1 加 ω.

```agda
B1ᴿ : Base (tw 1)
B1ᴿ j u = RW.ψ Λ Ok-Λ (B₀ Λ) j (inc 1 u) (Ωt j) (cum Fᴧ 0)

hc : Tr zero → L
hc c = zero ⊕ ↑ zero c

Fc : (c′ : Tr zero) → zero ≤ hc c′ → Tr⁺ zero
Fc c′ v = ψ⁰ (hc c′) (proj₂ (Ok-tw 1) c′) (B₀ _) zero v (Ωt zero) (proj₁ (Ωt (hc c′)))

ω₀ : Tr zero
ω₀ = proj₁ (next⁺ (Ωt zero))

B1-new : (c′ : Tr zero) (v : zero ≤ hc c′) → proj₁ (B1ˢ zero (inc c′ v)) ≡ proj₁ (Fc c′ v) + ι zero ω₀
B1-new c′ v = refl

B1-old : (c′ : Tr zero) (v : zero ≤ hc c′) → proj₁ (B1ᴿ zero (inc c′ v)) ≡ suc zero + ι zero ω₀
B1-old c′ v = refl

+ˡ≼ : (a a′ b : Tr zero) → readRW a ≼ readRW a′ → readRW (a + ι zero b) ≼ readRW (a′ + ι zero b)
+ˡ≼ a a′ zero          h = h
+ˡ≼ a a′ (suc b)       h = s≼s (+ˡ≼ a a′ b h)
+ˡ≼ a a′ (lim f r)     h = l≼ (λ n → ≼l n (+ˡ≼ a a′ (f n) h))
+ˡ≼ a a′ (Ω () g)      h
+ˡ≼ a a′ (up x () y e) h

⊴≼ : {x y : Tr zero} → x KV.⊴ y → readRW x ≼ readRW y
⊴≼ KV.⊴r     = ≼-refl _
⊴≼ (KV.⊴◃ d) = ◃→≼ d

B1-ge : (c′ : Tr zero) (v : zero ≤ hc c′) → readRW (proj₁ (B1ᴿ zero (inc c′ v))) ≼ readRW (proj₁ (B1ˢ zero (inc c′ v)))
B1-ge c′ v = +ˡ≼ (suc zero) (proj₁ (Fc c′ v)) ω₀
  (⊴≼ (ψ-⊵ (hc c′) (proj₂ (Ok-tw 1) c′) (rb-no _) (B₀ _) zero v (Ωt zero) (proj₁ (Ωt (hc c′)))))
```

## F2 上的对应底

经 `inb c v` 的分量照新的一行手写 (孩子 c 的 Ω 树的折叠加 ω), 其余分量与 `b⊥` 取第 1 支原来的底 `dB 1`.

```agda
Y′ : F.Tr F.zero
Y′ = F.ψ₀ F.zero tt tt (F.suc F.zero)

nY′ : F._⊢_◃_ F.zero F.zero Y′
nY′ = F.nz⊥ F.zero tt tt (F.B₀ F.zero) (F.suc F.zero)

bsᶠ : (j : F.L) → F._≤_ j (F.tw 1) → F.Tr j
bsᶠ j (F.inb c v) =
  F.ψs (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (T1.h₁ c)) F.+ F.ι j Y′
bsᶠ j F.self     = F.bs (dB 1) j F.self
bsᶠ j (F.ink v)  = F.bs (dB 1) j (F.ink v)
bsᶠ j (F.inu vs) = F.bs (dB 1) j (F.inu vs)

nsᶠ : (j : F.L) (w : F._≤_ j (F.tw 1)) → F._⊢_◃_ j F.zero (bsᶠ j w)
nsᶠ j (F.inb c v) =
  F.◃t (F.nzs (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (T1.h₁ c)))
       (F.+-mono (F.ψs (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (T1.h₁ c)))
                 (F.ι-mono j nY′))
nsᶠ j F.self     = F.ns (dB 1) j F.self
nsᶠ j (F.ink v)  = F.ns (dB 1) j (F.ink v)
nsᶠ j (F.inu vs) = F.ns (dB 1) j (F.inu vs)

Bᶠ : F.Base (F.tw 1)
Bᶠ = F.base (F.b⊥ (dB 1)) (F.n⊥ (dB 1)) bsᶠ nsᶠ
```

## 相关, `OKB`, 起点

```agda
chE : ∀ {k h k′ h′ o ε ρ} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ
    → (c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′ → RelE (h c) (h′ c′) (proj₂ o c) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)
chE (eΩ rk rwc rc) = rc

cΛ : RelBase (tw 1) (F.tw 1) (λ i w → ψ⁰ Λ Ok-Λ (B₀ Λ) i (inc 1 w) (B₀ Λ i (inc 1 w)) (cum Fᴧ 0))
       (F.dL F.tw F.Ev-Λ F.Rt-Λ (F.B₀ F.Λ) 1 (F.cumΩ F.tw 0))
cΛ = cL Λ-E (B₀ Λ) (F.B₀ F.Λ) (B₀-R Λ-L) (cumΩ-R Λ-L 0) 1

y-R : RelT zero F.zero (suc zero) (F.suc F.zero)
y-R = is iz

rB1 : RelBase (tw 1) (F.tw 1) B1ˢ Bᶠ
rB1 j j′ w w′ rw@wself      = cΛ j j′ w w′ rw
rB1 j j′ w w′ rw@(winuΩ _)  = cΛ j j′ w w′ rw
rB1 j j′ w w′ rw@(wink _)   = cΛ j j′ w w′ rw
rB1 j j′ w w′ (wincΩ {c = c} {c′ = c′} rcc rv) =
  let rec = chE (tw-E 1) c c′ rcc
      rlj = W→L (E→L rec) rv
      s₁  = S rec (B₀ _) (F.B₀ _) (B₀-R (E→L rec)) rv (Ωt j) (Ωt-R rlj) (Ωn-R rlj) (Ωt-R (E→L rec))
      a₂  = A ez (B₀ zero) (F.B₀ F.zero) (B₀-R lz) (Ωt zero) (Ωt-R lz) (Ωn-R lz) y-R
  in +-R (proj₁ s₁) (ι-R (proj₁ a₂)) , dt (proj₂ s₁ , +m-R (proj₁ s₁) (ιm-R (proj₂ a₂)))

β1-R : RelT zero F.zero (proj₁ β1ˢ) (F.b⊥ Bᶠ) × RelD zero F.zero (proj₂ β1ˢ) (F.n⊥ Bᶠ)
β1-R = A Λ-E (B₀ Λ) (F.B₀ F.Λ) (B₀-R Λ-L) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (cumΩ-R Λ-L 0)

br1-R : RelT zero F.zero (brˢ 1) (Fn 1 Bᶠ)
br1-R = proj₁ (A (tw-E 1) B1ˢ Bᶠ rB1 β1ˢ (proj₁ β1-R) (proj₂ β1-R) (Ωt-R (tw-L 1)))

okᶠ : OKB (F.tw 1) Bᶠ
okᶠ = proj₁ (ok-dB 1) , okbs
  where
  okbs : (j : F.L) (w : F._≤_ j (F.tw 1)) → j ⊢ F.Ωt j ⊴ bsᶠ j w
  okbs j (F.inb c v) =
    ⊴◃ (⊴-◃ (ψs-⊵ (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (T1.h₁ c)))
             (F.+-mono (F.ψs (T1.h₁ c) (T1.εh c) (T1.ρh c) (F.B₀ (T1.h₁ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (T1.h₁ c)))
                       (F.ι-mono j nY′)))
  okbs j F.self     = proj₂ (ok-dB 1) j F.self
  okbs j (F.ink v)  = proj₂ (ok-dB 1) j (F.ink v)
  okbs j (F.inu vs) = proj₂ (ok-dB 1) j (F.inu vs)

stᶠ : Start Bᶠ
stᶠ = start-dB1
```

## 终点 ≥ BTBO

```agda
btbo-br1ˢ : D.BTBOᴵ ≼ readRW (brˢ 1)
btbo-br1ˢ = up≼ br1-R (Btbo.btbo-B Bᶠ okᶠ stᶠ)

btbo-EBOˢ : D.BTBOᴵ ≼ readRW EBOˢ
btbo-EBOˢ = ≼-trans btbo-br1ˢ (brˢ≼ 1)
```
