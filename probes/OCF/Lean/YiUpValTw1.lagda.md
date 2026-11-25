# 上折: tw 1 这一站与 BTBO (条件定理)

> 验收文件. 站定在 `Tw1′ = ψ₀ (tw 1) (Ev-tw 1) (Ωt (tw 1))` (新折叠). `Tw1′-form` (`refl`): 它是 `G′ (pt′ n)` 的部分和的极限, 链 `pt′ (m+1) = K (pt′ m)`, `K x` 是层号 `h₁ x` 的 Ω 树沿 `lift` 路径折到第 0 层的树, `G′ x` 是同一层上的 ψ₀(Ω).
> 编译定理: 目标是第 0 层且路径是 `lift` 形时, `ψs` 与 `ψ⊥` 逐点相同 (`eq0`, 对一切带证据的层号), 所以 `K x` 与 `G′ x` 读回 `≅` (`KG`). 条件定理 `btbo-tw1′ : LOWER′ → V3F′ → D.BTBOᴵ ≼ read Tw1′`; 两条前提在 m = 0 是定理.
> 无前提: `low1-Ω₂ : ψ⁰(Ω₂) ≼ read (G′ (pt′ 1))` 与 `bho-tw1 : ψ⁰(Ω₂) ≼ read Tw1′` (链里实际出现的底代入 `YiUpVal.At`). `LOWER′` 在 m = 1 的其余分量 (一切有限层) 未证. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpValTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; Leg; Ωt-leg; Ωt-nz)
open import OCF.Lean.YiFreshValRead
open import OCF.Lean.YiFreshValTw1 using (h₁; cp; Mono-cp)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiLegal using (kp-ind)
open import OCF.Lean.YiUpFold
open import OCF.Lean.YiUpLegal using (ψ₀-leg; press; LegB₀; dS; dL; dW)
open import OCF.Lean.YiUpCheck using (one; two)
open import OCF.Lean.YiUpVal using (_⊢_⊴_; ⊴r; ⊴◃; ⊴-◃; ◃-⊴; ⊴-trans; ⊴→≼; ⊥0-⊵; s-⊴; Sβ₀; I1; I2; 𝟏; module At)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼)
open import OCF.BTBO using (module Ord-Ord)
module S = Ord-Ord
open S using (ordᴰ)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOFullEb using (module Blocks)
open import OCF.Align.BTBOFullV3 using (𝕋₀; bkᴵ)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFullLv using (SV-L)
open import OCF.Align.BTBOFull using (St-bk; bk≅γ)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-∘; PEmb-⊑)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.NoCumsum as N
open import OCF.Lean.YiBtboV2 using (V2′)
import OCF.Lean.YiPEStep as PS

module WT = Blocks 𝕋₀
```

## 1 第 0 层树的逐点相同

```agda
data E : Tr zero → Tr zero → Set where
  ez : E zero zero
  es : ∀ {a b} → E a b → E (suc a) (suc b)
  el : ∀ {f g} → (∀ n → E (f n) (g n)) → E (lim f) (lim g)

E-+ : ∀ {a a′ b b′} → E a a′ → E b b′ → E (a + b) (a′ + b′)
E-+ ea ez     = ea
E-+ ea (es e) = es (E-+ ea e)
E-+ ea (el h) = el (λ n → E-+ ea (h n))

E-next : ∀ {b b′} → E b b′ → E (next b) (next b′)
E-next {b} {b′} e = el go
  where
  go : ∀ n → E (iter (b +_) b n) (iter (b′ +_) b′ n)
  go zero    = e
  go (suc n) = E-+ e (go n)

E-cum : (F F′ : ℕ → Tr zero) → (∀ n → E (F n) (F′ n)) → E (lim (cum F)) (lim (cum F′))
E-cum F F′ h = el go
  where
  go : ∀ n → E (cum F n) (cum F′ n)
  go zero    = h zero
  go (suc n) = E-+ (go n) (h (suc n))

E→≅ : ∀ {a b} → E a b → read a L.≅ read b
E→≅ ez     = L.z≅
E→≅ (es e) = L.s≅ (E→≅ e)
E→≅ (el h) = L.l≅ (λ n → E→≅ (h n))
```

## 2 目标是第 0 层: `ψs` 与 `ψ⊥`

路径只经 `ins`, `inlu`, `inu` (`lift` 的形状) 时, `up` 的每一行都交给孩子层, 没有回退; 结点在第 0 层没有槽位可保留, 两边都是链的部分和.

```agda
LiftP : ∀ {j ℓ} → j ≤ ℓ → Set
LiftP self      = ⊤
LiftP (ins w)   = LiftP w
LiftP (inl n w) = ⊥
LiftP (inlu ws) = ∀ n → LiftP (ws n)
LiftP (ink w)   = ⊥
LiftP (inb c w) = ⊥
LiftP (inu ws)  = ∀ c → LiftP (ws c)

LiftP-∙ : ∀ {ℓ} (a b : LF) (w : ℓ ≤ a) → LiftP w → LiftP (w ∙ lift a b)
LiftP-∙ a zero     w lw = lw
LiftP-∙ a (suc b)  w lw = LiftP-∙ a b w lw
LiftP-∙ a (lim g)  w lw = λ n → LiftP-∙ a (g n) w lw
LiftP-∙ a (Ωₗ k h) w lw = λ c → LiftP-∙ a (h c) w lw

eq0 : (ℓ : LF) (ε : Ev ℓ) (B : Base ℓ) (w : zero ≤ ℓ) → LiftP w → (β : Tr zero) → E β (b⊥ B)
    → (x : Tr ℓ) → E (ψs ℓ ε B zero w β x) (ψ⊥ ℓ ε B x)
eq0 ℓ ε B w lw β e zero    = e
eq0 ℓ ε B w lw β e (suc x) = E-next (eq0 ℓ ε B w lw β e x)
eq0 ℓ ε B w lw β e (lim f) = el (λ n → eq0 ℓ ε B w lw β e (f n))
eq0 ℓ ε B w lw β e (Ω p g) =
  kp-ind ℓ ε p w (λ X → E X (ψ⊥ ℓ ε B (Ω p g))) (λ ())
    (E-cum _ _ (λ n → eq0 ℓ ε B w lw β e (g _)))
eq0 zero     ε B w         lw β e (up x () y)
eq0 (suc a)  ε B (ins w)   lw β e (up x _ y) =
  eq0 a ε (dS a ε B x) w lw _ (eq0 (suc a) ε B (ins w) lw β e x) y
eq0 (lim g)  ε B (inlu ws) lw β e (up x m y) =
  eq0 (g m) (ε m) (dL g ε B m x) (ws m) (lw m) _ (eq0 (lim g) ε B (inlu ws) lw β e x) y
eq0 (Ωₗ k h) ε B (inu ws)  lw β e (up x c y) =
  eq0 (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (ws c) (lw c) _ (eq0 (Ωₗ k h) ε B (inu ws) lw β e x) y
```

## 3 这一站的形状

```agda
εh : (x : Tr zero) → Ev (h₁ x)
εh x = proj₂ (proj₂ (Ev-tw 1) x)

wh : (x : Tr zero) → zero ≤ h₁ x
wh x = self ∙ lift zero (↑ zero x)

G′ : Tr zero → Tr zero
G′ x = ψ₀ (h₁ x) (εh x) (Ωt (h₁ x))

K : Tr zero → Tr zero
K x = ψs (h₁ x) (εh x) (B₀ (h₁ x)) zero (wh x) (suc zero) (Ωt (h₁ x))

pt′ : ℕ → Tr zero
pt′ = iter K zero

Tw1′ : Tr zero
Tw1′ = ψ₀ (tw 1) (Ev-tw 1) (Ωt (tw 1))

Tw1′-form : Tw1′ ≡ lim (cum (λ n → G′ (pt′ n)))
Tw1′-form = refl

KG : (x : Tr zero) → read (K x) L.≅ read (G′ x)
KG x = E→≅ (eq0 (h₁ x) (εh x) (B₀ (h₁ x)) (wh x) (LiftP-∙ zero (↑ zero x) self tt) (suc zero) (es ez) (Ωt (h₁ x)))

G′-leg : (x : Tr zero) → Leg zero (G′ x)
G′-leg x = ψ₀-leg (h₁ x) (εh x) (Ωt (h₁ x)) (Ωt-leg (h₁ x))

K-leg : (x : Tr zero) → Leg zero (K x)
K-leg x = proj₁ (press (h₁ x) (εh x) (B₀ (h₁ x)) (LegB₀ (h₁ x)) zero (wh x) (suc zero) (tt , ◃s)
  (Ωt (h₁ x)) (Ωt-leg (h₁ x)))

pt′-leg : ∀ m → Leg zero (pt′ m)
pt′-leg zero    = tt
pt′-leg (suc m) = K-leg (pt′ m)

lvl : (x : Tr zero) → Leg zero x → L.Ordᴵ
lvl x l = L.toLevel (read x) (HS-read x l)

κ′ : ℕ → L.Ordᴵ
κ′ m = lvl (pt′ m) (pt′-leg m)
```

## 4 两条前提

```agda
LOWER′ : Set
LOWER′ = ∀ m → L.ψ⁰ (L.Ω (κ′ m)) ≼ read (G′ (pt′ m))

V3F′ : Set
V3F′ = ∀ m → WT.Eb (ordᴰ (cp (pt′ m))) (read (G′ (pt′ m)))

LOWER′-0 : L.ψ⁰ (L.Ω (κ′ 0)) ≼ read (G′ (pt′ 0))
LOWER′-0 = next≽ (suc zero) (≼-refl (L.suc L.zero))

V3F′-0 : WT.Eb (ordᴰ (cp (pt′ 0))) (read (G′ (pt′ 0)))
V3F′-0 = WT.Eb-zero
```

## 5 链与下界 (条件定理)

与 `YiFreshValTw1.Chain` 同形; 平移一步换成 `KG` (下一个链点与折叠值读回 `≅`, 不再是 1 + 折叠值).

```agda
shift′ : ∀ x → PEmb (L.toLevel (read (G′ x)) (HS-read (G′ x) (G′-leg x))) (lvl (K x) (K-leg x))
shift′ x = PS.PEmb-≅ʳ (PEmb-⊑ L.⊑ᴵ-refl)
  (L.toLevel-≅ (HS-read (G′ x) (G′-leg x)) (HS-read (K x) (K-leg x)) (L.≅-sym (KG x)))

module Chain (low : LOWER′) (v3 : V3F′) where
  emb : ∀ n m → D.γ n ≼ read (pt′ m) → PEmb (D.L n) (κ′ (suc m))
  emb n m w =
    PEmb-∘ (PW₃ (V1 (SV-L n)))
    (PEmb-∘ (PW₁ (V2′ (bkᴵ (N.L n)) (cp η) (St-bk (SV-L n)) (Mono-cp η l) w′))
    (PEmb-∘ (PW₂ (HS-read (G′ η) (G′-leg η)) (v3 m))
            (shift′ η)))
    where
    η = pt′ m
    l = pt′-leg m
    w′ : tr₀ (bkᴵ (N.L n)) ≼ tr₀ (cp η)
    w′ = ≼-trans (≅→≼ (bk≅γ n)) (≼-trans w (≅→≼ (L.≅-sym (cp≅ η))))
      where open import OCF.Lean.YiFreshValTw1 using (cp≅)

  lowc : ∀ k → L.ψ⁰ (L.Ω (κ′ k)) ≼ read (pt′ (suc k))
  lowc k = ≼-trans (low k) (≅→≼ (L.≅-sym (KG (pt′ k))))

  chainV : ∀ n → Σ ℕ (λ m → D.γ n ≼ read (pt′ m))
  chainV zero    = 1 , ≼l 0 (≼-refl (L.suc L.zero))
  chainV (suc n) = suc (suc m) , ≼-trans (Ψ-emb (emb n m w)) (lowc (suc m))
    where
    m = proj₁ (chainV n)
    w = proj₂ (chainV n)

  btbo : D.BTBOᴵ ≼ read Tw1′
  btbo = l≼ (λ n → ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n))))
    (limcum≽ (λ k → G′ (pt′ k)) (suc (proj₁ (chainV n))) (low (suc (proj₁ (chainV n))))))

btbo-tw1′ : LOWER′ → V3F′ → D.BTBOᴵ ≼ read Tw1′
btbo-tw1′ low v3 = Chain.btbo low v3
```

## 6 m = 1 处的 Ω₂ 分量与 `Tw1′` 的 ψ₀(Ω₂) 下界 (无前提)

链点 `pt′ 1` 是 ω, 层号 `h₁ (pt′ 1)` 是 ℕ 极限 `lim g₁`, 第 1 项是层号 2. `G′ (pt′ 1)` 的第 1 分量是层号 2 的 Ω 树的折叠, 底 `Bc` 来自第 0 分量 (经回退行, 是 `B₀` 的各分量右加一棵第 0 层的树); 它满足 `At` 的四条.

```agda
g₁ : ℕ → LF
g₁ n = zero ⊕ ↑ zero (iter (suc zero +_) (suc zero) n)

lv-pt1 : h₁ (pt′ 1) ≡ lim g₁
lv-pt1 = refl

Bc : Base two
Bc = dL g₁ (εh (pt′ 1)) (B₀ (lim g₁)) 1 (up zero 0 (Ωt one))

c₁ : Tr zero
c₁ = ψ⊥ one tt (B₀ one) (Ωt one)

Bc-one : bs Bc one (ins self) ≡ Ωt one + ι one c₁
Bc-one = refl

+ι⊴ : ∀ {j} (b : Tr j) (c : Tr zero) → j ⊢ b ⊴ b + ι j c
+ι⊴ b zero    = ⊴r
+ι⊴ b (suc c) = ⊴◃ (⊴-◃ (+ι⊴ b c) ◃s)
+ι⊴ b (lim f) = ⊴◃ (⊴-◃ (+ι⊴ b (f zero)) (◃l zero))
+ι⊴ b (Ω () _)
+ι⊴ b (up _ () _)

⊥1-⊵ : (B : Base one) (t : Tr one) → zero ⊢ b⊥ B ⊴ ψ⊥ one tt B t
⊥1-⊵ B zero       = ⊴r
⊥1-⊵ B (suc t)    = ⊴◃ (⊴-◃ (⊥1-⊵ B t) (◃l zero))
⊥1-⊵ B (lim f)    = ⊴◃ (⊴-◃ (⊥1-⊵ B (f zero)) (◃l zero))
⊥1-⊵ B (Ω p g)    = ⊴◃ (⊴-◃ (⊥1-⊵ B (g (fromBr one p zero))) (◃l zero))
⊥1-⊵ B (up t _ c) = ⊴-trans (⊥1-⊵ B t) (⊥0-⊵ (dS zero tt B t) c)

low1-Ω₂ : L.ψ⁰ (L.Ω I2) ≼ read (G′ (pt′ 1))
low1-Ω₂ = ≼l 1 (At.lower2 Bc
  (s-⊴ Sβ₀ (+ι⊴ (Ωt one) c₁))
  (◃-⊴ (Ωt-nz one) (+ι⊴ (Ωt one) c₁))
  (+ι⊴ (suc zero) c₁)
  (⊴→≼ (⊥1-⊵ (dL g₁ (εh (pt′ 1)) (B₀ (lim g₁)) 0 zero) (Ωt one))))

bho-tw1 : L.ψ⁰ (L.Ω I2) ≼ read Tw1′
bho-tw1 = limcum≽ (λ k → G′ (pt′ k)) 1 low1-Ω₂
```
