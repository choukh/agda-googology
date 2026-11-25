# ℕ 极限层号的路线: 值 (回归)

> 验收文件. 编译定理, 无前提: 新折叠上 `bho-lower : ψ⁰(Ω₂) ≼ read (ψ₀ 2 (Ωt 2))` 与 `bho-tw1 : ψ⁰(Ω₂) ≼ read Tw1ᴸ` (塔第 1 项的闭项, 路线 `Rt-tw 1`); 即 `YiUpVal`, `YiUpValTw1` 的两条无前提下界在新折叠上仍成立 (只有下界).
> 证法: 模拟关系 `R⁰`, `S` 与不涉及折叠的引理取自 `YiUpVal`; 涉及折叠的 (`Qu`, `Vu`, `At`) 对新折叠重证, 同文多传路线.
> 不否定什么. `LOWER′` 在 m = 2 的 ω+1 分量未走通: 塔第 1 项给那一层的路线是 "没有路径" (`YiLimCheck.tw1-none`), 那一层上新折叠与 `YiUpFold` 走同样的行; 带路径的层号上的值没有做 (缺按层号统一的模拟族).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLimVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; +-mono; Ωt-nz)
open import OCF.Lean.YiFreshValRead using (T₀; read; ◃⊑; next≽; next≼; limcum≽)
open import OCF.Lean.YiFreshValTw1 using (h₁)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpCheck using (one; two; d₁)
open import OCF.Lean.YiUpVal using
  ( _⊢_⊴_; ⊴r; ⊴◃; ⊴-◃; ◃-⊴; ⊴-trans; ⊴→≼; Up-⊵; R⁰; rz; rs; rL; rw; S; S-z; S-s; S-L; S-w; S-n; S-u0; S-us; S-u
  ; r-⊴; s-⊴; r-next; r-cum; r-tr; s-next; ψ₁; Sβ₀; Pu; 𝟏; ψ₁₀; I1; I2; T₁ )
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimFold
open import OCF.Lean.YiLimLegal using (mono⊥; monos; dS; dL)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ⊑→≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 第 0 层与第 1 层上的保持 (对新折叠重证)

```agda
s0-⊵ : (B : Base zero) (b c : Tr zero) → zero ⊢ b ⊴ ψs zero tt tt B zero self b c
s0-⊵ B b zero    = ⊴r
s0-⊵ B b (suc c) = ⊴◃ (⊴-◃ (s0-⊵ B b c) (◃l zero))
s0-⊵ B b (lim f) = ⊴◃ (⊴-◃ (s0-⊵ B b (f zero)) (◃l zero))
s0-⊵ B b (Ω () _)
s0-⊵ B b (up _ () _)

⊥0-⊵ : (B : Base zero) (c : Tr zero) → zero ⊢ b⊥ B ⊴ ψ⊥ zero tt tt B c
⊥0-⊵ B zero    = ⊴r
⊥0-⊵ B (suc c) = ⊴◃ (⊴-◃ (⊥0-⊵ B c) (◃l zero))
⊥0-⊵ B (lim f) = ⊴◃ (⊴-◃ (⊥0-⊵ B (f zero)) (◃l zero))
⊥0-⊵ B (Ω () _)
⊥0-⊵ B (up _ () _)

Qu : ∀ {y c} (σ : L.Simᴵ L.zero I1) (B : Base zero) (b : Tr zero) → zero ⊢ suc zero ⊴ b → R⁰ y c
   → R⁰ (L.ψ {i = L.zero} {k = L.zero} {ℓ = I1} L.zero σ y) (ψs zero tt tt B zero self b c)
Qu σ B b ob (rz {c}) = r-⊴ (rs rz) (⊴-trans ob (s0-⊵ B b c))
Qu σ B b ob (rs r)   = r-next (Qu σ B b ob r)
Qu σ B b ob (rL h)   = rL (λ n → Qu σ B b ob (h n))
Qu σ B b ob (rw r d) = rw (Qu σ B b ob r) (monos zero tt tt B zero self b d)

Vu : ∀ {y c} (B : Base zero) → 𝟏 ≼ read (b⊥ B) → R⁰ y c → L.ψ⁰ y ≼ read (ψ⊥ zero tt tt B c)
Vu B ob (rz {c}) = ≼-trans ob (⊴→≼ (⊥0-⊵ B c))
Vu B ob (rs {c = c} r) = next≽ (ψ⊥ zero tt tt B c) (Vu B ob r)
Vu B ob (rL h)   = l≼ (λ n → Vu B ob (h n))
Vu B ob (rw {c = c} r d) =
  ≼-trans (Vu B ob r) (⊑→≼ (read (ψ⊥ zero tt tt B c)) (◃⊑ (mono⊥ zero tt tt B d)))

module At (B₂ : Base two)
  (hβ : S (L.Ω I1) (bs B₂ one (ins self)))
  (zβ : one ⊢ zero ◃ bs B₂ one (ins self))
  (h0 : zero ⊢ suc zero ⊴ bs B₂ zero (ins (ins self)))
  (h⊥ : 𝟏 ≼ read (b⊥ B₂)) where

  Bᵃ : Base one
  Bᵃ = dS one tt tt B₂ zero

  β₁ : Tr one
  β₁ = bs B₂ one (ins self)

  β₀ : Tr zero
  β₀ = bs B₂ zero (ins (ins self))

  F : Tr one → Tr one
  F t = ψs one tt tt Bᵃ one self β₁ t

  H : Tr one → Tr zero
  H t = ψs one tt tt Bᵃ zero (ins self) β₀ t

  F-⊵ : (t : Tr one) → one ⊢ β₁ ⊴ F t
  F-⊵ zero       = ⊴r
  F-⊵ (suc t)    = ⊴◃ (⊴-◃ (F-⊵ t) (◃l zero))
  F-⊵ (lim f)    = ⊴◃ (⊴-◃ (F-⊵ (f zero)) (◃l zero))
  F-⊵ (Ω p g)    = ⊴◃ (⊴-◃ (F-⊵ (g (fromBr one p zero))) ◃w)
  F-⊵ (up t _ c) = ⊴-trans (F-⊵ t) (Up-⊵ zero d₁ (F t) c)

  H-⊵ : (t : Tr one) → zero ⊢ β₀ ⊴ H t
  H-⊵ zero       = ⊴r
  H-⊵ (suc t)    = ⊴◃ (⊴-◃ (H-⊵ t) (◃l zero))
  H-⊵ (lim f)    = ⊴◃ (⊴-◃ (H-⊵ (f zero)) (◃l zero))
  H-⊵ (Ω (inj₁ tt) g) = ⊴◃ (⊴-◃ (H-⊵ (g zero)) (◃l zero))
  H-⊵ (Ω (inj₂ ()) g)
  H-⊵ (up t _ c) = ⊴-trans (H-⊵ t) (s0-⊵ (dS zero tt tt Bᵃ t) (H t) c)

  nzF : (t : Tr one) → one ⊢ zero ◃ F t
  nzF t = ◃-⊴ zβ (F-⊵ t)

  P : ∀ {x t} → S x t → S (ψ₁ x) (F t)
  P S-z        = hβ
  P (S-s {t = t} s) = s-next (P s) (nzF t)
  P (S-L h)    = S-L (λ n → P (h n))
  P (S-w s d)  = S-w (P s) (monos one tt tt Bᵃ one self β₁ d)
  P (S-n h)    = S-n (λ y c r → P (h (L.tr⁻ _ y) c (r-tr _ r)))
  P (S-u0 {t = t} s c) = s-⊴ (P s) (Up-⊵ zero d₁ (F t) c)
  P (S-us {t = t} {c = c} s) = s-next (P s) (◃-⊴ (nzF t) (Up-⊵ zero d₁ (F t) c))
  P (S-u r)    = Pu _ β₁ hβ zβ r

  wch : (T₀ → T₁) → ℕ → T₀
  wch f = iterᴸ (λ x → ψ₁₀ (f x)) (L.suc L.zero)

  vch : (Tr zero → Tr one) → ℕ → Tr zero
  vch g = iter (λ z → H (g z)) zero

  mutual
    Q : ∀ {x t} → S x t → R⁰ (ψ₁₀ x) (H t)
    Q S-z        = r-⊴ (rs rz) h0
    Q (S-s s)    = r-next (Q s)
    Q (S-L h)    = rL (λ n → Q (h n))
    Q (S-w s d)  = rw (Q s) (monos one tt tt Bᵃ zero (ins self) β₀ d)
    Q (S-n {f} {g} h) =
      rL (λ n → r-cum (λ m → H (g (vch g m))) (suc n) (Q (h (wch f n) (vch g (suc n)) (chain h n))))
    Q (S-u0 {t = t} s c) = r-⊴ (Q s) (s0-⊵ (dS zero tt tt Bᵃ t) (H t) c)
    Q (S-us s)   = r-next (Q s)
    Q (S-u r)    = Qu _ (dS zero tt tt Bᵃ zero) β₀ h0 r

    chain : ∀ {f : T₀ → T₁} {g : Tr zero → Tr one} → (∀ y c → R⁰ y c → S (f y) (g c))
          → ∀ n → R⁰ (wch f n) (vch g (suc n))
    chain {g = g} h zero    = r-⊴ (rs rz) (⊴-trans h0 (H-⊵ (g zero)))
    chain h (suc n) = Q (h _ _ (chain h n))

  V : ∀ {x t} → S x t → L.ψ⁰ x ≼ read (ψ⊥ one tt tt Bᵃ t)
  V S-z        = h⊥
  V (S-s {t = t} s) = next≽ (ψ⊥ one tt tt Bᵃ t) (V s)
  V (S-L h)    = l≼ (λ n → V (h n))
  V (S-w {t = t} s d) = ≼-trans (V s) (⊑→≼ (read (ψ⊥ one tt tt Bᵃ t)) (◃⊑ (mono⊥ one tt tt Bᵃ d)))
  V (S-n {f} {g} h) =
    l≼ (λ n → limcum≽ (λ m → ψ⊥ one tt tt Bᵃ (g (vch g m))) (suc n)
      (V (h (wch f n) (vch g (suc n)) (chain h n))))
  V (S-u0 {t = t} s c) = ≼-trans (V s) (⊴→≼ (⊥0-⊵ (dS zero tt tt Bᵃ t) c))
  V (S-us {t = t} {c = c} s) = next≽ (ψ⊥ one tt tt Bᵃ (up t tt c)) (V s)
  V (S-u r)    = Vu (dS zero tt tt Bᵃ zero) h⊥ r

  γ : ℕ → T₁
  γ = iterᴸ ψ₁ (L.Ω I1)

  z : ℕ → Tr one
  z = iter (λ c → next (F c)) zero

  form : ψ⊥ two tt tt B₂ (Ωt two) ≡ lim (cum (λ k → next (ψ⊥ one tt tt Bᵃ (z k))))
  form = refl

  sγ : ∀ n → S (γ n) (z (suc n))
  sγ zero    = S-w hβ (◃l zero)
  sγ (suc n) = S-w (P (sγ n)) (◃l zero)

  lower2 : L.ψ⁰ (L.Ω I2) ≼ read (ψ⊥ two tt tt B₂ (Ωt two))
  lower2 = l≼ (λ n → limcum≽ (λ k → next (ψ⊥ one tt tt Bᵃ (z k))) (suc n)
    (next≼ (ψ⊥ one tt tt Bᵃ (z (suc n))) (V (sγ n))))

bho-lower : L.ψ⁰ (L.Ω I2) ≼ read (ψ₀ two tt tt (Ωt two))
bho-lower = At.lower2 (B₀ two) Sβ₀ (Ωt-nz one) ⊴r (≼-refl 𝟏)
```

## 2 塔第 1 项

`Tw1ᴸ` 是 `Gᴸ (ptᴸ n)` 的部分和的极限 (`refl`). 链点 `ptᴸ 1` 是 ω, 层号是 ℕ 极限 `lim g₁`, 第 1 项是层号 2; 那里的底 `Bc` 来自第 0 分量, 路线没有路径, 经回退行 (与 `YiUpValTw1` 同文).

```agda
εh : (x : Tr zero) → Ev (h₁ x)
εh x = proj₂ (proj₂ (Ev-tw 1) x)

ρh : (x : Tr zero) → Rt (h₁ x)
ρh x = proj₂ (Rt-tw 1) x

wh : (x : Tr zero) → zero ≤ h₁ x
wh x = self ∙ lift zero (↑ zero x)

Gᴸ : Tr zero → Tr zero
Gᴸ x = ψ₀ (h₁ x) (εh x) (ρh x) (Ωt (h₁ x))

Kᴸ : Tr zero → Tr zero
Kᴸ x = ψs (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) zero (wh x) (suc zero) (Ωt (h₁ x))

ptᴸ : ℕ → Tr zero
ptᴸ = iter Kᴸ zero

Tw1ᴸ : Tr zero
Tw1ᴸ = ψ₀ (tw 1) (Ev-tw 1) (Rt-tw 1) (Ωt (tw 1))

Tw1ᴸ-form : Tw1ᴸ ≡ lim (cum (λ n → Gᴸ (ptᴸ n)))
Tw1ᴸ-form = refl

g₁ : ℕ → LF
g₁ n = zero ⊕ ↑ zero (iter (suc zero +_) (suc zero) n)

lv-pt1 : h₁ (ptᴸ 1) ≡ lim g₁
lv-pt1 = refl

Bc : Base two
Bc = dL g₁ (εh (ptᴸ 1)) (ρh (ptᴸ 1)) (B₀ (lim g₁)) 1 (up zero 0 (Ωt one))

c₁ : Tr zero
c₁ = ψ⊥ one tt tt (B₀ one) (Ωt one)

Bc-one : bs Bc one (ins self) ≡ Ωt one + ι one c₁
Bc-one = refl

+ι⊴ : ∀ {j} (b : Tr j) (c : Tr zero) → j ⊢ b ⊴ b + ι j c
+ι⊴ b zero    = ⊴r
+ι⊴ b (suc c) = ⊴◃ (⊴-◃ (+ι⊴ b c) ◃s)
+ι⊴ b (lim f) = ⊴◃ (⊴-◃ (+ι⊴ b (f zero)) (◃l zero))
+ι⊴ b (Ω () _)
+ι⊴ b (up _ () _)

⊥1-⊵ : (B : Base one) (t : Tr one) → zero ⊢ b⊥ B ⊴ ψ⊥ one tt tt B t
⊥1-⊵ B zero       = ⊴r
⊥1-⊵ B (suc t)    = ⊴◃ (⊴-◃ (⊥1-⊵ B t) (◃l zero))
⊥1-⊵ B (lim f)    = ⊴◃ (⊴-◃ (⊥1-⊵ B (f zero)) (◃l zero))
⊥1-⊵ B (Ω p g)    = ⊴◃ (⊴-◃ (⊥1-⊵ B (g (fromBr one p zero))) (◃l zero))
⊥1-⊵ B (up t _ c) = ⊴-trans (⊥1-⊵ B t) (⊥0-⊵ (dS zero tt tt B t) c)

low1-Ω₂ : L.ψ⁰ (L.Ω I2) ≼ read (Gᴸ (ptᴸ 1))
low1-Ω₂ = ≼l 1 (At.lower2 Bc
  (s-⊴ Sβ₀ (+ι⊴ (Ωt one) c₁))
  (◃-⊴ (Ωt-nz one) (+ι⊴ (Ωt one) c₁))
  (+ι⊴ (suc zero) c₁)
  (⊴→≼ (⊥1-⊵ (dL g₁ (εh (ptᴸ 1)) (ρh (ptᴸ 1)) (B₀ (lim g₁)) 0 zero) (Ωt one))))

bho-tw1 : L.ψ⁰ (L.Ω I2) ≼ read Tw1ᴸ
bho-tw1 = limcum≽ (λ k → Gᴸ (ptᴸ k)) 1 low1-Ω₂
```
