# 带表的那一行在塔第 1 项顶层的值: 目标第 0 层, 孩子是 ℕ 极限

> 验收文件 (F2 对照块 [YiVTFold](YiVTFold.lagda.md) 上), 不进成品. 编译定理, 无前提 (新写, 不是照搬): 层号 `tw 1`, 目标第 0 层经孩子 c (c 字面是 ℕ 极限), 对一切底 B, 起点 b, 路径 w, 树 "左项为零, 分支 x 上嵌 `Ωt (h₁ x)`" 的那一行不低于标准底的 `G x` (`rowG`).
> x 字面是零时表给 "把 1 沿 `z≤ᶠ` 嵌进孩子 c 的层再折", 没有 Ω 形状的层号上嵌入的 1 朝第 0 层的折叠逐字是 `next b` (`em-fold`); x 是后继或 ℕ 极限时表里没有条目, 是原行 `b + ι (G x)`.
> 不给出什么: 孩子 c 字面是零或后继的情形, 目标不是第 0 层的情形. 用处: `YiVTEVTw2.compβ`, [YiVTHi](YiVTHi.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTEmb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inl; inlu; inb; _∙_; Ev; Rt; Ev-tw; Rt-tw; way; caseW-ind; emb; emb-nz)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read; read-+; plus≽; ◃→≺)
open import OCF.Lean.YiVTLSFold using (NL; n0; n+; nω)
open import OCF.Lean.YiVTLSTw1 using (h₁; G; nl-↑)
open import OCF.Lean.YiVTT2Frame using (IsLim)
open import OCF.Lean.YiDropRow using (ι₀≅)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ≺→s≼) renaming (+-mono to +ᵛ-mono)
```

## 嵌入的 1 朝第 0 层的折叠

`Em1 ℓ t`: t 是 1 经若干次嵌入到层号 ℓ 的树. 没有 Ω 形状的层号 (`NL`) 上, 它朝第 0 层的折叠沿任何路径、对任何底都是 `next b`.

```agda
data Em1 : (ℓ : LF) → Tr ℓ → Set where
  e0 : Em1 zero (suc zero)
  eS : ∀ {a y e} → Em1 a y → Em1 (suc a) (up zero tt y e)
  eL : ∀ {g} n {y e} → Em1 (g n) y → Em1 (lim g) (up zero n y e)

emb-Em : ∀ {ℓ} → NL ℓ → (ε : Ev ℓ) → ∀ {k} (v : k ≤ ℓ) {y nz} → Em1 k y → Em1 ℓ (emb ℓ ε v y nz)
emb-Em f      ε self      em = em
emb-Em (n+ f) ε (ins v)   em = eS (emb-Em f ε v em)
emb-Em (nω f) ε (inl n v) em = eL n (emb-Em (f n) (ε n) v em)
emb-Em (nω f) ε (inlu vs) em = eL zero (emb-Em (f zero) (ε zero) (vs zero) em)

em-fold : ∀ {ℓ} → NL ℓ → ∀ {t} → Em1 ℓ t → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (w : zero ≤ ℓ)
  (b : Tr zero) (nb : zero ⊢ zero ◃ b) → ψs ℓ ε ρ B zero w b nb t ≡ next b nb
em-fold n0     e0      ε ρ B self    b nb = refl
em-fold (n+ f) (eS em) ε ρ B (ins w) b nb = em-fold f em ε ρ _ w b nb
em-fold (nω f) (eL n em) ε (ρc , R) B (inlu ws) b nb = em-fold (f n) em (ε n) (ρc n) _ (ws n) b nb
em-fold (nω f) (eL {g} n em) ε (ρc , R) B (inl m w) b nb =
  caseW-ind (λ Z → Z ≡ next b nb) (way g R n m)
    (λ v → em-fold (f m) (emb-Em (f m) (ε m) v em) (ε m) (ρc m) _ w b nb)
    (λ v → em-fold (f n) em (ε n) (ρc n) _ (w ∙ v) b nb)
```

## `next` 对非零的底不降

```agda
next1≼ : (b : Tr zero) (nb : zero ⊢ zero ◃ b) → read (next (suc zero) ◃s) ≼ read (next b nb)
next1≼ b nb = l≼ (λ n → ≼l n (it n))
  where
  it : ∀ n → read (iter (suc zero +_) (suc zero) n) ≼ read (iter (b +_) b n)
  it zero    = ≺→s≼ (◃→≺ nb)
  it (suc n) = ≼-trans (≅→≼ (read-+ (suc zero) (iter (suc zero +_) (suc zero) n)))
    (≼-trans (+ᵛ-mono (≺→s≼ (◃→≺ nb)) (it n)) (≅→≼ (L.≅-sym (read-+ b (iter (b +_) b n)))))
```

## 那一行

```agda
rowT : (B : Base (tw 1)) (c : Tr zero) (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b) (x : Tr zero) → Tr zero
rowT B c w b nb x = ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (inb c w) b nb (up zero x (Ωt (h₁ x)) (Ωt-nz (h₁ x)))

rowG : (B : Base (tw 1)) (c : Tr zero) → IsLim c → (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b) (x : Tr zero)
  → read (G x) ≼ read (rowT B c w b nb x)
rowG B c@(lim f a) tt w b nb zero =
  subst (λ Z → read (G zero) ≼ read Z)
    (sym (em-fold (nl-↑ c) (emb-Em (nl-↑ c) (proj₂ (proj₂ (Ev-tw 1) c)) (z≤ᶠ (h₁ c)) e0)
            (proj₂ (proj₂ (Ev-tw 1) c)) (proj₂ (Rt-tw 1) c) _ w b nb))
    (next1≼ b nb)
rowG B (lim f a) tt w b nb (suc x)   = plus≽ b (ι zero (G (suc x))) (≅→≼ (L.≅-sym (ι₀≅ (G (suc x)))))
rowG B (lim f a) tt w b nb (lim g d) = plus≽ b (ι zero (G (lim g d))) (≅→≼ (L.≅-sym (ι₀≅ (G (lim g d)))))
rowG B (lim f a) tt w b nb (Ω () _)
rowG B (lim f a) tt w b nb (up _ () _ _)
```
