# 验收: `G` 对记号的关系式下界 (加法型), 与 V130 的归约

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 对一切第 0 层的树: `G-low : M⁰ (ψ₀ᵗ t) (G c₀) → M⁰ η y → M⁰ (ψ₀ᵗ (t ++ η)) (G (c₀ + y))`, 对 `M⁰ η y` 的零, 后继, 极限, 松弛四种情形都成立; 实例 `G-lowE` (c₀ 取见证的底的第 0 层分量 `E₀`, t 取 Ω_Ω).
> 强度只是界: `G (c₀ + y)` 不低于 ψ₀(t+η), 不是 ψ₀(Ω_Ω+ψ₁(Ω_η)). V130 没有证出; 条件定理 `tower→V130`: 前提 `Tower` (tA 的每个基本列项对着 `G (suc E₀)`) 推出 `L.suc (Rt hA) ≼ readRW Vᴿ`. `Tower` 没有证也没有否定.
> 用到 [YiG0Mono](YiG0Mono.lagda.md) 的 `G-mono`. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiG0Low where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins)
open import OCF.Lean.YiLegFold
import OCF.Align.EboLeanDef as E
open E using (HC; cof; c1; cω; pred; fsn; ψ)
import OCF.Align.Level as O
import OCF.Align.Value as V
open V using (_≼_)
open import OCF.Lean.YiMEBase
open import OCF.Lean.YiMENote
open import OCF.Lean.YiMEAnchor using (ψ₀ᵗ; u₀; ++[]; module G⁰)
open import OCF.Lean.YiMWPre using (M⁰-≼)
open import OCF.Lean.YiMWLow using (rd≼; rd≽; sem0; tΩ)
import OCF.Lean.YiLSRead as S
open import OCF.Lean.YiLSTw1 using (h₁; εh; ρh; G)
open import OCF.Lean.YiG0Mono using (G-mono)
open import OCF.Lean.YiInv using (L1; BW1)
import OCF.Lean.YiDropRow as DR
open import OCF.Lean.YiDropRW using (Vᴿ; V-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
open import OCF.Lean.YiNFOCase using (tA; hA)
import OCF.Lean.YiRefTw2 as R2
```

## 后继孩子: `G (suc x)` 的形状

层号 `h₁ (suc x)` 是后继层号; 它的 Ω 树的折叠是 `h₁ x` 层上 `suc (zs x n)` 的折叠的部分和极限 (`formS`, `refl`), 链 `zs x` 从零起, 每步是自身行的折叠再取 `next`. 第 1 项 `zs x 1 = next (Ωt (h₁ x))` 的第一位置是 `Ωt (h₁ x)`, 所以 `G x` 在第 1 行之下 (`G◃z1`).

```agda
zs : (x : Tr zero) → ℕ → Tr (h₁ x)
zs x = iter (λ z → next (ψs (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (h₁ x) self (Ωt (h₁ x)) (Ωt-nz (h₁ x)) z)
                        (nzs (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (h₁ x) self (Ωt (h₁ x)) (Ωt-nz (h₁ x)) z)) zero

rowS : (x : Tr zero) → ℕ → Tr zero
rowS x n = ψ⊥ (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (suc (zs x n))

nzS : (x : Tr zero) (n : ℕ) → zero ⊢ zero ◃ rowS x n
nzS x n = nz⊥ (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (suc (zs x n))

formS : (x : Tr zero) → G (suc x) ≡ limc (rowS x) (nzS x)
formS x = refl

G◃z1 : (x : Tr zero) → zero ⊢ G x ◃ ψ⊥ (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (zs x 1)
G◃z1 x = mono⊥ (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (◃l zero)

G-strict : (x : Tr zero) → O.suc (S.read (G x)) ≼ S.read (G (suc x))
G-strict x = S.limcum≽ (rowS x) (nzS x) 1 (V.≼l 0 (V.≺→s≼ (S.◃→≺ (G◃z1 x))))
```

记号一侧: 余尾 ω 且基本列是 p·n 的项 s (规则 4 的形状) 对着 `G (suc x)`, 只要 p 对着 `G x`.

```agda
G-suc : ∀ {s p} (x : Tr zero) → cof s ≡ cω → (∀ n → fsn s n ≡ replicate n p)
      → M⁰ (p ∷ []) (G x) → M⁰ s (G (suc x))
G-suc x e q m =
  G⁰.m-cum (rowS x) (nzS x) 1
    (G⁰.m-next (nz⊥ (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (zs x 1)) e q (mw m (G◃z1 x)))
```

## 松弛与膨胀

`G-mono` 给读回的 `≼`; 第 0 层的关系对读回的 `≼` 向上封闭 (`YiMWPre.M⁰-≼`), 所以关系沿孩子的第一位置序搬运 (`G-mw`). `G y` 不低于 y (`G-infl`).

```agda
monoᴹ : {x y : Tr zero} → zero ⊢ x ◃ y → read (G x) ≼ read (G y)
monoᴹ {x} {y} d = V.≼-trans (rd≼ (G x)) (V.≼-trans (G-mono d) (rd≽ (G y)))

G-mw : ∀ {s} {x x′ : Tr zero} → M⁰ s (G x) → zero ⊢ x ◃ x′ → M⁰ s (G x′)
G-mw {x′ = x′} m d = M⁰-≼ m (G x′) (monoᴹ d)

G-m⊴ : ∀ {s} {x x′ : Tr zero} → M⁰ s (G x) → x ⊴ x′ → M⁰ s (G x′)
G-m⊴ m ⊴r     = m
G-m⊴ m (⊴◃ d) = G-mw m d

G-infl : (y : Tr zero) → S.read y ≼ S.read (G y)
G-infl zero          = V.z≼
G-infl (suc y)       = V.≼-trans (V.s≼s (G-infl y)) (G-strict y)
G-infl (lim f a)     = V.l≼ (λ n → V.≼-trans (G-infl (f n)) (G-mono (◃l {f = f} {a = a} n)))
G-infl (Ω () _)
G-infl (up _ () _ _)
```

## 一般引理 (加法型)

对 `M⁰ η y` 归纳. 零: 松弛到 `c₀ + y`. 后继: 规则 4, `G-suc`. 极限: 规则 5, 逐项. 松弛: `G-mw`. 量化域: 一切第 0 层的树 c₀, y 与一切前缀 t.

```agda
G-low : ∀ {t} (c₀ : Tr zero) → M⁰ (ψ₀ᵗ t) (G c₀) → ∀ {η y} → M⁰ η y → M⁰ (ψ₀ᵗ (t ++ η)) (G (c₀ + y))
G-low {t} c₀ m (mz {x = y}) = ++[] (λ s → M⁰ (ψ₀ᵗ s) (G (c₀ + y))) t (G-m⊴ m (+⊴ c₀ y))
G-low {t} c₀ m (m1 {t = η} {x = y} e r) =
  G-suc (c₀ + y) (cofψ1 u₀ (t ++ η) (cof++1 t η e))
    (λ n → trans (fsnψ1 u₀ (t ++ η) n (cof++1 t η e)) (cong (λ s → replicate n (ψ u₀ s)) (pred++ t η e)))
    (G-low c₀ m r)
G-low {t} c₀ m (mL {t = η} {x = y} e h) =
  mL (cofψω u₀ (t ++ η) (cof++ω t η e))
    (λ n → subst (λ s → M⁰ s (G (c₀ + y)))
      (sym (trans (fsnψω u₀ (t ++ η) n (cof++ω t η e)) (cong ψ₀ᵗ (fsn++ t η n e))))
      (G-low c₀ m (h n)))
G-low c₀ m (mΩ {p = ()} _ _ _)
G-low c₀ m (mU {c = ()} _ _)
G-low c₀ m (mw r d) = G-mw (G-low c₀ m r) (+-mono c₀ d)
```

实例 (前提可满足): c₀ 取最小见证的底的第 0 层分量 `E₀`; 它不低于 BTBO 的参照 (`YiDropRow.btbo≼E₀`), `G` 膨胀, 所以 ψ₀(Ω_Ω) 对着 `G E₀`.

```agda
mE₀ : M⁰ (ψ₀ᵗ tΩ) (G DR.E₀)
mE₀ = sem0 (G DR.E₀) (V.≼-trans DR.btbo≼E₀ (G-infl DR.E₀))

G-lowE : ∀ {η y} → M⁰ η y → M⁰ (ψ₀ᵗ (tΩ ++ η)) (G (DR.E₀ + y))
G-lowE = G-low DR.E₀ mE₀
```

## V130 的归约

链点 `c₁` 之下字面地有 `suc (suc E₀)`: `c₁` 的第一位置依次是 `next P₁`, `P₁`, `next E₀`, 它的第 1 项 `E₀ + E₀`, 而 `E₀` 之下有 2.

```agda
one◃G0 : zero ⊢ suc zero ◃ G zero
one◃G0 = ◃l zero

two◃E₀ : zero ⊢ suc (suc zero) ◃ DR.E₀
two◃E₀ = ◃t (◃l zero) (◃l zero)

P₁ : Tr zero
P₁ = ψs L1 tt tt BW1 zero (ins self) DR.E₀ DR.nE₀ (Ωt L1)

s1 : zero ⊢ suc (suc DR.E₀) ◃ DR.E₀ + DR.E₀
s1 = +-mono DR.E₀ two◃E₀

s2 : zero ⊢ DR.E₀ + DR.E₀ ◃ next DR.E₀ DR.nE₀
s2 = ◃l 1

s3 : zero ⊢ next DR.E₀ DR.nE₀ ◃ P₁
s3 = monos L1 tt tt BW1 zero (ins self) DR.E₀ DR.nE₀ (◃w {p = inj₁ tt} {g = λ c → up zero tt (suc c) (z◃s c)})

s4 : zero ⊢ P₁ ◃ ψs L1 tt tt BW1 zero (ins self) DR.E₀ DR.nE₀ (suc (Ωt L1))
s4 = ◃l zero

s5 : zero ⊢ ψs L1 tt tt BW1 zero (ins self) DR.E₀ DR.nE₀ (suc (Ωt L1)) ◃ DR.c₁
s5 = monos L1 tt tt BW1 zero (ins self) DR.E₀ DR.nE₀ (+-mono (Ωt L1) (ι-mono L1 one◃G0))

E₀2◃c₁ : zero ⊢ suc (suc DR.E₀) ◃ DR.c₁
E₀2◃c₁ = ◃t s1 (◃t s2 (◃t s3 (◃t s4 s5)))
```

`Tower`: tA = ψ₀(Ω_Ω+ψ₁(Ω₂)) 的第 n 个基本列项 ψ₀(Ω_Ω+ψ₁(γₙ)) 对着 `G (suc E₀)`. 由它, `G (suc E₀)` 不低于 tA 的参照; `G (suc (suc E₀))` 严格更高 (`G-strict`), 又不高于 `G c₁` (`G-mono`), 后者不高于见证的值 (`YiDropRow.row≼V`).

```agda
Tower : Set
Tower = ∀ n → M⁰ (fsn tA n) (G (suc DR.E₀))

tower→V : Tower → (h : HC tA) → O.suc (R2.Rt h) ≼ S.read DR.V
tower→V prem h =
  V.≼-trans (V.s≼s (V.≼-trans (lower⁰ (mL refl prem) h) (rd≼ (G (suc DR.E₀)))))
  (V.≼-trans (G-strict (suc DR.E₀))
  (V.≼-trans (G-mono E₀2◃c₁) (DR.row≼V 1)))

tower→V130 : Tower → (h : HC tA) → O.suc (R2.Rt h) ≼ readRW Vᴿ
tower→V130 prem h = up≼ V-R (tower→V prem h)
```
