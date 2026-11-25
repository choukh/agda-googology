# 诊断：上界 (V122): 最小见证的底 β₁ 在 BTBO 之上的链点取值

> 诊断：上界, 不进成品, F2 块, 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. 见证 `up β two (Ωt 2)` 的折叠 `V` 不低于第 1 层底 β₁ 的结点行 `G (ch n)` (`row≼V`); 链点 `ch 1` 严格高于底的第 0 层分量 `E₀` (`E₀◃c₁`), 而 `E₀` 不低于 BTBO 的参照 (`btbo≼E₀`, `btbo≺c₁`).
> 于是 `V` 不低于 Level 在 `lvl (ch 1)` 上的 ψ⁰(Ω) (`lvl≼V`), 也不低于在 `E₀` 的层号的后继上的 (`naive≼V`). 这一族下界是 V122 上界的第一个障碍: 要证上界, 必须给这些行一个不高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照的界.
> 不否定 V122 的上界 (没有 Level 与记号参照之间的桥). 参照的读法与判断在回报里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDropRow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read; read-+; plus≽; limcum≽; ◃→≺; HSr; ⊴-◃)
open import OCF.Lean.YiLSFold using (ψs-⊵)
open import OCF.Lean.YiLSTw1 using (h₁; G; G-nz; pt; lvl; lower-↑)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiT2Frame using (ε¹; ρ¹; β; one; two)
open import OCF.Lean.YiInv using (L1; BW1; zz)
open import OCF.Lean.YiCeilRead using (stp⊥)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; ≺→s≼)
  renaming (+-mono to +ᵛ-mono)
open import OCF.Align.YiBtValBT using (module D)
```

## 见证, 底的两个分量, 结点行的链

`BW1` 是孩子 one 的底, 与孩子 two 在 `up zero tt …` 之后的底逐字相同 (`YiInv.base-same`). 第 0 层分量 `E₀` 是 β 用回退行折到第 0 层; 第 1 层分量 β₁ 是结点, 分支 c 上是 `Ωt 1 + ι 1 (G c)`.

```agda
Wit : Tr (tw 1)
Wit = up β two (Ωt (h₁ two)) (Ωt-nz (h₁ two))

V : Tr zero
V = ψ₀ (tw 1) ε¹ ρ¹ Wit

E₀ : Tr zero
E₀ = bs BW1 zero (ins self)

nE₀ : zero ⊢ zero ◃ E₀
nE₀ = ns BW1 zero (ins self)

β₁ : Tr L1
β₁ = bs BW1 L1 self

g₁ : Tr zero → Tr L1
g₁ c = Ωt L1 + ι L1 (G c)

ch : ℕ → Tr zero
ch = stp⊥ L1 tt tt BW1 (inj₁ tt) g₁

c₁ : Tr zero
c₁ = ch 1
```

定义的展开 (有限测试, `refl`).

```agda
β₁-form : β₁ ≡ Ω (inj₁ tt) g₁
β₁-form = refl

ch-step : ∀ n → ch (suc n) ≡ ψs L1 tt tt BW1 zero (ins self) E₀ nE₀ (g₁ (ch n))
ch-step n = refl

zz1-form : zz 1 ≡ next β₁ (ns BW1 L1 self)
zz1-form = refl

b⊥-form : b⊥ BW1 ≡ twᶜ 1
b⊥-form = refl

E₀-row : ∀ c → ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (inb one (ins self)) (Ωt zero) (Ωt-nz zero)
                 (up zero c (Ωt (h₁ c)) (Ωt-nz (h₁ c)))
             ≡ Ωt zero + ι zero (G c)
E₀-row c = refl
```

## 读回的小引理

```agda
suc≼next : (b : Tr zero) (nz : zero ⊢ zero ◃ b) {Y : T₀} → Y ≼ read b → L.suc Y ≼ read (next b nz)
suc≼next b nz q = ≼l 1 (≼-trans (+ᵛ-mono q (≺→s≼ (◃→≺ nz))) (≅→≼ (L.≅-sym (read-+ b b))))

ι₀≅ : (y : Tr zero) → read (ι zero y) L.≅ read y
ι₀≅ zero          = L.z≅
ι₀≅ (suc y)       = L.s≅ (ι₀≅ y)
ι₀≅ (lim f a)     = L.l≅ (λ n → ι₀≅ (f n))
ι₀≅ (Ω () _)
ι₀≅ (up _ () _ _)

cum≼cum : (F F′ : ℕ → Tr zero) → (∀ n → read (F n) ≼ read (F′ n)) → ∀ n → read (cum F n) ≼ read (cum F′ n)
cum≼cum F F′ h zero    = h zero
cum≼cum F F′ h (suc n) =
  ≼-trans (≅→≼ (read-+ (cum F n) (F (suc n))))
  (≼-trans (+ᵛ-mono (cum≼cum F F′ h n) (h (suc n))) (≅→≼ (L.≅-sym (read-+ (cum F′ n) (F′ (suc n))))))

limc≼cum : (F F′ : ℕ → Tr zero) (nz : (n : ℕ) → zero ⊢ zero ◃ F n)
  → (∀ n → read (F n) ≼ read (F′ n)) → read (limc F nz) ≼ L.lim (λ n → read (cum F′ n))
limc≼cum F F′ nz h = l≼ (λ n → ≼l n (cum≼cum F F′ h n))
```

第 1 层的树右加一棵嵌入的可数树 y, 折到第 0 层后不低于 y (对一切底).

```agda
ιrow : (x : Tr L1) (B : Base L1) (y : Tr zero) → read y ≼ read (ψ⊥ L1 tt tt B (x + ι L1 y))
ιrow x B zero          = z≼
ιrow x B (suc y)       = suc≼next (ψ⊥ L1 tt tt B (x + ι L1 y)) (nz⊥ L1 tt tt B (x + ι L1 y)) (ιrow x B y)
ιrow x B (lim f a)     = l≼ (λ n → ≼l n (ιrow x B (f n)))
ιrow x B (Ω () _)
ιrow x B (up _ () _ _)
```

## 底的第 0 层分量在 BTBO 之上, 链点在它之上

`E₀` 的各行是 `1 + G (pt n)`, 塔第 1 项的各行是 `G (pt n)` (`YiLSTw1.tw1-form`).

```agda
tw1≼E₀ : read (twᶜ 1) ≼ read E₀
tw1≼E₀ = limc≼cum (λ n → G (pt n)) (λ n → Ωt zero + ι zero (G (pt n))) (λ n → G-nz (pt n))
  (λ n → plus≽ (Ωt zero) (ι zero (G (pt n))) (≅→≼ (L.≅-sym (ι₀≅ (G (pt n))))))

btbo≼E₀ : D.BTBOᴵ ≼ read E₀
btbo≼E₀ = ≼-trans btbo-tw1 tw1≼E₀

E₀◃c₁ : zero ⊢ E₀ ◃ c₁
E₀◃c₁ = ⊴-◃ (ψs-⊵ L1 tt tt BW1 zero (ins self) E₀ nE₀ (Ωt L1))
            (monos L1 tt tt BW1 zero (ins self) E₀ nE₀ (+-mono (Ωt L1) (ι-mono L1 (G-nz zero))))

btbo≺c₁ : L.suc D.BTBOᴵ ≼ read c₁
btbo≺c₁ = ≼-trans (s≼s btbo≼E₀) (≺→s≼ (◃→≺ E₀◃c₁))
```

## 结点行进入见证的值

β₁ 的折叠是行 `ψ⊥ (g₁ (ch n))` 的部分和的极限; `zz 1 = next β₁`; 见证的值是 `ψ⊥ (suc (zz n))` 的部分和的极限 (`YiInv.lhs-form`).

```agda
G≼β₁ : ∀ n → read (G (ch n)) ≼ read (ψ⊥ L1 tt tt BW1 β₁)
G≼β₁ n = limcum≽ (λ k → ψ⊥ L1 tt tt BW1 (g₁ (ch k))) (λ k → nz⊥ L1 tt tt BW1 (g₁ (ch k))) n
  (ιrow (Ωt L1) BW1 (G (ch n)))

β₁≼V : read (ψ⊥ L1 tt tt BW1 β₁) ≼ read V
β₁≼V = limcum≽ (λ n → ψ⊥ L1 tt tt BW1 (suc (zz n))) (λ n → nz⊥ L1 tt tt BW1 (suc (zz n))) 1
  (≼l 0 (≼l 0 (≼-refl (read (ψ⊥ L1 tt tt BW1 β₁)))))

row≼V : ∀ n → read (G (ch n)) ≼ read V
row≼V n = ≼-trans (G≼β₁ n) β₁≼V
```

## Level 的下界

`lower-↑` (对一切第 0 层的树) 在链点 `c₁` 上; `E₀ ◃ c₁` 给出层号的严格前驱, 所以也不低于 `E₀` 的层号的后继上的 ψ⁰(Ω).

```agda
lvl≼V : L.ψ⁰ (L.Ω (lvl c₁)) ≼ read V
lvl≼V = ≼-trans (lower-↑ c₁) (row≼V 1)

naive≼V : L.ψ⁰ (L.Ω (L.suc (lvl E₀))) ≼ read V
naive≼V = ≼-trans (⊑→≼ (L.ψ⁰ (L.Ω (L.suc (lvl E₀))))
                       (L.Ψ⁰-mono (L.s⊑′ (L.toLevel-≺ (HSr E₀) (HSr c₁) (◃→≺ E₀◃c₁)))))
                  lvl≼V
```
