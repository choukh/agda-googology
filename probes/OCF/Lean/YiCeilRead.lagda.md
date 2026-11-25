# 上界工具 (一): 第 0 层的读回上界, 部分和的吸收, 层号 1 的 Ω 树

> 诊断：上界. 不进成品. 档: 编译定理, 无前提. 与 `YiLSRead` 的下界引理对偶: 加法, `next`, 部分和极限的读回不高于参照 (`plus≼`, `next≼`, `limc≼`, `limc≼lim`); 第 0 层的折叠不高于参照的幂 `pw` (`fold₀≼`, `folds₀≼`).
> 最小的例子: `ε₀-upper` (层号 1 的 Ω 树的折叠不高于 `OCF.Align.Level` 的 ψ⁰(Ω₁), 读作 ψ₀(Ω₁) = ε₀; 链逐项对上 `chain≼`).
> 不否定什么, 不涉及合法块在 Ω 结点层号上的值. 链的类的定理在 [YiCeilWit](YiCeilWit.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCeilRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; posW)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read; read-+)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≅→≼; ≼-suc; ≼-+ʳ; iter-≼)
  renaming (+-mono to +ᵛ-mono)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 参照一侧的算术

`mul Y n` 读作 Y·n, `ωx Y` 读作 Y·ω, `pw Y a` 读作 Y·ω^a. 只在第 0 层.

```agda
𝟏 : T₀
𝟏 = L.suc L.zero

mul : T₀ → ℕ → T₀
mul Y = iterᴸ (Y L.+_) L.zero

ωx : T₀ → T₀
ωx Y = L.lim (mul Y)

pw : T₀ → T₀ → T₀
pw Y L.zero        = Y
pw Y (L.suc a)     = ωx (pw Y a)
pw Y (L.lim f)     = L.lim (λ n → pw Y (f n))
pw Y (L.limᵢ () f)
pw Y (L.up () x)

0+≼ : (Y : T₀) → L.zero L.+ Y ≼ Y
0+≼ L.zero        = z≼
0+≼ (L.suc Y)     = s≼s (0+≼ Y)
0+≼ (L.lim f)     = l≼ (λ n → ≼l n (0+≼ (f n)))
0+≼ (L.limᵢ () f)
0+≼ (L.up () x)

assoc≼ : (a b c : T₀) → (a L.+ b) L.+ c ≼ a L.+ (b L.+ c)
assoc≼ a b L.zero        = ≼-refl (a L.+ b)
assoc≼ a b (L.suc c)     = s≼s (assoc≼ a b c)
assoc≼ a b (L.lim f)     = l≼ (λ n → ≼l n (assoc≼ a b (f n)))
assoc≼ a b (L.limᵢ () f)
assoc≼ a b (L.up () x)

mul-comm : (Y : T₀) (n : ℕ) → mul Y n L.+ Y ≼ mul Y (suc n)
mul-comm Y zero    = 0+≼ Y
mul-comm Y (suc n) = ≼-trans (assoc≼ Y (mul Y n) Y) (+ᵛ-mono (≼-refl Y) (mul-comm Y n))

mul≼ωx : (Y : T₀) (n : ℕ) → mul Y n ≼ ωx Y
mul≼ωx Y n = ≼l n (≼-refl (mul Y n))

ωx-mono : {Y Y′ : T₀} → Y ≼ Y′ → ωx Y ≼ ωx Y′
ωx-mono q = l≼ (λ n → ≼l n (iter-≼ q n))

pw-base : (Y a : T₀) → Y ≼ pw Y a
pw-base Y L.zero        = ≼-refl Y
pw-base Y (L.suc a)     = ≼-trans (pw-base Y a) (mul≼ωx (pw Y a) 1)
pw-base Y (L.lim f)     = ≼l 0 (pw-base Y (f 0))
pw-base Y (L.limᵢ () f)
pw-base Y (L.up () x)

pw-mono : {Y Y′ a a′ : T₀} → Y ≼ Y′ → a ≼ a′ → pw Y a ≼ pw Y′ a′
pw-mono {Y′ = Y′} {a′ = a′} q z≼ = ≼-trans q (pw-base Y′ a′)
pw-mono q (s≼s e)  = ωx-mono (pw-mono q e)
pw-mono q (≼l n e) = ≼l n (pw-mono q e)
pw-mono q (l≼ h)   = l≼ (λ n → pw-mono q (h n))
pw-mono q (≼i {p = ()} x ex e)
pw-mono q (i≼ {p = ()} h)
pw-mono q (≼u {r = ()} e)
pw-mono q (u≼ {r = ()} e)
```

## 读回的上界: 加法, `next`, 部分和

`limc≼`: 各项都不高于 Y 时, 部分和的极限不高于 Y·ω. `limc≼lim`: 各项不高于递增的参照列 G, 且 G 逐步吸收 (`G n`·ω 不高于 `G (n+1)`) 时, 部分和的极限不高于 `lim G`.

```agda
plus≼ : (a b : Tr zero) {A B : T₀} → read a ≼ A → read b ≼ B → read (a + b) ≼ A L.+ B
plus≼ a b p q = ≼-trans (≅→≼ (read-+ a b)) (+ᵛ-mono p q)

next≼ : (b : Tr zero) (nz : zero ⊢ zero ◃ b) {Y : T₀} → read b ≼ Y → read (next b nz) ≼ ωx Y
next≼ b nz {Y} q = l≼ (λ n → ≼l (suc n) (go n))
  where
  go : ∀ n → read (iter (b +_) b n) ≼ mul Y (suc n)
  go zero    = q
  go (suc n) = plus≼ b (iter (b +_) b n) q (go n)

cum≼ : (F : ℕ → Tr zero) (G : ℕ → T₀) → (∀ n → read (F n) ≼ G n) → (∀ n → G n ≼ G (suc n))
  → ∀ n → read (cum F n) ≼ mul (G n) (suc n)
cum≼ F G h m zero    = h zero
cum≼ F G h m (suc n) =
  ≼-trans (plus≼ (cum F n) (F (suc n)) (≼-trans (cum≼ F G h m n) (iter-≼ (m n) (suc n))) (h (suc n)))
          (mul-comm (G (suc n)) (suc n))

limc≼lim : (F : ℕ → Tr zero) (nz : (n : ℕ) → zero ⊢ zero ◃ F n) (G : ℕ → T₀)
  → (∀ n → read (F n) ≼ G n) → (∀ n → G n ≼ G (suc n)) → (∀ n → ωx (G n) ≼ G (suc n))
  → read (limc F nz) ≼ L.lim G
limc≼lim F nz G h m ab =
  l≼ (λ n → ≼l (suc n) (≼-trans (cum≼ F G h m n) (≼-trans (mul≼ωx (G n) (suc n)) (ab n))))

limc≼ : (F : ℕ → Tr zero) (nz : (n : ℕ) → zero ⊢ zero ◃ F n) {Y : T₀}
  → (∀ n → read (F n) ≼ Y) → read (limc F nz) ≼ ωx Y
limc≼ F nz {Y} h = l≼ (λ n → ≼l (suc n) (cum≼ F (λ _ → Y) h (λ _ → ≼-refl Y) n))
```

## 折叠的结点行

朝第 0 层的折叠在任何层号的结点 `Ω p g` 上是链 `stp⊥` 上各行的部分和的极限 (定义的展开). 链上各行不高于递增且逐步吸收的参照列 G 时, 结点的折叠不高于 `lim G`. 链点本身的上界 (回灌 `ψs` 的值) 由使用者在证 h 时给出.

```agda
stp⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → ℕ → Br ℓ p
stp⊥ ℓ ε ρ B p g = iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p)
  (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p)

Ω≼ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) (G : ℕ → T₀)
  → (∀ n → read (ψ⊥ ℓ ε ρ B (g (stp⊥ ℓ ε ρ B p g n))) ≼ G n)
  → (∀ n → G n ≼ G (suc n)) → (∀ n → ωx (G n) ≼ G (suc n))
  → read (ψ⊥ ℓ ε ρ B (Ω p g)) ≼ L.lim G
Ω≼ ℓ ε ρ B p g G h m ab =
  limc≼lim (λ n → ψ⊥ ℓ ε ρ B (g (stp⊥ ℓ ε ρ B p g n))) (λ n → nz⊥ ℓ ε ρ B (g (stp⊥ ℓ ε ρ B p g n))) G h m ab
```

## 第 0 层的折叠

层号零上没有结点与嵌入, 折叠只有零, 后继, ℕ 极限三行, 逐行不高于 `pw`.

```agda
fold₀≼ : (B : Base zero) {Y : T₀} → read (b⊥ B) ≼ Y → (x : Tr zero) → read (ψ⊥ zero tt tt B x) ≼ pw Y (read x)
fold₀≼ B q zero          = q
fold₀≼ B q (suc x)       = next≼ (ψ⊥ zero tt tt B x) (nz⊥ zero tt tt B x) (fold₀≼ B q x)
fold₀≼ B q (lim f a)     = l≼ (λ n → ≼l n (fold₀≼ B q (f n)))
fold₀≼ B q (Ω () _)
fold₀≼ B q (up _ () _ _)

folds₀≼ : (B : Base zero) (β : Tr zero) (nβ : zero ⊢ zero ◃ β) {Y : T₀} → read β ≼ Y
  → (x : Tr zero) → read (ψs zero tt tt B zero self β nβ x) ≼ pw Y (read x)
folds₀≼ B β nβ q zero          = q
folds₀≼ B β nβ q (suc x)       = next≼ (ψs zero tt tt B zero self β nβ x) (nzs zero tt tt B zero self β nβ x) (folds₀≼ B β nβ q x)
folds₀≼ B β nβ q (lim f a)     = l≼ (λ n → ≼l n (folds₀≼ B β nβ q (f n)))
folds₀≼ B β nβ q (Ω () _)
folds₀≼ B β nβ q (up _ () _ _)
```

## 最小的例子: 层号 1 的 Ω 树

块的链 `c₁ (n+1) = ψs … (g (c₁ n))` 从零起, 每步读回不高于 ω^(·+1); 参照的塔 `e (n+1) = ω^(e n)` 从 1 起. 不变量 `inv`: 链的第 n 项加 2 不高于塔的第 n+1 项.

```agda
c₁ : ℕ → Tr zero
c₁ = iter (λ z → ψs (suc zero) tt tt (B₀ (suc zero)) zero (ins self) (Ωt zero) (Ωt-nz zero)
                   (up zero tt (suc z) (z◃s z))) zero

F₁ : ℕ → Tr zero
F₁ n = ψ₀ (suc zero) tt tt (up zero tt (suc (c₁ n)) (z◃s (c₁ n)))

ε₀-form : ψ₀ (suc zero) tt tt (Ωt (suc zero))
        ≡ limc F₁ (λ n → nz⊥ (suc zero) tt tt (B₀ (suc zero)) (up zero tt (suc (c₁ n)) (z◃s (c₁ n))))
ε₀-form = refl

e : ℕ → T₀
e zero    = 𝟏
e (suc n) = pw 𝟏 (e n)

1≼e : ∀ n → 𝟏 ≼ e n
1≼e zero    = ≼-refl 𝟏
1≼e (suc n) = pw-base 𝟏 (e n)

ss≼ : {Q : T₀} → 𝟏 ≼ Q → L.suc (L.suc (ωx Q)) ≼ ωx (ωx Q)
ss≼ {Q} q = ≼-trans (+ᵛ-mono (≼-refl (ωx Q)) (≼l 2 (+ᵛ-mono q q))) (mul≼ωx (ωx Q) 2)

e-step : ∀ n → L.suc (e n) ≼ e (suc n)
e-step zero    = ≼l 2 (≼-refl (L.suc 𝟏))
e-step (suc n) =
  ≼-trans (+ᵛ-mono (≼-refl (e (suc n))) (1≼e (suc n)))
  (≼-trans (mul≼ωx (e (suc n)) 2) (pw-mono (≼-refl 𝟏) (e-step n)))

e-mono : ∀ n → e n ≼ e (suc n)
e-mono n = ≼-trans (≼-suc (≼-refl (e n))) (e-step n)

step≼ : (z : Tr zero) → read (ψs (suc zero) tt tt (B₀ (suc zero)) zero (ins self) (Ωt zero) (Ωt-nz zero)
                   (up zero tt (suc z) (z◃s z))) ≼ pw 𝟏 (L.suc (read z))
step≼ z = folds₀≼ _ (Ωt zero) (Ωt-nz zero) (≼-refl 𝟏) (suc z)

inv : ∀ n → L.suc (L.suc (read (c₁ n))) ≼ e (suc n)
inv zero    = ≼l 2 (≼-refl (L.suc 𝟏))
inv (suc n) =
  ≼-trans (s≼s (s≼s (step≼ (c₁ n))))
  (≼-trans (ss≼ (pw-base 𝟏 (read (c₁ n)))) (pw-mono (≼-refl 𝟏) (inv n)))

chain≼ : ∀ n → read (F₁ n) ≼ e (suc (suc n))
chain≼ n = ≼-trans (fold₀≼ _ (≼-refl 𝟏) (suc (c₁ n))) (pw-mono (≼-refl 𝟏) (≼-trans (≼-suc (≼-refl _)) (inv n)))

ε₀-tower : read (ψ₀ (suc zero) tt tt (Ωt (suc zero))) ≼ L.lim (λ n → e (suc (suc n)))
ε₀-tower = Ω≼ (suc zero) tt tt (B₀ (suc zero)) (inj₁ tt) (λ c → up zero tt (suc c) (z◃s c)) (λ n → e (suc (suc n))) chain≼ (λ n → e-mono (suc (suc n)))
  (λ n → pw-mono (≼-refl 𝟏) (e-step (suc n)))
```

## 接到 `OCF.Align.Level` 的 ψ⁰(Ω₁)

Level 的 ψ 在第 0 层的树上与 `pw 𝟏` 同形, 所以塔不高于 Level 的链.

```agda
pw≼ψ⁰ : (x : T₀) → pw 𝟏 x ≼ L.ψ⁰ x
pw≼ψ⁰ L.zero        = ≼-refl 𝟏
pw≼ψ⁰ (L.suc x)     = ωx-mono (pw≼ψ⁰ x)
pw≼ψ⁰ (L.lim f)     = l≼ (λ n → ≼l n (pw≼ψ⁰ (f n)))
pw≼ψ⁰ (L.limᵢ () f)
pw≼ψ⁰ (L.up () x)

pw≼ψ : ∀ {ℓ} (p : L.zero L.<ᴵ ℓ) (σ : L.Simᴵ L.zero ℓ) (x : T₀) → pw 𝟏 x ≼ L.ψ p σ x
pw≼ψ p σ L.zero        = ≼-refl 𝟏
pw≼ψ p σ (L.suc x)     = ωx-mono (pw≼ψ p σ x)
pw≼ψ p σ (L.lim f)     = l≼ (λ n → ≼l n (pw≼ψ p σ (f n)))
pw≼ψ p σ (L.limᵢ () f)
pw≼ψ p σ (L.up () x)

cᴸ : ℕ → T₀
cᴸ = iterᴸ (λ x → L.ψ {i = L.zero} L.zero (λ r → r) (L.up L.zero x)) 𝟏

ψ⁰Ω₁-form : L.ψ⁰ (L.Ω (L.suc L.zero)) ≡ L.lim (λ n → L.ψ⁰ (cᴸ n))
ψ⁰Ω₁-form = refl

e≼cᴸ : ∀ n → e n ≼ cᴸ n
e≼cᴸ zero    = ≼-refl 𝟏
e≼cᴸ (suc n) = ≼-trans (pw-mono (≼-refl 𝟏) (e≼cᴸ n)) (pw≼ψ L.zero (λ q → L.suc q) (cᴸ n))

ε₀-upper : read (ψ₀ (suc zero) tt tt (Ωt (suc zero))) ≼ L.ψ⁰ (L.Ω (L.suc L.zero))
ε₀-upper = ≼-trans ε₀-tower
  (l≼ (λ n → ≼l (suc n) (≼-trans (pw-mono (≼-refl 𝟏) (e≼cᴸ (suc n))) (pw≼ψ⁰ (cᴸ (suc n))))))
```
