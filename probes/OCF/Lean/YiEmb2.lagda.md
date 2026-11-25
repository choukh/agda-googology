# YiEmb2：两个方向的保值嵌入给出定义域版的折叠单调

**验收文件，档位：编译定理与条件定理。** `VMˣ₂ : XEmb a b → XEmb b a → ψ⁰ (Ω a) ≼ˣ ψ⁰ (Ω b)` 与 `VMˣ` (两个方向的 `≼ˣ` 推导) 无条件成立 (证法在 [YiEmb2Le](YiEmb2Le.lagda.md))。于是 `P1` 的两向版 `p1₂` 对一切 n 是定理，`P1 1` 是定理 (`p1₁`)；`chain-cond₂ : P2₂ → …` 把两向的链不变量归约到主线一侧的 `P2₂`，且 `P2₂ → P1`。
不否定什么：一个方向的 `VMˣ` (只有 `x ≼ˣ y`) 没有证也没有否定；`P2₂ 0` 是定理，`P2₂ n` (n ≥ 1) 未证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEmb2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
import OCF.Align.Level as L
open L using (Ordᴵ; _⊑ᴵ_; _≺ᴵ_; via; HS; toLevel; z⊑; s⊑; l⊑)
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Align.BTBOFullEmb using (PEmb; module PE)
open PEmb
open import OCF.Align.YiVmConExact using (XEmb; V; V-≅; ≈→≅; _≼ˣ_; reflˣ; ˣ→ᵖ; embˣ)
open XEmb
open import OCF.Lean.YiEmb2Le using (module Two)
open import OCF.Lean.YiLeanTw3 using (pts; T₃; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read)
open import OCF.Lean.YiLeanValFin using (ChainP; btbo-p; κ; HS-read)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiChainBase using (transˣ)
open import OCF.Lean.YiChainCond using (P1; P2; p2₀)
open import OCF.Lean.YiChainBack using (γ₁≈; back₁)
```

## 1 实例：两个嵌入给出 E 的翻转与 Ω 律

`flip`：E 的 `sub` 支里，i 与 `P′` 把 i′ 映回的前驱值相等 (`ex`, `ex′` 两次)，又都是 a 的字面前驱，故 `≅ᴵ` (`≈→≅`)。`Ω′` 逐字照 `BTBOFullEmb.PE.Ω′`。

```agda
module Inst {a b : Ordᴵ} (X : XEmb a b) (Y : XEmb b a) where
  module PX = PE (P X)
  module PY = PE (P Y)

  flip : ∀ {i i′} → PX.E i i′ → PY.E i′ i
  flip (PX.top e e′) = PY.top e′ e
  flip {i} {i′} (PX.sub r e′) = PY.sub r′ (≈→≅ r (bnd (P Y) r′) v₁ v₂) where
    r′ : i′ ≺ᴵ b
    r′ = L.≺ᴵ-respˡ e′ (bnd (P X) r)
    v₁ : V i ≼ V (map (P Y) r′)
    v₁ = ≼-trans (ex′ X r) (≼-trans (V-≅ (L.≅ᴵ-sym e′)) (ex′ Y r′))
    v₂ : V (map (P Y) r′) ≼ V i
    v₂ = ≼-trans (ex Y r′) (≼-trans (V-≅ e′) (ex X r))

  open Two PX.E PX.E-resp PY.E PY.E-resp

  Ω′ : ∀ {x c c′} → x ⊑ᴵ c → PX.E c c′ → Lx (L.Ω x) (L.Ω c′)
  Ω′ {c′ = c′} z⊑ ec = Le-one c′ (L.≅ᴵ-refl c′)
  Ω′ {c′ = c′} (s⊑ e q) ec with PX.low ec (via e q)
  ... | r , via e₂ q₂ = walk c′ (L.≅ᴵ-refl c′) (PX.sub r (L.≅ᴵ-sym e₂)) q₂
  Ω′ (l⊑ k) ec = Lll (λ n → Lul (Ω′ (k n) ec))

  open WithLaws PX.lt′ PX.eq′ PY.ℒ flip (Ω′ L.⊑ᴵ-refl)

  vm : L.ψ⁰ (L.Ω a) ≼ˣ L.ψ⁰ (L.Ω b)
  vm = Ψ⁰ˣ (PX.top (L.≅ᴵ-refl a) (L.≅ᴵ-refl b))
```

## 2 定义域版的折叠单调

```agda
VMˣ₂ : ∀ {a b} → XEmb a b → XEmb b a → L.ψ⁰ (L.Ω a) ≼ˣ L.ψ⁰ (L.Ω b)
VMˣ₂ X Y = Inst.vm X Y

VMˣ : ∀ x (hx : HS x) y (hy : HS y) → x ≼ˣ y → y ≼ˣ x →
  L.ψ⁰ (L.Ω (toLevel x hx)) ≼ˣ L.ψ⁰ (L.Ω (toLevel y hy))
VMˣ x hx y hy d d′ = VMˣ₂ (embˣ x hx y hy d) (embˣ y hy x hx d′)
```

## 3 链上：`P1` 的两向版是定理

```agda
P1₂ : Set
P1₂ = ∀ n → D.γ n ≼ˣ read (co (pts n)) → read (co (pts n)) ≼ˣ D.γ n →
  (L.ψ⁰ (L.Ω (D.L n)) ≼ˣ L.ψ⁰ (L.Ω (κ n))) × (L.ψ⁰ (L.Ω (κ n)) ≼ˣ L.ψ⁰ (L.Ω (D.L n)))

p1₂ : P1₂
p1₂ n d d′ =
  VMˣ (D.γ n) (D.cert n) (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n))) d d′ ,
  VMˣ (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n))) (D.γ n) (D.cert n) d′ d

p1-one : L.ψ⁰ (L.Ω (D.L 1)) ≼ˣ L.ψ⁰ (L.Ω (κ 1))
p1-one = proj₁ (p1₂ 1 (proj₁ γ₁≈) (proj₂ γ₁≈))

p1₁ : D.γ 1 ≼ˣ read (co (pts 1)) → L.ψ⁰ (L.Ω (D.L 1)) ≼ˣ L.ψ⁰ (L.Ω (κ 1))
p1₁ _ = p1-one
```

## 4 两向的链不变量

`P2₂`：`P2` 加上反向。`P2₂ 0` 是定理 (`p2₀` 与 `back₁`；`D.γ 1` 定义性地是 `ψ⁰ (Ω (κ 0))`)。

```agda
P2₂ : Set
P2₂ = ∀ n → (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n)))

p2₂-0 : (L.ψ⁰ (L.Ω (κ 0)) ≼ˣ read (co (pts 1))) × (read (co (pts 1)) ≼ˣ L.ψ⁰ (L.Ω (κ 0)))
p2₂-0 = p2₀ , back₁

module FromP2₂ (p2 : P2₂) where
  inv : ∀ n → (D.γ n ≼ˣ read (co (pts n))) × (read (co (pts n)) ≼ˣ D.γ n)
  inv zero = reflˣ _ , reflˣ _
  inv (suc n) =
    transˣ (proj₁ (p1₂ n (proj₁ (inv n)) (proj₂ (inv n)))) (proj₁ (p2 n)) ,
    transˣ (proj₂ (p2 n)) (proj₂ (p1₂ n (proj₁ (inv n)) (proj₂ (inv n))))

chain-cond₂ : P2₂ → ∀ n → (D.γ n ≼ˣ read (co (pts n))) × (read (co (pts n)) ≼ˣ D.γ n)
chain-cond₂ p2 = FromP2₂.inv p2

P2₂→P1 : P2₂ → P1
P2₂→P1 p2 n _ = proj₁ (p1₂ n (proj₁ (FromP2₂.inv p2 n)) (proj₂ (FromP2₂.inv p2 n)))

P2₂→P2 : P2₂ → P2
P2₂→P2 p2 n = proj₁ (p2 n)

btbo-cond₂ : P2₂ → D.BTBOᴵ ≼ read T₃
btbo-cond₂ p2 = btbo-p (λ n → n , ˣ→ᵖ (proj₁ (chain-cond₂ p2 n)))
```

## 5 第 2 项

由 `p2₂-0` 与 `p1₂` 得第 2 项两个方向的前一半：`ψ⁰ (Ω (D.L 1))` 与 `ψ⁰ (Ω (κ 1))` 两个方向都在 `≼ˣ` 里。到 `read (co (pts 2))` 还要 `P2₂ 1`。

```agda
γ₂≈κ₁ : (D.γ 2 ≼ˣ L.ψ⁰ (L.Ω (κ 1))) × (L.ψ⁰ (L.Ω (κ 1)) ≼ˣ D.γ 2)
γ₂≈κ₁ = p1₂ 1 (proj₁ γ₁≈) (proj₂ γ₁≈)

γ₂-cond : (L.ψ⁰ (L.Ω (κ 1)) ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ L.ψ⁰ (L.Ω (κ 1))) →
  (D.γ 2 ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ D.γ 2)
γ₂-cond (u , u′) = transˣ (proj₁ γ₂≈κ₁) u , transˣ u′ (proj₂ γ₂≈κ₁)
```
