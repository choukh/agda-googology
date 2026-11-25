# YiDiag 验收：链点的层号与参照的对角线结构可比 (第 1 步)

**验收文件，档位：编译定理。** 读回的第 1 个链点与参照 `D.γ 1` 结构互模拟 (`read-pt1`，`≅`)，所以层号 `D.L 1 ≅ᴵ κ 1` (`L1≅κ1`)，判据 C2 `D.L 1 ⊑ᴵ κ 1` 成立；
C2′ 在 n = 0, 1 成立；C3 只到 n ≤ 1；C4 的 n = 1 是同值 (`≅`)，n = 2 在 [YiDiagAccFin](YiDiagAccFin.lagda.md)。
不陈述 n ≥ 2 的结构可比 (未走通，判断见回报)。闭项在 [YiDiagTw3](YiDiagTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDiagAcc where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiDiagCore
open import OCF.Lean.YiDiagFold
open import OCF.Lean.YiDiagTw3 using (R; F; pt; pt-lgl)
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.Diagonal as Diag
import OCF.Align.Uniform as Un
open import OCF.Align.YiVmConExact using (_≼ᵖ_; zᵖ; sᵖ; ˣ→ᵖ; ≅→≼ˣ)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
open L using (_≅_)

module D = Diag.Diagonal Un.Uniform
```

## 1 读回与层号 (C1)

`read`：第 0 层的树读成参照的第 0 层的树 (`top` 读成 1)。合法的树读回后遗传步进 (`HS-read`)，第一位置读成前驱包含 (`cp→⊑`)。
`κ m`：第 `m` 个链点读成参照的层号。

```agda
read : R → L.Ordᶜ L.zero
read G.zero = L.zero
read (G.suc a) = L.suc (read a)
read (G.lim f) = L.lim (λ n → read (f n))
read (G.lc () g)
read (G.em () a)
read G.top = L.suc L.zero

cp→⊑ : ∀ {a} b → Cp zero a b → read a L.⊑ read b
cp→⊑ b (inj₁ refl) h = h
cp→⊑ (G.suc b) (inj₂ p) h = L.≺s (cp→⊑ b p h)
cp→⊑ (G.lim f) (inj₂ (n , p)) h = L.≺l n (cp→⊑ (f n) p h)
cp→⊑ G.top (inj₂ refl) ()

HS-read : ∀ η → Lgl zero η → L.HS (read η)
HS-read G.zero l = L.hz
HS-read (G.suc a) l = L.hs (HS-read a l)
HS-read (G.lim f) (st , lf) = L.hl (λ n → HS-read (f n) (lf n)) (λ n → cp→⊑ (f (suc n)) (st n))
HS-read G.top l = L.hs L.hz

κ : ℕ → L.Ordᴵ
κ m = L.toLevel (read (pt m)) (HS-read (pt m) (pt-lgl m))
```

## 2 目标层 0 的折叠读成参照的 ψ⁰

第 0 层上的折叠逐构造子就是参照的 ψ⁰ (零给 1，后继给从零起的 ω 倍，极限逐项)，所以读回结构互模拟。

```agda
read-plus : ∀ x y → read (plus zero x y) ≅ (read x L.+ read y)
read-plus x G.zero = L.≅-refl⁰ (read x)
read-plus x (G.suc y) = L.s≅ (read-plus x y)
read-plus x (G.lim f) = L.l≅ (λ n → read-plus x (f n))
read-plus x (G.lc () g)
read-plus x (G.em () a)
read-plus x G.top = L.s≅ (L.≅-refl⁰ (read x))

copies : ∀ y {Y : L.Ordᶜ L.zero} → read y ≅ Y → ∀ n →
  read (iter (plus zero y) G.zero n) ≅ iterᴸ (Y L.+_) L.zero n
copies y e zero = L.z≅
copies y e (suc n) = L.≅-trans (read-plus y _) (L.add-≅ e (copies y e n))

fold-read : ∀ (x : Ext zero zero) y → read (Ψ zero v0 x y) ≅ L.ψ⁰ (read y)
fold-read x G.zero = L.s≅ L.z≅
fold-read x (G.suc a) = L.l≅ (copies _ (fold-read x a))
fold-read x (G.lim f) = L.l≅ (λ n → fold-read x (f n))
fold-read x (G.lc () g)
fold-read x (G.em () a)
fold-read x G.top = L.l≅ (copies G.top (L.s≅ L.z≅))
```

## 3 第 1 个链点与参照的 γ₁ 同构 (C2, C2′, C4 n = 1)

`pt 1 = F top` 的链在第 0 层，从 `top` (读成 1) 起，每步一次第 0 层的折叠；参照 `D.G` 从 1 起，每步一次 `ψ`。

```agda
c₁ : ℕ → R
c₁ = chain zero (Ψ zero v0 (self zero))

chainG : ∀ n → read (c₁ n) ≅ D.G n
chainG zero = L.s≅ L.z≅
chainG (suc n) = L.≅-trans (fold-read _ (c₁ n))
  (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → L.suc q} (chainG n))

read-pt1 : read (pt 1) ≅ D.γ 1
read-pt1 = L.l≅ (λ n → L.≅-trans (fold-read _ (c₁ n)) (L.ψ⁰-≅ (chainG n)))

L1≅κ1 : D.L 1 L.≅ᴵ κ 1
L1≅κ1 = L.toLevel-≅ (D.cert 1) (HS-read (pt 1) (pt-lgl 1)) (L.≅-sym read-pt1)

≅ᴵ→⊑ᴵ : ∀ {a b} → a L.≅ᴵ b → a L.⊑ᴵ b
≅ᴵ→⊑ᴵ L.z≅ = L.z⊑
≅ᴵ→⊑ᴵ (L.s≅ e) = L.s⊑ e L.zero
≅ᴵ→⊑ᴵ (L.l≅ h) = L.l⊑ (λ n → L.⊑ᴵ-trans (≅ᴵ→⊑ᴵ (h n)) (L.Sim→⊑ᴵ (L.lim n)))

C2 : Σ ℕ λ m → D.L 1 L.⊑ᴵ κ m
C2 = 1 , ≅ᴵ→⊑ᴵ L1≅κ1

C3≤1 : ∀ n → n ≤ 1 → Σ ℕ λ m → D.L n L.⊑ᴵ κ m
C3≤1 zero z≤n = 0 , L.⊑ᴵ-refl
C3≤1 (suc zero) (s≤s z≤n) = C2

C2′ : Σ ℕ λ m → D.γ 1 ≼ᵖ read (pt m)
C2′ = 1 , ˣ→ᵖ (≅→≼ˣ (L.≅-sym read-pt1))

C2′₀ : Σ ℕ λ m → D.γ 0 ≼ᵖ read (pt m)
C2′₀ = 0 , sᵖ zᵖ

lower₁ : L.ψ⁰ (L.Ω (L.natᴵ 1)) V.≼ read (F (G.suc G.zero))
lower₁ = V.≅→≼ (L.≅-sym read-pt1)

-- 读回的第 1 个链点与参照的 ψ₀(Ω₁) 同值 (两边都是 ≅)。
same₁ : read (F (G.suc G.zero)) ≅ L.ψ⁰ (L.Ω (L.natᴵ 1))
same₁ = read-pt1
```
