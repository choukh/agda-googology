# YiChain 一般的 n：`ChainP` 归约到两条 `≼ˣ` 加强

**验收文件，档位：条件定理与编译定理。** `chain-cond : P1 → P2 → ChainP`，`btbo-cond : P1 → P2 → D.BTBOᴵ ≼ read T₃`。`P1` 只谈参照框架 (链点对上 `VMᵖ` 的结论加强到 `≼ˣ`)，`P2` 只谈主线 (`T₃-own` 加上链的一步，加强到 `≼ˣ`)。
`P1 0`, `P2 0` 是无条件的定理 (`p1₀`, `p2₀`，后者即 [YiChainOne](YiChainOne.lagda.md))；`Tri` 推出 `P1`, `P2` (`tri→P1`, `tri→P2`)，所以前提在经典模型里成立；n ≥ 1 的 `P1 n`, `P2 n` 未证。无条件推论 `T₃-γ₂ : D.γ 2 ≼ read T₃`。
不否定什么：`Tri` 推出 LPO，这里只用它说明前提相容，不说明前提要 LPO。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiChainCond where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₂)
open import OCF.Lean.YiLeanTw3 using (pts; obs; T₃; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read; plus≽)
open import OCF.Lean.YiLeanValFin using (ChainP; btbo-p; κ; HS-read; lower-read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; ≼-trans)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiVmConExact using (_≼ˣ_; lˣ; reflˣ; ˣ→ᵖ; VMᵖ; Tri; tri→cplˣ)
open import OCF.Lean.YiChainBase using (transˣ)
open import OCF.Lean.YiChainOne using (term; chainP₁)
```

## 1 前提与归约

`D.γ (n+1)` 定义性地是 `ψ⁰ (Ω (D.L n))`；中间点取 `ψ⁰ (Ω (κ n))` (`T₃-own` 的左边)。

```agda
P1 : Set
P1 = ∀ n → D.γ n ≼ˣ read (co (pts n)) → L.ψ⁰ (L.Ω (D.L n)) ≼ˣ L.ψ⁰ (L.Ω (κ n))

P2 : Set
P2 = ∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))

module FromP (p1 : P1) (p2 : P2) where
  inv : ∀ n → D.γ n ≼ˣ read (co (pts n))
  inv zero = reflˣ _
  inv (suc n) = transˣ (p1 n (inv n)) (p2 n)

chain-cond : P1 → P2 → ChainP
chain-cond p1 p2 n = n , ˣ→ᵖ (FromP.inv p1 p2 n)

btbo-cond : P1 → P2 → D.BTBOᴵ ≼ read T₃
btbo-cond p1 p2 = btbo-p (chain-cond p1 p2)
```

## 2 第 0 步的实例

`κ 0` 与 `D.L 0` 都定义性地是 `L.suc L.zero`。

```agda
p1₀ : D.γ 0 ≼ˣ read (co (pts 0)) → L.ψ⁰ (L.Ω (D.L 0)) ≼ˣ L.ψ⁰ (L.Ω (κ 0))
p1₀ _ = reflˣ _

p2₀ : L.ψ⁰ (L.Ω (κ 0)) ≼ˣ read (co (pts 1))
p2₀ = lˣ term
```

## 3 前提在经典模型里成立

两条的值的版本都已是定理 (`VMᵖ`；`lower-read` 加 `plus≽`)，`Tri` 把值序改写进 `≼ˣ`。

```agda
tri→P1 : Tri → P1
tri→P1 t n d = tri→cplˣ t _ _
  (VMᵖ (D.γ n) (D.cert n) (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n))) (ˣ→ᵖ d))

tri→P2 : Tri → P2
tri→P2 t n = tri→cplˣ t _ _ (plus≽ (co (pts n)) (obs (pts n)) (lower-read (co (pts n)) (lw (pts n))))
```

## 4 无条件的推论

`btbo-p` 的第 1 项：参照对角链的第 2 项 `D.γ 2 = ψ⁰ (Ω (D.L 1))` (读法 ψ₀(Ω_{ε₀})) 不高于读回的 `T₃`。下界，不是同值。

```agda
T₃-γ₂ : D.γ 2 ≼ read T₃
T₃-γ₂ = ≼l 1 (≼-trans
  (VMᵖ (D.γ 1) (D.cert 1) (read (co (pts 1))) (HS-read (co (pts 1)) (lw (pts 1))) (proj₂ chainP₁))
  (lower-read (co (pts 1)) (lw (pts 1))))
```
