# V107 的实验 (一): `T⁺` 的中间下界, 不逐项对齐

> 验收文件. 判决: 编译定理, 无前提, 档是 "高于 BTBO 的中间参照", 不到 ψ₀(Ω_{Ω+1}). 对每个 m, `tw 1` 上 `Ωt·(m+2)` 的折叠是一条链 `zx m` 的上确界: 链从 `Ωt·(m+1)` 的折叠之上起步 (`start`), 对 c ↦ ψ⁰(Ω_c) 封闭 (`closed`), 各项 ≼ `read T⁺` (`chain≼T⁺`, `lvl≼T⁺`).
> 参照是 `OCF.Align.Level` 的 ψ⁰(Ω_i), i 取链点的读回, 不是记号项. 读法 (判断): ω 个相继的 "c = ψ₀(Ω_c) 型封闭点", 记号里约是 ψ₀(Ω_Ω·ω).
> 只用 `up x c (Ωt (h c))` 朝第 0 层的一帧 (`YiT2Frame.up-lower`, `eqk`), 不经回退行与摊平式. 不否定什么; 上界见 [YiDecFlat](YiDecFlat.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDecLow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ink)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSFold using (ok-B₀)
open import OCF.Lean.YiLSTw1 using (h₁; nl-↑; corr-↑; lvl; E; ez; es; E→≅)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiT2Desc using (T⁺; R⁺; nzR⁺)
open import OCF.Lean.YiT2Frame using (ε¹; ρ¹; β; lw¹; up-lower; eqk)

import OCF.Align.Level as L
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.Value using (_≼_; z≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼)
```

## 一般的 x: `x + Ωt` 的折叠的链

`x + Ωt (tw 1)` 是结点, 分支 z 上是 `up x z (Ωt (h₁ z))`. 链 `zx` 是回灌的孩子下标, 行 `rowx n` 是分支 `zx n` 的底折叠. 与 `YiT2Frame` 的 `zc` 同形, 那里 x 固定为 `Ωt (tw 1)`.

```agda
module Ch (x : Tr (tw 1)) where
  gx : Tr zero → Tr (tw 1)
  gx z = up x z (Ωt (h₁ z)) (Ωt-nz (h₁ z))

  zx : ℕ → Tr zero
  zx = iter (λ z → ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (ink self) (Ωt zero) (Ωt-nz zero) (gx z)) zero

  rowx : ℕ → Tr zero
  rowx n = ψ⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (gx (zx n))

  nzx : ∀ n → zero ⊢ zero ◃ rowx n
  nzx n = nz⊥ (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (gx (zx n))

  form : ψ₀ (tw 1) ε¹ ρ¹ (x + β) ≡ limc rowx nzx
  form = refl

  row-lower : ∀ n → L.ψ⁰ (L.Ω (lvl (zx n))) ≼ read (rowx n)
  row-lower n = up-lower zero h₁ ε¹ ρ¹ (B₀ (tw 1)) (ok-B₀ (tw 1)) x (zx n) (nl-↑ (zx n)) (corr-↑ (zx n) (HSr (zx n)))

  zx-row : ∀ n → E (zx (suc n)) (rowx n)
  zx-row n = eqk zero h₁ ε¹ ρ¹ (B₀ (tw 1)) self lw¹ (Ωt zero) (Ωt-nz zero) (es ez) (gx (zx n))

  closed : ∀ n → L.ψ⁰ (L.Ω (lvl (zx n))) ≼ read (zx (suc n))
  closed n = ≼-trans (row-lower n) (≅→≼ (L.≅-sym (E→≅ (zx-row n))))

  start : zero ⊢ ψ₀ (tw 1) ε¹ ρ¹ x ◃ rowx 0
  start = ◃l zero

  top : ∀ n → read (zx n) ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (x + β))
  top zero    = z≼
  top (suc n) = limcum≽ rowx nzx n (≅→≼ (E→≅ (zx-row n)))

  lvl-top : ∀ n → L.ψ⁰ (L.Ω (lvl (zx n))) ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (x + β))
  lvl-top n = limcum≽ rowx nzx n (row-lower n)
```

## `Ωt` 的倍数

`km m` 是 `T⁺` 的链第 1 项 `next (Ωt (tw 1))` 的基本列第 m 项 (左加). 因为 `Ωt (tw 1)` 的分支是 `up zero …`, 它也等于右加一个 `Ωt` (`swap`), 所以上一节可用.

```agda
km : ℕ → Tr (tw 1)
km = iter (β +_) β

swap : ∀ m → km (suc m) ≡ km m + β
swap zero    = refl
swap (suc m) = cong (β +_) (swap m)

km◃R1 : ∀ m → zero ⊢ ψ₀ (tw 1) ε¹ ρ¹ (km m) ◃ R⁺ 1
km◃R1 m = ◃t (◃l m) (◃l zero)

km≼T⁺ : ∀ m → read (ψ₀ (tw 1) ε¹ ρ¹ (km m)) ≼ read T⁺
km≼T⁺ m = limcum≽ R⁺ nzR⁺ 1 (⊑→≼ (read (ψ₀ (tw 1) ε¹ ρ¹ (km m))) (◃⊑ (km◃R1 m)))

sum≼T⁺ : ∀ m → read (ψ₀ (tw 1) ε¹ ρ¹ (km m + β)) ≼ read T⁺
sum≼T⁺ m = subst (λ t → read (ψ₀ (tw 1) ε¹ ρ¹ t) ≼ read T⁺) (swap m) (km≼T⁺ (suc m))
```

## 结论

第 m 条链: 起点在 `Ωt·(m+1)` 的折叠之上, 对 c ↦ ψ⁰(Ω_c) 封闭, 整条在 `read T⁺` 之下. m = 0 时起点之下是 `twᶜ 1`, 它不低于 BTBO 的参照.

```agda
zxm : ℕ → ℕ → Tr zero
zxm m = Ch.zx (km m)

startm : ∀ m → read (ψ₀ (tw 1) ε¹ ρ¹ (km m)) L.≺ read (zxm m 1)
startm m = L.≺-respʳ (◃→≺ (Ch.start (km m))) (L.≅-sym (E→≅ (Ch.zx-row (km m) 0)))

closedm : ∀ m n → L.ψ⁰ (L.Ω (lvl (zxm m n))) ≼ read (zxm m (suc n))
closedm m = Ch.closed (km m)

prev≼ : ∀ m n → read (zxm m n) ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (km (suc m)))
prev≼ m n = subst (λ t → read (zxm m n) ≼ read (ψ₀ (tw 1) ε¹ ρ¹ t)) (sym (swap m)) (Ch.top (km m) n)

chain≼T⁺ : ∀ m n → read (zxm m n) ≼ read T⁺
chain≼T⁺ m n = ≼-trans (Ch.top (km m) n) (sum≼T⁺ m)

lvl≼T⁺ : ∀ m n → L.ψ⁰ (L.Ω (lvl (zxm m n))) ≼ read T⁺
lvl≼T⁺ m n = ≼-trans (Ch.lvl-top (km m) n) (sum≼T⁺ m)

btbo≼0 : D.BTBOᴵ ≼ read (ψ₀ (tw 1) ε¹ ρ¹ (km 0))
btbo≼0 = btbo-tw1
```
