# YiChain 压平：任意层的 ψ⁰ 是第 0 层树的 ψ⁰

**验收文件，档位：编译定理 (引理)。** `flat s` 把任意层的参照树 `s` 读成第 0 层的树 (`limᵢ` 换成 ψ⁰ 所用的那条链上的极限)，`ψ⁰-flat : ψ⁰ s ≅ ψ⁰ (flat s)`；于是 [YiChainBase](YiChainBase.lagda.md) 的吸收对一切层的参照主项成立 (`ABSΩ`)，前提是 `flat s` 有 `HS` 与一个结构前驱见证。
只谈参照框架。`HS (flat (Ω ℓ))` 与 `D.γ` 链上的见证没有证 (一般的 n 要它们)，这里只给出归约。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiChainFlat where

open import Data.Nat.Base using (ℕ; zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl)
open import OCF.Align.YiVmConExact using (_≼ˣ_; reflˣ; ≅→≼ˣ)
open import OCF.Lean.YiZeroAccP using (+ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ; module Abs)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

`limᵢ` 那一行逐字照 `L.ψ⁰` 的规则 (链从 `Ω j` 起，每步 `ψ q`)。

```agda
flat : ∀ {k} → L.Ordᶜ k → T₀
flat L.zero = L.zero
flat (L.suc a) = L.suc (flat a)
flat (L.lim f) = L.lim (λ n → flat (f n))
flat (L.limᵢ {i = j} q f) = L.lim (λ n → flat (f (L.into (L.<→◃ q)
  (iterᴸ (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω j) n))))
flat (L.up L.zero x) = flat x
flat (L.up (L.self n) x) = flat x

ψ⁰-flat : ∀ {k} (s : L.Ordᶜ k) → L.ψ⁰ s L.≅ L.ψ⁰ (flat s)
ψ⁰-flat L.zero = L.s≅ L.z≅
ψ⁰-flat (L.suc a) = L.l≅ (L.iter-R L._≅_ (λ e → L.add-≅ (ψ⁰-flat a) e) L.z≅)
ψ⁰-flat (L.lim f) = L.l≅ (λ n → ψ⁰-flat (f n))
ψ⁰-flat (L.limᵢ {i = j} q f) = L.l≅ (λ n → ψ⁰-flat (f (L.into (L.<→◃ q)
  (iterᴸ (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω j) n))))
ψ⁰-flat (L.up L.zero x) = ψ⁰-flat x
ψ⁰-flat (L.up (L.self n) x) = ψ⁰-flat x

ABSΩ : ∀ {X c : T₀} → L.ψ⁰ c ≼ˣ X → X ≼ L.ψ⁰ c → ∀ {k} (s : L.Ordᶜ k) → L.HS (flat s) → c L.≺ flat s →
  L.ψ⁰ s ≼ˣ (X L.+ L.ψ⁰ s)
ABSΩ {X} hx hv s h d = transˣ (≅→≼ˣ (ψ⁰-flat s))
  (transˣ (Abs.ABS hx hv (flat s) h d) (+ˣ (reflˣ X) (≼-refl X) (≅→≼ˣ (L.≅-sym (ψ⁰-flat s)))))
```
