# `SumOne.T₁` 的上界 (一): $\psi_0(\Omega_\Omega+1)$ 这一站

> **验收文件, 定理.** `T₁` 的第 1 段里第一次 `Step` 之后的位置 `Sω`: 它的值是 $\psi_0(\Omega_\Omega+1)$ (`Sω≈`, `Sω-vlab`, 序数值验收), 它是 `T₁` 的位置 (`Sω≤T₁`), 所以 $\psi^0(\mathrm{suc}\,\Omega_{\ell_0})\preccurlyeq$ `T₁` (`low-T₁`).
> 这时状态已带闭包 (`TreeLevelsO8State.no-seed-old-Inv`), 旧 `Inv` 用不上; `Step` 在第 0 层只读第 0 层的状态, 所以直接算. 不给以后各站的值. 入口 [SumOneUp](SumOneUp.lagda.md). `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneUpStation where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level hiding (below)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; +-mono; VLab)
import OCF.Align.NoCumsum as NC
open NC using (BTBOᴵ)
open import OCF.Align.Stage2 using (ℓ₀; ts; ts-label)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleVar using (trA; ≤→≼)
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nw; ni; nκ; sum; pt)
open import OCF.Align.SumOneClosed using (T₀; T₁; E₁; Y₁; Δ₀; τ₀; one; yc)
open import OCF.Align.SumOneAccept using (T₀≈; sum≥)
```

## §1 和就是加法 (值)

`sum b x` 的值是 `b` 的值加上 `x` 的值, 两个方向. 对 `x` 归纳; 第 0 层没有节点.

```agda
sum≼+ : ∀ {W} (x : D azero W) {b c : A} {B : Ordᶜ zero} → trA b ≼ B + trA c → trA (sum b x) ≼ B + trA (sum c x)
pt≼+  : ∀ {W} (d′ : ℕ → D azero W) n {b c : A} {B : Ordᶜ zero} → trA b ≼ B + trA c → trA (pt b d′ n) ≼ B + trA (pt c d′ n)
sum≼+ n0 h = h
sum≼+ n1 h = s≼s h
sum≼+ (x ⨾ y) h = sum≼+ y (sum≼+ x h)
sum≼+ (nl d′) h = l≼ (λ n → ≼l n (pt≼+ d′ n h))
sum≼+ (ni () u) h
sum≼+ (nκ () u) h
sum≼+ (nw p x) h = sum≼+ x h
pt≼+ d′ zero h = h
pt≼+ d′ (suc n) h = sum≼+ (d′ n) (pt≼+ d′ n h)

+≼sum : ∀ {W} (x : D azero W) {b c : A} {B : Ordᶜ zero} → B + trA c ≼ trA b → B + trA (sum c x) ≼ trA (sum b x)
+≼pt  : ∀ {W} (d′ : ℕ → D azero W) n {b c : A} {B : Ordᶜ zero} → B + trA c ≼ trA b → B + trA (pt c d′ n) ≼ trA (pt b d′ n)
+≼sum n0 h = h
+≼sum n1 h = s≼s h
+≼sum (x ⨾ y) h = +≼sum y (+≼sum x h)
+≼sum (nl d′) h = l≼ (λ n → ≼l n (+≼pt d′ n h))
+≼sum (ni () u) h
+≼sum (nκ () u) h
+≼sum (nw p x) h = +≼sum x h
+≼pt d′ zero h = h
+≼pt d′ (suc n) h = +≼sum (d′ n) (+≼pt d′ n h)
```

第 0 层的加法结合, 零是左单位 (值).

```agda
as≼ : ∀ (a b c : Ordᶜ zero) → (a + b) + c ≼ a + (b + c)
as≼ a b zero = ≼-refl _
as≼ a b (suc c) = s≼s (as≼ a b c)
as≼ a b (lim f) = l≼ (λ n → ≼l n (as≼ a b (f n)))
as≼ a b (limᵢ () f)
as≼ a b (up () x)

as≽ : ∀ (a b c : Ordᶜ zero) → a + (b + c) ≼ (a + b) + c
as≽ a b zero = ≼-refl _
as≽ a b (suc c) = s≼s (as≽ a b c)
as≽ a b (lim f) = l≼ (λ n → ≼l n (as≽ a b (f n)))
as≽ a b (limᵢ () f)
as≽ a b (up () x)

0+≼ : ∀ (x : Ordᶜ zero) → zero + x ≼ x
0+≼ zero = z≼
0+≼ (suc x) = s≼s (0+≼ x)
0+≼ (lim f) = l≼ (λ n → ≼l n (0+≼ (f n)))
0+≼ (limᵢ () f)
0+≼ (up () x)

≼0+ : ∀ (x : Ordᶜ zero) → x ≼ zero + x
≼0+ zero = z≼
≼0+ (suc x) = s≼s (≼0+ x)
≼0+ (lim f) = l≼ (λ n → ≼l n (≼0+ (f n)))
≼0+ (limᵢ () f)
≼0+ (up () x)
```

倍数. `M B n` 是 $B\cdot n$ (左加, 就是 $\psi^0(\mathrm{suc}\,a)$ 的第 $n$ 项). 右加一个 $B$ 与左加一个 $B$ 同值.

```agda
M : Ordᶜ zero → ℕ → Ordᶜ zero
M B = iter (B +_) zero

shift≼ : ∀ B n → M B n + B ≼ B + M B n
shift≼ B zero = 0+≼ B
shift≼ B (suc n) = ≼-trans (as≼ B (M B n) B) (+-mono (≼-refl B) (shift≼ B n))

shift≽ : ∀ B n → B + M B n ≼ M B n + B
shift≽ B zero = ≼0+ B
shift≽ B (suc n) = ≼-trans (+-mono (≼-refl B) (shift≽ B n)) (as≽ B (M B n) B)
```

## §2 站

`e₁`: 一次 `Step` 在第 0 层的一份, $\Omega_0+y_0$, 其中 $y_0$ 是状态 `Y₁` 在第 0 层的差. `c₁` 是 $\omega$ 份. `Sω = T₀ + c₁`.

```agda
e₁ : D azero one
e₁ = (n1 ⨾ n0) ⨾ ((n0 ⨾ yc Δ₀ τ₀ tt) ⨾ n0)

c₁ : D azero one
c₁ = nl (λ _ → e₁)

Sω : A
Sω = sum T₀ c₁

-- 一份的值就是 T₀
e₁-T₀ : sum azero e₁ ≡ T₀
e₁-T₀ = refl

Bω : Ordᶜ zero
Bω = ψ⁰ (suc (Ω ℓ₀))

Bω-shape : Bω ≡ lim (M BTBOᴵ)
Bω-shape = refl

up-pt : ∀ k → trA (pt T₀ (λ _ → e₁) k) ≼ M BTBOᴵ (suc k)
up-pt zero = proj₁ T₀≈
up-pt (suc k) =
  ≼-trans (sum≼+ e₁ {b = pt T₀ (λ _ → e₁) k} {c = azero} {B = M BTBOᴵ (suc k)} (up-pt k))
  (≼-trans (+-mono (≼-refl (M BTBOᴵ (suc k))) (proj₁ T₀≈))
           (shift≼ BTBOᴵ (suc k)))

lo-pt : ∀ k → M BTBOᴵ (suc k) ≼ trA (pt T₀ (λ _ → e₁) k)
lo-pt zero = proj₂ T₀≈
lo-pt (suc k) =
  ≼-trans (shift≽ BTBOᴵ (suc k))
  (≼-trans (+-mono (≼-refl (M BTBOᴵ (suc k))) (proj₂ T₀≈))
           (+≼sum e₁ {b = pt T₀ (λ _ → e₁) k} {c = azero} {B = M BTBOᴵ (suc k)} (lo-pt k)))

Sω≈ : trA Sω ≈ᵛ Bω
Sω≈ = l≼ (λ k → ≼l (suc k) (up-pt k)) , l≼ lo
  where
  lo : ∀ n → M BTBOᴵ n ≼ trA Sω
  lo zero = z≼
  lo (suc k) = ≼l k (lo-pt k)

Sω-vlab : VLab (trA Sω) ts
Sω-vlab = Bω , ts-label , Sω≈
```

## §3 `Sω` 是 `T₁` 的一个位置

`Pre p x`: 差 `p` 是差 `x` 的一个前缀 (只沿左边与 `nl` 的第 0 项走, 开头的 `n0` 可以跳过). `E₁ 0` 的形状由检查器归约给出: 开头的 `n0` 来自状态的零差, 第一个 `nl` 是 $S(\hat\Omega+\hat y)$ 的 $\omega$ 份, 第 0 份里先是 `Step` (就是 `c₁`), 后面才是 `nκ` 的回灌.

```agda
data Pre {W : A} (p : D azero W) : D azero W → Set where
  here : Pre p p
  inL  : ∀ {x y} → Pre p x → Pre p (x ⨾ y)
  skip : ∀ {y} → Pre p y → Pre p (n0 ⨾ y)
  inl0 : ∀ {d′} → Pre p (d′ 0) → Pre p (nl d′)

pre≤ : ∀ {W} b {p x : D azero W} → Pre p x → sum b p ≤ sum b x
pre≤ b here = ≤-refl _
pre≤ b {p} {x ⨾ y} (inL q) = ≤-trans (pre≤ b {p} {x} q) (sum≥ (sum b x) y)
pre≤ b {p} {n0 ⨾ y} (skip q) = pre≤ b {p} {y} q
pre≤ b {p} {nl d′} (inl0 q) = ≤l 1 (pre≤ b {p} {d′ 0} q)

c₁-pre : Pre c₁ (E₁ 0)
c₁-pre = skip (inL (inl0 (inL (inL here))))

Sω≤T₁ : Sω ≤ T₁
Sω≤T₁ = ≤l 1 (pre≤ T₀ c₁-pre)

low-T₁ : Bω ≼ trA T₁
low-T₁ = ≼-trans (proj₂ Sω≈) (≤→≼ Sω≤T₁)
```
