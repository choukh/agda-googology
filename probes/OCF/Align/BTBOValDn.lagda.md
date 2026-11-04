# 跨族模拟, 向下: `Ordᶜ` 的折叠不超过 src 的折叠

> 接 [BTBOValBase](BTBOValBase.lagda.md). src 的树族 (`S.Ord`, 下标 `Ordᴰ`) 与 Level 的树族 (`Ordᶜ`, 下标 `Ordᴵ`) 差在五处: $\Omega_0=\omega$ 对 $1$; 规则 6 的链起点 $0$ 对 $\Omega_j$; $i=j$ 时的 `lfp`; `↑` 遍历子树对 `up` 节点; 字面三歧对模 $\cong^\mathsf{I}$ 的三歧. 本文证其中一个方向: 在**形状相同的层号上**, Level 的折叠的值不超过 src 的折叠 (`Dn-ψ`, `Dn-Ω`, `Ψ⁰≼<`).
>
> 关系 `Dn y x` ("$y$ 不超过 $x$") 是归纳的, 按 Level 一侧的层号分层 (与 Level 的 `Eq₊`, `R` 同一个写法, 才能严格正). 它不是序数值的 `≼`: `limᵢ` 右边只有 "对一切分支" 一条规则 (`Rir`) 和 "同层逐分支" 一条规则 (`Rii`), 所以 `up y` 不会因为值小就 `Dn` 于 $\Omega_1$. `ψ⁰-not-cong`, `ψᴱ-not-mono` 正是这种 $y$. 这样的关系才对折叠封闭.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOValDn where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ)
open S using (iter; ordᴰ; zero; suc; lim; limᵢ)
open import OCF.Align.Level
open import OCF.Align.BTBOValBase using (tr₀; fd)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-suc; ≼-trans; ≅→≼)
open Restr
```

## §1 层号的翻译

`τ` 把 `Ordᴰ` 逐构造子送到 `Ordᴵ`; 严格单调给出 $\sqsubseteq^\mathsf{I}$-步进.

```agda
τ   : Ordᴰ → Ordᴵ
τ-< : ∀ {a b} → a B.< b → τ a <ᴵ τ b

<→⊑ᴵ : ∀ {a b} → a <ᴵ b → a ⊑ᴵ b
<→⊑ᴵ q = Sim→⊑ᴵ (λ c → <ᴵ-trans c q)

τ B.zero      = zero
τ (B.suc a)   = suc (τ a)
τ (B.lim f m) = lim (τ ∘ f) (λ n → <→⊑ᴵ (τ-< (m Trich.zero)))
  where open OCF.BTBO using (module Trich)

τ-< B.zero      = zero
τ-< (B.suc p)   = suc (τ-< p)
τ-< (B.lim n p) = lim n (τ-< p)
```

**派发一致.** 两边的三歧在 $\tau$ 相关的层上给同一种情况: 混合情况都推出 $a\prec^\mathsf{I}a$.

```agda
via< : ∀ {a b} → a <ᴵ b → a ≺ᴵ b
via< q = via (≅ᴵ-refl _) q

clash-lt-lt : ∀ {j i j′ i′} → τ j ≅ᴵ j′ → τ i ≅ᴵ i′ → j′ ≺ᴵ i′ → i B.< j → ⊥
clash-lt-lt ej ei r q = ≺ᴵ-irrefl (≺ᴵ-trans (≺ᴵ-respˡ (≅ᴵ-sym ei) (≺ᴵ-respʳ (via< (τ-< q)) ej)) r)

clash-lt-eq : ∀ {j i j′ i′} → τ j ≅ᴵ j′ → τ i ≅ᴵ i′ → j′ ≺ᴵ i′ → j ≡ i → ⊥
clash-lt-eq ej ei r refl = ≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-trans (≅ᴵ-sym ei) ej) r)

clash-gt-lt : ∀ {j i j′ i′} → τ j ≅ᴵ j′ → τ i ≅ᴵ i′ → i′ ≺ᴵ j′ → j B.< i → ⊥
clash-gt-lt ej ei r q = clash-lt-lt ei ej r q

clash-eq-lt : ∀ {j i j′ i′} → τ j ≅ᴵ j′ → τ i ≅ᴵ i′ → j′ ≅ᴵ i′ → j B.< i → ⊥
clash-eq-lt ej ei e q = ≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym ej) (≺ᴵ-respʳ (via< (τ-< q)) (≅ᴵ-trans ei (≅ᴵ-sym e))))
```

**coe 的相干.** src 的 `coe`, `coe₀` 都是沿 `Ord<-≡` 的 `transport`. 这条等式对证明的结构递归, `Ord<-≡` 每一步都归约, 不用 K.

```agda
coe-coe₀ : ∀ {j ℓ₁ ℓ₂} (q : j B.< ℓ₁) (q′ : j B.< ℓ₂) (z : S.Ord j) →
           S.coe {p = q} {q = q′} (S.coe₀ {p = q} z) ≡ S.coe₀ {p = q′} z
coe-coe₀ B.zero      B.zero       z = refl
coe-coe₀ (B.suc q)   B.zero       z = coe-coe₀ q B.zero z
coe-coe₀ (B.lim n q) B.zero       z = coe-coe₀ q B.zero z
coe-coe₀ B.zero      (B.suc q′)   z = coe-coe₀ B.zero q′ z
coe-coe₀ (B.suc q)   (B.suc q′)   z = coe-coe₀ (B.suc q) q′ z
coe-coe₀ (B.lim n q) (B.suc q′)   z = coe-coe₀ (B.lim n q) q′ z
coe-coe₀ B.zero      (B.lim m q′) z = coe-coe₀ B.zero q′ z
coe-coe₀ (B.suc q)   (B.lim m q′) z = coe-coe₀ (B.suc q) q′ z
coe-coe₀ (B.lim n q) (B.lim m q′) z = coe-coe₀ (B.lim n q) q′ z
```


## §2 关系

`Dn y x`: Level 的 $y$ 不超过 src 的 $x$. 按 Level 一侧分层: `Rii` 的前提和 `Rul` 用较低层的关系 `D<`, 这是参数, 所以严格正. src 一侧的层号 $\ell$ 是自由的.

```agda
module _ (k : Ordᴵ) (D< : (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {ℓ} → S.Ord ℓ → Set) where
  data Dn₊ : ∀ {ℓ} → Ordᶜ k → S.Ord ℓ → Set where
    Rz  : ∀ {ℓ} {b : S.Ord ℓ} → Dn₊ zero b
    Rs  : ∀ {ℓ} {a : Ordᶜ k} {b : S.Ord ℓ} → Dn₊ a b → Dn₊ (suc a) (suc b)
    Rsr : ∀ {ℓ} {a : Ordᶜ k} {b : S.Ord ℓ} → Dn₊ a b → Dn₊ a (suc b)
    Rll : ∀ {ℓ} {f : ℕ → Ordᶜ k} {b : S.Ord ℓ} → (∀ n → Dn₊ (f n) b) → Dn₊ (lim f) b
    Rlr : ∀ {ℓ} {a : Ordᶜ k} {g : ℕ → S.Ord ℓ} n → Dn₊ a (g n) → Dn₊ a (lim g)
    Rii : ∀ {ℓ j′ j} {p′ : j′ <ᴵ k} {q : j B.< ℓ} {f : U j′ (<→◃ p′) → Ordᶜ k} {g : S.Ord< j q → S.Ord ℓ} →
          τ j ≅ᴵ j′ →
          (∀ (z : Ordᶜ j′) (z′ : S.Ord j) → D< j′ (<→◃ p′) (into (<→◃ p′) z) z′ →
             Dn₊ (f (into (<→◃ p′) z)) (g (S.coe₀ {p = q} z′))) →
          Dn₊ (limᵢ p′ f) (limᵢ q g)
    Rir : ∀ {ℓ j} {a : Ordᶜ k} {q : j B.< ℓ} {g : S.Ord< j q → S.Ord ℓ} →
          (∀ (z′ : S.Ord j) → Dn₊ a (g (S.coe₀ {p = q} z′))) → Dn₊ a (limᵢ q g)
    Rul : ∀ {ℓ i} {r : i ◃₁ k} {x : U i (◃₁→◃ r)} {b : S.Ord ℓ} → D< i (◃₁→◃ r) x b → Dn₊ (up r x) b

D< : ∀ {k} (i : Ordᴵ) (r : i ◃ k) → U i r → ∀ {ℓ} → S.Ord ℓ → Set
D< i zero         x b = Dn₊ i D< x b
D< i (suc r)      x b = D< i r x b
D< _ (self {f} n) x b = Dn₊ (f n) D< x b
D< i (lim n r)    x b = D< i r x b

Dn : ∀ {k ℓ} → Ordᶜ k → S.Ord ℓ → Set
Dn {k} = Dn₊ k D<

D→Dn : ∀ {i k ℓ} (r : i ◃ k) {x : Ordᶜ i} {b : S.Ord ℓ} → D< i r (into r x) b → Dn x b
D→Dn zero      d = d
D→Dn (suc r)   d = D→Dn r d
D→Dn (self n)  d = d
D→Dn (lim n r) d = D→Dn r d

Dn→D : ∀ {i k ℓ} (r : i ◃ k) {x : Ordᶜ i} {b : S.Ord ℓ} → Dn x b → D< i r (into r x) b
Dn→D zero      d = d
Dn→D (suc r)   d = Dn→D r d
Dn→D (self n)  d = d
Dn→D (lim n r) d = Dn→D r d

Dn-up : ∀ {k ℓ i} (r : i ◃₁ k) {x : U i (◃₁→◃ r)} {b : S.Ord ℓ} → Dn (out (◃₁→◃ r) x) b → Dn (up r x) b
Dn-up zero     d = Rul d
Dn-up (self n) d = Rul d

Dn-up⁻ : ∀ {k ℓ i} (r : i ◃₁ k) {x : U i (◃₁→◃ r)} {b : S.Ord ℓ} → D< i (◃₁→◃ r) x b → Dn (out (◃₁→◃ r) x) b
Dn-up⁻ zero     d = d
Dn-up⁻ (self n) d = d
```

## §3 关系对运算封闭

**沿 `↑` 不变.** `↑` 不改树的结构, 只改证明.

```agda
Dn-↑ : ∀ {k ℓ₁ ℓ₂} (r : ℓ₁ B.< ℓ₂) {y : Ordᶜ k} {x : S.Ord ℓ₁} → Dn y x → Dn y (S.↑ r x)
Dn-↑ r Rz        = Rz
Dn-↑ r (Rs d)    = Rs (Dn-↑ r d)
Dn-↑ r (Rsr d)   = Rsr (Dn-↑ r d)
Dn-↑ r (Rll h)   = Rll (λ n → Dn-↑ r (h n))
Dn-↑ r (Rlr n d) = Rlr n (Dn-↑ r d)
Dn-↑ r (Rii {q = q} {g = g} e h) = Rii e (λ z z′ w →
  subst (λ u → Dn _ (S.↑ r (g u))) (sym (coe-coe₀ (B.<-trans q r) q z′)) (Dn-↑ r (h z z′ w)))
Dn-↑ r (Rir {q = q} {g = g} h) = Rir (λ z′ →
  subst (λ u → Dn _ (S.↑ r (g u))) (sym (coe-coe₀ (B.<-trans q r) q z′)) (Dn-↑ r (h z′)))
Dn-↑ r (Rul {r = zero} d)   = Rul (Dn-↑ r d)
Dn-↑ r (Rul {r = self n} d) = Rul (Dn-↑ r d)
```

**沿层间搬运不变.** `tr`, `tr⁻` 不改结构, 只把 `limᵢ` 节点换到 $\cong^\mathsf{I}$ 相关的代表元上. 四重互递归, 与 Level 的 `tr`, `tr⁻`, `res`, `res⁻` 一一对应.

```agda
Dn-tr    : ∀ {a a′ ℓ} (e : a ≅ᴵ a′) {y : Ordᶜ a} {x : S.Ord ℓ} → Dn y x → Dn (tr e y) x
Dn-tr⁻   : ∀ {a a′ ℓ} (e : a ≅ᴵ a′) {y : Ordᶜ a′} {x : S.Ord ℓ} → Dn y x → Dn (tr⁻ e y) x
Dn-back  : ∀ {j a b ℓ} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {x : S.Ord ℓ} → Dn u x → Dn (back (res q e) u) x
Dn-back⁻ : ∀ {j a b ℓ} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {x : S.Ord ℓ} → Dn u x → Dn (back (res⁻ q e) u) x

Dn-tr e Rz        = Rz
Dn-tr e (Rs d)    = Rs (Dn-tr e d)
Dn-tr e (Rsr d)   = Rsr (Dn-tr e d)
Dn-tr e (Rll h)   = Rll (λ n → Dn-tr e (h n))
Dn-tr e (Rlr n d) = Rlr n (Dn-tr e d)
Dn-tr e (Rii {p′ = q} {f = f} e₀ h) = Rii (≅ᴵ-trans e₀ (eq (res q e))) (λ z z′ w →
  subst (λ u → Dn (tr e (f (into (<→◃ q) (back (res q e) u)))) _) (sym (out-into (<→◃ (lt (res q e))) z))
        (Dn-tr e (h (back (res q e) z) z′ (Dn→D (<→◃ q) (Dn-back q e (D→Dn (<→◃ (lt (res q e))) w))))))
Dn-tr e (Rir h)   = Rir (λ z′ → Dn-tr e (h z′))
Dn-tr (s≅ e) (Rul {r = zero} d)   = Rul (Dn-tr e d)
Dn-tr (l≅ f) (Rul {r = self n} d) = Rul (Dn-tr (f n) d)

Dn-tr⁻ e Rz        = Rz
Dn-tr⁻ e (Rs d)    = Rs (Dn-tr⁻ e d)
Dn-tr⁻ e (Rsr d)   = Rsr (Dn-tr⁻ e d)
Dn-tr⁻ e (Rll h)   = Rll (λ n → Dn-tr⁻ e (h n))
Dn-tr⁻ e (Rlr n d) = Rlr n (Dn-tr⁻ e d)
Dn-tr⁻ e (Rii {p′ = q} {f = f} e₀ h) = Rii (≅ᴵ-trans e₀ (eq (res⁻ q e))) (λ z z′ w →
  subst (λ u → Dn (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) u)))) _) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
        (Dn-tr⁻ e (h (back (res⁻ q e) z) z′ (Dn→D (<→◃ q) (Dn-back⁻ q e (D→Dn (<→◃ (lt (res⁻ q e))) w))))))
Dn-tr⁻ e (Rir h)   = Rir (λ z′ → Dn-tr⁻ e (h z′))
Dn-tr⁻ (s≅ e) (Rul {r = zero} d)   = Rul (Dn-tr⁻ e d)
Dn-tr⁻ (l≅ f) (Rul {r = self n} d) = Rul (Dn-tr⁻ (f n) d)

Dn-back zero      (s≅ e) d = Dn-tr⁻ e d
Dn-back (suc q)   (s≅ e) d = Dn-back q e d
Dn-back (lim n q) (l≅ f) d = Dn-back q (f n) d

Dn-back⁻ zero      (s≅ e) d = Dn-tr e d
Dn-back⁻ (suc q)   (s≅ e) d = Dn-back⁻ q e d
Dn-back⁻ (lim n q) (l≅ f) d = Dn-back⁻ q (f n) d
```

**加法.** 右边的 $x'$ 任意: `add-r`. 左边 $a$ 不超过 $a'$, $b$ 不超过 $b'$, 和就不超过和: 对 $b$ 的关系递归.

```agda
Dn-add-r : ∀ {k ℓ} {a : Ordᶜ k} {a′ : S.Ord ℓ} (b′ : S.Ord ℓ) → Dn a a′ → Dn a (a′ S.+ b′)
Dn-add-r zero       d = d
Dn-add-r (suc b′)   d = Rsr (Dn-add-r b′ d)
Dn-add-r (lim g)    d = Rlr 0 (Dn-add-r (g 0) d)
Dn-add-r (limᵢ q g) d = Rir (λ z′ → Dn-add-r (g (S.coe₀ {p = q} z′)) d)

Dn-add : ∀ {k₁ k₂ ℓ} {a : Ordᶜ k₂} {σ : Simᴵ k₁ k₂} {a′ : S.Ord ℓ} {b : Ordᶜ k₁} {b′ : S.Ord ℓ} →
         Dn a a′ → Dn b b′ → Dn (add a σ b) (a′ S.+ b′)
Dn-add {b′ = b′} da Rz    = Dn-add-r b′ da
Dn-add da (Rs d)          = Rs (Dn-add da d)
Dn-add da (Rsr d)         = Rsr (Dn-add da d)
Dn-add da (Rll h)         = Rll (λ n → Dn-add da (h n))
Dn-add da (Rlr n d)       = Rlr n (Dn-add da d)
Dn-add {a = a} {σ = σ} {a′ = a′} da (Rii {p′ = q} {q = q₁} {f = f} {g = g} e h) = Rii e (λ z z′ w →
  subst (λ u → Dn (add a σ (f (into (<→◃ q) u))) (a′ S.+ g (S.coe₀ {p = q₁} z′))) (sym (out-into (<→◃ (σ q)) z))
        (Dn-add da (h z z′ (Dn→D (<→◃ q) (D→Dn (<→◃ (σ q)) w)))))
Dn-add da (Rir h)         = Rir (λ z′ → Dn-add da (h z′))
Dn-add da (Rul {r = zero} d)   = Dn-add da d
Dn-add da (Rul {r = self n} d) = Dn-add da d
```

## §4 $\Omega$ 与第一条链

```agda
Dn-Ω : ∀ {a a′} → τ a ≅ᴵ a′ → Dn (Ω a′) (S.Ω a)
Dn-Ω {a = B.zero}    z≅     = Rlr 1 (Rs Rz)
Dn-Ω {a = B.suc a}   (s≅ e) = Rii e (λ z z′ w → Rul (Dn-↑ B.zero w))
Dn-Ω {a = B.lim f m} (l≅ h) = Rll (λ n → Rlr n (Rul (Dn-↑ (B.f<l n) (Dn-Ω (h n)))))
```

`B1`: 目标层上的 $\Omega_{i'}$ 不超过 $\psi_i(x)$, 对一切 $x$. 对 src 的树递归. `ψ<` 的 `with` 要抽象同一个 `<-dec`.

```agda
Dn-B1 : ∀ {i i′ ℓ} (e : τ i ≅ᴵ i′) (p : i B.< ℓ) (x : S.Ord ℓ) → Dn (Ω i′) (S.ψ< p x)
Dn-B1 e p zero       = Dn-Ω e
Dn-B1 e p (suc a)    = Rlr 1 (Dn-B1 e p a)
Dn-B1 e p (lim g)    = Rlr 0 (Dn-B1 e p (g 0))
Dn-B1 e p (limᵢ q g) with B.<-dec q p
... | injᵃ j<i  = Rir (λ z′ → Dn-B1 e p (g (S.coe {p = j<i} {q = q} (S.coe₀ {p = j<i} z′))))
... | injᵇ _    = Rlr 0 (Dn-B1 e p (g (S.coe₀ {p = q} zero)))
... | injᶜ refl = Rlr 1 (Dn-B1 e p (g (S.coe₀ {p = q} zero)))
```

## §5 折叠

`Dn-ψ`: 目标层 $\tau$ 相关时, 折叠保持 `Dn`. 链的比较错开一位: Level 的链从 $\Omega_j$ 起, src 的链从 $0$ 起, 所以 Level 的第 $n$ 项不超过 src 的第 $n+1$ 项 (第 0 步是 `Dn-B1`). 这里不要分支单调, 也不要 `Good`: `Rii` 的前提已经是 "相关输入给出相关输出".

```agda
iter-Dn : ∀ {k ℓ} {A : Ordᶜ k} {A′ : S.Ord ℓ} → Dn A A′ → ∀ n → Dn (iter (A +_) zero n) (iter (A′ S.+_) zero n)
iter-Dn d zero    = Rz
iter-Dn d (suc n) = Dn-add d (iter-Dn d n)

Dn-ψ : ∀ {i i′ k ℓ′ ℓ} {y : Ordᶜ k} {x : S.Ord ℓ} (e : τ i ≅ᴵ i′) (p′ : i′ <ᴵ ℓ′) (σ : Simᴵ k ℓ′) (p : i B.< ℓ) →
       Dn y x → Dn (ψ p′ σ y) (S.ψ< p x)

chain-b : ∀ {j j′ k ℓ} {q′ : j′ <ᴵ k} {q : j B.< ℓ} {f : U j′ (<→◃ q′) → Ordᶜ k} {g : S.Ord< j q → S.Ord ℓ} →
          τ j ≅ᴵ j′ →
          (∀ (z : Ordᶜ j′) (z′ : S.Ord j) → D< j′ (<→◃ q′) (into (<→◃ q′) z) z′ → Dn (f (into (<→◃ q′) z)) (g (S.coe₀ {p = q} z′))) →
          ∀ n → Dn (iter (λ x → ψ q′ (λ r → r) (f (into (<→◃ q′) x))) (Ω j′) n)
                   (iter (λ x → S.ψ< q (g (S.coe₀ {p = q} x))) zero (suc n))
chain-b {q′ = q′} {q = q} {g = g} ej h zero    = Dn-B1 ej q (g (S.coe₀ {p = q} zero))
chain-b {q′ = q′} {q = q} {f = f} {g = g} ej h (suc n) = Dn-ψ ej q′ (λ r → r) q (h _ _ (Dn→D (<→◃ q′) (chain-b {q′ = q′} {q = q} {f = f} {g = g} ej h n)))

chain-c : ∀ {j j′ k ℓ} {q : j B.< ℓ} (p : j B.< ℓ) (q′ : j′ <ᴵ k) {f : U j′ (<→◃ q′) → Ordᶜ k} {g : S.Ord< j q → S.Ord ℓ} →
          τ j ≅ᴵ j′ →
          (∀ (z : Ordᶜ j′) (z′ : S.Ord j) → D< j′ (<→◃ q′) (into (<→◃ q′) z) z′ → Dn (f (into (<→◃ q′) z)) (g (S.coe₀ {p = q} z′))) →
          ∀ n → Dn (iter (λ x → ψ q′ (λ r → r) (f (into (<→◃ q′) x))) (Ω j′) n)
                   (iter (λ x → S.ψ< p (g (S.coe₀ {p = q} x))) zero (suc n))
chain-c {q = q} p q′ {g = g} ej h zero    = Dn-B1 ej p (g (S.coe₀ {p = q} zero))
chain-c {q = q} p q′ {f = f} {g = g} ej h (suc n) = Dn-ψ ej q′ (λ r → r) p (h _ _ (Dn→D (<→◃ q′) (chain-c {q = q} p q′ {f = f} {g = g} ej h n)))

Dn-ψ {x = x} e p′ σ p Rz = Dn-B1 e p x
Dn-ψ e p′ σ p (Rs d)     = Rll (λ n → Rlr n (iter-Dn (Dn-ψ e p′ σ p d) n))
Dn-ψ e p′ σ p (Rsr d)    = Rlr 1 (Dn-ψ e p′ σ p d)
Dn-ψ e p′ σ p (Rll h)    = Rll (λ n → Dn-ψ e p′ σ p (h n))
Dn-ψ e p′ σ p (Rlr n d)  = Rlr n (Dn-ψ e p′ σ p d)
Dn-ψ e p′ σ p (Rir {q = q} {g = g} h) with B.<-dec q p
... | injᵃ j<i  = Rir (λ z′ → subst (λ v → Dn _ (S.ψ< p (g v))) (sym (coe-coe₀ j<i q z′)) (Dn-ψ e p′ σ p (h z′)))
... | injᵇ _    = Rlr 0 (Dn-ψ e p′ σ p (h zero))
... | injᶜ refl = Rlr 1 (Dn-ψ e p′ σ p (h zero))
Dn-ψ e p′ σ p (Rul {r = zero} d)   = Dn-ψ e p′ (λ q → σ (suc q)) p d
Dn-ψ e p′ σ p (Rul {r = self n} d) = Dn-ψ e p′ (λ q → σ (lim n q)) p d
Dn-ψ e p′ σ p (Rii {p′ = q′} {q = q} {f = f} {g = g} ej h) with <ᴵ-dec (σ q′) p′ | B.<-dec q p
... | injᵃ (via e₁ r) | injᵃ j<i = Rii (≅ᴵ-trans ej e₁) (λ z z′ w →
        subst₂ (λ u v → Dn (ψ p′ σ (f (into (<→◃ q′) (tr⁻ e₁ u)))) (S.ψ< p (g v)))
               (sym (out-into (<→◃ r) z)) (sym (coe-coe₀ j<i q z′))
               (Dn-ψ e p′ σ p (h (tr⁻ e₁ z) z′ (Dn→D (<→◃ q′) (Dn-tr⁻ e₁ (D→Dn (<→◃ r) w))))))
... | injᵃ (via e₁ r) | injᵇ i<j  = ⊥-elim (clash-lt-lt ej e (via e₁ r) i<j)
... | injᵃ (via e₁ r) | injᶜ refl = ⊥-elim (clash-lt-eq ej e (via e₁ r) refl)
... | injᵇ r          | injᵃ j<i  = ⊥-elim (clash-gt-lt ej e r j<i)
... | injᶜ r          | injᵃ j<i  = ⊥-elim (clash-eq-lt ej e r j<i)
... | injᵇ _          | injᵇ _    = Rll (λ n → Rlr (suc n) (Dn-ψ e p′ σ p (h _ _ (Dn→D (<→◃ q′) (chain-b {q′ = q′} {q = q} {f = f} {g = g} ej h n)))))
... | injᶜ _          | injᵇ _    = Rll (λ n → Rlr (suc n) (Dn-ψ e p′ σ p (h _ _ (Dn→D (<→◃ q′) (chain-b {q′ = q′} {q = q} {f = f} {g = g} ej h n)))))
... | injᵇ _          | injᶜ refl = Rll (λ n → Rlr (suc (suc n)) (Dn-ψ e p′ σ p (h _ _ (Dn→D (<→◃ q′) (chain-c {q = q} p q′ {f = f} {g = g} ej h n)))))
... | injᶜ _          | injᶜ refl = Rll (λ n → Rlr (suc (suc n)) (Dn-ψ e p′ σ p (h _ _ (Dn→D (<→◃ q′) (chain-c {q = q} p q′ {f = f} {g = g} ej h n)))))
```

## §6 结论

第 0 层上 `Dn` 就是 `≼` 经翻译. `Ψ⁰≼<`: 层号是 `Ordᴰ` 的任意非零元, Level 的 $\psi^0(\Omega_{\tau a})$ 不超过 src 的 $\psi_0(\Omega_a)$. 这一半没有用到层号的任何性质.

```agda
Dn→≼ : ∀ {y : Ordᶜ zero} {x : S.Ord₀} → Dn y x → y ≼ tr₀ x
Dn→≼ Rz        = z≼
Dn→≼ (Rs d)    = s≼s (Dn→≼ d)
Dn→≼ (Rsr d)   = ≼-suc (Dn→≼ d)
Dn→≼ (Rll h)   = l≼ (λ n → Dn→≼ (h n))
Dn→≼ (Rlr n d) = ≼l n (Dn→≼ d)
Dn→≼ (Rii {p′ = ()} e h)
Dn→≼ (Rir {q = ()} h)
Dn→≼ (Rul {r = ()} d)

Ψ⁰≼<  : ∀ {a} (p : B.zero B.< a) → ψ⁰ (Ω (τ a)) ≼ tr₀ (S.ψ< p (S.Ω a))
Ψ⁰≼< {a} p = ≼-trans (≅→≼ (ψ⁰≅ψ {p = τ-< p} {σ = λ q → q} (Ω-refl (τ a))))
                     (Dn→≼ (Dn-ψ z≅ (τ-< p) (λ q → q) p (Dn-Ω (≅ᴵ-refl (τ a)))))
```
