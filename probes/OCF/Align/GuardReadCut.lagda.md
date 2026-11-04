# 切口: 分支 $G\,b$ 是 $G(b+1)$ 的切口

> 不含记号. 结论写在 [GuardRead](GuardRead.lagda.md). 读回的项 ([GuardTightUni](GuardTightUni.lagda.md)) 上的一个归纳关系 `Sp a y`: **$y$ 的每个位置, 要么落在 $a$ 里, 要么在 $a$ 之上**, 由结构给. 一个定义, 没有阶段, 没有闭包形状.
>
> - `s-eq`: $y\cong a$. `s-cg`: $z\cong y$, 搬过去再看, 什么节点都搬得动. `s-mv`: $z\sqsubseteq y$, 搬过去再看, 只搬后继与闭包节点. `s-zero`: 0 没有位置要读.
> - `s-suc`: 带证据 $a\sqsubseteq b$, 所以 $b+1$ 这个节点在 $a$ 之上. `s-lc`: 带证据 $a\sqsubseteq\mathrm{lim}_i f$. `s-lim`: **不带证据**, 极限节点自己的位置不判定 (带证据要比较 $a$ 与 $\lim h$, 这是 [GuardReadNeg](GuardReadNeg.lagda.md) 的 `no-cut`).
> - 封闭性: `sp-bot` (切口从 $c$ 传到 $c+x$), `sp-iter`, `Sp-ψ¹`, `Sp-ψ`, `Sp-add`, `Sp-tr`, `Sp-tr⁻`, `sp-Ωψ` ($\Omega_j$ 是 $\psi_j(y)$ 的切口). 都对 `Sp` 或项结构递归.
> - `read`: 由切口得到层号上的读法 `Cu`. `Cu` 的规格不空: 后继节点与闭包节点要么落在 $a$ 里 (`cIn`), 要么 $a$ 在它之下 (`cNw`); 只有 0 与极限节点可以不答 (`cUn`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardReadCut where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum hiding (steps)
open Restr
open import OCF.Align.GuardTightLv using (Dom₀; module Lv)
open Lv Dom₀ using (LG; _⊴_; ⊴-trans; ≈→⊴; ≈-sym; Cp; self; suc; lim; fst; bra; zero; AdmC; ⊴p; ⊴K; viaᴸ; viaᴷ; lc; _≈_; s≈; o≈; z≈; l≈; Src)
import OCF.Align.GuardTightUni as Uni
open Uni Dom₀ using (_⊑ᵒ_; _≈ᵒ_; idO; ≈ᵒ-reflʳ; ≅→⊑ᵒ; ψ-cong; ψ¹-cong; add-cong; tr-cong; tr⁻-cong; up-l; add-r; B1; B1¹;
                  ψ¹; ψ¹-≅; em; em-self; rb₀; rb₁; rbB; rbB-≈; BL; b0; b1; chain; chain-≅; i-resp; self-tr; self-tr⁻; self-back; self-back⁻; ≅-reflˡ; ≅-reflʳ)
open import OCF.Align.GuardTightBase using (Lk; lkT; lkC; mvC; mvc; toCpS; fromCpS; admToS; admFromS)
```

## §1 切口

`s-mv` 的 $z,y$ 同层: 读法要在层号上搬位置, 层号只读 0, 1 两层, 这样 `read` 的递归不出这两层. 层不同的情形只有 0 (`s-zero`).

```agda
data Sp {k} (a : Ordᶜ k) : ∀ {ℓ} → Ordᶜ ℓ → Set where
  s-zero : ∀ {ℓ} → a ≅ a → Sp a (zero {ℓ = ℓ})
  s-eq   : ∀ {ℓ} {y : Ordᶜ ℓ} → a ≅ y → Sp a y
  s-cg   : ∀ {ℓ} {z y : Ordᶜ ℓ} → z ≅ y → Sp a y → Sp a z
  s-mv   : ∀ {ℓ} {z y : Ordᶜ ℓ} → z ⊑ᵒ y → Sp a y → Sp a z
  s-suc  : ∀ {ℓ} {b : Ordᶜ ℓ} → a ⊑ᵒ b → b ≅ b → Sp a b → Sp a (suc b)
  s-lim  : ∀ {ℓ} {h : ℕ → Ordᶜ ℓ} → (∀ n → Sp a (h n)) → Sp a (lim h)
  s-lc   : ∀ {ℓ j} {q : j <ᴵ ℓ} {f : U j (<→◃ q) → Ordᶜ ℓ} → a ⊑ᵒ limᵢ q f → limᵢ q f ≅ limᵢ q f →
           (∀ (z : Ordᶜ j) → z ≅ z → Sp a (f (into (<→◃ q) z))) → Sp a (limᵢ q f)
  s-up   : ∀ {ℓ j} {r : j ◃₁ ℓ} {x : U j (◃₁→◃ r)} → Sp a (out (◃₁→◃ r) x) → Sp a (up r x)

⊑ᵒ-trans : ∀ {k k′} {x : Ordᶜ k} {y z : Ordᶜ k′} → x ⊑ᵒ y → y ⊑ᵒ z → x ⊑ᵒ z
⊑ᵒ-trans h h′ o = ⊴-trans (h o) (h′ (≈ᵒ-reflʳ o))

-- 位置经 `into`, `out` 回来: 对 `r` 递归, 叶子上定义相等
oi : ∀ {i ℓ} (r : i ◃ ℓ) (P : Ordᶜ i → Set) {x} → P x → P (out r (into r x))
oi zero      P p = p
oi (suc r)   P p = oi r P p
oi (self n)  P p = p
oi (lim n r) P p = oi r P p
```

## §2 底

**`sp-bot`: 若 $a\sqsubseteq c$ 且 $a$ 是 $c$ 的切口, 则 $a$ 是 $c+x$ 的切口, 对一切 $x$.** 取 $a=c$ 就是 "$c$ 是 $c+x$ 的切口". 这是 $a+\eta$, $c\cdot n$, $\lim_n(F\eta)\cdot n$ 共同的来源. `sp-iter`: 于是 $a$ 是 $c\cdot n$ 的切口. **对 $x$ 递归, 不判定任何东西.**

```agda
sp-bot : ∀ {k ℓ j} {a : Ordᶜ k} {c c′ : Ordᶜ ℓ} {σ : Simᴵ j ℓ} (x : Ordᶜ j) → a ⊑ᵒ c → Sp a c → c ≅ c′ → x ≅ x → Sp a (add c′ σ x)
sp-bot zero m S ec ex = s-cg (≅-sym ec) S
sp-bot {σ = σ} (suc b) m S ec ex =
  s-suc (⊑ᵒ-trans m (add-r {σ = σ} b ec eb)) (add-≅ {σ = σ} {σ′ = σ} (≅-reflʳ ec) eb) (sp-bot {σ = σ} b m S ec eb)
  where
  eb = Uni.s-inv Dom₀ ex
sp-bot {σ = σ} (lim h) m S ec ex = s-lim (λ n → sp-bot {σ = σ} (h n) m S ec (Uni.l-inv Dom₀ ex n))
sp-bot {c′ = c′} {σ = σ} (limᵢ q g) m S ec ex =
  s-lc (⊑ᵒ-trans m (add-r {σ = σ} (limᵢ q g) ec ex)) (add-≅ {σ = σ} {σ′ = σ} (≅-reflʳ ec) ex)
       (λ z ez → oi (<→◃ (σ q)) (λ u → Sp _ (add c′ σ (g (into (<→◃ q) u))))
                    (sp-bot {σ = σ} (g (into (<→◃ q) z)) m S ec (i-resp ex ez)))
sp-bot (up zero x) m S ec ex     = sp-bot x m S ec (Uni.u-refl Dom₀ zero ex)
sp-bot (up (self n) x) m S ec ex = sp-bot x m S ec (Uni.u-refl Dom₀ (self n) ex)

iter-self : ∀ {ℓ} {c : Ordᶜ ℓ} → c ≅ c → ∀ n → iter (c +_) zero n ≅ iter (c +_) zero n
iter-self ec = iter-R _≅_ (λ e → add-≅ {σ = λ q → q} {σ′ = λ q → q} ec e) z≅

sp-iter : ∀ {k ℓ} {a : Ordᶜ k} {c : Ordᶜ ℓ} → a ⊑ᵒ c → Sp a c → a ≅ a → c ≅ c → ∀ n → Sp a (iter (c +_) zero n)
sp-iter m S ea ec zero    = s-zero ea
sp-iter m S ea ec (suc n) = sp-bot (iter (_ +_) zero n) m S ec (iter-self ec n)
```

## §3 折叠与加法保持切口

每一条都对 `Sp` 结构递归. $\psi$ 把后继变成 $\lim_n c\cdot n$ (`sp-iter`), 把高层的 `limᵢ` 变成链的极限 (`chain`), 证据由 `ψ-cong` 搬过去. **极限步没有比较.**

```agda
Sp-ψ¹ : ∀ {k ℓ} {a : Ordᶜ k} {y : Ordᶜ ℓ} → a ≅ a → Sp a y → Sp (ψ¹ a) (ψ¹ y)
Sp-ψ¹ ea (s-zero _) = s-mv (B1¹ _ ea) (s-eq (ψ¹-≅ ea))
Sp-ψ¹ ea (s-eq e) = s-eq (ψ¹-≅ e)
Sp-ψ¹ ea (s-cg d S) = s-cg (ψ¹-≅ d) (Sp-ψ¹ ea S)
Sp-ψ¹ ea (s-mv m S) = s-mv (ψ¹-cong m) (Sp-ψ¹ ea S)
Sp-ψ¹ ea (s-suc ev eb S) = s-lim (sp-iter (ψ¹-cong ev) (Sp-ψ¹ ea S) (ψ¹-≅ ea) (ψ¹-≅ eb))
Sp-ψ¹ ea (s-lim K) = s-lim (λ n → Sp-ψ¹ ea (K n))
Sp-ψ¹ ea (s-lc {j = zero} ev ex K) = s-lc (ψ¹-cong ev) (ψ¹-≅ ex) (λ z ez → Sp-ψ¹ ea (K z ez))
Sp-ψ¹ ea (s-lc {j = suc j} ev ex K) = s-lim (λ n → Sp-ψ¹ ea (K _ (chain-≅ ex n)))
Sp-ψ¹ ea (s-lc {j = lim g s} ev ex K) = s-lim (λ n → Sp-ψ¹ ea (K _ (chain-≅ ex n)))
Sp-ψ¹ ea (s-up {r = zero} {x = x} S) = Sp-ψ¹ {y = x} ea S
Sp-ψ¹ ea (s-up {r = self n} {x = x} S) = Sp-ψ¹ {y = x} ea S

Sp-ψ : ∀ {i k₁ ℓ₁ k₂ ℓ₂} {p₁ : i <ᴵ ℓ₁} {σ₁ : Simᴵ k₁ ℓ₁} {p₂ : i <ᴵ ℓ₂} {σ₂ : Simᴵ k₂ ℓ₂} {a : Ordᶜ k₁} {y : Ordᶜ k₂} →
       a ≅ a → Sp a y → Sp (ψ p₁ σ₁ a) (ψ p₂ σ₂ y)
Sp-ψ {p₁ = p₁} {σ₁ = σ₁} ea (s-zero _) = s-mv (B1 {q = p₁} {σ = σ₁} _ ea) (s-eq (ψ-≅ (≅ᴵ-refl _) ea))
Sp-ψ {i} ea (s-eq e) = s-eq (ψ-≅ (≅ᴵ-refl i) e)
Sp-ψ {i} {p₂ = p₂} {σ₂ = σ₂} ea (s-cg d S) = s-cg (ψ-≅ {p = p₂} {σ = σ₂} {p′ = p₂} {σ′ = σ₂} (≅ᴵ-refl i) d) (Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea S)
Sp-ψ {i} {p₂ = p₂} {σ₂ = σ₂} {y = y} ea (s-mv {y = y′} m S) = s-mv (ψ-cong {p = p₂} {p′ = p₂} {σ = σ₂} {σ′ = σ₂} m) (Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea S)
Sp-ψ {i} {p₁ = p₁} {σ₁ = σ₁} {p₂ = p₂} {σ₂ = σ₂} ea (s-suc ev eb S) =
  s-lim (sp-iter (ψ-cong ev) (Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea S)
                 (ψ-≅ {p = p₁} {σ = σ₁} {p′ = p₁} {σ′ = σ₁} (≅ᴵ-refl i) ea) (ψ-≅ {p = p₂} {σ = σ₂} {p′ = p₂} {σ′ = σ₂} (≅ᴵ-refl i) eb))
Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea (s-lim K) = s-lim (λ n → Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea (K n))
Sp-ψ {i} {p₁ = p₁} {σ₁ = σ₁} {p₂ = p₂} {σ₂ = σ₂} {a = a} ea (s-lc {q = q} {f = f} ev ex K)
  with <ᴵ-dec (σ₂ q) p₂ | ψ-≅ {p = p₂} {σ = σ₂} {p′ = p₂} {σ′ = σ₂} (≅ᴵ-refl i) ex | ψ-cong {p = p₁} {p′ = p₂} {σ = σ₁} {σ′ = σ₂} ev
... | injᵃ (via e r) | ex′ | ev′ =
  s-lc ev′ ex′ (λ z ez → oi (<→◃ r) (λ u → Sp (ψ p₁ σ₁ a) (ψ p₂ σ₂ (f (into (<→◃ q) (tr⁻ e u)))))
                            (Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea (K (tr⁻ e z) (self-tr⁻ e ez))))
... | injᵇ _ | ex′ | ev′ = s-lim (λ n → Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea (K _ (chain-≅ ex n)))
... | injᶜ _ | ex′ | ev′ = s-lim (λ n → Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea (K _ (chain-≅ ex n)))
Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea (s-up {r = zero} {x = x} S) = Sp-ψ {p₂ = p₂} {σ₂ = λ q → σ₂ (suc q)} {y = x} ea S
Sp-ψ {p₂ = p₂} {σ₂ = σ₂} ea (s-up {r = self n} {x = x} S) = Sp-ψ {p₂ = p₂} {σ₂ = λ q → σ₂ (lim n q)} {y = x} ea S

Sp-add : ∀ {ℓ k₁ k₂} {c c′ : Ordᶜ ℓ} {σ₁ : Simᴵ k₁ ℓ} {σ₂ : Simᴵ k₂ ℓ} {a : Ordᶜ k₁} {y : Ordᶜ k₂} →
         c ≅ c′ → a ≅ a → Sp a y → Sp (add c σ₁ a) (add c′ σ₂ y)
Sp-add {σ₁ = σ₁} {a = a} ec ea (s-zero _) =
  s-mv (add-r {σ = σ₁} a (≅-sym ec) ea) (s-eq (add-≅ {σ = σ₁} {σ′ = σ₁} (≅-reflˡ ec) ea))
Sp-add ec ea (s-eq e) = s-eq (add-≅ ec e)
Sp-add {σ₂ = σ₂} ec ea (s-cg d S) = s-cg (add-≅ {σ = σ₂} {σ′ = σ₂} (≅-reflʳ ec) d) (Sp-add {σ₂ = σ₂} ec ea S)
Sp-add {σ₂ = σ₂} ec ea (s-mv m S) = s-mv (add-cong {σ = σ₂} {σ′ = σ₂} (≅-reflʳ ec) m) (Sp-add {σ₂ = σ₂} ec ea S)
Sp-add {σ₂ = σ₂} ec ea (s-suc ev eb S) = s-suc (add-cong ec ev) (add-≅ {σ = σ₂} {σ′ = σ₂} (≅-reflʳ ec) eb) (Sp-add {σ₂ = σ₂} ec ea S)
Sp-add {σ₂ = σ₂} ec ea (s-lim K) = s-lim (λ n → Sp-add {σ₂ = σ₂} ec ea (K n))
Sp-add {c = c} {c′ = c′} {σ₁ = σ₁} {σ₂ = σ₂} {a = a} ec ea (s-lc {q = q} {f = f} ev ex K) =
  s-lc (add-cong ec ev) (add-≅ {σ = σ₂} {σ′ = σ₂} (≅-reflʳ ec) ex)
       (λ z ez → oi (<→◃ (σ₂ q)) (λ u → Sp (add c σ₁ a) (add c′ σ₂ (f (into (<→◃ q) u))))
                    (Sp-add {σ₂ = σ₂} ec ea (K z ez)))
Sp-add {σ₂ = σ₂} ec ea (s-up {r = zero} {x = x} S) = Sp-add {σ₂ = λ q → σ₂ (suc q)} {y = x} ec ea S
Sp-add {σ₂ = σ₂} ec ea (s-up {r = self n} {x = x} S) = Sp-add {σ₂ = λ q → σ₂ (lim n q)} {y = x} ec ea S
```

## §4 层间搬运保持切口

`tr`, `tr⁻` 只在 `ψ` 的穿透分支出现 (下标类型的等价). 与 `Good-tr` 同形.

```agda
Sp-tr : ∀ {a₁ b₁ a₂ b₂} (e : a₁ ≅ᴵ b₁) (e′ : a₂ ≅ᴵ b₂) {a : Ordᶜ a₁} {y : Ordᶜ a₂} → a ≅ a → Sp a y → Sp (tr e a) (tr e′ y)
Sp-tr e e′ ea (s-zero _) = s-zero (self-tr e ea)
Sp-tr e e′ ea (s-eq d) = s-eq (tr-≅ e (≅-tr e′ d))
Sp-tr e e′ ea (s-cg d S) = s-cg (tr-≅ e′ (≅-tr e′ d)) (Sp-tr e e′ ea S)
Sp-tr e e′ ea (s-mv m S) = s-mv (tr-cong {e = e′} {e′ = e′} m) (Sp-tr e e′ ea S)
Sp-tr e e′ ea (s-suc ev eb S) = s-suc (tr-cong ev) (self-tr e′ eb) (Sp-tr e e′ ea S)
Sp-tr e e′ ea (s-lim K) = s-lim (λ n → Sp-tr e e′ ea (K n))
Sp-tr e e′ {a = a} ea (s-lc {q = q} {f = f} ev ex K) =
  s-lc (tr-cong ev) (self-tr e′ ex)
       (λ z ez → oi (<→◃ (lt (res q e′))) (λ u → Sp (tr e a) (tr e′ (f (into (<→◃ q) (back (res q e′) u)))))
                    (Sp-tr e e′ ea (K _ (self-back q e′ ez))))
Sp-tr e (s≅ e′) ea (s-up {r = zero} S) = s-up (Sp-tr e e′ ea S)
Sp-tr e (l≅ h) ea (s-up {r = self n} S) = s-up (Sp-tr e (h n) ea S)

Sp-tr⁻ : ∀ {a₁ b₁ a₂ b₂} (e : a₁ ≅ᴵ b₁) (e′ : a₂ ≅ᴵ b₂) {a : Ordᶜ b₁} {y : Ordᶜ b₂} → a ≅ a → Sp a y → Sp (tr⁻ e a) (tr⁻ e′ y)
Sp-tr⁻ e e′ ea (s-zero _) = s-zero (self-tr⁻ e ea)
Sp-tr⁻ e e′ ea (s-eq d) = s-eq (tr⁻-≅ e (≅-tr⁻ e′ d))
Sp-tr⁻ e e′ ea (s-cg d S) = s-cg (tr⁻-≅ e′ (≅-tr⁻ e′ d)) (Sp-tr⁻ e e′ ea S)
Sp-tr⁻ e e′ ea (s-mv m S) = s-mv (tr⁻-cong {e = e′} {e′ = e′} m) (Sp-tr⁻ e e′ ea S)
Sp-tr⁻ e e′ ea (s-suc ev eb S) = s-suc (tr⁻-cong ev) (self-tr⁻ e′ eb) (Sp-tr⁻ e e′ ea S)
Sp-tr⁻ e e′ ea (s-lim K) = s-lim (λ n → Sp-tr⁻ e e′ ea (K n))
Sp-tr⁻ e e′ {a = a} ea (s-lc {q = q} {f = f} ev ex K) =
  s-lc (tr⁻-cong ev) (self-tr⁻ e′ ex)
       (λ z ez → oi (<→◃ (lt (res⁻ q e′))) (λ u → Sp (tr⁻ e a) (tr⁻ e′ (f (into (<→◃ q) (back (res⁻ q e′) u)))))
                    (Sp-tr⁻ e e′ ea (K _ (self-back⁻ q e′ ez))))
Sp-tr⁻ e (s≅ e′) ea (s-up {r = zero} S) = s-up (Sp-tr⁻ e e′ ea S)
Sp-tr⁻ e (l≅ h) ea (s-up {r = self n} S) = s-up (Sp-tr⁻ e (h n) ea S)
```

## §5 $\Omega_j$ 是 $\psi_j(y)$ 的切口

**`sp-Ωψ`.** 与 `B1` (下界 $\Omega_j\sqsubseteq\psi_j(y)$) 同一个递归. 这就是第 5 站要的: $F(b+1)$ 是 $\psi_1(\text{链})$ 的极限, 链的每一点是 $\Omega_b$ 或 $\psi_b(\dots)$.

```agda
sp-Ωψ : ∀ {j ℓ k} {q : j <ᴵ ℓ} {σ : Simᴵ k ℓ} (y : Ordᶜ k) → y ≅ y → Sp (Ω j) (ψ q σ y)
sp-Ωψ {j} zero e = s-eq (Ω-refl j)
sp-Ωψ {j} {q = q} {σ = σ} (suc a) e =
  s-lim (sp-iter (B1 {q = q} {σ = σ} a ea) (sp-Ωψ {q = q} {σ = σ} a ea) (Ω-refl j) (ψ-≅ {p = q} {σ = σ} {p′ = q} {σ′ = σ} (≅ᴵ-refl j) ea))
  where ea = Uni.s-inv Dom₀ e
sp-Ωψ {q = q} {σ = σ} (lim h) e = s-lim (λ n → sp-Ωψ {q = q} {σ = σ} (h n) (Uni.l-inv Dom₀ e n))
sp-Ωψ {j} {q = q} {σ = σ} (limᵢ q′ g) e
  with <ᴵ-dec (σ q′) q | ψ-≅ {p = q} {σ = σ} {p′ = q} {σ′ = σ} (≅ᴵ-refl j) e | B1 {q = q} {σ = σ} (limᵢ q′ g) e
... | injᵃ (via e₁ r) | ex′ | ev′ =
  s-lc ev′ ex′ (λ z ez → oi (<→◃ r) (λ u → Sp (Ω j) (ψ q σ (g (into (<→◃ q′) (tr⁻ e₁ u)))))
                            (sp-Ωψ {q = q} {σ = σ} (g (into (<→◃ q′) (tr⁻ e₁ z))) (i-resp e (self-tr⁻ e₁ ez))))
... | injᵇ _ | ex′ | ev′ = s-lim (λ n → sp-Ωψ {q = q} {σ = σ} _ (i-resp e (chain-≅ e n)))
... | injᶜ _ | ex′ | ev′ = s-lim (λ n → sp-Ωψ {q = q} {σ = σ} _ (i-resp e (chain-≅ e n)))
sp-Ωψ {q = q} {σ = σ} (up zero x) e     = sp-Ωψ {q = q} {σ = λ r → σ (suc r)} x (Uni.u-refl Dom₀ zero e)
sp-Ωψ {q = q} {σ = σ} (up (self n) x) e = sp-Ωψ {q = q} {σ = λ r → σ (lim n r)} x (Uni.u-refl Dom₀ (self n) e)
```

## §6 读法

`Cu A P`: 位置 $P$ 相对 $A$ 的回答. **规格不空:** `Ab A k` 对后继 $B+1$ 说 $A\trianglelefteq B$ ($B$ 不在 $A$ 的严格下方), 对闭包说 $A\trianglelefteq k$; 对 0 与极限是空类型. `LZ k`: $k$ 是 0 或极限. 所以后继与闭包节点只有两个回答.

```agda
Ab : LG → LG → Set
Ab A zero        = ⊥
Ab A (suc B)     = A ⊴ B
Ab A (lim f)     = ⊥
Ab A (lc c t g)  = A ⊴ lc c t g

LZ : LG → Set
LZ zero       = ⊤
LZ (suc _)    = ⊥
LZ (lim _)    = ⊤
LZ (lc _ _ _) = ⊥

data Cu (A : LG) {k y : LG} (P : Cp k y) : Set where
  cIn : ∀ {rep} → Lk k rep → (Q : Cp rep A) → (∀ E → AdmC E P → AdmC E Q) → Cu A P
  cNw : Ab A k → Cu A P
  cUn : LZ k → Cu A P

cuT : ∀ {A k y y′} {P : Cp k y} {P′ : Cp k y′} → (∀ E → AdmC E P → AdmC E P′) → Cu A P′ → Cu A P
cuT t (cIn d Q u) = cIn d Q (λ E a → u E (t E a))
cuT t (cNw x) = cNw x
cuT t (cUn x) = cUn x

-- 位置沿 ⊴ 搬: 后继与闭包节点搬得动, 0 与极限节点搬不动 (不答)
cuMv : ∀ {A y y′ k} → y ⊴ y′ → (P : Cp k y) → (∀ {k′} (P′ : Cp k′ y′) → Cu A P′) → Cu A P
cuMv {k = zero} x P K = cUn tt
cuMv {k = lim f} x P K = cUn tt
cuMv {k = suc k′} x P K with ⊴p x (fromCpS P)
... | viaᴸ d p t with K (toCpS p)
...   | cIn d′ Q u = cIn (lkT (s≈ d) d′) Q (λ E a → u E (admToS p (t E (admFromS P a))))
...   | cNw ev = cNw (⊴-trans ev (≈→⊴ (≈-sym d)))
...   | cUn ()
cuMv {k = lc c t g} x P K with ⊴K x P
... | viaᴷ d p u with K p
...   | cIn d′ Q v = cIn (lkT d d′) Q (λ E a → v E (u E a))
...   | cNw ev = cNw (⊴-trans ev (≈→⊴ (≈-sym d)))
...   | cUn ()

-- 位置沿 ≈ 搬: 什么节点都搬得动
cuLk : ∀ {A y y′ k rep} {P : Cp k y} {P′ : Cp rep y′} → Lk k rep → (∀ E → AdmC E P → AdmC E P′) → Cu A P′ → Cu A P
cuLk (inj₂ refl) t r = cuT t r
cuLk d t (cIn d′ Q u) = cIn (lkC d d′) Q (λ E a → u E (t E a))
cuLk (inj₁ (s≈ e)) t (cNw ev) = cNw (⊴-trans ev (≈→⊴ (≈-sym e)))
cuLk (inj₁ (o≈ c e h)) t (cNw ev) = cNw (⊴-trans ev (≈→⊴ (≈-sym (o≈ c e h))))
cuLk (inj₁ z≈) t (cUn x) = cUn tt
cuLk (inj₁ (l≈ h)) t (cUn x) = cUn tt

read : ∀ {k₁ ℓ} (ba : BL k₁) (by : BL ℓ) {a : Ordᶜ k₁} {y : Ordᶜ ℓ} → Sp a y → ∀ {k} (P : Cp k (rbB by y)) → Cu (rbB ba a) P
read ba b0 (s-zero _) self = cUn tt
read ba b1 (s-zero _) self = cUn tt
read ba by (s-eq e) P with mvC P (rbB-≈ by ba (≅-sym e))
... | mvc d Q t = cIn d Q t
read ba by (s-cg d S) P with mvC P (rbB-≈ by by d)
... | mvc e Q t = cuLk e t (read ba by S Q)
read ba by (s-mv m S) P = cuMv (m (idO {b = by} {b′ = by})) P (read ba by S)
read ba b0 (s-suc ev eb S) self = cNw (ev (idO {b = ba} {b′ = b0}))
read ba b0 (s-suc ev eb S) (suc P) = cuT (λ _ a → a) (read ba b0 S P)
read ba b1 (s-suc ev eb S) self = cNw (ev (idO {b = ba} {b′ = b1}))
read ba b1 (s-suc ev eb S) (suc P) = cuT (λ _ a → a) (read ba b1 S P)
read ba b0 (s-lim K) self = cUn tt
read ba b0 (s-lim K) (lim n P) = cuT (λ _ a → a) (read ba b0 (K n) P)
read ba b1 (s-lim K) self = cUn tt
read ba b1 (s-lim K) (lim n P) = cuT (λ _ a → a) (read ba b1 (K n) P)
read ba b0 (s-lc {q = ()} ev ex K) P
read ba b1 (s-lc {q = suc ()} ev ex K) P
read ba b1 (s-lc {q = zero} ev ex K) self = cNw (ev (idO {b = ba} {b′ = b1}))
read ba b1 (s-lc {q = zero} ev ex K) (fst P) = cuT (λ _ a → a) (read ba b1 (K (suc zero) (s≅ z≅)) P)
read ba b1 (s-lc {q = zero} ev ex K) (bra η e P) = cuT (λ _ a → proj₂ a) (read ba b1 (K (em η) (em-self η)) P)
read ba b0 (s-up {r = ()} S) P
read ba b1 (s-up {r = zero} S) P = read ba b0 S P
```
