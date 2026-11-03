# 读回的闭包定理: 目标 1 的输出是好层号 (`good-feed` 的头一步)

> 不含记号. 结论写在 [LvGuard](LvGuard.lagda.md). 由 [Uniform](Uniform.lagda.md) §0–§7 用脚本生成, 差别只有四处:
>
> 1. 观测的底 `idO` 在第 0, 1 层 (`BL`), 底部的比较是**层号**上的 `L._⊴_` (`LvGuardBase`), 不是第 0 层树上的 $\sqsubseteq$. 这是 [InaccThetaObs](InaccThetaObs.lagda.md) 的 (1), (2) 的形状, 但没有世界, 没有判决 `S`.
> 2. 新观测 `ψ¹o` 与目标 1 的折叠 `ψ¹`: 与 `ψ⁰` 同形, 节点的层是字面 0 就穿透, 否则是链. 不用 `<ᴵ-dec`.
> 3. 读回 `rb₀`, `rb₁`: 第 0, 1 层的树到层号. **$\Omega$ 不再是原子**: `rb₁ (limᵢ zero f)` 是真的闭包 `lc`, 所以 `base⊑zero` 的问题不存在.
> 4. `limᵢ-r` 的底部走第一支 `L.⊴-fst`: 这是 `lc` 带 `t` 的用处.
>
> **这说明 [Uniform](Uniform.lagda.md) 的闭包定理对底部的序是参数化的:** 只用到 `L.≈→⊴`, `L.⊴-trans`, `L.⊴-lim-r`, `L.⊴-lim-l`, `L.⊴-suc-r`, `L.⊴-fst`, `L.⊴-zero`, 而这几条都不提分支值. 所以 `⊴` 的搬运**从不改变分支值**, 这句是由证明的形状读出的判断, 不是一条定理.
>
> 模块参数 `𝔻 : Dom` 是定义域, 不是假设: 实例见 `Dom₀` 与 [LvGuardNext](LvGuardNext.lagda.md).

```agda
{-# OPTIONS --safe --without-K #-}
open import OCF.Align.LvGuardBase using (Dom; module Lv)

module OCF.Align.LvGuardUni (𝔻 : Dom) where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level hiding (F)
open Restr
import OCF.Align.LvGuardBase
private module L = Lv 𝔻
open Dom 𝔻 using (b₁; rd; rd-one; rd-s; rd-≅)
```

## §0 目标 1 的折叠与读回

`ψ¹`: 与 `ψ⁰` 同形. `em`: `Ordᴵ` 到第 0 层的树. `rb₀`, `rb₁`: 读回. 第 1 层的节点读成带守卫的闭包, 下界是 `b₁` (下标 1), 第一支是 $f(1)$. 分支 $\eta$ 只经 `rd` 看见 `Ordᴵ`.

```agda
ψ¹ : ∀ {k} → Ordᶜ k → Ordᶜ (suc zero)
ψ¹ zero    = Ω (suc zero)
ψ¹ (suc a) = lim (iter (ψ¹ a +_) zero)
ψ¹ (lim f) = lim (λ n → ψ¹ (f n))
ψ¹ (limᵢ {i = zero} q f)    = limᵢ zero (λ y → ψ¹ (f (into (<→◃ q) y)))
ψ¹ (limᵢ {i = suc a} q f)   = lim (λ n → ψ¹ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω (suc a)) n))))
ψ¹ (limᵢ {i = lim g s} q f) = lim (λ n → ψ¹ (f (into (<→◃ q) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω (lim g s)) n))))
ψ¹ (up zero x)     = ψ¹ x
ψ¹ (up (self n) x) = ψ¹ x

ψ¹-≅ : ∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ≅ b → ψ¹ a ≅ ψ¹ b
ψ¹-≅ z≅     = Ω-refl (suc zero)
ψ¹-≅ (s≅ e) = l≅ (iter-R _≅_ (λ e′ → add-≅ (ψ¹-≅ e) e′) z≅)
ψ¹-≅ (l≅ h) = l≅ (λ n → ψ¹-≅ (h n))
ψ¹-≅ (upˡ {r = zero} e)   = ψ¹-≅ e
ψ¹-≅ (upˡ {r = self n} e) = ψ¹-≅ e
ψ¹-≅ (upʳ {r = zero} e)   = ψ¹-≅ e
ψ¹-≅ (upʳ {r = self n} e) = ψ¹-≅ e
ψ¹-≅ (lᵢ≅ {p = q} {q = q′} z≅ h) = lᵢ≅ z≅ (λ x y d → ψ¹-≅ (h x y (≅→R (<→◃ q) d)))
ψ¹-≅ (lᵢ≅ {p = q} (s≅ e) h) = l≅ (λ n → ψ¹-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ (s≅ e) (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ (s≅ e))
ψ¹-≅ (lᵢ≅ {p = q} (l≅ k) h) = l≅ (λ n → ψ¹-≅ (h _ _ (≅→R (<→◃ q) (chain n))))
  where chain = iter-R _≅_ (λ d → ψ-≅ (l≅ k) (h _ _ (≅→R (<→◃ q) d))) (Ω-≅ (l≅ k))

em : Ordᴵ → Ordᶜ zero
em zero      = zero
em (suc a)   = suc (em a)
em (lim f s) = lim (λ n → em (f n))

em-≅ : ∀ {a b} → a ≅ᴵ b → em a ≅ em b
em-≅ z≅     = z≅
em-≅ (s≅ e) = s≅ (em-≅ e)
em-≅ (l≅ h) = l≅ (λ n → em-≅ (h n))

rb₀ : Ordᶜ zero → L.LG
rb₀ zero        = L.zero
rb₀ (suc a)     = L.suc (rb₀ a)
rb₀ (lim f)     = L.lim (λ n → rb₀ (f n))
rb₀ (limᵢ () f)
rb₀ (up () x)

rb₁ : Ordᶜ (suc zero) → L.LG
rb₁ zero           = L.zero
rb₁ (suc a)        = L.suc (rb₁ a)
rb₁ (lim f)        = L.lim (λ n → rb₁ (f n))
rb₁ (limᵢ zero f)  = L.lc b₁ (rb₁ (f (suc zero))) (λ η e → rb₁ (f (em (rd e))))
rb₁ (limᵢ (suc ()) f)
rb₁ (up zero x)    = rb₀ x

rb-≈₀₀ : ∀ {a b : Ordᶜ zero} → a ≅ b → rb₀ a L.≈ rb₀ b
rb-≈₀₀ z≅     = L.z≈
rb-≈₀₀ (s≅ e) = L.s≈ (rb-≈₀₀ e)
rb-≈₀₀ (l≅ h) = L.l≈ (λ n → rb-≈₀₀ (h n))
rb-≈₀₀ (lᵢ≅ {p = ()} e h)
rb-≈₀₀ (upˡ {r = ()} e)
rb-≈₀₀ (upʳ {r = ()} e)

rb-≈₀₁ : ∀ {a : Ordᶜ zero} {b : Ordᶜ (suc zero)} → a ≅ b → rb₀ a L.≈ rb₁ b
rb-≈₀₁ z≅     = L.z≈
rb-≈₀₁ (s≅ e) = L.s≈ (rb-≈₀₁ e)
rb-≈₀₁ (l≅ h) = L.l≈ (λ n → rb-≈₀₁ (h n))
rb-≈₀₁ (lᵢ≅ {p = ()} e h)
rb-≈₀₁ (upˡ {r = ()} e)
rb-≈₀₁ (upʳ {r = zero} e) = rb-≈₀₀ e

rb-≈₁₁ : ∀ {a b : Ordᶜ (suc zero)} → a ≅ b → rb₁ a L.≈ rb₁ b
rb-≈₁₁ z≅     = L.z≈
rb-≈₁₁ (s≅ e) = L.s≈ (rb-≈₁₁ e)
rb-≈₁₁ (l≅ h) = L.l≈ (λ n → rb-≈₁₁ (h n))
rb-≈₁₁ (lᵢ≅ {p = zero} {q = zero} {f = f} {g = g} z≅ h) =
  L.o≈ (Dom.≅ᴰ-refl 𝔻 b₁) (rb-≈₁₁ (h (suc zero) (suc zero) (s≅ z≅)))
       (λ η e η′ e′ k → rb-≈₁₁ (h (em (rd e)) (em (rd e′)) (em-≅ (rd-≅ e e′ k))))
rb-≈₁₁ (lᵢ≅ {p = zero} {q = suc ()} e h)
rb-≈₁₁ (lᵢ≅ {p = suc ()} e h)
rb-≈₁₁ (upˡ {r = zero} e) = rb-≈₀₁ e
rb-≈₁₁ (upʳ {r = zero} e) = rb-≈sym (rb-≈₀₁ (≅-sym e))
  where
  rb-≈sym : ∀ {a b} → a L.≈ b → b L.≈ a
  rb-≈sym = L.≈-sym

data BL : Ordᴵ → Set where
  b0 : BL zero
  b1 : BL (suc zero)

rbB : ∀ {k} → BL k → Ordᶜ k → L.LG
rbB b0 x = rb₀ x
rbB b1 x = rb₁ x

rbB-≈ : ∀ {k k′} (b : BL k) (b′ : BL k′) {x : Ordᶜ k} {y : Ordᶜ k′} → x ≅ y → rbB b x L.≈ rbB b′ y
rbB-≈ b0 b0 e = rb-≈₀₀ e
rbB-≈ b0 b1 e = rb-≈₀₁ e
rbB-≈ b1 b0 e = L.≈-sym (rb-≈₀₁ (≅-sym e))
rbB-≈ b1 b1 e = rb-≈₁₁ e
```

## §1 观测与上界引理 (由 [Uniform](Uniform.lagda.md) 生成)

```agda
≅-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≅ a
≅-reflˡ e = ≅-trans e (≅-sym e)

≅-reflʳ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → b ≅ b
≅-reflʳ e = ≅-trans (≅-sym e) e

self-tr : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → x ≅ x → tr e x ≅ tr e x
self-tr e d = ≅-reflˡ (tr-≅ e d)

self-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → x ≅ x → tr⁻ e x ≅ tr⁻ e x
self-tr⁻ e d = ≅-reflˡ (tr⁻-≅ e d)

s-inv : ∀ {k k′} {a : Ordᶜ k} {b : Ordᶜ k′} → suc a ≅ suc b → a ≅ b
s-inv (s≅ e) = e

l-inv : ∀ {k k′} {f : ℕ → Ordᶜ k} {g : ℕ → Ordᶜ k′} → lim f ≅ lim g → ∀ n → f n ≅ g n
l-inv (l≅ h) = h

i-resp : ∀ {k k′ j} {p : j <ᴵ k} {f : U j (<→◃ p) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ p f ≅ b →
         ∀ {z z′ : Ordᶜ j} → z ≅ z′ → f (into (<→◃ p) z) ≅ f (into (<→◃ p) z′)
i-resp {p = p} (lᵢ≅ e h) {z} {z′} d =
  ≅-trans (h z (tr e z′) (≅→R (<→◃ p) (≅-tr e d)))
          (≅-sym (h z′ (tr e z′) (≅→R (<→◃ p) (≅-tr e (≅-reflʳ d)))))
i-resp (upʳ {r = zero} e)   = i-resp e
i-resp (upʳ {r = self n} e) = i-resp e

u-inv : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → up r x ≅ b → out (◃₁→◃ r) x ≅ b
u-inv zero     (upˡ e)              = e
u-inv zero     (upʳ {r = zero} e)   = upʳ (u-inv zero e)
u-inv zero     (upʳ {r = self n} e) = upʳ (u-inv zero e)
u-inv (self m) (upˡ e)              = e
u-inv (self m) (upʳ {r = zero} e)   = upʳ (u-inv (self m) e)
u-inv (self m) (upʳ {r = self n} e) = upʳ (u-inv (self m) e)

u-refl : ∀ {k ℓ} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} → up r x ≅ up r x → out (◃₁→◃ r) x ≅ out (◃₁→◃ r) x
u-refl r e = ≅-reflˡ (u-inv r e)

data Obs : Ordᴵ → Set where
  idO  : ∀ {k} → BL k → Obs k
  ψ⁰o  : ∀ {k} → Obs zero → Obs k
  ψ¹o  : ∀ {k} → Obs (suc zero) → Obs k
  ψo   : ∀ {i k ℓ} → Obs i → i <ᴵ ℓ → Simᴵ k ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordᶜ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

run : ∀ {k} → Obs k → Ordᶜ k → L.LG
run (idO b)      x = rbB b x
run (ψ⁰o O)      x = run O (ψ⁰ x)
run (ψ¹o O)      x = run O (ψ¹ x)
run (ψo O p σ)   x = run O (ψ p σ x)
run (addo O a σ) x = run O (add a σ x)
run (tro O e)    x = run O (tr e x)
run (tr⁻o O e)   x = run O (tr⁻ e x)

infix 4 _≈ᵒ_ _⊑ᵒ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
  idO  : ∀ {k k′} {b : BL k} {b′ : BL k′} → idO b ≈ᵒ idO b′
  ψ⁰o  : ∀ {k k′} {O O′ : Obs zero} → O ≈ᵒ O′ → ψ⁰o {k} O ≈ᵒ ψ⁰o {k′} O′
  ψ¹o  : ∀ {k k′} {O O′ : Obs (suc zero)} → O ≈ᵒ O′ → ψ¹o {k} O ≈ᵒ ψ¹o {k′} O′
  ψo   : ∀ {i k k′ ℓ ℓ′} {O O′ : Obs i} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → ψo O p σ ≈ᵒ ψo O′ p′ σ′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → a ≅ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᵒ-reflˡ idO        = idO
≈ᵒ-reflˡ (ψ⁰o o)    = ψ⁰o (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (ψ¹o o)    = ψ¹o (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (ψo o)     = ψo (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (addo o e) = addo (≈ᵒ-reflˡ o) (≅-reflˡ e)
≈ᵒ-reflˡ (tro o)    = tro (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (tr⁻o o)   = tr⁻o (≈ᵒ-reflˡ o)

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᵒ-reflʳ idO        = idO
≈ᵒ-reflʳ (ψ⁰o o)    = ψ⁰o (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (ψ¹o o)    = ψ¹o (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (ψo o)     = ψo (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (addo o e) = addo (≈ᵒ-reflʳ o) (≅-reflʳ e)
≈ᵒ-reflʳ (tro o)    = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)   = tr⁻o (≈ᵒ-reflʳ o)

run-≅ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordᶜ k} {x′ : Ordᶜ k′} → O ≈ᵒ O′ → x ≅ x′ → run O x L.≈ run O′ x′
run-≅ (idO {b = b} {b′ = b′}) d = rbB-≈ b b′ d
run-≅ (ψ⁰o o)    d = run-≅ o (ψ⁰-≅ d)
run-≅ (ψ¹o o)    d = run-≅ o (ψ¹-≅ d)
run-≅ (ψo o)     d = run-≅ o (ψ-≅ (≅ᴵ-refl _) d)
run-≅ (addo o a) d = run-≅ o (add-≅ a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (tr-≅ e (≅-tr e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻-≅ e (≅-tr⁻ e′ d))

_⊑ᵒ_ : ∀ {k k′} → Ordᶜ k → Ordᶜ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → run O x L.⊴ run O′ y

≅→⊑ᵒ : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ≅ y → x ⊑ᵒ y
≅→⊑ᵒ e o = L.≈→⊴ (run-≅ o e)

⊑ᵒ-≅ʳ : ∀ {k k′} {x : Ordᶜ k} {y y′ : Ordᶜ k′} → x ⊑ᵒ y → y ≅ y′ → x ⊑ᵒ y′
⊑ᵒ-≅ʳ h e o = L.⊴-trans (h o) (L.≈→⊴ (run-≅ (≈ᵒ-reflʳ o) e))

ψ-cong : ∀ {i k k′ ℓ ℓ′} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
         x ⊑ᵒ y → ψ p σ x ⊑ᵒ ψ p′ σ′ y
ψ-cong h o = h (ψo o)

ψ⁰-cong : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → ψ⁰ x ⊑ᵒ ψ⁰ y
ψ⁰-cong h o = h (ψ⁰o o)

ψ¹-cong : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → ψ¹ x ⊑ᵒ ψ¹ y
ψ¹-cong h o = h (ψ¹o o)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
           a ≅ a′ → x ⊑ᵒ y → add a σ x ⊑ᵒ add a′ σ′ y
add-cong e h o = h (addo o e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordᶜ a} {y : Ordᶜ a′} → x ⊑ᵒ y → tr e x ⊑ᵒ tr e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordᶜ b} {y : Ordᶜ b′} → x ⊑ᵒ y → tr⁻ e x ⊑ᵒ tr⁻ e′ y
tr⁻-cong h o = h (tr⁻o o)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {y : Ordᶜ ℓ′} → out (◃₁→◃ r) x ⊑ᵒ y → up r x ⊑ᵒ y
up-l {r = zero}   h (idO {b = b1} {b′ = b′}) = h (idO {b = b0} {b′ = b′})
up-l {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = zero}   h (ψ¹o o)    = h (ψ¹o o)
up-l {r = zero}   h (ψo o)     = h (ψo o)
up-l {r = zero}   h (addo o e) = h (addo o e)
up-l {r = zero}   h (tro {e = s≅ e} o)  = up-l {r = zero} (λ o′ → h (tro o′)) o
up-l {r = zero}   h (tr⁻o {e = s≅ e} o) = up-l {r = zero} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (idO {b = ()})
up-l {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = self n} h (ψ¹o o)    = h (ψ¹o o)
up-l {r = self n} h (ψo o)     = h (ψo o)
up-l {r = self n} h (addo o e) = h (addo o e)
up-l {r = self n} h (tro {e = l≅ f} o)  = up-l {r = self n} (λ o′ → h (tro o′)) o
up-l {r = self n} h (tr⁻o {e = l≅ f} o) = up-l {r = self n} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : U k (◃₁→◃ r)} {x : Ordᶜ ℓ′} → x ⊑ᵒ out (◃₁→◃ r) y → x ⊑ᵒ up r y
up-r {r = zero}   h (idO {b = b} {b′ = b1}) = h (idO {b = b} {b′ = b0})
up-r {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = zero}   h (ψ¹o o)    = h (ψ¹o o)
up-r {r = zero}   h (ψo o)     = h (ψo o)
up-r {r = zero}   h (addo o e) = h (addo o e)
up-r {r = zero}   h (tro {e′ = s≅ e} o)  = up-r {r = zero} (λ o′ → h (tro o′)) o
up-r {r = zero}   h (tr⁻o {e′ = s≅ e} o) = up-r {r = zero} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (idO {b′ = ()})
up-r {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = self n} h (ψ¹o o)    = h (ψ¹o o)
up-r {r = self n} h (ψo o)     = h (ψo o)
up-r {r = self n} h (addo o e) = h (addo o e)
up-r {r = self n} h (tro {e′ = l≅ f} o)  = up-r {r = self n} (λ o′ → h (tro o′)) o
up-r {r = self n} h (tr⁻o {e′ = l≅ f} o) = up-r {r = self n} (λ o′ → h (tr⁻o o′)) o

lim-r : ∀ {k k′} {x : Ordᶜ k} {h : ℕ → Ordᶜ k′} n → x ⊑ᵒ h n → x ⊑ᵒ lim h
lim-r n p (idO {b = b} {b′ = b0}) = L.⊴-lim-r n (p (idO {b = b} {b′ = b0}))
lim-r n p (idO {b = b} {b′ = b1}) = L.⊴-lim-r n (p (idO {b = b} {b′ = b1}))
lim-r n p (ψ⁰o o)    = lim-r n (ψ⁰-cong p) o
lim-r n p (ψ¹o o)    = lim-r n (ψ¹-cong p) o
lim-r n p (ψo o)     = lim-r n (ψ-cong p) o
lim-r n p (addo o a) = lim-r n (add-cong a p) o
lim-r n p (tro o)    = lim-r n (tr-cong p) o
lim-r n p (tr⁻o o)   = lim-r n (tr⁻-cong p) o

lim-l : ∀ {k k′} {h : ℕ → Ordᶜ k} {y : Ordᶜ k′} → (∀ n → h n ⊑ᵒ y) → lim h ⊑ᵒ y
lim-l K (idO {b = b0} {b′ = b′}) = L.⊴-lim-l (λ n → K n (idO {b = b0} {b′ = b′}))
lim-l K (idO {b = b1} {b′ = b′}) = L.⊴-lim-l (λ n → K n (idO {b = b1} {b′ = b′}))
lim-l K (ψ⁰o o)    = lim-l (λ n o′ → K n (ψ⁰o o′)) o
lim-l K (ψ¹o o)    = lim-l (λ n o′ → K n (ψ¹o o′)) o
lim-l K (ψo o)     = lim-l (λ n o′ → K n (ψo o′)) o
lim-l K (addo o a) = lim-l (λ n o′ → K n (addo o′ a)) o
lim-l K (tro o)    = lim-l (λ n o′ → K n (tro o′)) o
lim-l K (tr⁻o o)   = lim-l (λ n o′ → K n (tr⁻o o′)) o

suc-r : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → x ⊑ᵒ suc y
suc-r p (idO {b = b} {b′ = b0}) = L.⊴-suc-r (p (idO {b = b} {b′ = b0}))
suc-r p (idO {b = b} {b′ = b1}) = L.⊴-suc-r (p (idO {b = b} {b′ = b1}))
suc-r p (ψ⁰o o)    = lim-r 1 (ψ⁰-cong p) o
suc-r p (ψ¹o o)    = lim-r 1 (ψ¹-cong p) o
suc-r p (ψo o)     = lim-r 1 (ψ-cong p) o
suc-r p (addo o a) = suc-r (add-cong a p) o
suc-r p (tro o)    = suc-r (tr-cong p) o
suc-r p (tr⁻o o)   = suc-r (tr⁻-cong p) o

limᵢ-r : ∀ {k k′ j} {x : Ordᶜ k} {q : j <ᴵ k′} {g : U j (<→◃ q) → Ordᶜ k′} →
         (∀ z → z ≅ Ω j → x ⊑ᵒ g (into (<→◃ q) z)) → x ⊑ᵒ limᵢ q g
limᵢ-r {q = ()} H (idO {b′ = b0})
limᵢ-r {q = zero} H (idO {b = b} {b′ = b1}) = L.⊴-fst (H (suc zero) (s≅ z≅) (idO {b = b} {b′ = b1}))
limᵢ-r {q = suc ()} H (idO {b′ = b1})
limᵢ-r {j = j} H (ψ⁰o o) = lim-r 0 (ψ⁰-cong (H (Ω j) (Ω-refl j))) o
limᵢ-r {j = zero} H (ψ¹o o) = limᵢ-r (λ z d → ψ¹-cong (H z d)) o
limᵢ-r {j = suc j} H (ψ¹o o) = lim-r 0 (ψ¹-cong (H (Ω (suc j)) (Ω-refl (suc j)))) o
limᵢ-r {j = lim g s} H (ψ¹o o) = lim-r 0 (ψ¹-cong (H (Ω (lim g s)) (Ω-refl (lim g s)))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (ψo {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} o) with <ᴵ-dec (σ′ q) p′
... | injᵃ (via e r) = limᵢ-r (λ z d →
        subst (λ u → ψ p σ x ⊑ᵒ ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e u)))) (sym (out-into (<→◃ r) z))
              (ψ-cong (H (tr⁻ e z) (tr⁻-≅ e (≅-trans d (Ω-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (ψ-cong (H (Ω j) (Ω-refl j))) o
... | injᶜ _ = lim-r 0 (ψ-cong (H (Ω j) (Ω-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o ea) = limᵢ-r (λ z d →
  subst (λ u → add a σ x ⊑ᵒ add a′ σ′ (g (into (<→◃ q) u))) (sym (out-into (<→◃ (σ′ q)) z))
        (add-cong ea (H z d))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr e x ⊑ᵒ tr e′ (g (into (<→◃ q) (back (res q e′) u)))) (sym (out-into (<→◃ (lt (res q e′))) z))
        (tr-cong (H (back (res q e′) z) (≅-trans (back-≅ q e′ d) (Ω-≅ (≅ᴵ-sym (eq (res q e′)))))))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr⁻ e x ⊑ᵒ tr⁻ e′ (g (into (<→◃ q) (back (res⁻ q e′) u)))) (sym (out-into (<→◃ (lt (res⁻ q e′))) z))
        (tr⁻-cong (H (back (res⁻ q e′) z) (≅-trans (back⁻-≅ q e′ d) (Ω-≅ (≅ᴵ-sym (eq (res⁻ q e′)))))))) o

B1 : ∀ {j ℓ k} {q : j <ᴵ ℓ} {σ : Simᴵ k ℓ} (z : Ordᶜ k) → z ≅ z → Ω j ⊑ᵒ ψ q σ z
B1 zero e = ≅→⊑ᵒ (Ω-refl _)
B1 {q = q} {σ = σ} (suc a) e = lim-r 1 (B1 {q = q} {σ = σ} a (s-inv e))
B1 {q = q} {σ = σ} (lim h) e = lim-r 0 (B1 {q = q} {σ = σ} (h 0) (l-inv e 0))
B1 {j = j} {q = q} {σ = σ} (limᵢ {i = j′} q′ g) e with <ᴵ-dec (σ q′) q
... | injᵃ (via e₁ r) = limᵢ-r (λ z d →
        subst (λ u → Ω j ⊑ᵒ ψ q σ (g (into (<→◃ q′) (tr⁻ e₁ u)))) (sym (out-into (<→◃ r) z))
              (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (tr⁻ e₁ z))) (i-resp e (self-tr⁻ e₁ (≅-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
... | injᶜ _ = lim-r 0 (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
B1 (up zero x) e     = B1 x (u-refl zero e)
B1 (up (self n) x) e = B1 x (u-refl (self n) e)

B1⁰ : ∀ {k} (z : Ordᶜ k) → z ≅ z → Ω zero ⊑ᵒ ψ⁰ z
B1⁰ zero e    = ≅→⊑ᵒ (Ω-refl zero)
B1⁰ (suc a) e = lim-r 1 (B1⁰ a (s-inv e))
B1⁰ (lim h) e = lim-r 0 (B1⁰ (h 0) (l-inv e 0))
B1⁰ (limᵢ {i = j′} q′ g) e = lim-r 0 (B1⁰ (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
B1⁰ (up zero x) e     = B1⁰ x (u-refl zero e)
B1⁰ (up (self n) x) e = B1⁰ x (u-refl (self n) e)

B1¹ : ∀ {k} (z : Ordᶜ k) → z ≅ z → Ω (suc zero) ⊑ᵒ ψ¹ z
B1¹ zero e    = ≅→⊑ᵒ (Ω-refl (suc zero))
B1¹ (suc a) e = lim-r 1 (B1¹ a (s-inv e))
B1¹ (lim h) e = lim-r 0 (B1¹ (h 0) (l-inv e 0))
B1¹ (limᵢ {i = zero} q′ g) e = limᵢ-r (λ z d → B1¹ (g (into (<→◃ q′) z)) (i-resp e (≅-reflˡ d)))
B1¹ (limᵢ {i = suc j} q′ g) e = lim-r 0 (B1¹ (g (into (<→◃ q′) (Ω (suc j)))) (i-resp e (Ω-refl (suc j))))
B1¹ (limᵢ {i = lim h s} q′ g) e = lim-r 0 (B1¹ (g (into (<→◃ q′) (Ω (lim h s)))) (i-resp e (Ω-refl (lim h s))))
B1¹ (up zero x) e     = B1¹ x (u-refl zero e)
B1¹ (up (self n) x) e = B1¹ x (u-refl (self n) e)

add-r : ∀ {k ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordᶜ k) → a ≅ a′ → b ≅ b → a ⊑ᵒ add a′ σ b
add-r zero ea eb = ≅→⊑ᵒ ea
add-r {σ = σ} (suc b) ea eb = suc-r (add-r {σ = σ} b ea (s-inv eb))
add-r {σ = σ} (lim h) ea eb = lim-r 0 (add-r {σ = σ} (h 0) ea (l-inv eb 0))
add-r {a = a} {a′ = a′} {σ = σ} (limᵢ q g) ea eb = limᵢ-r (λ z d →
  subst (λ u → a ⊑ᵒ add a′ σ (g (into (<→◃ q) u))) (sym (out-into (<→◃ (σ q)) z))
        (add-r {σ = σ} (g (into (<→◃ q) z)) ea (i-resp eb (≅-reflˡ d))))
add-r (up zero x)     ea eb = add-r x ea (u-refl zero eb)
add-r (up (self n) x) ea eb = add-r x ea (u-refl (self n) eb)

zero-l : ∀ {k k′} {y : Ordᶜ k′} → y ≅ y → 𝟎 {k} ⊑ᵒ y
zero-l ey (idO {b = b0}) = L.⊴-zero
zero-l ey (idO {b = b1}) = L.⊴-zero
zero-l ey (ψ⁰o o)     = B1⁰ _ ey o
zero-l ey (ψ¹o o)     = B1¹ _ ey o
zero-l ey (ψo o)      = B1 _ ey o
zero-l ey (addo o ea) = add-r _ ea ey o
zero-l ey (tro {e′ = e′} o)  = zero-l (self-tr e′ ey) o
zero-l ey (tr⁻o {e′ = e′} o) = zero-l (self-tr⁻ e′ ey) o

Ω0 : ∀ b → Ω zero ⊑ᵒ Ω b
Ω0 zero      = ≅→⊑ᵒ (Ω-refl zero)
Ω0 (suc b)   = limᵢ-r (λ z d → up-r (⊑ᵒ-≅ʳ (Ω0 b) (≅-sym d)))
Ω0 (lim g s) = lim-r 0 (up-r (Ω0 (g 0)))

Ω< : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ω (suc a) ⊑ᵒ Ω b
Ω< e zero      = ≅→⊑ᵒ (Ω-≅ (s≅ e))
Ω< e (suc q)   = limᵢ-r (λ z d → up-r (⊑ᵒ-≅ʳ (Ω< e q) (≅-sym d)))
Ω< e (lim n q) = lim-r n (up-r (Ω< e q))

Ω-monoᵒ : ∀ {a b} → a ⊑ᴵ b → Ω a ⊑ᵒ Ω b
Ω-monoᵒ {b = b} z⊑ = Ω0 b
Ω-monoᵒ (s⊑ e q)   = Ω< e q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l (Ω-monoᵒ (k n)))

module _ (ℓ : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set) where
  data Good₊ : Ordᶜ ℓ → Set where
    gz : Good₊ zero
    gs : ∀ {a} → Good₊ a → Good₊ (suc a)
    gl : ∀ {h : ℕ → Ordᶜ ℓ} → (∀ n → Good₊ (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ (lim h)
    gi : ∀ {j} {p : j <ᴵ ℓ} {f : U j (<→◃ p) → Ordᶜ ℓ} →
         (∀ (z : Ordᶜ j) → z ≅ z → G< j (<→◃ p) (into (<→◃ p) z) → Good₊ (f (into (<→◃ p) z))) →
         (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ p) z) ⊑ᵒ f (into (<→◃ p) z′)) →
         Good₊ (limᵢ p f)
    gu : ∀ {k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Good₊ (up r x)

Gd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set
Gd i zero         x = Good₊ i Gd x
Gd i (suc r)      x = Gd i r x
Gd _ (self {f} n) x = Good₊ (f n) Gd x
Gd i (lim n r)    x = Gd i r x

Good : ∀ {ℓ} → Ordᶜ ℓ → Set
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Gd i r (into r x) → Good x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Good x → Gd i r (into r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g

Gd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordᶜ i} → Gd i r (into r x) → Gd i r′ (into r′ x)
Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)

back-mono : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordᶜ (rep (res q e))} → u ⊑ᵒ u′ → back (res q e) u ⊑ᵒ back (res q e) u′
back-mono zero      (s≅ e) h = tr⁻-cong h
back-mono (suc q)   (s≅ e) h = back-mono q e h
back-mono (lim n q) (l≅ f) h = back-mono q (f n) h

back⁻-mono : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordᶜ (rep (res⁻ q e))} → u ⊑ᵒ u′ → back (res⁻ q e) u ⊑ᵒ back (res⁻ q e) u′
back⁻-mono zero      (s≅ e) h = tr-cong h
back⁻-mono (suc q)   (s≅ e) h = back⁻-mono q e h
back⁻-mono (lim n q) (l≅ f) h = back⁻-mono q (f n) h

self-back : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → u ≅ u → back (res q e) u ≅ back (res q e) u
self-back q e d = ≅-reflˡ (back-≅ q e d)

self-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → u ≅ u → back (res⁻ q e) u ≅ back (res⁻ q e) u
self-back⁻ q e d = ≅-reflˡ (back⁻-≅ q e d)

Good-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → Good x → Good (tr e x)
Good-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → Good x → Good (tr⁻ e x)
Good-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → Good u → Good (back (res q e) u)
Good-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → Good u → Good (back (res⁻ q e) u)

Good-tr e gz         = gz
Good-tr e (gs g)     = gs (Good-tr e g)
Good-tr e (gl hg st) = gl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
Good-tr e (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ w → Good (tr e (f (into (<→◃ q) (back (res q e) w))))) (sym (out-into (<→◃ (lt (res q e))) z))
                    (Good-tr e (hb (back (res q e) z) (self-back q e ez)
                                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (lt (res q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → tr e (f (into (<→◃ q) (back (res q e) w))) ⊑ᵒ tr e (f (into (<→◃ q) (back (res q e) w′))))
                         (sym (out-into (<→◃ (lt (res q e))) z)) (sym (out-into (<→◃ (lt (res q e))) z′))
                         (tr-cong (hm (back-mono q e h))))
Good-tr (s≅ e) (gu {r = zero} g)   = gu (Good-tr e g)
Good-tr (l≅ f) (gu {r = self n} g) = gu (Good-tr (f n) g)

Good-tr⁻ e gz         = gz
Good-tr⁻ e (gs g)     = gs (Good-tr⁻ e g)
Good-tr⁻ e (gl hg st) = gl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
Good-tr⁻ e (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ w → Good (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
                    (Good-tr⁻ e (hb (back (res⁻ q e) z) (self-back⁻ q e ez)
                                    (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (lt (res⁻ q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))) ⊑ᵒ tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w′))))
                         (sym (out-into (<→◃ (lt (res⁻ q e))) z)) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
                         (tr⁻-cong (hm (back⁻-mono q e h))))
Good-tr⁻ (s≅ e) (gu {r = zero} g)   = gu (Good-tr⁻ e g)
Good-tr⁻ (l≅ f) (gu {r = self n} g) = gu (Good-tr⁻ (f n) g)

Good-back zero      (s≅ e) g = Good-tr⁻ e g
Good-back (suc q)   (s≅ e) g = Good-back q e g
Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

Good-back⁻ zero      (s≅ e) g = Good-tr e g
Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g

Good-Ω : ∀ a → Good (Ω a)
Good-Ω zero      = gs gz
Good-Ω (suc c)   = gi (λ z ez g → gu g) (λ h → up-l (up-r h))
Good-Ω (lim g s) = gl (λ n → gu (Good-Ω (g n))) (λ n → up-l (up-r (Ω-monoᵒ (s n))))

Good-add : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {b : Ordᶜ k} → Good a → a ≅ a → Good b → Good (add a σ b)
Good-add ga ea gz          = ga
Good-add ga ea (gs g)      = gs (Good-add ga ea g)
Good-add ga ea (gl hg st)  = gl (λ n → Good-add ga ea (hg n)) (λ n → add-cong ea (st n))
Good-add {a = a} {σ = σ} ga ea (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ u → Good (add a σ (f (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
                    (Good-add ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (λ {z} {z′} h → subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ⊑ᵒ add a σ (f (into (<→◃ q) v)))
                         (sym (out-into (<→◃ (σ q)) z)) (sym (out-into (<→◃ (σ q)) z′)) (add-cong ea (hm h)))
Good-add ga ea (gu {r = zero} g)   = Good-add ga ea g
Good-add ga ea (gu {r = self n} g) = Good-add ga ea g

Good-iter : ∀ {ℓ} {c : Ordᶜ ℓ} → Good c → c ≅ c → ∀ n → Good (iter (c +_) zero n)
Good-iter gc ec zero    = gz
Good-iter gc ec (suc n) = Good-add gc ec (Good-iter gc ec n)

rule4ᵒ : ∀ {ℓ} {c : Ordᶜ ℓ} → c ≅ c → ∀ n → iter (c +_) zero n ⊑ᵒ iter (c +_) zero (suc n)
rule4ᵒ ec zero    = zero-l ec
rule4ᵒ ec (suc n) = add-cong ec (rule4ᵒ ec n)

chain : ∀ {j k} (q : j <ᴵ k) (f : U j (<→◃ q) → Ordᶜ k) → ℕ → Ordᶜ j
chain {j} q f = iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j)

chain-≅ : ∀ {j k k′} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b → ∀ n → chain q f n ≅ chain q f n
chain-≅ {j} e zero    = Ω-refl j
chain-≅ {j} {q = q} e (suc n) = ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl j) (i-resp e (chain-≅ e n))

chain-step : ∀ {j k k′} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b →
             (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ q) z) ⊑ᵒ f (into (<→◃ q) z′)) →
             ∀ n → chain q f n ⊑ᵒ chain q f (suc n)
chain-step {j} {q = q} {f = f} e hm zero = B1 {q = q} {σ = λ r → r} (f (into (<→◃ q) (Ω j))) (i-resp e (Ω-refl j))
chain-step e hm (suc n) = ψ-cong (hm (chain-step e hm n))

Good-ψ : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ p σ x)
chain-good : ∀ {j k} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} →
             (∀ (z : Ordᶜ j) → z ≅ z → Gd j (<→◃ q) (into (<→◃ q) z) → Good (f (into (<→◃ q) z))) →
             limᵢ q f ≅ limᵢ q f → ∀ n → Good (chain q f n)
chain-good {j} hb e zero = Good-Ω j
chain-good {q = q} {f = f} hb e (suc n) =
  Good-ψ (hb (chain q f n) (chain-≅ e n) (Good→Gd (<→◃ q) (chain-good hb e n))) (i-resp e (chain-≅ e n))

Good-ψ {i} gz ex = Good-Ω i
Good-ψ {i} {p = p} {σ = σ} (gs {a} g) ex = gl (Good-iter (Good-ψ g ea) eψ) (rule4ᵒ eψ)
  where ea = s-inv ex
        eψ = ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
Good-ψ (gl hg st) ex = gl (λ n → Good-ψ (hg n) (l-inv ex n)) (λ n → ψ-cong (st n))
Good-ψ {p = p} {σ = σ} (gi {j = j} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = gi
  (λ z ez g → subst (λ u → Good (ψ p σ (f (into (<→◃ q) (tr⁻ e u))))) (sym (out-into (<→◃ r) z))
                    (Good-ψ (hb (tr⁻ e z) (self-tr⁻ e ez) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                            (i-resp ex (self-tr⁻ e ez))))
  (λ {z} {z′} h → subst₂ (λ u v → ψ p σ (f (into (<→◃ q) (tr⁻ e u))) ⊑ᵒ ψ p σ (f (into (<→◃ q) (tr⁻ e v))))
                         (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r) z′)) (ψ-cong (hm (tr⁻-cong h))))
... | injᵇ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-resp ex (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
... | injᶜ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-resp ex (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
Good-ψ (gu {r = zero} g) ex   = Good-ψ g (u-refl zero ex)
Good-ψ (gu {r = self n} g) ex = Good-ψ g (u-refl (self n) ex)

Good-ψ⁰ : ∀ {k} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ⁰ x)
Good-ψ⁰ gz ex = gs gz
Good-ψ⁰ (gs {a} g) ex = gl (Good-iter (Good-ψ⁰ g ea) (ψ⁰-≅ ea)) (rule4ᵒ (ψ⁰-≅ ea))
  where ea = s-inv ex
Good-ψ⁰ (gl hg st) ex = gl (λ n → Good-ψ⁰ (hg n) (l-inv ex n)) (λ n → ψ⁰-cong (st n))
Good-ψ⁰ (gi {p = q} {f = f} hb hm) ex =
  gl (λ n → Good-ψ⁰ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n))) (i-resp ex (chain-≅ ex n)))
     (λ n → ψ⁰-cong (hm (chain-step ex hm n)))
Good-ψ⁰ (gu {r = zero} g) ex   = Good-ψ⁰ g (u-refl zero ex)
Good-ψ⁰ (gu {r = self n} g) ex = Good-ψ⁰ g (u-refl (self n) ex)
```

## §2 目标 1 的好树

```agda
Good-ψ¹ : ∀ {k} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ¹ x)
Good-ψ¹ gz ex = Good-Ω (suc zero)
Good-ψ¹ (gs {a} g) ex = gl (Good-iter (Good-ψ¹ g ea) (ψ¹-≅ ea)) (rule4ᵒ (ψ¹-≅ ea))
  where ea = s-inv ex
Good-ψ¹ (gl hg st) ex = gl (λ n → Good-ψ¹ (hg n) (l-inv ex n)) (λ n → ψ¹-cong (st n))
Good-ψ¹ (gi {j = zero} {p = q} {f = f} hb hm) ex =
  gi (λ z ez g → Good-ψ¹ (hb z ez (Good→Gd (<→◃ q) g)) (i-resp ex ez)) (λ h → ψ¹-cong (hm h))
Good-ψ¹ (gi {j = suc a} {p = q} {f = f} hb hm) ex =
  gl (λ n → Good-ψ¹ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n))) (i-resp ex (chain-≅ ex n)))
     (λ n → ψ¹-cong (hm (chain-step ex hm n)))
Good-ψ¹ (gi {j = lim h s} {p = q} {f = f} hb hm) ex =
  gl (λ n → Good-ψ¹ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n))) (i-resp ex (chain-≅ ex n)))
     (λ n → ψ¹-cong (hm (chain-step ex hm n)))
Good-ψ¹ (gu {r = zero} g) ex   = Good-ψ¹ g (u-refl zero ex)
Good-ψ¹ (gu {r = self n} g) ex = Good-ψ¹ g (u-refl (self n) ex)
```

## §3 好树读回成好层号

`em-mono`: 下标单调到观测. `good-em`: `em a` 是好树. **`Good→WF₁`: 第 1 层的好树读回好层号**, 这是闭包定理的出口. 闭包的 `WF` 要的第一支在分支之下与严格上升, 都由 `hm` 给, 分支的好由 `hb` 给. 全部对 $x$ 的推导结构递归, 没有世界.

```agda
em<ᵒ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → em (suc a) ⊑ᵒ em b
em<ᵒ e zero      = ≅→⊑ᵒ (s≅ (em-≅ e))
em<ᵒ e (suc q)   = suc-r (em<ᵒ e q)
em<ᵒ e (lim n q) = lim-r n (em<ᵒ e q)

em-self : ∀ a → em a ≅ em a
em-self a = em-≅ (≅ᴵ-refl a)

em-mono : ∀ {a b} → a ⊑ᴵ b → em a ⊑ᵒ em b
em-mono {b = b} z⊑ = zero-l (em-self b)
em-mono (s⊑ e q)   = em<ᵒ e q
em-mono (l⊑ k)     = lim-l (λ n → em-mono (k n))

good-em : ∀ a → Good (em a)
good-em zero      = gz
good-em (suc a)   = gs (good-em a)
good-em (lim f s) = gl (λ n → good-em (f n)) (λ n → em-mono (s n))

suc⊑→⊑ : ∀ {a b} → suc a ⊑ᴵ b → a ⊑ᴵ b
suc⊑→⊑ (s⊑ e q) = ⊑ᴵ-trans (≅→⊑ᴵ′ e) (⊑ᴵ-sub q)
  where
  ≅→⊑ᴵ′ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
  ≅→⊑ᴵ′ z≅ = z⊑
  ≅→⊑ᴵ′ (s≅ e) = s⊑ e zero
  ≅→⊑ᴵ′ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅→⊑ᴵ′ (h n)) (Sim→⊑ᴵ (λ q → lim n q)))
  ⊑ᴵ-sub : ∀ {a b} → a <ᴵ b → a ⊑ᴵ b
  ⊑ᴵ-sub q = Sim→⊑ᴵ (λ r → <ᴵ-trans r q)

Good→WF₀ : ∀ {x : Ordᶜ zero} → Good x → L.WFˢ (rb₀ x)
Good→WF₀ gz = tt
Good→WF₀ (gs g) = Good→WF₀ g
Good→WF₀ (gl hg st) = (λ n → st n (idO {b = b0} {b′ = b0})) , (λ n → Good→WF₀ (hg n))
Good→WF₀ (gi {p = ()} hb hm)
Good→WF₀ (gu {r = ()} g)

Good→WF₁ : ∀ {x : Ordᶜ (suc zero)} → Good x → L.WFˢ (rb₁ x)
Good→WF₁ gz = tt
Good→WF₁ (gs g) = Good→WF₁ g
Good→WF₁ (gl hg st) = (λ n → st n (idO {b = b1} {b′ = b1})) , (λ n → Good→WF₁ (hg n))
Good→WF₁ (gi {p = zero} {f = f} hb hm) =
  (λ η e → hm (em-mono (rd-one e)) (idO {b = b1} {b′ = b1})) ,
  (λ η e η′ e′ d → hm (em-mono (suc⊑→⊑ (rd-s e e′ d))) (idO {b = b1} {b′ = b1})) ,
  Good→WF₁ (hb (suc zero) (s≅ z≅) (gs gz)) ,
  (λ η e → Good→WF₁ (hb (em (rd e)) (em-self (rd e)) (good-em (rd e))))
Good→WF₁ (gi {p = suc ()} hb hm)
Good→WF₁ (gu {r = zero} g) = Good→WF₀ g
```

## §4 决定性的检验: $F\,\theta$ 与 $\mathrm{Lv}_5$

`F θ` $=\psi_1(\Omega_\theta)$ 读回. `WF-F`, `self-F`: **无条件**, 对一切 $\theta:\mathsf{Ord}^\mathsf I$. `F-mono`: 下标单调推出层号单调. `Lv₅`: 带守卫的闭包, 第 5 站的下标 $\psi_1(\Omega_\Omega)$. `WF-Lv₅`, `self-Lv₅`: 无条件.

```agda
F : Ordᴵ → L.LG
F θ = rb₁ (ψ¹ (Ω θ))

good-F : ∀ θ → Good (ψ¹ (Ω θ))
good-F θ = Good-ψ¹ (Good-Ω θ) (Ω-refl θ)

WF-F : ∀ θ → L.WFˢ (F θ)
WF-F θ = Good→WF₁ (good-F θ)

F-≈ : ∀ {a b} → a ≅ᴵ b → F a L.≈ F b
F-≈ e = rb-≈₁₁ (ψ¹-≅ (Ω-≅ e))

self-F : ∀ θ → F θ L.≈ F θ
self-F θ = F-≈ (≅ᴵ-refl θ)

F-mono : ∀ {a b} → a ⊑ᴵ b → F a L.⊴ F b
F-mono e = ψ¹-cong (Ω-monoᵒ e) (idO {b = b1} {b′ = b1})

Cf-F : ∀ θ → L.Cfˢ (F θ)
Cf-F θ = WF-F θ , self-F θ

Lv₅ : L.LG
Lv₅ = L.lc b₁ (F (suc zero)) (λ η e → F (rd e))

WF-Lv₅ : L.WFˢ Lv₅
WF-Lv₅ =
  (λ η e → F-mono (rd-one e)) ,
  (λ η e η′ e′ d → F-mono (suc⊑→⊑ (rd-s e e′ d))) ,
  WF-F (suc zero) ,
  (λ η e → WF-F (rd e))

self-Lv₅ : Lv₅ L.≈ Lv₅
self-Lv₅ = L.o≈ (Dom.≅ᴰ-refl 𝔻 b₁) (self-F (suc zero)) (λ η e η′ e′ k → F-≈ (rd-≅ e e′ k))

Cf-Lv₅ : L.Cfˢ Lv₅
Cf-Lv₅ = WF-Lv₅ , self-Lv₅
```
