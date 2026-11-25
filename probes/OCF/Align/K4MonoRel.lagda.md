# K4 (一): `Level` 族上单向的逐点关系

> **判决: HOLDS (定理, 已编译).** 定义关系 `_⊑ᵖ_` (带参数 `M`). 零, 后继, ℕ-极限, 提升的规则同 `Value._≼_` (另加右后继 `≤s`); Ω-结点只有两条: 逐点 (`i≤`: 分支层 `≅ᴵ` 相关, 输入相关则分支相关) 与 "在右结点的全部分支之下" (`≤i`). 值序的 `≼i` (在某一支之下) 与 `i≼` 不在定义里. `M = ⊤` 时左自反 (`⊑ᵖ-reflˡ`) 且传递 (`⊑ᵖ-trans`), 对一切层; 层间搬运在关系下不可见 (`tr-⊑`, `⊑-tr`, `tr²`).
> **不否定:** `M = ⊥` 版的传递未证, 也无反例. 只导入 [Level](Level.lagda.md), 导入闭包无记号模块. 入口 [K4Mono](K4Mono.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K4MonoRel where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.Align.Level
open Restr
```

## §1 定义

写法同 `Level.Eq₊` (低层关系 `Q` 作参数, 所以严格正). 两处定义理由: `i≤` 的第二个前提是 `M` 之下左结点分支的单调性, 传递要用它得到中间输入的自反; `≤i` 对右结点的一切原始输入量化, 它给出最小元 (`zero⊑`), 传递里 `≤i` 接 `i≤` 用零作中间输入.

```agda
into-out : ∀ {i ℓ} (r : i ◃ ℓ) (y : U i r) → into r (out r y) ≡ y
into-out zero      y = refl
into-out (suc r)   y = into-out r y
into-out (self n)  y = refl
into-out (lim n r) y = into-out r y

module Rel (M : Set) where

  module _ (ℓ : Ordᴵ) (Q : (i : Ordᴵ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set) where
    data Le₊ : ∀ {ℓ′} → Ordᶜ ℓ → Ordᶜ ℓ′ → Set where
      z≤ : ∀ {ℓ′} → Le₊ {ℓ′} zero zero
      s≤ : ∀ {ℓ′} {a : Ordᶜ ℓ} {b : Ordᶜ ℓ′} → Le₊ a b → Le₊ (suc a) (suc b)
      ≤s : ∀ {ℓ′} {a : Ordᶜ ℓ} {b : Ordᶜ ℓ′} → Le₊ a b → Le₊ a (suc b)
      ≤l : ∀ {ℓ′} {a : Ordᶜ ℓ} {g : ℕ → Ordᶜ ℓ′} n → Le₊ a (g n) → Le₊ a (lim g)
      l≤ : ∀ {ℓ′} {f : ℕ → Ordᶜ ℓ} {b : Ordᶜ ℓ′} → (∀ n → Le₊ (f n) b) → Le₊ (lim f) b
      i≤ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : U j (<→◃ p) → Ordᶜ ℓ} {g : U j′ (<→◃ q) → Ordᶜ ℓ′} →
           j ≅ᴵ j′ →
           (M → ∀ (x y : Ordᶜ j) → Q j (<→◃ p) (into (<→◃ p) x) y → Le₊ (f (into (<→◃ p) x)) (f (into (<→◃ p) y))) →
           (∀ (x : Ordᶜ j) (y : Ordᶜ j′) → Q j (<→◃ p) (into (<→◃ p) x) y → Le₊ (f (into (<→◃ p) x)) (g (into (<→◃ q) y))) →
           Le₊ (limᵢ p f) (limᵢ q g)
      ≤i : ∀ {ℓ′ j′} {a : Ordᶜ ℓ} {q : j′ <ᴵ ℓ′} {g : U j′ (<→◃ q) → Ordᶜ ℓ′} →
           (∀ (y : U j′ (<→◃ q)) → Le₊ a (g y)) → Le₊ a (limᵢ q g)
      u≤ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → Q k (◃₁→◃ r) x b → Le₊ (up r x) b
      ≤u : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : U k (◃₁→◃ r)} {a : Ordᶜ ℓ} → Le₊ a (out (◃₁→◃ r) y) → Le₊ a (up r y)

  Rᵖ : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set
  Rᵖ i zero         x b = Le₊ i Rᵖ x b
  Rᵖ i (suc r)      x b = Rᵖ i r x b
  Rᵖ _ (self {f} n) x b = Le₊ (f n) Rᵖ x b
  Rᵖ i (lim n r)    x b = Rᵖ i r x b

  infix 4 _⊑ᵖ_
  _⊑ᵖ_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
  _⊑ᵖ_ {ℓ₁} = Le₊ ℓ₁ Rᵖ

  R→⊑ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → Rᵖ i r (into r x) b → x ⊑ᵖ b
  R→⊑ zero      e = e
  R→⊑ (suc r)   e = R→⊑ r e
  R→⊑ (self n)  e = e
  R→⊑ (lim n r) e = R→⊑ r e

  ⊑→R : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → x ⊑ᵖ b → Rᵖ i r (into r x) b
  ⊑→R zero      e = e
  ⊑→R (suc r)   e = ⊑→R r e
  ⊑→R (self n)  e = e
  ⊑→R (lim n r) e = ⊑→R r e

  Rᵖ-conv : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordᶜ j} {b : Ordᶜ ℓ′} → Rᵖ j r (into r x) b → Rᵖ j r′ (into r′ x) b
  Rᵖ-conv r r′ e = ⊑→R r′ (R→⊑ r e)
```

`i≤` 的两个前提用 `_⊑ᵖ_` 写出来 (`node-⊑`).

```agda
  node-⊑ : ∀ {ℓ ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : U j (<→◃ p) → Ordᶜ ℓ} {g : U j′ (<→◃ q) → Ordᶜ ℓ′} →
           j ≅ᴵ j′ →
           (M → ∀ (x y : Ordᶜ j) → x ⊑ᵖ y → f (into (<→◃ p) x) ⊑ᵖ f (into (<→◃ p) y)) →
           (∀ (x : Ordᶜ j) (y : Ordᶜ j′) → x ⊑ᵖ y → f (into (<→◃ p) x) ⊑ᵖ g (into (<→◃ q) y)) →
           limᵢ p f ⊑ᵖ limᵢ q g
  node-⊑ {p = p} e m h = i≤ e (λ μ x y d → m μ x y (R→⊑ (<→◃ p) d)) (λ x y d → h x y (R→⊑ (<→◃ p) d))

  lim-⊑ᵖ : ∀ {ℓ ℓ′} {f : ℕ → Ordᶜ ℓ} {g : ℕ → Ordᶜ ℓ′} → (∀ n → f n ⊑ᵖ g n) → lim f ⊑ᵖ lim g
  lim-⊑ᵖ h = l≤ (λ n → ≤l n (h n))
```

提升的反演: 提升在两侧都透明.

```agda
  ≤u⁻ : ∀ {ℓ ℓ′ k} {r : k ◃₁ ℓ′} {y : U k (◃₁→◃ r)} {a : Ordᶜ ℓ} → a ⊑ᵖ up r y → a ⊑ᵖ out (◃₁→◃ r) y
  ≤u⁻ (l≤ h)             = l≤ (λ n → ≤u⁻ (h n))
  ≤u⁻ (u≤ {r = zero} d)   = u≤ (≤u⁻ d)
  ≤u⁻ (u≤ {r = self n} d) = u≤ (≤u⁻ d)
  ≤u⁻ (≤u d)             = d

  u≤⁻ : ∀ {ℓ ℓ′ k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → up r x ⊑ᵖ b → out (◃₁→◃ r) x ⊑ᵖ b
  u≤⁻ {r = zero}   (u≤ d) = d
  u≤⁻ {r = self n} (u≤ d) = d
  u≤⁻ (≤s d)   = ≤s (u≤⁻ d)
  u≤⁻ (≤l n d) = ≤l n (u≤⁻ d)
  u≤⁻ (≤i h)   = ≤i (λ y → u≤⁻ (h y))
  u≤⁻ (≤u d)   = ≤u (u≤⁻ d)
```

## §2 左自反

在 `M` 之下, $a\sqsubseteq b$ 的推导里已经存着 $a$ 的每个 Ω-结点的单调性, 所以 $a\sqsubseteq a$. 下面把 $a\sqsubseteq a$ 叫作 $a$ **合法**.

```agda
  ⊑ᵖ-reflˡ : M → ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ⊑ᵖ b → a ⊑ᵖ a
  ⊑ᵖ-reflˡ μ z≤                 = z≤
  ⊑ᵖ-reflˡ μ (s≤ d)             = s≤ (⊑ᵖ-reflˡ μ d)
  ⊑ᵖ-reflˡ μ (≤s d)             = ⊑ᵖ-reflˡ μ d
  ⊑ᵖ-reflˡ μ (≤l n d)           = ⊑ᵖ-reflˡ μ d
  ⊑ᵖ-reflˡ μ (l≤ h)             = l≤ (λ n → ≤l n (⊑ᵖ-reflˡ μ (h n)))
  ⊑ᵖ-reflˡ μ (i≤ {j = j} e m h) = i≤ (≅ᴵ-refl j) m (m μ)
  ⊑ᵖ-reflˡ μ (≤i {q = q} h)     = ⊑ᵖ-reflˡ μ (h (into (<→◃ q) zero))
  ⊑ᵖ-reflˡ μ (u≤ {r = zero} d)   = u≤ (≤u (⊑ᵖ-reflˡ μ d))
  ⊑ᵖ-reflˡ μ (u≤ {r = self n} d) = u≤ (≤u (⊑ᵖ-reflˡ μ d))
  ⊑ᵖ-reflˡ μ (≤u d)             = ⊑ᵖ-reflˡ μ d
```

第 0 层的树都合法; 零在一切层的一切树之下. 不用 `M`.

```agda
  ⊑ᵖ-refl⁰ : (a : Ordᶜ zero) → a ⊑ᵖ a
  ⊑ᵖ-refl⁰ zero        = z≤
  ⊑ᵖ-refl⁰ (suc a)     = s≤ (⊑ᵖ-refl⁰ a)
  ⊑ᵖ-refl⁰ (lim f)     = lim-⊑ᵖ (λ n → ⊑ᵖ-refl⁰ (f n))
  ⊑ᵖ-refl⁰ (limᵢ () f)
  ⊑ᵖ-refl⁰ (up () x)

  zero⊑ : ∀ {ℓ ℓ′} (b : Ordᶜ ℓ′) → 𝟎 {ℓ} ⊑ᵖ b
  zero⊑ zero            = z≤
  zero⊑ (suc b)         = ≤s (zero⊑ b)
  zero⊑ (lim f)         = ≤l 0 (zero⊑ (f 0))
  zero⊑ (limᵢ p f)      = ≤i (λ y → zero⊑ (f y))
  zero⊑ (up zero x)     = ≤u (zero⊑ x)
  zero⊑ (up (self n) x) = ≤u (zero⊑ x)
```

## §3 层间搬运在关系下不可见

`Level.tr` 沿 $a\cong^{\mathsf I}b$ 把第 $a$ 层的树搬到第 $b$ 层. `_≅_` 的情形 (`Level.tr-≅`) 一侧搬运加对称就够. 这里没有对称, 所以分三组:

- 右侧搬 (`⊑-tr`, `⊑-tr⁻`, `⊑-back`, `⊑-back⁻`): $y\sqsubseteq x\Rightarrow y\sqsubseteq\mathrm{tr}\,e\,x$. 左边的结点不动, 单调性字段原样带过去.
- 两侧同时搬 (`tr²`, `tr⁻²`, `back²`, `back⁻²`, `tr⁻-back`, `tr-back⁻`): $x\sqsubseteq y\Rightarrow\mathrm{tr}\,e_1\,x\sqsubseteq\mathrm{tr}\,e_2\,y$. 搬过的左结点的单调性字段由同一条引理 (取 $e_2=e_1$) 给出.
- 左侧搬 (`tr-⊑`, `tr⁻-⊑`, `back-⊑`, `back⁻-⊑`): $x\sqsubseteq y\Rightarrow\mathrm{tr}\,e\,x\sqsubseteq y$. 单调性字段用两侧版.

每组的递归结构与 `Level.tr-≅` 相同: 对 ($e$, 推导) 的字典序.

```agda
  ⊑-tr    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordᶜ ℓ′} {x : Ordᶜ a} → y ⊑ᵖ x → y ⊑ᵖ tr e x
  ⊑-tr⁻   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordᶜ ℓ′} {x : Ordᶜ b} → y ⊑ᵖ x → y ⊑ᵖ tr⁻ e x
  ⊑-back  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {v : Ordᶜ ℓ′} {u : Ordᶜ (rep (res q e))} → v ⊑ᵖ u → v ⊑ᵖ back (res q e) u
  ⊑-back⁻ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {v : Ordᶜ ℓ′} {u : Ordᶜ (rep (res⁻ q e))} → v ⊑ᵖ u → v ⊑ᵖ back (res⁻ q e) u

  ⊑-tr e z≤       = z≤
  ⊑-tr e (s≤ d)   = s≤ (⊑-tr e d)
  ⊑-tr e (≤s d)   = ≤s (⊑-tr e d)
  ⊑-tr e (≤l n d) = ≤l n (⊑-tr e d)
  ⊑-tr e (l≤ h)   = l≤ (λ n → ⊑-tr e (h n))
  ⊑-tr e (i≤ {p = p} {q = q} {f = f} {g = g} ej m h) =
    i≤ (≅ᴵ-trans ej (eq (res q e))) m λ u v d →
      subst (λ w → f (into (<→◃ p) u) ⊑ᵖ tr e (g (into (<→◃ q) (back (res q e) w))))
            (sym (out-into (<→◃ (lt (res q e))) v))
            (⊑-tr e (h u (back (res q e) v) (⊑→R (<→◃ p) (⊑-back q e (R→⊑ (<→◃ p) d)))))
  ⊑-tr e (≤i {q = q} h) = ≤i (λ y → ⊑-tr e (h (into (<→◃ q) (back (res q e) (out (<→◃ (lt (res q e))) y)))))
  ⊑-tr e (u≤ {r = zero} d)   = u≤ (⊑-tr e d)
  ⊑-tr e (u≤ {r = self n} d) = u≤ (⊑-tr e d)
  ⊑-tr (s≅ e) (≤u {r = zero} d)   = ≤u (⊑-tr e d)
  ⊑-tr (l≅ h) (≤u {r = self n} d) = ≤u (⊑-tr (h n) d)

  ⊑-tr⁻ e z≤       = z≤
  ⊑-tr⁻ e (s≤ d)   = s≤ (⊑-tr⁻ e d)
  ⊑-tr⁻ e (≤s d)   = ≤s (⊑-tr⁻ e d)
  ⊑-tr⁻ e (≤l n d) = ≤l n (⊑-tr⁻ e d)
  ⊑-tr⁻ e (l≤ h)   = l≤ (λ n → ⊑-tr⁻ e (h n))
  ⊑-tr⁻ e (i≤ {p = p} {q = q} {f = f} {g = g} ej m h) =
    i≤ (≅ᴵ-trans ej (eq (res⁻ q e))) m λ u v d →
      subst (λ w → f (into (<→◃ p) u) ⊑ᵖ tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) w))))
            (sym (out-into (<→◃ (lt (res⁻ q e))) v))
            (⊑-tr⁻ e (h u (back (res⁻ q e) v) (⊑→R (<→◃ p) (⊑-back⁻ q e (R→⊑ (<→◃ p) d)))))
  ⊑-tr⁻ e (≤i {q = q} h) = ≤i (λ y → ⊑-tr⁻ e (h (into (<→◃ q) (back (res⁻ q e) (out (<→◃ (lt (res⁻ q e))) y)))))
  ⊑-tr⁻ e (u≤ {r = zero} d)   = u≤ (⊑-tr⁻ e d)
  ⊑-tr⁻ e (u≤ {r = self n} d) = u≤ (⊑-tr⁻ e d)
  ⊑-tr⁻ (s≅ e) (≤u {r = zero} d)   = ≤u (⊑-tr⁻ e d)
  ⊑-tr⁻ (l≅ h) (≤u {r = self n} d) = ≤u (⊑-tr⁻ (h n) d)

  ⊑-back zero      (s≅ e) d = ⊑-tr⁻ e d
  ⊑-back (suc q)   (s≅ e) d = ⊑-back q e d
  ⊑-back (lim n q) (l≅ h) d = ⊑-back q (h n) d

  ⊑-back⁻ zero      (s≅ e) d = ⊑-tr e d
  ⊑-back⁻ (suc q)   (s≅ e) d = ⊑-back⁻ q e d
  ⊑-back⁻ (lim n q) (l≅ h) d = ⊑-back⁻ q (h n) d
```

两侧同时搬. `back (res q e)` 沿 $q$ 下降到底是某个子证明上的 `tr⁻`, 两侧的 $q_1,q_2$ 长度可以不同, 所以多两条过渡引理 (`tr⁻-back`, `tr-back⁻`): 左边已经到底, 右边继续下降.

```agda
  tr²      : ∀ {a₁ b₁ a₂ b₂} (e₁ : a₁ ≅ᴵ b₁) (e₂ : a₂ ≅ᴵ b₂) {x : Ordᶜ a₁} {y : Ordᶜ a₂} → x ⊑ᵖ y → tr e₁ x ⊑ᵖ tr e₂ y
  tr⁻²     : ∀ {a₁ b₁ a₂ b₂} (e₁ : a₁ ≅ᴵ b₁) (e₂ : a₂ ≅ᴵ b₂) {x : Ordᶜ b₁} {y : Ordᶜ b₂} → x ⊑ᵖ y → tr⁻ e₁ x ⊑ᵖ tr⁻ e₂ y
  back²    : ∀ {j₁ a₁ b₁ j₂ a₂ b₂} (q₁ : j₁ <ᴵ a₁) (e₁ : a₁ ≅ᴵ b₁) (q₂ : j₂ <ᴵ a₂) (e₂ : a₂ ≅ᴵ b₂)
             {u : Ordᶜ (rep (res q₁ e₁))} {v : Ordᶜ (rep (res q₂ e₂))} → u ⊑ᵖ v → back (res q₁ e₁) u ⊑ᵖ back (res q₂ e₂) v
  back⁻²   : ∀ {j₁ a₁ b₁ j₂ a₂ b₂} (q₁ : j₁ <ᴵ b₁) (e₁ : a₁ ≅ᴵ b₁) (q₂ : j₂ <ᴵ b₂) (e₂ : a₂ ≅ᴵ b₂)
             {u : Ordᶜ (rep (res⁻ q₁ e₁))} {v : Ordᶜ (rep (res⁻ q₂ e₂))} → u ⊑ᵖ v → back (res⁻ q₁ e₁) u ⊑ᵖ back (res⁻ q₂ e₂) v
  tr⁻-back : ∀ {a₁ b₁ j₂ a₂ b₂} (e₁ : a₁ ≅ᴵ b₁) (q₂ : j₂ <ᴵ a₂) (e₂ : a₂ ≅ᴵ b₂)
             {u : Ordᶜ b₁} {v : Ordᶜ (rep (res q₂ e₂))} → u ⊑ᵖ v → tr⁻ e₁ u ⊑ᵖ back (res q₂ e₂) v
  tr-back⁻ : ∀ {a₁ b₁ j₂ a₂ b₂} (e₁ : a₁ ≅ᴵ b₁) (q₂ : j₂ <ᴵ b₂) (e₂ : a₂ ≅ᴵ b₂)
             {u : Ordᶜ a₁} {v : Ordᶜ (rep (res⁻ q₂ e₂))} → u ⊑ᵖ v → tr e₁ u ⊑ᵖ back (res⁻ q₂ e₂) v

  tr² e₁ e₂ z≤       = z≤
  tr² e₁ e₂ (s≤ d)   = s≤ (tr² e₁ e₂ d)
  tr² e₁ e₂ (≤s d)   = ≤s (tr² e₁ e₂ d)
  tr² e₁ e₂ (≤l n d) = ≤l n (tr² e₁ e₂ d)
  tr² e₁ e₂ (l≤ h)   = l≤ (λ n → tr² e₁ e₂ (h n))
  tr² e₁ e₂ (i≤ {p = q₁} {q = q₂} {f = f} {g = g} ej m h) =
    i≤ (≅ᴵ-trans (≅ᴵ-sym (eq (res q₁ e₁))) (≅ᴵ-trans ej (eq (res q₂ e₂))))
       (λ μ u v d →
          subst₂ (λ w w′ → tr e₁ (f (into (<→◃ q₁) (back (res q₁ e₁) w))) ⊑ᵖ tr e₁ (f (into (<→◃ q₁) (back (res q₁ e₁) w′))))
                 (sym (out-into (<→◃ (lt (res q₁ e₁))) u)) (sym (out-into (<→◃ (lt (res q₁ e₁))) v))
                 (tr² e₁ e₁ (m μ _ _ (⊑→R (<→◃ q₁) (back² q₁ e₁ q₁ e₁ (R→⊑ (<→◃ (lt (res q₁ e₁))) d))))))
       (λ u v d →
          subst₂ (λ w w′ → tr e₁ (f (into (<→◃ q₁) (back (res q₁ e₁) w))) ⊑ᵖ tr e₂ (g (into (<→◃ q₂) (back (res q₂ e₂) w′))))
                 (sym (out-into (<→◃ (lt (res q₁ e₁))) u)) (sym (out-into (<→◃ (lt (res q₂ e₂))) v))
                 (tr² e₁ e₂ (h _ _ (⊑→R (<→◃ q₁) (back² q₁ e₁ q₂ e₂ (R→⊑ (<→◃ (lt (res q₁ e₁))) d))))))
  tr² e₁ e₂ (≤i {q = q} h) = ≤i (λ y → tr² e₁ e₂ (h (into (<→◃ q) (back (res q e₂) (out (<→◃ (lt (res q e₂))) y)))))
  tr² (s≅ e₁) e₂ (u≤ {r = zero} d)   = u≤ (tr² e₁ e₂ d)
  tr² (l≅ h₁) e₂ (u≤ {r = self n} d) = u≤ (tr² (h₁ n) e₂ d)
  tr² e₁ (s≅ e₂) (≤u {r = zero} d)   = ≤u (tr² e₁ e₂ d)
  tr² e₁ (l≅ h₂) (≤u {r = self n} d) = ≤u (tr² e₁ (h₂ n) d)

  tr⁻² e₁ e₂ z≤       = z≤
  tr⁻² e₁ e₂ (s≤ d)   = s≤ (tr⁻² e₁ e₂ d)
  tr⁻² e₁ e₂ (≤s d)   = ≤s (tr⁻² e₁ e₂ d)
  tr⁻² e₁ e₂ (≤l n d) = ≤l n (tr⁻² e₁ e₂ d)
  tr⁻² e₁ e₂ (l≤ h)   = l≤ (λ n → tr⁻² e₁ e₂ (h n))
  tr⁻² e₁ e₂ (i≤ {p = q₁} {q = q₂} {f = f} {g = g} ej m h) =
    i≤ (≅ᴵ-trans (≅ᴵ-sym (eq (res⁻ q₁ e₁))) (≅ᴵ-trans ej (eq (res⁻ q₂ e₂))))
       (λ μ u v d →
          subst₂ (λ w w′ → tr⁻ e₁ (f (into (<→◃ q₁) (back (res⁻ q₁ e₁) w))) ⊑ᵖ tr⁻ e₁ (f (into (<→◃ q₁) (back (res⁻ q₁ e₁) w′))))
                 (sym (out-into (<→◃ (lt (res⁻ q₁ e₁))) u)) (sym (out-into (<→◃ (lt (res⁻ q₁ e₁))) v))
                 (tr⁻² e₁ e₁ (m μ _ _ (⊑→R (<→◃ q₁) (back⁻² q₁ e₁ q₁ e₁ (R→⊑ (<→◃ (lt (res⁻ q₁ e₁))) d))))))
       (λ u v d →
          subst₂ (λ w w′ → tr⁻ e₁ (f (into (<→◃ q₁) (back (res⁻ q₁ e₁) w))) ⊑ᵖ tr⁻ e₂ (g (into (<→◃ q₂) (back (res⁻ q₂ e₂) w′))))
                 (sym (out-into (<→◃ (lt (res⁻ q₁ e₁))) u)) (sym (out-into (<→◃ (lt (res⁻ q₂ e₂))) v))
                 (tr⁻² e₁ e₂ (h _ _ (⊑→R (<→◃ q₁) (back⁻² q₁ e₁ q₂ e₂ (R→⊑ (<→◃ (lt (res⁻ q₁ e₁))) d))))))
  tr⁻² e₁ e₂ (≤i {q = q} h) = ≤i (λ y → tr⁻² e₁ e₂ (h (into (<→◃ q) (back (res⁻ q e₂) (out (<→◃ (lt (res⁻ q e₂))) y)))))
  tr⁻² (s≅ e₁) e₂ (u≤ {r = zero} d)   = u≤ (tr⁻² e₁ e₂ d)
  tr⁻² (l≅ h₁) e₂ (u≤ {r = self n} d) = u≤ (tr⁻² (h₁ n) e₂ d)
  tr⁻² e₁ (s≅ e₂) (≤u {r = zero} d)   = ≤u (tr⁻² e₁ e₂ d)
  tr⁻² e₁ (l≅ h₂) (≤u {r = self n} d) = ≤u (tr⁻² e₁ (h₂ n) d)

  back² zero       (s≅ e₁) q₂ e₂ d = tr⁻-back e₁ q₂ e₂ d
  back² (suc q₁)   (s≅ e₁) q₂ e₂ d = back² q₁ e₁ q₂ e₂ d
  back² (lim n q₁) (l≅ h₁) q₂ e₂ d = back² q₁ (h₁ n) q₂ e₂ d

  back⁻² zero       (s≅ e₁) q₂ e₂ d = tr-back⁻ e₁ q₂ e₂ d
  back⁻² (suc q₁)   (s≅ e₁) q₂ e₂ d = back⁻² q₁ e₁ q₂ e₂ d
  back⁻² (lim n q₁) (l≅ h₁) q₂ e₂ d = back⁻² q₁ (h₁ n) q₂ e₂ d

  tr⁻-back e₁ zero       (s≅ e₂) d = tr⁻² e₁ e₂ d
  tr⁻-back e₁ (suc q₂)   (s≅ e₂) d = tr⁻-back e₁ q₂ e₂ d
  tr⁻-back e₁ (lim n q₂) (l≅ h₂) d = tr⁻-back e₁ q₂ (h₂ n) d

  tr-back⁻ e₁ zero       (s≅ e₂) d = tr² e₁ e₂ d
  tr-back⁻ e₁ (suc q₂)   (s≅ e₂) d = tr-back⁻ e₁ q₂ e₂ d
  tr-back⁻ e₁ (lim n q₂) (l≅ h₂) d = tr-back⁻ e₁ q₂ (h₂ n) d
```

左侧搬.

```agda
  tr-⊑    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordᶜ a} {y : Ordᶜ ℓ′} → x ⊑ᵖ y → tr e x ⊑ᵖ y
  tr⁻-⊑   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordᶜ b} {y : Ordᶜ ℓ′} → x ⊑ᵖ y → tr⁻ e x ⊑ᵖ y
  back-⊑  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {v : Ordᶜ ℓ′} → u ⊑ᵖ v → back (res q e) u ⊑ᵖ v
  back⁻-⊑ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {v : Ordᶜ ℓ′} → u ⊑ᵖ v → back (res⁻ q e) u ⊑ᵖ v

  tr-⊑ e z≤       = z≤
  tr-⊑ e (s≤ d)   = s≤ (tr-⊑ e d)
  tr-⊑ e (≤s d)   = ≤s (tr-⊑ e d)
  tr-⊑ e (≤l n d) = ≤l n (tr-⊑ e d)
  tr-⊑ e (l≤ h)   = l≤ (λ n → tr-⊑ e (h n))
  tr-⊑ e (i≤ {p = q} {q = q₂} {f = f} {g = g} ej m h) =
    i≤ (≅ᴵ-trans (≅ᴵ-sym (eq (res q e))) ej)
       (λ μ u v d →
          subst₂ (λ w w′ → tr e (f (into (<→◃ q) (back (res q e) w))) ⊑ᵖ tr e (f (into (<→◃ q) (back (res q e) w′))))
                 (sym (out-into (<→◃ (lt (res q e))) u)) (sym (out-into (<→◃ (lt (res q e))) v))
                 (tr² e e (m μ _ _ (⊑→R (<→◃ q) (back² q e q e (R→⊑ (<→◃ (lt (res q e))) d))))))
       (λ u v d →
          subst (λ w → tr e (f (into (<→◃ q) (back (res q e) w))) ⊑ᵖ g (into (<→◃ q₂) v))
                (sym (out-into (<→◃ (lt (res q e))) u))
                (tr-⊑ e (h _ v (⊑→R (<→◃ q) (back-⊑ q e (R→⊑ (<→◃ (lt (res q e))) d))))))
  tr-⊑ e (≤i h) = ≤i (λ y → tr-⊑ e (h y))
  tr-⊑ (s≅ e) (u≤ {r = zero} d)   = u≤ (tr-⊑ e d)
  tr-⊑ (l≅ h) (u≤ {r = self n} d) = u≤ (tr-⊑ (h n) d)
  tr-⊑ e (≤u d) = ≤u (tr-⊑ e d)

  tr⁻-⊑ e z≤       = z≤
  tr⁻-⊑ e (s≤ d)   = s≤ (tr⁻-⊑ e d)
  tr⁻-⊑ e (≤s d)   = ≤s (tr⁻-⊑ e d)
  tr⁻-⊑ e (≤l n d) = ≤l n (tr⁻-⊑ e d)
  tr⁻-⊑ e (l≤ h)   = l≤ (λ n → tr⁻-⊑ e (h n))
  tr⁻-⊑ e (i≤ {p = q} {q = q₂} {f = f} {g = g} ej m h) =
    i≤ (≅ᴵ-trans (≅ᴵ-sym (eq (res⁻ q e))) ej)
       (λ μ u v d →
          subst₂ (λ w w′ → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))) ⊑ᵖ tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w′))))
                 (sym (out-into (<→◃ (lt (res⁻ q e))) u)) (sym (out-into (<→◃ (lt (res⁻ q e))) v))
                 (tr⁻² e e (m μ _ _ (⊑→R (<→◃ q) (back⁻² q e q e (R→⊑ (<→◃ (lt (res⁻ q e))) d))))))
       (λ u v d →
          subst (λ w → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))) ⊑ᵖ g (into (<→◃ q₂) v))
                (sym (out-into (<→◃ (lt (res⁻ q e))) u))
                (tr⁻-⊑ e (h _ v (⊑→R (<→◃ q) (back⁻-⊑ q e (R→⊑ (<→◃ (lt (res⁻ q e))) d))))))
  tr⁻-⊑ e (≤i h) = ≤i (λ y → tr⁻-⊑ e (h y))
  tr⁻-⊑ (s≅ e) (u≤ {r = zero} d)   = u≤ (tr⁻-⊑ e d)
  tr⁻-⊑ (l≅ h) (u≤ {r = self n} d) = u≤ (tr⁻-⊑ (h n) d)
  tr⁻-⊑ e (≤u d) = ≤u (tr⁻-⊑ e d)

  back-⊑ zero      (s≅ e) d = tr⁻-⊑ e d
  back-⊑ (suc q)   (s≅ e) d = back-⊑ q e d
  back-⊑ (lim n q) (l≅ h) d = back-⊑ q (h n) d

  back⁻-⊑ zero      (s≅ e) d = tr-⊑ e d
  back⁻-⊑ (suc q)   (s≅ e) d = back⁻-⊑ q e d
  back⁻-⊑ (lim n q) (l≅ h) d = back⁻-⊑ q (h n) d
```

## §4 传递

`M` 只用在 `i≤` 接 `i≤`: 给了 $x\sqsubseteq z$, 中间输入取 $\mathrm{tr}\,e\,x$, 要 $x\sqsubseteq\mathrm{tr}\,e\,x$, 即 $x$ 合法 (`⊑ᵖ-reflˡ`).

```agda
  ⊑ᵖ-trans : M → ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ⊑ᵖ b → b ⊑ᵖ c → a ⊑ᵖ c
  ⊑ᵖ-trans μ (u≤ {r = zero} e)   d = u≤ (⊑ᵖ-trans μ e d)
  ⊑ᵖ-trans μ (u≤ {r = self n} e) d = u≤ (⊑ᵖ-trans μ e d)
  ⊑ᵖ-trans μ (l≤ h)   d        = l≤ (λ n → ⊑ᵖ-trans μ (h n) d)
  ⊑ᵖ-trans μ d        (≤u e)   = ≤u (⊑ᵖ-trans μ d e)
  ⊑ᵖ-trans μ d        (≤s e)   = ≤s (⊑ᵖ-trans μ d e)
  ⊑ᵖ-trans μ d        (≤l n e) = ≤l n (⊑ᵖ-trans μ d e)
  ⊑ᵖ-trans μ d        (≤i h)   = ≤i (λ y → ⊑ᵖ-trans μ d (h y))
  ⊑ᵖ-trans μ z≤       z≤       = z≤
  ⊑ᵖ-trans μ (s≤ d)   (s≤ e)   = s≤ (⊑ᵖ-trans μ d e)
  ⊑ᵖ-trans μ (≤s d)   (s≤ e)   = ≤s (⊑ᵖ-trans μ d e)
  ⊑ᵖ-trans μ (≤l n d) (l≤ h)   = ⊑ᵖ-trans μ d (h n)
  ⊑ᵖ-trans μ (≤u {r = zero} d)   (u≤ e) = ⊑ᵖ-trans μ d e
  ⊑ᵖ-trans μ (≤u {r = self n} d) (u≤ e) = ⊑ᵖ-trans μ d e
  ⊑ᵖ-trans μ (i≤ {p = p} {q = q} e m h) (i≤ e′ m′ h′) =
    i≤ (≅ᴵ-trans e e′) m λ x z d →
      ⊑ᵖ-trans μ (h x (tr e x) (⊑→R (<→◃ p) (⊑-tr e (⊑ᵖ-reflˡ μ (R→⊑ (<→◃ p) d)))))
                 (h′ (tr e x) z (⊑→R (<→◃ q) (tr-⊑ e (R→⊑ (<→◃ p) d))))
  ⊑ᵖ-trans μ {a = a} (≤i {q = q} h) (i≤ {q = q″} {g = k} e′ m′ h′) =
    ≤i λ w → subst (λ v → a ⊑ᵖ k v) (into-out (<→◃ q″) w)
                   (⊑ᵖ-trans μ (h (into (<→◃ q) zero))
                               (h′ zero (out (<→◃ q″) w) (⊑→R (<→◃ q) (zero⊑ (out (<→◃ q″) w)))))
```

## §5 两个版本

```agda
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

-- 不带合法性: i≤ 的单调性字段是空的
module Wide = Rel ⊥
-- 带左合法性: a ⊑ b 蕴含 a ⊑ a, 关系传递
module Legal = Rel ⊤
```

