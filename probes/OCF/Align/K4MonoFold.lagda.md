# K4 (二): 折叠保持逐点关系, 对一切层

> 入口 [K4Mono](K4Mono.lagda.md). 第 4 层 (验收侧) 的工具, 不进成品. 只导入 [Level](Level.lagda.md) 与 [K4MonoRel](K4MonoRel.lagda.md), 不改任何已有文件. `importclosure.py OCF.Align.K4MonoFold`: 禁用表命中 0.
>
> **定理 `ψ-⊑` (已编译).** 对一切目标层 $i\cong^{\mathsf I}i'$, 一切输入层, 一切折叠证据:
>
>     ψ-⊑ : i ≅ᴵ i′ → a ⊑ᵖ b → ψ p σ a ⊑ᵖ ψ p′ σ′ b
>
> 陈述与 `Level.ψ-≅` 逐字同形, 只把 `_≅_` 换成 `_⊑ᵖ_`. 对关系的两个版本 (`M` 任意) 都成立, 没有合法性前提. 证明是对 $a\sqsubseteq b$ 的推导的一个结构归纳, 一切层一条, 不按层号分情况.
>
> 同时得到: $\Omega$ 尊重层号的 `≅ᴵ` (`Ω-⊑`), 加法对两个参数单调 (`add-⊑`), 目标层 0 的无证明折叠 (`ψ⁰-⊑`).
>
> **证明里每一行用到什么.**
>
> | 规则 | 输入的关系 | 用到 |
> |---|---|---|
> | 1 ($\psi\,0=\Omega_i$) | `z≤` | `Ω-⊑` |
> | 4 (后继) | `s≤` | `add-⊑`, 逐项 |
> | 4 (后继, 只在右边) | `≤s` | 右边取第 1 项, 它定义性地是 $\psi\,b$ |
> | 5ω | `≤l`, `l≤` | 折叠与 ℕ-极限交换 |
> | 5Ω (穿透), 两边都穿透 | `i≤` | 两侧搬运 `tr⁻²`; 输出结点的单调性字段由输入结点的单调性字段折叠得到 |
> | 6 (链), 两边都走链 | `i≤` | 两条链逐项相关: 起点 `Ω-⊑`, 每步是对分支的一次递归调用 |
> | 派发不一致 | `i≤` | `Level.clash₁`, `clash₂`, 只看层号 |
> | 5Ω 或 6, 只看右边 | `≤i` (左边在右结点的全部分支之下) | 穿透: 输出仍在全部分支之下; 链: 取链的第 0 项 $\Omega_{j'}$ 那一支 |
>
> 规则 6 是提示里说的要点: `ψ-≅` 里两条 γ-链同步, 这里是链点逐项 `⊑ᵖ`. 它成立是因为 `i≤` 的前提正是 "输入相关则分支相关", 链的第 $n+1$ 项是对第 $n$ 项应用分支再折叠. 没有哪一行需要把 `⊑ᵖ` 换回 `≅`, 也没有用到值的同余.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K4MonoFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.K4MonoRel using (module Rel)

module Fold (M : Set) where
  open Rel M public
```

## §1 $\Omega$, 提升, 加法

```agda
  Ω-⊑ : ∀ {a b} → a ≅ᴵ b → Ω a ⊑ᵖ Ω b
  Ω-⊑ z≅     = s≤ z≤
  Ω-⊑ (s≅ e) = i≤ e (λ μ x y d → u≤ (≤u d)) (λ x y d → u≤ (≤u d))
  Ω-⊑ (l≅ h) = lim-⊑ᵖ (λ n → u≤ (≤u (Ω-⊑ (h n))))

  Ω-legal : ∀ ℓ → Ω ℓ ⊑ᵖ Ω ℓ
  Ω-legal ℓ = Ω-⊑ (≅ᴵ-refl ℓ)

  lift-⊑ : ∀ {k ℓ ℓ′} (r : k ◃ ℓ) {x : Ordᶜ k} {b : Ordᶜ ℓ′} → x ⊑ᵖ b → lift r x ⊑ᵖ b
  lift-⊑ zero      e = u≤ e
  lift-⊑ (suc r)   e = u≤ (lift-⊑ r e)
  lift-⊑ (self n)  e = u≤ e
  lift-⊑ (lim n r) e = u≤ (lift-⊑ r e)

  ⊑-lift : ∀ {k ℓ ℓ′} (r : k ◃ ℓ) {x : Ordᶜ k} {a : Ordᶜ ℓ′} → a ⊑ᵖ x → a ⊑ᵖ lift r x
  ⊑-lift zero      e = ≤u e
  ⊑-lift (suc r)   e = ≤u (⊑-lift r e)
  ⊑-lift (self n)  e = ≤u e
  ⊑-lift (lim n r) e = ≤u (⊑-lift r e)
```

加法对两个参数单调. `i≤` 情形: 输出结点的单调性字段要 $a+f\,x\sqsubseteq a+f\,y$, 用到 $a\sqsubseteq a$ (`⊑ᵖ-reflˡ`, 在 `M` 之下可用).

```agda
  add-⊑ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordᶜ ℓ₁} {a′ : Ordᶜ ℓ₂} {b : Ordᶜ k₁} {b′ : Ordᶜ k₂} →
          a ⊑ᵖ a′ → b ⊑ᵖ b′ → add a σ b ⊑ᵖ add a′ σ′ b′
  add-⊑ ea z≤       = ea
  add-⊑ ea (s≤ e)   = s≤ (add-⊑ ea e)
  add-⊑ ea (≤s e)   = ≤s (add-⊑ ea e)
  add-⊑ ea (≤l n e) = ≤l n (add-⊑ ea e)
  add-⊑ ea (l≤ h)   = l≤ (λ n → add-⊑ ea (h n))
  add-⊑ {σ′ = σ′} ea (≤i {q = q′} h) = ≤i (λ y → add-⊑ ea (h (coe (<→◃ (σ′ q′)) (<→◃ q′) y)))
  add-⊑ ea (u≤ {r = zero} e)   = add-⊑ ea e
  add-⊑ ea (u≤ {r = self n} e) = add-⊑ ea e
  add-⊑ ea (≤u {r = zero} e)   = add-⊑ ea e
  add-⊑ ea (≤u {r = self n} e) = add-⊑ ea e
  add-⊑ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} ea (i≤ {p = q} {q = q′} {f = f} {g = g} e m h) =
    i≤ e
       (λ μ x y d →
          subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ⊑ᵖ add a σ (f (into (<→◃ q) v)))
                 (sym (out-into (<→◃ (σ q)) x)) (sym (out-into (<→◃ (σ q)) y))
                 (add-⊑ (⊑ᵖ-reflˡ μ ea) (m μ x y (Rᵖ-conv (<→◃ (σ q)) (<→◃ q) d))))
       (λ x y d →
          subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ⊑ᵖ add a′ σ′ (g (into (<→◃ q′) v)))
                 (sym (out-into (<→◃ (σ q)) x)) (sym (out-into (<→◃ (σ′ q′)) y))
                 (add-⊑ ea (h x y (Rᵖ-conv (<→◃ (σ q)) (<→◃ q) d))))
```

右加不减 (`⊑-addʳ`), 左加不减 (`⊑-addˡ`), 对一切层. 两条都用到 "在全部分支之下" 的规则 `≤i`: 右边的和是 Ω-结点时, 左边在它的每一支之下.

```agda
  ⊑-addʳ : ∀ {k ℓ ℓ₀} {σ : Simᴵ k ℓ} {a : Ordᶜ ℓ₀} {a′ : Ordᶜ ℓ} → a ⊑ᵖ a′ → (b : Ordᶜ k) → a ⊑ᵖ add a′ σ b
  ⊑-addʳ ea zero            = ea
  ⊑-addʳ ea (suc b)         = ≤s (⊑-addʳ ea b)
  ⊑-addʳ ea (lim f)         = ≤l 0 (⊑-addʳ ea (f 0))
  ⊑-addʳ {σ = σ} ea (limᵢ q g) = ≤i (λ y → ⊑-addʳ ea (g (coe (<→◃ (σ q)) (<→◃ q) y)))
  ⊑-addʳ ea (up zero x)     = ⊑-addʳ ea x
  ⊑-addʳ ea (up (self n) x) = ⊑-addʳ ea x

  ⊑-addˡ : ∀ {k₁ k₂ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} (a′ : Ordᶜ ℓ₂) {b : Ordᶜ k₁} {b′ : Ordᶜ k₂} → b ⊑ᵖ b′ → b ⊑ᵖ add a′ σ′ b′
  ⊑-addˡ a′ z≤       = zero⊑ a′
  ⊑-addˡ a′ (s≤ e)   = s≤ (⊑-addˡ a′ e)
  ⊑-addˡ a′ (≤s e)   = ≤s (⊑-addˡ a′ e)
  ⊑-addˡ a′ (≤l n e) = ≤l n (⊑-addˡ a′ e)
  ⊑-addˡ a′ (l≤ h)   = l≤ (λ n → ⊑-addˡ a′ (h n))
  ⊑-addˡ {σ′ = σ′} a′ (i≤ {p = q} {q = q′} {f = f} {g = g} e m h) =
    i≤ e m λ x y d →
      subst (λ v → f (into (<→◃ q) x) ⊑ᵖ add a′ σ′ (g (into (<→◃ q′) v)))
            (sym (out-into (<→◃ (σ′ q′)) y))
            (⊑-addˡ a′ (h x y d))
  ⊑-addˡ {σ′ = σ′} a′ (≤i {q = q′} h) = ≤i (λ y → ⊑-addˡ a′ (h (coe (<→◃ (σ′ q′)) (<→◃ q′) y)))
  ⊑-addˡ a′ (u≤ {r = zero} e)   = u≤ (⊑-addˡ a′ e)
  ⊑-addˡ a′ (u≤ {r = self n} e) = u≤ (⊑-addˡ a′ e)
  ⊑-addˡ a′ (≤u {r = zero} e)   = ⊑-addˡ a′ e
  ⊑-addˡ a′ (≤u {r = self n} e) = ⊑-addˡ a′ e
```

## §2 折叠

```agda
  ψ-⊑ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
        {a : Ordᶜ k₁} {b : Ordᶜ k₂} → i ≅ᴵ i′ → a ⊑ᵖ b → ψ p σ a ⊑ᵖ ψ p′ σ′ b
  ψ-⊑ ei z≤       = Ω-⊑ ei
  ψ-⊑ ei (s≤ e)   = lim-⊑ᵖ (iter-R _⊑ᵖ_ (λ e′ → add-⊑ (ψ-⊑ ei e) e′) z≤)
  ψ-⊑ ei (≤s e)   = ≤l 1 (ψ-⊑ ei e)
  ψ-⊑ ei (≤l n e) = ≤l n (ψ-⊑ ei e)
  ψ-⊑ ei (l≤ h)   = l≤ (λ n → ψ-⊑ ei (h n))
  ψ-⊑ ei (u≤ {r = zero} e)   = ψ-⊑ ei e
  ψ-⊑ ei (u≤ {r = self n} e) = ψ-⊑ ei e
  ψ-⊑ ei (≤u {r = zero} e)   = ψ-⊑ ei e
  ψ-⊑ ei (≤u {r = self n} e) = ψ-⊑ ei e
  ψ-⊑ {p′ = p′} {σ′ = σ′} ei (≤i {j′ = j′} {q = q′} h) with <ᴵ-dec (σ′ q′) p′
  ... | injᵃ (via e₂ r₂) = ≤i (λ y → ψ-⊑ ei (h (into (<→◃ q′) (tr⁻ e₂ (out (<→◃ r₂) y)))))
  ... | injᵇ _ = ≤l 0 (ψ-⊑ ei (h (into (<→◃ q′) (Ω j′))))
  ... | injᶜ _ = ≤l 0 (ψ-⊑ ei (h (into (<→◃ q′) (Ω j′))))
  ψ-⊑ {i = i} {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} ei (i≤ {p = q} {q = q′} {f = f} {g = g} e m h)
    with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
  ... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) =
    i≤ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂))
       (λ μ x y d →
          subst₂ (λ u v → ψ p σ (f (into (<→◃ q) (tr⁻ e₁ u))) ⊑ᵖ ψ p σ (f (into (<→◃ q) (tr⁻ e₁ v))))
                 (sym (out-into (<→◃ r₁) x)) (sym (out-into (<→◃ r₁) y))
                 (ψ-⊑ (≅ᴵ-refl i) (m μ _ _ (⊑→R (<→◃ q) (tr⁻² e₁ e₁ (R→⊑ (<→◃ r₁) d))))))
       (λ x y d →
          subst₂ (λ u v → ψ p σ (f (into (<→◃ q) (tr⁻ e₁ u))) ⊑ᵖ ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v))))
                 (sym (out-into (<→◃ r₁) x)) (sym (out-into (<→◃ r₂) y))
                 (ψ-⊑ ei (h _ _ (⊑→R (<→◃ q) (tr⁻² e₁ e₂ (R→⊑ (<→◃ r₁) d))))))
  ... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
  ... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
  ... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
  ... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
  ... | injᵇ _ | injᵇ _  = lim-⊑ᵖ (λ n → ψ-⊑ ei (h _ _ (⊑→R (<→◃ q) (chain n))))
    where chain = iter-R _⊑ᵖ_ (λ d → ψ-⊑ e (h _ _ (⊑→R (<→◃ q) d))) (Ω-⊑ e)
  ... | injᵇ _ | injᶜ _  = lim-⊑ᵖ (λ n → ψ-⊑ ei (h _ _ (⊑→R (<→◃ q) (chain n))))
    where chain = iter-R _⊑ᵖ_ (λ d → ψ-⊑ e (h _ _ (⊑→R (<→◃ q) d))) (Ω-⊑ e)
  ... | injᶜ _ | injᵇ _  = lim-⊑ᵖ (λ n → ψ-⊑ ei (h _ _ (⊑→R (<→◃ q) (chain n))))
    where chain = iter-R _⊑ᵖ_ (λ d → ψ-⊑ e (h _ _ (⊑→R (<→◃ q) d))) (Ω-⊑ e)
  ... | injᶜ _ | injᶜ _  = lim-⊑ᵖ (λ n → ψ-⊑ ei (h _ _ (⊑→R (<→◃ q) (chain n))))
    where chain = iter-R _⊑ᵖ_ (λ d → ψ-⊑ e (h _ _ (⊑→R (<→◃ q) d))) (Ω-⊑ e)
```

目标层 0 的无证明折叠 `ψ⁰` (没有穿透). 这是值验收实际使用的形式.

```agda
  ψ⁰-⊑ : ∀ {k₁ k₂} {a : Ordᶜ k₁} {b : Ordᶜ k₂} → a ⊑ᵖ b → ψ⁰ a ⊑ᵖ ψ⁰ b
  ψ⁰-⊑ z≤       = s≤ z≤
  ψ⁰-⊑ (s≤ e)   = lim-⊑ᵖ (iter-R _⊑ᵖ_ (λ e′ → add-⊑ (ψ⁰-⊑ e) e′) z≤)
  ψ⁰-⊑ (≤s e)   = ≤l 1 (ψ⁰-⊑ e)
  ψ⁰-⊑ (≤l n e) = ≤l n (ψ⁰-⊑ e)
  ψ⁰-⊑ (l≤ h)   = l≤ (λ n → ψ⁰-⊑ (h n))
  ψ⁰-⊑ (u≤ {r = zero} e)   = ψ⁰-⊑ e
  ψ⁰-⊑ (u≤ {r = self n} e) = ψ⁰-⊑ e
  ψ⁰-⊑ (≤u {r = zero} e)   = ψ⁰-⊑ e
  ψ⁰-⊑ (≤u {r = self n} e) = ψ⁰-⊑ e
  ψ⁰-⊑ (≤i {j′ = j′} {q = q′} h) = ≤l 0 (ψ⁰-⊑ (h (into (<→◃ q′) (Ω j′))))
  ψ⁰-⊑ (i≤ {p = q} e m h) = lim-⊑ᵖ (λ n → ψ⁰-⊑ (h _ _ (⊑→R (<→◃ q) (chain n))))
    where chain = iter-R _⊑ᵖ_ (λ d → ψ-⊑ e (h _ _ (⊑→R (<→◃ q) d))) (Ω-⊑ e)
```

## §3 合法的树对运算封闭

$a$ 合法指 $a\sqsubseteq a$. 第 0 层的树都合法 (`K4MonoRel.⊑ᵖ-refl⁰`); $\Omega_\ell$ 合法 (`Ω-legal`); 后继, ℕ-极限, 提升, 加法, 折叠保持合法. 都是上面各条取两边相同的实例, 写出来备查.

```agda
  suc-legal : ∀ {ℓ} {a : Ordᶜ ℓ} → a ⊑ᵖ a → suc a ⊑ᵖ suc a
  suc-legal = s≤

  lim-legal : ∀ {ℓ} {f : ℕ → Ordᶜ ℓ} → (∀ n → f n ⊑ᵖ f n) → lim f ⊑ᵖ lim f
  lim-legal = lim-⊑ᵖ

  lift-legal : ∀ {k ℓ} (r : k ◃ ℓ) {x : Ordᶜ k} → x ⊑ᵖ x → lift r x ⊑ᵖ lift r x
  lift-legal r e = lift-⊑ r (⊑-lift r e)

  add-legal : ∀ {k ℓ} {σ : Simᴵ k ℓ} {a : Ordᶜ ℓ} {b : Ordᶜ k} → a ⊑ᵖ a → b ⊑ᵖ b → add a σ b ⊑ᵖ add a σ b
  add-legal = add-⊑

  ψ-legal : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {a : Ordᶜ k} → a ⊑ᵖ a → ψ p σ a ⊑ᵖ ψ p σ a
  ψ-legal {i = i} = ψ-⊑ (≅ᴵ-refl i)

  ψ⁰-legal : ∀ {k} {a : Ordᶜ k} → a ⊑ᵖ a → ψ⁰ a ⊑ᵖ ψ⁰ a
  ψ⁰-legal = ψ⁰-⊑
```

**小结.** `ψ-⊑` 对一切层成立, 一条证明. 关系的两个版本都适用.
