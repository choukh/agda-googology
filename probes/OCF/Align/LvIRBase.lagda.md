# 归纳-递归块的底座: 第 0 层的折叠 $P_0$ 单调且保持 `HS`

> 不含记号. 结论写在 [LvIR](LvIR.lagda.md). 只导入标准库与 [EBOTopStage](EBOTopStage.lagda.md). 这里的定理对**一切**第 0 层的树成立, 不要 `HS` 的前提 (`P₀-mono`), 块里的闭包定理用它们.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvIRBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Align.EBOTopStage public using
  (O₀; _≅⁰_; _≺⁰_; _⊑⁰_; HS; hz; hs; hl; ≺z; ≺s; ≺l; z≅; s≅; l≅; ≅⁰-refl; ≅⁰-sym; ≅⁰-trans; ≺⁰-respʳ; ≺⁰-respˡ; ≺⁰-irrefl)
```

## §1 第 0 层的加法与 $P_0$

```agda
iterᴼ : (O₀ → O₀) → ℕ → O₀
iterᴼ f zero    = O₀.zero
iterᴼ f (suc n) = f (iterᴼ f n)

_⊕_ : O₀ → O₀ → O₀
a ⊕ O₀.zero  = a
a ⊕ O₀.suc b = O₀.suc (a ⊕ b)
a ⊕ O₀.lim f = O₀.lim (λ n → a ⊕ f n)

⊕-cong : ∀ {a a′ b b′} → a ≅⁰ a′ → b ≅⁰ b′ → (a ⊕ b) ≅⁰ (a′ ⊕ b′)
⊕-cong ea z≅     = ea
⊕-cong ea (s≅ e) = s≅ (⊕-cong ea e)
⊕-cong ea (l≅ h) = l≅ (λ n → ⊕-cong ea (h n))

P₀ : O₀ → O₀
P₀ O₀.zero    = O₀.suc O₀.zero
P₀ (O₀.suc a) = O₀.lim (iterᴼ (P₀ a ⊕_))
P₀ (O₀.lim f) = O₀.lim (λ n → P₀ (f n))

iter-cong : ∀ {a a′} → a ≅⁰ a′ → ∀ n → iterᴼ (a ⊕_) n ≅⁰ iterᴼ (a′ ⊕_) n
iter-cong e zero    = z≅
iter-cong e (suc n) = ⊕-cong e (iter-cong e n)

P₀-cong : ∀ {a b} → a ≅⁰ b → P₀ a ≅⁰ P₀ b
P₀-cong z≅     = s≅ z≅
P₀-cong (s≅ e) = l≅ (iter-cong (P₀-cong e))
P₀-cong (l≅ h) = l≅ (λ n → P₀-cong (h n))
```

## §2 单调

`⊕-r`: 右边单调. `⊕-mid`: 左边的前驱. `P₀-mono` 对 `≺⁰` 的推导归纳, 不要 `HS`. $P_0(a+1)$ 的第 1 项就是 $P_0(a)$.

```agda
⊕-r : ∀ a {b b′} → b ⊑⁰ b′ → (a ⊕ b) ⊑⁰ (a ⊕ b′)
⊕-rs : ∀ a {c b′} → c ≺⁰ b′ → (a ⊕ c) ≺⁰ (a ⊕ b′)
⊕-rs a (≺z e)   = ≺z (⊕-cong (≅⁰-refl a) e)
⊕-rs a (≺s q)   = ≺s (⊕-rs a q)
⊕-rs a (≺l n q) = ≺l n (⊕-rs a q)

-- a 的前驱也是 a ⊕ b 的前驱
⊕-l : ∀ a b {c} → c ≺⁰ a → c ≺⁰ (a ⊕ b)
⊕-l a O₀.zero    q = q
⊕-l a (O₀.suc b) q = ≺s (⊕-l a b q)
⊕-l a (O₀.lim f) q = ≺l 0 (⊕-l a (f 0) q)

⊕-r a {O₀.zero}   σ q = ⊕-z a σ q where
  ⊕-z : ∀ a {b′} → O₀.zero ⊑⁰ b′ → ∀ {c} → c ≺⁰ a → c ≺⁰ (a ⊕ b′)
  ⊕-z a {b′} _ q = ⊕-l a b′ q
⊕-r a {O₀.suc b}  σ (≺z e)   = ≺⁰-respˡ (≅⁰-trans (≅⁰-sym e) (≅⁰-refl _)) (⊕-rs a (σ (≺z (≅⁰-refl b))))
⊕-r a {O₀.suc b}  σ (≺s q)   = ⊕-r a (λ q′ → σ (≺s q′)) q
⊕-r a {O₀.lim f}  σ (≺l n q) = ⊕-r a (λ q′ → σ (≺l n q′)) q

-- 第 1 项
P₀-term : ∀ a {c} → c ≺⁰ P₀ a → c ≺⁰ P₀ (O₀.suc a)
P₀-term a q = ≺l 1 q

P₀-≺ : ∀ {a b} → a ≺⁰ b → P₀ (O₀.suc a) ⊑⁰ P₀ b
P₀-≺ {a} (≺z (e)) q = ≺⁰-respʳ q (l≅ (iter-cong (P₀-cong e)))
P₀-≺ (≺s p) q = P₀-term _ (P₀-≺ p q)
P₀-≺ (≺l n p) q = ≺l n (P₀-≺ p q)

P₀-zero : ∀ b → O₀.zero ≺⁰ P₀ b
P₀-zero O₀.zero    = ≺z z≅
P₀-zero (O₀.suc a) = ≺l 1 (P₀-zero a)
P₀-zero (O₀.lim f) = ≺l 0 (P₀-zero (f 0))

P₀-mono : ∀ a {b} → a ⊑⁰ b → P₀ a ⊑⁰ P₀ b
P₀-mono O₀.zero    {b} σ (≺z z≅) = P₀-zero b
P₀-mono O₀.zero    σ (≺s ())
P₀-mono (O₀.suc a) σ q = P₀-≺ (σ (≺z (≅⁰-refl a))) q
P₀-mono (O₀.lim f) σ (≺l n q) = P₀-mono (f n) (λ q′ → σ (≺l n q′)) q
```

## §3 `HS`

```agda
⊕-HS : ∀ {a b} → HS a → HS b → HS (a ⊕ b)
⊕-HS ha hz          = ha
⊕-HS ha (hs hb)     = hs (⊕-HS ha hb)
⊕-HS {a} ha (hl h st) = hl (λ n → ⊕-HS ha (h n)) (λ n → ⊕-r a (st n))

iter-HS : ∀ {p} → HS p → ∀ n → HS (iterᴼ (p ⊕_) n)
iter-HS hp zero    = hz
iter-HS hp (suc n) = ⊕-HS hp (iter-HS hp n)

iter-step : ∀ p n → iterᴼ (p ⊕_) n ⊑⁰ iterᴼ (p ⊕_) (suc n)
iter-step p zero    ()
iter-step p (suc n) = ⊕-r p (iter-step p n)

P₀-HS : ∀ {y} → HS y → HS (P₀ y)
P₀-HS hz          = hs hz
P₀-HS (hs h)      = hl (iter-HS (P₀-HS h)) (iter-step _)
P₀-HS {O₀.lim f} (hl h st) = hl (λ n → P₀-HS (h n)) (λ n → P₀-mono (f n) (st n))
```

`HS` 只看 $\cong^0$ 类.

```agda
HS-resp : ∀ {a b} → a ≅⁰ b → HS a → HS b
HS-resp z≅     hz        = hz
HS-resp (s≅ e) (hs h)    = hs (HS-resp e h)
HS-resp (l≅ k) (hl h st) = hl (λ n → HS-resp (k n) (h n))
  (λ n q → ≺⁰-respʳ (st n (≺⁰-respʳ q (≅⁰-sym (k n)))) (k (suc n)))

⊑⁰-resp : ∀ {a a′ b b′} → a ≅⁰ a′ → b ≅⁰ b′ → a ⊑⁰ b → a′ ⊑⁰ b′
⊑⁰-resp ea eb σ q = ≺⁰-respʳ (σ (≺⁰-respʳ q (≅⁰-sym ea))) eb
```
