# YiKB 读回: 第 0 层树到参照框架

> 验收用 (导入 `OCF.Align.Level`, `OCF.Align.Value`; 不进块与折叠). `read` 逐构造子把 `T z` 读成 `L.Ordᶜ L.zero`; 第 0 层没有分支与叶.
> 编译定理: 结构序读成值序 (`≼ᵗ→≼`); 第 0 层上 `E` 对两个参数单调 (`E-mono`); 塔的每一项不高于 Λ 的闭项 (`into`); 嵌入再坍缩不降值 (`emb-read`).
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKBRead where

open import Data.Nat using (ℕ; zero; suc)

open import OCF.Lean.YiKBBlock
open import OCF.Lean.YiKBFold
open import OCF.Lean.YiKBProps as P using (_≼ᵗ_; rfl; inflE)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans)
```

```agda
read : T₀ → L.Ordᶜ L.zero
read zero    = L.zero
read (suc t) = L.suc (read t)
read (lim f) = L.lim (λ n → read (f n))

≼ᵗ→≼ : ∀ {a b : T₀} → a ≼ᵗ b → read a ≼ read b
≼ᵗ→≼ P.z≼       = z≼
≼ᵗ→≼ (P.s≼s p)  = s≼s (≼ᵗ→≼ p)
≼ᵗ→≼ (P.≼l n p) = ≼l n (≼ᵗ→≼ p)
≼ᵗ→≼ (P.l≼ p)   = l≼ (λ n → ≼ᵗ→≼ (p n))
```

## 第 0 层上 `E` 单调

第 0 层没有对角, `E acc t = acc + ω^t` 对两个参数都单调. 高层上对 `t` 的单调性没有证.

```agda
infl′ : ∀ {a a′ : T₀} (t : T₀) → a ≼ᵗ a′ → suc a ≼ᵗ E rf′ a′ t
infl′ zero    p = P.s≼s p
infl′ (suc t) p = P.≼l 1 (infl′ t p)
infl′ (lim f) p = P.≼l 0 (infl′ (f 0) p)

E-mono : ∀ {a a′ t t′ : T₀} → a ≼ᵗ a′ → t ≼ᵗ t′ → E rf′ a t ≼ᵗ E rf′ a′ t′
E-mono {t′ = t′} p P.z≼ = infl′ t′ p
E-mono {a = a} {a′ = a′} p (P.s≼s {a = t} {b = t′} q) = P.l≼ (λ n → P.≼l n (it n))
  where
  it : ∀ n → iter (λ r → E rf′ r t) n a ≼ᵗ iter (λ r → E rf′ r t′) n a′
  it zero    = p
  it (suc n) = E-mono (it n) q
E-mono p (P.≼l n q) = P.≼l n (E-mono p q)
E-mono p (P.l≼ q)   = P.l≼ (λ n → E-mono p (q n))
```

## 塔在 Λ 之下, 嵌入一致

`EBOᶜ` 的第 n 项是 `join (suc (Ωtop z)) (twᶜ n)`.

```agda
into : ∀ n → read (twᶜ n) ≼ read EBOᶜ
into n = ≼l n (≼l 1 (≼-refl (read (twᶜ n))))

emb-read : ∀ (acc t : T₀) → read t ≼ read (step (s z) acc (lf t))
emb-read acc zero    = z≼
emb-read acc (suc t) = ≼l 2 (≼-trans (s≼s (emb-read acc t)) (≼ᵗ→≼ (inflE rf′ (E rf′ acc t) t)))
emb-read acc (lim f) = l≼ (λ n → ≼l n (emb-read acc (f n)))
```
