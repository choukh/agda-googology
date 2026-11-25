# 合法块: 第 1 层的 Ω 树基底单调

> 判决: 成品候选. 编译定理, 无前提: 第 0 层的折叠对参数按值单调, 同时对底与起点单调 (`am⊥`, `ams`: 两棵参数树只按值比较); 由此第 1 层 (`suc zero`) 的 Ω 树基底单调 (`bm-one : BM⊥ one (Ωt one)`), 即 `YiLPMono.BM⊥` 在第 0 层以上的规范树上有实例.
> 证法是 `YiLPMono.bm-Nx` 的同一条链: 两条回灌链逐项按值比较. 第 1 层每个分支的孩子层都是第 0 层, 不随坐标变; 塔第 1 项的分支孩子层 0 ⊕ ↑c 随坐标 c 变, 这一步不在本文 (见 `YiLPInto` 的 `chain-B₁`).
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPBMOne where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLPVal hiding (emb; emb-mono)
open import OCF.Lean.YiLPMono using (next≼; limc≼; _⊴_; BM⊥)
```

## 折叠不低于底的分量与起点

```agda
base≼⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (x : Tr ℓ) → val zero (b⊥ B) ≼ val zero (ψ⊥ ℓ ε ρ B x)
base≼⊥ ℓ ε ρ B x with zl x
... | inj₁ refl = ≼-refl _
... | inj₂ d    = ◁→≼ (val-mono zero (mono⊥ ℓ ε ρ B d))

start≼s : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
        → val j β ≼ val j (ψs ℓ ε ρ B j w β nβ x)
start≼s ℓ ε ρ B j w β nβ x with zl x
... | inj₁ refl = ≼-refl _
... | inj₂ d    = ◁→≼ (val-mono j (monos ℓ ε ρ B j w β nβ d))
```

## 第 0 层: 对参数按值单调

两棵参数树 c, c′ 只按值比较 (`val zero c ≼ val zero c′`), 沿这个推导递归.

```agda
am⊥ : (B B′ : Base zero) → B ⊴ B′ → (c c′ : Tr zero) → val zero c ≼ val zero c′
    → val zero (ψ⊥ zero tt tt B c) ≼ val zero (ψ⊥ zero tt tt B′ c′)
am⊥ B B′ hB zero          c′          d         = ≼-trans (proj₁ hB) (base≼⊥ zero tt tt B′ c′)
am⊥ B B′ hB (suc x)       zero        ()
am⊥ B B′ hB (suc x)       (suc x′)    (s≼s d)   =
  next≼ (nz⊥ zero tt tt B x) (nz⊥ zero tt tt B′ x′) (am⊥ B B′ hB x x′ d)
am⊥ B B′ hB (suc x)       (lim g b)   (≼l n d)  = ≼l n (am⊥ B B′ hB (suc x) (g n) d)
am⊥ B B′ hB (lim f a)     zero        (l≼ h)    = l≼ (λ n → am⊥ B B′ hB (f n) zero (h n))
am⊥ B B′ hB (lim f a)     (suc x′)    (l≼ h)    = l≼ (λ n → am⊥ B B′ hB (f n) (suc x′) (h n))
am⊥ B B′ hB (lim f a)     (lim g b)   (l≼ h)    = l≼ (λ n → am⊥ B B′ hB (f n) (lim g b) (h n))
am⊥ B B′ hB (lim f a)     (lim g b)   (≼l n d)  = ≼l n (am⊥ B B′ hB (lim f a) (g n) d)
am⊥ B B′ hB (Ω () _)      c′          d
am⊥ B B′ hB (up _ () _ _) c′          d
am⊥ B B′ hB c             (Ω () _)    d
am⊥ B B′ hB c             (up _ () _ _) d

ams : (B B′ : Base zero) (β β′ : Tr zero) (nβ : zero ⊢ zero ◃ β) (nβ′ : zero ⊢ zero ◃ β′) → val zero β ≼ val zero β′
    → (c c′ : Tr zero) → val zero c ≼ val zero c′
    → val zero (ψs zero tt tt B zero self β nβ c) ≼ val zero (ψs zero tt tt B′ zero self β′ nβ′ c′)
ams B B′ β β′ nβ nβ′ hβ zero          c′          d         = ≼-trans hβ (start≼s zero tt tt B′ zero self β′ nβ′ c′)
ams B B′ β β′ nβ nβ′ hβ (suc x)       zero        ()
ams B B′ β β′ nβ nβ′ hβ (suc x)       (suc x′)    (s≼s d)   =
  next≼ (nzs zero tt tt B zero self β nβ x) (nzs zero tt tt B′ zero self β′ nβ′ x′) (ams B B′ β β′ nβ nβ′ hβ x x′ d)
ams B B′ β β′ nβ nβ′ hβ (suc x)       (lim g b)   (≼l n d)  = ≼l n (ams B B′ β β′ nβ nβ′ hβ (suc x) (g n) d)
ams B B′ β β′ nβ nβ′ hβ (lim f a)     zero        (l≼ h)    = l≼ (λ n → ams B B′ β β′ nβ nβ′ hβ (f n) zero (h n))
ams B B′ β β′ nβ nβ′ hβ (lim f a)     (suc x′)    (l≼ h)    = l≼ (λ n → ams B B′ β β′ nβ nβ′ hβ (f n) (suc x′) (h n))
ams B B′ β β′ nβ nβ′ hβ (lim f a)     (lim g b)   (l≼ h)    = l≼ (λ n → ams B B′ β β′ nβ nβ′ hβ (f n) (lim g b) (h n))
ams B B′ β β′ nβ nβ′ hβ (lim f a)     (lim g b)   (≼l n d)  = ≼l n (ams B B′ β β′ nβ nβ′ hβ (lim f a) (g n) d)
ams B B′ β β′ nβ nβ′ hβ (Ω () _)      c′          d
ams B B′ β β′ nβ nβ′ hβ (up _ () _ _) c′          d
ams B B′ β β′ nβ nβ′ hβ c             (Ω () _)    d
ams B B′ β β′ nβ nβ′ hβ c             (up _ () _ _) d
```

## 第 1 层的 Ω 树

```agda
one : L
one = suc zero

bm-one : BM⊥ one (Ωt one)
bm-one tt tt B B′ hB = limc≼ (F B) (F B′) (nF B) (nF B′) (λ m → next≼ _ _ (am⊥ (dB B) (dB B′) hd (ch B m) (ch B′ m) (chain m)))
  where
  dB : Base one → Base zero
  dB B = dS zero tt tt B zero
  hd : dB B ⊴ dB B′
  hd = proj₁ hB , λ j w → proj₂ hB j (ins w)
  st : Base one → Tr zero → Tr zero
  st B z = ψs one tt tt B zero (ins self) (bs B zero (ins self)) (ns B zero (ins self)) (up zero tt (suc z) (z◃s z))
  ch : Base one → ℕ → Tr zero
  ch B m = iter (st B) zero m
  chain : (m : ℕ) → val zero (ch B m) ≼ val zero (ch B′ m)
  chain zero    = z≼
  chain (suc m) = ams (dB B) (dB B′) _ _ (ns B zero (ins self)) (ns B′ zero (ins self)) (proj₂ hB zero (ins self))
                      (suc (ch B m)) (suc (ch B′ m)) (s≼s (chain m))
  F : Base one → ℕ → Tr zero
  F B m = ψ⊥ one tt tt B (up zero tt (suc (ch B m)) (z◃s (ch B m)))
  nF : (B : Base one) (m : ℕ) → zero ⊢ zero ◃ F B m
  nF B m = nz⊥ one tt tt B (up zero tt (suc (ch B m)) (z◃s (ch B m)))
```
