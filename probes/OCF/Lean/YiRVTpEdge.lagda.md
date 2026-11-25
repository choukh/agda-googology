# 值支配 `Tp` 的两条边界

> 判决: 编译定理, 无前提. (一) 沿层号的语法路径 `k ≤ ℓ`, `Tr k` 被 `Tr ℓ` 按值支配 (`TpPath`, 嵌入逐步是 `upz`). (二) 去掉合法性 `Ok`, 值支配不成立 (`¬TpNoOk`): 下标层取 `sc zero` 而孩子全为零的层号, 值不超过 `sc zero`, 它的 Ω 结点却能对 `Tr (sc zero)` 全体取上确界.
> 所以 `YiRVOmega.Tp` 的前提 `Ok` 不能去掉; 带 `Ok` 的 `Tp` 是否成立未判, 不否定它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRVTpEdge where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (Ok; _≤_; self; inc; inu; ink; _∙_)
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiVWVal as W
open W using (V; val; _≼_; _⊹_)
open import OCF.Lean.YiRVLevel using (_≼ᴸ_; n≼; z≼; sc)
open import OCF.Lean.YiRVOmega using (_⊙_; ≼s; ≼br; ⊹-mono₂)
```

## 沿路径的值支配

```agda
emb≽ : (ℓ : L) (o : Ok ℓ) {k : L} (v : k ≤ ℓ) (y : Tr⁺ k) → val k (proj₁ y) ≼ val ℓ (proj₁ (P.emb ℓ o v y))
emb≽ ℓ             o self      y = W.≼-refl _
emb≽ (nd s h)      o (inc c v) y = emb≽ (h c) (proj₂ o c) v y ⊙ ≼br c _ _
emb≽ (nd s h)      o (inu vs)  y = emb≽ (h (c₀ s)) (proj₂ o (c₀ s)) (vs (c₀ s)) y ⊙ ≼br (c₀ s) _ _
emb≽ (nd (sΩ k) h) o (ink v)   y = emb≽ (h zero) (proj₂ o zero) (v ∙ proj₂ (proj₁ o) zero) y ⊙ ≼br zero _ _

TpPath : ∀ {a a′} → Ok a′ → a ≤ a′ → (x : Tr a) → Σ (Tr a′) λ x′ → val a x ≼ val a′ x′
TpPath {a} {a′} o v x = proj₁ (P.emb a′ o v (suc x , z◃ x ◃s)) , (≼s _ ⊙ emb≽ a′ o v (suc x , z◃ x ◃s))
```

## 不带 `Ok` 的值支配被否定

`Bg = nd (sΩ (sc zero)) (λ _ → zero)`: 值与 `sc zero` 相同 (`Bg≼`), 不合法 (下标层不 ≤ 孩子). `ι₁` 把 `Tr (sc zero)` 逐构造子搬进 `Tr Bg` (槽位换成孩子 `zero` 处的同型槽位), 值不降.

```agda
one : L
one = sc zero

Bg : L
Bg = nd (sΩ one) (λ _ → zero)

Bg≼ : Bg ≼ᴸ one
Bg≼ = n≼ (λ _ → tt , z≼)

q₀ : Pos Bg
q₀ = inj₂ (zero , inj₁ tt)

mutual
  ι₁ : Tr one → Tr Bg
  ι₁ zero                           = zero
  ι₁ (suc x)                        = suc (ι₁ x)
  ι₁ (lim f a)                      = lim (λ n → ι₁ (f n)) (λ n → ι₁m (a n))
  ι₁ (Ω (inj₂ (tt , inj₁ tt)) g)    = Ω q₀ (λ z → ι₁ (g z))
  ι₁ (up x tt y e)                  = up (ι₁ x) zero y e

  ι₁m : {x y : Tr one} → one ⊢ x ◃ y → Bg ⊢ ι₁ x ◃ ι₁ y
  ι₁m ◃s                               = ◃s
  ι₁m (◃l n)                           = ◃l n
  ι₁m (◃w {p = inj₂ (tt , inj₁ tt)})   = ◃w
  ι₁m (◃u x tt y e)                    = ◃u (ι₁ x) zero y e
  ι₁m (◃c x tt d)                      = ◃c (ι₁ x) zero d
  ι₁m (◃t d e)                         = ◃t (ι₁m d) (ι₁m e)

ι₁≽ : (x : Tr one) → val one x ≼ val Bg (ι₁ x)
ι₁≽ zero                        = W.z≼
ι₁≽ (suc x)                     = W.s≼s (ι₁≽ x)
ι₁≽ (lim f a)                   = W.l≼ (λ n → W.≼l n (ι₁≽ (f n)))
ι₁≽ (Ω (inj₂ (tt , inj₁ tt)) g) = W.Ω≼ (λ z → W.≼Ω z (ι₁≽ (g z)))
ι₁≽ (up x tt y e)               =
  ⊹-mono₂ (ι₁≽ x) (W.emb-≼ one tt (val zero y) ⊙ W.≼-emb Bg zero (val zero y))

¬s≼ : ∀ {ℓ} (v : V ℓ) → W.suc v ≼ v → ⊥
¬s≼ W.zero    ()
¬s≼ (W.suc v) (W.s≼s d) = ¬s≼ v d
¬s≼ (W.lim f) (W.≼l n d) = ¬s≼ (f n) (W.s≼s (W.≼l n (W.≼-refl (f n))) ⊙ d)
¬s≼ (W.Ω p g) (W.≼Ω z d) = ¬s≼ (g z) (W.s≼s (W.≼Ω z (W.≼-refl (g z))) ⊙ d)

TpNoOk : Set
TpNoOk = ∀ {a a′} → a ≼ᴸ a′ → (x : Tr a) → Σ (Tr a′) λ x′ → val a x ≼ val a′ x′

¬TpNoOk : TpNoOk → ⊥
¬TpNoOk tp with tp Bg≼ (Ω (inj₁ (inj₁ tt)) ι₁)
... | x′ , e = ¬s≼ (val one x′) (ι₁≽ (suc x′) ⊙ W.≼Ω (suc x′) (W.≼-refl _) ⊙ e)
```
