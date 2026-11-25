# 保留结点重编号的首分支与值
> 编译定理，无经典前提。非零后继目标不能同时要求换号保零且每个孩子都有目标路径。
> 保零的尾部平移在第 1 层的标准 Ω 树上保值，在另一棵同槽位的合法树上严格丢失一个分支值。入口为 `canonical-same` 与 `peak-lost`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLAReindex where

open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (Pth)
import OCF.Lean.YiVWVal as V

h : Tr zero → L
h c = zero ⊕ ↑ zero c

no-root-path : ∀ {b s f} → Pth b (nd s f) zero → ⊥
no-root-path ()

no-based-path : ∀ {b} (r : Tr zero) (ρ : Tr zero → Tr zero) → ρ zero ≡ zero
              → ((c : Tr zero) → Pth b (h (suc r)) (h (ρ c))) → ⊥
no-based-path {b} r ρ base paths =
  no-root-path (subst (λ z → Pth b (h (suc r)) (h z)) base (paths zero))

shift : Tr zero → Tr zero → Tr zero
shift r zero      = zero
shift r (suc c)   = suc (r + c)
shift r (lim f a) = r + lim f a

shift-first : (r : Tr zero) → shift r zero ≡ zero
shift-first r = refl

module At {ℓ : L} (p : Pos ℓ) (G : Br ℓ p → Tr ℓ) (ρ : Br ℓ p → Br ℓ p) where
  cover : ((z : Br ℓ p) → Σ (Br ℓ p) λ w → V.val ℓ (G z) V.≼ V.val ℓ (G (ρ w)))
        → V.val ℓ (Ω p G) V.≈ V.val ℓ (Ω p (λ w → G (ρ w)))
  cover dom = V.Ω≼ (λ z → hit (dom z)) , V.Ω≼ (λ w → V.≼Ω (ρ w) (V.≼-refl _))
    where
    hit : ∀ {v} → (Σ (Br ℓ p) λ w → v V.≼ V.val ℓ (G (ρ w))) → v V.≼ V.val ℓ (Ω p (λ w → G (ρ w)))
    hit (w , d) = V.≼Ω w d

one : L
one = nd sS (λ _ → zero)

slot : Pos one
slot = inj₂ (tt , inj₁ tt)

left-add : (r c : Tr zero) → V.val zero c V.≼ V.val zero (r + c)
left-add r zero      = V.z≼
left-add r (suc c)   = V.s≼s (left-add r c)
left-add r (lim f a) = V.l≼ (λ n → V.≼l n (left-add r (f n)))

shift-dom : (r c : Tr zero) → V.val zero c V.≼ V.val zero (shift r c)
shift-dom r zero      = V.z≼
shift-dom r (suc c)   = V.s≼s (left-add r c)
shift-dom r (lim f a) = left-add r (lim f a)

branch : Tr zero → Tr one
branch c = proj₁ (upz {s = sS} {h = λ _ → zero} tt (suc c , z◃ c ◃s))

canonical-same : (r : Tr zero) → V.val one (proj₁ (Ωt one)) V.≈ V.val one (Ω slot (λ c → branch (shift r c)))
canonical-same r = At.cover slot branch (shift r) (λ c →
  c , V.⊹-mono V.zero (V.emb-mono one tt (V.s≼s (shift-dom r c))))

two : Tr zero
two = suc (suc zero)

peak : Tr zero → Tr one
peak (suc zero) = suc (suc zero)
peak _          = suc zero

peak-positive : (c : Tr zero) → one ⊢ zero ◃ peak c
peak-positive (suc zero)      = ◃t ◃s ◃s
peak-positive (suc (suc c))   = ◃s
peak-positive (suc (lim f a)) = ◃s
peak-positive zero            = ◃s
peak-positive (lim f a)       = ◃s

tail-flat : (c : Tr zero) → peak (suc (two + c)) ≡ suc zero
tail-flat zero      = refl
tail-flat (suc c)   = refl
tail-flat (lim f a) = refl

shift-flat : (c : Tr zero) → peak (shift two c) ≡ suc zero
shift-flat zero      = refl
shift-flat (suc c)   = tail-flat c
shift-flat (lim f a) = refl

peak-lost : V.val one (Ω slot peak) V.≼ V.val one (Ω slot (λ c → peak (shift two c))) → ⊥
peak-lost d = absurd (V.≼-trans (V.Ω⁻ (suc zero) d) (V.Ω≼ bound))
  where
  bound : ∀ c → V.val one (peak (shift two c)) V.≼ V.suc {one} V.zero
  bound c rewrite shift-flat c = V.s≼s V.z≼
  absurd : V.suc {one} (V.suc V.zero) V.≼ V.suc {one} V.zero → ⊥
  absurd (V.s≼s ())
```
