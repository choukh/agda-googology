# 抽象理论 (六): 终点出口是通用出口的实例

> 验收文件 (读记号). 判决: 编译定理, 无前提. `OCF.Align.Value` 的 `≼` 在第 0 层是 `YiAbsSim.Val` 的实例 (`𝕍`); EBO 参照的 (`cof`, `pred`, `fsn`) 是 `Exit` 的参照系统; `YiMonoExit.exit` 与 `ebo-lower` 由通用的 `exit` 重推 (`exit′`, `ebo-lower′`).
> 所以 `YiAbsSim.Exit.Sim.lower` 的结论可以直接接终点: 给出对应 R 与两种步, 就有 `toL (tree h) ≼ v (ψ x)` (`lower′`).
> 不给出什么: 没有构造任何 R; 这一篇只说明抽象出口没有丢掉终点要的东西.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsSimInst where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.EboLeanDef using (T; HC; h0; h1; hω; cof; c0; c1; cω; pred; fsn; EBOψ)
open import OCF.Align.EboLeanTree using (tree; hc-tower; EBO-tree′)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-trans; ≼-refl; ≼-suc)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiAbsSim

𝕍 : Val
𝕍 = record
  { V = L.Ordᶜ L.zero ; _≼_ = λ a b → a ≼ b ; ≼-refl = ≼-refl _ ; ≼-trans = ≼-trans
  ; vz = L.zero ; vs = L.suc ; vl = L.lim
  ; z≼ = z≼ ; s≼s = s≼s ; l≼ = l≼ ; ≼s = ≼-suc (≼-refl _) }

module E = Exit 𝕍 {T = T} (λ t → cof t ≡ c0) (λ t → cof t ≡ c1) (λ t → cof t ≡ cω) pred fsn

conv : ∀ {t} → HC t → E.HC t
conv (h0 e)   = E.h0 e
conv (h1 e h) = E.h1 e (conv h)
conv (hω e h) = E.hω e (λ n → conv (h n))

toL-tree : ∀ {t} (h : HC t) → toL (tree h) ≼ E.tree (conv h)
toL-tree (h0 e)   = z≼
toL-tree (h1 e h) = s≼s (toL-tree h)
toL-tree (hω e h) = l≼ (λ n → ≼l n (toL-tree (h n)))

exit′ : ∀ {P} → E.Closed P → ∀ {t X} → P t X → (h : HC t) → toL (tree h) ≼ X
exit′ C p h = ≼-trans (toL-tree h) (E.exit C p (conv h))

ebo-lower′ : ∀ {P} → E.Closed P → (Y : L.Ordᶜ L.zero) →
  (∀ k → Σ (L.Ordᶜ L.zero) λ X → P (EBOψ k) X × (X ≼ Y)) → toL EBO-tree′ ≼ Y
ebo-lower′ C Y tw = l≼ (λ k →
  ≼-trans (exit′ C (proj₁ (proj₂ (tw k))) (hc-tower k)) (proj₂ (proj₂ (tw k))))
```

接上 `Sim`: 源层的对应与两种步给出参照树的下界.

```agda
module _ {S₁ S₀ : Set} (v : S₀ → L.Ordᶜ L.zero) (ψ : S₁ → S₀) (G : S₁ → Set)
    (_⇝ˢ_ _⇝_ : S₁ → S₁ → Set)
    (strict : ∀ {x y} → G y → x ⇝ˢ y → L.suc (v (ψ x)) ≼ v (ψ y))
    (weak   : ∀ {x y} → G y → x ⇝ y → v (ψ x) ≼ v (ψ y))
    (R : T → S₁ → Set)
    (r1 : ∀ {t x} → R t x → G x → cof t ≡ c1 → Σ S₁ λ x′ → R (pred t) x′ × G x′ × (x′ ⇝ˢ x))
    (rω : ∀ {t x} → R t x → G x → cof t ≡ cω → ∀ n → Σ S₁ λ x′ → R (fsn t n) x′ × G x′ × (x′ ⇝ x)) where

  lower′ : ∀ {t x} → R t x → G x → (h : HC t) → toL (tree h) ≼ v (ψ x)
  lower′ r g h = ≼-trans (toL-tree h) (E.Sim.lower v ψ G _⇝ˢ_ _⇝_ strict weak R r1 rω r g (conv h))
```
