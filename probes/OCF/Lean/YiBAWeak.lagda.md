# `AboveL` 的链一支去掉逐项对齐

> 判决: 编译定理, 无前提; 只导入标准库与 `YiAbs*`, `YiFIIface`, `YiQDIface`, `YiXTIface`, 不读记号. `RefChainʳ`: 参照链 γ 的第 k 项只要不高于树的链的某一项 (下标 m 由 k 决定), 不要求第 k 项对第 k 项. 原形状推出它 (`weaken`); 它对结点一行仍然足够 (`nodeʳ`), 因为链点到结点像的支配对每个下标都成立.
> 用途: [YiBAEbo](YiBAEbo.lagda.md) 的 `¬above` 否定的是逐项对齐 (参照链第 0 项是 Ω_κ, 树的链从零树起). 不给出什么: `RefChainʳ` 在 EBO 参照上是否成立没有检查; 不处理参照不坍缩的点 (那里结点出口本身不成立, `YiBAEbo.¬nodeout`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBAWeak where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiXTIface

module W {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
         (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open FI 𝔾 𝔻
  open QD 𝔾 𝔻

  module _ {j : Lv} (𝒮 : Sys j) where
    private module S = Sys 𝒮

    RefChainʳ : ∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) (t : T) → Chain 𝒮 s p g → Set
    RefChainʳ {a} s K p g t (z , _) = Σ (ℕ → T) λ γ → Cω (S.ap K t) × (∀ k → fsn (S.ap K t) k ≡ S.ap K (fsT t (γ k)))
      × (∀ k → Σ ℕ λ m → R (slL a p) (γ k) (slT a p (z m)))

    weaken : ∀ {a} {s : S.St a} {K p g t} (c : Chain 𝒮 s p g) → XT.RefChain 𝔾 𝔻 𝒮 s K p g t c → RefChainʳ s K p g t c
    weaken c (γ , cω , fs , ch) = γ , cω , fs , λ k → k , ch k

    nodeʳ : Lim → ∀ {a} (s : S.St a) K (p : Sl a) {t} (g : SlT a p → Tr a) (c : Chain 𝒮 s p g)
      → RefChainʳ s K p g t c
      → (∀ η x → R (slL a p) η (slT a p x) → S.Q s K (fsT t η) (g x))
      → S.Q s K t (nd p g)
    nodeʳ lm s K p {t} g (z , dm) (γ , cω , fs , ch) hQ =
      lm cω (λ k → subst (λ o → R j o (S.Φ s (nd p g))) (sym (fs k))
        (dm (proj₁ (ch k)) (hQ (γ k) (z (proj₁ (ch k))) (proj₂ (ch k)))))
```
