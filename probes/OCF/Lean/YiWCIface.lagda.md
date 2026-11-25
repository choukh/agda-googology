# 较弱链形状给出结点出口 (抽象)

> 判决: 编译定理, 无前提; 只导入标准库, `YiAbs*`, `YiFIIface`, `YiQDIface`, `YiXTIface`, `YiBAWeak`, 不读记号. `XT.out` 的变体 `outʳ`: `AboveL` 与分叉一份换成 `YiBAWeak.RefChainʳ` (参照链第 k 项只要不高于树的链的某一项), 结点出口照样成立; 做法是按 `RefChainʳ` 给的下标重排树的链 (`reidx`). 原形状推出较弱形状 (`weakenA`).
> 不给出什么: 不涉及值, 不对记号实填; EBO 参照上的实例与否定在 [YiWCTw1](YiWCTw1.lagda.md), 接线在 [YiWCWire](YiWCWire.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWCIface where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiFIIface
open import OCF.Lean.YiQDIface
open import OCF.Lean.YiXTIface
open import OCF.Lean.YiBAWeak

module XW {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
          (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open FI 𝔾 𝔻
  open QD 𝔾 𝔻
  open XT 𝔾 𝔻
  open W 𝔾 𝔻

  module _ {j : Lv} (𝒮 : Sys j) where
    private module S = Sys 𝒮
    module _ (𝓀 : S.KeepLaw) (D : ∀ {a} → S.St a → Tr a → Set) (xt : XTree 𝒮 𝓀 D) where
      open XTree xt
```

`PartXʳ`, `AboveLʳ`: `XT.PartX`, `XT.AboveL` 的链一支换成 `RefChainʳ`, 其余逐字.

```agda
      PartXʳ : ∀ {a} (s : S.St a) (K : S.Cxt) (p : Sl a) (g : SlT a p → Tr a) → D s (nd p g) → T → T → XPick 𝒮 s p → Set
      PartXʳ s K p g d t κ (cross ne _ _ _ _) = RefChainʳ 𝒮 s K p g t (ch s p g d ne)
      PartXʳ s K p g d t κ (kept _)           = ⊤
      PartXʳ s K p g d t κ (high _ _)         = ⊤

      AboveLʳ : Set
      AboveLʳ = ∀ {a} (s : S.St a) K → S.Bdˢ s K → (p : Sl a) → ∀ {t κ} (g : SlT a p → Tr a) (d : D s (nd p g))
        → CΩ t κ → Nu a p κ → (∀ η c → R (slL a p) η (slT a p c) → R a (fsT t η) (g c))
        → (ne : S.Ev s p → ⊥) → j ⊑ slL a p → RefChainʳ 𝒮 s K p g t (ch s p g d ne)

      weakenA : AboveL 𝒮 𝓀 D xt → AboveLʳ
      weakenA ab s K bd p g d e nu hR ne u = weaken 𝒮 (ch s p g d ne) (ab s K bd p g d e nu hR ne u)
```

`NodeRes` 的链一支不要求链是树一侧给的那条, 所以重排后的链 `z ∘ m` 直接可用.

```agda
      reidx : ∀ {a} {s : S.St a} {K p g t κ} (c : Chain 𝒮 s p g) → RefChainʳ 𝒮 s K p g t c → NodeRes 𝒮 𝓀 s K p g t κ
      reidx (z , dm) (γ , cω , fs , ch′) =
        inj₂ (γ , (λ k → z (proj₁ (ch′ k))) , cω , fs , (λ k → proj₂ (ch′ k)) , (λ k → dm (proj₁ (ch′ k))))

      outʳ : Below 𝒮 → AboveLʳ → At 𝒮 𝓀 D xt PartXʳ → NodeOut 𝒮 𝓀 D
      outʳ bl ab cx s K bd p {t} {κ} g d e nu hR = go (xp s p) (cx s K bd p g d e nu hR)
        where
        go : (x : XPick 𝒮 s p) → PartXʳ s K p g d t κ x → NodeRes 𝒮 𝓀 s K p g t κ
        go (kept ev) _ with bl s K bd p e nu (S.KeepLaw.slot 𝓀 s p ev) (lvl s p ev)
        ... | cΩ , fs , nu′ = inj₁ (ev , cΩ , fs , nu′ , mvR s p ev)
        go (high ne u) _ = reidx (ch s p g d ne) (ab s K bd p g d e nu hR ne u)
        go (cross ne _ _ _ _) r = reidx (ch s p g d ne) r
```
