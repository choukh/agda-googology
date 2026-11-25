# K4: 折叠对逐点关系单调, `Level` 族一切层

> **判决: HOLDS (定理, 已编译; 第 4 层工具, 不进成品).** `Level` 族上有单向的逐点关系 `_⊑ᵖ_`, 折叠在一切层保持它: `ψ-⊑ : i ≅ᴵ i′ → a ⊑ᵖ b → ψ p σ a ⊑ᵖ ψ p′ σ′ b`. 第 0 层上它就是值序, 所以 `ψ⁰-monoᵖ : a ⊑ᵖ b → ψ⁰ a ≼ ψ⁰ b` 对任意两层的输入成立. 第 2 层没有出现障碍.
> **关系:** 零, 后继, ℕ-极限, 提升的规则同 `Value._≼_`; Ω-结点只有逐点 (分支层 `≅ᴵ` 相关) 与 "在右结点的全部分支之下" 两条. 带合法性的版本 (`Legal`, `L`) 左自反且传递; 不带的版本 (`Wide`, `W`) 原样给出 `RR4MonoFragment` 的 `pointwise-mono₁` (`pointwise-mono₁′`).
> **编译过的边界:** "在某一支之下" 不能加回 (`no-below`); 逐点规则不能放宽到分支层不同的结点, 第 2 层有闭项反例 (`no-cross-level`); 层号平移不在关系里 (`incomplete`).
> **不否定, 也不覆盖:** `Wide` 版的传递未证, 无反例; 高层上 `⊑ᵖ` 与 `≼` 的关系未比较; 只对 `Level` 族, 不涉及差树与高度树上带状态与世界的折叠.
> 文件: [K4MonoRel](K4MonoRel.lagda.md) (关系, 搬运, 传递), [K4MonoFold](K4MonoFold.lagda.md) (折叠), [K4MonoValue](K4MonoValue.lagda.md) (值序, 实例), [K4MonoNeg](K4MonoNeg.lagda.md) (边界). 后两件的导入闭包经 `Value` 含记号模块.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K4Mono where

open import OCF.Align.K4MonoRel public using (module Rel; module Wide; module Legal)
open import OCF.Align.K4MonoFold public using (module Fold)
open import OCF.Align.K4MonoValue public
  using (module Val; module W; module L; pointwise-mono₁′; node-char; node-charᴸ; ⊑ᴸ-trans; ⊑ᴸ-reflˡ;
         no-below; ⊑ᵖ-no-below; ≼-not-fold-mono; ≅-legal-not-⊑-legal)
open import OCF.Align.K4MonoNeg public using (no-cross-level; Aˣ; Bˣ; Aˣ⋢Bˣ; incomplete)
```
