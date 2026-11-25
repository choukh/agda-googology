# 路线乙 O1：链接口与解释接口的共同非空实例

**第 4 层的可满足性检查。** 用可数树的恒等折叠、字面第一位置的链步，
实例化 `ChainDom`；再把参照解释接进同一个实例。它说明链接口、解释
接口及全塔覆盖可以同时满足。实例读记号，不能作为任何候选的实填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevelsO1Model where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)
open import OCF.Lean.CRwBase
  using (Cd; hz; hs; _⊲[_]_; LgB; hself; hsuc; hlim; hLim)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤s; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl)
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω; cof; cω)
import OCF.Align.EboLean3Tree as E
open import OCF.Align.TerminalFoldAccept
  using (read; reference; branch-in-reference)
open import OCF.Align.TreeLevelsO1Cover
  using (GeneratedCover; reference-cover; hc-pred; hc-branch; c0≠cω; c1≠cω)
open import OCF.Align.TreeLevelsO1Chain

countable-system : TreeSystem
countable-system = record
  { Level = Cd
  ; World = ⊤
  ; Position = λ w a b → a ⊲[ w ] b
  ; LegalBound = λ _ b → LgB b
  ; Object = λ _ _ → Cd
  ; observe = λ x → x
  }

frame₀ : Frame countable-system
frame₀ = record
  { world = tt
  ; bound = hs hz
  ; legal = tt
  ; target = hz
  ; source = hz
  ; target-in = hsuc hself
  ; source-in = hsuc hself
  }

identity-fold : FoldSystem
identity-fold = record
  { trees = countable-system
  ; fold = λ _ x → x
  ; Generated = λ _ _ → ⊤
  ; ChainStep = λ _ x y → x ⊲[ tt ] y
  }

prefix-value : ∀ {a b : Cd} → a ⊲[ tt ] b → a ≤ᵛ b
prefix-value hself = ≤ᵛ-refl _
prefix-value (hsuc p) = ≤s (prefix-value p)
prefix-value (hlim n p) = ≤l n (prefix-value p)
prefix-value (hLim {κ = ()} e p)

identity-dom : ChainDom identity-fold
identity-dom = record { chain-lower = λ _ _ _ _ _ p → prefix-value p }

reference-call : ∀ {t} (h : HC t) (e : cof t ≡ cω) n →
  LimCall identity-fold
    (read (E.tree (hc-branch h e n))) (read (E.tree h))
reference-call (h0 f) e n = ⊥-elim (c0≠cω (trans (sym f) e))
reference-call (h1 f h) e n = ⊥-elim (c1≠cω (trans (sym f) e))
reference-call (hω f h) e n = record
  { frame = frame₀
  ; left = read (E.tree (h n))
  ; right = read (E.tree (hω f h))
  ; left-generated = tt
  ; right-generated = tt
  ; step = hlim n hself
  ; lower = ≤ᵛ-refl _
  ; upper = ≤ᵛ-refl _
  }

reference-interpretation : ChainInterpretation identity-fold Cd (λ x → x)
reference-interpretation = record
  { Domain = HC
  ; ι = λ h → read (E.tree h)
  ; predecessor = hc-pred
  ; branch = hc-branch
  ; tower = E.hc-tower
  ; successor-law = GeneratedCover.successor-law reference-cover
  ; limit-call = reference-call
  }

reference-via-chain : reference ≤ᵛ reference
reference-via-chain = Accept.terminal reference-interpretation identity-dom
  branch-in-reference
```

本实例没有 Ω 节点，不能据此称任意候选的规则 6 已满足链支配。
它检验接口整体非空及覆盖接线的方向；候选实填时必须使用自己的
`fold`、`Generated`、`ChainStep`，以及真实 γ 链在它们之间的模拟。
