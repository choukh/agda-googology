# 跨高度单调 (五): 下一步的评估

> 结论写在 [LadderMono](LadderMono.lagda.md). 不写新树. 两条编译过的小事实, 都只说现在的 `Q m`:
>
> 1. **`no-top`: 没有一个 $m:\mathbb N$ 让每个高度都 $<^L m$.** 所以 $\Omega_{\Omega\cdot\omega+1}$ 的输入 (含一切高度的节点) 不是任何 `Q m α` 的元素. 这条很弱, 只否定"现有的 `Q m` 直接够用", 不否定 ℕ 作高度标签.
> 2. **`Ω↓⊑`, `Ω↓↓⊑`: 跨高度单调的**上下文**版本已经有了.** 在任何相似的上下文里, $\iota_\downarrow(\dot\Omega_m\,0)\sqsubseteq^T\dot\Omega_{m+1}\,0$, 再过一次 $\iota_\downarrow$ 也成立. 这是把 $\dot\Omega_{\Omega\cdot\omega}\,0$ 写成 `ql` 时, 规则 `gl` 要的单调在有限高度上的影子. 用的是现成的 `cl-rᵀ`, `Ωz↓`, `ιD-cong`.
>
> 其余的评估是判断, 写在 [LadderMono](LadderMono.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderMonoNext where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Free.Level
open import OCF.Align.LadderNFTree
open import OCF.Align.LadderNFRules using (_⊑ᵀ_; wk-rᵀ; ιD-cong)
open import OCF.Align.LadderNFRules2 using (cl-rᵀ)
open import OCF.Align.LadderNFMono using (Ωz↓)
```

```agda
<ᴸ-irr : ∀ m → m <ᴸ m → ⊥
<ᴸ-irr (suc m) q = <ᴸ-irr m (dn q)

no-top : ∀ m → (∀ n → n <ᴸ m) → ⊥
no-top m all = <ᴸ-irr m (all m)

Ω↓⊑ : ∀ m → ι↓ {n = m} {α = zero} (Ω̇ m zero) ⊑ᵀ Ω̇ (suc m) zero
Ω↓⊑ m = cl-rᵀ (wk-rᵀ (Ωz↓ (suc zero)))

Ω↓↓⊑ : ∀ m → ι↓ {α = zero} (ι↓ {n = m} {α = zero} (Ω̇ m zero)) ⊑ᵀ ι↓ {α = zero} (Ω̇ (suc m) zero)
Ω↓↓⊑ m = ιD-cong (Ω↓⊑ m)
```
