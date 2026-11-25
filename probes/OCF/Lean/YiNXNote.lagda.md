# 非标准形见证项的相邻层规范化
> 验收文件（读记号），编译定理：`W k = ψ₀(ψₖ(Ωₖ₊₁))` 有推导，与标准形 `N k = ψ₀(Ωₖ₊₁)` 的参照值互相 `≼`；`W k` 不是标准形。
> 标准形 `s ≤ᵀ W k` 的项序可搬到 `N k`，从而推出值序。树、折叠、合法性不改。
> 平移论证参照 `YiNFOCase.D≼B/B≼D`；直接复用 `YiKSRead.fs-sup`、`YiCFMono.mono≤ⁿ` 与已有记号方程。完整合成出口见 `YiNXFull.Out.exit-low0`，全部叶子的值比较由三次第 0 支给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNXNote where

open import Data.Nat using (ℕ; zero; suc; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using ([])
open import Data.Sum using (inj₁)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import OCF.Align.EboLeanDef using (T; HC; hω; cof; cω; fsn; γT; natT; _<ᵀ_; hd<; ar<; lv<; []<)
open import OCF.Align.EboLeanBase using (NF; n∷; nψ; gp; gh; _≤ᵀ_; c∷; c[]; ≤-<; <ᵀ-asym)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; Ctbl-fsn)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofΩ; fsTΩ; cmp-gt)
open import OCF.Lean.YiANEnd using (nat<)
open import OCF.Lean.YiDCRel using (nat≤)
open import OCF.Lean.YiKSRead using (fs-sup)
open import OCF.Lean.YiDCExit using (nf-low; pre[])
open import OCF.Lean.YiMENote using (cofψω; fsnψω)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼; fs≼)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Align.Value using (_≼_; ≼-trans)

N W : ℕ → T
N k = ψᴺ 0 (Ωᴺ (suc k))
W k = ψᴺ 0 (ψᴺ k (Ωᴺ (suc k)))

G : ℕ → ℕ → T
G k n = γT (Ωᴺ (suc k)) (natT k) n

nfN : ∀ k → NF (N k)
nfN k = nf-low (pre[] (suc k)) ≤-refl

cofN : ∀ k → cof (N k) ≡ cω
cofN k rewrite cofΩ k | cmp-gt {b = 0} {a = k} z≤n = refl

cofI : ∀ k → cof (ψᴺ k (Ωᴺ (suc k))) ≡ cω
cofI k rewrite cofΩ k | cmp-gt {b = k} {a = k} ≤-refl = refl

cofW : ∀ k → cof (W k) ≡ cω
cofW k = cofψω [] (ψᴺ k (Ωᴺ (suc k))) (cofI k)

fsN : ∀ k n → fsn (N k) n ≡ ψᴺ 0 (G k n)
fsN k n rewrite cofΩ k | cmp-gt {b = 0} {a = k} z≤n | fsTΩ k (G k n) = refl

fsI : ∀ k n → fsn (ψᴺ k (Ωᴺ (suc k))) n ≡ ψᴺ k (G k n)
fsI k n rewrite cofΩ k | cmp-gt {b = k} {a = k} ≤-refl | fsTΩ k (G k n) = refl

G-step : ∀ k n → G k (suc n) ≡ ψᴺ k (G k n)
G-step k n = cong (ψᴺ k) (fsTΩ k (G k n))

shift : ∀ k n → fsn (W k) n ≡ fsn (N k) (suc n)
shift k n rewrite fsnψω [] (ψᴺ k (Ωᴺ (suc k))) n (cofI k) | fsI k n | fsN k (suc n) | G-step k n = refl

first-step : ∀ k → fsn (N k) 0 <ᵀ fsn (N k) 1
first-step k rewrite fsN k 0 | fsN k 1 | G-step k 0 = hd< (ar< (hd< (ar< []<)))

W<N : ∀ k → W k <ᵀ N k
W<N k = hd< (ar< (hd< (lv< (nat< k))))

opaque
  hN : ∀ k → HC (N k)
  hN k = hc (nfN k) (c∷ c[])

hW : ∀ k → HC (W k)
hW k = hω (cofW k) (λ n → subst HC (sym (shift k n)) (hω-inv (hN k) (cofN k) (suc n)))

W≼N : ∀ k (h : HC (W k)) (h′ : HC (N k)) → Rt h ≼ Rt h′
W≼N k h h′ = fs-sup h (cofW k) (λ n →
  ≼-trans (tree-≼ (shift k n) (hω-inv h (cofW k) n) (hω-inv h′ (cofN k) (suc n))) (fs≼ h′ (cofN k) (suc n)))

N≼W : ∀ k (h : HC (N k)) (h′ : HC (W k)) → Rt h ≼ Rt h′
N≼W k h h′ = fs-sup h (cofN k) λ where
  zero → ≼-trans (mono≤ⁿ (cl-fsn-NF (nfN k) (cofN k) 0) (cl-fsn-NF (nfN k) (cofN k) 1)
                           (Ctbl-fsn (c∷ c[]) (cofN k) 1)
                           (hω-inv h (cofN k) 0) (hω-inv h (cofN k) 1) (inj₁ (first-step k)))
                  (≼-trans (tree-≼ (sym (shift k 0)) (hω-inv h (cofN k) 1) (hω-inv h′ (cofW k) 0)) (fs≼ h′ (cofW k) 0))
  (suc n) → ≼-trans (tree-≼ (sym (shift k n)) (hω-inv h (cofN k) (suc n)) (hω-inv h′ (cofW k) n)) (fs≼ h′ (cofW k) n)

orderW : ∀ k {s} → s ≤ᵀ W k → s ≤ᵀ N k
orderW k le = inj₁ (≤-< le (W<N k))

monoW : ∀ k {s} → NF s → s ≤ᵀ W k → (h : HC s) (h′ : HC (W k)) → Rt h ≼ Rt h′
monoW k ns le h h′ = ≼-trans (mono≤ⁿ ns (nfN k) (c∷ c[]) h (hN k) (orderW k le)) (N≼W k (hN k) h′)

¬nfW : ∀ k → NF (W k) → ⊥
¬nfW k (n∷ (nψ _ _ g) _ _) = <ᵀ-asym (g (gp (gh (nat≤ {m = 0} {n = k} z≤n)))) (hd< (lv< (nat< k)))
```
