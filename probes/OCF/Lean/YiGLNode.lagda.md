# 精确标签下的结点行

> 验收文件 (读记号)。编译条件定理: 在 `Rˣ` 里, 带 `Low` 搬运的框架 `NodeFrameᴸ` 加分支保持与链, 推出 Ω 结点折到任意目标的保持 (`node-rowˣ`); 后继形状层号折到孩子的框架无前提有居民 (`frameᴸ-S`)。
> 做法: 逐字照 `YiGTNode.Core.node-at` 的两支 (保留支与走链支), 关系换成 `Rˣ`, 槽位余尾换成 `Lbl`; 记号一侧的算式引用 `YiANFam` 与 `YiMWPre`。
> 链 (`Chainˣ`) 与分支保持是前提, 没有实填; 嵌入、上折、自身三行没有移到 `Rˣ`。不否定什么。入口: [YiGLExact](YiGLExact.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGLNode where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (feed)
open import OCF.Lean.YiANFam using (Pen; cofG; fsnG; cofK; fsTK)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLean3Base using (sucT≤)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Lean.YiGLFrame
open import OCF.Lean.YiGLExact
```

## 各层的三条生成规则

```agda
mΩˣ : ∀ j {t κ} (q : Pos j) {G : Br j q → Tr j} → E.cof t ≡ E.cΩ κ → Lbl (at j q) κ
  → (∀ η c → Lowˣ j q η c → Rˣ j (E.fsT t η) (G c)) → Rˣ j t (Ω q G)
mΩˣ zero ()
mΩˣ (nd s h) q e nu f = H.mΩ e nu f

mLˣ : ∀ j {t x} → E.cof t ≡ E.cω → (∀ n → Rˣ j (E.fsn t n) x) → Rˣ j t x
mLˣ zero = H.mL
mLˣ (nd s h) = H.mL

cumˣ : ∀ j (F : ℕ → Tr⁺ j) n {t} → Rˣ j t (proj₁ (F n)) → Rˣ j t (proj₁ (limc⁺ F))
cumˣ zero F n = H.G⁰.m-cum F n
cumˣ (nd s h) F n = Gˣ.m-cum s h F n
```

## 框架与结点行

`KeepSpecᴸ` 比 `YiGLFrame.KeepSpecˣ` 多保留一支的 `Low` 搬运。

```agda
KeepSpecᴸ : ∀ ℓ j (ν : E.T) (p : Pos ℓ) (κ : E.T) → Keep j (Br ℓ p) (fromBr ℓ p zero) → Set
KeepSpecᴸ ℓ j ν p κ nothing = E.cmpᵀ (E.sucT κ) ν ≡ E.gt
KeepSpecᴸ ℓ j ν p κ (just (q , cv , eq)) = Pen (E.cmpᵀ (E.sucT κ) ν) × Lbl (at j q) κ
  × (∀ η c → Lowˣ j q η c → Lowˣ ℓ p η (cv c))

NodeFrameᴸ : ∀ ℓ → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
NodeFrameᴸ ℓ o j w ν = (p : Pos ℓ) (κ : E.T) → Lbl (at ℓ p) κ → KeepSpecᴸ ℓ j ν p κ (kp ℓ o p w)

frameᴸ-S : (h : ⊤ → L) (o : Ok (nd sS h)) {ν : E.T} → Lbl (h tt) ν
  → NodeFrameᴸ (nd sS h) o (h tt) (inc tt self) ν
frameᴸ-S h o lν (inj₁ ())
frameᴸ-S h o {ν} lν (inj₂ (tt , inj₁ tt)) κ lκ =
  subst (λ z → E.cmpᵀ (E.sucT z) ν ≡ E.gt) (sym (uniq (h tt) lκ lν)) (<→gt (<-sucT ν))
frameᴸ-S h o lν (inj₂ (tt , inj₂ q)) κ lκ =
  ≤→pen (sucT≤ (below (h tt) q lκ lν)) , lκ , λ η c l → l

module Nodeˣ (ℓ j : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ)
  (ν t : E.T) (β : Tr⁺ j) where
  F : Tr ℓ → Tr⁺ j
  F x = ψ ℓ o r B j w β x

  Chainˣ : E.T → (p : Pos ℓ) → E.T → (Br ℓ p → Tr ℓ) → Set
  Chainˣ a p κ g = ∀ n → Lowˣ ℓ p (E.γT (t ++ a) κ n)
    (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))

  node-atˣ : ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ
    → (∀ η c → Lowˣ ℓ p η c → Rˣ j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → Chainˣ a p κ g
    → (K : Keep j (Br ℓ p) (fromBr ℓ p zero)) → KeepSpecᴸ ℓ j ν p κ K
    → Rˣ j (E.ψ ν (t ++ a) ∷ []) (proj₁ (node⁺ K (λ c → F (g c)) (feed ℓ o r B p g)))
  node-atˣ p {a} {κ} g e bh hc (just (q , cv , eq)) (pen , nuq , low) =
    mΩˣ j q (cofK ν (t ++ a) pen (cof++Ω t a e)) nuq
      (λ η c lc → subst (λ z → Rˣ j z (proj₁ (F (g (cv c)))))
        (sym (trans (fsTK ν (t ++ a) η pen (cof++Ω t a e))
          (cong (λ z → E.ψ ν z ∷ []) (fsT++ t a η e))))
        (bh η (cv c) (low η c lc)))
  node-atˣ p {a} {κ} g e bh hc nothing gt =
    mLˣ j (cofG ν (t ++ a) gt (cof++Ω t a e))
      (λ n → subst (λ z → Rˣ j z
        (proj₁ (limc⁺ (λ k → F (g (iter (feed ℓ o r B p g) (fromBr ℓ p zero) k))))))
        (sym (trans (fsnG ν (t ++ a) n gt (cof++Ω t a e))
          (cong (λ z → E.ψ ν z ∷ []) (fsT++ t a (E.γT (t ++ a) κ n) e))))
        (cumˣ j (λ k → F (g (iter (feed ℓ o r B p g) (fromBr ℓ p zero) k))) (suc n)
          (bh (E.γT (t ++ a) κ n) _ (hc n))))

  node-rowˣ : NodeFrameᴸ ℓ o j w ν
    → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → Lbl (at ℓ p) κ
    → (∀ η c → Lowˣ ℓ p η c → Rˣ j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → Chainˣ a p κ g
    → Rˣ j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))
  node-rowˣ frame p {κ = κ} g e nu bh hc = node-atˣ p g e bh hc (kp ℓ o p w) (frame p κ nu)
```
