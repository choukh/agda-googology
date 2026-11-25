# 验收 (换基折叠): Ω 树朝第 2 层的折叠沿层号的后继与 ℕ 极限上行

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理, 无前提, 对任意层号 ℓ 与任意证据: `SL t ℓ o v` (对一切底与起点, t 对着层号 ℓ 的 Ω 树沿 v 朝第 2 层的折叠, `YiRBSib` 的折叠) 沿后继形状上行 (`sucC`, `sucU`), 沿 ℕ 极限形状上行 (`limU`: 一切孩子的路径; `limC`: 经孩子 0 的路径, 第 n 项经 `way` 落到孩子 n 的层, 路径是 `v₀ ∙ from0`).
> 来源: `sucC`, `sucU` 是 `YiRBFam.liftC`, `liftU` 去掉 "层号是 `fn m`" 的限制; `limU`, `limC` 照 `YiKCStep.limH` (候选 A) 在 `YiRBSib` 的折叠上重写.
> ℕ 极限形状的层上不需要关系族: 那一层的 Ω 树各项都是孩子层的 Ω 树的嵌入. 不涉及 Ω 形状的层号, 不涉及上界. 用在 [YiRLCrit](YiRLCrit.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRLClos where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (OKB; ψ-⊵)
open import OCF.Lean.YiRBCrit using (two)
open import OCF.Lean.YiKVRel using (mw; _⊴_; ⊴-◃)
open import OCF.Lean.YiKCStep using (⊴-trans)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiANFam using (Ωᴺ)
open import OCF.Lean.YiCLFam using (M; module GM; m⊴N)
```

## 陈述

```agda
SL : E.T → (ℓ : L) → Ok ℓ → two ≤ ℓ → Set
SL t ℓ o v = (r : Rb ℓ) (B : Base ℓ) (β : Tr⁺ two) → OKB B → M 2 (Ωᴺ 2) (proj₁ β)
           → M 2 t (proj₁ (ψ ℓ o r B two v β (proj₁ (Ωt ℓ))))
```

## 后继形状

结点不保留; 回灌链的第 1 项在孩子层的 Ω 树之上, 折叠的第 1 项是 `next⁺ (孩子层上的折叠)`.

```agda
module _ {t : E.T} (ℓ : L) (o : Ok (nd sS (λ _ → ℓ))) (v : two ≤ ℓ) where
  private
    Fk : (r : Rb (nd sS (λ _ → ℓ))) (B : Base (nd sS (λ _ → ℓ))) (β : Tr⁺ two) → ℕ → Tr⁺ two
    Fk r B β k = next⁺ (ψ ℓ (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) two v β
      (iter (λ z → proj₁ (next⁺ (ψ ℓ (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) ℓ self (B ℓ (inc tt self)) z))) zero k))

    core : SL t ℓ (proj₂ o tt) v → (r : Rb (nd sS (λ _ → ℓ))) (B : Base (nd sS (λ _ → ℓ))) (β : Tr⁺ two)
         → OKB B → M 2 (Ωᴺ 2) (proj₁ β) → M 2 t (proj₁ (limc⁺ (Fk r B β)))
    core s r B β ok hβ =
      GM.m-cum 1 (Fk r B β) 1
        (mw (mw (s (proj₂ r tt) (λ i u → B i (inc tt u)) β (λ i u → ok i (inc tt u)) hβ)
                (mono ℓ (proj₂ o tt) (proj₂ r tt) (λ i u → B i (inc tt u)) two v β (⊴-◃ (ok ℓ (inc tt self)) (◃l zero))))
            (◃l zero))

  sucC : SL t ℓ (proj₂ o tt) v → SL t (nd sS (λ _ → ℓ)) o (inc tt v)
  sucC = core

  sucU : SL t ℓ (proj₂ o tt) v → SL t (nd sS (λ _ → ℓ)) o (inu (λ _ → v))
  sucU = core
```

折叠的第 0 项是 `next⁺ β` (供 η = 0 用).

```agda
  suc0C : (r : Rb (nd sS (λ _ → ℓ))) (B : Base (nd sS (λ _ → ℓ))) (β : Tr⁺ two) → M 2 t (proj₁ (next⁺ β))
        → M 2 t (proj₁ (ψ (nd sS (λ _ → ℓ)) o r B two (inc tt v) β (proj₁ (Ωt (nd sS (λ _ → ℓ))))))
  suc0C r B β m = GM.m-cum 1 (Fk r B β) 0 m

  suc0U : (r : Rb (nd sS (λ _ → ℓ))) (B : Base (nd sS (λ _ → ℓ))) (β : Tr⁺ two) → M 2 t (proj₁ (next⁺ β))
        → M 2 t (proj₁ (ψ (nd sS (λ _ → ℓ)) o r B two (inu (λ _ → v)) β (proj₁ (Ωt (nd sS (λ _ → ℓ))))))
  suc0U r B β m = GM.m-cum 1 (Fk r B β) 0 m
```

## ℕ 极限形状

Ω 树的第 n 项字面地是 `up (前 n 项) n (孩子 n 的 Ω 树)` (`cum-form`).

```agda
pfx : (g : ℕ → L) → ℕ → Tr (nd sL g)
pfx g zero    = zero
pfx g (suc n) = cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) n

cum-form : (g : ℕ → L) (n : ℕ)
  → cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) n ≡ up (pfx g n) n (proj₁ (Ωt (g n))) (proj₂ (Ωt (g n)))
cum-form g zero    = refl
cum-form g (suc n) = refl

module _ {t : E.T} (g : ℕ → L) (o : Ok (nd sL g)) where
  private
    Bn : (r : Rb (nd sL g)) (B : Base (nd sL g)) (n : ℕ) → Base (g n)
    Bn r B n i u = ψ (nd sL g) o r B i (inc n u) (B i (inc n u)) (pfx g n)

    okn : (r : Rb (nd sL g)) (B : Base (nd sL g)) (n : ℕ) → OKB B → OKB (Bn r B n)
    okn r B n ok i u = ⊴-trans (ok i (inc n u)) (ψ-⊵ (nd sL g) o r B i (inc n u) (B i (inc n u)) (pfx g n))

  limU : (vs : (n : ℕ) → two ≤ g n) (n : ℕ) → SL t (g n) (proj₂ o n) (vs n) → SL t (nd sL g) o (inu vs)
  limU vs n s r B β ok hβ =
    mw (subst (λ Y → M 2 t (proj₁ (ψ (nd sL g) o r B two (inu vs) β Y))) (sym (cum-form g n))
         (s (proj₂ r n) (Bn r B n) (ψ (nd sL g) o r B two (inu vs) β (pfx g n)) (okn r B n ok)
            (m⊴N 2 hβ (ψ-⊵ (nd sL g) o r B two (inu vs) β (pfx g n)))))
       (◃l n)

  limC : (v₀ : two ≤ g 0) (n : ℕ) → SL t (g n) (proj₂ o n) (v₀ ∙ from0 g (proj₁ o) n) → SL t (nd sL g) o (inc 0 v₀)
  limC v₀ n s r B β ok hβ =
    mw (subst (λ Y → M 2 t (proj₁ (ψ (nd sL g) o r B two (inc 0 v₀) β Y))) (sym (cum-form g n))
         (s (proj₂ r n) (Bn r B n) (ψ (nd sL g) o r B two (inc 0 v₀) β (pfx g n)) (okn r B n ok)
            (m⊴N 2 hβ (ψ-⊵ (nd sL g) o r B two (inc 0 v₀) β (pfx g n)))))
       (◃l n)
```
