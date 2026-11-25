# 替代写法的探针 (四): 读作 ψ₀(Ω_{Ω+1}) 那一站的有限测试

> 有限测试 (`refl` 与 `tt`, 单个样本), 不是证明. 样本取自 `YiT2Frame` 的两处, 搬到精简块: 自身行输出的孩子一侧结点 (孩子 1 的 Ω 树上折进 `tw 1`) 朝孩子层目标折叠; 嵌入 `up x c y` 朝孩子 2 里的第 1 层折叠 (`β₁-form` 的那一行).
> 结果: 摊平处, 主线与候选一是 ℕ 极限, 候选二是结点 (同支与异支都是; 槽位层号是第 0 层). 槽位层号高于下标层时候选二仍是 ℕ 极限 (`hi-lev`). 回退处, 目标在第 1 层时三者都没有把孩子树朝第 1 层折叠; 目标在第 0 层而路径经指定孩子时, 两个候选交接, 主线回退.
> 不否定什么, 不比较值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAltTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
import OCF.Lean.YiRWFold as R
open import OCF.Lean.YiAltCmp
open import OCF.Lean.YiAltFold

module N = Fold false
module V = Fold true

isΩ isLim : {ℓ : L} → Tr ℓ → Set
isΩ (Ω _ _) = ⊤
isΩ _       = ⊥
isLim (lim _ _) = ⊤
isLim _         = ⊥
```

## 样本

`tw 1` 的孩子 c 的层号是 `h₁ c`; 孩子 1 的层号是 `nd sS (λ _ → zero)` (第 1 层), 孩子 2 的是第 2 层.

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

o¹ : Ok (tw 1)
o¹ = Ok-tw 1

c1 c2 : Tr zero
c1 = suc zero
c2 = suc c1

β : Tr⁺ (tw 1)
β = Ωt (tw 1)

selfnode : Tr (tw 1)
selfnode = proj₁ (Up (h₁ c1) (down stop c1) β (proj₁ (Ωt (h₁ c1))))

hinode : Tr (tw 1)
hinode = proj₁ (Up (h₁ c2) (down stop c2) β (proj₁ (Ωt (h₁ c2))))

flat-in : isΩ selfnode
flat-in = tt

hi-in : isΩ hinode
hi-in = tt
```

## 摊平处

同支目标 (孩子 1 的层号本身, 路径 `inc c1 self`): 主线与候选一是 ℕ 极限, 候选二是结点.

```agda
flat-old : isLim (proj₁ (R.ψ (tw 1) o¹ (B₀ (tw 1)) (h₁ c1) (inc c1 self) (Ωt (h₁ c1)) selfnode))
flat-old = tt

flat-nrm : isLim (proj₁ (N.ψ (tw 1) o¹ (B₀ (tw 1)) (h₁ c1) (inc c1 self) (Ωt (h₁ c1)) selfnode))
flat-nrm = tt

flat-lev : isΩ (proj₁ (V.ψ (tw 1) o¹ (B₀ (tw 1)) (h₁ c1) (inc c1 self) (Ωt (h₁ c1)) selfnode))
flat-lev = tt
```

异支目标 (孩子 2 里的第 1 层, 与孩子 2 的层号本身): 候选二也是结点, 所以保留与否不分同支异支. 目标是第 0 层 (路径经指定孩子) 时是 ℕ 极限.

```agda
flat-lev-x1 : isΩ (proj₁ (V.ψ (tw 1) o¹ (B₀ (tw 1)) (h₁ c1) (inc c2 (inc tt self)) (Ωt (h₁ c1)) selfnode))
flat-lev-x1 = tt

flat-lev-x2 : isΩ (proj₁ (V.ψ (tw 1) o¹ (B₀ (tw 1)) (h₁ c2) (inc c2 self) (Ωt (h₁ c2)) selfnode))
flat-lev-x2 = tt

flat-lev-z : isLim (proj₁ (V.ψ (tw 1) o¹ (B₀ (tw 1)) zero (inc c1 (inc tt self)) (Ωt zero) selfnode))
flat-lev-z = tt
```

槽位层号是第 1 层 (孩子 2 的 Ω 树上折的结点), 目标是孩子 2 的层号 (第 2 层), 同支: 候选二仍是 ℕ 极限. 槽位层号不经下标层 (这里下标层是第 0 层), 路径比较交不出结果.

```agda
hi-old : isLim (proj₁ (R.ψ (tw 1) o¹ (B₀ (tw 1)) (h₁ c2) (inc c2 self) (Ωt (h₁ c2)) hinode))
hi-old = tt

hi-lev : isLim (proj₁ (V.ψ (tw 1) o¹ (B₀ (tw 1)) (h₁ c2) (inc c2 self) (Ωt (h₁ c2)) hinode))
hi-lev = tt
```

## 回退处

目标是孩子 2 里的第 1 层 (`YiT2Frame.β₁-form` 的那条路径), 嵌入在任意孩子 c. 候选一与主线同形 (回退到第 0 层再用 `ι` 嵌回); 候选二把孩子树折到下标层 (这里是第 0 层, 底是 x 的折叠) 再用 `emb` 嵌回. 三者都没有朝第 1 层折叠孩子树.

```agda
p1 : h₁ c1 ≤ h₁ c2
p1 = inc tt self

module _ (B : Base (tw 1)) (b : Tr⁺ (h₁ c1)) (x : Tr (tw 1)) (c : Tr zero) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y) where

  fb-old : R.ψ (tw 1) o¹ B (h₁ c1) (inc c2 p1) b (up x c y e)
         ≡ R.ψ (tw 1) o¹ B (h₁ c1) (inc c2 p1) b x ⊞ R.ψ₀ (h₁ c) (proj₂ o¹ c) y
  fb-old = refl

  fb-nrm : N.ψ (tw 1) o¹ B (h₁ c1) (inc c2 p1) b (up x c y e)
         ≡ N.ψ (tw 1) o¹ B (h₁ c1) (inc c2 p1) b x ⊞ N.ψ₀ (h₁ c) (proj₂ o¹ c) y
  fb-nrm = refl

  fb-lev : V.ψ (tw 1) o¹ B (h₁ c1) (inc c2 p1) b (up x c y e)
         ≡ V.ψ (tw 1) o¹ B (h₁ c1) (inc c2 p1) b x
           ⊹ emb (h₁ c1) (Ok-≤ (h₁ c2) (proj₂ o¹ c2) p1) (inu (λ _ → self))
               (V.ψ (h₁ c) (proj₂ o¹ c) (λ i u → V.ψ (tw 1) o¹ B i (inc c u) (B i (inc c u)) x) zero
                    (proj₂ (proj₁ o¹) c) (B zero (ink self)) y)
  fb-lev = refl
```

目标是第 0 层, 路径经指定孩子 1 (结点行的链对孩子一侧第 0 层槽位用的就是这种路径, `posW`): 主线回退, 两个候选对任意孩子 c 交接 (底是 x 的折叠, 偏移是 x 的折叠).

```agda
pz : zero ≤ h₁ c1
pz = inc tt self

module _ (B : Base (tw 1)) (b : Tr⁺ zero) (x : Tr (tw 1)) (c : Tr zero) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y) where

  z-old : R.ψ (tw 1) o¹ B zero (inc c1 pz) b (up x c y e)
        ≡ R.ψ (tw 1) o¹ B zero (inc c1 pz) b x ⊞ R.ψ₀ (h₁ c) (proj₂ o¹ c) y
  z-old = refl

  z-nrm : N.ψ (tw 1) o¹ B zero (inc c1 pz) b (up x c y e)
        ≡ N.ψ (h₁ c) (proj₂ o¹ c) (λ i u → N.ψ (tw 1) o¹ B i (inc c u) (B i (inc c u)) x) zero
            (self ∙ proj₂ (proj₁ o¹) c) (N.ψ (tw 1) o¹ B zero (inc c1 pz) b x) y
  z-nrm = refl

  z-lev : V.ψ (tw 1) o¹ B zero (inc c1 pz) b (up x c y e)
        ≡ V.ψ (h₁ c) (proj₂ o¹ c) (λ i u → V.ψ (tw 1) o¹ B i (inc c u) (B i (inc c u)) x) zero
            (self ∙ proj₂ (proj₁ o¹) c) (V.ψ (tw 1) o¹ B zero (inc c1 pz) b x) y
  z-lev = refl
```

## 闭项

两个候选的塔各项与 Λ 的闭项仍是合法的树 (类型给出); 根是 ℕ 极限.

```agda
tw1-nrm : isLim (N.twᶜ 1)
tw1-nrm = tt

tw1-lev : isLim (V.twᶜ 1)
tw1-lev = tt

tw2-nrm : isLim (N.twᶜ 2)
tw2-nrm = tt

tw2-lev : isLim (V.twᶜ 2)
tw2-lev = tt

EBO-nrm : isLim N.EBOᶜ
EBO-nrm = tt

EBO-lev : isLim V.EBOᶜ
EBO-lev = tt
```
