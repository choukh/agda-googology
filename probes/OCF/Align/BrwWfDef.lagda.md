# 沿 View 递归 (一): 部分关系, 良基的记录, 度量引理

> 不含记号. 入口 [BrwWf](BrwWf.lagda.md). [BrwViewDef](BrwViewDef.lagda.md) 的记录 `BrwView` 给每个合法对象一个 View (零, 后继, $\mathbb N$-极限, $\Omega$-极限), 但没有说部分良基, 所以还不能沿 View 递归. 这里补上.
>
> - `Obj`: 合法对象 (下标, 对象, 合法性的证明). 第 1 层的合法性 `HW` 带内容, 所以部分带着它自己的合法性证明.
> - `Part w o`: $o$ 是 View $w$ 的一个部分. 后继的 $y$, $\mathbb N$-极限的每个 $f\,n$, $\Omega$-极限在**合法坐标**上的 $g\,c$ (只有那里有合法性).
> - `_◁_`: $o' ◁ o$ 当且仅当 $o'$ 是 $o$ 的 View 的部分. 它依赖 View 的选法 (`BrwView` 的 `view`).
> - `BrwViewᵂ`: `BrwView` 加上 `_◁_` 良基 (标准库的 `Acc`, 构造的).
> - `measure`: 部分在一个良基关系里严格下降, 则 `_◁_` 良基. 三个实例都用它, 度量各不相同.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwWfDef where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import OCF.Align.BrwViewDef using (Sig; View; vz; vs; vl; vΩ; BrwView)
```

## §1 部分

```agda
module _ (S : Sig) (X : Sig.Ix S → Set) (val : ∀ {i} → X i → Sig.B S i) (Lgl : ∀ {i} → X i → Set) where
  open Sig S

  Obj : Set
  Obj = Σ Ix (λ i → Σ (X i) (Lgl {i}))

  data Part {i : Ix} {v : B i} : View S X val Lgl i v → Obj → Set where
    p-s : ∀ {y ly e} → Part (vs y ly e) (i , y , ly)
    p-l : ∀ {f lf st e} n → Part (vl f lf st e) (i , f n , lf n)
    p-Ω : ∀ {k g lg e} (c : Cd k) (lc : LgC c) → Part (vΩ k g lg e) (tg c , g c , lg c lc)

  module _ (V : BrwView S X val Lgl) where
    infix 4 _◁_
    _◁_ : Obj → Obj → Set
    o ◁ (i , x , lx) = Part (BrwView.view V x lx) o

  record BrwViewᵂ : Set where
    field
      bv : BrwView S X val Lgl
      wf : WellFounded (_◁_ bv)
```

**读法.** `_◁_` 只看 View 给出的部分, 不看对象的字面结构. 第 0 层的部分是前缀与部分和, 第 1 层 $\Omega$-极限的部分是 "前缀抬到大世界, 再接上一段积分", 都不是字面子项. 所以良基要用度量.

## §2 度量引理

```agda
module _ {O T : Set} (_◁_ : O → O → Set) (_<_ : T → T → Set) (m : O → T) where
  measure-acc : ∀ (dec : ∀ {o o′} → o′ ◁ o → m o′ < m o) o → Acc _<_ (m o) → Acc _◁_ o
  measure-acc dec o (acc rs) = acc (λ {o′} r → measure-acc dec o′ (rs (dec r)))

  measure : WellFounded _<_ → (∀ {o o′} → o′ ◁ o → m o′ < m o) → WellFounded _◁_
  measure wf dec o = measure-acc dec o (wf (m o))
```
