# 单一并上的折叠要什么 (三): 只增长的世界, 可数增量

> 不含记号. 入口 [CohW2](CohW2.lagda.md). [CohW2Need](CohW2Need.lagda.md) 的定理要 `r-sub` (被升一层的子层号的界不变), 那是回灌后把树搬回原世界 (`drp`) 要的. 另一条出路 (`DiagK2` 在 `L′ 1` 上试): **回灌不搬回, 目标世界跟着长**; 那就不要 `r-sub`, 只要 "被升的一层恰好接长, 其余各层只长不缩". 接口写成记录 `RaiseGrow`, 与 `RaiseAt` 只差 `r-sub` 换成 `g-grow`:
>
> - `raise : X → Wd → Wd` (增量的类型 `X`, 经 `inj` 进被升那一层的坐标);
> - `g-at`: 层 $\ell$ 的界变成 `β ℓ w ⊞⁰ inj x`;
> - `g-grow`: 每一层的界都是原来的界接上某个增量 (所以原来的界是新界的第一位置, `⊞⁰-fst`, 在一切世界里).
>
> **定理.** `growA`: 增量是**可数的** (`H⁰ (Lv lz)`, 没有 $\Omega$-节点) 时, `GW` 上**对一切层号** (包括极限层号, 包括 `CohW2Need.ℓα α`) 都有 `RaiseGrow`: 把同一个可数增量接到**每一层**的界上, 不挑出哪一层, 不用判定. `CohW2Need` 的 WLPO 论证用不上这里 (没有 `r-sub`).
>
> **没有做到的 (判断).** 回灌的增量是读回的输出: 第 0 层读回 (`sum`) 是可数的, `growA` 够用; 更高层的读回 (`HtTowerFRead.rd`) 含低层种类的 $\Omega$-节点, 不是可数的, 要把它接到**一切**层上, 就要把层 $\ell$ 的坐标翻译成层 $y$ 的坐标 (只在结构对得上的地方). 翻译在 $y\equiv\ell$ 处是外延的恒等, 要 `g-at` 的等式就要函数外延 (分支是函数). 没有写, 未走通.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohW2Grow where

open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.CohWGl using (LH; lz; Lv; Lv⋆; H⁰; z⁰; s⁰; l⁰; Ω⁰; cv; bot⋆; botBd⋆)
open import OCF.Align.CohW2Need using (World; Wd; β; _⊞⁰_; GWo)

record RaiseGrow (Wo : World) (ℓ : LH) (X : Set) (inj : X → H⁰ (Lv ℓ)) : Set where
  field
    raise  : X → Wd Wo → Wd Wo
    g-at   : ∀ x w → β Wo ℓ (raise x w) ≡ (β Wo ℓ w ⊞⁰ inj x)
    g-grow : ∀ y x w → Σ (H⁰ (Lv y)) (λ e → β Wo y (raise x w) ≡ (β Wo y w ⊞⁰ e))
open RaiseGrow public
```

接长之后原来的界是第一位置 (对一切层号、一切世界; 走进 $\Omega$-节点时取最小坐标).

```agda
⊞⁰-fst : ∀ y (a b : H⁰ (Lv y)) {u} → cv y a ⊲[ u ] cv y (a ⊞⁰ b)
⊞⁰-fst y a z⁰ = hself
⊞⁰-fst y a (s⁰ b) = hsuc (⊞⁰-fst y a b)
⊞⁰-fst y a (l⁰ f) = hlim 0 (⊞⁰-fst y a (f 0))
⊞⁰-fst y a (Ω⁰ κ g) {u} = hLim {S = Lv⋆ y} (botBd⋆ y κ u) (⊞⁰-fst y a (g (bot⋆ y κ)))
```

可数的增量原样进任一层 (`Lv lz` 没有种类, 所以没有 $\Omega$-节点).

```agda
embA : ∀ y → H⁰ (Lv lz) → H⁰ (Lv y)
embA y z⁰ = z⁰
embA y (s⁰ a) = s⁰ (embA y a)
embA y (l⁰ f) = l⁰ (λ n → embA y (f n))
embA y (Ω⁰ () g)

growA : ∀ ℓ → RaiseGrow GWo ℓ (H⁰ (Lv lz)) (embA ℓ)
growA ℓ = record
  { raise = λ x w y → w y ⊞⁰ embA y x
  ; g-at = λ x w → refl
  ; g-grow = λ y x w → embA y x , refl }
```
