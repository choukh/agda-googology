# 相干的世界 (六): 改一层的界要判定层号相等

> 不含记号. 入口 [CohW](CohW.lagda.md). 折叠 (`HtTowerFFold`) 在三处造世界: 走法 `Cut₁` 在 $(w_A, b)$ 上取分支, 旧种类的闭包 `KG` 在 $(c, \beta)$ 上, 新种类的闭包 `RunM` 在 $(w_A, v_1)$ 上. 都是 "**把当前世界的某一个分量换掉, 其余不动**". `HtTowerF` 的世界是元组, 换一个分量是投影与配对.
>
> [CohWGl](CohWGl.lagda.md) 的世界 `GW` 是层号上的函数. 换掉层 $y$ 的界, 其余不动, 写成类型就是 `Upd` (两条律: 在 $y$ 上取新值; 在别的层上不变). **`upd→wdec`**: 有 `Upd` 就能对任意两个层号判定 "不相等, 或者不是不相等". 层号块 `LH` 有函数分支 (`ll`, `lΩ`), 判断: 这在 `--safe --without-K` 里写不出 (纸面: 对 $f=$ 常值 $0$ 与 $g_\alpha$, 输出要区分 $\alpha$ 是否内涵地恒为假, 违反连续性). 这一条是**条件定理**, 不是否定: 不说 `Upd` 不存在 (经典逻辑下它存在), 只说造它至少要判定层号相等.
>
> **范围.** 只对 `GW` 上 "恰好换一层, 其余不变" 的更新. 不否定别的折叠设计 (例如分支只取 "一切更大的世界", 不在走法里造世界), 也不否定别的世界形状 (例如沿当前层的层号路径存元组).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CohWUpd where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import OCF.Align.CohWGl using (LH; Lv; H⁰; z⁰; s⁰; l⁰; Ω⁰; GW)

record Upd : Set where
  field
    upd : (y : LH) → H⁰ (Lv y) → GW → GW
    at  : ∀ y b w → upd y b w y ≡ b
    off : ∀ y b w y′ → ¬ (y ≡ y′) → upd y b w y′ ≡ w y′
open Upd public

w₀ : GW
w₀ _ = z⁰
```

把层 $y$ 的界换成 $1$, 看层 $y'$ 上的值: 是 $0$ 就不相等 (相等会把 $1$ 搬过来), 不是 $0$ 就不是不相等 (不相等时值不变, 是 $0$).

```agda
z≢s : ∀ {S} {h : H⁰ S} → z⁰ ≡ s⁰ h → ⊥
z≢s ()

module _ (U : Upd) where
  look : ∀ y y′ (h : H⁰ (Lv y′)) → upd U y (s⁰ z⁰) w₀ y′ ≡ h → ¬ (y ≡ y′) ⊎ ¬ ¬ (y ≡ y′)
  look y y′ z⁰ e = inj₁ (λ { refl → z≢s (trans (sym e) (at U y (s⁰ z⁰) w₀)) })
  look y y′ (s⁰ h) e = inj₂ (λ ne → z≢s (trans (sym (off U y (s⁰ z⁰) w₀ y′ ne)) e))
  look y y′ (l⁰ f) e = inj₂ (λ ne → nz (trans (sym (off U y (s⁰ z⁰) w₀ y′ ne)) e))
    where
    nz : z⁰ ≡ l⁰ f → ⊥
    nz ()
  look y y′ (Ω⁰ κ g) e = inj₂ (λ ne → nz (trans (sym (off U y (s⁰ z⁰) w₀ y′ ne)) e))
    where
    nz : z⁰ ≡ Ω⁰ κ g → ⊥
    nz ()

  upd→wdec : ∀ y y′ → ¬ (y ≡ y′) ⊎ ¬ ¬ (y ≡ y′)
  upd→wdec y y′ = look y y′ (upd U y (s⁰ z⁰) w₀ y′) refl
```
