# 可数层的对角, 第二轮 (一): 不改一个分量的升高, 能做到哪里

> 不含记号. 入口 [DiagK2](DiagK2.lagda.md). `L′ 1` 的 `Lev` 部分的世界是 $\prod_{c:H_0}\mathrm{Wd}(\mathrm{Lev}(\mathrm{up}\,c))$; [DiagKLev](DiagKLev.lagda.md) 说恰好改一个分量要弱判定. 这里给一个**不改一个分量**的升高: **一切 `A` 分量加同一个增量** (`mapA f`, $f$ 满足 $a\lhd f\,a$, 例如 $a\mapsto$ `sum a z`, $z$ 是第 0 层输出). 对一切高度 $x$ 的 `Lev x` 递归定义, 不判定任何东西.
>
> - **`mapA-≤`** (定理): `mapA f w` 在 $w$ 之上 (`Lev x` 的世界序), 对一切 $x$, $w$.
> - **`lg-mapA`** (定理): $f$ 保合法时保世界合法.
> - **`mapA-at`** (定理, `refl`): 底种类 (`S₀`) 的界恰好变成 $f$(旧界). 回灌的第 $n$ 格要的正是这个: $x_{n+1}$ 是在旧界上接输出读出来的 (`HtTowerFFold.κc`: `sum (proj₁ W) (z Y)`), 所以 "一切 `A` 界都接上同一个 $z$" 在被回灌的那个分量上与 "只改它" 给出同一个界.
>
> **范围 (判断).** 只对坐标是 `A` 的种类 (底种类与它在 `Lev` 里的一切拷贝). 回灌的目标是第 0 层时 (`KG.RKy hz`), 第 0 层的树不看世界 (`drp`), 所以多升高的分量无害. 对 `Lev` 部分的新种类 (坐标是 `HB (Lev y)`, $y$ 随分量变) 没有同一个增量可加, 回灌的目标层也会看被多升高的分量, `drp₁` 那一步不再成立. 那是下一个障碍, 见入口.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DiagK2Raise where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerNStage using (L′; two)
```

## §1 一切 `A` 分量加同一个增量

```agda
module _ (f : A → A) where
  mapA : ∀ {S} (x : HB S) → Wd (Lev x) → Wd (Lev x)
  mapA hz a = f a
  mapA (hs x) (w , b) = mapA x w , b
  mapA (hl g) w = λ n → mapA (g n) (w n)
  mapA (hΩ κ g) w = λ c → mapA (g c) (w c)

  mapA-at : ∀ (a : A) → mapA {S₀} hz a ≡ f a
  mapA-at a = refl

  module _ (ffst : ∀ a → a ⊲ f a) where
    mapA-≤ : ∀ {S} (x : HB S) (w : Wd (Lev x)) → _≤w_ (Lev x) w (mapA x w)
    mapA-≤ hz a = ffst a
    mapA-≤ (hs x) (w , b) = mapA-≤ x w , hself
    mapA-≤ (hl g) w = λ n → mapA-≤ (g n) (w n)
    mapA-≤ (hΩ κ g) w = λ c → mapA-≤ (g c) (w c)

  module _ (flg : ∀ a → Lg a → Lg (f a)) where
    lg-mapA : ∀ {S} (x : HB S) (w : Wd (Lev x)) → LgW (Lev x) w → LgW (Lev x) (mapA x w)
    lg-mapA hz a l = flg a l
    lg-mapA (hs x) (w , b) (lw , lb) = lg-mapA x w lw , lb
    lg-mapA (hl g) w l = λ n → lg-mapA (g n) (w n) (l n)
    lg-mapA (hΩ κ g) w l = λ c → lg-mapA (g c) (w c) (l c)
```

## §2 在 `L′ (k+1)` 的整个世界上

链分量 `step (L′ k)` 的 `A` 分量按位置, `Lev` 分量用 `mapA`. 这里只写 `Lev` 分量 (链分量是 [DiagKPos](DiagKPos.lagda.md) 的情形).

```agda
module _ (f : A → A) (ffst : ∀ a → a ⊲ f a) (S : KS) where
  raiseLev : Wd (Lev (Ωtop S)) → Wd (Lev (Ωtop S))
  raiseLev = mapA f (Ωtop S)

  raiseLev-≤ : ∀ w → _≤w_ (Lev (Ωtop S)) w (raiseLev w)
  raiseLev-≤ = mapA-≤ f ffst (Ωtop S)

raiseL′ : (f : A → A) → (∀ a → a ⊲ f a) → ∀ k → Wd (Lev (Ωtop (L′ k))) → Wd (Lev (Ωtop (L′ k)))
raiseL′ f ffst k = raiseLev f ffst (L′ k)
```
