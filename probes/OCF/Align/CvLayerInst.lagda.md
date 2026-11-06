# 第 1 层输入的一个实例: `Ai` 满足 `HAᶜ`

> 不含记号. 入口 [CvLayer](CvLayer.lagda.md). 第 1 层输入 `xs = ni self (λ _ _ w → ↑ w)`: 分支就是坐标本身 (第 0 层的差树抬到第 1 层). 它的分支读坐标, 所以 `CvFoldRun.HA` 对它的 `Ai` 不成立; `HAᶜ` 成立 (`AiH`):
>
> - `Up`, `Down`: 折叠在第 1 层上走 `↑ z` 与在第 0 层上走 $z$, 值互相 $\preccurlyeq$ (动作都是 `Step`). 这是对输入树的值单调里最简单的一类: 第 1 层树里没有 `ni`, `nκ`.
> - `AiH`: `Ai` 的一步 = 走 `↑ w`; 由 `Up`, `CvLayerRun.cong0` (在 `Step` 上), `Down`, 对坐标的值单调.
> - **`KL-mono`**: 折叠 $\psi$ 在目标第 1 层上走 `xs` 得到的 `ni` 节点, 分支对坐标的第 0 层值单调, 无前提. 证明用两次 `CvLayerRun`: 一次在 `Step` 上 (给 `AiH`), 一次在 `Ai` 上 (`HAᶜ` 由 `AiH` 给).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CvLayerInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ss; ⊲-tr)
import OCF.Align.CumReadCF as C
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; sum)
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl; ≤-trans)
open import OCF.Align.BrwMidZero using (toA; sum₀)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp)
open import OCF.Align.CvFoldInst using (StepV)
open import OCF.Align.CvHighInst using (br)
import OCF.Align.CvLayerRun as L
```

## §1 抬升与 `Step`

```agda
valA : ∀ {V} → D azero V → A
valA w = sum azero w

↑ : ∀ {W} → D azero W → D one W
↑ n0 = n0
↑ n1 = n1
↑ (x ⨾ y) = ↑ x ⨾ ↑ y
↑ (nl d) = nl (λ n → ↑ (d n))
↑ (ni () u)
↑ (nκ () u)
↑ (nw p x) = nw p (↑ x)

StepA₀ : ∀ {W} → F.Ig (cnt azero) W
StepA₀ _ _ _ Y = F.Step Y

StepA₁ : ∀ {W} → F.Ig (cnt one) W
StepA₁ _ _ _ Y = F.Step Y
```

## §2 第 1 层走 `↑ z` 与第 0 层走 $z$

```agda
module Tr {W : A} (lW : Lg W) (t1 : one ⊲ W) (ac₁ : F.AccY (cnt one)) (ll₁ : one ⊲ W) (A₁ : F.Ig (cnt one) W)
          (ac₀ : F.AccY (cnt azero)) (ll₀ : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) where

  vv : F.St W → B₁ W
  vv Y = S C.self lW bz (F.yc (F.d Y) (inj₁ t1) tt)

  y₁ : ∀ {V} → D azero V → V ⊲ W → D one W → F.St W → D one W
  y₁ z q w Y = F.yc (F.Run ac₁ (↑ z) q lW ll₁ A₁ w Y) (inj₁ t1) tt

  y₀ : ∀ {V} → D azero V → V ⊲ W → D azero W → F.St W → D one W
  y₀ z q w Y = F.yc (F.Run ac₀ z q lW ll₀ A₀ w Y) (inj₁ t1) tt

  module _ (hA : ∀ w₁ w₀ c c′ Y Y′ → c ≼ c′ → vv Y ≼ vv Y′ →
                 S C.self lW c (F.yc (A₁ C.self lW w₁ Y) (inj₁ t1) tt) ≼ S C.self lW c′ (F.yc (A₀ C.self lW w₀ Y′) (inj₁ t1) tt))
           (hA′ : ∀ w₁ w₀ c c′ Y Y′ → c ≼ c′ → vv Y ≼ vv Y′ →
                 S C.self lW c (F.yc (A₀ C.self lW w₀ Y) (inj₁ t1) tt) ≼ S C.self lW c′ (F.yc (A₁ C.self lW w₁ Y′) (inj₁ t1) tt)) where

    Up : ∀ {V} (z : D azero V) q₁ q₀ w₁ w₀ c c′ Y Y′ → c ≼ c′ → vv Y ≼ vv Y′ →
         S C.self lW c (y₁ z q₁ w₁ Y) ≼ S C.self lW c′ (y₀ z q₀ w₀ Y′)
    Up n0 q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = cb
    Up n1 q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = hA w₁ w₀ c c′ Y Y′ cb r
    Up (x ⨾ y) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r =
      Up y q₁ q₀ _ _ _ _ _ _ (Up x q₁ q₀ w₁ w₀ c c′ Y Y′ cb r) (Up x q₁ q₀ w₁ w₀ _ _ Y Y′ r r)
    Up (nl d) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = l≼ (λ n → ≼l n (proj₁ (go n)))
      where
      P₁ = λ n → F.Rpt ac₁ (λ m → ↑ (d m)) q₁ lW ll₁ A₁ w₁ Y n
      P₀ = λ n → F.Rpt ac₀ d q₀ lW ll₀ A₀ w₀ Y′ n
      go : ∀ n → (Sp C.self lW c (λ m → y₁ (d m) q₁ (proj₁ (P₁ m)) (proj₂ (P₁ m))) n ≼
                  Sp C.self lW c′ (λ m → y₀ (d m) q₀ (proj₁ (P₀ m)) (proj₂ (P₀ m))) n) ×
                 (vv (proj₂ (P₁ n)) ≼ vv (proj₂ (P₀ n)))
      go zero = cb , r
      go (suc n) = let (gb , gs) = go n in
        Up (d n) q₁ q₀ _ _ _ _ _ _ gb gs , Up (d n) q₁ q₀ _ _ _ _ _ _ gs gs
    Up (ni () u) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r
    Up (nκ () u) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r
    Up (nw p x) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = Up x (⊲-tr p q₁) (⊲-tr p q₀) w₁ w₀ c c′ Y Y′ cb r

    Down : ∀ {V} (z : D azero V) q₁ q₀ w₁ w₀ c c′ Y Y′ → c ≼ c′ → vv Y ≼ vv Y′ →
           S C.self lW c (y₀ z q₀ w₀ Y) ≼ S C.self lW c′ (y₁ z q₁ w₁ Y′)
    Down n0 q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = cb
    Down n1 q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = hA′ w₁ w₀ c c′ Y Y′ cb r
    Down (x ⨾ y) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r =
      Down y q₁ q₀ _ _ _ _ _ _ (Down x q₁ q₀ w₁ w₀ c c′ Y Y′ cb r) (Down x q₁ q₀ w₁ w₀ _ _ Y Y′ r r)
    Down (nl d) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = l≼ (λ n → ≼l n (proj₁ (go n)))
      where
      P₁ = λ n → F.Rpt ac₁ (λ m → ↑ (d m)) q₁ lW ll₁ A₁ w₁ Y′ n
      P₀ = λ n → F.Rpt ac₀ d q₀ lW ll₀ A₀ w₀ Y n
      go : ∀ n → (Sp C.self lW c (λ m → y₀ (d m) q₀ (proj₁ (P₀ m)) (proj₂ (P₀ m))) n ≼
                  Sp C.self lW c′ (λ m → y₁ (d m) q₁ (proj₁ (P₁ m)) (proj₂ (P₁ m))) n) ×
                 (vv (proj₂ (P₀ n)) ≼ vv (proj₂ (P₁ n)))
      go zero = cb , r
      go (suc n) = let (gb , gs) = go n in
        Down (d n) q₁ q₀ _ _ _ _ _ _ gb gs , Down (d n) q₁ q₀ _ _ _ _ _ _ gs gs
    Down (ni () u) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r
    Down (nκ () u) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r
    Down (nw p x) q₁ q₀ w₁ w₀ c c′ Y Y′ cb r = Down x (⊲-tr p q₁) (⊲-tr p q₀) w₁ w₀ c c′ Y Y′ cb r
```

## §3 输入 `xs` 与它的 `Ai`

```agda
xs : D one one
xs = ni (ss C.self) (λ _ _ w → ↑ w)

KL : D one one → F.St one → D one one
KL w Y = F.yc (F.Run (F.accCn one) xs C.self tt C.self StepA₁ w Y) (inj₁ C.self) tt

kW : azero ⊲ one
kW = ⊲-tr (C.suc C.self) C.self

Ai′ : D one one → F.Ig (cnt azero) one
Ai′ w = F.Ai (F.accCn one) (ss C.self) (λ _ _ w → ↑ w) C.self kW C.self StepA₁ w

val→V0 : ∀ {V} {z z′ : D azero V} → valA z ≤ valA z′ → proj₁ (toA z) ≤ proj₁ (toA z′)
val→V0 {z = z} {z′} h = ≤-trans (proj₂ (sum₀ z)) (≤-trans h (proj₁ (sum₀ z′)))

-- Ai 沿任意路径 π 对坐标的值单调
AiH : ∀ (w : D one one) {W′} (π : one ⊲ W′) (l : Lg W′) (t′ : one ⊲ W′) (ll₀ : azero ⊲ W′) →
      ∀ z z′ c c′ Y Y′ → valA z ≤ valA z′ → c ≼ c′ →
      S C.self l bz (F.yc (F.d Y) (inj₁ t′) tt) ≼ S C.self l bz (F.yc (F.d Y′) (inj₁ t′) tt) →
      S C.self l c (F.yc (Ai′ w π l z Y) (inj₁ t′) tt) ≼ S C.self l c′ (F.yc (Ai′ w π l z′ Y′) (inj₁ t′) tt)
AiH w {W′} π l t′ ll₀ z z′ c c′ Y Y′ le cb r =
  ≼-trans (T.Up hA hA z C.self C.self _ n0 c c′ Y Y′ cb r)
  (≼-trans (proj₁ (L₀.cong0 ha₀ z z′ (val→V0 le)) C.self C.self n0 n0 c′ c′ Y′ Y′ (≤-refl _) (≼-refl _) (≼-refl _))
           (T.Down hA hA z′ C.self C.self _ n0 c′ c′ Y′ Y′ (≼-refl _) (≼-refl _)))
  where
  module T = Tr l t′ (F.accCn one) (⊲-tr C.self π) (F.Ig↾ π StepA₁) (F.accCn azero) ll₀ StepA₀
  hA : ∀ (w₁ : D one W′) (w₀ : D azero W′) e e′ Z Z′ → e ≼ e′ → T.vv Z ≼ T.vv Z′ →
       S C.self l e (F.yc (F.Step Z) (inj₁ t′) tt) ≼ S C.self l e′ (F.yc (F.Step Z′) (inj₁ t′) tt)
  hA w₁ w₀ e e′ Z Z′ eb s = StepV l t′ Z Z′ eb s
  module L₀ = L l t′ (F.accCn azero) ll₀ StepA₀
  ha₀ : L₀.HAᶜ
  ha₀ w w′ e e′ Z Z′ _ eb s = StepV l t′ Z Z′ eb s
```

## §4 折叠走 `xs` 得到的节点

```agda
KL-mono : ∀ (w : D one one) (Y : F.St one) {W′} (p : one ⊲ W′) (l : Lg W′) (z z′ : D azero W′) →
          proj₁ (toA z) ≤ proj₁ (toA z′) → S C.self l bz (br (KL w Y) p l z) ≼ S C.self l bz (br (KL w Y) p l z′)
KL-mono w Y {W′} p l z z′ le =
  AiH w p″ l t′ ll′ z z′ bz bz (Y₂ F.⊕ Rz z) (Y₂ F.⊕ Rz z′) (smono0 le) z≼ walk
  where
  p″ = ⊲-tr C.self p
  t′ = ⊲-tr C.self p
  ll′ = ⊲-tr kW p″
  A′ : F.Ig (cnt azero) W′
  A′ = F.Ig↾ p″ (Ai′ w)
  Y₂ = F.cv p″ l Y
  Rz : D azero W′ → F.Df W′
  Rz z = F.Run (F.accCn azero) z C.self l ll′ A′ n0 Y₂
  smono0 : proj₁ (toA z) ≤ proj₁ (toA z′) → valA z ≤ valA z′
  smono0 h = ≤-trans (proj₁ (sum₀ z)) (≤-trans h (proj₂ (sum₀ z′)))
  module L₁ = L l t′ (F.accCn azero) ll′ A′
  ha₁ : L₁.HAᶜ
  ha₁ v v′ e e′ Z Z′ lv eb s = AiH w (⊲-tr p″ C.self) l t′ ll′ v v′ e e′ Z Z′ lv eb s
  walk : S C.self l bz (F.yc (F.d (Y₂ F.⊕ Rz z)) (inj₁ t′) tt) ≼ S C.self l bz (F.yc (F.d (Y₂ F.⊕ Rz z′)) (inj₁ t′) tt)
  walk = proj₁ (L₁.cong0 ha₁ z z′ le) C.self C.self n0 n0 (S C.self l bz (F.yc (F.d Y₂) (inj₁ t′) tt)) (S C.self l bz (F.yc (F.d Y₂) (inj₁ t′) tt)) Y₂ Y₂ (≤-refl _) (≼-refl _) (≼-refl _)
```

**`KL` 确实是 `ni` 节点** (所以 `br` 取到的是它的分支, `KL-mono` 不是空话):

```agda
IsNi : ∀ {W} → D one W → Set
IsNi (ni _ _) = ⊤
IsNi _ = ⊥

KL-ni : ∀ w Y → IsNi (KL w Y)
KL-ni w Y = tt
```
