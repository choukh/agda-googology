# 结构关系, 第十轮 (一): `Ai` 与 `Kp` 给上下文包的 `nw`

> 入口见 [StrRel10](StrRel10.lagda.md). 不读记号.
>
> `SumOneFold` 里另外两处给上下文包 `nw`:
>
> - `Ai … w p … = Run (u …) C.self … (nw p w ⨾ Int …)`: $p$ 是 `Ai` 的底世界到动作被调用处的路径. 链 `Chn` 直接调用时 (`Run` 的 `n1` 一句) $p$ = `C.self`; 经 `Ig↾` 时 $p$ 是 `Ig↾` 叠起来的路径 (`Kp` 的 `wu`, `Kb` 的 `⊲-tr wu p`).
> - `Kp … wu … = Walk … (nw wu w) (cv wu Y)`: `RKy` 在目标 $\tau$ 上取 `wu = W⊲wm τ`. 目标在世界之下 (`inj₁`) 时 `W⊲wm τ` = `C.self`; 目标在世界之上 (`inj₂ q`) 时 `wu = q`, 就是**目标路径本身**.
>
> 本文两条:
>
> 1. **`nw-self`** (定理): 前段是 `C.self` 的一对 `nw` 由 `snd-nwA` 直接收下 (对齐 `aS`, 领先量 `adm-self`, 等式 `refl`). 所以链里直接调用的 `Ai`, 与目标在世界之下时的 `Kp`, 都归到 `snd-nwA`.
> 2. **`¬nw-tgt`** (否定, 定理): 两边都包 `nw`, 顶端世界相同 (都是 $1$), 左边底端 $0\le$ 右边底端 $1$, 内层按 `Le` 相关 (`κᴸ`), 顶端的领先量与 `Lg` 等式都满足, `SemL` 仍不成立. 这正是 "目标在世界之上" 时两边目标路径的形状 (前段 = 从世界到目标的路径, 顶端是目标). 所以 `R∀` 若对**一切**目标对取读数关系, `Kp` 的 `nw wu w` 收不下; 目标路径必须作为对齐的数据 (`Al`) 交给语义. 范围: 只否定 "前段只有值的比较 (底端 ≤, 顶端相同)" 的规则; 不否定带前段对齐的版本 (那是 `snd-nwA`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel10Kp where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; z⊲; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.SumOneTree using (D; n0; nw; sum)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁)
open import OCF.Align.StrRel4Walk using (aS)
open import OCF.Align.StrRel4Gen using (adm-self)
open import OCF.Align.StrRel4Pr using (z0; vsᴾ)
open import OCF.Align.StrRel5Nest using (stepA)
open import OCF.Align.StrRel7Coh using (Y∅; ch∅)
open import OCF.Align.StrRel8Neg using (Nz; nzm; chk-ok; pt0; xL; xR)
open import OCF.Align.StrRel9Snd using (Le; n1ᴸ; κᴸ; SemL)
open import OCF.Align.StrRel9Nw using (snd-nwA)
```

## 1 前段是 `self`

```agda
nw-self : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {x : D one W} {x′ : D one W′} →
          SemL lW lW′ x x′ → SemL lW lW′ (nw C.self x) (nw C.self x′)
nw-self {W} {W′} {lW′ = lW′} = snd-nwA (aS C.self lW′) (adm-self W W′) refl refl
```

## 2 目标路径形状的前段: 只有值的比较不够

```agda
hxL : Le {V = azero} {V′ = one} tt tt xL xR
hxL = κᴸ (λ _ _ _ _ _ → n1ᴸ)

¬nw-tgt : ¬ SemL {V = one} {V′ = one} tt tt (nw (C.suc C.self) xL) (nw C.self xR)
¬nw-tgt s = noR (nzm (vsᴾ h (z≤ {azero})) yesL)
  where
  τ = inj₁ (z⊲ one)
  h = s tt tt C.self C.self (≤-refl one) C.self C.self (aS C.self tt) refl refl (adm-self one one)
        n0 n0 Y∅ Y∅ ch∅ ((λ _ _ → z0) , z0) τ τ
  yesL : Nz (sum azero (F.yc (F.Run ac₁ (nw (C.suc C.self) xL) C.self tt C.self stepA n0 Y∅) τ tt))
  yesL = chk-ok 6 _ tt
  noR : ¬ Nz (sum azero (F.yc (F.Run ac₁ xR C.self tt C.self stepA n0 Y∅) τ tt))
  noR (n , t) = pt0 n t
```

规则形式: 内层的前提 `hxL` 可满足, 结论不成立.

```agda
¬rule-tgt : ¬ (Le {V = azero} {V′ = one} tt tt xL xR → SemL {V = one} {V′ = one} tt tt (nw (C.suc C.self) xL) (nw C.self xR))
¬rule-tgt f = ¬nw-tgt (f hxL)
```
