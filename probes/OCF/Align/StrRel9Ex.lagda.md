# 结构关系, 第九轮 (三): 例子与对照

> 入口见 [StrRel9](StrRel9.lagda.md). 三件事:
>
> 1. **`cv` 读数的形状 (`cv-read`).** `cv` 在 `inj₁` 一支给读数包上前段 `sum-fst U z` (`SumOneFold.cv`), 新世界的极限结构是 `Lg-sum U z lU`, 之后读数在新世界上以 `self` 运行 (`Chn` 的第 0 项). 两边各包一个、旧世界 $U\le U'$、$z\sqsubseteq^{\mathsf P}z'$ (`R∀` 的第二分量) 时, 输出相关. 前提 (`self`, `refl`, `adm-self`) 全部由字面给出.
> 2. **前提可满足且确实用到新规则的例子 (`ex-nw`).** 两边是同一形状的 `nκ` 树, 包上不同的前段 ($1$ 对 $1\cdot 1$, 旧世界任意 $U\le U'$).
> 3. **新语义没有救活不对齐的 `nw` (`¬nwˡᴸ`).** `StrRel8Neg` 的反例在 `SemL` 下照样成立: 新加的三条前提 (树世界处的领先量 `adm-self one one`, 两条 `Lg` 等式 `refl`) 在反例的参数上都满足. 所以 `SemL` 不是靠多加前提把坏规则变成空真的; `nwΣᴸ` 的可靠性来自前段的形状.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel9Ex where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; z⊲; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nκ; nw; sum; sum-fst; Lg-sum)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁)
open import OCF.Align.StrRel4Walk using (aS)
open import OCF.Align.StrRel4Gen using (adm-self)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; o1; pr; vsᴾ)
open import OCF.Align.StrRel5Nest using (stepA; OA; R∀)
open import OCF.Align.StrRel7Coh using (Ch; Y∅; ch∅)
open import OCF.Align.StrRel8Neg using (Nz; nzm; chk-ok; pt0; xL; xR)
open import OCF.Align.StrRel9Snd using (Le; n1ᴸ; κᴸ; nwΣᴸ; SemL; sndᴸ; top)
```

## 1 `cv` 的读数

```agda
cv-read : ∀ {U U′ Z Z′} {lU : Lg U} {lU′ : Lg U′} {z : D azero Z} {z′ : D azero Z′} {x : D one U} {x′ : D one U′} →
          U ≤ U′ → z ⊑ᴾ z′ → Le lU lU′ x x′ → (l₁ : one ⊲ sum U z) (l₁′ : one ⊲ sum U′ z′) →
          ∀ w w′ (Y : F.St (sum U z)) (Y′ : F.St (sum U′ z′)) → Ch Y → R∀ Y Y′ →
          OA (F.Run ac₁ (nw (sum-fst U z) x) C.self (Lg-sum U z lU) l₁ stepA w Y)
             (F.Run ac₁ (nw (sum-fst U′ z′) x′) C.self (Lg-sum U′ z′ lU′) l₁′ stepA w′ Y′)
cv-read hU hz h l₁ l₁′ = top (nwΣᴸ hU hz h) l₁ l₁′ (vsᴾ hz hU)
```

## 2 例子

```agda
xκ : ∀ {U} → D one U
xκ = nκ tt (λ _ _ → n1)

ex-nw : ∀ {U U′} {lU : Lg U} {lU′ : Lg U′} → U ≤ U′ →
        Le {V = asuc U} {V′ = asuc (asuc U′)} (Lg-sum U (n1 {W = azero}) lU) (Lg-sum U′ (n1 {W = azero} ⨾ n1) lU′)
           (nw (sum-fst U (n1 {W = azero})) (xκ {U})) (nw (sum-fst U′ (n1 {W = azero} ⨾ n1)) (xκ {U′}))
ex-nw hU = nwΣᴸ hU (pr {y′ = n1} o1) (κᴸ (λ _ _ _ _ _ → n1ᴸ))

-- 前提可满足: 世界 one ≤ one, 空状态
ex-run : OA (F.Run ac₁ (nw (sum-fst one (n1 {W = azero})) (xκ {one})) C.self (Lg-sum one (n1 {W = azero}) tt) (C.suc C.self) stepA n0 Y∅)
            (F.Run ac₁ (nw (sum-fst one (n1 {W = azero} ⨾ n1)) (xκ {one})) C.self (Lg-sum one (n1 {W = azero} ⨾ n1) tt) (C.suc (C.suc C.self)) stepA n0 Y∅)
ex-run = top (ex-nw (≤-refl one)) (C.suc C.self) (C.suc (C.suc C.self)) (s≤ (s≤ z≤)) n0 n0 Y∅ Y∅ ch∅ ((λ _ _ → z0) , z0)
```

## 3 不对齐的 `nw` 在新语义下仍不可靠

```agda
¬nwˡᴸ : ¬ SemL {V = one} {V′ = one} tt tt (nw (C.suc C.self) xL) xR
¬nwˡᴸ s = noR (nzm (vsᴾ h (z≤ {azero})) yesL)
  where
  τ = inj₁ (z⊲ one)
  h = s tt tt C.self C.self (≤-refl one) C.self C.self (aS C.self tt) refl refl (adm-self one one)
        n0 n0 Y∅ Y∅ ch∅ ((λ _ _ → z0) , z0) τ τ
  yesL : Nz (sum azero (F.yc (F.Run ac₁ (nw (C.suc C.self) xL) C.self tt C.self stepA n0 Y∅) τ tt))
  yesL = chk-ok 6 _ tt
  noR : ¬ Nz (sum azero (F.yc (F.Run ac₁ xR C.self tt C.self stepA n0 Y∅) τ tt))
  noR (n , t) = pt0 n t
```
