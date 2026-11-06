# 跨层值同余 (一): `mid₁` 归结为三件

> 不含记号. 入口 [KValC](KValC.lagda.md). `mid₁` (`SumOneClosed.Δ₀` 在目标第 1 层的输出) 字面是 `Aᵐ ⨾ (Pk ⨾ nκ tt uMid)` (`mid≡`, 由检查器归约). 所以它在 `hi` 档自比, 当且仅当 (充分条件, `rf-mid`) 三件:
>
> 1. `Aᵐ` 在 `lo` 档自比: **定理** (`rf-Aᵐ`).
> 2. `Pk` 在 `lo` 档自比 (`PkRf`): 它是读坐标的 `ni`, 要 `DValKn.Kn-Rf` 的跨世界版. 未做.
> 3. `uMid` 对层的值单调 (`MidMono = KMono uMid`): 分支 $u(c)$ 是在世界 $c$ 里对第 $c$ 层的差走链得到的第 1 层树, 要折叠对第 $c$ 层输入的值同余. 未做.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValCMid where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; ss)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (≤-refl)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.LayerTrFold using (mid₁)
open import OCF.Align.CvFoldInst using (Aᵐ; Pk)
open import OCF.Align.KValTree
```

## §1 拆开

```agda
κBr : ∀ {W} → D one W → Bk W
κBr (_ ⨾ (_ ⨾ nκ _ u)) = u
κBr _ = λ _ _ → n0

uMid : Bk one
uMid = κBr mid₁

mid≡ : mid₁ ≡ (Aᵐ ⨾ (Pk ⨾ nκ tt uMid))
mid≡ = refl
```

## §2 三件与归结

```agda
PkRf : Set
PkRf = Rfᵏ lo Pk

MidMono : Set
MidMono = KMono uMid

rf-Aᵐ : Rfᵏ lo Aᵐ
rf-Aᵐ = nl⊑ (λ _ → ⨾⊑ (⨾⊑ n1⊑ (⨾⊑ n0⊑ (ni⊑ (λ _ _ _ _ _ _ _ → n1⊑) (λ _ _ _ _ _ _ _ → n1⊑) (λ _ _ _ _ _ _ _ → n1⊑)))) n0⊑)

rf-mid : PkRf → MidMono → Rfᵏ hi mid₁
rf-mid rP m = ⨾⊑ (up-hi rf-Aᵐ) (⨾⊑ (up-hi rP) (rf-κ (≤-refl one) m))
```
