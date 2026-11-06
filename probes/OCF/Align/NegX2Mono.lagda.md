# X₂ 与往 `tw n`, 否定一路 (四): `Ψ₂` 不单调

> 不含记号. 入口 [NegX2](NegX2.lagda.md). 只读导入构造一路的 [X2Fold](X2Fold.lagda.md) 与否定一路旧文件 [NegTySupMono](NegTySupMono.lagda.md) 的 `MS.notLim`, 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **`Ψ₂-not-mono` (定理, 对一切实例 `V`, 一切世界, 目标, 当前界).** $1\lhd\lim(0,1,1,\dots)$ (两者都带路径, 无结点), 但 $\Psi_2\,1\not\lhd\Psi_2\,\lim(0,1,1,\dots)$. 原因同 `NegTySupMono.Φ-not-mono` 与 `NegX1UpInst.ΦU-not-mono`: ℕ-极限取部分和, 后继取倍数 (累加). 所以 $X_2$ 的折叠的中间输出 (目标 $t\ne 0$ 时留下结点) 一般不满足 `LgB`; 最终输出 (第 0 层) 的合法由形状给出 (`Sh-Ψ₂`), 不由单调.
>
> **只否定什么.** 只否定 `Ψ₂` 保字面第一位置. **不否定** `Sh-Ψ₂` 与闭项的 `LgB` 证书. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX2Mono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.TySupIf using (module TySupIf)
open import OCF.Align.PathOutIf using (module PathOutIf)
open import OCF.Align.X1UpIf
open import OCF.Align.X2If
import OCF.Align.X2Fold as XF
open import OCF.Align.NegTySupMono using (module MS)

module NotMono₂ (V : X2If) where
  open X2If V
  open X1UpIf U using (P)
  open PathOutIf P
  open TySupIf R using (L)
  open XF V using (Ψ₂; PH₂)

  fI : ℕ → HB XS₂
  fI zero = hz
  fI (suc n) = hs hz

  hI : HB XS₂
  hI = hl fI

  phI : ∀ {W} n → PH₂ W (fI n)
  phI zero = tt
  phI (suc n) = tt

  one⊲hI : ∀ {w} → hs hz ⊲[ w ] hI
  one⊲hI = hlim 1 hself

  Ψ₂-not-mono : ∀ W lW t pt b {w : Wd (L t)} →
    ¬ (Ψ₂ W lW t pt b (hs hz) tt ⊲[ w ] Ψ₂ W lW t pt b hI (phI {W}))
  Ψ₂-not-mono W lW t pt b p =
    MS.notLim R {L t} (λ n → Ψ₂ W lW t pt b (fI n) (phI {W} n)) refl (λ _ → refl) p
```

## 结论 (按档)

- **[定理]** `NotMono₂.fI`, `hI`, `phI` (前提实例: 输入带路径), `one⊲hI`, **`NotMono₂.Ψ₂-not-mono`** (对一切 `V`).
