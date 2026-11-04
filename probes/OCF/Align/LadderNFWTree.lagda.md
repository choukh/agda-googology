# 标签世界的树

> 验收用. `ScafLadderQ` 就是 `LadderNFTree`, 只差 §0 与导入. 见 [LadderNFAccept](LadderNFAccept.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNFWTree where

open import Data.Product using (proj₁; _,_)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.ScafLadderZUniform3Base using (Flr; _⊔_; fk; Ev; Top; Bd; Fc; FB; evF; liftEv)
open import OCF.Align.ScafLadderQ public
open import OCF.Align.ScafLadderZUniform4Base public using (_<ᴸ_; zero; suc; tr<)

evη : ∀ {i ℓ} (φ : Flr) (B : Top i ℓ (φ ⊔ fk zero)) η (e : Bd B ⊑ᴵ η) → Ev (Mlev (Fc B) (suc η) (FB B e)) (φ ⊔ fk η)
evη φ B η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)
```
