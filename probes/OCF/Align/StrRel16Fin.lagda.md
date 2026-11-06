# 结构关系, 第十六轮 (四): 有限层上 `RelX⁺` 的动作前提与状态 $Y_1$

> 不读记号. 入口 [StrRel16](StrRel16.lagda.md). 接口 [StrRel16If](StrRel16If.lagda.md).
>
> **(定理) `ΩRX²⁺`, `stepOA²⁺`, `hawAct²⁺`, `hY₁⁺`**: `StrRel15Fin.FinΛ` 的同名定理换成 `RelX⁺`/`J²⁺`/`HAW²⁺`, 证明逐句相同 (只用旧的构造子). 对一切有限的 $\Lambda$ (`StrRel15Fin.Fin`: 只由 $0$ 与后继组成).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel16Fin where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hself; ss; D; n0; n1; _⨾_; nl; Ωd)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel16If as If³
open import OCF.Align.StrRel15Fin using (Fin; fin⊲)

module FinΛ⁺ (Λ : H) (lΛ : LgH Λ) (fΛ : Fin Λ) where
  open Rk Λ lΛ using (_⊑∞_; s∞; u∞; tr∞)
  open J14 Λ lΛ using (NE; here; rgt0)
  open If³ Λ lΛ
  open P using (Tg; tm; St; Df; yc; d; Step; Act; Y₀; _⊕⟨_⟩_)

  pred⊑ : ∀ {b b′} → hs b ⊑∞ hs b′ → b ⊑∞ b′
  pred⊑ s∞ = s∞
  pred⊑ (u∞ h) = tr∞ (u∞ s∞) h

  ΩRX²⁺ : ∀ {t t′} → Fin t → Fin t′ → t ⊑∞ t′ → ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → RelX⁺ t t′ lW lW′ (Ωd t {W}) (Ωd t′ {W′})
  ΩRX²⁺ {t = hz} {t′ = hz} f f′ h = n1⁺
  ΩRX²⁺ {t = hz} {t′ = hs b′} f f′ h = pr⁺ n1⁺
  ΩRX²⁺ {t = hs b} {t′ = hz} f f′ ()
  ΩRX²⁺ {t = hs b} {t′ = hs b′} f f′ h = ⨾⁺ n1⁺ (ni⁺ {r = ss hself} {r′ = ss hself} (pred⊑ h) (λ p p′ lc lc′ cp y y′ hb → n1⁺))

  stepOA²⁺ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J²⁺ lW lW′ Y Y′ → OA²⁺ lW lW′ (Step Y) (Step Y′)
  stepOA²⁺ hY T T′ tx = nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) fΛ) (fin⊲ (tm T′) fΛ) (proj₂ tx)) (proj₁ (proj₁ hY) T T′ tx))

  hawAct²⁺ : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW²⁺ L L′ lW lW′ Act Act
  hawAct²⁺ L L′ p p′ l l′ cp w w′ hw Y Y′ hY = stepOA²⁺ hY

  Y₁ : ∀ {W} → Lg W → St W
  Y₁ lW = Y₀ ⊕⟨ lW ⟩ Step Y₀

  hY₁⁺ : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) → J²⁺ lW lW′ (Y₁ lW) (Y₁ lW′)
  hY₁⁺ lW lW′ =
    ((λ T T′ tx → ⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) fΛ) (fin⊲ (tm T′) fΛ) (proj₂ tx)) n0⁺))) ,
     ⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ n1⁺ n0⁺))) ,
    ((λ T → n0 , rgt0 here) , (λ T → n0 , rgt0 here))
```
