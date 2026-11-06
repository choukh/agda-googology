# 结构关系, 第十五轮 (三): 有限层上的动作前提; `xL`/`xR` 的升升与留留; 一条值的定理

> 不读记号. 入口 [StrRel15](StrRel15.lagda.md). 接口 [StrRel15If](StrRel15If.lagda.md).
>
> 1. **(定理) `ΩRX²`**: 有限高度 (`Fin`: 只由 $0$ 与后继组成) 上, $t\sqsubseteq_\infty t'$ 蕴含 `RelX t t′ (Ωd t) (Ωd t′)`. 于是 (`stepOA²`) `J²` 相关的状态经 `Step` 给出 `OA²` 相关的输出, 动作 `Act` 满足 `HAW²` (`hawAct²`); 分支是常数 `n1` 的节点, 它的分支动作 `Ai` 也满足 `HAW²` (`hawAi`, `Ai` 在常数分支上定义性地化成 `Act`).
> 2. **(定理, 前提可满足) `hY₁`**: 有限的 $\Lambda$ 上, 状态 $Y_1=Y_0\oplus\mathrm{Step}\,Y_0$ (闭项在第一个 `n1` 之后的状态) 与自己 `J²` 相关, 在任意两个世界上.
> 3. **(定理) `rrInst`, `kkInst`**: 实例 $\Lambda_2=2$, `StrRel13Val` 的节点对 `xL` (坐标层 $0$) 与 `xR` (坐标层 $1$), 运行世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`, 状态 $Y_1$: 接口的升升义务 `OblRR²` 与留留义务 `OblKK²` 成立 (由 `StrRel15Node.Zero` 的 `oblRR`, `oblKK`, 前提全部填上).
> 4. **(定理, 值) `valRR`**: 在同一组参数上, 第 $0$ 层目标上两次运行的读数和**左边不超过右边**: $\Sigma_0(\text{xL 的输出})\le\Sigma_0(\text{xR 的输出})$. 对照 `StrRel13Val.¬valX`: 状态换成 `Yv` (第 $0$ 层读 `n1`, 第 $1$ 层读 `n0`) 时同一不等式是假的; `Yv` 不满足 `J²` 的跨目标层分量 (`RelX hz (hs hz) n1 n0` 不成立, `¬Yv`).
>
> **范围.** `valRR` 是关于这一对节点在这一个状态上的值的定理, 不是闭项的严格增长或界. `rrInst`/`kkInst` 只覆盖四种义务中的两种; 另两种在 `RelX` 里不成立 (`StrRel15Bar`), 所以 `SemX² Λ₂ Λ₂ xL xR` 本身不成立 (`StrRel15Bar.¬semXLR`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel15Fin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; ss; D; D₀; n0; n1; _⨾_; nl; ni; Ωd;
  accL; sum)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel14J as J14
import OCF.Align.StrRel15If as If²
import OCF.Align.StrRel15Node as Nd
open import OCF.Align.StrRel14NegNode using (module G)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; r₁; xL; xR; Yv; cp00)
```

## 1 有限高度

```agda
Fin : H → Set
Fin hz = ⊤
Fin (hs b) = Fin b
Fin (hl f) = ⊥
Fin (hΩ g) = ⊥

fin⊲ : ∀ {a b W} → a ⊲[ W ] b → Fin b → Fin a
fin⊲ hself f = f
fin⊲ (hsuc p) f = fin⊲ p f
fin⊲ (hlim n p) ()
fin⊲ (hLim e p) ()
```

## 2 对一切有限的 $\Lambda$: $\Omega_t$ 跨层相关, 动作前提, 状态 $Y_1$

```agda
module FinΛ (Λ : H) (lΛ : LgH Λ) (fΛ : Fin Λ) where
  open Rk Λ lΛ using (_⊑∞_; s∞; u∞; tr∞)
  open If Λ lΛ using (RelX; n0ˣ; n1ˣ; ⨾ˣ; nlˣ; prˣ; niˣ)
  open J14 Λ lΛ using (NE; here; rgt0)
  open If² Λ lΛ using (TX; OA²; R²; J²; HAW²)
  module Q = At Λ lΛ
  open Q using (Tg; tm; St; Df; yc; d; Step; Act; Y₀; _⊕⟨_⟩_; Ai; Ig; LW)

  pred⊑ : ∀ {b b′} → hs b ⊑∞ hs b′ → b ⊑∞ b′
  pred⊑ s∞ = s∞
  pred⊑ (u∞ h) = tr∞ (u∞ s∞) h

  ΩRX² : ∀ {t t′} → Fin t → Fin t′ → t ⊑∞ t′ → ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → RelX t t′ lW lW′ (Ωd t {W}) (Ωd t′ {W′})
  ΩRX² {t = hz} {t′ = hz} f f′ h = n1ˣ
  ΩRX² {t = hz} {t′ = hs b′} f f′ h = prˣ n1ˣ
  ΩRX² {t = hs b} {t′ = hz} f f′ ()
  ΩRX² {t = hs b} {t′ = hs b′} f f′ h = ⨾ˣ n1ˣ (niˣ {r = ss hself} {r′ = ss hself} (pred⊑ h) (λ p p′ lc lc′ cp y y′ hb → n1ˣ))

  stepOA² : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} {Y : St W} {Y′ : St W′} → J² lW lW′ Y Y′ → OA² lW lW′ (Step Y) (Step Y′)
  stepOA² hY T T′ tx = nlˣ (λ _ → ⨾ˣ (ΩRX² (fin⊲ (tm T) fΛ) (fin⊲ (tm T′) fΛ) (proj₂ tx)) (proj₁ (proj₁ hY) T T′ tx))

  hawAct² : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW² L L′ lW lW′ Act Act
  hawAct² L L′ p p′ l l′ cp w w′ hw Y Y′ hY = stepOA² hY

  Y₁ : ∀ {W} → Lg W → St W
  Y₁ lW = Y₀ ⊕⟨ lW ⟩ Step Y₀

  hY₁ : ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) → J² lW lW′ (Y₁ lW) (Y₁ lW′)
  hY₁ lW lW′ =
    ((λ T T′ tx → ⨾ˣ n0ˣ (nlˣ (λ _ → ⨾ˣ (ΩRX² (fin⊲ (tm T) fΛ) (fin⊲ (tm T′) fΛ) (proj₂ tx)) n0ˣ))) ,
     ⨾ˣ n0ˣ (nlˣ (λ _ → ⨾ˣ n1ˣ n0ˣ))) ,
    ((λ T → n0 , rgt0 here) , (λ T → n0 , rgt0 here))
```

## 3 实例 $\Lambda_2$: `xL`/`xR` 的升升与留留

```agda
open Rk Λ₂ tt using (s∞; u∞)
open If Λ₂ tt using (RelX)
open If² Λ₂ tt using (TX; J²; HAW²)
open FinΛ Λ₂ tt tt using (stepOA²; hawAct²; Y₁; hY₁)
module P = At Λ₂ tt
open P using (Tg; tg; τ₀; St; yc; Run; Act; Ai; kk)

module Z = Nd.Zero Λ₂ tt {lV = tt} {lV′ = tt} r₀ r₁ (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λ₂) (accL hz) (accL Λ₂) (accL (hs hz))
                 C.self C.self hself hself Act Act n0 n0 (Y₁ tt) (Y₁ tt)

-- 常数分支的分支动作: 定义性地化成 Act
hawAi : HAW² hz (hs hz) tt tt Z.A² Z.A²′
hawAi p p′ l l′ cp z z′ hz₁ Y Y′ hY = stepOA² hY

rrInst : Z.OblRR²
rrInst = Z.oblRR cp00 hawAi (hY₁ tt tt)

kkInst : Z.OblKK²
kkInst = Z.oblKK hawAi (hY₁ tt tt)
```

## 4 值: 第 $0$ 层目标上左边不超过右边

```agda
OL OR : St azero → D₀ azero
OL Y = yc (Run (accL Λ₂) xL C.self tt hself Act n0 Y) (τ₀ tt)
OR Y = yc (Run (accL Λ₂) xR C.self tt hself Act n0 Y) (τ₀ tt)

valRR : sum azero (OL (Y₁ tt)) ≤ sum azero (OR (Y₁ tt))
valRR = G.vsumX Λ₂ tt (rrInst (τ₀ tt) (τ₀ tt) (cp00 , s∞) refl refl) (≤-refl azero)

-- 对照: StrRel13Val 的反例状态 Yv 不满足 J² (第 0 层读 n1, 第 1 层读 n0, 跨目标层不相关)
T₁ : Tg azero (hs hz) azero
T₁ = tg C.self (hsuc hself) tt

¬Yv : ¬ J² tt tt Yv Yv
¬Yv ((r , _) , _) with r (τ₀ tt) T₁ (cp00 , u∞ s∞)
... | ()
```
