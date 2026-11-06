# 结构关系, 第十七轮 (一): 决定性实验: `valLK` 的同一对输出, 以更小的状态 `YN` 再折叠

> 不读记号. 入口 [StrRel17](StrRel17.lagda.md). 接口 [StrRel17If](StrRel17If.lagda.md).
>
> **(定理, 值) `valLKN`: 通过.** `StrRel16Val` 的那一对输出 (`xL` 以 $Y_1$ 运行, 第 $0$ 层目标上的链极限 `OutL`, 第 $1$ 层目标上的节点 `OutR`), 两边都以状态 `YN` 再折叠 (动作 `Act`, 上下文 `n0`, 读第 $0$ 层): $\Sigma_0(\mathrm{LaterL}^N)\le\Sigma_0(\mathrm{LaterR}^N)$. `YN` 在每个目标 (层 $t$) 上读 $\omega\cdot(\Omega_t⨾0)$, 累计为 `n0` (`StrRel15NNode.YN`, `NegSR16Kap.YN` 的同一形状, 这里在 $\Lambda_2$ 上).
>
> **`YN` 不晚于产生时的状态.** `YN` 不是 $Y_1$ 的向右延长: $Y_1$ 的读数是 $0⨾\omega\cdot(\Omega_t⨾0)$, `YN` 的读数是 $\omega\cdot(\Omega_t⨾0)$, 前者不是后者的左前缀 (`¬laterY₁YN`, 定理). 所以这次再折叠不满足接口的字面时间关系 `Later`; 值的结论仍成立.
>
> **为什么 (定理 `domY₁`).** `valLK` 第 $2$ 步要的状态关系是 "左边产生时的状态 $Y_1$" 对 "右边再折叠时内部节点 $N$ 处的状态 $S^\circ$". 右边的再折叠在 $N$ 之前先经过一个 `n1` (`Ωd 1` 的开头), 所以 $S^\circ=S_0\oplus\mathrm{Step}\,S_0$, 其中 $S_0$ 是那时的状态. **对一切非空 ($\mathsf{NE}$) 的 $S_0$, `J²⁺ Y₁ (S₀ ⊕ Step S₀)` 成立**: $Y_1$ 的读数 $0⨾\omega\cdot(\Omega_t⨾0)$ 落在 $S_0$ 的读数 $⨾\,\omega\cdot(\Omega_{t'}⨾S_0\text{ 的读数})$ 之下, 不看 $S_0$ 是什么. 也就是说: 产生时的状态是最小的 $Y_1$ 时, 第 $2$ 步不需要时间关系. 这一实验因此**不判定**时间关系对一般的产生状态是否必需 (见入口 §2).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel17Val where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (azero; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl)
open import OCF.Align.HtFeedTree using (hz; hs; hself; hsuc; ss; z⊲ᴴ; D; D₀; n0; n1; _⨾_; nl; Ωd; accL; sum)
open import OCF.Align.HtFeedClosed using (module At)
import OCF.Align.StrRel11Rk as Rk
open import OCF.Align.StrRel13Val using (Λ₂; r₀; xL; cp00)
open import OCF.Align.StrRel14J Λ₂ tt using (NE; here; rgt0; ne⊕)
open import OCF.Align.StrRel15Fin using (Fin; fin⊲)
open import OCF.Align.StrRel16Lem using (Lp; here; left; module V0)
open import OCF.Align.StrRel16If Λ₂ tt using (RelX⁺; J²⁺; n0⁺; n1⁺; ⨾⁺; nl⁺; in⁺; In; here; inL; inR; inE)
open import OCF.Align.StrRel16Sem Λ₂ tt using (jPfx⁺; semX00⁺)
open import OCF.Align.StrRel16Fin using (module FinΛ⁺)
open import OCF.Align.StrRel16Node Λ₂ tt using (module Z00)
open import OCF.Align.StrRel16Val using (OutL; OutR)
open import OCF.Align.StrRel17If Λ₂ tt using (Later)

open Rk Λ₂ tt using (s∞)
open FinΛ⁺ Λ₂ tt tt using (ΩRX²⁺; stepOA²⁺; Y₁; hY₁⁺)
open V0 Λ₂ tt using (vsum⁺)
module P = At Λ₂ tt
open P using (Tg; tm; τ₀; St; st; Df; df; d; z; yc; Run; Act; Step; _⊕⟨_⟩_)
```

## 1 状态 `YN`, 与 "产生时的状态 $Y_1$ 被 $S_0\oplus\mathrm{Step}\,S_0$ 支配"

```agda
YN : ∀ {W} → St W
YN = st (df (λ {t} T → nl (λ _ → Ωd t ⨾ n0))) n0

jN : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → J²⁺ lW lW′ (YN {W}) (YN {W′})
jN = ((λ T T′ tx → nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺)) , n0⁺) ,
     ((λ T → n0 , here) , (λ T → n0 , here))

-- 产生时的状态 Y₁ 被 "任意非空状态 S₀ 再加一步" 支配
domY₁ : (S₀ : St azero) → NE S₀ → J²⁺ {azero} {azero} tt tt (Y₁ tt) (S₀ ⊕⟨ tt ⟩ Step S₀)
domY₁ S₀ ne =
  ((λ T T′ tx → ⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ (ΩRX²⁺ (fin⊲ (tm T) tt) (fin⊲ (tm T′) tt) (proj₂ tx)) n0⁺))) ,
   ⨾⁺ n0⁺ (nl⁺ (λ _ → ⨾⁺ n1⁺ n0⁺))) ,
  ((λ T → n0 , rgt0 here) , ne⊕ {lW = tt} S₀ (Step S₀) ne)

-- YN 不晚于 Y₁: 第 0 层目标上的读数 Y₁ 不是 YN 的左前缀
¬lp : ¬ Lp {t = hz} {m = azero} (n0 ⨾ nl (λ _ → n1 ⨾ n0)) (nl (λ _ → n1 ⨾ n0))
¬lp ()

¬laterY₁YN : ¬ Later (Y₁ {azero} tt) YN
¬laterY₁YN (h , _) = ¬lp (h (τ₀ tt))
```

## 2 再折叠

```agda
LaterLN LaterRN : D₀ azero
LaterLN = yc (Run (accL hz) OutL C.self tt (z⊲ᴴ Λ₂) Act n0 YN) (τ₀ tt)
LaterRN = yc (Run (accL (hs hz)) OutR C.self tt (hsuc hself) Act n0 YN) (τ₀ tt)
```

证明的路线与 `StrRel16Val` 相同, 只有两处不同: (i) 右边链的第一项是 `YN` 的读数 $\omega\cdot(1⨾0)$, 没有开头的 `n0`, 所以路径少一个 `inR`; (ii) 第 $2$ 步的状态前提由 `domY₁` 给出 (不是左前缀的延长), 第 $3$ 步的状态前提是 `YN` 向右延长四次 (`jPfx⁺ jN`).

```agda
valLKN⁺ : RelX⁺ hz hz tt tt LaterLN LaterRN
valLKN⁺ =
  in⁺
    (semX00⁺
      (Z00.rr00 {lV = tt} {lV′ = tt} r₀ (ss hself) (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt (accL Λ₂) (accL hz) _ _
         C.self _ hself _ Act _ n0 _ (Y₁ tt) _
         cp00 (λ p p′ l l′ cp z₁ z₁′ hz₁ Y Y′ hY → stepOA²⁺ hY)
         (domY₁ YN (λ T → n0 , here))
         (τ₀ tt) _ (cp00 , s∞) refl refl)
      tt tt (accL hz) _ (z⊲ᴴ Λ₂) _ C.self _ cp00 Act _ (λ p p′ l l′ cp w w′ hw Y Y′ hY → stepOA²⁺ hY) n0 _ n0⁺ YN _
      (jPfx⁺ jN ((λ T → left (left (left (left here)))) , left (left (left (left here)))))
      (τ₀ tt) (τ₀ tt) (cp00 , s∞))
    (inE 0 (inE 0 (inL (inE 1 (inL (inR (inE 0 (inL (inR (inL (inR here)))))))))))

valLKN : sum azero LaterLN ≤ sum azero LaterRN
valLKN = vsum⁺ valLKN⁺ (≤-refl azero)
```
