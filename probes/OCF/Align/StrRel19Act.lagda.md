# 结构关系, 第十九轮 (一): 决定性实验: 折叠的动作都定义性地属于 `ActS`; `Az` 不属于

> 不读记号. 入口 [StrRel19](StrRel19.lagda.md). 接口 [StrRel19If](StrRel19If.lagda.md) §1.
>
> 1. **(定理) 折叠造动作的六处, 加闭项的起点** (`Sites` 七条, 一切 $\Lambda$): `HtFeedFold` 里传给 `Run` 的动作, 除了原样传下的, 只有 `Ai` 的 `Ig↾ p A₀`, `BNi` 的 `Ig↾ p (Ai …)`, `RKi` 的 rise 句 (与 `Chn`) 的 `Ai …`, `Kp` 的 `Ig↾ wu A₀`, `Kb` 的 `Ig↾ (⊲-tr wu p) A₀`, `κΔ` 的 `Ig↾ (wv c) A₀`. 每一处的类型逐字写出折叠里的那个项, 由 `ActS` 的构造子直接给出: 输入动作属于 `ActS` 时, 造出的动作也属于. 闭项从 `Act` 起 (`HtFeedClosed.ΔΩ`), 所以闭项里实际运行的动作都属于 `ActS`. "只有这七处" 是读 `HtFeedFold` §3 的字面得到的 (判断, 依据定义的文本; 本文对每一处给出编译的类型).
> 2. **(定理) 闭项里的实例**: $\Lambda_\kappa$ 的闭项第一步的 `nκ` 的格 `fκ` 用的动作 (`Kb` 里的 `Ig↾ (⊲-tr self p) Act`), 保留节点的分支动作 `StrRel18Az.AiK` (读累计的那个, `¬noZ-AiK`), $\Lambda_2$ 上障碍那一对的节点 `O` 的分支动作 `StrRel17Time.Core.A²R`: 都属于 `ActS`.
> 3. **(定理, 否定) `actNoZ₂`, `¬ActS-Az`**: 在 $\Lambda_2=2$ 上, 第 $2$ 层的 `ActS` 动作都不读第 $0$ 层累计 (`NoZ`), 因为第 $2$ 层上没有 `sAi` (节点的坐标层是 $2$ 时节点的层要高于 $2$, 而层都在 $\Lambda_2$ 之下, `noAi₂`). `NegSR17RkT.Az` (输出 "累计 ⨾ 1") 读累计, 所以 **`Az` 不属于 `ActS`**. `NegSR18Up.¬UpSoundR` 与 `NegSR17RkT.¬RkSoundT` 的反例都用 `Az` 作产生时的动作 (节点 `r₀` 在第 $2$ 层), 它们不满足接口 `UpSoundS`, `RkSoundZ` 的前提 `ActS A₀`.
>
> **只否定什么.** `¬ActS-Az` 只说那一个动作 (在第 $2$ 层, 世界 $0$) 不在语法里; 不说 `ActS` 的动作都不读累计: 在有 $\Omega$-极限的 $\Lambda_\kappa$ 上, `ActS` 里的 `AiK` 读累计 (`StrRel18Az.¬noZ-AiK`, 本文 `act-AiK` 说它属于 `ActS`).
>
> **前提可满足.** `Sites` 的每一条: 前提 `ActS A₀` 由 `sAct` 满足. `actNoZ₂` 的前提由 `sAct`, `sIg↾` 满足.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel19Act where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hself; hsuc; ss; sl; sL; _⊲[_]_; StH; Vs; D; D₀; n0; n1; _⨾_; AccY; accL; ⊲ᴴ↑; z⊲ᴴ)
import OCF.Align.StrRel19If as If
import OCF.Align.StrRel16If as If³
```

## 1 折叠的六处与闭项的起点 (一切 $\Lambda$)

```agda
module Sites (Λ : H) (lΛ : LgH Λ) where
  open If Λ lΛ using (ActS; sAct; sIg↾; sAi)
  open If³ Λ lΛ using (module P)
  open P using (Ig; Ig↾; Ai; LW; Cl; wv; Act)

  -- 闭项的起点: HtFeedClosed.ΔΩ 以 Act 运行
  top : ∀ {L W} → ActS {L} {W} Act

  -- Ai: 分支的树以 Ig↾ p A₀ 运行
  siteAi : ∀ {ly W W′} (p : W ⊲ W′) {A₀ : Ig ly W} → ActS A₀ → ActS (Ig↾ p A₀)

  -- RKi 的 rise 句 (与 Chn): 链的动作是节点的分支动作
  siteRKi : ∀ {ly W₀ W k} (ac : AccY ly) (ac₁ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
              (q₀ : W₀ ⊲ W) (hk : LW k W) (ll : LW ly W) {A₀ : Ig ly W} (w : D ly W) →
            ActS A₀ → ActS (Ai ac ac₁ r u q₀ hk ll A₀ w)

  -- BNi: 保留节点的分支先以 Ig↾ p (Ai …) 运行输入
  siteBNi : ∀ {ly W₀ W k W′} (ac : AccY ly) (ac₁ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′)
              (q₀ : W₀ ⊲ W) (hk : LW k W) (ll : LW ly W) {A₀ : Ig ly W} (w : D ly W) (p : W ⊲ W′) →
            ActS A₀ → ActS (Ig↾ p (Ai ac ac₁ r u q₀ hk ll A₀ w))

  -- Kp: 走到目标世界
  siteKp : ∀ {ly W W⁺} (wu : W ⊲ W⁺) {A₀ : Ig ly W} → ActS A₀ → ActS (Ig↾ wu A₀)

  -- Kb: nκ 的格
  siteKb : ∀ {ly W W⁺ c} (wu : W ⊲ W⁺) (p : W⁺ ⊲ c) {A₀ : Ig ly W} → ActS A₀ → ActS (Ig↾ (⊲-tr wu p) A₀)

  -- κΔ: 第 0 层回灌的一格
  siteκΔ : ∀ {ly W W₀} (cl : Cl W W₀ ly) {A₀ : Ig ly W} → ActS A₀ → ActS (Ig↾ (wv cl) A₀)

  top = sAct
  siteAi p s = sIg↾ p s
  siteRKi ac ac₁ r u q₀ hk ll w s = sAi ac ac₁ r u q₀ hk ll w s
  siteBNi ac ac₁ r u q₀ hk ll w p s = sIg↾ p (sAi ac ac₁ r u q₀ hk ll w s)
  siteKp wu s = sIg↾ wu s
  siteKb wu p s = sIg↾ (⊲-tr wu p) s
  siteκΔ cl s = sIg↾ (wv cl) s
```

## 2 闭项里的实例

```agda
open import OCF.Align.NegSR16Kap using (Λκ; lΛκ)
import OCF.Align.StrRel18Az as Az18

module Iκ where
  open If Λκ lΛκ using (ActS; sAct; sIg↾; sAi)
  open If³ Λκ lΛκ using (module P)
  open P using (Ig; Ig↾; Act)

  -- fκ (StrRel18Az): Kb 以 Ig↾ (⊲-tr self p) Act 运行
  act-fκ : ∀ {c} (p : azero ⊲ c) → ActS {Λκ} (Ig↾ {W = azero} (⊲-tr C.self p) Act)
  act-fκ p = sIg↾ (⊲-tr C.self p) sAct

  -- 读累计的那个保留节点的分支动作
  act-AiK : ∀ Y w → ActS (Az18.AiK Y w)
  act-AiK Y w = sAi (accL Λκ) (accL (hs hz)) Az18.r (Az18.brK Y w) C.self Az18.hkK hself n0 sAct

open import OCF.Align.StrRel13Val using (Λ₂; r₀)
open import OCF.Align.StrRel17Time using (module Core)
open import OCF.Align.StrRel15Fin using (module FinΛ)

module I₂ where
  open If Λ₂ tt using (ActS; sAct; sIg↾; sAi)
  open If³ Λ₂ tt using (module P)
  open FinΛ Λ₂ tt tt using (Y₁)

  -- 障碍那一对的节点 O 的分支动作
  act-A²R : ActS (Core.A²R (Y₁ tt))
  act-A²R = sAi (accL (hs hz)) (accL hz) (ss hself) (Core.brR (Y₁ tt)) C.self (Core.hk (Y₁ tt)) (hsuc hself) n0 sAct
```

## 3 第 $2$ 层: `ActS` 不读累计; `Az` 不属于 `ActS`

```agda
module L2 where
  open If Λ₂ tt using (ActS; sAct; sIg↾; sAi)
  open If³ Λ₂ tt using (module P)
  open P using (Tg; τ₀; St; st; d; z; yc; Ig; Y₀)
  import OCF.Align.NegSR17RkT as N17

  -- 同 StrRel18If.NoZ (不带 Lg 参数; NoZ lW A₀ 定义性地就是它)
  NoZ′ : ∀ {L W} → Ig L W → Set
  NoZ′ {L} {W} A₀ =
    ∀ {W₁} (p : W ⊲ W₁) (lW₁ : Lg W₁) (w : D L W₁) (Y : St W₁) (z′ : D₀ W₁) {t m} (T : Tg W₁ t m) →
    yc (A₀ p lW₁ w Y) T ≡ yc (A₀ p lW₁ w (st (d Y) z′)) T

  -- 坐标层为 2 的节点不存在 (节点的层要在 Λ₂ = 2 之下)
  noAi₂ : ∀ {W₀ W ly} → StH W₀ Λ₂ ly → ly ⊲[ W ] Λ₂ → ⊥
  noAi₂ (ss (hsuc ())) hself
  noAi₂ (ss P) (hsuc (hsuc ()))
  noAi₂ (sl n P) (hsuc (hsuc ()))
  noAi₂ (sL e P) (hsuc (hsuc ()))

  actNoZ₂ : ∀ {W} {A₀ : Ig Λ₂ W} → ActS A₀ → NoZ′ A₀
  actNoZ₂ sAct p lW₁ w Y z′ T = refl
  actNoZ₂ (sIg↾ p s) p′ = actNoZ₂ s (⊲-tr p p′)
  actNoZ₂ (sAi ac ac₁ r u q₀ hk ll w s) p = ⊥-elim (noAi₂ r ll)

  ¬ActS-Az : ¬ ActS (N17.Az {Λ₂} {azero})
  ¬ActS-Az s with actNoZ₂ s C.self tt n0 Y₀ n1 (τ₀ tt)
  ... | ()
```
