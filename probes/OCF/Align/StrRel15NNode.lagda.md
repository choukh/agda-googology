# 结构关系, 第十五轮的否定 (二): 同一个节点, 目标层对 $(0,1)$ 上左升右留; `NodeSound²` 不成立

> 不读记号. 入口 [StrRel15N](StrRel15N.lagda.md). 对着接口 [StrRel15If](StrRel15If.lagda.md) (定稿 2026-11-05 10:48) 写. 实例 $\Lambda_1=1$ (`hs hz`, 不含 $\Omega$-极限).
>
> 节点 `x1 = ni (ss hself) (λ _ _ _ → n1)`: 层 $1$, 坐标层 $0$. 运行世界 $0$, 路径 `self`. 目标对 $T_0$ (层 $0$) 与 $T_1$ (层 $1$), 世界都是 $0$, 对齐 `cp00`, 目标层 $0\sqsubseteq_\infty 1$ (`u∞ s∞`): 这是一个 `TX` 对. 在 $T_0$ 上 `rkT` 是 `rise` ($0\sqsubseteq 0$), 在 $T_1$ 上是 `keep (ss hself)` ($0\sqsubset 1$) (`rkT0`, `rkT1`, 都是 `refl`). 左右是**同一个节点**, 坐标层相同 ($k=k'=0$, `s∞`).
>
> 1. **(定理) `¬oblRK²`**: 在这对节点 (两边都是 `x1`) 与任意状态、动作、上下文上, `OblRK²` 不成立.
> 2. **(定理) `¬semX²`, `relX1`**: `RelX Λ₁ Λ₁ tt tt x1 x1` 成立 (`niˣ s∞`, 分支 `n1ˣ`), 而 `SemX² Λ₁ Λ₁ tt tt x1 x1` 不成立. 即接口 §4 的语义对节点**不自反**.
> 3. **(定理) `¬NodeSound²`, `¬NodeSound²₀`**: 接口 §5 的两条可靠性 (一般的, 与左坐标层为 $0$ 的特例) 都不成立.
> 4. **(定理) `NoNlNi`, `refl-nlni`**: 对任意关系族 $R$ (取代 `RelX` 作跨目标层的输出关系), 只要它没有 "左 `nl`, 右 `ni`" 的推导, `x1` 在 $(T_0,T_1)$ 上的两个读数就不 $R$ 相关, 对一切状态、动作、上下文. 所以任何以跨目标层输出关系为结论、对 `x1` 自反的语义, 其关系都必须含一条 "极限对节点" 的规则.
>
> **前提可满足 (全部写出).** 状态 `YN` (每个目标 $T$ (层 $t$) 上读 $\omega\cdot(\Omega_t⨾0)$, 第 $0$ 层分量 `n0`) 满足 `J² tt tt YN YN` (`jN`: `R²` 由 `ΩX` (一切 $t\sqsubseteq_\infty t'$ 上 $\Omega_t$ 与 $\Omega_{t'}$ `RelX` 相关) 给出, `NE` 是 `here`). 动作取零动作 `Z₀` (`HAW²` 由 `n0ˣ` 给出, `hZ`). 上下文 `n0`, `n0ˣ`. 路径 `cp00`. 分支前提 `n1ˣ`.
>
> **构造一路为什么需要这些.** `NodeSound²` 与 `NodeSound²₀` 是接口 §5 写出的可靠性本身; `OblRK²` 是接口为目标层不同时新增的第四种义务. `SemX²` 的结论是 `OA²`, 它在一切 `TX` 对上比; 而 `Law⊕` 要的正是 `OA²` 相关的输出 (语义在 `⨾` 处把前一段的输出加进状态), 所以构造一路要对一切出现在树里的节点给出 `OA²`, 包括两边相同的节点.
>
> **只否定什么.** 只否定: 以 `StrRel14If.RelX` 为跨目标层输出关系的 `SemX²` 对节点的自反性, `NodeSound²`, `NodeSound²₀`, 以及这一对上的 `OblRK²`; 第 4 条否定任何缺 "极限对节点" 推导的关系族. 与状态无关 (第 1, 4 条对一切状态), 所以换不变量救不回. **不否定**: 加了 "极限对节点" 规则的输出关系 (那条规则的语义本文没有碰); 把 `TX` 限制为不跨过节点坐标层的目标对 (判断: 这要按树里出现的节点坐标层选定义域, 不是字面的目标层证据); 同目标层的 `StrRel14` 语义. 没有推出 LPO/WLPO 或判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel15NNode where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; hsuc; ss; StH; Vs; D; n0; n1; _⨾_; nl; ni; Ωd; accL; _⊲[_]_)
open import OCF.Align.StrRel13Val using (cp00)
open import OCF.Align.StrRel11Rk (hs hz) tt using (_⊑∞_; s∞; u∞)
open import OCF.Align.StrRel14If (hs hz) tt using (RelX; n0ˣ; n1ˣ; ⨾ˣ; nlˣ; prˣ; niˣ)
open import OCF.Align.StrRel14J (hs hz) tt using (Lf; here)
open import OCF.Align.StrRel15If (hs hz) tt
open import OCF.Align.StrRel15NDead (hs hz) tt using (¬nlni; module Dead)
open P using (Tg; tg; tm; lm; τ₀; St; st; Df; df; yc; zeroD; Run; Ig; Rk; rkT; rise; keep)

Λ₁ : H
Λ₁ = hs hz

r1 : StH azero hz Λ₁
r1 = ss hself

x1 : D Λ₁ azero
x1 = ni r1 (λ _ _ _ → n1)

T₀ : Tg azero hz azero
T₀ = τ₀ tt

T₁ : Tg azero Λ₁ azero
T₁ = tg C.self hself tt

tx01 : TX tt tt T₀ T₁
tx01 = cp00 , u∞ s∞
```

## 1 两个目标上的种类

```agda
rkT0 : rkT {hz} {hz} {azero} (hsuc hself) (hsuc hself) tt ≡ rise
rkT0 = refl

rkT1 : rkT {hz} {Λ₁} {azero} (hsuc hself) hself tt ≡ keep (ss hself)
rkT1 = refl
```

## 2 `OblRK²` 在同一个节点上不成立 (对一切状态)

```agda
module _ (A₀ A₀′ : Ig Λ₁ azero) (w w′ : D Λ₁ azero) (Y Y′ : St azero) where
  module O = NodeObl² {lV = tt} {lV′ = tt} r1 r1 (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                      (accL Λ₁) (accL hz) (accL Λ₁) (accL hz) C.self C.self hself hself A₀ A₀′ w w′ Y Y′
  module Dd = Dead {lV = tt} {lV′ = tt} r1 r1 (λ _ _ _ → n1) (λ _ _ _ → n1) tt tt
                   (accL Λ₁) (accL hz) (accL Λ₁) (accL hz) C.self C.self hself hself A₀ A₀′ w w′ Y Y′

  ¬oblRK² : ¬ O.OblRK²
  ¬oblRK² = Dd.rk-dead⇒ T₀ T₁ tx01 (ss hself) refl refl
```

## 3 前提: 一个 `J²` 状态, 一个 `HAW²` 动作

```agda
ΩX : ∀ {t t′ m m′} {lm : Lg m} {lm′ : Lg m′} → t ⊲[ m ] Λ₁ → t′ ⊲[ m′ ] Λ₁ → t ⊑∞ t′ →
     RelX t t′ lm lm′ (Ωd t {m}) (Ωd t′ {m′})
ΩX hself hself le = ⨾ˣ n1ˣ (niˣ {r = ss hself} {r′ = ss hself} s∞ (λ p p′ lc lc′ cp y y′ b → n1ˣ))
ΩX hself (hsuc hself) ()
ΩX (hsuc hself) hself le = prˣ n1ˣ
ΩX (hsuc hself) (hsuc hself) le = n1ˣ

YN : ∀ {W} → St W
YN = st (df (λ {t} T → nl (λ _ → Ωd t ⨾ n0))) n0

jN : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → J² lW lW′ (YN {W}) (YN {W′})
jN = ((λ T T′ tx → nlˣ (λ _ → ⨾ˣ (ΩX (tm T) (tm T′) (proj₂ tx)) n0ˣ)) , n0ˣ) ,
     ((λ {t} T → n0 , here) , (λ {t} T → n0 , here))

Z₀ : ∀ {ly W} → Ig ly W
Z₀ _ _ _ _ = zeroD

hZ : ∀ L L′ {W W′} {lW : Lg W} {lW′ : Lg W′} → HAW² L L′ lW lW′ (Z₀ {L} {W}) (Z₀ {L′} {W′})
hZ L L′ p p′ l l′ cp w w′ hw Y Y′ hY T T′ tx = n0ˣ
```

## 4 语义对节点不自反; 两条可靠性都不成立

```agda
relX1 : RelX Λ₁ Λ₁ tt tt x1 x1
relX1 = niˣ {r = r1} {r′ = r1} s∞ (λ p p′ lc lc′ cp y y′ b → n1ˣ)

¬semX² : ¬ SemX² Λ₁ Λ₁ tt tt x1 x1
¬semX² s = ¬nlni (s tt tt (accL Λ₁) (accL Λ₁) hself hself C.self C.self cp00 Z₀ Z₀ (hZ Λ₁ Λ₁) n0 n0 n0ˣ YN YN jN T₀ T₁ tx01)

¬NodeSound² : ¬ NodeSound²
¬NodeSound² ns = ¬semX² (ns r1 r1 {u = λ _ _ _ → n1} {u′ = λ _ _ _ → n1} s∞ (λ p p′ lc lc′ cp y y′ b → n1ˣ))

¬NodeSound²₀ : ¬ NodeSound²₀
¬NodeSound²₀ ns = ¬semX² (ns r1 r1 {u = λ _ _ _ → n1} {u′ = λ _ _ _ → n1} s∞ (λ p p′ lc lc′ cp y y′ b → n1ˣ))
```

## 5 任何缺 "极限对节点" 的关系族都不行

```agda
RelT2 : Set₁
RelT2 = ∀ L L′ {V V′} → Lg V → Lg V′ → D L V → D L′ V′ → Set

NoNlNi : RelT2 → Set
NoNlNi R = ∀ {L L′ V V′ k} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D L V} {r : StH V′ k L′}
             {u : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L′ r W′ → D L′ W′} → ¬ R L L′ lV lV′ (nl e) (ni r u)

nn-RelX : NoNlNi RelX
nn-RelX = ¬nlni

refl-nlni : ∀ (R : RelT2) → NoNlNi R → ∀ (A₀ A₀′ : Ig Λ₁ azero) (w w′ : D Λ₁ azero) (Y Y′ : St azero) →
            ¬ R hz Λ₁ tt tt (yc (Run (accL Λ₁) x1 C.self tt hself A₀ w Y) T₀) (yc (Run (accL Λ₁) x1 C.self tt hself A₀′ w′ Y′) T₁)
refl-nlni R nn A₀ A₀′ w w′ Y Y′ h = nn h
```
