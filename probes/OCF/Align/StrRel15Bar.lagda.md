# 结构关系, 第十五轮 (四): 第一个障碍: `RelX` 没有 "节点对极限" 与 "极限对节点"

> 不读记号. 入口 [StrRel15](StrRel15.lagda.md). 接口 [StrRel15If](StrRel15If.lagda.md). 本文是构造一路的障碍记录, 写成编译过的否定; 每条只否定写明的形状.
>
> 实例 $\Lambda_2=2$, 节点 `xL` (坐标层 $0$), `xR` (坐标层 $1$), 分支常数 `n1`, 运行世界 $0$, 路径 `self`, 动作 `Act`, 上下文 `n0`, 状态 $Y_1$. 这组参数满足 `SemX²` 的全部前提 (`StrRel15Fin`: `hawAct²`, `hY₁`, `cp00`).
>
> 1. **(否定) `¬oblKR`, `¬oblRK`**: 在这组参数上, 接口的左留右升义务 `OblKR²` 与左升右留义务 `OblRK²` 不成立. `OblKR²`: 目标对 (第 $1$ 层, 第 $1$ 层), 左边 `rkT` 是 `keep (ss hself)`, 右边是 `rise` (两个等式都是 `refl`), 输出是 `ni …` 对 `nl …`; `OblRK²`: 目标对 (第 $0$ 层, 第 $2$ 层), 左 `rise` 右 `keep`, 输出是 `nl …` 对 `ni …`. `RelX` (`StrRel14If.LeX`) 的八个构造子里没有一个的两边是这样的头 (`n0ˣ` 要左边 `n0`, `nlˣ` 要两边都 `nl`, `prˣ` 要右边 `⨾`, `niˣ` 要两边都 `ni`, …), 所以不论分支与状态如何, 这两种义务在实际出现时都是假的.
> 2. **(否定) `¬semXLR`, `¬NodeSound²`, `¬NodeSound²₀`**: 由第 1 条, `SemX² Λ₂ Λ₂ xL xR` 不成立, 接口的 `NodeSound²` 与它的左坐标层为 $0$ 的特例 `NodeSound²₀` 都不成立.
> 3. **(否定) `¬semXLL`, `¬sem∀²`**: 同一个节点 `xL` 与自己: `RelX Λ₂ Λ₂ xL xL` 成立 (`relLL`, 同层 `niˣ`), 但 `SemX²` 不成立. 目标对 (第 $0$ 层, 第 $1$ 层): 左边升 (坐标层 $0\sqsubseteq 0$), 右边留 ($0\sqsubset 1$), 输出 `nl …` 对 `ni …`. 所以 "`RelX` ⇒ `SemX²`" 对层 $2$ 不成立 (`¬sem∀²`), 与跨坐标层无关: **跨目标层的输出关系 `OA²` 在折叠下不封闭**, 一个与自己相关的节点的输出, 在两个不同的目标层上就不 `RelX` 相关. 于是接口的 `Law⊕` 只能喂 `OA²` 相关的输出, 而折叠给出的输出不都是.
> 4. **(否定) `¬J²Ω`** (实例 $\Omega^{\mathsf H}$, 世界 $1$): 闭项在第一个 `n1` 之后的状态 $Y_1$ **不**与自己 `J²` 相关. 目标对 (第 $1$ 层, 第 $\Omega$ 层): 读数分别以 $\Omega_1=1⨾\mathrm{ni}\ldots$ 与 $\Omega_\Omega=1⨾\mathrm{n\kappa}\ldots$ 开头, `RelX` 没有 `ni` 对 `nκ` 的规则 (`¬ΩΩ`). 所以在 $\Omega^{\mathsf H}$ 上, 接口的状态不变量不含闭项的状态, `HAW²`/`SemX²` 的前提对闭项不可满足; `StrRel14` 接手清单第 6 项 (`HAW Ωᴴ`, `MonoStep Ωᴴ`) 在本接口里走不到.
>
> **只否定什么.** 第 1–3 条否定的是 "以 `StrRel14If.RelX` 为结论关系、在一切 `TX` 目标对 (目标层可不同) 上比输出" 的节点可靠性与 `RelX ⇒ SemX²`. 不否定换一个结论关系 (加 "节点对极限", "极限对节点" 两种规则) 之后的版本; 不否定只在同一目标层上比的 `StrRel14If.SemX` (那里第 3 条的情形不出现, 第 1 条的左留右升仍出现, 即 `StrRel13Kr.¬krX`); 不否定 `StrRel15Node` 的升升与留留. 第 4 条否定的是 "$\Omega^{\mathsf H}$ 上 $Y_1$ 满足 `J²`", 不否定 $\Omega^{\mathsf H}$ 上存在 `J²` 相关的状态.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel15Bar where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (≤-refl)
open import OCF.Align.HtFeedTree using (H; hz; hs; hΩ; hself; hsuc; hLim; ss; D; n0; n1; _⨾_; nl; Ωd; accL)
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ; emb)
open import OCF.Align.HtFeedClosed using (module At; one)
import OCF.Align.StrRel11Rk as Rk
import OCF.Align.StrRel14If as If
import OCF.Align.StrRel15If as If²
open import OCF.Align.StrRel12Al using (CP; cp-self)
open import OCF.Align.StrRel13Val using (Λ₂; r₀; r₁; xL; xR; cp00)
open import OCF.Align.StrRel15Fin using (module FinΛ; module Z; T₁)
```

## 1 实例 $\Lambda_2$: 左留右升与左升右留

```agda
module R₂ = Rk Λ₂ tt
open R₂ using (s∞; u∞)
open If Λ₂ tt using (RelX; n0ˣ; n1ˣ; niˣ)
open If² Λ₂ tt using (SemX²; NodeSound²; NodeSound²₀)
open FinΛ Λ₂ tt tt using (hawAct²; Y₁; hY₁)
module P = At Λ₂ tt
open P using (Tg; tg; τ₀; Act)

T₂ : Tg azero Λ₂ azero
T₂ = tg C.self hself tt

¬oblKR : ¬ Z.OblKR²
¬oblKR ob with ob T₁ T₁ (cp00 , s∞) (ss hself) refl refl
... | ()

¬oblRK : ¬ Z.OblRK²
¬oblRK ob with ob (τ₀ tt) T₂ (cp00 , u∞ (u∞ s∞)) (ss hself) refl refl
... | ()
```

## 2 `xL` 对 `xR`: 节点规则不可靠

```agda
¬semXLR : ¬ SemX² Λ₂ Λ₂ tt tt xL xR
¬semXLR s with s tt tt (accL Λ₂) (accL Λ₂) hself hself C.self C.self cp00 Act Act (hawAct² Λ₂ Λ₂) n0 n0 n0ˣ (Y₁ tt) (Y₁ tt) (hY₁ tt tt)
                 T₁ T₁ (cp00 , s∞)
... | ()

¬NodeSound² : ¬ NodeSound²
¬NodeSound² ns = ¬semXLR (ns r₀ r₁ {u = λ _ _ _ → n1} {u′ = λ _ _ _ → n1} (u∞ s∞) (λ p p′ lc lc′ cp y y′ b → n1ˣ))

¬NodeSound²₀ : ¬ NodeSound²₀
¬NodeSound²₀ ns = ¬semXLR (ns r₀ r₁ {u = λ _ _ _ → n1} {u′ = λ _ _ _ → n1} (u∞ s∞) (λ p p′ lc lc′ cp y y′ b → n1ˣ))
```

## 3 `xL` 对自己: 跨目标层的输出关系在折叠下不封闭

```agda
relLL : RelX Λ₂ Λ₂ tt tt xL xL
relLL = niˣ {r = r₀} {r′ = r₀} s∞ (λ p p′ lc lc′ cp y y′ b → n1ˣ)

¬semXLL : ¬ SemX² Λ₂ Λ₂ tt tt xL xL
¬semXLL s with s tt tt (accL Λ₂) (accL Λ₂) hself hself C.self C.self cp00 Act Act (hawAct² Λ₂ Λ₂) n0 n0 n0ˣ (Y₁ tt) (Y₁ tt) (hY₁ tt tt)
                 (τ₀ tt) T₁ (cp00 , u∞ s∞)
... | ()

¬sem∀² : ¬ (∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D Λ₂ V} {x′ : D Λ₂ V′} → RelX Λ₂ Λ₂ lV lV′ x x′ → SemX² Λ₂ Λ₂ lV lV′ x x′)
¬sem∀² h = ¬semXLL (h relLL)
```

## 4 $\Omega^{\mathsf H}$: 闭项的状态不满足 `J²`

```agda
module RΩ = Rk Ωᴴ Lg-Ωᴴ
open If Ωᴴ Lg-Ωᴴ using () renaming (RelX to RelXΩ; ⨾ˣ to ⨾Ω; prˣ to prΩ; nlˣ to nlΩ)
open If² Ωᴴ Lg-Ωᴴ using () renaming (J² to J²Ω)
module PΩ = At Ωᴴ Lg-Ωᴴ

¬ΩΩ : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → ¬ RelXΩ (hs hz) Ωᴴ lW lW′ (Ωd (hs hz) {W}) (Ωd Ωᴴ {W′})
¬ΩΩ (⨾Ω _ ())
¬ΩΩ (prΩ ())

¬seg : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} → ¬ RelXΩ (hs hz) Ωᴴ lW lW′ (Ωd (hs hz) {W} ⨾ n0) (Ωd Ωᴴ {W′} ⨾ n0)
¬seg (⨾Ω h _) = ¬ΩΩ h
¬seg (prΩ (⨾Ω () _))
¬seg (prΩ (prΩ ()))

¬rd : ∀ {W W′} {lW : Lg W} {lW′ : Lg W′} →
      ¬ RelXΩ (hs hz) Ωᴴ lW lW′ (n0 ⨾ nl (λ _ → Ωd (hs hz) {W} ⨾ n0)) (n0 ⨾ nl (λ _ → Ωd Ωᴴ {W′} ⨾ n0))
¬rd (⨾Ω _ (nlΩ h)) = ¬seg (h 0)
¬rd (prΩ ())

Y₁Ω : PΩ.St one
Y₁Ω = PΩ.Y₀ PΩ.⊕⟨ tt ⟩ PΩ.Step PΩ.Y₀

-- 第 1 层 (= emb 1) 与第 Ω 层的目标, 都在世界 1
T₁Ω : PΩ.Tg one (hs hz) one
T₁Ω = PΩ.tg C.self (hLim {c = one} C.self hself) tt

TΩ : PΩ.Tg one Ωᴴ one
TΩ = PΩ.tg C.self hself tt

cp11 : CP {V = one} {V′ = one} tt tt C.self tt C.self tt
cp11 = cp-self tt tt (≤-refl one) tt tt

¬J²Ω : ¬ J²Ω tt tt Y₁Ω Y₁Ω
¬J²Ω ((r , _) , _) = ¬rd (r T₁Ω TΩ (cp11 , RΩ.L∞ one RΩ.s∞))
```
