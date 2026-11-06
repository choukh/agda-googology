# 结构关系, 第十五轮的否定 (三): `nκ` 在目标层对 $(0,1)$ 上也是 "回灌对保留"; `κˣ` 在 `SemX²` 下不可靠

> 不读记号. 入口 [StrRel15N](StrRel15N.lagda.md). 对着接口 [StrRel15If](StrRel15If.lagda.md) (定稿 2026-11-05 10:48) 写. 实例 $\Lambda_1=1$, 同 [StrRel15NNode](StrRel15NNode.lagda.md) 的目标对 $(T_0,T_1)$ 与前提 (`YN`, `jN`, `Z₀`, `hZ`, `cp00`).
>
> `nκ` 没有坐标层, 但折叠对它也按目标层分两种 (`HtFeedFold.RKy`): 目标是第 $0$ 层时**回灌** (输出 `nl …`), 别的层时**保留** (输出 `Kp` 的读数 `⨾ nκ …`). 所以只要 `TX` 允许目标层对 $(0,t')$ ($t'\neq 0$), 同一个 `nκ` 两边的读数就是 "极限" 对 "前缀 ⨾ `nκ`". 取 `xK = nκ tt (λ _ _ → n1)` (层 $1$), 运行路径 `self`, 目标 $T_1$ 的世界路径 `self`: `Kp` 走过的路径是 `self`, 读数是 `n0`; 右边的读数字面上是 `n0 ⨾ nκ tt …`.
>
> 1. **(定理) `¬nl-n0κ`**: `RelX t t′` 不含 (`nl e`, `n0 ⨾ nκ zz u`) (唯一可能的 `prˣ` 要 `nl e` 对 `n0`, 没有这样的构造子).
> 2. **(定理) `relK`, `¬semK²`**: `RelX Λ₁ Λ₁ tt tt xK xK` 成立 (`κˣ`, 分支 `n1ˣ`), `SemX² Λ₁ Λ₁ tt tt xK xK` 不成立 (前提全部可满足). 所以 "`RelX` ⇒ `SemX²`" 在 `κˣ` 一句也不成立, 与节点一句 (`StrRel15NNode.¬semX²`) 独立: 这里没有 `ni`, 没有坐标层.
> 3. **(定理) `NoNlK`, `refl-nlK`**: 任何没有 (`nl e`, `n0 ⨾ nκ zz u`) 推导的关系族, 都不能把这两个读数相关, 对一切状态、动作、上下文.
>
> **构造一路为什么需要.** `SemX²` 对 `nκ` 对的情形是 `κˣ` 的可靠性 (接口 §4 的语义, §3 的 `LawKp`/`LawKb` 正是为它准备的); 结论 `OA²` 在一切 `TX` 对上比, 含 $(0,t')$.
>
> **只否定什么.** 只否定以 `StrRel14If.RelX` 为跨目标层输出关系时, 同一个 `nκ` 的 `SemX²` (从而 `κˣ` 的可靠性); 第 3 条否定缺这条推导的任何关系族. **不否定** `LawKp`, `LawKb` 本身 (它们只说 `Kp`/`Kb` 两种输出, 不含回灌; 本文没有处理), 不否定加了 "回灌对保留" 规则之后的版本, 不否定同目标层的 `κ` 语义. 没有推出 LPO/WLPO 或判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel15NKap where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hself; D; NZ; n0; n1; _⨾_; nl; nκ; accL)
open import OCF.Align.StrRel13Val using (cp00)
open import OCF.Align.StrRel14If (hs hz) tt using (RelX; n0ˣ; n1ˣ; prˣ; κˣ)
open import OCF.Align.StrRel15If (hs hz) tt
open import OCF.Align.StrRel15NNode using (Λ₁; T₀; T₁; tx01; YN; jN; Z₀; hZ; RelT2)
open P using (St; yc; Run; Ig)

xK : D Λ₁ azero
xK = nκ tt (λ _ _ → n1)
```

## 1 "回灌对保留" 不在 `RelX` 里

```agda
¬nl-n0κ : ∀ {t t′ V V′} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D t V} {zz : NZ t′} {u : ∀ {c} → V′ ⊲ c → Lg c → D t′ c} →
          ¬ RelX t t′ lV lV′ (nl e) (n0 ⨾ nκ zz u)
¬nl-n0κ (prˣ ())
```

## 2 同一个 `nκ`: `RelX` 成立, `SemX²` 不成立

```agda
relK : RelX Λ₁ Λ₁ tt tt xK xK
relK = κˣ (λ p p′ lc lc′ cp → n1ˣ)

¬semK² : ¬ SemX² Λ₁ Λ₁ tt tt xK xK
¬semK² s = ¬nl-n0κ (s tt tt (accL Λ₁) (accL Λ₁) hself hself C.self C.self cp00 Z₀ Z₀ (hZ Λ₁ Λ₁) n0 n0 n0ˣ YN YN jN T₀ T₁ tx01)
```

## 3 任何缺这条推导的关系族都不行

```agda
NoNlK : RelT2 → Set
NoNlK R = ∀ {t t′ V V′} {lV : Lg V} {lV′ : Lg V′} {e : ℕ → D t V} {zz : NZ t′} {u : ∀ {c} → V′ ⊲ c → Lg c → D t′ c} →
          ¬ R t t′ lV lV′ (nl e) (n0 ⨾ nκ zz u)

nk-RelX : NoNlK RelX
nk-RelX = ¬nl-n0κ

refl-nlK : ∀ (R : RelT2) → NoNlK R → ∀ (A₀ A₀′ : Ig Λ₁ azero) (w w′ : D Λ₁ azero) (Y Y′ : St azero) →
           ¬ R hz Λ₁ tt tt (yc (Run (accL Λ₁) xK C.self tt hself A₀ w Y) T₀) (yc (Run (accL Λ₁) xK C.self tt hself A₀′ w′ Y′) T₁)
refl-nlK R nn A₀ A₀′ w w′ Y Y′ h = nn h
```
