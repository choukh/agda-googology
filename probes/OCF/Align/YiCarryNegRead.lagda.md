# YiCarryNeg：读回域上的 Ω̂ 反例搜索

**状态：未找到 ReadOmegaCounterexample 的实例，不作否定。**
起点反例见 YiCarryNeg；它不能直接作为本记录的 input，因为该字段要求
LglB。以下逐项检查候选是否真在读回域，并记录目标 Carry 的状态。
局部正证书只用于排除这些候选，不改接口、不实现任何修补。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryNegRead where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as Y
import OCF.Align.YiCarryV0 as V0
import OCF.Align.YiCarryNeg as N
import OCF.Align.YiK2Stop as S
import OCF.Align.YiK1 as K
import OCF.Align.RR4RegOmega2 as R
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase
  using (Below; one; more; e-first; e-branch)
```

## 1. Ω̂ 2 的读回域：不能偷用 V0 的坏坐标

Ω̂ 2 的 lc 分支坐标位于 Raw 1，而非 Raw (Ω̂ 2)。
它对应 ReadOmegaCounterexample 的 index=1。
环境 Reg 1、Below 1 (Ω̂ 1)、Carry (Ω̂ 1) 都有闭实例。
V0 的坏坐标过原守卫，但其 input-B 字段编译否定。

```agda
index1 : F.LF
index1 = F.suc F.zero

index1-reg : Reg index1
index1-reg = tt

index1-root : Below index1 (V.Ω̂ index1)
index1-root = one e-first

index1-omega-carry : Y.Carry (V.Ω̂ index1)
index1-omega-carry = Y.tw2-carry

v0-input-guard : F.Gd index1 (V.cO index1) V0.bad-coordinate
v0-input-guard = V0.bad-coordinate-guard

no-v0-input-B : Y.LglB index1 V0.bad-coordinate → ⊥
no-v0-input-B (l , lc , bc , bt , bg) = S.no-bound-legal lc
```

## 2. 下界换成合法 1 的常 top 分支：目标 Carry 可填

这里是另一个搜索候选，不改 V0：下界是合法的 raw1，
读回仍为 lc，第一支与所有分支是 tw 2；再取 Ω̂ 后均为 tw 3。
失败字段 fails 无法由该候选给出，因为目标 Carry 已有闭证据。

```agda
constant-input : F.Raw index1
constant-input = G.lc (inj₁ tt) R.raw1 G.top (λ _ _ → G.top)

constant-input-lgl : F.Lgl index1 constant-input
constant-input-lgl =
  (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

constant-input-guard : F.Gd index1 (V.cO index1) constant-input
constant-input-guard = inj₂ (inj₁ refl) , constant-input-lgl

constant-input-B : Y.LglB index1 constant-input
constant-input-B = constant-input-lgl , tt , tt , tt , (λ _ _ → tt)

constant-target-form : V.Ω̂ (V.up index1 constant-input) ≡
  F.lc F.zero R.raw1 (V.tw 3) (λ _ _ → V.tw 3)
constant-target-form = refl

constant-target-reg : Reg (V.Ω̂ (V.up index1 constant-input))
constant-target-reg = more (more (one e-first) e-first) e-first ,
  tt , K.tw3-reg , (λ _ _ → K.tw3-reg)

constant-target-carry : Y.Carry (V.Ω̂ (V.up index1 constant-input))
constant-target-carry = constant-target-reg , tt , Y.tw3-carry ,
  (λ _ _ _ → Y.tw3-carry)
```

## 3. 同域的后继 top：根路径经过原 Ω 分支，目标也可填

input=suc top 的读回是 suc (tw 2)。其 Ω̂ 的 lc 层参数已是
tw 2，不能用第 0 层空嵌套条件敷衍。Reg 的根路径用 Ω̂ 2
在 suc top 坐标处的分支，再接 tw 3 在 raw2 坐标处的分支。
高层读回 Carry 则只应用冻结接口已有的条件定理，三项环境均实填。

```agda
successor-input : F.Raw index1
successor-input = G.suc G.top

successor-input-guard : F.Gd index1 (V.cO index1) successor-input
successor-input-guard = inj₂ (inj₁ refl) , tt

successor-input-B : Y.LglB index1 successor-input
successor-input-B = tt , tt

suc-tw2-below-tw3 : Below (F.suc (V.tw 2)) (V.tw 3)
suc-tw2-below-tw3 = more (one (e-branch successor-input successor-input-guard))
  (e-branch R.raw2 R.raw2-guard)

successor-target-reg : Reg (V.Ω̂ (V.up index1 successor-input))
successor-target-reg = more suc-tw2-below-tw3 e-first ,
  R.Ω₁-reg , K.tw3-reg ,
  (λ η e → K.guard-read-reg (V.tw 2) R.Ω₁-reg (one e-first) K.tw3-reg η e)

successor-target-carry : Y.Carry (V.Ω̂ (V.up index1 successor-input))
successor-target-carry = successor-target-reg , tt , Y.tw3-carry ,
  (λ η e b → Y.guard-read-carry (V.tw 2) R.Ω₁-reg
    (one e-first) Y.tw3-carry η e b)
```

## 4. tw 3 的读回域：起点反例不能充当输入；top 仍未决

tw 3 的高层坐标参数是 tw 2。因此下面用 index=tw 2，
其环境正是已编译的 Reg (tw 2)、Below (tw 2) (tw 3)、
Carry (tw 3)。YiCarryNeg 的坏坐标虽过原守卫，却缺 input-B。
再试规范 top：所有输入字段均实填，目标字面就是 Carry (tw 4)。
本篇没有得到它的证明，也没有得到它的否定函数。

```agda
index-tw2-reg : Reg (V.tw 2)
index-tw2-reg = R.Ω₁-reg

index-tw2-root : Below (V.tw 2) (V.Ω̂ (V.tw 2))
index-tw2-root = one e-first

index-tw2-omega-carry : Y.Carry (V.Ω̂ (V.tw 2))
index-tw2-omega-carry = Y.tw3-carry

high-bad-input-guard : F.Gd (V.tw 2) (V.cO (V.tw 2)) N.bad-coordinate
high-bad-input-guard = inj₂ (inj₁ refl) , N.bad-coordinate-lgl

no-high-bad-input-B : Y.LglB (V.tw 2) N.bad-coordinate → ⊥
no-high-bad-input-B b = N.no-bad-coordinate-nested (proj₂ b)

top-input-guard : F.Gd (V.tw 2) (V.cO (V.tw 2)) G.top
top-input-guard = inj₁ refl , tt

top-input-B : Y.LglB (V.tw 2) G.top
top-input-B = Y.top-B (V.tw 2)

top-target-form : V.Ω̂ (V.up (V.tw 2) G.top) ≡ V.tw 4
top-target-form = refl
```

**卡点（判断／未完成的义务）。** top 候选的 fails 要求
`Carry (tw 4) → ⊥`；仅把已有 tw 3 证明再套一次并不生产这个函数。
展开 tw 4，根下界仍是合法且带 Nested 的 raw1，第一支 Carry (tw 3)
也已有。未决的是 Reg (tw 4) 的全原分支，以及 Carry 分支中的
`Carry (Ω̂ (Ω̂ (up 0 η)))`，其中 η 过原 raw1 守卫且带 LglB。
原 Reg 检查全部合法坐标，不能因 Carry 限到 LglB 就缩减其量词。
本篇未找到使这些字段失败的闭坐标；这只是搜索停点，不是封闭定理或否定。

对 index=1 还试了规范 top：其目标就是已编译的 Carry (tw 3)。
以下是这一候选的完整输入与目标证书。

```agda
low-top-input-guard : F.Gd index1 (V.cO index1) G.top
low-top-input-guard = inj₁ refl , tt

low-top-input-B : Y.LglB index1 G.top
low-top-input-B = Y.top-B index1

low-top-target-carry : Y.Carry (V.Ω̂ (V.up index1 G.top))
low-top-target-carry = Y.tw3-carry
```

这些闭实例不是以有限样本证明一般 Ω̂ 封闭；未实现完整记录，
也未声称 ReadOmegaCounterexample 为空。没有搜索任意层的穷尽性结论。

## 5. 真正以 Ω̂ 2 的坐标读回作层号

上面 index=1 是底层核对。现在把 constant-input 的读回本身作为
ReadOmegaCounterexample.index：`read-index=lc 0 raw1 (tw 2) (const (tw 2))`。
它是 Ω̂ 2 的带 LglB 坐标读回；其 Reg、root、omega-carry 与 top 输入
均有闭证据，未借用待证的全塔。root 路径先在 Ω̂ 2 找到 read-index，
再在 tw 3 找到 Ω̂ 2，最后接到 Ω̂ read-index 的第一支。

```agda
read-index : F.LF
read-index = V.up index1 constant-input

read-index-reg : Reg read-index
read-index-reg = K.guard-read-reg index1 index1-reg index1-root R.Ω₁-reg
  constant-input constant-input-guard

read-index-root : Below read-index (V.Ω̂ read-index)
read-index-root = more
  (more (one (e-branch constant-input constant-input-guard))
    (e-branch R.raw2 R.raw2-guard)) e-first

read-index-omega-carry : Y.Carry (V.Ω̂ read-index)
read-index-omega-carry = constant-target-carry

read-index-input-guard : F.Gd read-index (V.cO read-index) G.top
read-index-input-guard = inj₁ refl , tt

read-index-input-B : Y.LglB read-index G.top
read-index-input-B = Y.top-B read-index

read-index-target-form : V.Ω̂ (V.up read-index G.top) ≡
  F.lc F.zero R.raw1 (V.tw 4) (λ _ _ → V.tw 4)
read-index-target-form = refl
```

此候选只剩 fails 未填。目标的第一支 Carry 字段就是 Carry (tw 4)，
本轮没有这个字段的否定。不能从“第一支尚未证”推出目标不可满足。

还把 successor-input 的读回 `suc (tw 2)` 作层号：它同样是 Ω̂ 2
的 LglB 坐标读回，环境全部可填；其 top 目标的第一支也要求 tw 4。

```agda
successor-read-index : F.LF
successor-read-index = V.up index1 successor-input

successor-read-index-reg : Reg successor-read-index
successor-read-index-reg = R.Ω₁-reg

successor-read-index-root : Below successor-read-index (V.Ω̂ successor-read-index)
successor-read-index-root = proj₁ successor-target-reg

successor-read-index-omega-carry : Y.Carry (V.Ω̂ successor-read-index)
successor-read-index-omega-carry = successor-target-carry

successor-read-index-input-guard :
  F.Gd successor-read-index (V.cO successor-read-index) G.top
successor-read-index-input-guard = inj₁ refl , tt

successor-read-index-input-B : Y.LglB successor-read-index G.top
successor-read-index-input-B = Y.top-B successor-read-index

successor-read-target-form : V.Ω̂ (V.up successor-read-index G.top) ≡
  F.lc (V.tw 2) G.top (V.tw 4)
    (λ η e → V.Ω̂ (V.up (V.tw 2) η))
successor-read-target-form = refl
```

## 6. 真正以 tw 3 作层号

此处 index=tw 3，不是上一节的 index=tw 2。
Reg、root 与 top 输入均可填；但 omega-carry 本身已经是
Carry (tw 4)，尚未证明可满足。因此连记录的输入环境也未填齐，
不能在这个候选上声称有反例。top 目标的 fails 还会要求否定 tw 5。

```agda
tw3-index-reg : Reg (V.tw 3)
tw3-index-reg = K.tw3-reg

tw3-index-root : Below (V.tw 3) (V.Ω̂ (V.tw 3))
tw3-index-root = one e-first

tw3-index-input-guard : F.Gd (V.tw 3) (V.cO (V.tw 3)) G.top
tw3-index-input-guard = inj₁ refl , tt

tw3-index-input-B : Y.LglB (V.tw 3) G.top
tw3-index-input-B = Y.top-B (V.tw 3)

tw3-index-omega-form : V.Ω̂ (V.tw 3) ≡ V.tw 4
tw3-index-omega-form = refl

tw3-index-target-form : V.Ω̂ (V.up (V.tw 3) G.top) ≡ V.tw 5
tw3-index-target-form = refl
```

**搜索结论（判断）。** 在这两个 Ω̂ 2 读回层号上，记录除 fails 外
的输入字段均已给闭实例；在 tw 3 上尚缺 omega-carry 和 fails。
未找到记录实例，不判定读回域 Ω̂ 封闭成立或失败，也不据此否定 K1′。
