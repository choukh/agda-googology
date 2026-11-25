# YiCarryNeg2：补齐全塔证书后的读回域反例搜索

**状态：未找到 ReadOmegaCounterexample，不作一般封闭或否定。**
上轮缺的 `Carry (tw 4)` 现在由 YiK1b.tower-carry 给出；规范 top
的失败目标 `Carry (tw 5)` 也已有证书。本篇只应用既有定理排除搜索候选，
不改树、证书或接口，不实现修补，不写折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryNeg2Read where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as Y
import OCF.Align.YiCarryNegRead as Old
import OCF.Align.YiK1b as K
import OCF.Align.YiK1bBase as B
import OCF.Align.YiK1bCarry as C
import OCF.Align.YiK1bReg as R
import OCF.Align.RR4RegOmega2 as O
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (Below; one; e-first)
```

## 1. 真正以 tw 3 作层号：环境与全部输入域核对

`index-root` 仍是冻结记录的弱根路径；较强的后继根路径只用于调用
已有 read-carrys，不加进记录。它从第 0 层正坐标开始，经两次原 top
读回给出；环境的三份 Carry 是闭证据，未以全塔作为公理。

```agda
one-strong-root : Below (F.suc (V.tw 1)) (V.Ω̂ (V.tw 1))
one-strong-root = R.coordinate-suc-root O.raw1 (inj₁ refl , tt)

tw2-strong-root : Below (F.suc (V.tw 2)) (V.Ω̂ (V.tw 2))
tw2-strong-root = B.read-root (V.tw 1) one-strong-root G.top (inj₁ refl , tt)

tw3-strong-root : Below (F.suc (V.tw 3)) (V.Ω̂ (V.tw 3))
tw3-strong-root = B.read-root (V.tw 2) tw2-strong-root G.top (inj₁ refl , tt)

tw3-index-reg : Reg (V.tw 3)
tw3-index-reg = Y.forget (K.tower-carry 3)

tw3-index-root : Below (V.tw 3) (V.Ω̂ (V.tw 3))
tw3-index-root = one e-first

tw3-omega-carry : Y.Carry (V.Ω̂ (V.tw 3))
tw3-omega-carry = K.tower-carry 4

tw3-top-guard : F.Gd (V.tw 3) (V.cO (V.tw 3)) G.top
tw3-top-guard = inj₁ refl , tt

tw3-top-B : Y.LglB (V.tw 3) G.top
tw3-top-B = Y.top-B (V.tw 3)

tw3-top-target-form : V.Ω̂ (V.up (V.tw 3) G.top) ≡ V.tw 5
tw3-top-target-form = refl

tw3-top-target : Y.Carry (V.Ω̂ (V.up (V.tw 3) G.top))
tw3-top-target = K.tower-carry 5

-- 只把已有有限次 Ω 读回定理应用到该层号，排除该层的全部候选。
tw3-read-target : ∀ η → F.Gd (V.tw 3) (V.cO (V.tw 3)) η →
  Y.LglB (V.tw 3) η → Y.Carry (V.Ω̂ (V.up (V.tw 3) η))
tw3-read-target η e b = proj₂
  (C.read-carrys 1 (V.tw 3) tw3-strong-root
    ((K.tower-carry 3 , K.tower-carry 4) , K.tower-carry 5) η e b)

no-tw3-fails : ∀ η (e : F.Gd (V.tw 3) (V.cO (V.tw 3)) η)
  (b : Y.LglB (V.tw 3) η) →
  (Y.Carry (V.Ω̂ (V.up (V.tw 3) η)) → ⊥) → ⊥
no-tw3-fails η e b fails = fails (tw3-read-target η e b)
```

`no-tw3-fails` 的守卫与 LglB 前提由同节 top 闭实例同时满足；
最后一个箭头正是被排除的 fails 字段，不当作可满足的背景前提。
这排除 **index 字面固定为 tw 3** 的反例，不声称整个记录为空。

## 2. 非 top 的实际候选

另外逐项给出后继、常 top 极限，以及在根槽、第一支槽、原守卫分支槽
放置的 lc 坐标。后三者的下界合法且带 Nested，不偷用 V0 的坏下界。
所有输入字段与目标均实填；常值极限在原弱步进下合法。

```agda
suc-input : F.Raw (V.tw 3)
suc-input = G.suc G.top

suc-guard : F.Gd (V.tw 3) (V.cO (V.tw 3)) suc-input
suc-guard = inj₂ (inj₁ refl) , tt

suc-B : Y.LglB (V.tw 3) suc-input
suc-B = tt , tt

suc-target : Y.Carry (V.Ω̂ (V.up (V.tw 3) suc-input))
suc-target = tw3-read-target suc-input suc-guard suc-B

lim-input : F.Raw (V.tw 3)
lim-input = G.lim (λ _ → G.top)

lim-guard : F.Gd (V.tw 3) (V.cO (V.tw 3)) lim-input
lim-guard = inj₂ (0 , inj₁ refl) , (λ _ → inj₁ refl) , (λ _ → tt)

lim-B : Y.LglB (V.tw 3) lim-input
lim-B = ((λ _ → inj₁ refl) , (λ _ → tt)) , (λ _ → tt)

lim-target : Y.Carry (V.Ω̂ (V.up (V.tw 3) lim-input))
lim-target = tw3-read-target lim-input lim-guard lim-B

root-lc : F.Raw (V.tw 3)
root-lc = G.lc (inj₁ (inj₁ tt)) O.raw1 G.top (λ _ _ → G.top)

first-lc : F.Raw (V.tw 3)
first-lc = G.lc (inj₂ (inj₁ (inj₁ (inj₁ tt)))) O.raw1 G.top (λ _ _ → G.top)

branch-lc : F.Raw (V.tw 3)
branch-lc = G.lc (inj₂ (inj₂ (O.raw2 , O.raw2-guard , inj₁ (inj₁ tt))))
  G.top G.top (λ _ _ → G.top)

root-lc-lgl : F.Lgl (V.tw 3) root-lc
root-lc-lgl = (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

first-lc-lgl : F.Lgl (V.tw 3) first-lc
first-lc-lgl = (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

branch-lc-lgl : F.Lgl (V.tw 3) branch-lc
branch-lc-lgl = (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

root-lc-guard : F.Gd (V.tw 3) (V.cO (V.tw 3)) root-lc
root-lc-guard = inj₂ (inj₁ refl) , root-lc-lgl

first-lc-guard : F.Gd (V.tw 3) (V.cO (V.tw 3)) first-lc
first-lc-guard = inj₂ (inj₁ refl) , first-lc-lgl

branch-lc-guard : F.Gd (V.tw 3) (V.cO (V.tw 3)) branch-lc
branch-lc-guard = inj₂ (inj₁ refl) , branch-lc-lgl

root-lc-B : Y.LglB (V.tw 3) root-lc
root-lc-B = root-lc-lgl , tt , tt , tt , (λ _ _ → tt)

first-lc-B : Y.LglB (V.tw 3) first-lc
first-lc-B = first-lc-lgl , tt , tt , tt , (λ _ _ → tt)

branch-lc-B : Y.LglB (V.tw 3) branch-lc
branch-lc-B = branch-lc-lgl , tt , tt , tt , (λ _ _ → tt)

root-lc-target : Y.Carry (V.Ω̂ (V.up (V.tw 3) root-lc))
root-lc-target = tw3-read-target root-lc root-lc-guard root-lc-B

first-lc-target : Y.Carry (V.Ω̂ (V.up (V.tw 3) first-lc))
first-lc-target = tw3-read-target first-lc first-lc-guard first-lc-B

branch-lc-target : Y.Carry (V.Ω̂ (V.up (V.tw 3) branch-lc))
branch-lc-target = tw3-read-target branch-lc branch-lc-guard branch-lc-B
```

## 3. 上轮的两个真正读回层号

constant-input 的读回与 successor-input 的读回均作 index 重试。
先从 index=1 的四份全塔证书得到读回的三份证书，再应用已有定理；
不是把“下一项 Carry”写作未填假设。原记录的 Reg、弱根路径和
omega-carry 仍直接引用上轮已经实填的闭证据。

```agda
constant-read-env : C.Carrys 2 Old.read-index
constant-read-env = C.read-carrys 2 Old.index1 one-strong-root
  (((K.tower-carry 1 , K.tower-carry 2) , K.tower-carry 3) , K.tower-carry 4)
  Old.constant-input Old.constant-input-guard Old.constant-input-B

constant-read-strong-root :
  Below (F.suc Old.read-index) (V.Ω̂ Old.read-index)
constant-read-strong-root = B.read-root Old.index1 one-strong-root
  Old.constant-input Old.constant-input-guard

constant-read-target : ∀ η → F.Gd Old.read-index (V.cO Old.read-index) η →
  Y.LglB Old.read-index η → Y.Carry (V.Ω̂ (V.up Old.read-index η))
constant-read-target η e b = proj₂
  (C.read-carrys 1 Old.read-index constant-read-strong-root constant-read-env η e b)

constant-read-top-target : Y.Carry (V.Ω̂ (V.up Old.read-index G.top))
constant-read-top-target = constant-read-target G.top
  Old.read-index-input-guard Old.read-index-input-B

successor-read-env : C.Carrys 2 Old.successor-read-index
successor-read-env = C.read-carrys 2 Old.index1 one-strong-root
  (((K.tower-carry 1 , K.tower-carry 2) , K.tower-carry 3) , K.tower-carry 4)
  Old.successor-input Old.successor-input-guard Old.successor-input-B

successor-read-strong-root :
  Below (F.suc Old.successor-read-index) (V.Ω̂ Old.successor-read-index)
successor-read-strong-root = B.read-root Old.index1 one-strong-root
  Old.successor-input Old.successor-input-guard

successor-read-target : ∀ η →
  F.Gd Old.successor-read-index (V.cO Old.successor-read-index) η →
  Y.LglB Old.successor-read-index η →
  Y.Carry (V.Ω̂ (V.up Old.successor-read-index η))
successor-read-target η e b = proj₂
  (C.read-carrys 1 Old.successor-read-index successor-read-strong-root
    successor-read-env η e b)

successor-read-top-target :
  Y.Carry (V.Ω̂ (V.up Old.successor-read-index G.top))
successor-read-top-target = successor-read-target G.top
  Old.successor-read-index-input-guard Old.successor-read-index-input-B
```

## 搜索边界与三档

**编译定理。** tw 3 的记录输入环境全部实填；
该层全部原守卫且带 LglB 的坐标均有目标 Carry，所以没有 fails；
两种上轮真正读回层号也有同范围的目标证书。六个 tw 3 闭输入
（top、suc top、lim const top、三个 lc 槽位）与两个旧读回层号的 top
均有闭证据。旧 V0／V1 坏坐标缺 input-B 的否定原样保留在旧篇，
这里没有把它们伪装为输入。

**有限测试。** 没有以计算样本支持全域结论；上述具体输入有类型检查
证书，三个固定层号的全量词结论是已有定理的应用。

**判断／未完成。** 未找到 ReadOmegaCounterexample。这里调用
read-carrys 1 需要较强的 Below (suc index) (Ω̂ index)，以及
Carry index、Carry (Ω̂ index)、Carry (Ω̂ (Ω̂ index))。原反例记录只给
Reg index、弱根路径和 Carry (Ω̂ index)，没有给前后两份 Carry 或
较强根路径。未证明一般环境能生产这些证据，也未找到满足原三项环境
而 fails 成立的层号／坐标；不能把证明缺口说成否定或一般封闭。

翻译账：仅应用原全塔与有限次 Ω 读回证明，未加新字段、构造子、
分支域、记号规则或阶段专属前提；没有值或 FGH 比较，没有新强度界。
本次获得的是指定搜索域内的精确排除信息，不声称树自足已完成。
第 4 层逼出：无。不调用新比较器；已有定理的比较仍保留原字面公共界。

冷编与依赖审计见本轮入口 [YiCarryNeg2](YiCarryNeg2.lagda.md)。
