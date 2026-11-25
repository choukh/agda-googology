# YiCarry V1 否定：高层 gt 生成器没有带证书的初项

本篇只检验冻结的 YiCarry V1，不改树、守卫、合法性或接口。
反例的层参数是非零的 `tw 2`。源结点同时有 Carry 与 Legal，
原守卫也有闭起点，但带嵌套下界证书的 PointB 为空。
因此 K2′ 的全层 gt-generator 字段不可满足；失败先于 next、grow、
output-step 或任何 ψ 输出性质。不据此否定 K1′、规范塔的折叠或乙路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiCarryNeg where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
open F using (module G)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as Y
import OCF.Align.YiK2Stop as S
import OCF.Align.RR4RegOmega2 as R
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (one; e-first)
```

## 1. 下界合法，但其内部 lc 的下界不合法

V0 的坏下界是 `lim (1,0,0,…) : Raw 0`。这里把它放进
`Raw (tw 2)` 的根槽位，第一支与全部分支都取 top；正如 V0，
原 Lgl 不检查 lc 自己的下界。新增的 Nested 恰好检查这个字段。

```agda
level : F.LF
level = V.tw 2

level-nonzero : level ≡ F.zero → ⊥
level-nonzero ()

bad-coordinate : F.Raw level
bad-coordinate = G.lc (inj₁ (inj₁ tt)) S.bad-bound G.top (λ _ _ → G.top)

bad-coordinate-lgl : F.Lgl level bad-coordinate
bad-coordinate-lgl =
  (λ _ _ → inj₁ refl) , (λ _ _ _ _ _ → inj₁ refl) ,
  (λ _ _ _ → refl) , tt , (λ _ _ → tt)

no-bad-coordinate-nested : Y.Nested level bad-coordinate → ⊥
no-bad-coordinate-nested (lc , bc , bt , bg) = S.no-bound-legal lc

-- Raw 构造沿用 V0 的形状；读回后根下界相同，第一支随层号变化。
bad-coordinate-read : V.up level bad-coordinate ≡
  F.lc F.zero S.bad-bound (V.tw 3) (λ _ _ → V.tw 3)
bad-coordinate-read = refl
```

排除下界本身还不够：生成器可选任意原守卫坐标。
下面对目标 Raw 结构递归，排除所有把此坏坐标作为第一位置、
同时携带 Nested 的项。后继、极限及 lc 第一支只投影已有证书；
em 与 top 分支按原 Cp 的定义反演，不用比较器。

```agda
no-bad-cp-nested : ∀ (η : F.Raw level) →
  F.Cp level bad-coordinate η → Y.Nested level η → ⊥
no-bad-cp-nested G.zero (inj₁ ()) b
no-bad-cp-nested G.zero (inj₂ ()) b
no-bad-cp-nested (G.suc η) (inj₁ ()) b
no-bad-cp-nested (G.suc η) (inj₂ p) b = no-bad-cp-nested η p b
no-bad-cp-nested (G.lim f) (inj₁ ()) b
no-bad-cp-nested (G.lim f) (inj₂ (n , p)) b = no-bad-cp-nested (f n) p (b n)
no-bad-cp-nested (G.lc r c t g) (inj₁ refl) b = no-bad-coordinate-nested b
no-bad-cp-nested (G.lc r c t g) (inj₂ p) (lc , bc , bt , bg) =
  no-bad-cp-nested t p bt
no-bad-cp-nested (G.em i a) (inj₁ ()) b
no-bad-cp-nested (G.em i a) (inj₂ ()) b
no-bad-cp-nested G.top (inj₁ ()) b
no-bad-cp-nested G.top (inj₂ ()) b

no-point-B : Y.PointB level bad-coordinate → ⊥
no-point-B p = no-bad-cp-nested (Y.coordinate p)
  (proj₁ (Y.guard p)) (proj₂ (Y.bounds p))
```

## 2. 同一源的全部输入前提实填

源的第一支与全部分支取 `suc (tw 2)`。这直接给出 Reg 根字段
所需的 `Below (suc level) source`，其余递归证书由已编译的
tw 2 实例给出。分支并非因原守卫为空而空真：`original-start`
自取合法的 bad-coordinate，确实属于原 Point。

```agda
first : F.LF
first = F.suc level

body : (η : F.Raw level) → F.Gd level bad-coordinate η → F.LF
body η e = first

bad-source : F.LF
bad-source = F.lc level bad-coordinate first body

source-reg : Reg bad-source
source-reg = one e-first , R.Ω₁-reg , R.Ω₁-reg , (λ _ _ → R.Ω₁-reg)

source-carry : Y.Carry bad-source
source-carry = source-reg , bad-coordinate-lgl , Y.tw2-carry ,
  (λ _ _ _ → Y.tw2-carry)

source-legal : V.Legal bad-source
source-legal = V.Legal-tw 2 , (λ _ _ → V.self) ,
  (λ _ _ _ _ _ → V.self) , (λ _ _ _ → refl) ,
  V.Legal-tw 2 , (λ _ _ → V.Legal-tw 2)

original-start : Y.Point level bad-coordinate
original-start = bad-coordinate , (inj₁ refl , bad-coordinate-lgl)

source-package : Y.Source
source-package = Y.source bad-source source-carry source-legal
```

## 3. 失败字段：GtGenerator.seed，故 PsiRows 与 K2′ 不可满足

ψ 可任意选；不假设它已有行律或输出合法性。不可满足的是冻结接口
要求的全层生成器，下面从 seed 字段立即取出矛盾。
反例所需的 Carry、Legal 已在上节同一闭项上给出。
PsiRows、K2′ 正是被否定的目标，不将它们当成可满足的背景前提。

```agda
no-gt-generator : ∀ (ψ : Y.Source → F.Raw F.zero) →
  Y.GtGenerator ψ level bad-coordinate first body source-carry source-legal → ⊥
no-gt-generator ψ d = no-point-B (Y.GtGenerator.seed d)

no-psi-rows : ∀ (ψ : Y.Source → F.Raw F.zero) → Y.PsiRows ψ → ⊥
no-psi-rows ψ rows = no-gt-generator ψ
  (Y.PsiRows.gt-generator rows level bad-coordinate first body source-carry source-legal)

no-K2′ : Y.K2′ → ⊥
no-K2′ d = no-psi-rows (Y.K2′.ψ d) (Y.K2′.rows d)
```

## 4. 否定范围、前提与翻译账

**编译定理。** `source-package` 是 Carry 与 Legal 同时成立的合法闭源；
`original-start` 给它的原守卫闭起点；`no-point-B` 排除全部带 LglB 的
守卫坐标。`no-gt-generator` 对任意 ψ 成立，`no-psi-rows` 只用
gt-generator，`no-K2′` 不用 output-B、output-legal、positive 或
bounded-position。这里的“全层不可满足”指一个量化所有 k 的记录无实例，
不是每个固定 k 的生成器都不存在；第 0 层原有起点结果不受影响。

否定的背景前提可满足：同一源的 Carry、Legal、Reg、非零层号和原守卫
起点全已实填。辅助 no-bad-cp-nested 的 Cp 前提可自取坏坐标，
其目标 Nested 则正是被否定的新增性质。任意 ψ 的函数类型非空
（例如常值 `λ _ → G.suc G.zero`），没有假设这个函数满足任何行律。
PointB、GtGenerator、PsiRows 与 K2′ 是被否定的目标，不能要求它们
另有可满足实例。搜索读回域 Ω̂ 的状态与逐项前提见
[YiCarryNegRead](YiCarryNegRead.lagda.md)：未找到反例，未否定。

**有限测试。** 无。闭项等式及具体证书由类型检查，不用抽样支持全域声称。

**判断。** 本结果说明 V1 的 Carry 与 Legal 域不足以为接口量化的
全部高层输入提供 gt 生成器；它没有证明规范闭项的实际计算会选中本源，
也没有否定 EBO 目标、乙路线、K1′ 或其它输入域。没有序数值或 FGH
比较，没有新强度界。按任务不实施修补，也不据此另开路线。

字面公共界：本篇未新增或调用比较器。bad-coordinate 与任意守卫坐标 η
的公共界就是 η：guard 给前者的 Cp，后者有自反 Cp，guard 还给 Lgl η。
original-start 的公共界是合法的 bad-coordinate 自身。
Reg 的根位置以源结点为结构祖先，不送入 CP 比较器。
坏下界 1→0 的反演原样用 YiK2Stop 的编译否定，没有索取全局三歧。

翻译账：只新增闭反例和否定证明，没有新树构造子、分支域、证书字段或
阶段专属前提；新增反例形状由冻结 Nested 检查的字段与 V0 坏下界选定。
信息是高层 seed 的精确缺口，不是提高强度或完成树自足。
第 4 层逼出：无。没有改 src、archive、README、LOG 或任何已有定义。

## 5. 冷编与审计清单（2026-11-10）

| 模块 | 仅删自身字面接口后重编 | 堆上限 | 退出码 | 目标 Checking |
|---|---|---|---|---|
| YiCarryNeg | 是 | 6G | 0 | 有 |
| YiCarryNegRead | 是 | 6G | 0 | 有 |

两件依次执行，依赖使用缓存，不声称冷编整个闭包。未使用
ignore-interfaces，也未删改任何别的模块接口；退出码直接读取，不经过管道。
每次均带 `+RTS -M6G -RTS`，成功生成 HTML 与编译器依赖图后再切片。

- 两件均为 `--safe --without-K --lossy-unification`；代码公设、洞、
  跳过停机／正性检查指示、信任相等及函数外延前提均为 0。
- 源码本地闭包分别 24／26，库叶均 19。importclosure 白名单为
  `OCF.Align.Yi`、`OCF.Align.RR4RegOmega2`、`OCF.Align.RR4CoordRoot`、
  `OCF.Align.LevelFix`、`OCF.Free.Level`、`OCF.BTBO`；白名单外和禁用表
  均为 0，无记号／C 线。成功编译器图的本地集合逐一相同。
- 成功 HTML 的切片：source-carry 63、source-legal 53、no-point-B 48、
  no-K2′ 101；Read 中 constant-target-carry 114、successor-target-carry 117、
  read-index-omega-carry 116。各根记号模块块数与其它模块记号词命中均为 0。
- 正对照另成功生成 EboLean3Lab HTML，ebo-lab″ 为 352／33／36；
  未删除该旧模块的接口，它也不在两件新模块的导入闭包中。
  切片只作语法级近似，不代替前提检查或值验收。
- YiCarry、YiCarryBounds、YiCarryExamples、YiCarryV0、YiK1、YiK2Stop
  的源文件摘要与开工时相同。只新增本前缀两件 literate Agda；
  未提交、推送、安装包或实施修补。

复现（从仓库根，库文件包含 stdlib 与 cubical 的有效库路径）：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryNeg.lagda.md +RTS -M6G -RTS
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiCarryNegRead.lagda.md +RTS -M6G -RTS
python3 probes/Survey/scripts/importclosure.py OCF.Align.YiCarryNeg OCF.Align.YiCarryNegRead --only OCF.Align.Yi --only OCF.Align.RR4RegOmega2 --only OCF.Align.RR4CoordRoot --only OCF.Align.LevelFix --only OCF.Free.Level --only OCF.BTBO
```
