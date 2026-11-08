# 接续 Third：全种类合法化、合法坐标覆盖与世界扩张

本轮从接手前 `Third.Sb/Tw` 的完整构造出发，处理其已经记载的
`leg-const` 损失。不重造 BTBO，不重开 CrossM，不改变旧闭项。
结果是一套对全部底、全部塔高度和全部种类的结构操作，而不是新阶段
的专属节点；**还没有得到 ψ₀Λ 闭项，也没有新增具名强度**。

## 1. 定义与定理

旧合法化在非指标种类处只看零坐标。新 θ 按坐标树递归；在后继处
保留前缀、当前原分支和后继原分支：

θ(0)=g(0)，θ(d+1)=θ(d)+g(d)+g(d+1)。

极限与 Ω 情形沿原低层树构造；所有种类均沿结构找到其起源 step。
额外的 g(d) 使每个原分支在后继坐标处有覆盖，不要求 g 按值单调。
这是树分支覆盖的设计要求，不是从记号基本列抄来的新规则；它仍有
累加代价，不声称在合法输入上恒等或保持基本列。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRichLeg where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase using (HB; LgB; Wd; LgW; _≤w_; hs; hz; hself)
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb; fl)
import OCF.Lean.ThirdRichLegBuild as B
import OCF.Lean.ThirdRichLegValueRun as R
import OCF.Lean.ThirdRichLegValueLegal as V
import OCF.Lean.ThirdRichLegNegWorld as N
import OCF.Lean.ThirdRichWorldSections as W

normalise : ∀ n → HB (Sb n) → HB (Sb n)
normalise = B.legS

normalise-legal : ∀ n a → LgB (normalise n a)
normalise-legal = B.Lg-legS

normalise-covers : ∀ n a → V.Domain.Cover (Sb n) (R.LegalS n) a (normalise n a)
normalise-covers = V.inflateS

tower-normalise : ∀ n m → HB (Tw (Sb n) m) → HB (Tw (Sb n) m)
tower-normalise = B.legT

tower-legal : ∀ n m a → LgB (tower-normalise n m a)
tower-legal = B.Lg-legT

tower-covers : ∀ n m a → V.Domain.Cover (Tw (Sb n) m) (R.LegalT n m) a (tower-normalise n m a)
tower-covers = V.inflateT

normalised-floor : ∀ n → HB (Sb n)
normalised-floor n = normalise n (fl n)

floor-legal : ∀ n → LgB (normalised-floor n)
floor-legal n = normalise-legal n (fl n)

floor-covers : ∀ n → V.Domain.Cover (Sb n) (R.LegalS n) (fl n) (normalised-floor n)
floor-covers n = normalise-covers n (fl n)

-- 沿旧默认组件政策，以新富合法化的指标界实填；不是历史旧 wS。
module Actual = N.Actual (hs hz) tt
module At (n : ℕ) = W.Frames n (Actual.D.world n) (Actual.D.world-legal n)

closed-world : ∀ n → Wd (Sb (Data.Nat.suc n))
closed-world n = At.advanced-world n (Actual.bounds n)

closed-world-legal : ∀ n → LgW (Sb (Data.Nat.suc n)) (closed-world n)
closed-world-legal n = At.advanced-legal n (Actual.bounds n) (Actual.bounds-legal n)

default-world-extends : ∀ n → _≤w_ (Sb (Data.Nat.suc n)) (Actual.D.world (Data.Nat.suc n)) (closed-world n)
default-world-extends n (inj₁ _) = W.rfS n (Actual.D.world n) , hself
default-world-extends n (inj₂ c) = At.from-default n (At.initial n) (At.floors n) (hs c)
```

`normalise-covers/tower-covers` 的 Ω 左分支只量化该种类的合法低层坐标，
右侧选取的后继坐标仍合法。坐标域非空有实例，统一下界规则不靠空前提。
第零层关系接标准值序；高层关系尚未与旧动态折叠的输出建立模拟。

## 2. 世界准入是独立义务

`ThirdRichLegNegWorld.Defaults` 对任意合法界族证明：若仍使用旧 wT，
每个组件顶种类只能读零坐标。`Actual` 已代入新合法化的真实地板界：
合法输入的分支 0、1 经合法化分别为 1、3，但旧世界仍只允许读前者。
这不是整个方向的不可能性，也不是序数值上界。

正面构造 `ThirdRichWorldSections.Frames` 不做精确点更新。它接收各目标
自己的输入树族 Q，以同类型合法化计算反馈坐标，令新界为其后继：

feed(m)=B(m)+normaliseₘ(Q(m))，next(m)=feed(m)+1。

对所有底 n、所有高度 m，有合法世界、旧世界到新世界的扩张、feed 的
可入证据，以及 Q(m) 被 feed(m) 覆盖的定理。`floors` 用原 Third 全族地板
实际实例化，并非空记录。这里没有组件判等、无界比较或常值代替回灌。

这里的“旧世界”指固定同一底世界 u、同一指标界 i 时的组件默认政策。
闭合实例的指标界已经由新富合法化计算；`default-world-extends` 没有
证明历史 `ThirdLeg.W.wS` 整体嵌入新世界。它也没有同步写回所有低层
世界：`full-grow` 保持 u、i，只扩张其上的组件塔。

**仍缺的实质一步：** 旧折叠给出某个目标的输出；本构造需要同一来源的
全目标输入族。怎样沿实际折叠生成它，并让保留分支和路径证书随新世界
继续，是未完成义务。以前 ColimA 的“族增量”已指出类似问题；本轮将合法
不缩操作与实际 Third 世界接通，没有因此宣布该问题解决。

## 3. 文件、成本与翻译账

| 文件 | 内容 |
|---|---|
| ThirdRichLegIf | θ 的共同定义、局部律和共享接口 |
| ThirdRichLegBuild | 全 Sb/Tw 的实际 θK、合法化及合法性 |
| ThirdRichLegValueIf/Theta/Run | raw 共尾覆盖、实际后继坐标及覆盖证明 |
| ThirdRichLegValueLegal | 合法低层坐标覆盖、域非空、第零层标准值桥 |
| ThirdRichLegNegWorld | 原默认世界的精确边界及新操作的真实实例 |
| ThirdRichWorldSections | 全目标族的世界构造、扩张、准入和值覆盖 |

前三层成本须从实际定义和合法性根做依赖切片；不能以新文件行数加旧
1049 作成品数字。值覆盖和边界证明另计。尚未形成替换旧 Third 后的新
完整闭项，因此本轮不报告它已满足 1513 成品预算。

主审 HTML 上的完整依赖切片（仓库代码，非空非注释行，不计第三方库）：
全合法化与合法性 294；加真实地板实例 340；再并入闭合世界及整族
扩张、合法、准入 440；加合法坐标覆盖 561；含第零层标准值桥 591。
脚本为 `Survey/scripts/thirdrich/locslice_thirdrich.py`，模块实例参数已补根；
仍是语法级切片近似。这些是局部操作的成本，不能当作新完整 Third 成本。

翻译账：没有新增树构造子或按记号阶段分类的字段；继承现有 step/sup、
Sb/Tw 与 Ctx。θ 的额外项由分支覆盖要求产生，世界后继界由字面准入
产生；二者均仍有算术累加。未修改旧树、折叠、合法性或证书，也未让
终点标签验收反向定制旧定义。若接入完整流程，必须继续交内部 View、
成本和实际输出值比较，不能仅用这组局部结论声称完成。

额外分支项和取后继界是满足这些合同的一种设计，已证有效，未证唯一；
不能据此宣布树已经能自行给出下一步的全部定义。
