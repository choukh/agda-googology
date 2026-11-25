# S3 第十一轮：(b) Reg₂ 在既有塔 Ω₁ 上触发止损

**交付 (b)，停在第4步 Ω 封闭；第5步要求的全塔也已有反例。**
按指定形状增加相邻项的严格第一位置证据后，Reg₂ 排除了两个旧反例，
并由 Reg₂→Reg 继承任意层的保留覆盖。但 1 合法且满足 Reg₂，
既有结构 Ω̂1（即 tower 2、Ω₁）却不满足 Reg₂。
失败发生在原始合法分支域允许的常值1极限坐标；不是根位置或不可数坐标问题。
这是本轮止损条件中的“实际使用的塔树不满足严格性”，故不再补正则性形状。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound11 where

open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiDispBase
  using (RetainedDomain; structural; one; e-suc)
open import OCF.Align.YiReg2Base using (all-retained-reg₂)
import OCF.Align.YiReg2Stop

-- 已继承的全层覆盖合同有非空实例；这里不是新 Ω 封闭或新强度结果。
retained-two-zero : RetainedDomain (F.suc (F.suc F.zero)) Y.zero
retained-two-zero = all-retained-reg₂ (Y.suc (Y.suc Y.zero)) Y.zero tt
  (structural (one e-suc)) refl
```

## 第1至3步：定义、排旧例、沿用全层覆盖

[YiReg2Base](YiReg2Base.lagda.md) 另定义 Reg₂；lc 子句逐字沿用 Reg 的条件，
仍量化原 Gd 的全部合法坐标。唯一增强是：

```text
Reg₂ (lim f) = (∀n Proper(f n,f(n+1))) × (∀n Reg₂(f n))
```

Proper 是 YiLevelBase 的严格第一位置路径，证据随树携带，不运行判定。
no-zero-limit 排除 q=lim const0；no-old-node 经 forget 排除第九轮旧 Ω 结点。
forget 对一切 LF 结构递归给 Reg₂ x→Reg x，故 all-retained-reg₂ 直接复用
第十轮全层定理：任意合法目标 i、Reg₂ 字段层 j 和已知 keep 派发，
第一支与原全部合法坐标里的字段都有 DispEv。此结论仍不保证输出本身 Reg₂。
入口 retained-two-zero 给这些前提的闭实例，不用矛盾前提支撑条件定理。

已核对 [BrwViewNeg.strict→LPO](BrwViewNeg.lagda.md) 的接口：它要求值映射上的
asuc(val(f n))≤val(f(n+1))，以及任意二进制序列的 Enc。
这里没有这项值上的严格 View、值转换或 Enc；只要求部分树携带语法 Proper，
没有实填该 LPO 定理的前提。本轮没有证明任意合法树都能获得 Reg₂。

## 第4步的反例：原合法坐标读回常值1列

[YiReg2Stop](YiReg2Stop.lagda.md) 的反例形状是：

```text
x = 1
Ω̂x = lc 0 raw1 1 (ληe → up 0 η) = tree(tower 2)
η = raw-lim(λn → raw1)
up 0 η = lim(λn → 1)
```

主否定为 no-reg₂-Ω₁ : Reg₂(Ω̂1)→⊥。
no-Ω-preservation₂ 排除 ∀x Legal x→Reg₂ x→Reg₂(Ω̂x)，
no-tower2／no-all-towers 排除 tower 2 的实例及“全部塔层 Reg₂”的合同。

输入 x 的 Legal 与 Reg₂ 均为 tt。η 的原 Gd 守卫也已实填：
raw1 位于 η 的第0支；相邻 raw1 用自反 Cp 步进，各支原 Lgl 为 tt。
因此没有假定空分支或矛盾的合法性前提。
Ω̂1 根所要求的 Below(1,Ω̂1) 已由第一支给出；旧根位置问题在此不存在。

若 Reg₂(Ω̂1)，lc 的全支递归义务就在这个 η 上给 Reg₂(lim const1)，
其新严格性字段在 n=0 给 Proper(1,1)。但该路径只能由 under-suc 构成，
会要求 CP(1,0)，后者没有构造子。由此排除所有可能证据，
不只是某次路径构造失败。

**反例分类须分开说：** 常值1坐标是原 Legal 接受的退化坐标；
含有这条合法支的整个 Ω₁ 是已有塔的实际层树。
本轮没有证明该坐标被某条记号侧 Reach／fsn 运行选中，
也没有证明实际 ψ 输出基本列出现相邻停顿。
全树 Reg₂ 要覆盖原全部合法分支，已有这一支就足以否定本轮要求的 Ω 封闭和全塔合同。
这不是第三种全新的退化形状，仍是常值 ℕ 极限，但它由实际 Ω₁ 的原分支域读回产生，
而非先给一个不正则输入来反驳保持。

## 编译错误原文

为了实填该读回分支的新字段，实验尝试：

```text
attempt : Reg₂ (F.lim (λ _ → F.suc F.zero))
attempt = (λ _ → Y.under-suc V.self) , (λ _ → tt)
```

单6G退出42；仅替换实验目录路径：

```text
<实验目录>/StrictReadAttempt.agda:11.30-36: error: [UnequalTerms]
(F.suc F.zero) != F.zero of type F.LF
when checking that the expression V.self has type
V.CP (F.suc F.zero) F.zero
```

该失败实验没有生成或用于 HTML／依赖切片。
正式否定由可编译的空模式证明给出，而非把退出42本身当成不可能性证明。

## 停点、五堵墙与翻译账

第2、3步已完成。第4步有非空输入的保持反例，第5步的“对一切 n”塔实例
也被 tower 2 排除，故按作者止损停下。未续查 Reg₂ Λ、Ω_Ω、完整 Env、
ψ 列、γ 保持或回灌；没有改 Raw／Gd 准入域或正则性子句来绕过反例。
这只否定本轮 Reg₂ 在既有 Ω／原分支域上的闭包，不否定所有正则性方案或乙路线。

卡点在最低层 Raw 0 的常值极限读回，不在不可数坐标。
它没有要求裸下标更新律、跨世界拷贝、固定类型回收器，也没有定义带回灌的保留下层规则；
交接五堵墙的完整前提均未被实填。与 C 线层2的不可数坐标停点不同，
本轮在到达那里之前就因严格性与原合法分支域不相容而止损。
没有使用 UIP、Funext、值上的比较、宽位置三歧或给原始树补码。

Reg₂ 的严格性字段由第十轮 no-omega-preservation 的常零极限反例逼出，
本轮按作者选定的结构 Proper 检验，没有从记号基本列取字段或按记号语法分情况。
旧 lc 的 bound 仍承接 no-next-ev 所揭露的树侧位置需求。
本轮的否定表明：仅增强输入正则性，不能让原全部合法 Raw 支自动满足同一严格性。
没有据此提出或采用新的修补。P1仍 x=Ω·ω²，无新值界、闭项或 FGH。

正式编译从仓库根，逐件删除本轮各自字面接口，单6G；审计记录见 LOG。
三件均退出0，禁用构造0；源码与编译器本地闭包逐一相同，且无记号／C线导入。
关键定义的语法依赖切片记号命中0，读标签正对照非零；切片不作值或完整成品认证。
