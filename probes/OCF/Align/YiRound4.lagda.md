# S3 第四轮： (a) 依赖上下文的有限目标来源包络

**结论是 (a) 依赖上下文。** 每个实际目标都来自根目标0，或严格先前
某一步 γ 链允许引入的共尾层ν。给定运行历史，候选表有限，并由过去步骤
的字面 Ω 字段及其前驱生成；不是看到当前目标u以后才把u加入候选表。
本轮不追上一轮共同后继前提，也不写树运算或树侧 ψ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound4 where

import OCF.Align.YiTargetBase
import OCF.Align.YiTargetTransport
import OCF.Align.YiTargetScan
import OCF.Align.YiTargetOrigin
import OCF.Align.YiTargetHistory
import OCF.Align.YiTargets
import OCF.Align.YiTargetExamples
```

## Targets 与候选集的生成规则

[YiTargets](YiTargets.lagda.md) 定义 Targets l u = Actual l u，完全沿用
第二轮已冻结的真实 Reach／FsnCall 集合，不把任意子项当成可到达项。
At r l u 保留发生时的具体历史r；context-target／targets-context接回全局集合。
targets-below 复用 actual-gt：每个实际目标的码比较均严格低于该次左端。

[YiTargetHistory](YiTargetHistory.lagda.md) 定义历史候选Env，生成规则为：

```text
Env(tower k)          = [0]
Env(pred-step r)      = Env(r)
Env(fs-step r n)      = Env(r)          若 scan(source r) = nothing
Env(fs-step r n)      = ν :: Env(r)     若 scan(source r) = just(ν,v)
```

scan读取旧源项，不展开基本列输出，也不计算γ的分支。
该步增加的是共尾层ν，即那次比较左端ν+1的前驱；旧目标v被丢弃。
新环境对所有分支编号n使用同一个新增候选，允许重复和已不活跃的条目。
当n=0等情况下，候选ν不必真的成为输出的正ψ头；这里只要求安全包含。

主定理 target-in-env：若a:Targets l u，则u属于Env(reached a)。
context-bound同样覆盖任意给定的Reach历史与该时刻FsnCall。
added-call证明每个非根新增候选对应前一步真正发生的gt比较；
added-target-blind证明新增规则不依赖该步的旧目标v。
target-history-origin进一步给出：当前目标为0，或有Earlier证据，
定位到严格先前的一步真实扫描，并附该旧源项的字面Ω字段及前驱等式。
target-came-from-comparison由此给一个直接的Targets来源律：若非零u曾作为目标，
则存在更早的一次实际比较(u+1,v)。Earlier保留“更早”的具体历史证明，
不仅给一个无时间关系的全局存在性。
这给全局Targets l的上下文来源界；没有宣称固定l的全历史并集有限。

## 为什么是严格先前来源，而非 Actual 换名

[YiTargetBase](YiTargetBase.lagda.md) 固定 AllTags P a：a中每个正参数ψ
的目标满足P，同时递归检查其下标、参数、尾项。空参数Ω的下标本身不作为
目标；例如Ω_ω里含有ω这棵码，不自动把整个ω算作可派发目标。

[YiTargetTransport](YiTargetTransport.lagda.md) 不假定标准形或Reach，证明：

- pred-tags：前驱不增加这些正ψ目标。
- cof-tags：共尾层ν内部已有的正ψ目标来自原项。
- fsT-tags：Ω基本列仅运输原项与输入坐标已有的正ψ目标。
- gamma-tags：γ链唯一获准新增的正ψ头为ν；ν内部目标由cof-tags运输。

fsn-tags继而对原fsn规则证明一步保持；env-tags从根对Reach全部构造子归纳。
当前u的成员证明由该归纳不变量与call-tags给出，不是额外假设或事后检查。
根只有0，Env的定义完全不访问当前比较的FsnCall证据。

[YiTargetScan](YiTargetScan.lagda.md) 的call-scan／scan-call与原FsnCall
双向对应；call-unique证明单次fsn至多一处这种比较。
它只扫描fsn内部那次fsnc，未把cof／fsTc自己的码比较加入集合。

[YiTargetOrigin](YiTargetOrigin.lagda.md) 将“字面决定”进一步固定：
Field w a表示Ω_w在a的语法中出现，只有头、下标、参数、尾项四种位置。
cof-origin与scan-origin证明被取出的ν是某个这样的原字段w的前驱，且cof w=c1。
这不是假定ν自己就是a的字面子项；“取该字段的前驱”是明确允许的生成步骤。
这些Field是记号语法的位置，不是乙树的CP证据。

## 两条反例的具体来源

[YiTargetExamples](YiTargetExamples.lagda.md) 给闭项等式及成员／非成员定理：

| 实际比较 | γ步之前的Env | 该步扫描结果 | γ步之后的Env |
|---|---|---|---|
| Ω₂+1 对2 | 四个0 | (2,0) | 2及四个0 |
| Ω·2+1 对ω | 五个0 | (ω,0) | ω及五个0 |

two-absent-before／omega-absent-before排除目标此前已在候选表；
two-present-after／omega-present-after给加入后的证据，
two-at-comparison／omega-at-comparison由全称定理给后来比较时的成员证明。
这组具体等式是测试闭项上的定理；全历史结论由env-tags单独证明。

第一对沿[第二轮路径](YiRound2.lagda.md#实际发生路径与形状)，
2在t₅→t₆的γ₂首次进入Env；第二对沿[第三轮路径](YiRound3.lagda.md#实际发生与来源)，
ω在t10→t11的γ_ω首次进入Env。两者都由外层链带入内层正规Ω字段的比较。
第三轮已证明ω不在ν=Ω·2的字面子项中；来源界通过较早上下文说明它从何而来。

## 范围与剩余判断

本轮构造的Env候选表依赖比较发生前的整个运行历史，不只依赖当前层号l=ν+1。
它可能含高于当前l或不再活跃的历史条目；实际目标的严格码界另由targets-below给出。
因此没有据此为固定l制造一个统一脊柱，也没有把所有Targets l枚举完。

**未证明：不存在仅依赖l的更强刻画。** 当前历史包络与一个可能的层号自身
刻画、乃至某个固定层号有无限目标反链的(b)，逻辑上可以并存。
本轮不将“我给出的包络依赖上下文”加强成“任何位置方案都只能依赖上下文”。
若采用本轮包络生成位置证据，证据的数据来源需要随运行携带；这是对这个
构造方案的判断，尚无对应的树侧闭包定理。

按作者第四项，本轮不写树运算。没有追共同后继、改LevelFixCore／YiLevelBase、
给raw树补码或改变CP；没有UIP、Funext及裸层号上的比较律。
五墙涉及的世界更新、拷贝运输、固定HB收缩、反馈合法化与留下规则均未引入。
P1仍为x=Ω·ω²，没有新的序数值前沿。

## 翻译账与验证

AllTags、scan、Field、Env及Targets都在第4层明读EBO语法与基本列。
新字段只有诊断谓词和历史来源数据，不进入乙的树、合法性、折叠或闭项证书。
原Ωprefix、其全层合法性及Λp保留；没有用本轮验收结果反改前三层定义。
本轮提供的是所有Reach的一步来源保持及历史不变量，不是逐项翻译的新成品。

正式从仓库根，单路6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound4.lagda.md +RTS -M6G -RTS
```

七个数学模块与入口共八件删除各自接口后冷编，均Checking，单路6G退出0；
safe／without-K齐全，禁用构造与洞0。证明与范围已配对只读审查，
审查路模块由主路读证并删接口冷编复核。编译器导入图及导航检查详见LOG。
本入口按授权引用记号，不作导入闭包无记号的成品认证。
