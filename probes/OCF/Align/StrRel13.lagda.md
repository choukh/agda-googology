# 结构关系, 第十三轮: 跨坐标层的节点规则: 入口

> **判决: PARTIAL, 受阻 (未否定路线).** 交接单第 1 项 (跨坐标层的节点规则及其可靠性) 没有走通; 第 2 项 ($\Omega^{\mathsf H}$ 处的动作前提, `MonoStep Ωᴴ`) 因此没有开始, 只把它在 `StrRel12` 族里的三个前提编译成否定. 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件, 没有改树, 折叠与合法性.
>
> 本轮得到的是一个分类定理与六条编译过的否定, 它们把 "跨坐标层" 这一步要什么说成了定理:
>
> 1. **(定理) `StrRel13Rk.rk-mono`**: 坐标层字面地 $k\sqsubseteq k'$ 时, 两边节点读数的种类只有 (升, 升), (留, 留), (左留, 右升) 三种; "左升右留" 不出现. 三种都实际出现 (`StrRel13Kr` 的 `rk00`/`rk10`, `rk02`/`rk12`, `rkL`/`rkR`).
> 2. **(否定) 状态关系不够: `StrRel13Val.¬valX`, `¬semX`.** 层 $2$ 上坐标层 $0$ 与 $1$ 的两个节点 (分支都是 `n1`), 状态按 `R∀c` 与自己相关, 第 $0$ 层目标上两边都升, 左边的读数值上严格大. 原因: `R∀c` 只比同一目标上的读数, 链从状态在**各自坐标层**上的读数起. 与结论层取结构还是取值无关.
> 3. **(否定) 结构结论层不够: `StrRel13Kr.¬krX`, `¬semKr`.** 同一对节点, 空状态, 第 $1$ 层目标 (夹在中间): 左边输出节点, 右边输出链的极限; 没有 "节点对极限" 规则的关系族 (含 `StrRel12Rel.Rel` 及在它上面加任意 `ni` 对 `ni` 的跨层规则) 都不能把它们相关.
> 4. **(否定) 加 "节点 ≤ 极限" 的读法也不够: `StrRel13Later.¬laterV`, `¬semLater`.** 把上一条的两个输出以折叠真实经过的状态 $Y_0\oplus\mathrm{Step}\,Y_0$ 再折叠一次, 第 $0$ 层的读数左边非零, 右边为零. 右边升的时候用的是当时的 (空) 状态, 左边留下来等以后的状态. 附: `StrRel13Kr.¬alLim0`: 现有的对齐 `Al` 不能把非空路径对进极限的第一位置, 所以 "吸收进极限的某一段" 的规则在第 $0$ 层喂不了 `genAl`.
> 5. **(否定) $\Omega^{\mathsf H}$ 处 `StrRel12` 的三个前提: `StrRel13Om`.** `¬cpTop`/`¬relTop`: `MonoStep Ωᴴ` 的顶层比较 (树世界 $0$ 经 `z⊲ one` 对树世界 $1$ 经 `self`) 不是 `CP`, 并进树 (`nw`) 也不相关, 所以它在 `sem∀` 的定义域外, 与跨坐标层无关. `¬selfΩ`: 同一世界里 $\Omega_\Omega$ 也不自相关 (`StrRel12Om.¬ΩR` 是世界 $0$ 对 $1$; 这里两边同为世界 $0$). `¬hawΩ`: `HAW Ωᴴ tt tt Act Act` 不成立 (`StrRel12` §3 那一步判断的编译形式).
>
> **意味着什么 (判断).** 第 2, 3, 4 条合起来说: 跨坐标层的节点规则要成立, 改的不是结论层 (结构或值), 而是**状态的前提**: 语义不能对一切按 `R∀c` 相关的状态量化, 要带一个跨目标层的状态不变量, 说状态在高坐标层上的读数支配低坐标层的 (第 2 条的反例状态违反它), 并且这个不变量对 "升的那一边当时的状态" 成立 (第 4 条用的是空状态). `MonoPort7` 的单世界语义正是带状态不变量 (`Good`/`SRel`) 的, 那里 $\Omega_k$ 的比较能做; `StrRel12` 的两世界语义没有这样的不变量, 它的 `sem` 对一切层一个证明. 下一步要把两者合起来 (§3).

## 0 模块

| 文件 | 内容 | 档 |
|---|---|---|
| [StrRel13Rk](StrRel13Rk.lagda.md) | `RkX`, `rR`, `lK`, `lKK`, **`rk-mono`** | 定理 |
| [StrRel13Val](StrRel13Val.lagda.md) | `Λ₂`, `xL`, `xR`, `Yv`, `hYv`, `lowL`, `xz`, `pt≤`, `chz`, `upR`, **`¬valX`**, **`¬semX`**, 对照 `selfR`, `selfOk` | 否定 (定理), 对照 (定理) |
| [StrRel13Kr](StrRel13Kr.lagda.md) | `T₁`, `rkL`, `rkR`, `rk00`, `rk10`, `rk02`, `rk12`, `NoNiNl`, `nn12`, **`¬krX`**, **`¬semKr`**, `¬alLim0` | 否定 (定理) |
| [StrRel13Later](StrRel13Later.lagda.md) | `nzb`, `nzb-ok`, `Y₁`, `lowLater`, `nlz`, `stz`, `upLater`, `hY₁`, **`¬laterV`**, **`¬semLater`** | 否定 (定理) |
| [StrRel13Om](StrRel13Om.lagda.md) | **`¬cpTop`**, `ΔΩ-nw`, **`¬relTop`**, `cp12′`, **`¬selfΩ`**, `¬selfΩ⨾`, **`¬hawΩ`** | 否定 (定理) |
| 本文 | `rkInst` (`rk-mono` 的前提的实例) | 定理 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel13 where

open import Data.Unit using (tt)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtFeedTree using (hz; hs; hself; hsuc)
open import OCF.Align.StrRel11Rk using (s∞; u∞)
import OCF.Align.StrRel13Rk as Rk13
open import OCF.Align.StrRel13Val public using (¬valX; ¬semX; selfOk; Λ₂)
open import OCF.Align.StrRel13Kr public using (¬krX; ¬semKr; ¬alLim0; rkL; rkR)
open import OCF.Align.StrRel13Later public using (¬laterV; ¬semLater)
open import OCF.Align.StrRel13Om public using (¬cpTop; ¬relTop; ¬selfΩ; ¬hawΩ)

-- rk-mono 的前提可满足: 坐标层 0 ⊑ 1, 目标第 1 层, 结果是第三种 (左留右升)
module R₂ = Rk13 Λ₂ tt

rkInst : R₂.RkX (R₂.P.rkT {hz} {hs hz} {azero} (hsuc (hsuc hself)) (hsuc hself) tt) (R₂.P.rkT {hs hz} {hs hz} {azero} (hsuc hself) (hsuc hself) tt)
rkInst = R₂.rk-mono (u∞ s∞) (hsuc (hsuc hself)) (hsuc hself) tt (hsuc hself) (hsuc hself) tt
```

## 1 结论层选哪个 (交接单第 1 项的第一问)

交接单给了两个选项: 给 `Rel hz` 加第 $0$ 层的值比较读法, 或写跨层关系. **两个都不选, 理由是编译过的否定:**

- **值读法.** `¬valX` 本身就是值上的: 在 `R∀c` 的状态前提下, 跨坐标层的节点对在第 $0$ 层目标上值就错. 所以换成值读法不能让节点规则可靠. 另外 (判断, 依据 `StrRel4Walk` 文件头引的 `StrRel2Neg.phead→LPO`): 第 $0$ 层关系在 `κᴸ` 的证明里要生成对齐 (`genAl` 对 `Rel hz` 的推导递归), 只给值就要从值求对应位置, 那是 LPO 的形状.
- **跨层的结构关系.** `¬krX`: 目标层夹在中间时输出是 "节点对极限", 只加 `ni` 对 `ni` 的跨层规则收不下. `¬laterV`: 再加 "节点 ≤ 极限" 的读法, 在 `R∀c` 的语义下值也错.

要改的是状态的前提 (见入口文件头 "意味着什么"). 这是判断, 依据是这三条否定都只在状态前提处起作用: `¬valX` 的状态是 `R∀c` 允许的一个形状 (第 $0$ 层读 `n1`, 第 $1$ 层读 `n0`; 折叠是否产生这种状态, 本轮没有查), `¬laterV` 的状态是闭项的起始状态 `Y₀` (这时右边的链全是 `n0`).

## 2 一边升一边留 (第一问的第二部分)

`rk-mono` 说只有 "左留右升" 一种 (左边坐标层低). 它的输出对是 `ni R …` (第 $t$ 层, 坐标层 $k$) 对 `nl (λ n → 第 n 段)` (坐标层 $k'$ 的链). `¬krX`, `¬laterV`, `¬alLim0` 依次说明三种处理在现有设定下不成立: 不处理 (结构关系里没有这种对), 加 "节点 ≤ 极限" (在 `R∀c` 的语义下值错), 让链的第一段吸收节点 (现有的 `Al` 给不出对齐). 剩下的路 (判断, 未试): 在 "升的那一边当时的状态" 带不变量的前提下, 链的第 $0$ 段含有一个坐标层 $\ge k$ 的节点 (状态的读数里有 $\mathrm{Step}$ 留下的 $\Omega_{k'}$, 它的节点坐标层是 $k'$ 的前驱), 先把这一对放到同层的 `niᴸ` 下, 再处理吸收所需的 `Al` 构造子.

## 3 第一个障碍与接手清单

**第一个障碍 (判断, 依据 §1 的三条否定).** 两世界语义 `StrRel12Sem.SemW` 对一切 `R∀c` 相关的状态量化; 跨坐标层的节点比较要的是带状态不变量的语义. 不变量要满足三条 (每条对应一条否定): (a) 跨目标层: 状态在坐标层 $k'$ 上的读数与在 $k\sqsubseteq k'$ 上的读数相关 (`¬valX`); (b) 对 "当时" 的状态成立, 不能是空状态 (`¬laterV`); (c) 经得起 `cv`, `⊕`, `Kp`/`Kb` 的换世界 (`StrRel11CvNeg.¬cv-al` 说在旧折叠上带对齐的目标对经不起 `cv`, 在主线上由 `StrRel11Tg.cvR` 解决; 不变量要同样经得起, 未试). (a) 需要一个跨层的关系 (两边层不同的树), 这是 `Rel L` 的异质版, 本轮没有写.

**`grow≪` 与 `changeW` (判断).** `MonoPort7Lim.grow≪` 比的是两个实例的闭项 ($T_{\mathrm{emb}\,a}<T_{\mathrm{emb}\,b}$), 状态是 `Y₀`, 动作是 `Act`; 跨坐标层的 `rise/rise` 比的是同一实例里从任意状态起的两条链. 两者接上要两步: 状态不变量把 "坐标层 $k$ 的读数" 说成以 $\Omega_k$ 开头 (状态 $Y_0\oplus\mathrm{Step}\,Y_0$ 的读数字面上是 $0⨾\omega\cdot(\Omega_k⨾0)$), 再用 `MonoPort8Sim.changeW` 把实例 $\Omega^{\mathsf H}$ 里层 $k$ (不含 Ω-极限) 的折叠换成实例 $k$ 里的折叠. 第一步就是上面的障碍. 本轮没有编译这条路的任何一环.

**接手清单 (按依赖顺序).**

1. 带状态不变量的两世界语义: 把 `MonoPort7` 的 `Good`/`SRel` (单世界) 与 `StrRel12Sem.SemW` (两世界, `CP`) 合起来; 先在不含 Ω-极限的实例上重证 `StrRel12.sem` 的八条规则 (不变量对 `⊕`, `cv` 封闭).
2. 异质的关系 `Rel L L′` (左层 $L$ 右层 $L'$, 对左层递归, 坐标关系沿左边位置取到 `Rel j j′`), 跨坐标层的节点规则, 以 `rk-mono` 的三种情形证可靠性; 第三种按 §2 的剩下的路.
3. `MonoStep Ωᴴ` 的顶层: `¬cpTop`/`¬relTop` 说要一种不经 `CP` 的顶层比较 (树世界 $0$ 对 $1$; `StrRel8Neg` 说不带前段对齐的 `nw` 规则不可靠). 判断: 改成比较第 $0$ 格的走法路径 ($[0,v)$ 对 $[1,v')$, 它们可以对齐), 而不比较 `q₀` 本身.
4. 然后才是交接单第 2 项: `HAW Ωᴴ` (`¬hawΩ` 说在本族里不成立, 要第 2 条的跨层关系), `hs-reduce<′` 的 `Free` 前提.

## 4 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `RkX` 三种, `rk-mono` | `RunNi` 对 `rkT` 分情形, 两边坐标层不同 | **树逼的** |
| `¬valX` 的反例状态 | `Chn` 的起点读状态在坐标层上的读数 (`RKi`, `Chn` 的字面); `R∀c` 只比同目标 | **树逼的** (否定) |
| `¬krX`, `NoNiNl` | `RKi` 的 `keep` 句输出 `ni`, `rise` 句输出 `nl` | **树逼的** (否定) |
| `¬laterV`, `nzb` | `rise` 在产生输出时读状态, `keep` 留到以后 (`RKi` 的两句) | **树逼的** (否定) |
| `¬alLim0` | `sum-fst b (nl d) = lim 0 self`; `Al` 的五个构造子 | **树逼的** (否定) |
| `¬cpTop`, `¬relTop`, `¬selfΩ`, `¬hawΩ` | `Ωd (hΩ g)` 的字面, `Act`/`Step` 的字面, `CP` 的定义 | **树逼的** (否定) |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树与折叠, 没有 `Lab`, 没有记号, 没有新脚手架. 一个分类定理对一切实例与一切层; 六条否定各划出一种不能有的形状 (同目标的状态前提, 只有 `ni`-`ni` 的跨层规则, "节点 ≤ 极限" 的读法, 吸收进极限第一位置的对齐, `MonoStep Ωᴴ` 顶层的 `CP`, 本族的 `HAW Ωᴴ`). 这一站新用到的字段: `Chn` 的起点 (状态在坐标层上的读数), `RKi` 两句的输出形状, `sum-fst` 在 `nl` 上的值.
