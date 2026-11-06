# 折叠对一切高度有定义: 让回灌能 $\Omega$-迭代

> 摆脱侧. 入口. **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 不改 `H` (作者 2026-11-05 定). 定义不读记号, 没有验收文件, 没有打开 `EBO`, `Lab`, 标签.
>
> 问题 ([HtOut](HtOut.lagda.md) 第一个障碍 2): 回灌 `Fb : HL → HL` 只在合法高度上有定义 (折叠的比较 `rkT` 要最高层合法), 而 $\Omega$-迭代要全函数 $H\to H$; `HtOutNeg.no-total` 说连续且严格变大的分支在不合法坐标上必有不合法的高度.
>
> 一句话: **全函数做得到, 在合法处不变做不到.**
>
> 1. **否定** ([HtTotalNeg](HtTotalNeg.lagda.md)). 折叠只在比较 `rkT` 处用到最高层的合法性 (看 `HtFeedFold` 的定义), 所以可动的是比较, 或最高层本身. 两种在合法处不变都推出 LPO: `no-clamp` (夹法在合法高度上是恒等), `no-valid` / **`no-agree`** (比较器在一切最高层 $1\boxplus g\,c$ 上有定义, 在合法坐标 $c$ 上与 `rkT` 判得一样; $g$ 是任一连续、后继严格变大的分支, 比较器可以看 $c$). 原因是树逼的: $\mathbb N$-极限 `hl f` 不带相邻项的路径, 相邻项的路径只在合法性证明里, 不是高度的函数 (判断: 折叠真的要用它, 同 `HtCrossNeg.path-real`).
> 2. **全函数** ([HtTotalClamp](HtTotalClamp.lagda.md)). 夹法 `cl` 用部分和 (`⊞ᴴ`) 把任何高度变成合法的 (`Lg-cl`, 无前提); `TΛᶜ h = TΛ (cl h) _`, **`Fbᶜ h = rd (h+1) (out₁ (cl h) _)`** 对一切高度有定义, 折叠本身不改, 比较仍是合法最高层上的 `cmpH`. 在有限高度上与 `TΛ`, `Fb` 相等 (`TΛᶜ-fin`, **`agree-fin`**, `≡`); 合法的 $\omega$ 被挪动 (`cl-moves`); 按 1, 全有定义的夹法不能在一切合法高度上不动 (否则 LPO).
> 3. **$\Omega$-迭代** ([HtTotalIter](HtTotalIter.lagda.md)). `Fbᶜ` 是 `HtFeedHt.Good` (`Good-Fbᶜ`; 一般地 `Good-rd`: 底取 $h+1$ 的读法一律 `Good`), 所以 `Ωit`, `Tk`, `Tω` 都用得上, 合法性是 `HtFeedHt` 的一般定理的实例, 不要坐标合法, `no-total` 不挡. 高度 `ΛΩ₀ = Ωit Fbᶜ 0` (第 0 支就是 `Λs 1`), `ΛΩ = Ωit Fbᶜ Λω`, `Λ²ω`, `ΛT = Tω Fbᶜ Λω`; 闭项 `T-Ω₀`, `T-Ω`, `T-Λ²ω`, `T-T` (原来的 `TΛ`, 高度合法, 不经夹法); 增长 `Sup-Ω₀`, `Sup-Ω`, `Sup-Tk k`, 与 `HtFeedGrow.Sup` 同档.
>
> **没有做到的:** 迭代里每一步是 `Fbᶜ`, 不是 `Fb`; 两者在合法的无穷高度上的差没有定理 (只有判断: `Fbᶜ` 不低于 `Fb`, 因为 `cl` 只把高度变大). 闭项之间跨实例的比较 (`T-Ω` 对 `T-fbω`) 仍没有 (同 `HtCross` 的障碍). 一切值.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 夹法 | `cl`: $0$, 后继原样; $\lim f\mapsto\lim_n(\mathrm{cl}f_0\boxplus\cdots\boxplus\mathrm{cl}f_n)$; $\mathrm{h\Omega}\,g\mapsto$ 沿坐标的部分和, 极限坐标处连续 (`nb`) | HtTotalClamp |
| 合法 | `Lg-cl : ∀ h → LgH (cl h)`; 极限处 `⊞ᴴ-fst`, $\Omega$-极限处 `cont→LgH` | 同上 |
| 全有定义的闭项, 回灌 | `TΛᶜ h = TΛ (cl h) _`; `Fbᶜ h = rd (h+1) (out₁ (cl h) _)`: 只夹折叠的最高层, 底不夹 | 同上 |
| 合法性与折叠无关 | `Good-rd`: 任何 `x : H → D₁ 1`, `h ↦ rd (h+1) (x h)` 都 `Good`; `rd-n0`: `x` 取空树就是后继 | 同上 |
| $\Omega$-迭代 | `Ωᶜ = Ωit Fbᶜ`; `ΛΩ₀`, `ΛΩ`, `Λ²s`, `Λ²ω`, `ΛT = Tω Fbᶜ Λω` | HtTotalIter |
| 判定 | `Rk`, `Valid` (同 `HtCrossRun.Val`), `Cmp g`, `ValidAt g` | HtTotalNeg |

**为什么不另写一个折叠.** 否定 1 说, 不论比较器怎么写, 只要全有定义且在合法坐标上与 `rkT` 一致就推出 LPO; 所以另写一个以比较器为参数的折叠 (例如路径前缀相同才保留, 否则上升) 也不能在一切合法坐标的一切路径上与原来判得一样 (否则 LPO), 而它还要复制折叠的十六个函数. 夹法不复制折叠, 判定仍有效, 代价落在最高层的值上 (见累加的账). 带参数比较器的折叠没有写, 不是否定.

**累加的账** (判断, 两边都记). 好处: 全有定义, 不改 `H`, 不改折叠, 合法性由形状给出; 有限高度上与原来逐字相等. 代价: 部分和在可加主数的上升列上不改上确界, 别处变大 ($\lim_n(\Omega+n)$ 变成 $\Omega\cdot\omega$ 那一档; $\Omega$-分支 $c\mapsto\Omega+c$ 变成 $\Omega^2$ 那一档); 所以 `Fbᶜ` 在合法高度上读 $\psi_1(\Omega_{1+\mathrm{cl}\,h})$ 而不是 $\psi_1(\Omega_{1+h})$. 判断: 在回灌的迭代里这个差被吸收 (回灌一步的增长远大于 `cl` 的放大), 没有定理.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| **`no-clamp`** | HtTotalNeg | $\kappa$ 总给合法高度, 且合法处 $\kappa\,h\equiv h$ ⇒ LPO | 否定, 定理 |
| **`no-valid`** | HtTotalNeg | 对一切连续且后继严格变大的 $g$: 在一切 $g\,c$ 上有定义、在合法坐标上有效的比较器 ⇒ LPO | 否定, 定理 |
| `no-valid-top⁺`, `no-valid-all` | HtTotalNeg | 最高层取 $1\boxplus g\,c$; 比较器对一切最高层, 在合法最高层上有效 | 否定, 定理 |
| `old-valid` | HtTotalNeg | `HtFeedFold.rkT` 在合法最高层上有效 (`HtCrossRun.Val.rk-valid` 的改写) | 定理 |
| **`no-agree`** | HtTotalNeg | 比较器在合法坐标上与 `rkT` 判得一样 ⇒ LPO | 否定, 定理 |
| `gs-lim`, `gs-suc`, `Kgs` | HtTotalNeg | `no-valid`, `no-agree` 的分支前提可满足 | 定理 |
| **`Lg-cl`** | HtTotalClamp | 一切高度夹出来合法, 无前提 | 定理 |
| `cl-fin`, `TΛᶜ-fin`, **`agree-fin`** | HtTotalClamp | 有限高度上 `cl` 是恒等, `TΛᶜ ≡ TΛ`, `Fbᶜ ≡ Fb` (任一合法性证明) | 定理 |
| `cl-moves` | HtTotalClamp | `cl` 挪动合法的 $\omega$ | 否定, 定理 |
| **`Good-rd`**, `Good-Fbᶜ`, `fbᶜ-fst`, `rd-n0` | HtTotalClamp | 底取 $h+1$ 的读法都 `Good`; `Fbᶜ` 是; $h+1\lhd\mathrm{Fb}^{\mathsf c}\,h$; 空输出就是后继 | 定理 |
| `TΛᶜ`, `Lg-TΛᶜ`, `Fbᶜ` | HtTotalClamp | 对一切高度的闭项与回灌 | 定义; 合法性是定理 |
| `Good-Ωᶜ`, `lΛΩ₀`, `lΛΩ`, `lΛ²ω`, `lΛT` | HtTotalIter | 迭代高度合法 | 定理 (`HtFeedHt` 一般定理的实例) |
| `ΛΩ₀-0` | HtTotalIter | `ΛΩ₀` 的第 0 支就是 `HtOutFeed.Λs 1` | 定理 |
| `ω⊲Ω`, `Ω⊲Λ²ω`, `Ω⊲ΛT` | HtTotalIter | $\Lambda_\omega\lhd\Lambda_\Omega\lhd\Lambda^2_\omega$, $\Lambda_\Omega\lhd\Lambda_T$ (第一位置, 高度上) | 定理 |
| `T-Ω₀`, `T-Ω`, `T-Λ²ω`, **`T-T`**, `Lg-T-T`, `fgh` | HtTotalIter | 闭项 | 定义; 合法性是定理 |
| **`Sup-Ω₀`, `Sup-Ω`, `Sup-Tk`** | HtTotalIter | `HtFeedGrow.Sup` 那一档: 闭包站严格高于前缀站的任意可数子族 | 定理 |
| `no-agree-it` | HtTotalIter | `no-agree` 用在 `it Fbᶜ x` 上 | 否定, 定理 |

**否定的范围.** `no-clamp` 只否定 "夹法在一切合法高度上是恒等"; 不否定在某一类合法高度上是恒等 (`cl` 在有限高度上就是), 也不否定值相等的夹法. `no-valid`, `no-agree` 只否定比较器在**它能收到的一切路径**上一致; 不否定只在折叠实际发出的比较上一致. 判断: 折叠确实发出证明里那一种比较. 理由: 以 $\lim F$ 为最高层时, $\Omega_{\lim F}$ 的节点 $F(1)$ 上升成链, 链的第 0 项在目标 $F(1)$ (路径 `hlim 1 hself`) 上读状态, 状态里有节点 $F(0)$ (路径 `hlim 0 hself`) 的贡献, 于是要判 $F(0)$ 是否严格低于 $F(1)$. 这条没有编译. 也不否定判定不同而输出的值相同. LPO 的前提可满足性同 `Barrier`: LPO 在 `--safe` 下不可证, 所以这几个定理说的是满足前提的东西在纲领内写不出来.

**与壁垒.** 合法的最高层是被比较的两个位置的字面公共上界, `cmpH` 是这个上界之内的比较. 最高层不合法时, $\mathbb N$-极限的两支之间没有路径, 上界只是形式上的. 再要比, 就是 `noBT`, `no-bra-cmp` 那一族; `no-valid` 是同一现象在 "最高层是迭代的一个坐标" 上的形式.

## 闭项与读法

**读法都是判断** (纸面, 按 `HtFeed`, `HtOut` 的读法: `TΛ Λ` 读 $\psi_0(\Omega_\Lambda)$, `Fb h` 读 $\psi_1(\Omega_{1+h})$ 那一段, 底 $h+1$ 被吸收). 记 $x_\omega$ 为 `HtOut` 的 `T-fbω` 的高度的读法.

| 闭项 | 高度 | 读法 (判断) |
|---|---|---|
| `T-Ω₀` | `Ωit Fbᶜ 0`: 第 $c$ 支是 `Fbᶜ` 从 `Λs 1` 起迭代 $c$ 次 | $\psi_0(\Omega_y)$, $y$ 是回灌映射从 $0$ 起的第 $\Omega$ 次迭代, 在 $x_\omega$ 之上 |
| `T-Ω` | `Ωit Fbᶜ Λω` | 同上, 从 $x_\omega$ 起 |
| `T-Λ²ω` | 上一行沿 ℕ 再迭代的对角 | 更高 |
| `T-T` | `Tω Fbᶜ Λω`: `HtFeedHt` 的变换族 (读 $\Omega^{\Omega^\omega}$ 的那一族) 以回灌为底 | 更高 |

四个的界 (判断): $\psi_0(\Omega_{\varepsilon_{\Omega+1}})<\cdot<\psi_0(\Omega_{\Omega_2})$. 下界: 都高于 `T-fb 2` 的读法 $\psi_0(\Omega_{x_2})$, $x_2>\varepsilon_{\Omega+1}$ (`HtOut`). 上界: 高度是第二数类的树, 值在 $\Omega_2$ 之下. 中间的 $y$ 不能用 $\Omega$ 的算术写. 跨实例的比较 (例如 `T-Ω` 高于 `T-fbω`) 都没有定理, 只有高度上的第一位置 (`ω⊲Ω`, `Ω⊲Λ²ω`, `Ω⊲ΛT`) 与实例之内的 `Sup`.

## 第一个障碍

1. **`Fbᶜ` 与 `Fb` 在合法无穷高度上的关系.** 要么证 `cl` 不改值 (对 `rd` 读出的那一类高度; 判断: 它们的分支多是可加主数, 部分和不改上确界), 再用跨实例的换算 (`HtCross.change` 一类) 证 $\mathrm{Fb}^{\mathsf c}\,h$ 与 $\mathrm{Fb}\,h$ 值相等; 要么接受 `Fbᶜ` 本身作定义. 前者要第 4 层的值, 未走通.
2. **全有定义而在合法处不变的回灌**, 按否定 1 不能靠比较器或恒等夹法. 剩下的: 让迭代的坐标进入折叠的世界 (世界总合法, 比较只在世界之下的坐标间进行), 也就是让折叠自己做 $\Omega$-迭代, 读第 2 层的输出 (`HtOut` 障碍 4). 没有试.
3. 跨实例的比较与值: 同 `HtOut`.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 夹法必须挪动合法高度 | `no-clamp` | **树逼的** |
| 比较器不能在合法处一致 | `no-valid`, `no-agree` (合法性证明里的路径是折叠要的信息, `HtCrossNeg.path-real`) | **树逼的** |
| `cl` 的形状: 部分和, 用 `⊞ᴴ` | `⊞ᴴ` 是现成的保证 "$a$ 是 $a\boxplus b$ 的第一位置" 的运算 (这里没有现成的第一位置的并); $\Omega$-分支处沿坐标用 `nb` (连续由 `cont→LgH` 逼出, 同 `HtOutRead`) | **选择** (累加; 账见上); 形状由第一位置的单调逼出 |
| 只夹折叠的最高层, 底 $h+1$ 不夹 | 合法性只要底合法 (`Lg-rd`), 新高度仍以 $h+1$ 为第一位置 | 选择; 由 `Good-rd` 支持 |
| $\Omega$-迭代 `Ωit`, `Hier`, `Tk`, `Tω` | `HtFeedHt` 原样, 以 `Fbᶜ` 代 `hs` 作底 | 沿用; 那一族原来是照 $\Omega\cdot2$, $\Omega^k$, $\Omega^{\Omega^k}$ 的算术写的生成规则 (见 README 翻译账 `HtFeedTree` 一行的 "高度本身仍是给定的数据"); 这里底换成回灌 |
| 折叠本体, `S = ω⋅`, `out₁`, `rd` | `HtFeed`, `HtOut` 原样 | 同 README 翻译账 `HtFeedTree`, `HtFeedFold`, `HtOutRead` |

**按 `AGENTS.md` 归类: 提供信息.**
- 加深的三个标志: 新构造子或节点字段读自基本列规则: **没有** (没有新类型; `H`, `D₊`, 折叠都不变). 闭包定理新增专属前提: **没有** (`Lg-cl`, `Good-rd` 无前提; `Sup-*` 是 `HtFeedGrow` 的实例). 只能用 `Lab` 验收: **不是**.
- 提供信息的三个标志: 对结构参数的一步定理: **有** (`Lg-cl` 对一切高度, 新用到的是 `hl` 与 `hΩ` 两个构造子上的 `⊞ᴴ-fst`; `Good-rd` 对一切读法; `no-valid` 对一切连续严格变大的分支, 用到的是 `hl` 不带路径). 序数值验收: **没有**. 否定定理划出不能有的: **有** (`no-clamp`: 恒等夹法; `no-valid`, `no-agree`: 合法处一致的全比较器).
- 摆脱了什么: `HtOut` 障碍 2 里 "`Fb` 只在合法高度上有定义, 不能 $\Omega$-迭代" 这一条, 在 `Fbᶜ` 上解除. 没摆脱的: 迭代的形状 (`Ωit` 一族) 是 `HtFeedHt` 的生成规则, 不是从输出读出来的, 这一面比 `HtOut` 的 `T-fbω` (只用回灌与 ℕ-对角) 退了一步; 被迭代的是 `Fbᶜ` 不是 `Fb`.

## 账

**定义级切片** (口径同 `htfeed/locslice_htout.py`: 计 agda 非空非注释行, 记号模块除外; 脚本在临时目录 `httotal/locslice_httotal.py`).

| 路线 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加增长 |
|---|---|---|---|---|
| HtFeed, 高度给定 | 51 | 661 (去共用 578) | 665 (去共用 582) | 892 (净增 227) |
| HtOut, 回灌沿 ℕ; 闭项 `T-fbω` | 51 | 643 (去共用 560) | 649 (去共用 566) | 892 (净增 243) |
| **HtTotal, 回灌的 $\Omega$-迭代; 闭项 `T-T`** | 51 | 761 (去共用 678) | 767 (去共用 684) | 990 (净增 223) |

- 层 2 按模块: HtFeedTree 220, HtFeedFold 167, HtOutRead 82, HtFeedHt 64, Free.Level 56, HtTotalIter 36, CumReadCF 36, BTBO 27, HtOutFeed 27, HtTotalClamp 24, HtFeedClosed 22. 与 `HtOut` 比: 多了 HtFeedHt 64 (`it`, `Ωit`, `Hier`, `Tk`, `Tω` 与它们的 `Good`; `Good` 记录里带着合法性, 所以算在层 2), HtTotalIter 36, HtTotalClamp 24 (`cl`, `Lg-cl`, `Fbᶜ`, `Good-rd`); 少了 HtOutFeed 6. 折叠没有复制.
- 层 3 多 6 行 (`Lg-T-T` 是 `Lg-TΛ` 的一次调用).
- 增长净增 223 行 (HtFeedGrow 193, TLRuleSpec 24, HtTotalIter 6); 本路新写的只有 6 行.
- 独立切片: 夹法加合法 (`cl`, `Lg-cl`) 108 行 (HtOutRead 43, HtFeedTree 27, CumReadCF 20, HtTotalClamp 18); 否定 (`no-clamp`, `no-valid`, `no-agree`) 377 行 (HtTotalNeg 171, HtFeedTree 76, CumReadCF 36, HtOutRead 30, BTBO 23, HtCrossRun 14, HtFeedFold 12, 其余 15); 只算 `no-clamp`, `no-valid` 是 186 行; 一致 (`agree-fin`, `TΛᶜ-fin`) 599 行, 几乎都是折叠本身.
- 文件级 (代码块里非空非注释行): `HtTotalNeg` 201, `HtTotalClamp` 74, `HtTotalIter` 74, 入口 5, 合计 354.

## 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtOut --only OCF.Align.HtCross --only OCF.Align.HtTotal`): `HtTotal` (34 个模块, 本地 24), `HtTotalNeg` (30, 本地 20), `HtTotalClamp` (19, 本地 10), `HtTotalIter` (33, 本地 23) 都是退出码 0, 禁用表 0, `--only` 之外 0. `HtTotalNeg` 的闭包含 `HtCrossRun`, `HtCrossSim` (只为 `old-valid` 引 `rk-valid`).
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtTotalIter:fgh` 196/0/0, `HtTotalIter:T-T` 178/0/0, `HtTotalIter:Lg-T-T` 181/0/0, `HtTotalIter:T-Ω` 168/0/0, `HtTotalIter:T-Ω₀` 161/0/0, `HtTotalIter:T-Λ²ω` 170/0/0, `HtTotalIter:Sup-Ω` 240/0/0, `HtTotalIter:Sup-Tk` 245/0/0, `HtTotalIter:no-agree-it` 203/0/0, `HtTotalClamp:Fbᶜ` 139/0/0, `HtTotalClamp:TΛᶜ` 130/0/0, `HtTotalClamp:Lg-cl` 29/0/0, `HtTotalClamp:agree-fin` 149/0/0, `HtTotalClamp:Good-rd` 48/0/0, `HtTotalNeg:no-clamp` 34/0/0, `HtTotalNeg:no-valid` 42/0/0, `HtTotalNeg:no-agree` 106/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发 (见翻译账).
- **禁用构造**: 四个文件的代码块无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 无 `Funext`, 不用 `--cubical`; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (`--ignore-interfaces`): 入口退出码 0 (35 秒, 峰值 1.0G).

## 时间线

写定义前读过: `HtOut*` 全部, `HtFeedTree`, `HtFeedFold`, `HtFeedClosed`, `HtFeedHt`, `HtFeedGrow` 的头与 `ΩSt`, `HtCross`, `HtCrossSim`, `HtCrossRun` 的前 120 行, `CumReadCF` 的签名, README 的 "主线与下一步" 与 "翻译账". 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTotal where

open import OCF.Align.HtTotalNeg using (LPO; Rk; Valid; Cmp; ValidAt; no-clamp; no-valid; no-valid-top⁺; no-valid-all; module Old; no-agree; gs; gs-lim; gs-suc; Kgs) public
open import OCF.Align.HtTotalClamp using (cl; Lg-cl; fin; cl-fin; cl-moves; TΛᶜ; Lg-TΛᶜ; Fbᶜ; Good-rd; rd-n0; Good-Fbᶜ; fbᶜ-fst; TΛᶜ-fin; agree-fin) public
open import OCF.Align.HtTotalIter using (Ωᶜ; Good-Ωᶜ; ΛΩ₀; ΛΩ₀-0; ΛΩ; ω⊲Ω; Λ²ω; Ω⊲Λ²ω; ΛT; Ω⊲ΛT; T-Ω₀; T-Ω; T-Λ²ω; T-T; Lg-T-T; fgh; Sup-Ω₀; Sup-Ω; Sup-Tk; no-agree-it) public
```
