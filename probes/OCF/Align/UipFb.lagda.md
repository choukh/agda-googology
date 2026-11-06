# UIP 条件下的回灌: 探路

> 入口. 作者选定原话: "在 UIP 条件下先写回灌探路". 这一路只探路, 一切用到 `UIPᴴ` 的结论都是条件定理, 不进成品. 接 [AdmW](AdmW.lagda.md) 的方向 A: `AdmWCoh.dirA-cond` 说在 `UIPᴴ` (高度 `HB S₀` 的相等证明唯一) 之下, `Slot` 上有保相干的更新 `raise₀ᴮ` 与相干世界上的坐标比较 `CmpKᶜ Coh≡`.
>
> **判决.**
>
> 1. **世界侧攀爬 (定理).** 用 `raise₀` 生成的 `Slot` 世界里, 第一级新种类 (坐标 `HB S₁`, `ChainZNeg` 的 `κ₂` 的同形物) 处含新种类节点的格**有界** (`UipFbChain.yes-Ω-cell`, `¬noChainᴿ`): `ChainZNeg.no-chain`/`no-Ω-cell` 的结论在这一族世界里不成立. 第二级 (坐标 `HB S₂`) 同样 (`UipFbTop.bd-κ₃`). 这一条**不用 `UIPᴴ`**: `raise₀` 的四条律本来无条件.
> 2. **`UIPᴴ` 只用于相干 (定理), 外层界有限时用不上 (定理, 对 $b=2$).** 外层界 $b=2$ 时可入坐标的证据唯一 (`UipFbClosed.uniq₂`), 一切世界相干, 坐标比较无条件 (`coh-b₂`, `cmp-b₂`); 对一般有限 $b$ 同样成立是判断 (没有写). 外层界是 $\omega$ 时一切有限坐标同时可入, 证据不唯一, 链的相干是条件定理 (`cohω`, 条件 `UIPᴴ`, 经 `RC`). 两个外层世界上的链逐格相等, 连同合法性 (`same`), 闭项的输入互模拟 (`inω≈`): `UIPᴴ` 世界上的链给不出别的槽.
> 3. **第一级的闭项 (定理, 无条件).** `UipFbClosed.Tᵁ : A`: 升界链 (读界, 升界 $x_{n+1}=x_n\boxplus\mathrm{rd}_2(1,\mathrm{out}_2\,x_n)$, 低层不动) 的槽的 ℕ-极限交给两种种类的折叠 `T⁺`. 合法 (`Lg-Tᵁ`), 有 FGH (`fghᵁ`). **不被压回**: 第一格含新种类节点 (`x₁-new`), 与任何 $H_0$ 嵌入不互模拟 (`¬x₁≈up`), 在世界里有界 (`bd-x₁`); `TdPlusVal.top-bd` 的同形物在这条链上不成立 (`¬top-bd₁`). 第一格就是 `HtTowerNFb.Λs₂ 1` 接在 $0$ 后面 (`x₁≡`, `refl`).
> 4. **第二级: 世界不压回, 现有的折叠压回 (定理); 不压回的第二级未走通.** 以 `HB S₂` 为层的折叠没有; 本路写出的是投影折叠 `fold₂ = T⁺ ∘ pr₂` (合法, `Lg-fold₂`; "现有工具下只写得出投影" 是判断), 它把第二级级顶压回 $\Omega_2$ (`pr₂-top`), 把第 1 条里有界的那个第二级格也压回 (`pr₂-cell`). `pr₂` 不读 `Slot` 的世界. 所以 `TdPlusVal.pr-top` 那种压回是**投影折叠**的性质, 不是世界族的性质. 没有写出不经投影、以 `HB S₂` 为层的折叠, 所以第二级的攀爬**未走通** (没有否定定理; `pr₂-top` 只否定 `fold₂`).
> 5. **对无条件路线 (判断, 依据上面的定理).** 问题不在 `UIPᴴ`. 世界侧在 `UIPᴴ` 下攀爬, 去掉 `UIPᴴ` 要的正是 `RC` (`raise₀` 保 `Coh≡`, LocUip 一路的引理); 有限外界下它已无条件成立. 但即使有 `RC`, 第一级的攀爬也只来自折叠外的读回 `rd₂` (`HtTowerNFb` 已有, 不用任何世界), 第二级卡在折叠: 缺以 `HB S₂` 为层 (或对一切级) 的折叠, 与 `UIPᴴ` 无关.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延. `UIPᴴ` 只作模块参数. 定义不读记号, 没有打开 `EBO`, `Lab`, 标签. 没有改任何已有文件.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 一步 | `yes-cell`: `raise₀` 在 $(c_0,p_0)$ 接 $\delta$ 后, 格 "旧槽 $\boxplus\delta$" 有界; `yes-Ω-cell`: 后继坐标 $c+1$ 处取 $\delta=\Omega_{\mathrm{top}}(G_0\,c)$ | [UipFbChain](UipFbChain.lagda.md) |
| 可达世界 | `ReachR` (起点合法相干, 每步任意可入坐标与合法增量); `reach-lg`; `reach-coh`, `reach-cmp` (条件 `RC`) | 同上 |
| 相干前提 | `RC = RaiseCoh Coh≡ raise₀ᴮ`; `uip→RC` | 同上 |
| 升界链 | `Chain`: 读界 `x n`, 升界 `next` (经 `raise₀`), 低层搬回 `chain-off`; `chain-at`, `chain-cell`, `Λᶜ`, `lΛᶜ`; `chain-coh`, `chain-cmp` (条件 `RC`) | 同上 |
| 第一级实例 | 外层 $(0,2)$, 坐标 $1$, 读回 $\delta(h)=\mathrm{rd}_2(1,\mathrm{out}_2\,h)$; `uniq₂`, `coh-b₂`, `cmp-b₂` | [UipFbClosed](UipFbClosed.lagda.md) |
| 闭项 | `Tᵁ = T⁺ Λᶜ`, `Lg-Tᵁ`, `fghᵁ` | 同上 |
| 外层 $\omega$ | `wω`, `all-adm`; `cohω`, `cmpω` (条件 `UIPᴴ`); `same`, `inω≈` | 同上 |
| 第二级 | `bd-κ₃`, `new-κ₃`, `coh-κ₃`; `pr₂`, `pr₂-mono`, `Lg-pr₂`, `fold₂`, `pr₂-top`, `pr₂-cell` | [UipFbTop](UipFbTop.lagda.md) |

**对照 `RunM` 的三步.** `HtTowerFFold.κc₁`: 读界 ($x_0=\mathrm{rd}(\text{界},z_1)$), 升界 ($x_{n+1}=\mathrm{rd}(x_n,\Delta_n)$), 低层搬回 (`drp₁`). 这里: 读界是槽 `x n` (`slotS`), 升界是 `raise₀` 接 $\delta(x_n)$ (`next`, `chain-at`), 低层搬回是别的可入坐标与外层世界不动 (`chain-off`; 外层世界是模块参数). 不同处: `RunM` 在折叠**之内** (新种类闭包在低层目标上的输出), 这里的链在折叠**之外** (同 `HtOut.Fb`, `HtTowerNFb.Fb₂`), 槽的值作**层**进 `T⁺`. 在折叠之内回灌以 `HB S₁` 为坐标的种类, 要三种种类的折叠 (判断; 第一个障碍).

## 闭项的类型原文

```text
UipFbClosed.Tᵁ     : A                 -- = T⁺ C₁.Λᶜ C₁.lΛᶜ
UipFbClosed.Lg-Tᵁ  : Lg Tᵁ
UipFbClosed.fghᵁ   : ℕ → ℕ             -- = FL.FGH (ord Tᵁ)
C₁.Λᶜ              : HB (G₀ (fin 1))   -- = hl C₁.x, G₀ (fin 1) = step S₀ = S₁
UipFbTop.fold₂     : (Λ : HB S₂) → LgB Λ → A
UipFbTop.t₂        : A                 -- = fold₂ (Ωtop S₁) (Lg-Ωtop S₁)
```

`Tᵁ` 无模块参数, 无前提. 条件定理 (`cohω`, `cmpω`) 以 `UIPᴴ` 为模块参数, 讲的是同一个闭项的世界 (`inω≈`).

## 定理表

档: **定理** = 编译过, 无条件; **条件** = 编译过, 以所写前提为模块参数.

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `yes-cell`, **`yes-Ω-cell`** | UipFbChain | `raise₀` 之后格 "旧槽 $\boxplus\delta$" 有界; 后继坐标处 $\delta$ 取新种类的 $\Omega$-节点 | 定理 |
| `new-Ωtop`, `G₀-hs`, `E-κ₂`, `E-κ₃` | UipFbChain | $\Omega_{\mathrm{top}}$ 含新节点; 坐标类型 (第一级 `HB S₁`, 第二级 `HB S₂`) | 定理 (`refl`) |
| `reach-lg` | UipFbChain | 可达世界合法 | 定理 |
| **`¬noChainᴿ`** | UipFbChain | 对一切可达世界与可入的后继坐标, `no-chain` 的结论不成立 | 定理 |
| `uip→RC` | UipFbChain | `UIPᴴ ⇒ RC` | 条件 (`UIPᴴ`) |
| `reach-coh`, `reach-cmp` | UipFbChain | 可达世界相干; 坐标可比 | 条件 (`RC`) |
| `chain-lg`, `chain-at`, `chain-off`, `chain-≤`, `chain-cell`, `lΛᶜ` | UipFbChain | 链合法, 槽的递推, 低层不动, 世界只增, 第 $n+1$ 格有界, 槽的极限合法 | 定理 |
| `chain-coh`, `chain-cmp` | UipFbChain | 链上世界相干, 坐标可比 | 条件 (`RC`, 起点相干) |
| **`uniq₂`**, **`coh-b₂`**, `cmp-b₂` | UipFbClosed | 外层界 $2$: 证据唯一, 一切世界相干, 坐标可比 | 定理 |
| **`Tᵁ`**, **`Lg-Tᵁ`**, `fghᵁ` | UipFbClosed | 第一级的闭项, 合法, FGH | 定义; 合法是定理 |
| `coh₂`, `cmp₂` | UipFbClosed | 闭项的链上世界相干, 可比 | 定理 |
| `x₁≡`, `x₁-ΩH` | UipFbClosed | 第一格 $=0\boxplus$ `Λs₂ 1`, 最外是新种类的 $\Omega$-极限 | 定理 (`refl`) |
| **`x₁-new`**, **`¬x₁≈up`**, `bd-x₁`, **`¬top-bd₁`** | UipFbClosed | 第一格含新节点, 不与 $H_0$ 嵌入互模拟, 有界; 级顶种类有界的坐标不都是 $H_0$ 的嵌入 | 定理 |
| `all-adm` | UipFbClosed | 外层 $\omega$ 下一切有限坐标可入 | 定理 |
| **`cohω`**, `cmpω` | UipFbClosed | 外层 $\omega$ 下链相干, 可比 | 条件 (`UIPᴴ`) |
| **`same`**, **`inω≈`** | UipFbClosed | 两个外层世界上的链逐格相等 (含合法性), 闭项输入互模拟 | 定理 |
| `bd-κ₃`, `new-κ₃`, `coh-κ₃` | UipFbTop | 第二级的新节点格有界, 相干 | 定理 |
| `pr₂-mono`, **`Lg-pr₂`**, `Lg-fold₂` | UipFbTop | 投影在一致世界里保第一位置; 保合法; `fold₂` 合法 | 定理 |
| `pr₂-up`, **`pr₂-top`**, `hz⊞`, `pr₂-≈`, **`pr₂-cell`** | UipFbTop | `fold₂` 把第二级级顶与第二级的有界新节点格都压回 `Ω₂ᴴ` (互模拟) | 定理 |
| "`Tᵁ` 读 $\psi_0(\Omega_{\Omega_3})$" | — | 读法 | 判断 |
| "`t₂` 读 $\psi_0(\Omega_{\Omega_2})$" | — | 读法 (互模拟输入上 `T⁺` 值相等是判断) | 判断 |

## 是否攀爬

- **(i) `κ₂` 处含新节点的格 (定理).** 有界. `yes-Ω-cell` 对一切可入后继坐标; 在 $c=0$ (坐标 `HB S₁`) 时格就是 `no-Ω-cell` 的 $y\boxplus\Omega_{\mathrm{top}}S_0$. `¬noChainᴿ` 把 `no-chain` 的结论写成谓词, 证它在一切可达世界上为假. 范围: 只说 `raise₀` 生成的世界族; 与 `no-chain` 不矛盾 (那里是 `growL′` 生成的族).
- **(ii) 对照 `pr-top` (定理, 两半).** 第一级: 闭项 `Tᵁ` 的输入的第一格含新节点, 与任何 $H_0$ 嵌入不互模拟 (`¬x₁≈up`), `top-bd` 的同形物不成立 (`¬top-bd₁`); 所以 `pr-top` 的论证 (有界坐标都是嵌入, 投影后退成 $\Omega_2$) 在这里没有前提. 第二级: 投影折叠 `fold₂` 把级顶压回 (`pr₂-top`), 尽管世界里第二级的新节点格有界 (`bd-κ₃`); 压回来自折叠.
- **合起来 (判断).** 第一级攀爬 (读法 $\psi_0(\Omega_{\Omega_3})$, 高于 `Tᴰ₊` 的读法 $\psi_0(\Omega_{\Omega_2})\cdot\omega$; 两者都是判断, 没有值定理). 第二级未走通: 世界侧给了, 折叠侧没有.

## 读法 (判断)

按 `HtTowerNFb` 对 `T-fb₂ω` 的读法: 槽的链每步接一个第 2 层输出的读回, 第一格就是 `Λs₂ 1` ($0\boxplus$ 它), 往后每步 $x_{n+1}=x_n\boxplus\mathrm{rd}_2(1,\mathrm{out}_2 x_n)$ 与 `Fb₂` 的 $\mathrm{rd}_2(x_n+1,\mathrm{out}_2 x_n)$ 只差读回的底 (判断: 同一读法). 所以 `Tᵁ` 读 $\psi_0(\Omega_{\Omega_3})$, 与 `T-fb₂ω` 同读法. 这是 `T⁺` 的层 (`HB S₁`) 能达到的上确界的读法 (判断): 更高要更大的层. 没有序数值定理, 没有与 `Tᴰ₊`, `T-fb₂ω` 的值比较 (缺 `T⁺` 对输入的单调或跨实例比较, 同 `TdPlus` 的 "缺的定理").

`t₂` 是 `T⁺` 在与 `Ω₂ᴴ` 互模拟的输入上的值, 读 $\psi_0(\Omega_{\Omega_2})$ (判断, 同 `TdPlusVal`).

## 对无条件路线的含义

- **若攀爬, 去掉 UIP 要什么 (定理部分).** 本路一切相干结论只经过 `RC = RaiseCoh Coh≡ raise₀ᴮ` (`reach-coh`, `chain-coh` 以 `RC` 为参数, `UIPᴴ` 只经 `uip→RC` 进来). 所以无条件版要的引理恰是 `RC`: 同一坐标 $c$ 的两条证据 $p,p'$ 经 `dD` 给出的两条相等证明 $c_0\equiv c$ 搬出同一个增量. 这是 LocUip 一路的引理. 已知的部分: 外层界有限时 `RC` 的结论 (相干) 无条件成立 (`coh-b₂`); 闭项的链上, 两个外层世界给出逐格相等的槽 (`same`).
- **问题不在 UIP (判断, 依据).** (a) 世界侧的攀爬 (`yes-Ω-cell`) 不用 `UIPᴴ`. (b) 闭项不用 `UIPᴴ` (`Tᵁ` 无前提; `UIPᴴ` 世界上的链给出同样的槽, `same`, `inω≈`). (c) 第一级闭项的攀爬来自折叠外的读回 `rd₂`, 这在 `HtTowerNFb.T-fb₂ω` 里不用任何世界就有了. (d) 第二级卡在折叠: 写得出的折叠是投影折叠, 压回 (`pr₂-top`). 所以有了 `RC` (或 `UIPᴴ`), 下一站要的仍是以 `HB S₂` 为层的折叠, 或对一切级一个折叠 (`HtTowerF` 的第一个障碍 `Need` 一族). 穷尽判断: "只有这两种办法" 是判断, 下一路应先挑战它.

## 第一个障碍

**以 `HB S₂` 为层的折叠.** 第二级的新种类坐标是 `HB S₁`; 在折叠之内回灌它 (对照 `RunM`), 要层的类型含这个种类 (三种种类: `A`, $H_0$, `HB S₁`), 数据树多一种闭包, 沿 `HB S₁` 坐标的走法 (中间穿过两种旧种类的 $\Omega$-极限, 各要一种闭包), 读回层是第 2 层 (`rd₂` 对三种种类的树的版本). 世界就是 `step S₁` 的成对世界 (`Slot` 在坐标 $1$ 处的分量, `G₀-hs`), 不需要 `Slot`, 也不需要 `UIPᴴ`. 判断: 按 `HtTowerF` 的账 (两种种类约 1000 行), 手写一份约同量; 要一切级一个定义, 先要 `Need`. 没有写, 没有否定定理.

`Slot` 与 `UIPᴴ` 真正要用的地方是外层界含极限时 (一切有限坐标同时可入, `all-adm`): 那时折叠要同时处理一切有限级的新种类, 读回要对一切级给出 (对一切 $c$ 读进 `HB (G₀ c)`). 这是对角的折叠, 本路没有碰.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `Chain` (读界, 升界, 低层不动) | `HtTowerFFold.κc₁` 的三步, 换成 `raise₀` | 沿用 (回灌形状来自 `HtFeedFold`/`RunM`, 翻译账在那里) |
| 读回 $\delta(h)=\mathrm{rd}_2(1,\mathrm{out}_2 h)$ | `HtTowerNFb.Fb₂` 的读回, 底换成 $1$ 以接 $\boxplus$ | 沿用 |
| `uniq₂`, `coh-b₂` | 有限界下证据唯一 | 树逼的 (无新字段) |
| `pr₂` | `TdPlusUni.pr` 高一级 | 沿用 |
| `RC` | 把 `UIPᴴ` 换成它实际被用到的那条律 | 树逼的 |

归类: 提供信息. 没有新构造子, 没有改树、折叠或合法性, 没有闭包定理, 没有 `Lab`, 没有序数值验收. 信息是三条: `raise₀` 世界不挡新节点格 (`¬noChainᴿ`); `UIPᴴ` 只经 `RC`, 有限界下不需要, 不改闭项 (`coh-b₂`, `same`); 投影折叠的压回与世界无关 (`pr₂-top` 加 `bd-κ₃`). 这一步没有加深翻译; 它把 "UIP 是不是障碍" 这个问题收窄成 "缺以 `HB S₂` 为层的折叠" (判断).

## 前提可满足

- `UIPᴴ`: `AdmWUip.fe→uip` 由函数外延推出 (条件: Funext). 函数外延与 Agda (`--safe --without-K`) 一致: 它在立方类型论 (Agda 的 `--cubical`) 里是定理, 也在 setoid 模型里成立 (判断, 元层事实, 本路没有形式化). `UIPᴴ` 本身也在集合模型里成立.
- `RC`: 由 `UIPᴴ` 推出 (`uip→RC`).
- 相干起点: `UipFbClosed.cohvz` (全 0 分量, `refl`).
- 可入坐标: `p₁` (外层 $2$), `all-adm` (外层 $\omega$).

## 审计

- **从头编译** (删去本路四个模块的 `.agdai`, 依赖用已有接口, 堆上限 6G): 入口 `agda --library-file=<scratch>/libraries -i src -i probes probes/OCF/Align/UipFb.lagda.md +RTS -M6G -RTS`, 退出码 0, 3.4 秒, 峰值常驻约 0.59G. 依赖的已有模块 (`AdmWCoh`, `HtTowerNFb`, `TdPlusVal` 等) 用的是共享接口, 没有重编.
- **导入闭包** (`importclosure.py`, `--only` 表: `OCF.Free.Level`, `OCF.BTBO`, `OCF.Align.` 下的 `CumReadCF`, `TLRuleSpec`, `TLRuleSum`, `HtFeed`, `HtTower`, `DiagK`, `ChainZ`, `TdPlus`, `StallDx`, `UniTr`, `AdmW`, `UipFb`): `UipFbChain` 45 个模块 (本地 34), `UipFbClosed` 49 (本地 38), `UipFbTop` 53 (本地 42), 入口 54 (本地 43); 都是退出码 0, 禁用表 0, `--only` 之外 0. `AdmWUip` (含 `Funext`) 不在任何一个闭包里.
- **定义级切片** (`depslice.py`, 到达块 / 记号模块块 / 别处记号词): `UipFbClosed:Tᵁ` 252/0/0, `Lg-Tᵁ` 256/0/0, `fghᵁ` 270/0/0, `¬top-bd₁` 116/0/0, `inω≈` 275/0/0, `cohω` 135/0/0, `UipFbChain:¬noChainᴿ` 115/0/0, `UipFbTop:pr₂-top` 69/0/0, `Lg-fold₂` 210/0/0, `bd-κ₃` 113/0/0; 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 切片看不见模块应用 (`module C₁ = Chain …`), 所以 `Tᵁ` 的块数可能少算链的定义; 导入闭包是编译器级的, 覆盖这一处. 只保证不引用, 不说明定义没有受记号启发.
- **禁用构造**: 四个文件的代码块里没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `Funext`; 选项都是 `--safe --without-K --lossy-unification`. `UIPᴴ` 只出现在模块参数 (`UipFbChain.uip→RC` 的参数, `UipFbClosed` §6 的模块参数).
- **代码行** (agda 块里非空非注释): `UipFbChain` 107, `UipFbClosed` 106, `UipFbTop` 84, 入口 6; 合计 303. 文件行: 185, 183, 130, 入口 129.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UipFb where

open import OCF.Align.UipFbChain using (yes-cell; new-Ωtop; yes-Ω-cell; G₀-hs; E-κ₂; E-κ₃; RC; uip→RC; module Reach; module Chain) public
open import OCF.Align.UipFbClosed using (vz; lgvz; cohvz; w₂; lo₂; uniq₂; coh-b₂; cmp-b₂; δ⋆; lδ⋆; p₁; module C₁; Tᵁ; Lg-Tᵁ; fghᵁ; coh₂; cmp₂;
  x₁≡; x₁-ΩH; x₁-new; ¬x₁≈up; bd-x₁; ¬top-bd₁; wω; loω; all-adm; module Cω; same; inω≈; cohω; cmpω) public
open import OCF.Align.UipFbTop using (S₂; v₃; cell₃; bd-κ₃; new-κ₃; coh-κ₃; pr₂; pr₂-mono; Lg-pr₂; fold₂; Lg-fold₂; pr₂-up; pr₂-top; t₂; pr₂-cell) public
```
