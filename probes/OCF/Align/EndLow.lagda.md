# 终点下界: 主线 $\succcurlyeq$ EBO 的参照树

> **验收入口** (导入验收文件 [EndLowAccept](EndLowAccept.lagda.md); 树侧只有 [EndLowH](EndLowH.lagda.md), 不读记号). 按 `AGENTS.md` 的最佳实践 "中间站给界, 终点对 EBO 验收": 终点先证主线树不低于 `WfFsn.EBO-tree`. **判决: PARTIAL; 终点下界未走通; `BTBOᴵ ≼ ⟪ T-fb 1 ⟫` 暂停 (见 "作者决定 1"); 第一个缺口在第 3 级 ($\psi_0(\Omega_{\Omega_\Omega})$), 是高度的类型, 不是单调.**
>
> 1. **桥** (`⟪_⟫`): 主线闭项 (`A`) 到 `OCF.Align.Level` 第 0 层, 保持并反射值序 (`≤→≼ᴬ`, `≼→≤ᴬ`), 与现成的 `trA`, `fr` 互模拟. 定理.
> 2. **终点恰是逐级下界** (`EBO≼`, `EBO≼⁻`, `EBO≼-from`): 参照树沿 Ω-塔单调 (`treeE-mono`, 由 `fs-tower0`: 塔的第 0 个基本列项是下一级), 所以 `EBO-tree ≼ X` 当且仅当对充分大的 $k$ 都有 `treeE k ≼ X`. `endpoint`: 给出 `Climb` (起点, 归纳步, 都在 $T$ 之下) 就有 `EBO-tree ≼ ⟪ T ⟫`. 定理.
> 3. **第 0, 1, 2 级** ($\omega$, $\psi_0(\Omega)$, $\psi_0(\Omega_\Omega)$): 差树的闭项 `SumOne.T₀`, `TLRuleSum.Top` 不低于它们, 第 2 级互相 $\preccurlyeq$ (`T₀≈E`, `Top≈E`), `T₁` 严格更高 (`E<T₁`). 定理, 无前提 (搬运 `SumOneAccept.T₀≈`, `TLRuleAccept.T≈`, 经 `treeE2≅`). 高度树一族 (`HtOut`) 是条件定理: `FbLow`, 前提 `Acc₁ : BTBOᴵ ≼ ⟪ T-fb 1 ⟫` (一次直接验收, 没有做); 搬到极限闭项 `T-fbω` 另要 `Funext` 与 `HtCrossInst.Hl.N.MonoL (λ n → proj₁ (Λs n)) lΛω 1`.
> 4. **归纳步的形状** (`fs-tower`, `γ-iter`, `step-shape`): 第 $k+1$ 级是 $G_k: x\mapsto\psi_0(\Omega^{(k)}_x)$ 从 $1$ 起的 ω-迭代, `treeE (suc k) ≼ Z` 恰化为 $Z$ 不低于每个 $G_k(\gamma_n)$ 的带标签树. 定理. 从第 2 级到第 3 级要主线上不低于 $G_2(x)=\psi_0(\Omega_{\Omega_x})$ 的算子, 第 1 项已是 $\psi_0(\Omega_{\Omega_{\psi_0(\Omega_\Omega)}})$.
> 5. **第 3 级的缺口.** 按读法 (判断), `TΛ Λ` 过第 3 级要 $\Lambda>\Omega_2$, 在 `H` 里就是严格高于一切高度, 而 `no-top` 说没有 (定理). 所以按读法, `HtFeed`, `HtOut` 的一切闭项 (含 `T-fbω`) 都在 `treeE 3` 之下. 没有编译过的否定: 那要主线折叠的值上界.
>
> **nκ 问题.** 下界方向在第 $\le2$ 级**可以避开** nκ: 只要在一站上直接验收 (`SumOne` 的先例 `SumOneTop` 不用带 `nκ` 的项; 对 `T-fb 1` 是前提 `Acc₁`). 要把下界搬到一个极限闭项 (`T-fbω`) 就**避不开**: `ToLimit` 的前提恰是 `MonoL` (实例之内折叠对状态与世界单调, `HtCross` 第一个障碍 1, 并行的 `KVal` 所攻的事). 第 3 级以上的缺口与 nκ 无关, 在高度的类型 (见 5).
>
> **只管序数** (作者 2026-11-05): 终点的声称只是序数值; FGH 或大数的比较不是目标. `fgh-⟪⟫` 只是桥的副产品 (换名不改 FGH), 不作声称. `Funext` 只出现在验收文件 `EndLowAccept` 的 `FbLow.ToLimit` 里, 用到它的结果都记作条件定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`. 编译要归档拷贝, 见文末.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EndLow where

open import OCF.Align.EndLowH using (_≤ᴴ_; ≤ᴴ-refl; ≤ᴴ-trans; irrᴴ; no-top; emb<Ωᴴ) public
open import OCF.Align.EndLowFb using (Λ₁; Λ₁-Ω′; g₁0-lim; F0-suc; F-Ω; Ωd-hΩ) public
open import OCF.Align.EndLowAccept
  using ( ⟪_⟫; ⟪⟫≅trA; ⟪⟫≅fr; fgh-⟪⟫; ≤→≼ᴬ; ≼→≤ᴬ
        ; treeE; treeE-lab; treeE≼EBO; EBO≼; EBO≼⁻; EBO≼-from; treeE-mono; treeE-≤; treeE2≅; treeE≤2
        ; cof-tower; fs-tower0; fs-tower; γ0; γ-iter; G; γk; lab-fs≼; lab-lim≼; step-shape
        ; T₀≈E; low-T₀; E<T₁; Top≈E; low-Top
        ; module FbLow; Climb; endpoint ) public
```

## 定理表

| 定理 | 文件 | 陈述 (略) | 档 |
|---|---|---|---|
| `⟪⟫≅trA`, `⟪⟫≅fr` | EndLowAccept §1 | 桥与现成映射互模拟 | 定理 |
| `Λ₁-Ω′`, `g₁0-lim`, `F0-suc`, **`F-Ω`**, `Ωd-hΩ` | EndLowFb | `T-fb 1` 的高度是 `hΩ g₁`, $g_1(0)$ = `hl F`, $F(n+1)$ 对一切 $n$ 是 $\Omega$-极限, $\Omega$-极限层的 $\Omega_L$ 带 `nκ` | 定理 (`refl`) |
| `≤→≼ᴬ`, **`≼→≤ᴬ`** | §1 | `a ≤ b ↔ ⟪ a ⟫ ≼ ⟪ b ⟫` (树侧值序 `TLRuleSpec._≤_`) | 定理 |
| `cof-tower`, `fsT-tower`, **`fs-tower0`**, **`fs-tower`**, `γ0`, `γ-iter` | §2 | 塔的共尾度 $\Omega_1$; $\psi_0(\Omega\text{-塔}_{k+1})[n]=G_k(\gamma_n)$, $\gamma_0=1$, $\gamma_{n+1}=G_k(\gamma_n)$, 第 0 项是 $\psi_0(\Omega\text{-塔}_k)$; 对一切 $k,n$ | 定理 (记号侧) |
| `lab-fs≼`, `lab-lim≼` | §2 | 带标签的树不低于它的基本列项; 不高于基本列项的上界 | 定理 |
| **`treeE-mono`**, `treeE-≤` | §2 | 参照树沿塔单调 | 定理 |
| **`EBO≼`, `EBO≼⁻`, `EBO≼-from`** | §2 | 终点 ⟺ 逐级 ⟺ 充分大的各级 | 定理 |
| `treeE2≅` | §2 | `treeE 2 ≅ BTBOᴵ` | 定理 |
| **`T₀≈E`**, `low-T₀`, `E<T₁`, **`Top≈E`**, `low-Top` | §3 | 第 $\le2$ 级 $\preccurlyeq$ 差树闭项; 第 2 级互相 $\preccurlyeq$; `T₁` 严格更高 | 定理, 无前提 |
| `FbLow.low-fb1` | §4 | `Acc₁` ⟹ 第 $\le2$ 级 $\preccurlyeq$ `⟪ T-fb 1 ⟫` | 条件定理 |
| `FbLow.ToLimit.fb1≤ω`, `low-fbω` | §4 | `Acc₁`, `Funext`, `MonoL` ⟹ 第 $\le2$ 级 $\preccurlyeq$ `⟪ T-fbω ⟫` | 条件定理 |
| **`endpoint`** | §5 | `Climb T` ⟹ `EBO-tree ≼ ⟪ T ⟫` | 定理 (参数是 `Climb`) |
| **`step-shape`** | §2 | `treeE (suc k) ≼ Z` ⟸ $Z$ 不低于每个 $G_k(\gamma_n)$ 的带标签树 | 定理 |
| **`no-top`**, `irrᴴ`, `emb<Ωᴴ` | EndLowH | 没有高度严格高于一切高度; 正对照: `Ωᴴ` 严格高于一切可数高度 | 定理 (树侧) |
| 第 3 级的读法链 | §5 | 高度树的闭项都低于 `treeE 3` | 判断 |

## 作者决定 1: `BTBOᴵ ≼ ⟪ T-fb 1 ⟫` (高度树一族第一条序数值定理)

**没有做出来, 也没有编译过的结果能确认或否定 "它不依赖共用的单调引理"; 状态: 暂停.** 编译过的只有形状 (`EndLowFb`), 它们说明这条定理比审稿人设想的难在哪里:

1. `T-fb 1` 的高度 $\Lambda_1$ = `hΩ g₁`, $g_1(0)$ = `hl F`, $F(n+1)$ 都是 $\Omega$-极限 (定理). 闭项的第 0 层回灌走的节点都在层 $g_1(c)\sqsupseteq g_1(0)$ 上 (看 `HtFeedFold` 的 `κΔ`, `Walk` 的判断).
2. 所以 $\psi_0(\Omega_\Omega)$ 那么大的值不是 `T-Ω` 那样出自最外层的回灌 (`T-Ω` 的层都是可数的 `emb c`), 只能出自**套在里面的**回灌: 层 $F(1)$ ($\Omega$-极限, 它的 $\Omega_L$ 带 `nκ`, `Ωd-hΩ`) 上的节点折叠到第 0 层的目标, 在已经非空的状态与世界里 (判断).
3. 因此直接证它有两条路, 都没有现成的: (a) 用共用的单调 (`MonoStep`, `MonoL` 一类) 把那一次套着的折叠比到空状态, 再接一次 `T-Ω` 式的验收; (b) 不用单调, 照 `SumOneTop` 的 `CI` 写一个**精确跟踪状态**的不变量, 但它要穿过带 `nκ` 的不可数层, 而 `SumOneTop` 恰好是因为 "没有用到带 `nκ` 的项" 才不需要单调. 审稿人的判断要成立, 只能走 (b); (b) 是否可行没有定理. 估计 (判断): (b) 在 1000 行以上, 不比 nκ 的值语义省.
4. **建议的替代 (判断):** 高度树一族的第一条序数值定理先取 `HtFeedClosed.T-Ω` (高度 `Ωᴴ`, 层全是可数的, 读 $\psi_0(\Omega_\Omega)$, 与 `SumOne.T₀` 到深度 6 同形, `HtFeedTest`): `BTBOᴵ ≼ ⟪ T-Ω ⟫` 照 `SumOneRel`/`Sim`/`Top`/`Accept` 改写, 估计 600 到 900 行, 不碰 nκ 的值语义, 也不要单调. 由作者定.

## 缺的前提 (Agda 类型原样)

1. `Acc₁ : BTBOᴵ ≼ ⟪ T-fb 1 ⟫`: 高度树折叠的第一次序数值验收. 见上节: 对 `T-fb 1` 要穿过带 `nκ` 的不可数层; 对 `T-Ω` (`BTBOᴵ ≼ ⟪ T-Ω ⟫`) 判断约 600 到 900 行, 不用 nκ 的值语义.
2. `Funext` 与 `Hl.N.MonoL (λ n → proj₁ (Λs n)) lΛω 1` (即 `TΛ-in Λω lΛω (proj₁ (Λs 1)) (hlim 1 hself) ≤ sum β X`): 只在把下界搬到 `T-fbω` 时要; 判断是 nκ 值语义 (折叠对状态与世界单调) 那一类问题.
3. 第 3 级: `Climb.step` 在 $k+K=2$ 处, 经 `step-shape 2` 是 `∀ n → Σ (Ordᶜ zero) (λ Y → Lab Y (G 2 (γk 2 n)) × Y ≼ ⟪ t 1 ⟫)`. 按读法它要高度 $>\Omega_2$, `H` 里没有 (`no-top`). 要的不是引理, 是新的高度类型 (以高度为下标的 $\Omega_x$); 由作者定.

## 第一个障碍

第 3 级. 第 $\le2$ 级在差树上已是定理; 在高度树上只差一次直接验收 (`Acc₁`). 第 3 级要 $G_2(x)=\psi_0(\Omega_{\Omega_x})$, 高度要取 $\Omega_x$ ($x\ge\psi_0(\Omega_\Omega)$), 而 `H` 是第二数类. 主线现在的最高闭项 `T-fbω` 读 $\psi_0(\Omega_{x_\omega})$ ($x_\omega<\Omega_2$), 按读法在 `treeE 3` 之下, 也在 $\psi_0(\Omega_{\Omega_2})$ 之下. 这是判断; 否定要折叠的值上界, 没有做, 只写 "未走通".

## 审计与编译

- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 读记号的 (验收): `T₀≈E` 1388/91/83, `Top≈E` 1154/91/83, `low-T₀` 1404/91/88, `low-fbω` 912/91/88, `low-fb1` 806/91/88, `treeE-mono` 280/70/44, `step-shape` 280/70/43, `endpoint` 293/70/44, `fs-tower` 64/55/2. 不读记号的: `⟪_⟫` 17/0/0, `≼→≤ᴬ` 34/0/0, `EndLowH:no-top` 12/0/0.
- **禁用构造**: 三个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`; 都带 `--safe --without-K --lossy-unification`. `treeE` 在 `opaque` 里 (工程原因, 见 EndLowAccept §2).
- **导入闭包**: `EndLowH` 过 `importclosure.py --only OCF.Align.CumReadCF --only OCF.Align.HtFeedTree --only OCF.Align.HtFeedHt --only OCF.Align.EndLowH --only OCF.BTBO --only OCF.Free.Level` (13 个模块, 本地 5; 禁用表 0, `--only` 之外 0, 退出码 0). `EndLowFb` 过 `--only OCF.Align.CumReadCF --only OCF.Align.HtFeed --only OCF.Align.HtOut --only OCF.Align.HtGen --only OCF.Align.SumOne --only OCF.Align.TLRuleS --only OCF.Align.BrwMid --only OCF.Align.BrwHigh --only OCF.Align.LayerTr --only OCF.Align.EndLow --only OCF.BTBO --only OCF.Free.Level` (19 个模块, 本地 10; 禁用表 0, 之外 0, 退出码 0). `EndLowAccept`, `EndLow` 是验收文件, 闭包含记号, 不审.
- **行数** (代码块里非空非注释行): `EndLowAccept` 200, `EndLowH` 53, `EndLowFb` 33, 入口 10.
- **编译** (从仓库根; 归档只读, 用临时拷贝): 把 `archive/src/Mahlo` 拷到个人临时目录 `<arch>/`, 加 `<arch>/arch.agda-lib` (`name: endlow-arch`, `depend: standard-library-2.4`, `include: .`, `flags: --hidden-argument-puns -W noUnsupportedIndexedMatch`). 堆上限 12G 时要分步: 先在 `<arch>` 里单独编译 `Mahlo/Inacc/Enum`, `Mahlo/Inacc/FGH`, `Mahlo/Inacc/FactsImpl`, 再从仓库根编译 `WfTauNF`, `WfFsn`, 最后 `agda --library-file=<含 stdlib 与 cubical 的库文件> -i src -i probes -i <arch> probes/OCF/Align/EndLow.lagda.md +RTS -M12G -RTS`. 一次编译全部会堆耗尽.
