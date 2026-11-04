# 不开 K 的闭项落到序数: 第一步 (判决: PARTIAL)

> 文件: [NoKCertRd](NoKCertRd.lagda.md) (紧读法), [NoKCertTree](NoKCertTree.lagda.md) (折叠, 改一行), [NoKCertTc](NoKCertTc.lagda.md) (闭项), [NoKCertEval](NoKCertEval.lagda.md) (计值判据), [NoKCertSmall](NoKCertSmall.lagda.md) (判据不空), [NoKCertNeg](NoKCertNeg.lagda.md) (否定), [NoKCertProbe](NoKCertProbe.lagda.md) (有限测试的比较器). 对塔的比较只在 [NoKCertAccept](NoKCertAccept.lagda.md), [NoKCertAcceptT](NoKCertAcceptT.lagda.md), 没有用到记号本身. 接 [LevelNoK](LevelNoK.lagda.md).
>
> **判决: PARTIAL. 界对塔这一件有进展: 紧读法写出来了 (`Tc-of`, 一个定义, 读 `Legal`, 不读记号), 加 `owk` 一行之后, `LevelNoKAccept` 里不一致的三条在测到的范围内一致. 落到序数这一件没有做到: 没有 `Goodᵁ` 的闭包定理, 除 $\psi_0(\Omega_0)=\omega$ 外没有闭项计值到 `Ord₀`, 没有 `Family` 的项, 没有 $\psi_0(\Lambda)$ 的序数树. `chain-stuck` 没有解决. 第一个障碍在 $\Omega$, 比预想的第一站还低: 链点要当下标, 字面的 `Lgl` 不由 `HS` 给 (`no-HS→Lgl`).**
>
> **编译过的定理 (无条件).**
>
> | 东西 | 陈述 | 哪里 |
> |---|---|---|
> | `Tc-of` | `∀ x → Legal x → Cnt x → Tc (toU x)` | [Rd](NoKCertRd.lagda.md) |
> | `cut` | `FS b → Cpᶠ a b → (P : Cp p b) → CutR a P`: 位置在第一位置 $a$ 这份拷贝里, 或者在它之上 | [Rd](NoKCertRd.lagda.md) |
> | `cnt₀`, `cnt-Ω̂`, `cnt-add`, `cnt-tw`, `cnt-Λ`, `cnt-nat` | 连续性数据 `Cnt` | [Rd](NoKCertRd.lagda.md) |
> | `Tψᵗ`, `x̂ᵗ`, `ψ₀Λᵗ` | 带紧读法的闭项, 类型仍是 `T⁰`, 无参数 | [Tc](NoKCertTc.lagda.md) |
> | `Goodᵁ`, `forceᵁ`, `forceᵁ-HS`, `fgh` | 计值判据 | [Eval](NoKCertEval.lagda.md) |
> | `G-x̂₀`, `fgh-x̂₀` | `Goodᵁ (rdZ (x̂ᵗ 0))`, 值 $\omega$. 只说明判据的前提可满足 | [Small](NoKCertSmall.lagda.md) |
> | `no-HS→Lgl` | `(∀ y → HS y → Lgl zero (rdR zero y)) → ⊥`. 前提的反例 `HS-Y` 是定理 | [Neg](NoKCertNeg.lagda.md) |
> | `no-⊑-Cp` | `⊑⁰` 推不出字面第一位置 | [Neg](NoKCertNeg.lagda.md) |
>
> **条件定理.** 没有.
>
> **目标 1: 定位.** 计值要什么写在 `Goodᵁ`: 链点 $y_m$ 读成下标时要 `el j c ⊑̂ el j (rdR j y_m)`, 含字面的 `Lgl`.
>
> | $x$ in $\psi_0(\Omega_x)$ | 第 0 层的树 | 要的证据 | 状况 |
> |---|---|---|---|
> | $0$ | 无闭包, $\omega$ | 自然数的步进 | **定理** `G-x̂₀` |
> | $1$ | 无闭包, 链 `riseΩ` (判断: $\varepsilon_0$) | `⊑⁰` 的单调 | 没有写. 判断约 300 行, 不提高强度 |
> | $\Omega$ | 第一个 `oŝ`, 第 0 层的自链 | `gŝ` 的 `dy`: 字面 `Lgl zero` | **第一个障碍.** `OCF/Free` 的 `GᴺΩ̇` 给的链点只有 `HS`, `no-HS→Lgl` 说这不够 |
> | $\Omega+1$, $\Omega\cdot2$ | 同上 | 同上; 界对塔 (下面) | 没有证书 |
> | $\Omega_2$ | 第一个 `oĉ`, 第 1 层的链 | `gĉ`: $z\approx$ `up 1 η`, `Lgl 1 η` | 没有证书. 第一个链点的下界在第一路径上, 步进字面成立 (测试 `g-Ω₂`, `c-Ω₂`, `l-ψ₁Ω₂`) |
> | $\Omega_\Omega$ (`tw 3`) 起 | 分支里有非自然数的节点 ($\Omega_{\omega+1}$), `ix` 给 0, 高层的链变成第 0 层的自链 | `no-tn-ω⁺` 的同一个点没有绕开 | 判断: 这里即使有证书, 值也是错的 |
>
> `no-id` 说恒等读法在 $\Omega+1$ 上对 `T₀` 没有证书. 这里没有重证它在 $\mathbb U$ 上的类比, 紧读法不在它的前提里.
>
> **目标 2: 紧读法. 做到, 只是测试意义上的一致.** 读法不读记号: `Legal` 给的 `tg`, `dir` 是字面第一位置, 所以切口是两个位置的同步下降. 与 `no-cut` 不矛盾: 那条的输入是 `⊴`, 这里是 `Cpᶠ`. 只靠读法不够, 测试给 2 对 1, 与 `T₀-too-high` 同一个现象; `owk` 一行取自 [GuardBridgeTree](GuardBridgeTree.lagda.md) 之后一致.
>
> **有限测试 ([AcceptT](NoKCertAcceptT.lagda.md), 全部 `refl`, 不是证明).** 比较器 `misQ` 逐闭包比下界, 只读极限第 1 项的数, 走 $\lim$ 与字面 $c+k$, 下标 $<w$, `misP` 沿给定路径同样比.
>
> | 目标 | 比较器, 深, 宽 | 结果 |
> |---|---|---|
> | $\Omega$ | `misQ`, 10, 3 | 一致 |
> | $\Omega+1$ | `misQ`, 10, 2; 8, 3 | 一致. 旧: 10, 2 上 2 对 1 |
> | $\Omega\cdot2$ | `misQ`, 8, 2 | 一致 |
> | $\Omega+2$ | `misQ`, 6, 3 | 一致 |
> | `b-Ω+1`, `b-Ω2`, `b-Ω+1₂` 报错的路径 | `misP`, 宽 3, 3, 2 | 一致; 对照 `ctl-p₁`, `ctl-p₂`, `ctl-p₃`: 旧树在同一路径上报错 |
> | $\psi_1(\Omega_{\Omega_2})$ 读回 | `legalNo`, 5, 宽 2 | 字面步进 0 个不过 |
> | $\Omega_2$ 的链点 | `findB` 8, 2; `chainSteps` 6, 3 | 0 个 `no` |
>
> 随机路径 (scratch, 不在文件里; 种子固定, 25 条, 长度 9, 步子 $\{0,1,1,2,300\}$, 宽 2, 单条 40 秒): 15 条一致, 每条比到 2 到 4 个闭包, 10 条超时, 0 条不一致. 按目标 (一致, 超时): $\Omega+1$ (2, 3), $\Omega+2$ (2, 3), $\Omega\cdot2$ (2, 3), $\Omega\cdot2+1$ (5, 0), $\Omega\cdot3$ (4, 1).
>
> **没有结果 (超时, 不算一致也不算不一致, 运行记录在 scratch, 不在文件里):** `misQ` 10, 3 的 $\Omega+1$ (12 分钟未完); 6, 3 的 $\Omega\cdot2$, $\Omega\cdot2+1$ (各 300 秒); 5, 3 的 $\Omega\cdot3$ (约 170 秒未完, 手动停). **所以 $\Omega\cdot2$ 以上宽 3 的穷尽没有结果, 原来报错的路径是定向测的.** 运行记录: $\Omega+1$ 9, 3 一致 (46 秒).
>
> **未诊断的运行记录.** $\Omega_2+1$, `findB` 深 8 宽 2 给一个 `no`: 下界 `el 1 top` 不在链点的第一路径上 (极限取第 2 项). 同一目标深 6 宽 3, 深 8 宽 1 都没有 `no`. 判断: 可能是比较器只看单个极限项的假阴性, 也可能是证据缺失给的 `o0`; 诊断的打印超时, 没有查清. **这不算 `chain-stuck` 在真树上的复现.**
>
> **目标 3: `chain-stuck`. 暂停.** 没有写新的 `Gd` 变体. 现状 (判断, 没有编译): 字面第一位置的上界必须同时盖住地板与分支. $\Omega_1+3$ 这样的地板不在 $\psi_1(\dots)$ 的第一路径上 (`no-cp-Ω3-Ω2`, `no-fg-floor`), 所以要么分支换成 $M+\eta$ (下界不再升高, 第一位置自动成立; 要写 `Raw` 上跨 `em`, `top` 的加法, 估 300 行; 基本列不再与记号逐项一致, 标签要换, `ψ⁰-not-cong` 是风险), 要么守卫放宽并带表的证据. 这两条都没有写, **都不是被否定**. 见下面第 2 条: 就算链点过了守卫, `Lgl` 也还没有证.
>
> **目标 4: 没有做到.** 没有覆盖塔的类, 没有闭包定理, `x₃` 没有 `Ord₀` 的值, `fgh` 只有 $\omega$ 上的测试 (`fgh-2`).
>
> **第一个障碍.**
>
> 1. **`HS` 不给字面 `Lgl` (编译).** `no-HS→Lgl`. 所以 `Good-≲` 那种到 `OCF/Free` 的桥给不出 `dy`. **只否定这个想法.** 树自己的链点在测到的范围内是字面步进的 (判断: 这就是基本列的 Bachmann 性质).
> 2. **字面步进没有一般的证法 (编译报错, 不是否定).** 证 `Legal (feed x w n)` 要在开项上比较两棵读回的树, 例如折叠里 `Ω̇ t (tcT T)` 与 `Ω̇ k (Tc-at r tc)` 是两个读法证据. 临时文件 (不进仓库) 里最小的形状:
>
> `irr : ∀ (f : ℕ → LG) (tc tc′ : Tc (U.lim f)) → rb (Ω̇ (U.lim f) tc) ≡ rb (Ω̇ (U.lim f) tc′)`, `irr f tc tc′ = refl`. 报错原文: `error: [UnequalTerms]`, `tc n != tc′ n of type Tc (f n)`.
>
> 逐点相等推不出 `lim` 相等, 没有函数外延. `Cp` 的叶子是 `≡`, 所以判断: **块里的 `≡` 要换成 `Raw` 上的结构等价** (`LevelFixCore` 的 `P1` 拒绝的是 `LF` 上的 `≡`, 这个没有试). 代价: `_≅ᴰ_` 的 `ret`, `sec` 在等价的下界上要证据无关, 判断要改 `Lv` 的接口. 没有写.
>
> 3. **`chain-stuck`**, 上面. **`no-tn-ω⁺`**: $\Omega_{\omega+1}$ 起高层的链变成自链, `x₃` 的值即使有证书也不对 (判断).
>
> **判断 (未证).** 证书的下一步: Bachmann 型的闭包定理, $z$ 是 $z'$ 的第一位置推出 $\psi(\iota z)$ 是 $\psi(\iota z')$ 的第一位置, 同时给 `Lgl` 与 `HS`, 不用支配论证, 形状上与阶段无关. 这要紧读法 (分支值不同的两个表, 读到同一个位置) 与结构等价. 没有试, 不知道过不过 `ocv`.
>
> **受记号影响的形状.** `owk` 一行: 看塔定的 (继承 `GuardBridge`). `zpos` (节点 0 答第一支): 继承 `GuardWeakRd`, 那里看塔定的. 读法的回答要与塔的界对上, 这是看塔验收的. `cO`, `ix`, 带链的闭包继承 `LevelNoK`. **树侧逼出的:** `cut` (`Legal` 只有第一位置), `Cnt` 可选 (`Legal` 不含连续性), `no-HS→Lgl`. 不算树自足.
>
> **壁垒 (判断, 没有形式对比).** `cut` 只沿字面第一位置下降, 极限处用 `Legal` 的步进, 不比较两个任意下标, 不判定值; 没有新的序, 没有新的下标类型. `Goodᵁ` 的证据由预言序列给, 不判定. 我没有证明这组定义永不触犯壁垒.
>
> **审计.** 见文件末.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCert where

open import OCF.Align.NoKCertRd using (FS; Legal→FS; cut; CutR; inn; abv; LimV; Cnt; cnt₀; cnt-Ω̂; cnt-add; cnt-tw; cnt-Λ; Tc-of; module Rd)
open import OCF.Align.NoKCertTree using (Tn; module FoldO)
open import OCF.Align.NoKCertTc using (Tψᵗ; x̂ᵗ; ψ₀Λᵗ)
open import OCF.Align.NoKCertEval using (Zᵁ; rdZ; rdR; Goodᵁ; forceᵁ; forceᵁ-HS; fgh)
open import OCF.Align.NoKCertSmall using (G-x̂₀; fgh-x̂₀; fgh-2)
open import OCF.Align.NoKCertNeg using (HS-Y; no-Lgl-Y; no-HS→Lgl; no-⊑-Cp)
open import OCF.Align.NoKCertProbe using (onF; legalNo; findB; chainSteps; ctl-no; ctl-yes)
```

## 审计

`importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LevelFixCore --only OCF.Align.LevelFixVal --only OCF.Align.LevelNoK --only OCF.Align.NoKCert OCF.Align.NoKCert`: 退出码 0, 30 个模块 (本地 19, 库 11), 禁用表命中 0, `--only` 之外 0. 对照 `OCF.Align.LevelNoKAccept`: 退出码 1. `NoKCertAcceptT` 过禁用表 (退出码 0): 它读的是塔 [LadderNFTree](LadderNFTree.lagda.md), 不读记号, 但塔的形状来自记号, 所以仍算验收.

`depslice.py` (语法级, 看不见隐式参数):

| 根 | 到达块数 | 记号模块块数 | 别处的记号词 |
|---|---|---|---|
| `NoKCertRd:Tc-of` | 155 | 0 | 0 |
| `NoKCertTree:Tn` | 260 | 0 | 0 |
| `NoKCertTc:x̂ᵗ` | 372 | 0 | 0 |
| `NoKCertTc:ψ₀Λᵗ` | 376 | 0 | 0 |
| `NoKCertEval:forceᵁ` | 148 | 0 | 0 |
| `NoKCertSmall:G-x̂₀` | 425 | 0 | 0 |
| `NoKCertNeg:no-HS→Lgl` | 160 | 0 | 0 |
| `NoKCertProbe:findB` | 160 | 0 | 0 |
| `NoKCertAcceptT:w-p₁` | 578 | 0 | 0 |
| 正对照 `LevelNoKAccept:a-Ωω` | 410 | 48 | 5 |

全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 没有 `Un`, UIP, 函数外延. 模块参数: `NoKCertTree` 的 `X` 是定义域, `FoldO`, `Rd`, `Rep` 的参数由调用处给, 都不是假设. 这些只保证不引用记号, 不说明定义没有受记号启发.
