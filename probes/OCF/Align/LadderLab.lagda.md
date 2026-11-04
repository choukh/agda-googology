# 高度上的标签: 把标签推过 $\psi_0(\Omega_{\Omega\cdot\omega})$

> **判决 (编译过的定理, 无条件, `--safe`; 贴在克隆世界的证书上). 目标 1: HOLDS. 目标 2: HOLDS. 目标 3: HOLDS.** [LadderInf](LadderInf.lagda.md) 对高处树的读法是对的, 现在是定理: `G∞ α` 是 $\psi_0(\Omega_{\psi_1(1)+\alpha})$, `G₂ψ₁+Ω` 是 $\psi_0(\Omega_{\psi_1(1)+\Omega})$. 这是标签路线, 文件读记号, 不算记号无关.
>
> | 定理 | 陈述 | 文件 |
> | --- | --- | --- |
> | `label-∞1` | `Lab (forceᴺ _ (GᴺTᵠ ∞ (suc zero) ev p))` $\psi_0(\Omega_{\psi_1(1)+1})$ | [LadderLabAccept](LadderLabAccept.lagda.md) |
> | `label-∞` | `Lab Y θ`, `NF₁ θ`, $\theta<\psi_0(\Omega_{\psi_1(1)+\Omega})$, $\alpha\cong$ `toLevel Y hY` $\Rightarrow$ `Lab (forceᴺ _ (GᴺTᵠ ∞ α ev p))` $\psi_0(\Omega_{\psi_1(1)+\theta})$ | 同上 |
> | `label-∞ᴺ` | 同上, 上界换成 `NF₁` $\psi_0(\Omega_{\psi_1(1)+\theta})$ | 同上 |
> | `label-∞0`, `label-fin` | $\theta=0$ (不再经 `anchor`); 实例的有限部分 | 同上 |
> | `label-ψ₁+Ω` | `Lab (forceᴺ _ (GᴺTᵠ (top 1) zero ev p))` $\psi_0(\Omega_{\psi_1(1)+\Omega})$ | 同上 |
> | `label-top` | 一切 $n$: `top n` 上 $\psi_0(\Omega_{\psi_1(1)+\Omega\cdot n+\theta})$, $\theta<\psi_0(\Omega_{\psi_1(1)+\Omega\cdot(n+1)})$ | 同上 |
> | `agree-top0`, `mono-1-Ω` | 经 `Lab-uniq`, `Lab-oc`: 实例 ∞ 与 `top 0` 的树同值; $T_{\psi_1(1)+1}\prec T_{\psi_1(1)+\Omega}$ | 同上 |
> | `label-tree`, `label-cert` | 对一切 `HtS`, `PxS`: 树与证书的计值带标签 $\psi_0(\Omega_{P\,m\,\theta})$; 前提 `NF₁` $\psi_0(\Omega_{P\,m\,\theta})$ | [LadderLabTop](LadderLabTop.lagda.md) |
> | `NF-ψ` | `NF₁ θ`, `Ctbl θ`, $\theta<\psi_0(\Omega_{\psi_1(1)+\Omega\cdot(m+1)})$ $\Rightarrow$ `NF₁` $\psi_0(\Omega_{\psi_1(1)+\Omega\cdot m+\theta})$ | [LadderLabNFTop](LadderLabNFTop.lagda.md) |
>
> **条件.** 定理本身无假设, 模块参数只有结构 `𝕊`, `𝕏`, 两个实例都闭合 ([LadderLabInst](LadderLabInst.lagda.md)). 三处范围限制 (不是假设): 证书是克隆 `LadderLabZInfW*` 里的, 不是主线的 `LadderInf*` 里的; $\alpha$ 要 $\cong$ 一棵带标签的树的层号; $\theta$ 要低于上界. $\theta\ge\psi_0(\Omega_{\psi_1(1)+\Omega})$ 时 `Bnd₁` 不成立, 目标不是标准形, 这一行没有标签 (与 $\Omega\cdot m$ 同形, 判断: 那些 $\alpha$ 上树的值没有证明).
>
> **有限测试 (不是证明).** [LadderLabAccept](LadderLabAccept.lagda.md) §4: 主线与克隆的 FGH 在 `∞ 0`, `∞ 1`, `top 1` 的第 0 项上相等, `refl`. §3: 记号形状, `refl`.
>
> **怎么做的.** 上一轮的线索基本对, 下面是实际的账.
>
> 1. **记号 (`LadderLabZStandardOmega`, `LadderLabZSystemOmega`).** `Sb` 加一个构造子 `sψ : ∀ n → Ctbl c → Sb (ψ₁(1) ∷ Ωᵐ n c)`, 奇异叶加 `singψ n`: $\Omega_{\psi_1(1)+\Omega\cdot(n+1)}$, 基本列 $\Omega_{\psi_1(1)+\Omega\cdot n+\eta}$. `sing²` 有的情形 `singψ` 全要有 (`singΩψ`, `SWψ₀`, `SWψ`, `singGψ`, `leafVar`, `fsT-mono₁`, `visLeaf`, `leafLift`, `NF₁-fsT`), 证明几乎逐行相同. **新东西只有一处:** $\psi_1(1)$ 的下标和参数里有 $1$, 所以 $\Omega_{\psi_1(1)+\ldots}$ 经 `vs` 看得见参数 $1$, 要 $1<C[\Omega_{\ldots}]$ (`1<plugR`, `1<plug′`); $\Omega$ 版这里是 $0$. 补丁约 147 行代码; `SystemOmega` 补 2 行 (`Sb-suc`, `leafSb`). 其余 46 个模块**一行不改**, 全部重新检查通过: 下游不看 `Sb` 的构造子 (判断: 这就是单文件试验能下推的原因).
> 2. **前缀 (`LadderLabBase`).** `PxS`: `P : Ht → T → T` 加 11 条记号等式. $\Omega$ 版的硬编码有三处要放开, 都不是数学: `FlU→μ`, `Fw-ψ`, `LimRow` 只用到 $\mu\nu$ 的头是 $\psi_1(\cdot)$ 和 "$\mu\nu$ 对可数项恒 `gt`", 改写成 `FlU→P`, `Fw-ψP`, `LimRowP`.
> 3. **类 (`LadderLabClass`, `LadderLabPsi`, `LadderLabEval`).** 由 `ScafLadderQClass`, `ScafLadderQPsi`, `ScafLadderQEval` 脚本改写, 主体是替换 `Ωᵉ (suc m) ν ↦ P m ν`. 手写的只有: `LV` 走 `Rec`; `Lq-ι↓` 带 $d:n<m$ 且落在 `cap` 上 (`FlC`); `Lq-up` 对 `no<`; 第 0 行 `rowLq` 分三种写法 (`Row₀`), 与证书的 `rowG` 同形.
> 4. **互模拟 (`LadderLabRel`).** 由 `LadderInfWRel` 改写. **这是唯一一个上一轮没预见的卡点, 属于 `--without-K`, 不是数学.** `Lq→O` 同时对 `Lq x u` 和 `Rq x x` 模式匹配. 高度抽象后 `Rq` 的 `rcl`, `rΩ↓` 两边的 $n$ 相同, 对 `Rq x x` 反演要消去 $n=n$ (`Cannot eliminate reflexive equation n = n of type Ht`). `LadderInfWRel` 没碰到这个问题, 因为证书不反演 `Rq x x`. 解法: 两边的 $n$ 分开 (`SameQ q q′`, 回到 `ScafLadderQRel` 的形状), 假设写成 `Hy`, 只有高度相等时有内容; 要读假设的地方 (`R-ι↓` 两处, `R-Ψ` 一处) 用 `unH`, 它要 $n=n$ 的证明唯一, 由 `tri`, `irr` 给的可判定相等得 (Hedberg, `Decidable⇒UIP`), **不是新字段**. 另外 `rwk` 改回成对的构造子, 否则 `qwk` 的反演不唯一; `≅ˢ` 换回 `≅ᴬ`, 因为 `Od` 要的 `Rd` 是 `≈ᴬ`, 而 $\cong^\mathsf A$ 推不出 $\cong^\mathsf S$ (`lᵢ` 的假设方向相反).
> 5. **标准形 (`LadderLabNFOmega`, `LadderLabNFTop`).** `NF-Ωᵐ` 多一个情形: `sψ` 的下标比 $\Omega\cdot(m+2)$ 大, 由上界排除 (`no-ψ¹`). `NF-ψ` 与 `NF-Ωᵐ` 同形.
>
> **与上一轮判断的出入.** "`ScafLadderQClass/Psi/Eval` 对 `HtS` 抽象": 对. "`HSℕ` 的 ∞ 版还要 `NF-Ωᵐ`": 对. "要两件事": 少算了第 4 点. "能不重生成全部就不重生成": 没省下来. 全部依赖 `StandardOmega` (`Prefix` 的 `Z` 也在闭包里, 因为文件顶部导入记号), 重生成只花了 994 秒 (6 个进程), 比切模块便宜. $\psi_1(1)+\Omega$ 没撞上 `noTimes`: 高度是 $\omega+\omega$ 的元素.
>
> **第一个障碍 (判断, 没有试).** 三个目标内没有. 再往上是 $\psi_0(\Omega_{\psi_1(1)\cdot2})=\psi_0(\Omega_{\psi_1(1)+\Omega\cdot\omega})$: 证书要 `HtS` 的实例 $\omega\cdot3$ (`view-step` 够用), `Sb` 要 $\psi_1(1)\cdot k+\Omega\cdot n+c$. 看上去是把 `sψ`, `singψ`, `PxS` 对 $k$ 一致化. $\psi_1(2)$, $\psi_1(\Omega)$ 才要 `view-step` 不够的高度和 `Ordᴵ` (`LadderInf` 的判断, 这里没有新证据).
>
> **克隆的范围与重新生成.** `LadderLabZ*` 84 个模块: `ScafLadderZ*` 的 48 个 (不含 `ScafLadderZLvWalk`), `ScafLadderQ`, `LadderNFW*` 的 8 个, `LadderInfW*` 的 26 个, `LadderInfTop2`. 脚本 `Survey/scripts/ladderlab/mkall.sh`, 逐字节重新生成 (已比较: 90 个生成文件全同). 代码行与来源只差模块名, 例外是 `StandardOmega` 的补丁, `SystemOmega` 的 2 行, `InfWTop2` 的 3 行导入 (脚本比较).
>
> **审计.** 见文末.
>
> **受记号影响的形状 (如实说).** 这组文件就是读记号的. 证书和树是克隆, 不是新的; 高度的形状 $\omega+\omega$ 与 `view` 的分法仍读自记号, 这一点 [LadderInf](LadderInf.lagda.md) 已说明. 标签证实的是读法, 不说明树自足.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 没有写新的 `Goodᴺ`.

## 审计

- **主线不受影响:** 本轮没有改主线. `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf OCF.Align.LadderInfCert`: 通过 (重跑). `depslice.py`: `G∞`, `G₂ψ₁+Ω` 记号 0, 词命中 0 (重跑).
- **克隆的树:** `depslice.py`: `LadderLabZInfWTree:Tᵠ` 222 块, 记号 0, 词命中 0; `Ω̇` 88 块, 0, 0.
- **克隆的证书不干净, 这是预期:** `LadderLabZInfWMain:GᴺTᵠ` 1927 块, 记号 92, 词命中 175. 路径是 `one⁰` 经 `LadderLabZNFWAux` 落在 `LadderLabZDecouple` 里, 那个模块读记号. 所以克隆的证书不能替代主线的审计; 记号无关的结论在主线, 克隆只用于贴标签.
- **正对照:** `label-∞1` 2518 块, 记号 92, 词命中 376; `label-ψ₁+Ω` 2517 块, 92, 375. `importclosure.py OCF.Align.LadderLabAccept`: 失败 (退出码 1), 如预期.
- **克隆与主线:** `LadderInf*` 26 个模块与 `LadderLabZInfW*` 的代码行 (去掉导入、模块头、选项) 逐字相同, 共 6834 行; `LadderInfTop2` 与 `LadderLabZInfWTop2` 同 (脚本比较, 不是定理).
- **禁用构造:** `LadderLab*` 96 个文件的代码块里 `postulate`, 洞, 停机与正性编译指示, `trustMe`, `REWRITE` 命中 0; 选项都含 `--safe --without-K`. 切片是语法级的, 看不见隐式参数和模块别名.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLab where

open import OCF.Align.LadderLabBase public using (PxS; Row₀)
open import OCF.Align.LadderLabInst public using (Px∞; Px₂)
open import OCF.Align.LadderLabNFTop public using (NF-ψ)
open import OCF.Align.LadderLabAccept public using (label-∞; label-∞ᴺ; label-∞1; label-∞0; label-fin; label-top; label-ψ₁+Ω; label-ψ₁+Ω·n; label-ψ₁+Ω+1; agree-top0; mono-1-Ω; B∞)
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [LadderLabBase](LadderLabBase.lagda.md) | 结构 `PxS`, `Row₀` |
| [LadderLabInst](LadderLabInst.lagda.md) | 实例 ℕ∪{∞}, ω+ω |
| [LadderLabNFTop](LadderLabNFTop.lagda.md), `LadderLabNFOmega` | 目标的标准形 |
| `LadderLabRel`, `LadderLabClass`, `LadderLabPsi`, `LadderLabEval` | 标签类, 脚本改写 |
| `LadderLabForget` | `ofL`, `same`, 复制自 `LadderNFAccept` §1 |
| [LadderLabTop](LadderLabTop.lagda.md) | `label-tree`, `label-cert` |
| [LadderLabAccept](LadderLabAccept.lagda.md) | 定理与有限测试 |
| `LadderLabZ*` | 克隆, 不用读 |
