# 跨段: 共尾度 Ω 的下标, 第一站 $\psi_1(\Omega)$

> **判决: PARTIAL.** 目标 1 (上移, 树一致) **HOLDS**. 目标 4 (闭项 $\psi_0(\Omega_{\psi_1(\Omega)})$ 的树与 FGH) **HOLDS, 读法是判断**. 目标 2 (跨段节点) 有两层: `Z` 层的 `Node` 带证书 (HOLDS); 数据树 `T` 里的 `tH` 只有定义, 折叠的比较确实都在字面公共上界里. 目标 3 (闭包定理): `Z` 层一步对任何 `Node` (HOLDS); 数据树那一层 **没有** (第一个障碍).
>
> | 定理 | 陈述 | 文件 |
> | --- | --- | --- |
> | `_⊂_`, `up`, `up-mono`, `up-refl`, `up-inj`, `up-tri`, `up-down`, `up-rk`, `up-fst`, `up-trans`, `⊂+` | 字面初始段, 嵌入; 保序且反射, 单射, 三歧形状不变, 像下闭, 秩字面不变 | [CrossMUp](CrossMUp.lagda.md) |
> | `UpWorld.rowq` | 第 0 行的写法沿 `up` 对齐, 对一切 $M\subset M'$ | [CrossMUp](CrossMUp.lagda.md) |
> | `bridge` | `HtB` 两个世界之间的模拟 (条件: `e`, `ε`, `tri-self`, `rowq`) | [CrossMSim](CrossMSim.lagda.md) |
> | `up-sim e p α α′ d` | `Tᵖ M p α ≈ᴿ Tᵖ M′ (up e p) α′`, 无条件 | [CrossMUpTree](CrossMUpTree.lagda.md) |
> | `up-≅`, `up-fgh`, `up-lvl` | 计值 $\cong$, FGH 逐点相等, 层号 $\cong$ | 同上 |
> | `up≺`, `step≺` | 跨段严格增长, 字面 $\prec$ | 同上 |
> | `↑ᴾ`, `↓ᴾ` | 树上的上移与下移算子 (定义; 没有证与折叠交换) | [CrossMLift](CrossMLift.lagda.md) |
> | `Node`, `C`, `νZ`, `Gν 𝒩 M₀` | 分支对一切码; 累加链; 闭包定理对任何节点, 任何起点 | [CrossMNode](CrossMNode.lagda.md) |
> | `rk≼`, `val-next`, `Fix.feed-up`, `Fix.feed-dn`, `Fix.cof-out`, `Fix.cof-ht`, `Fix.y≺` | 严格增长的函数支配秩; 输出与高度互相共尾, 分支严格增长 | 同上 |
> | `𝒯`, `val≼T`, `Fixᵗ` | 塔的实例 | [CrossMInst](CrossMInst.lagda.md) |
> | `T⊤`, `HS⊤`, `lv⊤`, `fgh⊤`, `T⊤ᶜ` | 闭项, 无参数 | [CrossMClosed](CrossMClosed.lagda.md) |
> | `no-⊂⌈⌉`, `≼↛⊑` | 只否定两个证明办法, 见 [CrossMNeg](CrossMNeg.lagda.md) | [CrossMNeg](CrossMNeg.lagda.md), [CrossMNode](CrossMNode.lagda.md) |
>
> **只有定义 (没有证书).** [CrossMTop](CrossMTop.lagda.md): 数据树 `T₊`, `↑T`, `⊞`, `ι↓T`, `Ω̇ᵀ`, `ψᵀ`, `ΨT`, `ψ̄ᵀ`, 闭项 `Tᵀ M α : Run Fl` 对一切 $\alpha$. 读作 $\psi_0(\Omega_{\psi_1(\Omega)+\alpha})$ (判断). 这不算定义了序数: 还不知道它能读回.
>
> **有限测试 (不是证明).** [CrossMClosedTest](CrossMClosedTest.lagda.md): `sh T⊤ = sl`, `fgh⊤ 0 = 1`, 比较器 `refl`, 盲区: 小值不区分强度. [CrossMTopTest](CrossMTopTest.lagda.md): `Tᵀ cz 0` 头部是闭包节点, `Tᵀ cz 1` 头部是极限, 前两项是闭包节点, 比较器 `refl` 看头部, 盲区: 不看界, 不看值. `fgh⊤ 1 ≡ 2` 的 `refl` 在 400 秒, 20G 堆内没有结果; 这不是否定.
>
> **记号一侧 (定理, 只关于记号).** [CrossMAccept](CrossMAccept.lagda.md): `fs-ψΩ`: $\psi_0(\Omega_{\psi_1(\Omega)})[n]=\psi_0(\Omega_{\psi_1(\gamma_n)})$, $\gamma_0=1$, $\gamma_{n+1}=\psi_0(\Omega_{\psi_1(\gamma_n)})$; `fs-ψΩ1-1`: $\psi_0(\Omega_{\psi_1(\Omega)+1})[1]=\psi_0(\psi_u(\Omega_u))$. 树与记号之间 **没有** 定理.

## 读法 (判断)

$\psi_0(\Omega_{\psi_1(\Omega)})$ 是 $x\mapsto\psi_0(\Omega_{\psi_1(x)})$ 的最小闭包点: 记号的基本列就是这条链 (`fs-ψΩ`, 定理). 高度 $x$ 的第 0 行读作 $\psi_0(\Omega_{\Omega\cdot(1+x)})$, $\psi_1(x)=\Omega\cdot\omega^x$, 两条链互相共尾, 所以同一个极限. `T⊤` 的分支是 $C_n$ 上的第 0 行, `Fix` 说输出与高度互相共尾; $\lceil\cdot\rceil$ 可能把值放大, 但放大不超过闭包点 (判断, 没有编译).

**更正 [LadderOrd](LadderOrd.lagda.md) 的一句判断.** 那里说 `T-feed` "仍在 $\psi_1(\Omega)$ 之下". 按上面的读法, `T-feed` 与 `T⊤` 在值上都到了 $\psi_0(\Omega_{\psi_1(\Omega)})$ (仍是判断, 两棵树之间没有定理). 所以第一站的 **值** 不是硬点. 硬点在下一步, 见下.

**读法在闭包点之上不成立 (判断, 依据是定理).** `val≼T` 对一切码成立: 第 0 行的值不低于高度的值, `grow` 又说严格增长. 而记号里 $x$ 超过闭包点 $\beta$ 后 $\psi_0(\Omega_{\Omega\cdot x})$ 还是 $\beta$ ($\beta$ 本身不在闭包里). 所以 [LadderOrd](LadderOrd.lagda.md) 的读法 $\psi_0(\Omega_{\Omega\cdot(1+\mathrm{rk}\,p)+\alpha})$ 只在 $\beta$ 之下算数; 高度超过 $\beta$ 的树是把码当参数的树, 不是那个读法. `Gη`, `T⊤ᶜ M₀` 对一切码有证书, 但这不说明它们到了 $\beta$ 之上的 $\Omega$ 下标.

**为什么下一步要数据树 (判断).** 对任何 $\alpha$, $\sup_M$ `Tᵖ M end α` 都停在同一个闭包点: $M$ 在闭包点之下时, $\psi_0(\Omega_{\Omega\cdot(1+M)+\alpha})$ 也在闭包点之下. 所以逐世界地走 (每个世界里 `qΩ` 只吃本世界的输入) 过不了 $\psi_0(\Omega_{\psi_1(\Omega)})$. 记号里 $\psi_0(\Omega_{u+1})[1]=\psi_0(\psi_u(\Omega_u))$ 要把整个 $\Omega_u$ 放进被折叠的对象, 折叠的叶子是 $\Omega_u$ 本身, 不是某个世界里的近似. 这就是 `T₊` 的 `tH`: 叶子 `Ω̇ᵀ` 又是一个 `tH`, 分支的地板只升不降.

## 第一个障碍

`Tᵀ` 的第 0 行没有证书, 卡在两件事上.

**(a) 分支的证书.** 已有的闭包定理说的是 `Tᵖ` (`ψ̄ᵠ`), 分支是 `ψ̄ᵀ (stepT e)`. 字面不同, 检查器的话 (`Gbranch η = Gᵖ (cz ᶜ+ ⌈ η ⌉) end zero`, 下面略去了重复的项):

```text
error: [UnequalTerms]
OCF.Align.LadderOrdTree.ψ̄ᵠ (HB (cz ᶜ+ ⌈ η ⌉)) (ok₀ ...) (λ i h r → ok₀ ... i) (rowV (HB ...) end (ΩI ...) (fst (viewC ...))) ev₀ zero
!=
ψ̄ᵀ (λ i → ok₁) (λ i → κ-cap ... end (λ _ → tt) i (E-κ (⊂+ cz ⌈ η ⌉) i (ev1 (⊂+ cz ⌈ η ⌉) i))) (ι↓T (rowV (HB ...) end (ΩI ...) (fst (viewC ...)))) ev₀ zero
of type Ord₊ˢ zero Uˢ
```

要的是 `ψ̄ᵀ ∘ ι↓T` 与 `ψ̄ᵠ` 的模拟, 对应世界内的 `D→≈ᵠ`, 判断: 约 200 到 300 行, 没有写.

**(b) 链上的单调性.** `tH` 经 `ψ̄ᵀ` 落成已有的 `ŝ` (证书 `gc`, 规则 `gŝ`). `gc` 要 $y_k\sqsubseteq^0y_{k+1}$, 链点只记得 $\eta$, 世界是 $M$ `ᶜ+` $\lceil\eta\rceil$. `gŝ` 还要对一切 $\eta\sqsubseteq\eta'$ 单调. 上移给不了这个: `no-⊂⌈⌉`; 结构序也不能由 Brouwer 序代替: `≼↛⊑`. `Node` 绕开的办法是把累加写进链 (`C`), 这在 `Z` 层是一个 `lim`, 放不进 `ŝ`. 要放进数据树, 要么 `Ordˢ`, `Z`, `Goodᴺ` 多一个带码的节点, 要么分支把上一个输出字面地加在前面 (`ofL η ⊕ 1 ⊕ …`, 判断: 这样 `gc` 的单调性是平凡的, `⌈a⌉ ⊂ ⌈a ⊕ w⌉` 也对 $w$ 归纳成立; 没有写).

**(c) 闭包定理本身.** (a), (b) 只管 $\alpha=0$. $\alpha\ge1$ 要 `Rel`, `Cx`, `Rules`, `Strict`, `Class`, `Good`, `Omega` 全部带上地板索引和 `tH`, 还要 `↑ᴾ`, `↓ᴾ` 与折叠交换. 现有的闭包定理约 1 万行, 判断: 不能靠重命名脚本得到. 这是未走通, 不是否定.

## 壁垒

没有新的下标类型, `Ordᴵ`, `Code`, `Pos` 都没变. 被比较的两个高度总在同一个 `Pos (cs M′)` 里: `Node` 比较 $C_n$, $C_{n+1}$ 时 $M'=C_{n+1}$; `ΨT` 过 `tH` 时把目标上移. 跨码没有三歧 (`no-tri-code`), 这里也不用. 没有 Ω-共尾元作构造子: `tH` 是对象层的绑定, 落到 `Ordˢ` 是 `ŝ`, 读回时是对角 ℕ-极限.

## 是否按阶段定制

否. `up-sim`, `Gν`, `val≼T`, `rk≼`, `Fix` 对一切码或一切节点成立. `𝒯` 只取 `end` 一个位置和 $\alpha=0$, 这是实例, 不是证明的形状.

## 受记号影响的形状 (如实说)

- 第 0 行, $\Omega_{\psi_1(\Omega)}$ 是 "高度上的闭包", 回灌链的形状: 读自记号的规则 6 (`fs-ψΩ`), 高度 $\leftrightarrow\Omega\cdot(1+x)$ 的读法也是. 不算树自足.
- `T₊` 的构造子照抄 `Q₊`, `Q₊` 的形状读自记号 (见 [LadderInf](LadderInf.lagda.md) 的账). `tH` 的第 0 支 `𝟏ᵀ` 对应 $\gamma_0=1$.
- 没看记号的: `⊂`, `up`, 累加链 `C`, `Node`, Kripke 分支, 新高度默认地板 `Fl`. 这些是 Brouwer 树和类型的要求.

## 没有做的

标签 (树的基本列与记号不逐项一致, `C` 的高度不是 $\omega^{\gamma_n}$; 要标签得换链, 而换链要跨段比较). `T⊤` 与 `T-feed` 的值关系 (要 "位置下面的段" 的一般定理: 每个 $p$ 的树只看它下面的段, 只做了初始段). `↑ᴾ`, `↓ᴾ` 与折叠交换. 上面 (a), (b), (c).

全文 `--safe --without-K` (部分加 `--lossy-unification`), 无公设, 无洞, 无停机或正性编译指示.

## 审计

记号只在 [CrossMAccept](CrossMAccept.lagda.md), 入口不导入它.

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd --only OCF.Align.CrossM OCF.Align.CrossM`: 禁用表命中 0, `--only` 之外 0, 退出码 0; 闭包 59 个本地模块, 没有 `*W*` 克隆, `*Accept`, `EBO`. 正对照 `OCF.Align.CrossMAccept`: 禁用表命中 1 (`EBO`), 退出码 1.
- **定义级切片 `depslice.py` (块数, 记号块, 词命中):** `up` 6, 0, 0; `up-sim` 399, 0, 0; `↓ᴾ` 155, 0, 0; `Gν` 57, 0, 0; `𝒯` 1182, 0, 0; `T⊤` 1193, 0, 0; `fgh⊤` 1195, 0, 0; `Tᵀ` 397, 0, 0; `ΨT` 370, 0, 0; `no-⊂⌈⌉` 24, 0, 0. 正对照 `CrossMAccept:fs-ψΩ`: 51, 43, 3.
- 切片是语法级的, 模块别名和隐式参数看不见; 闭包是编译器保证的, 但不说明定义没有受记号启发.
- **禁用构造:** 全部 `CrossM*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`; 全部带 `--safe --without-K`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossM where

open import OCF.Align.CrossMUp public using (_⊂_; ⊂r; es; el; ⊂-trans; ⊂+; up; up-trans; up-mono; up-refl; up-inj; up-tri; up-down; up-rk; up-fst; module UpWorld)
open import OCF.Align.CrossMUpTree public using (up-sim; up-≅; up-fgh; up-lvl; up≺; step≺)
open import OCF.Align.CrossMLift using ()
open import OCF.Align.CrossMNode public using (Node; node; C; νZ; Gν; νT; νHS; νlv; rk≼; val-next; module Fix; ≼↛⊑)
open import OCF.Align.CrossMInst public using (𝒯; val≼T; module Fixᵗ)
open import OCF.Align.CrossMClosed public using (T⊤; HS⊤; lv⊤; fgh⊤; T⊤ᶜ)
open import OCF.Align.CrossMTop public using (QT; Ω̇ᵀ; ψᵀ; ΨT; ψ̄ᵀ; Tᵀ)
open import OCF.Align.CrossMNeg public using (no-⊂⌈⌉)
open import OCF.Align.CrossMClosedTest using ()
open import OCF.Align.CrossMTopTest using ()
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [CrossMUp](CrossMUp.lagda.md) | `⊂`, `up`, 第 0 行对齐 |
| [CrossMSim](CrossMSim.lagda.md), [CrossMSimEq](CrossMSimEq.lagda.md) | 两个 `HtB` 世界之间的模拟, 由 `LadderOrdCross` 机械改写 |
| [CrossMUpTree](CrossMUpTree.lagda.md) | 树沿上移一致 |
| [CrossMLift](CrossMLift.lagda.md) | 树上的上移, 下移算子 |
| [CrossMNode](CrossMNode.lagda.md) | `Z` 层的节点, 闭包定理, 定点 |
| [CrossMInst](CrossMInst.lagda.md) | 塔的实例 |
| [CrossMClosed](CrossMClosed.lagda.md), [CrossMClosedTest](CrossMClosedTest.lagda.md) | 闭项, FGH, 测试 |
| [CrossMTop](CrossMTop.lagda.md), [CrossMTopTest](CrossMTopTest.lagda.md) | 数据树上的节点, 只有定义 |
| [CrossMNeg](CrossMNeg.lagda.md) | 否定 |
| [CrossMAccept](CrossMAccept.lagda.md) | 记号一侧 (闭包不干净, 不进入口) |
