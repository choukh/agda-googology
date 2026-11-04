# 折叠是和的作用: 这几行规则哪些是值逼的

> 入口. **判决: PARTIAL.** 档次逐条写在下面. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 定义 ([TLRuleSum](TLRuleSum.lagda.md)) 不读记号; 记号相关的只在 [TLRuleAccept](TLRuleAccept.lagda.md), [TLRuleVar](TLRuleVar.lagda.md), 而且只读旧树, 不读标签.
>
> 一句话: $\psi_0(\Omega_\Omega)$ 这一站换一个写法: **树的极限节点是差的和, 折叠是和上的作用**, 除了讲和的 `Lg-sum` 没有合法性证明, 没有 `add`, 没有 `rep`, 没有 $\psi(\lim)$ 这一行, 与 `BTBOᴵ` 互相 $\preccurlyeq$ (`T≈`, `TΣ≈`), 顶层也带字面的 `Lg` (`Lg-TopΣ`). 只剩一行是选择: 一步 $S$; 换 $S$ 值就变 (`gap-Ω₁`); 要求输出对加法封闭, 这一步的值唯一 (`ω-uniq`). 那个要求本身是选择, 不是树逼的.

## 定义, 不是证明

    data D L: n0 | n1 | x ⨾ y | nl d | ni r u      -- 空, 一, 先后, ∑_n d_n, ∑_w u(w)

第 0 层的树 `sum b x` 给层: 第 $n$ 个部分和字面是第 $n+1$ 个部分和的第一位置, **对一切 $x$, 无前提** (`sum-fst`, `Lg-sum`). 这就是 "合法性由树的定义保证". 不是把证明塞进构造子: 构造子里根本没有证明, 单调性来自 "和" 这个写法. **如实说:** 比较 `cmpN` 仍要 `Lg W`, 所以定义里用到 `Lg-sum`; 但它只有十几行, 无前提, 只讲和, 不提折叠, 与 `HS`, `Goodᴺ`, `WF`, `ψW` 不是一类东西. 对照:

| 已有的否定 | 否定的是什么 | 这里为什么不撞 |
|---|---|---|
| `Cumsum.ψᴱ-not-mono`, `Certified.ψ-not-⊑mono` | 折叠对结构序单调 | 这里的 `lim` 不带步进证据, 不要输入单调. 输出的步进是字面的前缀 (`row-⨾`), 只沿积分的位置, 不沿任意分支. `no-full` 说全分支本来就不可能 |
| `Cumsum.overshoot` | 把任意 `lim` 换成累加改值 | 这里没有事后累加: 差是定义的一部分, 层的值就是树的值. 部分和在形式上就是累加, 这一点如实说; 区别是 $d_n$ 是折叠算出来的真差, 不是序列本身 |
| `no-tri-code`, `barrier` | 全局三歧 | 比较只有 `cmpN`, 都在世界 $W$ 之内, 有字面公共上界 |

折叠 `Run A w δ Y`: 状态 `Y` 记每个目标 $t$ 的 $\psi_t(X)-\Omega_t$, 输入多走 $\delta$, 返回差.

| 输入 | 规格 (全部定义性相等, 见 `row-*`) | 旧规则 |
|---|---|---|
| `n0` | 差是空 | |
| `x ⨾ y` | 先 `x`, 状态前进, 再 `y` | `add` 消失 |
| `nl d` | 逐段, 状态前进 | $\psi(\lim)=\lim\psi$ 消失 |
| `ni r u`, 比较得 $k\ll t$ | 节点保留, 每个坐标上走 `u` | 保留 |
| `ni r u`, 比较得 $t\lhd k$ | $t$ 层没有这个节点 (类型如此). 取 $\omega$ 段: 坐标 $w_0=0$, 下一段 $\delta_0=Y_k$, $\delta_{n+1}$ 是上一段在 $k$ 的差 | `injᵇ` 的链, 起点 $\Omega_k$ 不再单写 |
| `n1` | `S` ($\Omega_t+Y_t$) | **这一行留下** |

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `sum-fst`, `Lg-sum`, `Lg-Ψ` | TLRuleSum | 回灌无前提, 对一切 `S` | 定理 |
| `Ψ`, `cell`, `Top`, `fgh` | TLRuleSum | 闭项, 没有证书参数 | 定义 |
| `main-Rel`, `Co-Ψ` | TLRuleMain | 同一个层上, 和形式的折叠与 `CumReadCF` 的折叠结构对应, 只差极限开头的项 | 定理 |
| `RS` | TLRuleSim | 对应对被积函数参数化, 一步, 不分阶段 | 定理 |
| `T≈`, `TΣ≈` (不在本文件的导入里, 单独编译) | TLRuleAccept | `fr (ord Top) ≈ᵛ BTBOᴵ`, `fr (ord TopΣ) ≈ᵛ BTBOᴵ` | 定理, 序数值验收 |
| `TopΣ`, `Lg-TopΣ`, `v⊲`, `next` | TLRuleDiag | 对角线也是和, 相邻项字面第一位置, 下一站的闭项 `next` | 定理; `next` 的强度是判断 |
| `CI′`, `coΣ` | TLRuleDiagRel | 状态从世界 $u$ 延到 $v$ 仍对上旧折叠 | 定理 |
| `T≇`, `fgh₀`, `fghB₀` | TLRuleAccept | 不 $\cong$, FGH 在 0 处不同 | 定理 |
| `ω-spec`, `ω-uniq` | TLRuleSpec | $c\cdot\omega$ 是 $c$ 之上最小的加法封闭点 | 定理 |
| `step-ω`, `sum⊞` | TLRuleSpec | 和的一步的值就是 $b+c\cdot\omega$, `⨾` 的值就是加法 | 定理 |
| `no-full` | TLRuleSpec | 不存在对全部分支严格单调且有上界的折叠 | 定理 |
| `chain-least`, `chain-closed` | TLRuleSpec | 链的上确界是对 $g$ 封闭的最小点 | 定理 |
| `gap-Ω₁`, `blind` (不在本文件的导入里, 单独编译) | TLRuleVar | $S=+1$ 与 $S=\cdot\omega$ 在 $\Omega_1$ 上值不同 | 定理 |

## 这几行规则

| 规则 | 结论 | 依据 | 档 |
|---|---|---|---|
| `add` | **写法.** 去掉, 构造子代替, 站的值不变 | `T≈`; `sum⊞` 说 `⨾` 的值就是加法 | 定理 |
| `rep`, 第 0 项是 0 | **写法.** 去掉, 基本列变了 | `T≈`, `T≇` | 定理 |
| $\psi(\lim)=\lim\psi$ | **写法上消失**, 只是 "和的作用" 在 `nl` 上的样子. 没有试过别的 `nl` 行 | `row-nl`; `T≈` | 定理 (同值); 唯一性没有陈述 |
| 穿过时取可数个分支 | **值逼的** (对任何有上界的折叠) | `no-full` | 定理 |
| 取的是链 | **值逼的, 在 "对 $g$ 封闭的最小点" 这条原则下** | `chain-least`, `chain-closed`; `IsFix` 的 `fix-least` 同类 | 定理, 相对原则 |
| 链的起点 $\Omega_k$ | **写法.** 不再单写, 是状态的第一段 | `T≈` 这一写法同值. 别的起点没有编译 | 定理 (这一个); 判断 (一般) |
| $\psi(0)=\Omega_\tau$ | **未决.** 初态 $Y=0$ 加上 `Step` 里的 $\Omega_t$. 没有编译别的起点 | 判断: 不小于 $\Omega_\tau$ 是落层要求, 取最小是约定 | 判断 |
| $\psi(a+1)=\psi(a)\cdot\omega$ | **选择, 但相对原则唯一.** 只有和的结构时值不定 (`blind`); 要求输出对加法封闭, 值唯一 (`ω-uniq`). 加法封闭这条是 Buchholz 闭包的约定, 不是树逼的 | `gap-Ω₁`, `ω-spec`, `step-ω` | 定理, 原则是判断 |

## 与已知规格的差

- `Rows` (`ValueJudgeRow`): 对已给的 $W$ 陈述, 后继行只有不等式, `rows-blind`. 这里的 `blind` 是同一个教训, 但定位到了一行: 只有 `S` 决定差别, 其余是和的结构. 另加原则 (`Clo`) 后那一行唯一.
- `IsFix`: 只说链行, 对 $F$ 相对. `chain-least` 是它在第 0 层的同形.
- `IsPsi` (`OCFSpec`): 闭包里带 $+$ 和全部 $\psi_u$, 判官, 不生成, 够不到 $\Omega_\Omega$. 这里 $+$ 是构造子, 生成闭项, 到 $\psi_0(\Omega_\Omega)$; 代价是 $\Omega_\Omega$ 以上还没有, 且 `T≈` 的验收要 `BTBOFull` 的现成映射.

## 条件定理

没有. `T≈` 无条件; `Uniform` 与 `BTBOFull` 只在验收文件里用, 定义不用.

## 有限测试

[TLRuleTest](TLRuleTest.lagda.md). 比较器: 慢增长 `G n` (沿第 $n$ 项走到底计后继数). 盲区: 只走一条路径, 只看小参数, 不能推序数值, 不能推 FGH.

## 判断 (纸面, 没有编译)

- $S=+1$ 时 $\psi_0(\Omega_\Omega)$ 约 $\zeta_0$, 远低于 $\psi_0(\Omega_\Omega)$: $\psi^+_k(\Omega_{k+1})=\Omega_k\cdot\omega$, 每层只多一个 $\omega$ 的幂, 累到 $\psi^+_0(\Omega_\omega)=\varepsilon_0$, $y\mapsto\psi^+_0(\Omega_{\omega(1+y)})=\varepsilon_y$. **`T⁺` 与 `T` 的差只在 $\Omega_1$ 上编译了, 在这一站没有定理.**
- $S=\cdot2$ 时在 $\psi_0(\Omega_\Omega)$ 上同值, 只在第 0 层慢一个 $\Omega$ ($\psi^{\cdot2}_0(\Omega_1)=\omega$, $\psi^{\cdot2}_0(\Omega_1\cdot2)=\varepsilon_0$), 第 1 层起 $\psi_1(\Omega_2)$ 就相同. 更强的 $S$ (下一个 $\varepsilon$) 也同值. **没有编译.** 所以 "值逼的" 大概不是 $\cdot\omega$ 这一个 $S$, 是 "至少翻倍" 这一类.
- `next` 读 $\psi_0(\Omega_{\psi_0(\Omega_\Omega)})$. 它只是 $\psi_0(\Omega_\Omega)$ 之下的层上的一步, **不是** 超过 $\psi_0(\Omega_\Omega)$ 的强度: $\psi_0(\Omega_\Omega)$ 就是这个映射的不动点.

## 第一个障碍

超过 $\psi_0(\Omega_\Omega)$ 要层 $\Omega_{\Omega+1}$, 也就是把回灌闭包写成和上的节点 (`TLOpsW` 的 `oc`). 这里没有试. 这不是否定, 是没走到.

定义时的报错只有停机一类, 换写法解决, 不是路线的障碍: `with` 把 `acc f` 拆掉后, 重组的 `acc f` 失去大小信息:

    Termination checking failed for the following functions:
      Fold.Run
    Problematic calls:
      Run W lW S (acc f) kp A₁ w (ni r u) Y τ | cmpN (≪∘ r kp) τ lW

解法: `RunNi`, `RunK` 把比较的结果作参数, 不用 `with`.

## 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `TLRuleSum` | `S = ω⋅` 抄自旧折叠; $\Omega_{c+1}=\Omega_c+\sum_{w:c}1$ 与坐标从 $\Omega_k$ 算起, 是对照旧树的链设计的 (为了 `Rel` 逐项对上); 没有读记号的基本列; 没有新增的证书, 比旧树少 `add`, `rep`, `up`, `oe`, `ψ⁰` 的 `os`, `ol` 两行 | 提供信息, 形状受旧树影响 |

**时间线.** 写规格前读过: `AGENTS.md`, `probes/README.md`, `RouteReview` §0 到 §6, `TLOps*`, `TLOne`, `TreeLangFeed`, `CumReadCF`, `Level`, `BTBOFullLe`, `Cumsum`, `OCFSpec`, `ValueJudgeRow`. 这些都带旧折叠的形状. 没有打开 `EBO`, `Correspond`, `Label`. 所以这不算 "树自足": $S$ 和坐标的取法是看旧树定的, 结论不依赖记号.

## 审计

`importclosure.py`: `TLRule`, `TLRuleSum`, `TLRuleRel`, `TLRuleSim`, `TLRuleMain`, `TLRuleDiag`, `TLRuleDiagRel`, `TLRuleSpec` 都 OK (干净). 正对照 `TLRuleAccept`, `TLOpsAccept` FAIL (都经 `Value`, `BTBOValNeg` 碰到禁用表); `TLRuleVar` 导入 `TLRuleAccept`, 同样不干净, 是验收文件. `depslice.py`, 到达块数 / 记号块 / 词命中: `TLRuleSum:Run` 51/0/0, `TLRuleSum:Top` 70/0/0, `TLRuleDiag:TopΣ` 81/0/0, `TLRuleDiag:next` 84/0/0, `TLRuleMain:main-Rel` 219/0/0, `TLRuleDiagRel:coΣ` 259/0/0, `TLRuleSpec:ω-uniq` 22/0/0, `TLRuleAccept:TΣ≈` 691/0/0 (验收读旧树, 没有读标签). 正对照 `TLOpsAccept:label-TΩ` 1019/92/58. 只保证不引用, 不说明没受旧树启发; 看时间线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRule where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; azero; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum public using (D; n0; n1; _⨾_; nl; ni; sum; sum-fst; Lg-sum; module Gen; module Fold; Ψ; Lg-Ψ; cell; Top; fgh; ω⋅; Ωd)
open import OCF.Align.TLRuleSpec public using (ω-spec; ω-uniq; step-ω; sum⊞; no-full; chain-least; chain-closed)
open import OCF.Align.TLRuleMain public using (main-Rel; Co-Ψ)
open import OCF.Align.TLRuleDiag public using (TopΣ; Lg-TopΣ; v⊲; next; Lg-next; fghΣ)
open import OCF.Align.TLRuleDiagRel public using (coΣ)
```

## 规格的行 (定义性相等)

对一切 $S$, 一切世界. 这些 `refl` 就是规格.

```agda
module Rows (W : A) (lW : Lg W) (S : ∀ {t} → D t → D t) where
  open Fold W lW S

  row-0 : ∀ {k} ac (kp : k ⊲ W) A₀ w (Y : St) {t} (τ : t ⊲ W) → Run ac kp A₀ w n0 Y τ ≡ n0
  row-0 ac kp A₀ w Y τ = refl

  row-1 : ∀ {k} ac (kp : k ⊲ W) A₀ w (Y : St) {t} (τ : t ⊲ W) → Run ac kp A₀ w n1 Y τ ≡ A₀ w Y τ
  row-1 ac kp A₀ w Y τ = refl

  row-⨾ : ∀ {k} ac (kp : k ⊲ W) A₀ w x y (Y : St) {t} (τ : t ⊲ W) →
          Run ac kp A₀ w (x ⨾ y) Y τ ≡ (Run ac kp A₀ w x Y τ ⨾ Run ac kp A₀ (w ⨾ x) y (Y ⊕ Run ac kp A₀ w x Y) τ)
  row-⨾ ac kp A₀ w x y Y τ = refl

  row-nl : ∀ {k} ac (kp : k ⊲ W) A₀ w d (Y : St) {t} (τ : t ⊲ W) →
           Run ac kp A₀ w (nl d) Y τ ≡ nl (λ n → Run ac kp A₀ (proj₁ (Rpt ac kp A₀ w d Y n)) (d n) (proj₂ (Rpt ac kp A₀ w d Y n)) τ)
  row-nl ac kp A₀ w d Y τ = refl

  row-S : ∀ (Y : St) {t} (τ : t ⊲ W) → Step Y τ ≡ S (Ωd t C.self (lg⊲ τ lW) ⨾ Y τ)
  row-S Y τ = refl
```
