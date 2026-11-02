# 奇异下标的定时检验: `Lv` 上总判决方向的裁决

> 底座 [InaccSingularBase](InaccSingularBase.lagda.md) 与 [InaccSingularSharp](InaccSingularSharp.lagda.md) 不含记号, 导入链里没有 `OCF.Align.EBO`. [InaccSingularGrade](InaccSingularGrade.lagda.md), [InaccSingularRead](InaccSingularRead.lagda.md), [InaccSingularAccept](InaccSingularAccept.lagda.md) 与本文件是**验收节**.
>
> **裁决: CLOSE `Lv` 上的总判决方向. 既没有构造, 也没有反驳; 这是按定时规则作出的建议, 不是定理.** 判决本身的否定 (`⟹ WLPO`) 对标准形类不指望得到, 理由见下. 决定性检验 (`GV` 在含 Ω_Ω 的类上, 标签越过 `ψ₀(Ω_Ω)`) **没有通过**: 树侧判决 `D♯` 只解决了 Ω₁ 这一个目标, 而 `GV` 的证明另有一堵墙 (`no-grade-top`).
>
> **已编译的事实 (无条件或只以 `Funext` 为参数).**
>
> 1. **规格 (`Right`, `right→dec`, `Nd-limᴼ`).** 正确的判决就是字面前驱关系 `Nd` 的带见证判定. `limᴼ k g` 目标上恰有三种情形: `j` 是 `k`, 在 `k` 之下, 或在某个字面的 `g x` 之下.
> 2. **`allReg→WLPO`: 对全部 `Reg` 树满足 `Right` 的判决推出 WLPO.** 族 `σ s` 每棵都规整, 与 ω 字面相等当且仅当 `s` 全假. 这把 `dec→WLPO` 推到规整树上, 也把 InaccModulus 的 `Reg-ω`, `Reg-ω⁺` 变成定理: 规整性不够, 必须有向.
> 3. **`Dᵐ-right`, `dir-dec`: 在公共规整上界之内 `Dᵐ` 满足 `Right`, 所以 `Nd` 可判定.** 第 2 点的禁忌完全来自非有向; 有向规整族上这类否定不可能, `Dᵐ` 自身是反例.
> 4. **`D♯` (`Sharp`).** 比 `Dᵐ` 多一条子句: 目标 `limᴼ 0 g`, `j` 的 1-走步无 `limᴼ` 时进分支 `1 + toT₀ j`. 对任意 `Fam F`: `toT₀-inv` (`toT₀` 是 `toLv` 的字面逆), `pen♯` (族内节点对 Ω₁ 是字面的 `pen`), `rise-self`, `rise-O`, 而族内 `lt♯`, `gt♯`, `eq♯` 与 `Dᵐ` 相同. 这是树上的定理, 但只有目标 Ω₁.
> 5. **`no-grade`, `no-grade-2`, `no-grade-top` (`Grade`).** 按下标深度的 ℕ-分层 (`Strata` 的形状) 不能含 `ψ₀(Ω_Ω)`, `ψ₀(Ω_Ω+Ω₁)`, `ψ₀(Ω_Ω·2)`. 前一项是后一项的基本列的下标后代. 所以越过 `ψ₀(Ω_Ω)` 时 `GV` 不能再对深度递归, **与判决对错无关**.
> 6. **`rise-forgets`.** 走 `rise` 的折叠只在轨道上用参数函数, 对任意判决成立. `rise` 节点从树上不可逆.
> 7. **读数的三类 (`Read`).** `sub-*`: `Ω_ω` 对 `Ω_Ω` 要读下标. `rel-*`: `Ω_Ω+Ω_ω` 对 `Ω_Ω·2` 要读相对目标的尾项, 所以 `x` 依赖目标. `hid-*`: `ψ₁(Ω_Ω+Ω₂)` 对 `ψ₁(Ω_Ω·2)` 要 `x ≥ 3`, 而 `Ω₂` 不在它的基本列的尾项里 (`hid-fs0`, `hid-fs1`), 要反演 `rise`. `hid′-nat`: 换成下标 ω 则没有自然数够大.
>
> **任务单上的四个点 (`Accept`, 有限检验).** 一个 "对", 三个错.
>
> | 点 | `D♯` | 说明 |
> | --- | --- | --- |
> | `Ω_Ω` 对自身 | 对 (`self-OO`) | 没有内容: `limᴼ` 节点一律 `rise` |
> | `Ω_ω` 对 `Ω_Ω` | 错 (`wrong-Ωω`) | 要读下标 |
> | `Ω_Ω+1` 对 `Ω_Ω·2` | 错 (`wrong-OO+1`) | 要读相对尾项 |
> | `Ω_Ω` 对 `Ω_{Ω₂}` | 错 (`wrong-Ω₂`) | 目标 `k ≠ 0` |
> | 2 对 `Ω_Ω`, 2 对 `Ω_Ω·2` | 错 (`count-1`, `count-2`) | `g x` 的 `k ≠ 0` |
>
> 目标为 Ω₁ 的 `ok-1` 到 `ok-5` 通过. `ψ₀(Ω₁)` 对 Ω₁ 的同样检验没有算完, 无结果; 定理 `pen♯` 对任意 `Fam` 族成立 (`famReg` 是实例), 但 `L♯` 在含 Ω_Ω 的项类上的像是不是 `Fam`, 这里没有证明. 含 Ω_Ω 的项的 `diff` 没有运行.
>
> **第一个具体障碍, 有两个, 彼此独立.**
>
> - **判决侧.** 目标 `limᴼ k g` 的分支 `x` 要反读 `j` 的项结构: 下标, 相对尾项, 被折叠的参数. 第三类要反演 `rise`. 树上没有规则说明怎么做; 每多读一类就是多反编译一层记号. `D★`, `D⁺` 的修补链就是这件事的症状. 比 Ω₁ 高一步的目标 `Ω₁·2` (节点 `Ω₁+c`) 就已经要读相对尾项 (这一点是手算, 未编译).
> - **证明侧.** 即使判决正确, `Commute` 要的 `GV` 在 `ψ₀(Ω_Ω·2)` 的下标类上不能分层 (`no-grade-top`), 必须对项序作良基归纳, 而记号侧的良基性未做. `Standard` 的 `NF` 又要求 `Ctbl u`, 不含奇异叶; 把 `cofin` 扩到 Ω₁ 下标是 1100 行量级的重做. 所以 `D♯` 也**没有**产生 `ψ₀(Ω_Ω·2)` 或 (Ω_Ω)² 的标签.
>
> **任务 1 的回答.** 没有编译 "奇异下标上正确的判决 ⟹ WLPO", 我也不认为它成立, 下面是判断, 不是定理. 把 `dec→WLPO` 用到一个类上, 需要类内有非孤立点: `j_α` 在 `α` 全假时等于 `j`, 在首个真值处等于别的 `j_n`, 而判决对它们不同. 第 2 点的 `σ` 是这种点, 但不有向; 第 3 点说有向规整族里没有. 在 `limᴼ` 节点上, 用分支 `x` 的有限信息 (例如 `wk x`) 无法隔开大的 `x`: `wk x` 小的 `x` 无界, 所以单调的 `g` 无法只在 "`wk` 大" 处偏离. 标准形的项是可枚举的离散类, 经典元理论下正确的判决看来存在 (未形式化, 要处理 `L` 对判决的循环依赖). 若如此, 否定只能是 "没有**树侧规则**", 而这不是能在内部陈述的命题. 内部能说的就是上面的第 1, 2, 3, 6 点.
>
> **任务 2 的回答.** 构造只到 Ω₁ (第 4 点), 没有 `RegΩ`, 没有一个覆盖任务单四点的定理. `⁺-wrong-OO` 这一点 `cntb` 修掉了 (`self-OO`), 代价是 `wrong-Ωω`. 这又是一次把错误推后, 所以不再继续修补.
>
> **修正 InaccModulus 的一个观察.** 那里说 `⁺-wrong-OO` 的来源是 "`x` 不在族里". `Fam` 的前提确实失效, 但分支读数本身不是字面障碍: 下标读数是填充树时, 字面节点仍可能存在 (`pad-ok`: 层号 `lim [1,2,…]` 上有一棵树, 其 `toLv` 字面就是 `Ω_ω`). 真正错的是采样相等把别的 `limᴼ` 节点当成了 `j`.
>
> **任务 3 (`bach`): 没有证明, 只分析.** 规则 4 要 "末项沿 1-走步消到 0", 须对树或项序递归; 规则 6 要 `ψ_u(b[γ(n+1)])` 走到 `ψ_u(b[γ n])`, 这是一条广义 Bachmann 引理, `lin` 帮不上. 不便宜, 按定时规则放弃. 仍只有 InaccModulus 的采样.
>
> **任务 4 (去 `Funext`): 跳过.** `≡` 进入 `stepT`, `cast-id`, `Nd₂`, `toLv-strip` 全部结论, 换成逐点关系要重写 `Commute` 与 `Lift₂` (500 行以上). 是大改写, 不是清理.
>
> **保留什么 (判断).**
>
> - `Reg`, `wk`, `lin`, `mod`, `Dᵐ`, `famReg`, `tri`, `dir-dec`: 可数段上的完整理论, 其结论是 "有向规整族内 `Nd` 可判定".
> - `Right`, `allReg→WLPO`: 判决规格与有向性的必要性.
> - `no-grade`: 独立于 `Lv`. 它对任何沿用 "下标按深度递归" 的证明都是警告.
>
> **对其他路线的迁移 (判断).**
>
> - **Uniform3 的标签路线.** `no-grade-top` 说的是 `Commute` 的证明结构不能分层; Uniform3 有地板与 `Goodᴸ`, 不走这里的 `GV`, 我没有核对它是否隐含同样的分层, 所以只作提示. `dir-dec` 也提示: 地板的作用可以理解为提供公共上界 (InaccStrike 已有此判断), 这里给出了可数段上的定理形式.
> - **记号无关的闭包定理.** `allReg→WLPO` 说树侧的逐棵谓词不够, 类必须带有向性. 这对 UniformPending 的类如何陈述是直接约束. `rise-forgets` 说闭包不能指望从树反读参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccSingular where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import OCF.Align.InaccTreeBase hiding (eq)
open import OCF.Align.InaccStrikeOracle using (natL)
open import OCF.Align.InaccModulusBase using (Nd)
open import OCF.Align.InaccSingularBase using (ωL)
open import OCF.Align.InaccSingularBase using
  (Right; right→dec; Nd-limᴼ; σ; Reg-σ; allReg→WLPO; module Dir)
open import OCF.Align.InaccSingularSharp using (D♯; Dm♯; cntb; toT₀; module OnFam♯; module Forget)
open import OCF.Align.InaccSingularGrade using (Grade; module No)
open import OCF.Align.InaccSingularRead using (sub-nat; rel-nat; hid-need; hid′-nat)

-- 填充的层号 `lim [1,2,…]` 上仍有字面的 `Ω_ω`
ω⁺ : Lv
ω⁺ = lim (λ n → natL (suc n))

yω : Ordᴸ ω⁺
yω = lim (λ n → up n (up tt (Ω (natL n))))

pad-ok : Nd (toLv (Ω ωL)) (limᴼ ω⁺ toLv)
pad-ok = inj₂ (suc yω , inj₁ tt) , refl
```
