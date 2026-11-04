# 不开 K: 消掉 `Un` (判决: HOLDS)

> 底座 [LevelNoKLv](LevelNoKLv.lagda.md) (语法, 比较, 求界接口), [LevelNoKTab](LevelNoKTab.lagda.md), [LevelNoKX](LevelNoKX.lagda.md), [LevelNoKBase](LevelNoKBase.lagda.md), [LevelNoKTree](LevelNoKTree.lagda.md) (折叠, 脚本改写自 `GuardTightLv`, `GuardTightTab`, `LevelFixBase`, `LevelFixTree`), [LevelNoKU](LevelNoKU.lagda.md) (定义域与证书), [LevelNoKFold](LevelNoKFold.lagda.md) (闭项). 块与合法性直接用 [LevelFixCore](LevelFixCore.lagda.md), [LevelFixVal](LevelFixVal.lagda.md), 没有改. 记号只在 [LevelNoKAccept](LevelNoKAccept.lagda.md).
>
> **判决: HOLDS, 只对这一轮的目标. `--safe --without-K --lossy-unification` 下, `Cf-toU : ∀ x → Legal x → Cfˢ (toU x)` 无条件, `x̂ : ∀ n → T⁰ 0` 与 `ψ₀Λ : T⁰ 0` 是无参数的闭项. `Un`, UIP, 函数外延都不出现, 既不是假设, 也不是模块参数. **这不是说树对了:** `chain-stuck`, 紧读法, `HS` 都没有解决, 正确性只有有限测试. `LF` 上的 UIP 也没有证明: 是不需要它了.**
>
> **`Un` 来自哪里 (编译事实).** 主审判断它来自编码, 现在有编译过的依据: 同一个 `LF`, `Raw`, `Gd`, `Legal`, 只换接口, 条件就没了. 回路来自四条索引关系连成的圈 (`c ⊑̂ x`, `c ⊑̂ y`, `x <̂ X`, `y <̂ X`, 报错原文在 [LevelNoKU](LevelNoKU.lagda.md)), 以及同一个 $\eta$ 上的两个证据. 下标之间的关系都改成同一个下界之上证据之间的关系之后, 每个值只有一个父亲, 合一只解变量.
>
> **新编码 (方向 1 与 2 的混合, 比这两个方向都小).** 下标仍是 `el k c`, 守卫 `⊑̂` 仍是索引数据类型, `LG` 与 `lc c t g` 的形状不变. 变的是:
>
> | 旧 ([LevelFixU](LevelFixU.lagda.md), `GuardTightLv`) | 新 |
> |---|---|
> | `≅ᴰ` 是 `Dom` 字段, 在 $\mathbb U$ 上是 `≡` | `c ≅ᴰ c′` 是 `Lv` 里的记录: 两个守卫纤维在 `D` 上同构, 保序 (`conv`, `conv⁻`, `ret`, `sec`, 保 `≤ᵉ`, `<ᵉ`) |
> | `o≈ d e h`, `h η e η′ e′ : η ≅ᴰ η′ → g η e ≈ g′ η′ e′` | `o≈ d e h h⁻ hˡ hʳ`, `h η e : g η e ≈ g′ η (conv d e)`. 同一个 $\eta$, 证据算出来, 不问 "任意两个证据" |
> | `dir : η ⊑ᴰ η′ → g η e ⊴ g η′ e′` | `dir : e ≤ᵉ e′ → g η e ⊴ g η′ e′`, `e`, `e′` 在同一个下界之上 |
> | `<ᴰ`, `bd` 在 `D` 上 | `e <ᵉ F`, `bd e₁ e₂ F`, 三个证据的下界是同一个 $c$ |
> | 表的值是 `D` | 表的值是 `Up`: 节点加纤维里的上界 `F : c ⊑ᴰ X` |
> | `CovB`: 帧与路径是同一个 $\eta$, 证据各管各的 | 帧的证据是路径证据的像 (`e₁ ≡ lkG k e`) |
> | 地板的项是 `D` 的元, `Ev ℓ φ` | 地板的项是帧; `Ev w φ` 经 `≈` 搬到表项 $w$ 的纤维里; 求界读 `Fᵉ F` (纤维里的证据树) |
>
> **比较怎么过 (`cmpBr`).** 路径的分支与目标的分支各自经 `≈` 搬到表项的纤维里 (`o₁`, `o₂`), 在同一个字面上界之下, `bd` 给可比, 再用 `o₁` 的逆拉回节点, `≈` 的 `h` 给回原来的分支值. **`o₁`, `o₂` 之间不需要相干性, 因为结论只说分支值 (`⊴`), 不说证据相等.** 这是这个编码能成立的关键.
>
> `Legal` 与它的闭包定理没有动: `LF` 仍是一次封闭, 没有外部编号, `Legal-Ω̂` 仍是一步.
>
> **编译过的定理.**
>
> | 东西 | 陈述 | 哪里 | 档 |
> |---|---|---|---|
> | `self-U` | `∀ x → Legal x → toU x ≈ toU x` | [U](LevelNoKU.lagda.md) | 定理, 无条件 |
> | `WF-U` | `∀ x → Legal x → WFˢ (toU x)` | [U](LevelNoKU.lagda.md) | 定理, 无条件 |
> | `Cf-toU` | `∀ x → Legal x → Cfˢ (toU x)` | [U](LevelNoKU.lagda.md) | 定理, 无条件 |
> | `irr-U` | 同一个 `a : Raw k` 上两个证据的分支 `≈` | [U](LevelNoKU.lagda.md) | 定理, 读 `Legal` 的 `irr` |
> | `cp⊴` | `b ≈ b → Cpᶠ a b → a ⊴ b` | [U](LevelNoKU.lagda.md) | 定理 |
> | `cmpBr` | 同一个表项上界之下的两个分支值 `⊴` 可比 | [Lv](LevelNoKLv.lagda.md) | 定理, 对任何 `Dom` |
> | `boundU`, `bd̃` | $\mathbb U$ 的求界, 比较 | [U](LevelNoKU.lagda.md) | 定义, 带证据 |
> | `Tψ` | `(x : LF) → Legal x → (n : ℕ) → T⁰ n` | [Fold](LevelNoKFold.lagda.md) | 定义 |
> | `x̂` | `∀ n → T⁰ 0` | [Fold](LevelNoKFold.lagda.md) | **无参数闭项** |
> | `ψ₀Λ`, `ψ₀ΩΛ` | `T⁰ 0` | [Fold](LevelNoKFold.lagda.md) | **无参数闭项** |
> | `ψ-ΩΩ`, `ψ₁θ`, `feed`, `Ωfeed` | 对合法的层号 | [Fold](LevelNoKFold.lagda.md) | 定义. `feed` 的输出的合法性没有定理, 所以 `Ωfeed` 的合法性也没有 |
> | `Legal-Ω̂`, `Legal-tw`, `Legal-Λ` | 原样 | [LevelFixVal](LevelFixVal.lagda.md) | 定理, 没有动 |
>
> **闭项不等于序数.** 树里的闭包是待计值的符号 (`oŝ`, `oĉ`), 与 [LevelFix](LevelFix.lagda.md) 相同. **没有给 `Family` 的项, 没有 `HS`.**
>
> **条件.** 目标里没有. 模块参数只有定义域 (`LevelNoKTab` 的 `𝔻`, `LevelNoKBase`, `LevelNoKTree` 的 `X`), 在 `LevelNoKFold` 里实例化成 `XF`. `Fold` 模块的参数是层号与证书, 由 `Tn` 给出.
>
> **有限测试 ([Accept](LevelNoKAccept.lagda.md), 全部 `refl`, 不是证明).**
>
> | 测试 | 比较器, 深度, 宽度 | 结果 |
> |---|---|---|
> | 新树对 `LevelFixTree` 的树: $x_0$, $x_1$, $x_2$ | `cmpᵒ` (种类, 下界与链的指纹, 第一支, 分支 $c+k$), 10, 3 | 一致, 比了 6, 254, 1209 个节点 |
> | 同上: $\Omega+1$; $\Omega\cdot2$; $\Omega\cdot2+1$; $\Omega\cdot3$ | `cmpᵒ`, 6, 3 | 一致, 130, 123, 129, 187 |
> | 同上: $\Omega_2$; $\Omega_3$; $\Omega_\omega$; $\Omega_\omega+1$ | `cmpᵒ`, 6, 3 | 一致, 129, 162, 102, 107 |
> | 同上: $\Omega_2\cdot2$; $\Omega_2\cdot2+1$ | `cmpᵒ`, 6, 3 | 一致, 330, 261. **太慢 (几小时), 只单独跑过一次, 不在文件里编译** |
> | 读回 $\psi_1,\psi_2(\Omega_{\Omega_2})$ | `fpL`, 6 | 一致 |
> | 对照 `ctl-d₁`, `ctl-d₂` | | 分得开; `ctl-d₂` 败在下界指纹 |
> | 对 EBO: `LevelFixAccept` 的 `a-*` 全部, 同样的深度 | `dfO`, `dfL`, 不看界 | 一致 |
> | 界对 `LadderNFTree`: `b-Ω`, `b-Ω+1`, `b-Ω+1₂`, `b-Ω2` | `misQ`, 10, 3 或 2 | **与 `LevelFixAccept` 逐字相同**: `b-Ω` 一致, 其余三条不一致 (3 对 2, 2 对 1, 2 对 1) |
> | 旧树没有的闭项, 对 EBO: $x_0,\dots,x_4$ | `dfO`, 12, 3, 不看界, 不走第 0 层闭包的分支, **很弱** | 一致; 对照 `ctl-x₃` 分得开 |
> | $\psi_0(\Lambda)$ 的前 4 项对 $\psi_0(\Omega\text{-塔}_n)$ | `dfΛ`, 8, 3, 同样弱 | 一致 |
> | 只数节点: $x_3$; $x_4$; $\Omega_{\Omega_{\omega+1}}$; $\psi_0(\Lambda)$ | `cnt`, 6, 3 | $(731,0)$, $(1069,204)$, $(589,3)$, $(207,0)$: (节点数, 名字不是自然数时读的分支数). **只说明算得动, 不说明值对** |
>
> 盲区: 分支只走字面的 $c+k$, 下界要 `lglS` 认得 (`zero`, `suc`, `top`, 后继层的 `em`). 指纹有界 (`fpL 4`). $x_3$ 以上没有看界的参照物.
>
> **判断 (未证).**
>
> - 新旧两棵树在一切 $\mathrm{UIP}$ 成立的名字上逐点一致. 有限测试支持, 没有定理.
> - `Dom₀` (`Ordᴵ`) 不是新接口的自然实例: 它的 `≅ᴵ` 是互模拟, 新的 `o≈` 要同一个 $\eta$. 旧文件不受影响; 这里没有实例化它.
> - 壁垒: `bd̃` 只比同一个字面上界之下, 同一个纤维里的证据, `cmpBr` 没有比两个任意分支, 比旧接口窄. `barrier` 的前提不成立的理由与 [LevelFix](LevelFix.lagda.md) 相同; 我没有证明这组定义永不触犯壁垒.
>
> **第一个障碍.** 这一轮的目标没有障碍. 过程中编译过的报错只有一条有实质内容: 上面的回路 (`SplitError.UnificationStuck`, `Cannot eliminate reflexive equation k = k of type LF because K has been disabled`), 新接口绕开了它. 正确性的障碍原样留着, 下一节.
>
> **对另外三件事的影响.**
>
> - **`chain-stuck`: 没有解决, 也没有变难 (判断).** 守卫 `Gd` 没有动, 同一个窄守卫, 链点读成分支要 `Gd`, 没有定理. 带链的闭包仍是符号 (`oĉ`). [LevelFixNeg](LevelFixNeg.lagda.md) 的 `no-Lgl-Ωlim`, `no-cp-Ω3-Ω2` 只读块与 `Legal`, 仍然适用; `no-tn-ω⁺` 的同一个点没有绕开 (`ix` 仍给 0).
> - **紧读法: 没有写, 接口保留.** `Rdr`, `rdB` 还在, `⊲` 改成同一个下界之上两个证据的关系. `⊲-conv`, `⊲-lk` 是编译过的搬运, `belDown`, `domOf`, `fsLow` 都读它. 实例只有 `rdId`, 界的不一致与旧树逐字相同. 判断: 紧读法的 `a ⊲ η` 在 $\mathbb U$ 上本来就是同层的第一位置, 写到纤维里不增加难度, 没有试.
> - **`HS`: 没有, 这里不碰.** 好处: 证书不再带 `Un`. 代价 (判断): 以后的证明不能陈述 "两个 `Elt` 下标之间的关系后再读分支", 必须写成同一个下界之上的证据关系, 否则在 $\mathbb U$ 上会重新碰到回路. 证据无关还在 (`irr-U`), 但只对同一个 `a : Raw k`.
>
> **是否还有外部编号或逐阶段新类型.** 类型: 没有. `natF`, `ix`, `nodeC` 里的 $\mathbb N$ 是目标的编号, 来源同 `no-tn-ω⁺`, 不是定义域的编号. `uip-nat` 这种逐类的证明这里不需要了.
>
> **受记号影响的形状.** 全部继承, 这一轮没有新增: 第一支与下界取 $\Omega_k$ (`cO`), 带链的闭包与 `ix`. 这一轮的新形状 (`≅ᴰ`, `≤ᵉ`, `<ᵉ`, `Up`, `Fᵉ`, 帧作地板) 都是 `--without-K` 下模式匹配逼出的, 不来自记号. 不算树自足: `cO` 的选取没有树侧判据.
>
> **审计.** 见文件末.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelNoK where

open import OCF.Align.LevelFixCore using (LF; Raw; Gd; Lgl; Cp; cmpC)
open import OCF.Align.LevelFixVal using (up; Ω̂; tw; Λ; Legal; CP; Legal-Ω̂; Ω̂-CP; Legal-tw; Legal-Λ; Legal-ΩΛ; Legal-Ωω; Legal-ΩΩ₂; Legal-ΩΩ; Legal-add; branch)
open import OCF.Align.LevelNoKLv using (Dom; module Lv)
open import OCF.Align.LevelNoKX using (XU)
open import OCF.Align.LevelNoKU using (Elt; el; _⊑̂_; gd; _≤̂_; _<̂_; bd̃; boundU; 𝕌; XF; toU; fromU; self-U; WF-U; Cf-toU; cp⊴; irr-U)
open import OCF.Align.LevelNoKFold using (Tψ; feed; Ωfeed; x̂; ψ₀Λ; ψ₀ΩΛ; ψ-ΩΩ; ψ₁θ; Tψ-Ωn; Tψ-Ωω)
```

## 审计

`importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.GuardTight --only OCF.Align.DomFold --only OCF.Align.LevelFix --only OCF.Align.LevelNoK OCF.Align.LevelNoK`: 干净 (禁用表命中 0, `--only` 之外 0). 闭包比 `LevelFix` 窄: 里面的本仓库模块只有 `OCF.BTBO`, `OCF.Free.Level`, `LevelFixCore`, `LevelFixVal` 与 `LevelNoK*`. `LevelNoKAccept` 按预期不干净 (FAIL, 经 `Uniform3Base`).

`depslice.py` (语法级, 看不见隐式参数):

| 根 | 到达块数 | 记号模块块数 | 别处的记号词 |
|---|---|---|---|
| `LevelNoKFold:ψ₀Λ` | 340 | 0 | 0 |
| `LevelNoKFold:x̂` | 337 | 0 | 0 |
| `LevelNoKFold:Tψ` | 318 | 0 | 0 |
| `LevelNoKU:Cf-toU` | 119 | 0 | 0 |
| `LevelNoKU:𝕌` | 109 | 0 | 0 |
| `LevelNoKLv:cmpBr` | 50 | 0 | 0 |
| `LevelFixVal:Legal-Ω̂` | 38 | 0 | 0 |
| 正对照 `LevelNoKAccept:a-Ωω` | 410 | 48 | 5 |

全文 `--safe --without-K --lossy-unification`, 没有 `--cubical`, 没有 K. 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`. 定义文件的代码里没有 `Un`, `UIPk`, 函数外延. 只有 `LevelNoKAccept` 导入 `LevelFixU`, `LevelFixFold`, 作新旧对照. 这些只保证不引用记号, 不说明定义没有受记号启发.
