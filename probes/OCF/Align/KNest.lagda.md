# 嵌套 `nκ` 的值语义: 入口

> **判决: PARTIAL.** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`. 接 [KVal](KVal.lagda.md) 与 [KValK](KValK.lagda.md) (那里的文件一个没改).
>
> 1. **`KVal` 判决 5 的机制不是障碍 (定理).** [KNestInv](KNestInv.lagda.md): 回灌层 $\ell=W+z$ 等于 "基点 + 状态在第 0 层的累计差" (`InvU`, `InvL`), 这被任何一步 $\oplus$ 定义性地保持, 被回灌格的换世界保持, 对一切输入族 (含嵌套) 的每一格成立 (`inv-κc`). 所以 `Hℓ` 由状态值推出 (`hℓ-inv`), 上下文不必记格世界 (`Cxᴵ`, `toCx`). 左 $1,2,4,8$ / 右 $1,3,7,15$ 那种格世界错位, 不影响同一层上回灌层的比较: 回灌层只看已有输出.
> 2. **真正的障碍是内层的区间起点 (定理, 否定).** [KNestNeg](KNestNeg.lagda.md): 嵌套族 $u_\kappa(c)=\mathrm{n}\kappa(\lambda d.1)$ 对层**反**单调. 同一世界, 同一状态, $\ell=\ell'$, 上下文 `Cx` 的四条与 `Cxᴵ` 都成立, 而 $u_\kappa(1)$ 的输出 $\ge1$, $u_\kappa(2)$ 的输出 $=0$ (`anti`). 所以 (`¬KMonoˢ`, `¬crit`) 任何对 `OutLe m` 可靠的关系都不能以 "$c\le c'$ ⇒ $u(c)\sqsubseteq u(c')$" 为 `nκ` 的分支前提而覆盖这个族; `KValTree.κ⊑` 的三条分支前提都是这个形状, 直接放开嵌套推不出外层 $\mathrm{n}\kappa\,u_\kappa$ 的自比. 只有 $\ell\le\ell'$ 不够: 右边内层的树世界高时, 要右边的回灌层**领先**左边区间的长度.
> 3. **判据的形状: 领先量 (定理).** [KNestAdm](KNestAdm.lagda.md): $\mathrm{Adm}(\alpha,\alpha';\ell,\ell')=\exists\delta.\ \ell\le\alpha\oplus\delta\wedge\alpha'\oplus\delta\le\ell'$. 排除反例 (`¬adm-cex`), 包含单层的包含式 (`adm-cont`), 被推进保持 (`adm-adv`), 可复合 (`adm-tr`). 两条否定: 只降左边的下标不保持 (`lower-left`; 所以下标不能取树的世界, 否则 `nwˡ` 不可靠, 这是 `DVal` §3 判断的编译形式); 尾对齐的典型一对不满足 (`¬adm-end`).
> 4. **任意深度归结为一步 (条件定理).** [KNestSound](KNestSound.lagda.md): 关系 `x ⊑⟨ α , α′ ⟩ x′`, 下标单独记 (`nw` 透明), `κᴬ` 的分支在**同一个关系**里比, 下标取那一对层. 只要单个 `nκ` 的一步 `KStepᴬ` (分支前提是语义的, 类型见下) 成立, 关系对一切深度可靠 (`sndᴬ`, 一次结构归纳). 嵌套族 $\mathrm{nest}_k$ 对一切 $k$ 都在关系里 (`nest-rel`, 无条件); 推论 `nest-mono`. 包含式的入口 `contain` 把结论落回不带下标的单调.
> 5. **`KStepᴬ` 没有证: 未走通 (未完成, 不是否定).** 第一个障碍见 §3: `KValK` 的单层证明把前 $n$ 格换成一个世界里走一次 `Pre n`, 再用尾对齐的 `CutM`; 嵌套时这两步都不保值 (判断; 后者的数值形状是 `¬adm-end`), 要逐格的**首对齐**.

## 1 定义

    InvU b Y = ℓ Y ≤ b + δ(Y)        InvL b Y = b + δ(Y) ≤ ℓ Y          ℓ Y = W + z(Y)
    Cxᴵ s s′ Y Y′ = (b ≤ b′, InvU b Y, InvL b′ Y′, 路径一致两条, 状态值 ≤)
    Adm α α′ ℓ ℓ′ = Σ δ. ℓ ≤ α ⊞ δ × α′ ⊞ δ ≤ ℓ′
    Cxᴬ α α′ = Cxᴵ × Adm α α′ ℓ ℓ′

    data _⊑⟨_,_⟩_ : n0ᴬ n1ᴬ ⨾ᴬ nlᴬ nwˡᴬ nwʳᴬ (下标不动)
                    loᴬ : x ⊑[ lo ] x′ → x ⊑⟨ α , α′ ⟩ x′
                    κᴬ  : Adm V V′ α α′ → (分支三条, 层 c ≤ c′ 的一对在 ⊑⟨ c , c′ ⟩ 里) → nκ u ⊑⟨ α , α′ ⟩ nκ u′

    OutLeᴬ α α′ x x′ = ∀ s s′ → Ok s s′ → ∀ q q′ w w′ Y Y′ → Cxᴬ α α′ s s′ Y Y′ → ∀ c ≤ c′ → Ob s c x q w Y ≤ Ob s′ c′ x′ q′ w′ Y′

    SX u u′ = ∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) l l′ → c ≤ c′ → OutLeᴬ c c′ (u p l) (u′ p′ l′)
    KStepᴬ  = ∀ {α α′ V V′ zz zz′} {u : Bk V} {u′ : Bk V′} → Adm V V′ α α′ → SX u u → SX u′ u′ → SX u u′ →
              OutLeᴬ α α′ (nκ zz u) (nκ zz′ u′)

`KStepᴬ` 只要语义的分支前提, 所以它与关系无关; 它的单层特例 (分支在 `lo` 档) 是 `KValKHi.kh` 管的事, 但 `kh` 的上下文是 `Cx hi` 不带下标, 两者不互推 (判断).

## 2 定理

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `anti`, `¬mono` | KNestNeg | $u_\kappa(1)$ 对 $u_\kappa(2)$: 同上下文, 输出 $\ge1$ 对 $0$ | 定理 (否定) |
| **`¬KMonoˢ`, `¬crit`** | KNestNeg | 嵌套族对层单调是假的; 可靠的关系不能有这种前提 | 定理 (否定; 前提由 `ok₂`, `cx₂` 满足) |
| `invU⊕`, `invL⊕`, `invU-cv`, `invL-cv`, `inv-top`, `inv-cex` | KNestInv | 不变量被 $\oplus$ 与回灌换世界保持; 起点与反例满足 | 定理 |
| `cohW` | KNestInv | `Walk` 的输出路径一致, 对一切族 (不要 `KMono`) | 条件定理 (动作 `CohA`, 状态一致) |
| **`inv-κc`** | KNestInv | 回灌每一格满足不变量, 格世界就是它的回灌层 | 条件定理 (同上) |
| **`hℓ-inv`**, `toCx`, `nextᴵ` | KNestInv | `Hℓ` 由值推出; `Cxᴵ` 推出 `Cx hi`, 随 $\oplus$ 推进 | 定理 |
| `adm-tr`, `adm-adv`, `split`, `adm-cont`, `adm→hℓ` | KNestAdm | 领先量的代数 | 定理 |
| **`¬adm-cex`**, `lower-left`, `¬adm-end` | KNestAdm | 排除反例; 只降左下标不保持; 尾对齐的一对不满足 | 定理 (否定) |
| `nextᴬ`, `adv-sum` | KNestSound | `Cxᴬ` 随一步推进 | 条件定理 (动作 `Ok`) |
| **`sndᴬ`** | KNestSound | 带下标的关系对一切深度可靠 | 条件定理 (参数 `KStepᴬ`, 动作 `Ok`) |
| **`nest-diag`, `nest-rel`** | KNestSound | 任意深度的嵌套族在关系里 | 定理 |
| `nest-mono`, `contain` | KNestSound | 推论; 包含式入口 | 条件定理 (`KStepᴬ`) |

**否定的范围.** `¬crit` 只否定 "嵌套 `nκ` 的分支前提要求对层单调 (同上下文, $c\le c'$)" 这一类判据用在 $u_\kappa$ 上; 不否定外层 $\mathrm{n}\kappa\,u_\kappa$ 的折叠单调 (判断: 单调), 不否定带下标的判据. `lower-left` 只否定 "下标 = 树世界" 时 `nwˡ` 的可靠性 (在 Adm 语义下). `¬adm-end` 是数值的否定, 它与 `CutM` 的对应是判断.

**有限测试.** 无. `big` 是对具体项的归约 (`refl`), 算定理.

## 3 第一个障碍: `KStepᴬ` 要逐格的首对齐

`KValK` 的单层证明 (判断, 依据见该入口 §1): 前 $n$ 格 ≈ 在一个世界里走 `Pre n` ≈ `Cut u [V, a_n)`, 再用 `CutM`. 两步在嵌套时都不保值:

- **一个世界.** 分支在 `lo` 档时与世界无关 (`snd-lo` 跨世界). 嵌套分支的值经回灌层依赖世界: 格里层 $c$ 处 $\ell=b+\Lambda(c)$ (`inv-κc`), 一个世界 $v_n$ 里走时 $\ell=v_n+(\Lambda(c)-\Lambda_0)$, 一般更大. 在更高的世界里走只给左边的上界 (`InvL` 被抬升保持, `InvU` 不被), 不给右边的下界.
- **尾对齐.** `CutM` 在极限处把左边每个前缀的末层对到右边的末层. 嵌套时那一对的下标要满足 Adm, 典型的一对是 $[0,\omega)$ 的层对 $[0,\omega+1)$ 的层 $\omega$, 正是 `¬adm-end` 否定的形状.

可行的形状 (判断, 没有编译): 第 $n\ge1$ 格走的是 `sum-fst` 沿上一格输出 $d_0$ 的路径, 所以格里的层是 "格起点 + $d_0$ 的前缀". 左右按 $d_0$ 与 $d_0'$ 的结构对齐 (首对齐), 左层 $v_{n-1}\oplus\varepsilon$ 对右层 $v'_{n-1}\oplus\varepsilon$, 领先量 $\delta=(\mathrm{out}_{n-1}-\varepsilon)+z$ 两边可比, 所以 Adm 在每一对上成立. 这把一格的比较变成 "沿第 0 层坐标树走", 形状同 `KValZero.cong0`/`chain` (`ni` 的链). 第 0 格走 $[V,\ell)$, 右边起点高时同样首对齐, 低时用恒等对齐. 要写的: `Walk` 沿 `sum-fst b x` ≈ 以 $x$ 为坐标的走法 (桥), 再把 `cong0` 的论证搬到带下标的上下文. 估计 600–900 行 (判断).

## 4 翻译账

| 模块 | 记号读来的字段或形状 | 类 |
|---|---|---|
| `KNestNeg` | 无. 反例形状读自 `RKy` 的回灌 (第 0 格走 $[W_0,W+z)$) 与 `L1ValBase.κ-stall` | 提供信息 (否定定理划出不能有的判据) |
| `KNestInv` | 无. 不变量由 `cv` 与 `⊕` 的定义逼出 (新世界 = 旧的 $W+z$); 新用到的字段: `St.z` 与 `d` 在路径 `z⊲ W` 上的读数相差一个基点 | 提供信息 |
| `KNestAdm` | 无. 领先量由 `anti` 逼出 (反例里只缺它), 下标与树世界分开由 `lower-left` 逼出 | 提供信息 |
| `KNestSound` | 无新构造子, 无新折叠规则. 下标由 `lower-left` 逼出, 分支下标取那一对层由 `anti` 逼出; `loᴬ` 沿用 `KValTree` 的 `lo` 档 | 提供信息 |

没有用 `Lab`, 没有读自记号基本列的字段, 闭包定理 (`sndᴬ`) 对一切深度一个证明, 没有按深度的专属前提. 一步定理与新用到的字段: `inv-κc` 的后继步用格的 `Walk` 输出在 `z⊲ v` 上的读数 $d_0$ 同时进 $z$ 与 $d$; `sndᴬ` 的 `κᴬ` 一步只用分支推导本身 (递归); `nextᴬ` 用一步输出在 `z⊲ W` 与 `κ₀ ll` 两条路径上值相同. 加深翻译的标志都没有.

## 5 审计

- `importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRule --only OCF.Align.TLOpsW --only OCF.Align.SumOne --only OCF.Align.BrwMid --only OCF.Align.LayerTr --only OCF.Align.CvFold --only OCF.Align.CvHigh --only OCF.Align.CvLayer --only OCF.Align.NoCumLit --only OCF.Align.L1Val --only OCF.Align.DVal --only OCF.Align.HtGen --only OCF.Align.HtFeed --only OCF.Align.HtCross --only OCF.Align.KVal --only OCF.Align.KNest OCF.Align.KNest`: 闭包 37 个模块 (本地 27, 库 10), 禁用表命中 0, `--only` 之外 0, OK. 编译器保证的不引用; 不说明定义没有受记号启发.
- `depslice.py` (语法级近似): `KNestNeg:¬crit` 到达 174 块, `KNestInv:inv-κc` 179, `KNestInv:hℓ-inv` 81, `KNestAdm:¬adm-end` 18, `KNestSound:sndᴬ` 274, `KNestSound:nest-mono` 279, `KNestSound:contain` 173; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 到达 1188, 记号模块 92 块, 别处 58.
- agda 代码行 (非空, 代码块内): KNest 6, KNestNeg 69, KNestInv 116, KNestAdm 58, KNestSound 112, 合计 361.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KNest where

open import OCF.Align.KNestNeg using (uκ; anti; ¬mono; KMonoˢ; ¬KMonoˢ; ¬crit) public
open import OCF.Align.KNestInv using (InvU; InvL; invU⊕; invL⊕; invU-cv; invL-cv; inv-top; inv-cex; cohW; module Cells; hℓ-inv; Cxᴵ; toCx; nextᴵ) public
open import OCF.Align.KNestAdm using (Adm; adm-tr; adm-adv; adm-cont; adm→hℓ; ¬adm-cex; lower-left; ¬adm-end) public
open import OCF.Align.KNestSound using (_⊑⟨_,_⟩_; Cxᴬ; OutLeᴬ; SX; KStepᴬ; sndᴬ; nest; nest-diag; nest-rel; nest-mono; contain) public
```
