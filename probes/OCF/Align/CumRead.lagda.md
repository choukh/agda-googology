# 累加读回: 第一个障碍绕过去了, 带闭包的层上定义到了, 证书没有到 (判决: PARTIAL)

> 文件: [CumReadBase](CumReadBase.lagda.md) (累加, 否定, 吸收), [CumReadCF](CumReadCF.lagda.md) (没有闭包的折叠), [CumReadCFEq](CumReadCFEq.lagda.md) (同余), [CumReadCFThm](CumReadCFThm.lagda.md) (闭包定理), [CumReadTop](CumReadTop.lagda.md) ($\psi_0(\Omega_\Omega)$), [CumReadW](CumReadW.lagda.md) (带闭包的折叠), [CumReadWLv](CumReadWLv.lagda.md) (层的实例). 验收只在 [CumReadAccept](CumReadAccept.lagda.md), [CumReadAcceptW](CumReadAcceptW.lagda.md). 接 [NoKCert](NoKCert.lagda.md).
>
> **判决: PARTIAL.**
>
> - **`no-HS→Lgl` 这个障碍在 $\psi_0(\Omega_\Omega)$ 上绕过去了:** `HS-Tᶜ : HS Tᶜ`, 无条件, 无参数, 不经 `OCF.Free` 的 `Goodᴺ`, 也不经 `Vis`, `Hon`. 但这棵树是这一轮新写的折叠, **不是** `rdZ (x̂ᵗ 2)`. `LF` 上的 `x̂ᵗ` 这里没有给 `Goodᵁ`.
> - **闭包定理对没有闭包的层是一步的:** `ψL`, `ψW`, `HS-Y`, `Y-mono`, 对一切字面合法的可数 $\eta$, 与阶段无关. 这是第一次不问 "输出高于下标".
> - **带闭包的层: 只有定义.** `Tψ : ∀ L → Legal L → Ord₀` 是全函数, 所以 $\psi_0(\Omega_{\Omega+a})$, $\psi_0(\Omega_{\Omega\cdot\alpha})$, $\psi_0(\Omega_{\Omega^n})$ (判断) 有闭项和 FGH. **没有 `HS`, 没有闭包定理, 正确性只有浅的有限测试.**
> - **累加确实改值 (定理 `overshootᴬ`), 吸收只有条件定理 (`absorb`) 和 $\omega$ 上的实例 (`absorb-ω`).** 新树与带标签的树互相 `⊑⁰` 没有证, 这一档的值验收 **没有**. 见下面的讨论.
> - **没有到 $\Omega_2$, $x_3$, $\psi_0(\Lambda)$.** 这里的 `Lv` 只有 $\Omega_1$ 共尾的闭包.

## 编译过的定理

| 东西 | 陈述 | 文件 |
|---|---|---|
| `Lg-cum` | `∀ y → Lg (cumA y)` | Base |
| `next-⊲`, `Lg-next` | `η ⊲ next η y`; `Lg η → Lg (next η y)` | Base |
| `Legal-ordᴸ` | `∀ y → NoLc y → Legal (ordᴸ y)` | Base |
| `no-Legal-ordᴸ` | `Legal (ordᴸ (tw 2)) → ⊥`; `tw 2` 合法 (`Legal-tw2`) | Base |
| `no-cum-⊲` | `ωA ⊲ cumA b₀ → ⊥`; 树上 `ω₁ ◁ b₀` (`ω◁b₀`) | Base |
| `overshootᴬ` | $\omega\cdot3$ 在 `cumA ω·2` 之下, 字面路径 | Base |
| `dom-cum` | `∀ y → y ≼ toO (cumA y)` | Base |
| `absorb-ω` | $\omega$ 与 $\lceil\omega\rceil$ 互相 `≼` | Base |
| `no-⊞-left` | `⊞` 不保左边的第一位置 | Base |
| `ψQ` | `x ≈ y → ψ t T w x ≈ ψ t T′ w′ y` | CFEq |
| `ψL` | `x ⊴ y → ψ t T w x ⊴ ψ t T′ w′ y` | CFThm |
| `ψW` | `x ≈ x → WF x → WF (ψ t T w x)` | CFThm |
| `HS-Y` | `∀ η (w : Lg η) → HS (Y η w)` | CFThm |
| `Y-mono` | `a ⊲ b → Y a wa ⊑⁰ Y b wb` | CFThm |
| `HS-clo` | 分支对字面第一位置单调, 闭包的计值就是 `HS` | Top |
| `HS-Tᶜ` | `HS Tᶜ`, $\psi_0(\Omega_\Omega)$ (读法是判断) | Top |
| `Tψ`, `TΩ+`, `TΩ·`, `TP` | 闭项. **定义编译过, 不是证书** | W, WLv |
| `Legal-Ω`, `Legal-+`, `Legal-M`, `Legal-·Ω`, `Legal-P` | 层的合法性, 字面 | WLv |

**条件定理.** `absorb`: `Closed (lim f)` 且每项的读回在 $\lim f$ 之下, 则 $\lceil\lim f\rceil\preceq\lim f$. 前提 `Closed` 在 `Y` 的值上没有证.

## 目标 1: 读回

`cumA` 对第 0 层的树无条件字面合法. **`lc` 的分支过不去, 这是定理:** 累加不保第一位置 (`no-cum-⊲`), `Legal` 的 `dir` 要第一位置 (`no-Legal-ordᴸ`). 只否定逐点读分支这一个写法.

**绕法.** 链点不必读成合法的整棵树: 下一个下标是 $\eta+(\lceil y\rceil+1)$ (`next`), 第一位置由构造给出. 单调性不要 $y\sqsubseteq y'$, 要 $\eta\lhd\eta'$. 这样 `gŝ` 的 `dy`, `hy`, `lE` 都消失, 计值是全函数 (`Clo`). 这与 [CrossMNode](CrossMNode.lagda.md) 的累加链同形.

## 目标 2, 4: 闭包定理为什么这么短

`CumReadCFEq`, `CumReadCFThm` 合起来约 600 行, 带讲解. **这不能直接和 [OCF.Free](../Free/Main.lagda.md) 的 3416 行比:** 那里覆盖 $\Omega+\eta$, 这里只到可数层. 但没有闭包的这一段, 那里也要 `Vis`: 相邻的下标只有 `⊑ᴵ`, 所以要证输出高于下标才能比较. 这里相邻的下标字面第一位置, `ψ` 把第一位置映成第一位置 (节点的第一位置是 $h(\Omega_k)$), 对推导归纳就完了. **这是 Bachmann 型的单调, 它不问值.**

## 目标 3: `chain-stuck`

`Bd` 把链点排除的情形: 这里没有下界守卫, 第一个下标是 $c+(\lceil y_0\rceil+1)$, 第一位置由构造给出. [CumReadW](CumReadW.lagda.md) 的世界把这件事做到了一切闭包: `oc x g` 的分支在 $v\rhd u$ 上给出, 外层的下标都在 $v$ 之下, 两条走分支的路径字面可比 (`cmpN`). **定义层面消掉了帧, 表, 地板.** 证书层面没有兑现, 所以这只是定义上的解法.

## 累加到底改不改值

- **改.** `overshootᴬ`: $\lceil\omega\cdot2\rceil\succeq\omega\cdot3$ (字面路径), 判断值是 $\omega^2$.
- **在加法主数上不改, 条件定理** `absorb`, 实例 `absorb-ω`. 判断: 链的闭包点是 $\varepsilon$ 数, 不改.
- **链的上确界: 判断不变, 没有定理.** 新链 $y_{n+1}=\psi_0(\Omega_{\eta_n})$, 旧链 $y'_{n+1}=\psi_0(\Omega_{y'_n})$. 证明要 $\psi_0(\Omega_\cdot)$ 对值 `≼` 单调, 这条没有. **互相 `⊑⁰` 判断是假的:** `absorb-fails` 说 $b\sqsubseteq a+b$ 结构上不成立, 所以 $y'_n\sqsubseteq^0\eta_n$ 没有路. 没有编译否定, 只写未走通. 另一条路: 不累加, 证链点的相邻项字面第一位置 (模 `≈`), 那样树与 `OCF.Free` 同值, 但 `Lg` 要字面相等, `≈` 给不出 (没有函数外延). 没有试.

**有限测试 ([Accept](CumReadAccept.lagda.md), [AcceptW](CumReadAcceptW.lagda.md), `refl`, 不是证明).** 比较器 `fpO`, `fpZ`: 零, 后继, 极限的前 $w$ 项的形状, 深度 $d$ 截断. **看不见下标的差别在更深处的影响.**

| 对象 | 比较器, $d$, $w$ | 结果 |
|---|---|---|
| `Y (natA n)` 对 `OCF.Free` 的 `ψ̄ ∘ tl`, $n=0..3$ | `fp`, 8, 3 | 一致; 对照 `ctl` 分得开 |
| `Tᵂ₁`, `TΩ+ 1`, `TΩ+ 2` 对 `forceᴺ (GᴺΩ̇ n)`, $n=0,1,2$ | `fpO`, 4, 2 | 一致; 对照 `ctl-TF` 分得开 $\Omega$ 与 $\Omega+1$. `Tᵂ₁` 深 7 宽 2 在 300 秒内没有结果 |
| `fgh (TP 0) 0`, `fgh (TP 1) 0` | `refl` | 都是 1. 只说明算得动 |

**盲区.** 深 4 宽 2 只看到第 0, 1 项的前几层. 新链与旧链的差别 (下标不同) 在这个深度看不到, 所以 **这组测试没有检验累加是否被吸收.** $\Omega\cdot2$ 与 $\Omega^n$ 没有参照的比较.

## 第一个障碍

带闭包的层的证书. `Tψ` 的 `HS` 要 `ψL` 在 [CumReadW](CumReadW.lagda.md) 上的类比. 判断 (纸面, 没有编译): 第 0 层的闭包的链从它的世界 $b$ 出发, 而 `no-⊞-left` 说 $b\lhd b'$ 推不出 $b+x\lhd b'+x$. 所以 **同一个闭包在两个世界算出的两条链字面不可比.** `ψ` 的输出世界已经规范化 (`mx`), 只剩目标路径的世界 $\tau$: $\psi_\Omega(\Omega_{\eta+1})$ 的节点在 $\eta$ 下面, 上升时 $\tau$ 取到这个 $\eta$. 比较 $\eta\lhd\eta'$ 两个分支时, 第一位置上同一个节点的 $\tau$ 不同, 里面保留的闭包的世界就不同, `≈` 不成立. 我没有写 `≈` 并编译到报错, 这是读定义得到的.

判断的出路: $\tau$ 不从路径读, 从目标层本身读 (目标 $k$ 是可数层时取 $k$ 自己的字面值, 走分支的路径换成规范的 `bra k self`). 障碍: `upL` 不是字面单射 (没有函数外延), 所以 $k$ 的字面值要模结构等价. 没有写. **未走通, 不是否定.**

## 受记号影响的形状

$\psi_t(a+1)=\psi_t(a)\cdot\omega$, $\psi_t(0)=\Omega_t$, 上升的链, 目标与节点的比较: 继承 `OCF.Free`, 形状来自记号. `cumsum` 来自已发表的 BTBO. `P n` 的读法来自序数算术. **树侧逼出的:** `⊴`, `≈`, 世界, `no-cum-⊲`, `no-⊞-left`. 不算树自足.

## 壁垒 (判断)

下标类型是 `A`, 没有 $\Omega$-共尾元. `Lv` 的 `lc` 不作下标. 比较只在字面的世界之下 (`C.cmpF`). 没有全局三歧. 我没有证明这组定义永不触犯壁垒.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumRead where

open import OCF.Align.CumReadBase using (cumA; Lg-cum; next; next-⊲; Lg-next; ordᴸ; Legal-ordᴸ; no-Legal-ordᴸ; no-cum-⊲; overshootᴬ; dom-cum; absorb; absorb-ω; no-⊞-left)
open import OCF.Align.CumReadCF using (A; O; ψ; ψ₀Ω)
open import OCF.Align.CumReadCFEq using (_≈_; ψQ)
open import OCF.Align.CumReadCFThm using (_⊴_; WF; ψL; ψW; Y; HS-Y; Y-mono)
open import OCF.Align.CumReadTop using (module Clo; Tᶜ; HS-Tᶜ; fghᶜ)
open import OCF.Align.CumReadW using (Lv; Legal; Tψ)
open import OCF.Align.CumReadWLv using (Ωᴸ; Legal-Ω; Legal-+; Legal-M; Legal-·Ω; Legal-P; Tᵂ₁; TΩ+; TΩ·; TP)
```

## 审计

`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.LevelFixCore --only OCF.Align.LevelFixVal --only OCF.Align.CumRead OCF.Align.CumRead`: 退出码 0. 正对照 `OCF.Align.LevelNoKAccept`: 退出码 1. [AcceptW](CumReadAcceptW.lagda.md) 只读 `OCF.Free` 主线的树, 过禁用表 (退出码 0); 标签在 `OCF.Free.Bridge`, 这里没有导入, 所以它是对带标签的树的比较, 不是读标签.

`depslice.py` (语法级, 看不见隐式参数):

| 根 | 到达块数 | 记号模块块数 | 别处的记号词 |
|---|---|---|---|
| `CumReadCFThm:HS-Y` | 191 | 0 | 0 |
| `CumReadTop:HS-Tᶜ` | 219 | 0 | 0 |
| `CumReadW:Tψ` | 118 | 0 | 0 |
| `CumReadWLv:TP` | 136 | 0 | 0 |
| `CumReadBase:no-Legal-ordᴸ` | 84 | 0 | 0 |
| 正对照 `LevelNoKAccept:a-Ωω` | 410 | 48 | 5 |

全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 无 `trustMe`, 没有 `Un`, UIP, 函数外延. 这些只保证不引用记号, 不说明定义没有受记号启发.
