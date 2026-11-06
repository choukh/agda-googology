# 望远镜世界 (入口): 设计 D1 走到哪里, 卡在哪里

> 不含记号. 设计来源: [Survey/ClosedTermReview.md](../../Survey/ClosedTermReview.md) §2 D1 与实验 [ClosedReview1](ClosedReview1.lagda.md). 目标 "写出 ψ₀Λ 的候选闭项". 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **判决: D1 未走通, 停在第 2 步 ($\Omega_x$ 一步与 $\Lambda$); 第 3, 4 步 (折叠, 闭项) 没有开始. D1 没有被否定.**
>
> 1. **第 1 步过了 (定理).** 望远镜种类结构 `ST lvs` (种类是位置, 层号在类型里) 是 `HtTowerTy.KS` 的实例; 比较 `cmpT = cmpB {ST lvs}` 对一切望远镜一条; 升高一个位置的界 `rais` 是定义 (`at`/`off`), 世界变大且保合法 (`rais-≤`, `Lg-rais`); 推入与弱化保第一位置与合法 (`wk-⊲`, `Lg-wk`). 携带的位置上 $\Omega_{\mathrm{lv}\,p+1}$ 合法 (`Ωp`, `Lg-Ωp`). 这些与 `DiagKLev.upd→wdec` 的墙无关: 没有一处比较层号.
> 2. **第 2 步的障碍 (定理 + 判断).** (a) 固定的有限望远镜装不下 $x\mapsto\Omega_x$ (`no-fixed-Ω`, 由 `no-all-fin`; 正对照 `TopNewSL`: 积世界 `SL` 满足同一形状). 所以 $\Lambda$ 的高度必须让分支体**推入**新位置 (审查自己写的 `g : (c : …) → H (c ∷ Γ)`). (b) 推入的位置要一个界. 同一层号在折叠的历史里会推入不止一次; 若同层位置由路径自选, 回灌升高携带的那个位置就失去可比 (`raise→¬cmp`, 一般形 `sel→¬cmp`, 前提可满足 `cmpF-Γ₀`); 若界由路径存在地选取, 一开始就不可比 (`exists→¬cmp`). (c) 剩下 "每个推入的出现恰好一个位置": 按层号查是 `find→dec`, 按出现查是 `occ-find→dec` (出现由分支坐标确定), 把世界做成分支坐标上的积就是 `DiagKLev.upd→wdec` 的 $I$ = 坐标. **(a) (b) 是本轮编译的否定, 各自只杀写明的接口; "(b) (c) 穷尽了推入位置取界的办法" 是判断.**
> 3. **墙挪了地方, 没有消失 (判断).** 审查说 D1 把判定从 "写" 挪到 "读". 本轮看到的是: 在 $\Lambda$ 这一站, 被读的不是层号, 而是**推入的出现** (分支坐标). 积世界的 `∏_{k:LH}` 在 D1 里重新出现为 "对一切分支坐标 $c$, 分支体推入的那一位置的界", 即同一堵墙 (命题 W) 的 $I$ 从层号换成了分支坐标.
>
> **第一个障碍的精确形式:** 第 2 步要一个世界结构 $\mathcal W$, 对 $\Lambda$ 里每个推入的出现给出一个界, 满足: (i) 同一出现的两条路径拿到同一个界 (否则 `exists→¬cmp`), (ii) 回灌可以升高当前路径上那个出现的界 (`rais` 的形状), (iii) 升高后一切出现仍满足 `cmpT` 要的 "同一界之下"; 并且不按层号或出现查 (`find→dec`, `occ-find→dec`), 不在出现上做选择性更新 (`upd→wdec`). **下一条引理**: 要么构造 "由外层界决定的界族" $F\,b\,c$ (出现在外层位置 $p$ 的分支 $c$ 里, 界是 $p$ 的界 $b$ 的函数), 使回灌升高 $b$ 时在当前分支 $c_0$ 处忠实、在别的分支处单调合法 (这是审查 §1.1 的命题 W′ 在 D1 里的版本, 现在没有定理); 要么把 W′ 写成一条一般的否定. 这正是 D2 (`ChainZ`, 另一路) 的 "世界只增不读" 要回答的问题, 所以 D1 的下一步与 D2 合流.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TelW where

open import OCF.Align.TelWTy public
open import OCF.Align.TelWOm public
open import OCF.Align.TelWNeg public
```

## 定理表

| 名字 | 文件 | 内容 | 档 |
|---|---|---|---|
| `ST`, `HT`, `cmpT` | `TelWTy` | 望远镜种类结构; 比较对一切 `lvs` 一条 (就是 `cmpB {ST lvs}`) | 定理 |
| `rais`, `rais-at`, `rais-≤`, `Lg-rais` | `TelWTy` | 只升高位置 $p$ 的界: 定义, 世界变大, 保合法 | 定理 |
| `wkH`, `wk-⊲`, `Lg-wk`, `push-old`, `Lg-push` | `TelWTy` | 推入新层: 旧高度弱化保第一位置与合法, 旧界原样 (`refl`) | 定理 |
| `ιT`, `Ωp`, `Lg-Ωp` | `TelWOm` | 携带的位置 $p$ 上 $\Omega_{\mathrm{lv}\,p+1}$ 合法 | 定理 |
| `no-all-fin` | `TelWOm` | 固定望远镜不含一切有限层号 (鸽笼) | 定理 (否定) |
| `no-fixed-Ω` | `TelWOm` | 固定望远镜上没有后继处顶层种类取参数层号的 $x\mapsto\Omega_x$ | 定理 (否定) |
| `TopNewSL` | `TelWOm` | 正对照: `LFReTower.Ω̂` 在积世界 `SL` 上有这个形状 | 定理 |
| `cmpF-Γ₀` | `TelWNeg` | 前提可满足: 两个同层位置的合法世界, 路径自选的并之下可比 | 定理 |
| `raise→¬cmp`, `sel→¬cmp`, `¬cmpF-Γ₁` | `TelWNeg` | 路径自选 + 升高携带的位置 (任何 `at`/`off` 实现) ⇒ 失去可比 | 定理 (否定) |
| `exists→¬cmp` | `TelWNeg` | 推入位置的界由路径存在地选取 ⇒ 不可比 | 定理 (否定) |
| `occ-find→dec` | `TelWNeg` | 按出现 (分支坐标) 查位置 ⇒ 坐标相等可判定 (`ClosedReview1.find→dec` 的实例) | 定理 (条件) |
| (b)(c) 穷尽推入位置的取界办法 | — | | 判断 |
| `Λ` 之下要以分支坐标为层号的推入 (不可数多个) | — | 读法 | 判断 |

## 翻译账

| 新东西 | 来源 | 记号规则? | 脚手架是值要的还是翻译带来的 |
|---|---|---|---|
| 望远镜 `Tel`, 位置 `Pos`, 种类 = 位置 × 层内种类 | `upd→wdec`, `find→dec` 逼出 (审查 D1) | 否 | 值要的 (种类的界要能选择性升高) |
| `rais` = 只改一个位置的 `b ⊞ δ` | `HtTowerFFold.RunM` 的回灌形状, 搬到位置上 | 否 | 值要的 |
| `wkH` | 推入新层的类型要求 | 否 | 树逼出 |
| `Ωp` | `LFReTower.Lg-Ω̂` 后继情形的同一证明 | 否 (x ↦ Ω_x 是目标, 不是记号规则) | — |
| 否定的接口 (`AdmF`, `AdmE`) | D1 的推入在 $\Lambda$ 处的两种直接写法 | 否 | 否定划出不能有的字段 |

没有字段读自记号的基本列; 没有用 `Lab`. 这一步**提供信息**: 它用否定定理划出了 D1 在 $\Lambda$ 处不能用的两种取界方式, 并把墙定位到 "推入出现的界"; 没有加深翻译 (没有新增构造子, 没有阶段专属前提).
