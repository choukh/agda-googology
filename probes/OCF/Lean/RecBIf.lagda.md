# RecB: 接口 (世界塔的每一层)

> 不含记号. 入口 [RecB](RecB.lagda.md). 构造一路 RecB, 否定一路 NegRecB 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 [CRwBase](CRwBase.lagda.md), [CRwIf](CRwIf.lagda.md).
>
> **接口定稿 2026-11-06 01:48 (首次编译通过).** 定稿后只增不改.
>
> **设计 (构造一路的计划, 不是接口的律).** 层号是 (底的序号 $n:\mathbb N$, 可数高度 $m$), 读 $\Omega\cdot n+m$. 底对 $n$ 递归: 第 $0$ 个底是空结构 `S⊥`, 第 $n+1$ 个底是 `XSof (bS n)` $=\sup_{c}$ `Tw (bS n) (hs c)` (第 $n$ 个底上一切可数塔的并; $n=0$ 时字面就是 CRw 的 `XS`). 折叠对一切底一份: 同底折叠 (底种类留, 塔的新种类以层号高度为公共上界比较) 与跨底折叠 (从第 $n+1$ 个底折到第 $n$ 个底上的第 $t$ 层; `XSof` 的种类 $(c,\kappa)$ 带证据 $c+1\lhd B_{n+1}$, 以世界的界 $B_{n+1}$ 为公共上界比较; 底种类一律留).
>
> **世界是塔.** 第 $k$ 个底的分量序号由第 $k$ 层的世界 $B_k$ (一棵合法的可数树) 界住; 每一层的世界各自按本接口移动. 跨底折叠只移动自己那一层的世界; 下层的路径要求在上层的树里**冻结** (下层世界不随上层的回灌移动), 输出到下层后再解冻 (定理, 用 `PH-mono`). 冻结的理由 (判断, 待编译): 上层回灌 $B_{k+1}\boxplus\mathrm{leg}\,c$ 后的分支若在下层也移动世界, 输出的分支要在 $c+1$ 里带路径, 输入的分支只在 $(B_{k+1}\boxplus\mathrm{leg}\,c)+1$ 里带路径, 方向反了.
>
> **律.** 每一层世界的移动就是 `CRwIf` 的 7 个字段 (`adm-sh`, `nx-up`, `lg-nx`, `adm↓`), 律里成对的世界都带字面 $\lhd$ 证据, 没有对裸下标的比较律. 新增: 各层共用的初始世界 $W_0$, 带字面证据 $1\lhd W_0$ (第 $k$ 个底的地板的根是 $\Omega_1$ 的拷贝, 证据是分量序号 $0$ 的 $0+1\lhd W_0$) 与 $W_0$ 合法.
>
> 实例 (`RecB.J₁`): `mv = CRw.I₁`, $W_0=1$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RecBIf where

open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf public

record RecBIf : Set₁ where
  field
    mv  : CRwIf          -- 塔的每一层世界的移动 (CRwIf 的 7 个字段)
    W₀  : Cd             -- 每一层的初始世界
    o₀  : hs hz ⊲ W₀     -- 字面证据: 1 ⊲ W₀
    lW₀ : LgB W₀
```
