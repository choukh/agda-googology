# 结构关系, 第八轮: 左边 `nw`: 入口

> **判决: PARTIAL (否定一条规则, 其余暂停).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件, 没有改树与折叠.
>
> 1. **(否定, 编译) 不带前段对齐的 `nw` 规则不可靠** (`StrRel8Neg.¬nwˡ`). $x_L=\mathrm{nκ}(\lambda\_\,\_\mapsto 1)$ 在树世界 0, $x_R$ 同形在树世界 1, $x_L\sqsubseteq^{+}x_R$ (`hx`, 由 `κ⁺`); 但 `SemS (nw p x_L) x_R` 不成立 ($p$: 0 ⊲ 1). 前提全部可满足: 运行世界两边都是 1, 路径 `self`, 对齐 `aS`, 空状态 (自洽 `ch∅`). 左边第 0 格走过位置 0, 读数非零 (`yesL`, 由有限检查 `chk` 与它的可靠性 `chk-ok` 给出); 右边每格路径都是 `self`, 读数全是 0 (`isS`, `q0`, 对格号归纳). 范围: 推翻 "$x\sqsubseteq x'\Rightarrow\mathrm{nw}\,p\,x\sqsubseteq x'$", 也推翻两边的 "$x\sqsubseteq x'\Rightarrow\mathrm{nw}\,p\,x\sqsubseteq\mathrm{nw}\,p'\,x'$" (取 $p'=$ `self`, 因为 `Run (nw self x′) q = Run x′ q`). **不**推翻 "$\mathrm{nw}\,p\,x\sqsubseteq x$" (同一棵树, 右边也从 $V_0$ 出发): 它未走通.
> 2. **(暂停) 带前段对齐的 `nw`.** 换世界 `cv` 产生的 `nw` 两边的前段是 `sum-fst W z` 与 `sum-fst W′ z′`, $z\sqsubseteq^{\mathsf P}z'$, 这正是 `genᴾ` 能生成对齐的形状. 但对齐 `Al L L′` 以**运行世界** $L,L'$ 为参数, 前段的对齐要领先量 `Adm (sum W z) (sum W′ z′) L L′` (树世界处 "左边剩下的不比右边长"), 它不是静态的, 而 `Al` 在 `aS` 处不带领先量, 所以由 `SemS` 的前提推不出 (判断). 要的是把语义改成在树世界处也带领先量 (与 `KNestSound` 的带下标关系同形), 本轮没有做.
> 3. **(暂停) 多层族、移植、`MonoStep`.** 上级的 (2) 以第 1 条走通为前提. 第 1 条只得到否定与一个改语义的方向, 所以 (a)(b)(c)、移植到 `HtFeedFold`、在 `Ωᴴ` 处的 `MonoStep` 都没有做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel8 where

open import OCF.Align.StrRel8Neg public using (Nz; nzm; chk; chk-ok; IsSelf; wz; xL; xR; hx; isS; q0; pt0; ¬nwˡ)
```

## 1 为什么第 1 条说明的是 "前段"

`Run (nw p x) q = Run x (⊲-tr p q)`: `nw` 只把路径在底部接长. 对齐从顶端往下配对, 左边底部多出而右边已到起点时没有构造子 (`StrRel7.¬Al-lft`). 反例说明这不只是证明方法的缺口: 值上就错了 (左边非零, 右边为零), 所以任何可靠的 `nw` 规则都必须带关于底部两段的前提. `cv` 里两段由读数的和生成, 能对齐的前提是领先量, 见判决第 2 条.

## 2 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `¬nwˡ` | `Run` 对 `nw` 的展开与 `κc` 的第 0 格 (路径 `self` 时走法为空) | **树逼的** (否定) |
| 前段对齐要领先量 (判断) | `Al` 以运行世界为参数, `genᴾ` 要 `Adm` | **树逼的** |

**归类: 提供信息** (否定定理划出 `nw` 规则不能没有的前提). 没有新构造子或节点字段, 没有 `Lab`, 没有记号.

## 3 审计与账

- 编译: 删掉本轮两个 `.agdai` 后从入口从头编译, 退出码 0. 无禁用构造.
- 导入闭包 (`--only` 同 [StrRel7](StrRel7.lagda.md)): 61 个模块 (本地 51, 库 10), 禁用表命中 0, `--only` 之外 0, OK.
- `depslice.py`: `StrRel8Neg:¬nwˡ` 152 块, 记号模块 0, 别处记号词 0; 正对照 `Om1HnAccept:label-term₀` 1188, 92, 58.
- 代码行 (代码块内非空): 入口 3, `StrRel8Neg` 83.
