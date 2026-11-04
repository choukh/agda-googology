# 严格列: 只接受带证书的高度

> **判决: PARTIAL.** 目标 1 **HOLDS**. 目标 2 **HOLDS**, 其中 $\omega^\omega$, $\varepsilon_0$ 有一处要看清 (见下). 目标 3 **条件定理**: 证据的链写出来了, `T⊤` 是它的一个实例 (`same-T⊤`), 累加只剩一个参数 `Out`; 无累加的 `Out` 未走通, 不是否定. 目标 4: 第一个障碍精确到类型报错和定理.
>
> | 定理 | 陈述 | 文件 |
> | --- | --- | --- |
> | `Lit` | $t$ 的每个极限的前一项是后一项的字面子项 | [TLCodeLit](TLCodeLit.lagda.md) |
> | `HL h` | 对每个 `h : Lit t`, 一个 `HtB`, 11 个字段全闭合 | 同上 |
> | `rk-top`, `rk-chain`, `view-top` | 顶的秩就是 $t$ (`refl`); 顶的链是列本身 | 同上 |
> | `find`, `rk-inj`, `linear` | 位置与 $t$ 的字面子项一一对应 | 同上 |
> | `Gᴸ h p α`, `growᴸ`, `val≼ᴸ` | `GᴺTᵠ` 的特例, 闭包定理不改; 严格增长; 第 0 行不低于 $t$ | [TLCodeCert](TLCodeCert.lagda.md) |
> | `Lω·2`, `Lω²`, `Lω^ω`, `Lε₀`, `E<` | 检查点的证书; 塔不用分隔符 | [TLCodeArith](TLCodeArith.lagda.md) |
> | `Tω·2ᴸ`, `Tω²ᴸ`, `Tω^ωᴸ`, `Tε₀ᴸ`, `fgh…ᴸ` | 闭项与 FGH | [TLCodeCert](TLCodeCert.lagda.md) |
> | `Br.sim`, `val≅`, `fgh`, `lvl≅`, `val≈` | 块形同形则树一致, 计值 $\cong$, 序数值互相 `≼` | [TLCodeBridge](TLCodeBridge.lagda.md) |
> | `acc-ω·2`, `acc-ω²` | `Tω·2ᴸ ≅ Tω·2`, `Tω²ᴸ ≅ Tω²` | [TLCodeAccept](TLCodeAccept.lagda.md) |
> | `acc M p α`, `lv-exact M` | 一切旧码进新世界, 树 $\cong$, 值互相 `≼` | 同上 |
> | `acc-ω^ω`, `acc-ε₀`, `acc-feed` | `Lv M` 上的树 $\cong$ `Tω^ω`, `Tε₀`, `T-feed` | 同上 |
> | `new⊂old`, `Lit-val` | 一切新码进旧世界, 码的值与 $t$ 互相 `≼` | 同上 |
> | `Str→Lit`, `Str→Lit-val` | `Str` 的 $\eta$ 有 `Lit` 的码, 值互相 `≼` | 同上 |
> | `no-~ω^ω` | `ω^ωᴸ` 与 `ω^ωᶜ` 不逐块同形 | 同上 |
> | `up-simᴸ`, `up≺ᴸ`, `⊂⊕` | 新世界的上移 | [TLCodeUp](TLCodeUp.lagda.md) |
> | `Chain.Gν`, `Chain.Fx.*`, `𝕋ʷ` | 证据的链, 闭包定理, 输出与高度互相共尾, 对任何 `Out` | [TLCodeFeed](TLCodeFeed.lagda.md) |
> | `same-T⊤`, `same-fgh`, `pad~`, `⊕~` | 取 `padO` 时链上的树 $\cong$ 已有的 `T⊤`; `ᶜ+` 就是 $\oplus$ | [TLCodeFeedPad](TLCodeFeedPad.lagda.md) |
> | `exact→LPO`, `binder→LPO`, `no-Lit-deg`, `no-Good→Str`, `Out0.no-Str-out` | 只否定写明的陈述 | [TLCodeNeg](TLCodeNeg.lagda.md) |
>
> **条件定理.** `T⊤ˣ : ExactOut → LC → Ordᶜ zero`, `ofLit`, `ofStr`: 只要每个输出的层号带证书, 就有无 `⌈_⌉` 的闭项. 前提未证.
>
> **有限测试 (不是证明).** [TLCodeTest](TLCodeTest.lagda.md), 比较器 `refl`. `fghε₀ᴸ 1` 在 12G 堆内没有结果 (退出码 251), 已从测试里去掉; 这不是否定. 判断: `tw 0` 的列是 $1,2,3,\dots$, 算这个值要走高度 $1$ 的树, `ε₀ᶜ` 那边走高度 $0$, 所以比 `fghε₀ 1` 难算.

## 这是什么

旧码 `cl g` 的值是 $\sum_j(g_j+1)$: 任何 $g$ 都严格, 不用证明. 这里反过来, 极限就是 `lim f s`, 要证据才能作高度. 证据是 `f n <ᴵ f (suc n)`. 三件事因此变了:

1. **值是字面的.** 位置的秩是 $t$ 的字面子项, 顶的秩是 $t$. `rk<` 由证书直接给出, 不再要 `plus`, `Sb`. `dom₀` 没有位置, `⌈_⌉` 不在闭包里.
2. **列是绝对的.** 顶的链是 $f_0,f_1,\dots$. `ε₀ᴸ` 的列就是 $\omega^1,\omega^{\omega^1},\dots$.
3. **位置仍按块分解.** 块 $i+1$ 是 $f_{i+1}$ 高于切点的部分. `Sh` 只记这个形状, 没有值. 这是表示唯一 (三歧的相等是 $\equiv$) 的代价, 也是 `view` 的来源. `Sh` 的序, 三歧, 根, 写法与 `Pos` 逐行相同, 因为它们与值无关.

**字面严格就是前缀.** `Lit (lim f s)` 说 $f_{n+1}$ 字面含 $f_n$. 判断: 这和 `cl` 的块是同一件事的两种写法 (绝对与差分), `Lit-val` 和 `lv-exact` 是两个方向的定理: 块形读成码, 值就是 $t$; 码写成列, 值就是 `val`. 所以真正要去掉的累加不是 `ᶜ+` 或块分解, 而是 $\lceil\cdot\rceil$ 对非严格极限的放大. `⊕~` 说链上的 `ᶜ+` 就是通常的 $\oplus$.

**$\lceil\cdot\rceil$ 是什么 (判断, 依据是 `exact→LPO`).** 路径 $(j,q)$ 按块号字典序比较, 不看值. 这个序在非严格极限上不是值的序, 所以值被放大. 按值比较要判定退化, 那是 `exact→LPO`.

## 目标 2 的那一处

`Tω·2ᴸ`, `Tω²ᴸ` 用的字面的列 ($\omega\cdot k$) 与旧码逐块同形, 直接 $\cong$. `ω^ωᴸ`, `ε₀ᴸ` 不是: 旧的 `ω^ᶜ 1` 块长 2, 列 $1,3,5,\dots$; `E 1` 的列 $1,2,3,\dots$. `no-~ω^ω` 是这一点的定理.

- 已有的 `Tω^ω`, `Tε₀`, `T-feed` 都有新世界的高度 (`Lv M`, `acc-*`), 但 `Lv` 的列带分隔符 `suc`, 就是旧码的列.
- `Tω^ωᴸ`, `Tε₀ᴸ` 的树 $\cong$ 旧世界里 `toC (shape h)` 这个码上的树 (`new⊂old`), 码值与 $t$ 互相 `≼` (`Lit-val`). 与 `Tω^ω`, `Tε₀` 本身没有比较: **未走通**. 基本列错开, `≈ᴿ` 不成立, 要 [EmbVV](EmbVV.lagda.md) 那样的开关. 判断: `ω^ωᴸ` 与 `val ω^ωᶜ` 同值, 没有编译.

## 目标 3: 证据的链

$C_{n+1}=C_n\oplus(\mathrm{out}(C_n)+1)$, 证据 `⊂⊕`. `Chain` 对任何 `Out` 给闭包定理与定点. 取 `padO` ($\mathrm{out}$ 用 `lv₀ ⌈ ly c ⌉`) 时 `same-T⊤ : T⊤ᵖ ≅ T⊤`. 所以 **累加只剩 `padO`**, 目标缩成一个问题: 输出的层号有没有证书.

**`viewE→LPO` 会不会挡住?** 挡统一的转换, 不挡这条路线. 编译过的是 `exact→LPO`: 任意 `Ordᴵ` 都有精确的 `Lit` 码推出 LPO. 回灌只对折叠的输出取码, 链上 $\alpha=0$; `exact-Lit`, `exact-Str` 说带证书的 $\eta$ 满足前提. 没有定理否定 "输出带证书".

**第一个障碍.** 把 `Str` 从 `Goodᴺ` 读出来, 卡在 `gl` 的步进 (报错原文):

```text
_c_11 ≺ forceᴺ (f n) (G n) → _c_11 ≺ forceᴺ (f (suc n)) (G (suc n))
!=<
toLevel (forceᴺ (f n) (G n)) (hl₁ (forceᴺ-HS (Z.lim f) (gl G st)) n)
≺ᴵ
toLevel (forceᴺ (f (suc n)) (G (suc n))) (hl₁ (forceᴺ-HS (Z.lim f) (gl G st)) (suc n))
when checking that the expression st n has type ...
```

这不是工程量的问题: `no-Good→Str` 说只由 `Goodᴺ` 读不出, `no-Str-out` 说 $\alpha$ 退化时输出确实退化 (两项互相模拟). 所以要一条新的闭包定理, 证书的步进从 `⊑⁰` 加强到 $\prec$, 并跟踪 $\alpha$ 的严格性. 判断: 这要重走 `Good`, `Class`, `Omega`, `Strict` 那约 1 万行; `Ls true`, `grow` 是已有的部分. 没有写. 有限测试 (`TLCodeTest` §3 与一次性的扫描): 最低高度的 $a_0\prec a_1$, $a_1\prec a_2$ 在预算内找到字面拷贝; 第 1 行的前几项不互相 $\cong$ (截断比较); $y_0\prec y_1$ 预算内没找到. 没有证据说它假, 也没有证据说它真.

**确实要对不带证书的 $\eta$ 取高度的地方.** 不在 `T⊤` 的链上, 在数据树: [CrossMTop](CrossMTop.lagda.md) 的 `ψ̄ᵀ (tH x g) = ŝA 0 zero _ (λ η d → … ⊂+ M ⌈ η ⌉ …)`. `ŝ` 的绑定对任意 $\eta$ 要一支, 高度的类型里没有证书可取. 要精确就是 `binder→LPO` 的前提. 这条只否定不改绑定类型的写法; 绑定带证书的码要动 `Ordˢ`, `Z`, `Goodᴺ`, 并且运行时要给链点证书, 又回到上面那条定理. 未走通.

## 壁垒

下标类型没有变. 没有全局三歧: 比较都在一个 `Lit t` 之内, 字面公共上界就是 $t$. `no-all-Ord`, `all-Ord→LPO` 否定的单一高度类型这里没有用: `HL h` 对每个 $t$ 一个. 没有 Ω-共尾元. `exact→LPO` 与 `viewE→LPO` 同形, 见上.

## 是否按阶段定制

否. `HL`, `find`, `val≼ᴸ`, `Chain`, `lv-shape`, `⊕~` 对一切 `Lit` 或一切码. 检查点是实例.

## 受记号影响的形状 (如实说)

树, 第 0 行分三种写法, 读法 $\psi_0(\Omega_{\Omega\cdot(1+\mathrm{rk}\,p)+\alpha})$ 都继承自 [LadderOrd](LadderOrd.lagda.md), 账不变, 不算树自足. 新增的 `Lit`, `Sh`, `above`, `rkT`, `⊕`, `E`, `Chain` 是 Brouwer 树和类型的要求, 没有看记号. 回灌链的形状读自记号的规则 (见 [CrossM](CrossM.lagda.md)). 读法是判断, 没有标签. 这一路不读记号, 没有记号文件.

## 审计

- **导入闭包:** `importclosure.py --only OCF.Free. --only OCF.BTBO --only OCF.Align.LadderNF --only OCF.Align.LadderMono --only OCF.Align.LadderInf --only OCF.Align.LadderOrd --only OCF.Align.CrossMSim --only OCF.Align.TLCode` 对 `TLCodeShape`, `TLCodeLit`, `TLCodeArith`, `TLCodeCert`, `TLCodeUp`, `TLCodeFeed`: 退出码 0, 禁用表 0. 这六个的闭包不含 `LadderOrdPos`, `LadderOrdCode`, `LadderOrdStr`, `LadderOrdCert`, `LadderOrdClosed`, `CrossMNode`, `CrossMUp`, `CrossMTop` (字面搜索闭包列表). 对照: `TLCodeAccept`, `TLCodeFeedPad` 的闭包含 `LadderOrdPos`, `LadderOrdCode`. 入口 `TLCode` 退出码 0. 记号的正对照 `CrossMAccept`: 退出码 1.
- **定义级切片 `depslice.py` (块数, 记号块, 词命中):** `HL` 83, 0, 0; `Gᴸ` 1088, 0, 0; `val≼ᴸ` 1135, 0, 0; `Lε₀` 44, 0, 0; `up≺ᴸ` 1179, 0, 0; `up≺ᶜ` 1188, 0, 0; `same-T⊤` 1284, 0, 0; `acc-ε₀` 1265, 0, 0; `exact→LPO` 27, 0, 0; `no-Str-out` 1041, 0, 0. 正对照 `CrossMAccept:fs-ψΩ` 51, 43, 3. `T⊤ᵖ` 只到 159 块: 切片看不见模块实例 `𝕋ʷ` 的参数, 这是脚本写明的局限, 以 `up≺ᶜ` 和闭包为准.
- 切片是语法级的; 闭包是编译器保证的, 但不说明定义没有受记号启发.
- **禁用构造:** 全部 `TLCode*` 没有 `postulate`, 洞, 停机或正性编译指示, `trustMe`, `--cubical`; 全部带 `--safe --without-K`.

全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCode where

open import OCF.Align.TLCodeShape public using (Sh; sz; ss; sl; Pos; end; low; blk; _<ᴾ_; <ᴾ-tri; <ᴾ-prop)
open import OCF.Align.TLCodeLit public using (Lit; lz; ls; ll; shape; above; rkT; rk<; rk-top; rk-chain; view-top; find; rk-inj; linear; HL)
open import OCF.Align.TLCodeArith public using (_⊕_; L⊕; E; LE; E<; Lω; Lω·2; Lω²; Lω^ω; Lε₀; ω·2ᴸ; ω²ᴸ; ω^ωᴸ; ε₀ᴸ; tw)
open import OCF.Align.TLCodeCert public using (Tᴸ; Gᴸ; growᴸ; val≼ᴸ; Tω·2ᴸ; Tω²ᴸ; Tω^ωᴸ; Tε₀ᴸ; fghω·2ᴸ; fghω²ᴸ; fghω^ωᴸ; fghε₀ᴸ)
open import OCF.Align.TLCodeBridge public using (_~_; pm; module Br)
open import OCF.Align.TLCodeAccept public using (acc-ω·2; acc-ω²; acc-ω^ω; acc-ε₀; acc-feed; acc; lv-exact; lv-shape; module new⊂old; Lit-val; Str→Lit; Str→Lit-val; no-~ω^ω)
open import OCF.Align.TLCodeUp public using (_⊂_; up; up-simᴸ; up≅ᴸ; up≺ᴸ; ⊂⊕)
open import OCF.Align.TLCodeFeed public using (LC; lc; module Chain; module 𝕋ʷ; up≺ᶜ)
open import OCF.Align.TLCodeFeedPad public using (padO; T⊤ᵖ; fgh⊤ᵖ; same-T⊤; same-fgh; ⊕~)
open import OCF.Align.TLCodeNeg public using (exact→LPO; exact-Lit; exact-Str; binder→LPO; no-Lit-deg; no-Good→Str; module Out0; StrOut; ofStr)
open import OCF.Align.TLCodeTest using ()
```

## 导航

| 文件 | 内容 |
| --- | --- |
| [TLCodeShape](TLCodeShape.lagda.md) | 块形, 位置, 序, 三歧, 第 0 行的写法; 没有值 |
| [TLCodeLit](TLCodeLit.lagda.md) | 证书 `Lit`, 秩, 实例 `HL` |
| [TLCodeLe](TLCodeLe.lagda.md) | Brouwer 序 |
| [TLCodeArith](TLCodeArith.lagda.md) | $\oplus$, $\omega^x$, 检查点 |
| [TLCodeCert](TLCodeCert.lagda.md) | 证书, `grow`, 闭项 |
| [TLCodeTest](TLCodeTest.lagda.md) | 有限测试 |
| [TLCodeUp](TLCodeUp.lagda.md) | 上移 |
| [TLCodeFeed](TLCodeFeed.lagda.md) | 证据的链 |
| [TLCodeBridge](TLCodeBridge.lagda.md) | 验收工具: 块形同形 (导入 `Code`) |
| [TLCodeAccept](TLCodeAccept.lagda.md) | 序数值验收 (导入 `Code`) |
| [TLCodeFeedPad](TLCodeFeedPad.lagda.md) | 有累加的 `Out`, 复现 `T⊤` (导入 `Code`, `⌈_⌉`) |
| [TLCodeNeg](TLCodeNeg.lagda.md) | 否定 (导入 `Code`) |
