# 第三种组织: 否定一路 (入口)

> 不含记号. 与构造一路 `Third` 配对 (作者本轮选定 "攻: LHRec 的第三种组织"). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP. 函数外延只在 `NegThirdPre.upd→WLPO` 作前提. 本路没有关闭任何路线.
>
> 1. [NegThirdPre](NegThirdPre.lagda.md) (接口之前, 写在 `LHRec` §4 的设计上): `floor-forces`, `floor-no-stay`, `case-*` (内层指标在下层路径里不平凡); `keep-req`, `real-keep-fails`, `init-keep-fails`, `no-lower-rule` (留下带回灌, 任何下层规则都对不上); `upd→WLPO` (条件), `WB.weak-eq` (写回); `bd-dec→LPO`; `clT`, `node-form`, `bdK` (分类, 正面); `upL-collide`; `xb-naive`, `xb-acc`.
> 2. [NegThirdIf](NegThirdIf.lagda.md) (接口 `ThirdIf`, 21:21 定稿): `Pos↑`, `embP`, `Pos-emb`; `pos-wdep`, `pos-dec→LPO`, `Ill.no-pos`, `Twop.emb-not-unique`; 盲 `Blind.stay`, `KrS.J`, `sh-frozen`; `fb-must-legalize`, `no-plain-sh`; `frozen-no-pos`; **`no-wash`**.
> 3. [NegThirdStamp](NegThirdStamp.lagda.md): `antisym`; 戳方案三难: `SE.branch-indep`, `SE₀.reads-illegal`, `SEp.no-cmp-product`, `SEp.lex-needs`.
> 4. [NegThirdInst](NegThirdInst.lagda.md) (闭项 `TΛ`, 21:47 版): `TΛ-shape`, `cert-std`, `G.ΦX-acc`, `G.root-same`, `G.pick-keep`, `G.old-pk`, `G.old-const`, `Sa.san-noΩ`, `Sa.tp-bot`, `RW`, `rk-wdep`, `comp-rk`, `first-rk`.
> 5. [NegThirdTest](NegThirdTest.lagda.md): 有限测试, 不在入口的导入闭包里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegThird where

import OCF.Lean.NegThirdPre
import OCF.Lean.NegThirdIf
import OCF.Lean.NegThirdStamp
import OCF.Lean.NegThirdInst
```
