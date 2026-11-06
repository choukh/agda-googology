# X₁ 上叠层: 否定一路 (入口)

> 不含记号. 与构造一路 `X1Up` 配对 (作者本轮选定 "C 线继续: X₁ 上叠层"; 构造一路从 [PathOut](PathOut.lagda.md) 出发, 在 $X_1$ 上叠 `ls`/`ll` 写上层折叠, 留下 $X_1$ 的种类, 目标读法越过 ψ₀(Ω_Ω)). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延只在标 "条件" 的定理里作前提 (本路目前没有).
>
> **接口定稿之前的部分 (不依赖接口).**
>
> 1. [NegX1UpEmb](NegX1UpEmb.lagda.md): 叠层 `ofU x` ($X_1\oplus x$) 的种类分类 `cls` 与底种类的代表 `embB`. 命题等式 (`cls-emb`, `E-base`, `lvl-emb`, `ev-emb`) 对一切 $x$ 成立; 搬运不经 `subst`, 按 $x$ 递归定义, 往返恒等 (`outB`, `inB`, `out-in`, `in-out`, `evMove`). "对变量层号不是 refl" 是元层事实, 不写成对象层定理; PathOut 判断的 "卡点" 由这些构造化为工程量 (判断, 要构造一路的折叠确认). ℕ-极限偏移里底种类有可数多个代表 (`copies-ll`, `emb-not-unique`).
> 2. [NegX1UpCmp](NegX1UpCmp.lagda.md): 叠层后的比较. 底种类严格在 $X_1$ 之下 (`base⊏U`), 以叠层为目标时 "留" 精确且不要证据 (`exact-keep-base`); 底种类与新种类字面可比 (`base⊏new`); 新种类之间以折叠的层号为公共上界 (`cmp-new`), 没有它时不可比 (`incomp-new`); 叠层上底种类对可数目标没有精确决定 (`no-exact-up`); 叠层不在可数层号之下 (`U-not-cnt`).
> 3. [NegX1UpFlat](NegX1UpFlat.lagda.md): 累加不是塌缩点; 塌缩点是同层链的起点. 折叠保 "不含 $\Omega$-结点" (`Φ-noΩ`, `Ψ-noΩ`, 对一切实例); 同层的链从界 $0$ 起步, 分支 `up` 形时这一步的输出不含结点 (`same-noΩ`, `flat-at-X₁`; 前提实例 `flat-ICd`).
> 4. [NegX1UpPay](NegX1UpPay.lagda.md): `correct` 不管读回 (PathOut 接手清单第 4 条): 读回换常值仍是实例 (`constPayOf`), 闭项公式仍有 `LgB` 证书 (`LgB-TXLk`).
> 5. [NegX1UpPH](NegX1UpPH.lagda.md): `PH` 对世界单调 (`PH-mono`), 对 $\boxplus$, `mul`, `Σ⁺`, `chain` 封闭 (`PH-⊞` 不再要 "不含 $\Omega_1$"); 第 0 世界的根部只容第 1 层的种类 (`ph-root`, 反例 `¬PH-bad₂`).
>
> **接口定稿之后的部分** (接口 [X1UpIf](X1UpIf.lagda.md), "接口定稿 2026-11-05 23:45"; 只读导入).
>
> 6. [NegX1UpIf](NegX1UpIf.lagda.md): 盲: 地板换成不含结点的树仍是实例 (`flatTopOf`, `hzTopOf`; 由 `noΩ→PH`), 证据恒空也是实例 (`voidX1`). 边界 (对 `IX₁`): 合法的值 `cJ` 在一切合法世界里不带路径 (`no-world-cJ`), 在不合法的世界里带路径且这样的世界在一切世界之上 (`kripke-cJ`, `¬Lg-Bj`).
> 7. [NegX1UpLeg](NegX1UpLeg.lagda.md): 接口文首判断 "`leg` 不单调" 的编译反例: 合法的 $c_1\lhd c'$, $\mathrm{leg}\,c_1
ot\lhd\mathrm{leg}\,c'$ (`leg-not-mono`).
> 8. [NegX1UpInst](NegX1UpInst.lagda.md): 对构造一路的实例 `IU` 与折叠 `ΦU` ([X1UpFold](X1UpFold.lagda.md), [X1Up](X1Up.lagda.md) 只读导入). 正面: `TU1` 的中间值 (第 $X_1$ 层) 第 0 个链点的根是 $\Omega_1$-结点 (`root-Ω₁`, refl), 底种类一律留 (`keep-base`). 盲: `OkU` 对底种类的 "留" 是 $\top$ (`OkU-bas-blind`). 否定: 上层折叠不单调 (`ΦU-not-mono`, 对一切 `U`); 合法输入 `inΩ` 折到 $X_1$ 层后留下的 $\Omega_1$-结点不满足 `LgB` (`kept-not-LgB-U`). 地板换成 $0$ 的实例上同一公式不含结点 (`Flat0.flat-U1`).
>
> **只否定什么 (汇总).** 见各篇文件头. 没有一条否定构造一路的 `PH-ΦU`, `PH-ΦX`, `okU`, 闭项 `TU m`, `TU2` 与它们的 `LgB` 证书; 没有值的定理. 本路没有关闭任何路线.
>
> **对纲领与目标 (判断, 依据上面的定理).** 纲领 1, 2: 闭项是布劳威尔树上的合法项, 证书靠形状 (`Sh-Ψ`), 中间层不满足树自己的 `LgB` (8, 同 TySup, PathOut 的情形). 让树自足: 叠层后的比较分三种对 (2), 只有 (底种类, 可数目标) 一种要世界与证据, 其余字面可比; 这一条是树侧的判据, 不读记号. 盲区: 接口不保证地板有结点 (6), `correct`/`OkU` 不管读回与底种类的层号 (4, 8); 防塌缩靠实例的选择 (`topL`), 不靠律. 读法: `TU1` 读 ψ₀(Ω_{Ω_1+1}), `TU2` 读 ψ₀(Ω_{Ω_1·2}), 越过 ψ₀(Ω_{Ω_1}) 是判断, 字面依据是中间值里留下了 $\Omega_1$-结点 (`root-Ω₁`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegX1Up where

import OCF.Align.NegX1UpEmb
import OCF.Align.NegX1UpCmp
import OCF.Align.NegX1UpFlat
import OCF.Align.NegX1UpPay
import OCF.Align.NegX1UpPH
import OCF.Align.NegX1UpIf
import OCF.Align.NegX1UpLeg
import OCF.Align.NegX1UpInst
```
