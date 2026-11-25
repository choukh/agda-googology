# KJ: 越过 BTBO 的第一步 (前缀 KJ, 工作目录 <实验目录>/m8)

先读公共约束: <实验目录>/briefs/COMMON.md . 注意: 这次的基目录是 <实验目录>/w10 (都已编译, 只读; 编译命令里的 `-i .../w4` 换成 `-i <实验目录>/w10`). 里面是原 W4 的整条链: W4Block, W4Ops, W4Path, W4Fold, WVOne, WVTwo, K 前缀的模块 (含你上次写的 KAsBase, KAsV3, KAsTw 与终点 KBtbo, 以及主审补的 KLow: `lowerW : LOWERᵂ` 已无前提), 另有 Audit2 (真实运行的追踪, 全是 refl).

## 背景

你上次证了 `KAsTw.Run.btboRun`: 对 tw 1 上任意覆盖的运行, 参照链 γ 的极限 BTBOᴵ 不高于输出. 那条链从 γ 0 = 1 起步, γ (n+1) = ψ⁰ (Ω (L n)). 现在 `LOWERᵂ` 已经无前提, 所以 `btbo-lower : tr₀ BTBO ≼ read EBOᶜ` 是无前提的定理 (KBtbo).
下一步要越过 BTBO. 观察: tw 1 上的运行里, 链的起点其实是状态在第 0 层的条目 β′ (`S zero (ink self)`), 不是 1. 若 β′ 的值已经不低于某棵树 x, 链就从 x 往上走: x, ψ⁰(Ω_x), ψ⁰(Ω_{ψ⁰(Ω_x)}), … 记它的极限为 J x ("z ↦ ψ⁰(Ω_z) 在 x 之上的下一个闭包点"). 取 x = BTBOᴵ 就越过了 BTBO.
塔第 2 项的真实运行里正有这样一个运行: `Ωt (tw 2)` 朝第 0 层走链, 第 0 个链点的那一项是 "在孩子 zero (层号就是 tw 1) 里折 Ωt (tw 1)", 状态是塔第 2 项的状态在孩子 zero 的条目, 其中第 0 层的条目来自 Λ 的前缀, 含有塔第 1 项从头折的值作尾巴 (回退行; Audit2 的 `Gen.fallback` 与 `member₂` 可作参考).

## 要交的 (分阶段, 每阶段整体编译)

1. Level 一侧 (与 W4 无关): 对 x : Ordᶜ zero 及它需要的证书 (照 `NoCumsum` 与 `BTBOFullLv` 里 γ 用到的: `HS`, `St` 一类; `SV-toLevel`, `Uniform` 等引理是对一般的树陈述的), 定义从 x 起步的链 δ 与它的极限 `J x`. 给出 x = BTBOᴵ 时的实例 (证书由已有引理给出), 并证 `suc BTBOᴵ ≼ J BTBOᴵ` 或至少 `BTBOᴵ ≼ J BTBOᴵ` 且第 1 项 ψ⁰(Ω (toLevel BTBOᴵ …)) 出现在其中.
2. W4 一侧: 推广 `Run`: 对 tw 1 上任意覆盖的运行, 若 `x ≼ read (proj₁ β′)` (β′ 是状态在第 0 层的条目, 即你的 `stepRun` 用的底), 则 `J x ≼ read (proj₁ out)`. 证法照搬 `embL` / `chainV`, 把 γ, L n 换成 δ 与它的层号码.
3. 接到闭项: 证 `J BTBOᴵ ≼ read EBOᶜ` (无模块参数; `lower` 用 `KLow.lowerW`). 路线建议: EBOᶜ 的第 2 个成员是塔第 2 项的运行 (Audit2 `member₂`); 它的结点行是走链, 输出不低于第 0 个链点的那一项; 那一项逐字是孩子 zero 里的一个运行 (层号 tw 1); 它的状态覆盖; 它的第 0 层条目的值不低于 BTBOᴵ (因为含 `twᶜ 1` 那样的尾巴, 而 `KBtbo.tw1-lower : BTBOᴵ ≼ read (twᶜ 1)`).
4. 若顺手: 对一切 n, 塔第 n+2 项不低于 J 迭代 n+1 次; 或说明为什么要另一条引理.

## 要点

- 定理要无前提. 做不完时把没证的部分写成带确切陈述的模块参数并报出.
- 第 3 项里涉及具体闭项, 陈述逐字写; 大的中间项用抽象的运行参数表述后再实例化; 遇到 251 先改形状.
- 回报里用一句话说明: J BTBOᴵ 这棵参照树按原记号大概是什么, 并标明是估计.
