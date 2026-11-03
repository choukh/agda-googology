# 证书与阶段无关: 对一切 $k$ 的地板塔 (判决: ALL k, 字面目标到不含 `limᴼ` 的层号; `limᴼ` 作低层 BLOCKED)

> 接 [InaccTheta](InaccTheta.lagda.md). 底座 [LevelKBase](LevelKBase.lagda.md), [LevelKEq](LevelKEq.lagda.md), [LevelKObs](LevelKObs.lagda.md), [LevelKOrd](LevelKOrd.lagda.md), [LevelKGood](LevelKGood.lagda.md), [LevelKClose](LevelKClose.lagda.md), [LevelKFin](LevelKFin.lagda.md), [LevelKTower](LevelKTower.lagda.md), [LevelKLvP](LevelKLvP.lagda.md), [LevelKWorld](LevelKWorld.lagda.md), [LevelKNeg](LevelKNeg.lagda.md), [LevelKOmega](LevelKOmega.lagda.md), [LevelKChain](LevelKChain.lagda.md). 全部不含记号, 模块级导入链只到 `OCF.BTBO`, `InaccTreeBase`, `InaccFloorTree` 与 `LevelK*`. 唯一的例外是 [LevelKCoexist](LevelKCoexist.lagda.md), 它导入旧定理作并排陈述, 不被任何文件导入.
>
> **判决. ALL k: $\forall K$, 目标 $K$ 的证书是一个定理, 不是逐层抄写.** 层号是好层号 (`LvP`) 时 `K-stage.Cert`. 这个定理对 $K$ **没有递归, 也没有分情况**: 它对任何满足 `Stage` 与 `IsK` 的阶段成立. 递归只在造地板 (`tower`), 那一步 (`Next`) 也不看阶段, 而且是层号值的. **非自然数目标: 覆盖 $\omega$, $\omega+1$ (编译过), 不覆盖 $\Omega+1$, $\Omega\cdot2$** (`reach-W` 要的那些). **它给的是层号的证书 `WFᴬ`, 不是 $\psi_0$ 输出的 `HS`**: 目标 0 在第 $K\ge1$ 阶段不是观测.
>
> **编译过的定理.**
>
> 1. **目标 2 (`Cert₂`, `A₁∋Ω₁`).** 第 1 层的地板实在, 含 $\Omega_1$. $\psi_2(\Omega_\theta)$ 有证书. 建议的设计成立: 第 $k$ 层地板是 "`toLv` $\approx$ 第 $k-1$ 阶段证书的层号 $L$ 的可容许字面前驱", 比较用 `<-decᴬ L` (`Next.A′`, `cmp′`). 观测目标必须有全部低层的字面路径 (`Zt`).
> 2. **`Eq` 传递性不需要.** [InaccTheta](InaccTheta.lagda.md) 估计 `toLv x ⊑ᴬ toLv y → x ⊑ᵒ y` 要它. `mono-lv` 不要: 相等的部分走 `T→E`, 只用 `≈ᴮ` 的传递性加分支尊重 `Rp`. 异层 `Eq` 的传递性没有证, 它要在 $j\approx j'$ 之间搬输入; 这里绕开了.
> 3. **循环断开 (`Good-floor`, `PE`).** 地板 `A` 的定义不提 `Good`, `Eq`, 观测, 只提层号: `Cx = WFᴬ × Rp × Mn` ([LevelKBase](LevelKBase.lagda.md) §3). `Eq` 的分支前提多一支 "低层, 字面同层, 层号 $\approx$" (`PE`), 所以低层上的相等不回到 `Eq`. `Good-floor` 是定理: 层号好的树是好树. 依赖链 `Good → ⊑ᵒ → Eq → Bs → A` 在 `A` 处终止. 不是归纳-递归: 阶段是普通的记录, 对 $K$ 递归时只用单步搬运 (`Move`).
> 4. **全部 $k$ (`Cert∀`, `Cert∀ₙ`, `tower`).** `Cert∀ₙ`: $\psi_K(\Omega_n)$ 对一切 $K,n$, 任何 `S`, 任何世界选择, 无条件. 世界可以很丰富: 第 0 层任何 $\ell\ge\omega$ (`W-ℓ`), 第 $K$ 层取 $\psi_K(\Omega_\theta)+1$, 对任何好层号 $\theta$ (`W-F`, `chooseF`, `w₀∈`).
> 5. **`limᴼ` 作下标 (`Cert-Ω₂`, `Cert-ΩΩ∀`, `lvp-Ω`).** $\psi_K(\Omega_{\Omega_m})$ ($m\le K$) 有证书, **对任何 `S`, 没有 `HE`**, 在最小世界 (`canon`, 第 0 层 $\omega$) 里. 丰富世界里相对于地板上的判决正确 (`HE.Cert-ΩHE`): `HE` 只问地板.
> 6. **与 `no-Ω₂` 共存 (`Both.old`, `Both.new`, `no-Ω₂′`, `Co.¬full`).** 改变的前提恰好一个: **第 1 层的分支从全称 (`Bs 1 = ⊤`) 改成在地板里.** 所以 `no-Ω₂′`: `LvG (toLv Ω₂)` 加 "第 1 层的 `Bs` 含全部 `up tt (em a)`" 推出 WLPO; `new`: 塔的地板上 `LvG (toLv Ω₂)` 是定理; `¬full`: 塔的地板含全部那些元就是 WLPO.
> 7. **字面目标 (`Top.Cert-top`).** 任何阶段, 任何 `BL L` 的目标, 任何合法模式, 一个定理. 实例: $\psi_\omega(\Omega_n)$ (`Cert-ωₙ`), $\psi_\omega(\Omega_{\omega+1})$ (`Cert-ω₊`, 节点 $L$ 上升, 链的目标是 $L$ 自己), $\psi_{\omega+1}(\Omega_{\omega+2})$ (`Cert-ω₁`, 世界 $\ell=\omega+2$). `S` 都没有被问到. 塔在 $\omega$ 处取并 (`Union.Stω`), 地板对读它的阶段无关 (`extω`).
> 8. **目标 $k$ 的链 ([LevelKChain](LevelKChain.lagda.md)).** `y-cert`, `y-step`: [EBOTopRaw](EBOTopRaw.lagda.md) 的 `Must.chk` (`chk≡y`) 上每一点好, 层号好, 相邻步进, 相对于链上的 `he`. 这是 `must` 的层号版, 不是 `must` 本身.
>
> **编译过的否定.**
>
> - `¬both-low`, `Sep1.¬both-low`: 两个 `limᴼ 0 _` 同作低层, 在真子集的地板上就与 `low-≈` 矛盾. 两个分支族在地板上一致, 在外面不同.
> - `ω-low→ext`: $\omega$, $\omega'$ 同作低层给函数外延性的实例.
> - `¬lowΩ₁`: `Stage` 的低层不含 `limᴼ`, 所以 $\Omega+1$, $\Omega\cdot2$ 不是这个 `Stage` 的目标.
> - `¬Zt₀`: 第 $K\ge1$ 阶段目标 0 不合法.
> - `no-Ω₂′`, `¬full`: 上面.
> - `¬Reg-floor`: 地板不能同时含 $\omega_0+1$, $\omega_1+1$.
>
> **第一个障碍, 精确位置.** `Lv` 的 `o≈` 要两侧参数层**字面相同**, `b≃` 的节点情形因此要 `low-≈`. 自然数与单个 $\omega$ 满足它. 含 `limᴼ` 的低层不满足 (`¬both-low`). 丰富的世界里同一节点两个相似输入的层号就是这种对 (判断, 没有在塔的树上构造反例). 所以 `reach-W` 的目标 $\Omega+1$, $\Omega\cdot2$ 要低层含 $\Omega_1$ 的层号, 在这里过不去.
>
> **没有做的第二个设计 (判断, 未编译).** 让 $\approx$ 也分阶段: 第 $K+1$ 阶段的 `o≈` 两侧参数层只要 $\approx$, 前提是上一阶段的 $\approx$ 作参数, 这样数据类型严格正. 它要的是: 地板对 $\approx$ 跨层封闭, 沿 $j\approx j'$ 的树的搬运 (形如 `InaccTreeBase.tr`, 但只在 `Bs` 上), 再证 $\approx$ 的传递性. 这里的两条否定不挡它. 我没有写, 所以不能说它成立.
>
> **对终局 ([EBOTop](EBOTop.lagda.md)) 还差什么 (判断).** `must` 要的是 $\psi_0(\Omega_{\text{链点}})$ 的 `HS`. 那里目标 0 上第 1 层节点上升, 链点要在第 1 层的 `Bs` 里. 而这里第 $K\ge1$ 阶段把低层节点一律当穿透. 所以这个定理是层号的证书, 不直接给 `Family`. 接口: `Stage`, `Next`, `tower`, `K-stage.Cert`, `Top.Cert-top`, `cx-tree`, `lvp-cx`, `Worlds.WF.W-F`, `Chain.WithHE`.
>
> **壁垒对照.**
>
> | 东西 | 要有向性或三歧吗 | `dec-A→WLPO` | `¬WF-Reg` | `dir-dec` |
> |---|---|---|---|---|
> | 第 $m$ 层地板 $A_m$ | 要有向性; 只来自单个 $L_m$ 的 `<-decᴬ` (`cmpA`), 有界, 字面上界 | 不适用: 折叠 `ψᵖ` 不读 `A`, 成员资格是证据 | `¬Reg-floor`: 地板不是全部规整的树 | 同一现象的正面: 单个上界之下比较可判定, 没有新假设 |
> | 高层 (非低) | 不要. `A = ⊥`, 只走链 | 不适用 | 不适用 | 不适用 |
> | 全局三歧, 全分支比较 | 不要 | | | |
>
> `bounded`: 新地板都严格低于 $L$, 不是 `Ordᴰ` 的精确初始段, 所以 [Barrier](../Barrier.lagda.md) 的前提不成立 (判断, 那个前提的形式对比没有编译). `S` 的正确性没有被要求全局: `Cert∀ₙ`, `Cert-Ω₂`, `Cert-ω₁` 对任何 `S`.
>
> **有限测试.** 没有. 上面都是编译过的定理或标明的判断. 本文没有验收, 不说任何强度.
>
> 全文 `--safe --without-K` (`LevelKBase`, `LevelKEq` 加 `--lossy-unification`), 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelK where

open import OCF.Align.LevelKBase using (Fl; Stage; Ext; module Leaf; module Move)
open import OCF.Align.LevelKFin using (IsK; module Fin)
open import OCF.Align.LevelKTower using
  (St₀; NewLevel; World; WorldK; module Next; module Step; module Worlds; Tw; Choice; tower; canon; chooseF; W-ω; module AtK; Cert∀; Cert∀ₙ; Cert₂; A₁∋Ω₁)
open import OCF.Align.LevelKLvP using (module LvPs)
open import OCF.Align.LevelKWorld using (W-ℓ)
open import OCF.Align.LevelKNeg using
  (module NegK; module Canon; Cert-Ω₂; Cert-ΩΩ∀; module Co; ¬Reg-floor; bounded; module HE; ω-low→ext; module SepO; module Sep1)
open import OCF.Align.LevelKOmega using (module Top; module Union; module Lω; module Lω₁; module Pω-ℓ)
open import OCF.Align.LevelKChain using (module Chain; module NoTop)
```
