# 高度取序数: 累加世界的闭包定理到 $\Omega^2$ 之上

> **判决: HOLDS (合法性; 读法都是判断, 大小不在这一路).** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. **`HS` 不说明大小**, 见 §4 的对照. 记号只在 [CumHtAccept](CumHtAccept.lagda.md), 全是有限测试.
>
> **怎么换高度.** 层是 $(r,p,a)$, $r:\mathbb N$, $p,a:A$. 读法 (判断) $\Omega_{\Omega^2\cdot r+\Omega\cdot p+a}$. **$p$ 位不是 `Pos`, 就是 `A`, 活在世界里:** 目标与项的 $p$ 位都进 `mx`, 比较 `cmpH` 在世界 $m$ 之下, 字面公共上界就是 $m$. 码 $M$ 不进定义, 只提供合法的世界 (`gW`) 和第一位置 (`rk⊲`). 这样 `CumUp` 绕开 `no-⊞-left` 的办法对高度原样有效.
>
> | 定理 | 陈述 | 文件 |
> |---|---|---|
> | `HS-T` | 对任何 `𝓝 : Nx`, 一切 $H=\langle r,p\rangle$, $a$, 世界 $u_0$ (`Gw`), $p,a\lhd u_0$: `HS (Tψ H a u₀ g e)` | [CumHtMain](CumHtMain.lagda.md) |
> | `ψL′`, `ψ₀L′`, `ψW`, `ψ₀W` | 折叠保第一位置, 保 `WF`, 对项递归, 不按高度分情况 | 同上 |
> | `T-mono`, `T-monoᴾ`, `T-monoᴿ` | $a$ 位, $p$ 位的字面第一位置给 `⊑⁰`; $(r,0,0)\sqsubseteq^0(r+1,0,0)$ | 同上 |
> | `T-world` | 同一层在两个世界上算出的树 $\cong$. 上移 `up` 的对应物是世界的 `ow` | 同上 |
> | `cmpH`, `no-<≈`, `clashᴴ` | 世界之下高度三歧, 相等是字面的; 与等价相撞 | [CumHtBase](CumHtBase.lagda.md) |
> | `ψQ` | 目标与项模等价相同, 输出模等价相同 | [CumHtPsi](CumHtPsi.lagda.md) |
> | `HSᵖ`, `HSᴹ`, `mono-pos` | 对一切码 $M$, 位置 $p$, $r$: `HS`, 位置单调 | 本文 §1 |
> | `HS-Tω`, `HS-Tω·2`, `HS-Tω²`, `HS-Tω^ω`, `HS-Tε₀` | 闭项 (累加实例) | 本文 §3 |
> | `HS-T²`, `HS-T²⁺¹`, `HS-T²⁺`, `HS-Tᵍ`, `HS-T²ω`, `T²⊑T²⁺¹` | $(r+1,0,0)$, $(1,0,1)$, $(r+1,0,a)$, 一般的 $(r,p,a)$, 上确界 | 本文 §1 |
> | `T²-≅`, `T²⁰`, `T²-term`, `η²-step`, `η²-eq` | $(r+1,0,0)$ 模 $\cong$ 是链的极限, 第 $n+1$ 项 $\cong\langle r,\eta_n\rangle$ 的第 0 位, $\eta_n\lhd\eta_{n+1}=$ `nxt` | [CumHtShape](CumHtShape.lagda.md) |
> | `T²⁺¹-≅`, `T²⁺¹⁰` | $(1,0,1)$ 模 $\cong$ 是 $\lim\psi_0(z_n)$, $z_0=\dot\Omega$, $z_{n+1}=\psi_{(1,0,0)}(z_n)$ | 同上 |
> | `HS-Nxˢ`, `ηˢ` | 对照: 不读输出的链也 `HS`, 高度链只是 $2,3,4,\dots$ | 本文 §4 |
>
> **条件定理.** `HS-T` 与上面所有 `CumHtMain`, `CumHtPsi`, `CumHtShape` 的定理都以 `𝓝 : Nx` 为模块参数. 实例 `𝓝ᶜ` (累加, [CumHtCum](CumHtCum.lagda.md)), `𝓝ˢ` (对照) 都闭合, 所以闭项无条件.
>
> **有限测试 (不是证明).** [CumHtTest](CumHtTest.lagda.md), [CumHtAccept](CumHtAccept.lagda.md), 比较器 `refl`, 形状指纹深度 $d$ 宽度 $w$. 盲区: 只看前几项前几层; FGH 只算了参数 0, 值全是 1, 不区分任何树; 参数 1 的 `refl` 没有算完 (18 秒, 45 秒, 计时观察). 累加与对照到深度 5 相同, 深度 6 分开; $r=0$, $p$ 有限时与 `CumUp` 到深度 7 相同; 与带标签的 `OCF.Free` 树到深度 4 相同; 与 `T⊤` 到深度 3 相同, 深度 4 不同.
>
> ## 累加的依赖范围
>
> **由编译器保证:** `CumHtMain`, `CumHtShape` 的导入闭包不含 `CumReadBase`. 闭包定理只看 `Nx` 四个字段: 下一个下标字面在上 (`nxt-⊲`), 保合法 (`nxt-L`), 保等价 (`nxt-≈`). 定义里 `nxt` 只出现在 `CumHtW.step` 和它的证据 `gnext`, 经 `ψ₀⁰` 的 `oc` 行 (第 0 层闭包) 进折叠.
>
> | 只依赖 $(r,p,a)$ 世界 | 依赖 `Nx` | 依赖累加 |
> |---|---|---|
> | `CumHtBase`, `Tree`, `Eq`, `Le`; `oc` 的分支, `ow`, `mx`, `cmpH`, 非 0 目标上的 `ψ` | `CumHtW` 的第 0 层闭包, `Psi`, `Main`, `Shape` 经它依赖 | 只有 `CumHtCum`: `next`, `cumA`, `⊞` |
>
> `HS-Nxˢ` 说 `HS` 不需要累加. **需不需要累加来得到大小, 这里没有回答**, 那是 `NoCum`, `CumVal` 的问题. 累加实例的毛刺 (`CumUp` 的账) 全部保留. 码的读法 `cA` 的累积和是 `Code` 自带的, 与这个无关, 闭包定理不用它.
>
> ## 对 `CrossM` 的回答 (判断, 依据是编译结果)
>
> **累加世界的路线在这一站容易得多, 就合法性而言.** [CrossM](CrossM.lagda.md) 的三个障碍这里都没有出现: (a) 没有另一个折叠 `ψ̄ᵀ` 要与世界内对齐, $\Omega^2$ 是同一个构造子 `oc`, 同一个 `ψ`, `ψ₀`; (b) 链上单调性: 分支对一切世界给出, 相邻两支由 $\dot\Omega$ 在 $p$ 位的单调 `ΩH⊴` 给, 链字面递增由 `Nx` 给; (c) 闭包定理 `HS-T` 一条过 $\Omega^2$, $\Omega^2+1$, 7 个文件 2750 行, 其中比 `CumUp` 的 2160 行多的约 590 行, 不是 `CrossM` 估计的 "约 1 万行全部带地板". **代价:** 没有与 `T⊤` 的定理 (有限测试深度 4 就不同), 没有标签, 毛刺在 `Nx` 的实例里. `CrossM` 的 `Fix`, `val≼T` 这样关于值的定理这里一条也没有.
>
> ## 读法 (判断, 不是定理)
>
> `Tᴹ 0 M`: $\psi_0(\Omega_{\Omega\cdot M})$. `T² 0`: $\psi_0(\Omega_{\Omega^2})$, 与 `T⊤` 同形 (`T²-term`), 依据只是形状. `T²⁺¹`: $\psi_0(\Omega_{\Omega^2+1})$, 第 1 项的形状 $\psi_0(\psi_{\Omega^2}(\Omega_{\Omega^2}))$ 与记号的 `fs-ψΩ1-1` 同形. `T²ω`: $\psi_0(\Omega_{\Omega^2\cdot\omega})$, 这是这一路的上确界 (判断). 高度超过闭包点时读法不成立的问题 (`CrossM` 的 "读法在闭包点之上不成立") 这里同样存在, 没有分析.
>
> ## 壁垒
>
> 对照 `Barrier.Ω-Extension`: 没有实例. `<ᴵ-dec` 要求任意下标上界下的三歧; `cmpH`, `cmpN` 要的是字面世界 $m$, `Lg m`, 两边都是 $m$ 的第一位置, 上界是下标不够. $\Omega^2$ 没有 Ω-共尾元作可数层的构造子: 它是 `oc` 对世界的绑定, 第 0 层读成链的 $\mathbb N$-极限. 全局比较不用 (`no-tri-code`, `no-all-Ord` 否定的那个). 证明里没有一处跨世界比较高度.
>
> ## 受记号影响的形状 (如实说)
>
> 这不是 "树自足". 三位 $(r,p,a)$ 照着 $\Omega^2\cdot r+\Omega\cdot p+a$ 写, $\dot\Omega$ 的六种情形 (`Ω̇′`) 照着基本列写. 与 `CumUp` 同样的还有: 根层, 闭包, 链, `rep`. 比较 `cmpH` 的字典序也读自那个读法. 定义和证书不读记号是审计的结论, 不说明没受启发.
>
> ## 第一个障碍
>
> **这一路的上限是 $r:\mathbb N$.** $\Omega^3$ 要 $r$ 也进世界, 判断: 同样的手法 (`D⊲` 三位). 一般的位数要对位数做类型层递归, 没有试. **未走通, 不是否定.** 工程上遇到的, 都解决了, 记在这里免得重走:
>
> - **`--without-K` 下类型头卡住的参数不参与终止检查.** `CumUp` 的 `addL` 靠隐式的 $p$ 下降过关. $r$ 位下降时 $p$ 位自由, 字面的 $\langle s,p'\rangle$ 比不过 $\langle s+1,p\rangle$, 报 `[TerminationIssue]` `Termination checking failed for the following functions: add, add⁰, addL`. 解法: 盒子 `Bx`, 让参数的类型头是数据.
> - 同样的原因, `≈`, `WF` 要按 $(r,p,a)$ 三个分开的参数字典序递归 (`_≈′_`, `WF′`), 外面包一层别名.
> - `M₂` 必须是数据: 是记录时 `mx` 不等比较就展开, `with` 抽象不到, 报 `[UnequalTerms] m != (mx₂ …)`.
> - 闭项上的 `refl` 让转换检查展开整棵树, 5 分钟没有结果 (计时观察). `CumHtShape` 对 $r$ 与世界抽象, 对 `val` 抽象.
>
> ## 没有做的
>
> 大小 (`CumVal`); 去掉累加 (`NoCum`); 与 `CumUp`, `T⊤` 之间的定理 (只有有限测试); 单个 `Tᴹ` 在 $M\subset M'$ 之外的跨码单调 (`T-monoᴾ` 只要求字面第一位置); `T²` 高于一切 `Tᴹ` (没有定理, 判断: 字面的 $\sqsubseteq^0$ 不成立, 只有互相共尾那一类的值定理才有希望).
>
> ## 审计
>
> - **导入闭包:** `importclosure.py OCF.Align.CumHtMain OCF.Align.CumHtShape OCF.Align.CumHt`: 禁用表命中 0. `CumHtMain` 本地模块只有 `CumHtBase`, `Eq`, `Le`, `Main`, `Psi`, `Tree`, `W`, `CumReadCF`, `OCF.BTBO`, `OCF.Free.Level`.
> - **定义级切片 `depslice.py`:** `CumHtW:ψ₀` 136 块, `CumHtMain:HS-T` 366, `CumHtShape:T²-term` 257, `CumHt:HS-T²⁺¹` 388, `CumHt:fgh²⁺¹` 146, `CumHt:Tε₀` 417, `CumHtCum:𝓝ᶜ` 47; 记号 0, 词命中 0. **正对照:** `CrossMAccept:fs-ψΩ` 51 块, 记号 43, 词命中 3. 切片是语法级的; 闭包是编译器保证的, 但不说明定义没有受记号启发.
>
> ## 导航
>
> | 文件 | 内容 |
> |---|---|
> | [CumHtBase](CumHtBase.lagda.md) | 下标等价, 世界, 高度, 路径, `cmpH`, 接口 `Nx` |
> | [CumHtTree](CumHtTree.lagda.md) | 数据树, $\dot\Omega$, `mx`, 加法 |
> | [CumHtEq](CumHtEq.lagda.md) | `≈`, `add≈`, `rep≈` |
> | [CumHtW](CumHtW.lagda.md) | 折叠, 闭项 `Tψ` (参数 `Nx`) |
> | [CumHtPsi](CumHtPsi.lagda.md) | `ψQ` |
> | [CumHtLe](CumHtLe.lagda.md) | `⊴`, 加法 |
> | [CumHtMain](CumHtMain.lagda.md) | 闭包定理 `HS-T` |
> | [CumHtShape](CumHtShape.lagda.md) | $\Omega^2$, $\Omega^2+1$ 的展开 |
> | [CumHtCode](CumHtCode.lagda.md) | 码与位置进世界 |
> | [CumHtCum](CumHtCum.lagda.md) | 累加实例 |
> | [CumHtTest](CumHtTest.lagda.md) | 有限测试 |
> | [CumHtAccept](CumHtAccept.lagda.md) | 对 `CumUp`, `OCF.Free`, `LadderOrd`, `CrossM` 的有限对照 |


```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHt where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level using (HS; hl; _⊑⁰_; _≅_; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.LadderOrdPos using (Code; Pos; end)
import OCF.Align.LadderOrdPos as LP
open import OCF.Align.LadderOrdCode using (ωᶜ; ω·ᶜ; ω²ᶜ; ω^ωᶜ; ε₀ᶜ)
open import OCF.Align.CumHtBase
open import OCF.Align.CumHtTree
open import OCF.Align.CumHtEq
open import OCF.Align.CumHtCode
open import OCF.Align.CumHtCum using (𝓝ᶜ)
import OCF.Align.CumHtW as W′
import OCF.Align.CumHtMain as M′
import OCF.Align.CumHtShape as S′
```

## §1 对任何 `Nx`: 实例

**同一条定理 `HS-T`, 不按高度定制.** 下面只是把参数代进去.

```agda
module Inst (𝓝 : Nx) where
  open W′ 𝓝 public using (Tψ)
  open S′ 𝓝 public using (H²; T²; T²⁺¹; T²-≅; T²⁺¹-≅; module Ω²; module Ω²⁺¹; module Chain)
  open M′ 𝓝 public using (HS-T; T-mono; T-monoᴾ; T-monoᴿ; T-world)
  open Nx 𝓝

  -- 一切码 M, 一切位置 p, r 位任意
  Tᵖ : ℕ → (M : Code) → Pos (LP.cs M) → Ord₀
  Tᵖ r M p = Tψ ⟨ r , rkA azero p ⟩ azero (W M) (gW M) (e⊲W M p)

  HSᵖ : ∀ r M p → HS (Tᵖ r M p)
  HSᵖ r M p = HS-T _ _ _ (gW M) (e⊲W M p)

  -- 码的顶: 读法 ψ₀(Ω_{Ω²·r + Ω·M})
  Tᴹ : ℕ → Code → Ord₀
  Tᴹ r M = Tᵖ r M end

  HSᴹ : ∀ r M → HS (Tᴹ r M)
  HSᴹ r M = HSᵖ r M end

  -- 同一码之内, 位置的字面第一位置给 ⊑⁰
  mono-pos : ∀ r M (p q : Pos (LP.cs M)) → rkA azero p ⊲ rkA azero q → Tᵖ r M p ⊑⁰ Tᵖ r M q
  mono-pos r M p q d = T-monoᴾ r (gW M) (gW M) (e⊲W M p) (e⊲W M q) d

  -- Ω²·(r+1)
  HS-T² : ∀ r → HS (T² r)
  HS-T² r = HS-T (H² r) azero one g₀ (Dz one)

  -- Ω²+1
  HS-T²⁺¹ : HS T²⁺¹
  HS-T²⁺¹ = HS-T (H² 0) one one g₀ (z⊲ one ,ᵈ C.self)

  -- 第一位置给 ⊑⁰
  T²⊑T²⁺¹ : T² 0 ⊑⁰ T²⁺¹
  T²⊑T²⁺¹ = T-mono (H² 0) g₀ g₀ (Dz one) (z⊲ one ,ᵈ C.self) (z⊲ one)

  -- Ω²·(r+1) + a, 对一切合法的 a
  T²⁺ : ℕ → (a : A) → Gw a → Ord₀
  T²⁺ r a g = Tψ (H² r) a a g (z⊲ a ,ᵈ C.self)

  HS-T²⁺ : ∀ r a (g : Gw a) → HS (T²⁺ r a g)
  HS-T²⁺ r a g = HS-T (H² r) a a g (z⊲ a ,ᵈ C.self)

  -- Ω²·r + Ω·p + a, 一般的层: 只要一个世界
  Tᵍ : ∀ r p a u → Gw u → D⊲ p a u → Ord₀
  Tᵍ r p a u g e = Tψ ⟨ r , p ⟩ a u g e

  HS-Tᵍ : ∀ r p a u (g : Gw u) (e : D⊲ p a u) → HS (Tᵍ r p a u g e)
  HS-Tᵍ r p a u g e = HS-T ⟨ r , p ⟩ a u g e

  -- 上确界: Ω²·ω
  T²ω : Ord₀
  T²ω = FL.lim T²

  HS-T²ω : HS T²ω
  HS-T²ω = hl HS-T² (λ r → T-monoᴿ (suc r) g₀ g₀ (Dz one) (Dz one))
```

## §3 累加的实例

```agda
module Cum = Inst 𝓝ᶜ

fgh² : ℕ → ℕ
fgh² = FGH (Cum.T² 0)

fgh²⁺¹ : ℕ → ℕ
fgh²⁺¹ = FGH Cum.T²⁺¹

fgh²ω : ℕ → ℕ
fgh²ω = FGH Cum.T²ω

Tω : Ord₀
Tω = Cum.Tᴹ 0 ωᶜ

Tω·2 : Ord₀
Tω·2 = Cum.Tᴹ 0 (ω·ᶜ 1)

Tω² : Ord₀
Tω² = Cum.Tᴹ 0 ω²ᶜ

Tω^ω : Ord₀
Tω^ω = Cum.Tᴹ 0 ω^ωᶜ

Tε₀ : Ord₀
Tε₀ = Cum.Tᴹ 0 ε₀ᶜ

HS-Tω : HS Tω
HS-Tω = Cum.HSᴹ 0 ωᶜ

HS-Tω·2 : HS Tω·2
HS-Tω·2 = Cum.HSᴹ 0 (ω·ᶜ 1)

HS-Tω² : HS Tω²
HS-Tω² = Cum.HSᴹ 0 ω²ᶜ

HS-Tω^ω : HS Tω^ω
HS-Tω^ω = Cum.HSᴹ 0 ω^ωᶜ

HS-Tε₀ : HS Tε₀
HS-Tε₀ = Cum.HSᴹ 0 ε₀ᶜ
```

## §4 对照: 同一条闭包定理, 不读输出的链

`𝓝ˢ`: 下一个下标是上一个加一, 不读输出. **`HS` 照样成立** (`HS-Nxˢ`). 这棵 "$\Omega^2$" 的高度链只是 $2,3,4,\dots$ (`ηˢ`, 定理), 所以它的第 $n+1$ 项是有限高度的第 0 行 (`T²-term`), 读法到不了 $\psi_0(\Omega_{\Omega^2})$ (判断, 大概是 $\psi_0(\Omega_{\Omega\cdot\omega})$). **这就是 "`HS` 不说明大小" 的编译过的实例**: 合法性对链的内容没有要求, 只要字面递增.

```agda
𝓝ˢ : Nx
𝓝ˢ = record { nxt = λ η _ → asuc η ; nxt-⊲ = λ η y → C.suc C.self ; nxt-L = λ η y w → w ; nxt-≈ = λ e d → s≈ e }

module Ctl = Inst 𝓝ˢ

HS-Nxˢ : HS (Ctl.T² 0)
HS-Nxˢ = Ctl.HS-T² 0

natA : ℕ → A
natA zero = azero
natA (suc n) = asuc (natA n)

ηˢ : ∀ n → Ctl.Ω².η² 0 g₀ (Dz one) n ≡ natA (suc (suc n))
ηˢ zero = refl
ηˢ (suc n) = cong asuc (ηˢ n)
```
