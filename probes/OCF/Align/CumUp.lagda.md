# 带闭包的层: 高度世界

> **判决: HOLDS (三个目标), 强度的档次见下.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 这里不含记号, 账和验收在 `CumUpAccept*`.
>
> **目标 1, 序数值验收 (互相 $\preccurlyeq$).** `CumUpAcceptVal.Tᶜ≈ : fr Tᶜ ≈ᵛ BTBOᴵ`. 上一轮的 $T^c$ 与通过基本列验收的 $\psi_0(\Omega_\Omega)$ 序数值相等. 不是基本列验收, 不是前驱结构验收.
>
> **目标 3.** `CumUpMain.HS-T`: 对一切 $p$, 一切合法的 $a$ (`a ⊲ u₀`, `Gw u₀`), $\psi_0(\Omega_{\Omega\cdot p+a})$ 这棵树是 `HS` 序数. 同一条闭包定理 (`ψW`, `ψ₀W`), 对项递归, 不按 $p$, $a$ 分情况. 上确界 `TΩ·ω`, $\psi_0(\Omega_{\Omega\cdot\omega})$, 也 `HS`. **这些站的强度只有有限测试** (`CumUpAcceptF`), 不是定理: $\Omega+1$, $\Omega+2$, $\Omega\cdot 2$ 处序数值未证, 写成估计.
>
> **怎么绕开 `no-⊞-left`.** 定理本身不变 ($c\triangleleft a$ 推不出 $b+c\triangleleft b+a$). 上一轮卡在目标路径上的 $\tau$ 随路径变, 同一个闭包在两处算出的链不可比. 这里层是一对 $(p,a)$, 目标 $(q,t)$ 的 $t$ 自己就是世界的下界, 没有路径, 输出的世界是 $\max(u,t,a)$, 只看项与目标 (`mx`, `add` 让 $W$ 留在自己的世界). 比较模 $\approx^A$ (`ψQ`), 因为链点只有模 $\approx$ 相同.
>
> ## 更正上一轮
>
> 上一轮的报告说闭包定理 "第一次不问输出高于下标". **这句话是错的**: `Uniform` 早就对一切下标给 `HS`, 不累加的树 `BTBOᴵ` 也早就有. 在 $\psi_0(\Omega_\Omega)$ 这一站, 累加不是得到 `HS` 所必需的. `CumRead*` 已复核不改, 更正写在这里.
>
> ## 累加的账, 两边
>
> **累加改不改值.** $\psi_0(\Omega_\Omega)$ 这一站, 树的序数值不改 (`Tᶜ≈`, 定理). 逐项看改: 第 $k$ 项 $\gamma_{k+1}\preccurlyeq y_k$ (`term-≥`, 定理), 第 1 项严格更大 (`term₁-strict`, 定理). 下标本身的值也改 (`overshootᴬ`, $\lceil\omega\cdot2\rceil$ 里有 $\omega\cdot3$, 定理). $\Omega+1$ 以上未证.
>
> **累加这边付的:**
>
> | 项目 | 不累加 | `Tˢ` 影子 | `Tᵇ` 不加 1 | `Tᶜ` | 档 |
> |---|---|---|---|---|---|
> | 下标 $\omega$ 的第 5 项 | 5 | | 15 | 20 | 有限测试 |
> | 第一个下标的 $G(2)$ | 16 | 76 | 111994 | 206933 | 有限测试 |
> | 第一个下标的 $G(1)$ | 1 | 4 | 4 | 9 | 有限测试 |
> | 第 1 项的 $G(1)$ 的计算 | 瞬时给 1 | 20 秒未完 | 25 秒未完 | 240 秒未完 | 计时观察, 不是值 |
> | `FGH T 0`, `FGH T 1` | 1, 2 | | 2 (定理) | 1, 2 | 测试; `FGH₀-1` 说参数 1 上一切树都是 2, 比较器是瞎的 |
>
> 还有: 指纹在第 1 项深度 4 上就不同形 (`diff₄`); 前驱结构验收不成立的同类现象 (`no-⊑⁰-lab` 是 src 的, 对 $T^c$ 没有单独证); 上一轮的 `no-cum-⊲` (累加不保第一位置), `no-⊞-left`, `overshootᴬ`. FGH 的逐点比较: 未证. 参数 0, 1 相等且分不开, 参数 2 算不完, 所以**没有区分两棵树的 FGH 有限测试**.
>
> **不累加这边付的:**
>
> | 项目 | 不累加 (`BTBOᴵ`, `OCF.Free`) | 累加 (`Tᶜ`, `Tψ`) | 档 |
> |---|---|---|---|
> | 定义是否依赖关于输出的定理 | 是. `Diagonal` 以 `Uniform` 为模块参数, 层号 `lim` 的步进来自证书, $\psi$ 的派发读它. 字面树依赖证明项, 模 $\cong$ 不依赖 (`γ-indep`) | 否. 下标的合法性由构造给出 (`Lg-next`). `HS` 是事后的定理, 定义不读 | 源码事实 |
> | 定义块数 (语法切片, 看不见模块参数, 所以不累加这边低估) | `BTBOᴵ` 83, 另加 `Uniform` | `Tψ` 102, `out`(`Tᶜ`) 106 | 切片 |
> | 下标比较 | 模 $\cong^I$, 要 `tr`, `back` | 字面 `cmpN`, 不搬运 | 源码事实 |
> | 闭包定理的负担 | `Vis`, `Hon` 等: 链点要高于守卫. `OCF.Free` 全部 6360 行 (含树, 证书, 桥), 到 $\Omega\cdot2$ | 字面就高, 但多了世界的管理. `CumUpW`, `Eq`, `Psi`, `Le`, `Main` 合计 2160 行, 到一切 $\Omega\cdot p+a$ | 行数, 口径不同, 不是比较定理 |
>
> **判断.** 累加把 "定义依赖证书" 换成 "基本列带毛刺", 不是免费的, 这两个代价不可通约, 哪个更好这里不下结论. 毛刺的主要部分来自**每个极限都累加, 且逐层嵌套**, 不是那个 $+1$ (见 `G(2)`: 去掉 $+1$ 只从 206933 到 111994, 影子到 76).
>
> ## 哪些是写法带的
>
> 见 [CumUpClean](CumUpClean.lagda.md).
>
> | 毛刺 | 判定 | 依据 |
> |---|---|---|
> | `asuc` | 写法带的 | `HS-Tᵇ` |
> | `os` 极限上的累加 | 写法带的 | `HS-Tˢ` |
> | 起点的 `one ⊞` | 写法带的 (判断) | 没写无此项的版本 |
> | 其余极限上的累加 | 不带证据时未见替代 | `no-rd` (否定的只是 "逐点读对一切 `HS` 树字面合法"); `dec⊲→LPO` (否定的只是 "判定 $\triangleleft$ 再补偿") |
> | 链上的 `η ⊞` | 未定 | 没有定理, 未走通 |
>
> `Tᵇ`, `Tˢ` 的序数值未证. 这两棵只在 $\psi_0(\Omega_\Omega)$ 这一站写了, `Tψ` 仍用 `next`.
>
> ## 受记号影响的形状
>
> $(p,a)$ 这个层的形状是照着 $\Omega\cdot p+a$ 写的, 高度只到 $\mathbb N$. 这不是从树侧推出来的, 不算 "树自足". 下一步 $\Omega^2$ 要把高度换掉, 没有做, 也不知道要换成什么. 证书和定义的语法切片不到达记号 (见下).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Free.Level using (HS; hl; _⊑⁰_; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; Gw; gw; g₀; pos; gnext; lgw)
open import OCF.Align.CumUpW using (Ω̇; Tψ)
open import OCF.Align.CumUpLe using (_⊴_; fc; rL; Ω⊴)
open import OCF.Align.CumUpMain using (HS-T; T-mono; ⊴₀→⊑⁰; module M₀)
```

## §1 实例

**同一条定理 `HS-T`, 不按阶段定制.** 下面只是把参数代进去.

```agda
TΩ : Ord₀
TΩ = Tψ 1 azero one g₀ (z⊲ one)

HS-TΩ : HS TΩ
HS-TΩ = HS-T 1 azero one g₀ (z⊲ one)

TΩ+1 : Ord₀
TΩ+1 = Tψ 1 one one g₀ C.self

HS-TΩ+1 : HS TΩ+1
HS-TΩ+1 = HS-T 1 one one g₀ C.self

-- Ω+a: 对一切合法且不低于 1 的 a
TΩ+ : (a : A) → Gw a → Ord₀
TΩ+ a g = Tψ 1 a a g C.self

HS-TΩ+ : ∀ a (g : Gw a) → HS (TΩ+ a g)
HS-TΩ+ a g = HS-T 1 a a g C.self

TΩ·2 : Ord₀
TΩ·2 = Tψ 2 azero one g₀ (z⊲ one)

HS-TΩ·2 : HS TΩ·2
HS-TΩ·2 = HS-T 2 azero one g₀ (z⊲ one)

TΩ·2+ : (a : A) → Gw a → Ord₀
TΩ·2+ a g = Tψ 2 a a g C.self

HS-TΩ·2+ : ∀ a (g : Gw a) → HS (TΩ·2+ a g)
HS-TΩ·2+ a g = HS-T 2 a a g C.self
```

$\Omega\cdot p$ 的上确界: 相邻两项由闭包的第一支给出.

```agda
TP : ℕ → Ord₀
TP p = Tψ p azero one g₀ (z⊲ one)

TP-step : ∀ p → TP p ⊑⁰ TP (suc p)
TP-step p = ⊴₀→⊑⁰ (M₀.top (fc (rL (Ω⊴ p (z⊲ one)))) g₀ g₀ one g₀ (pos g₀) (z⊲ one) one g₀ (pos g₀) (z⊲ one))

TΩ·ω : Ord₀
TΩ·ω = FL.lim TP

HS-TΩ·ω : HS TΩ·ω
HS-TΩ·ω = hl (λ p → HS-T p azero one g₀ (z⊲ one)) TP-step

fgh : ℕ → ℕ
fgh = FGH TΩ·ω
```
