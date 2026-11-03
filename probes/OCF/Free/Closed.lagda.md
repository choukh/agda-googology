# 无记号主线 (二十一): 闭项与 FGH

> 接 [Main](Main.lagda.md). 结论先说:
>
> 1. **`TΩ₂ : Ordᶜ zero` 与 `fgh = FGH TΩ₂`: 闭项, 无假设.** 树由数据树 `TΩ·2` 计值, 证书 `certᵀ` 由闭包定理给出, 没有任何参数. 按 [Bridge](Bridge.lagda.md) 的验收, 它的强度是 $\psi_0(\Omega_{\Omega\cdot2})$; 本文件的闭包不知道这个标签.
> 2. **本文件的传递导入闭包里没有记号或标签模块:** 除 stdlib 外只有 `OCF.Free.*` 与 `src` 的 `OCF.BTBO` (`probes/Survey/scripts/importclosure.py`). 这是编译器的保证, 不靠语法切片: 闭包外的定义不可能被检查器用到.
> 3. **定理 `TΩ₂-indep`, `fgh-indep`:** 换一组求值环境 `ev`, `z`, 树只差一个 $\cong$, FGH 逐点相等. 所以 `ev₀` 的选取不影响值.
> 4. **有限测试 (不是证明):** §2 的 `refl`. $f(0)=1$, 以及基本列前几项的形状. `fgh 1` 在 580 秒内没有算完, 见 §2 的注.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Closed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (z≅; toZ-≅)
open import OCF.Free.Floor using (Ev; _⊔_; fk)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Free.Tree using (Fl; TΩ·2)
open import OCF.Free.Main using (GᴺTΩ·2; RTΩ·2)
```

## §1 闭项

目标层是 $0$, 环境取最小的: $\ell=1$, 两个紧地板都是恒等模拟. `HSᵀ` 是遗传步进证书, 所以 `TΩ₂` 也能当层号 (`levelᵀ`).

```agda
ev₀ : Ev (suc zero) (Fl ⊔ fk zero)
ev₀ = (tt , (λ q → q)) , (λ q → q)

certᵀ : Goodᴺ (toZ (TΩ·2 ev₀ zero))
certᵀ = GᴺTΩ·2 ev₀ zero

TΩ₂ : Ordᶜ zero
TΩ₂ = forceᴺ _ certᵀ

HSᵀ : HS TΩ₂
HSᵀ = forceᴺ-HS _ certᵀ

levelᵀ : Ordᴵ
levelᵀ = toLevel TΩ₂ HSᵀ

fgh : ℕ → ℕ
fgh = FGH TΩ₂

TΩ₂-indep : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (z : zero <ᴵ ℓ) → TΩ₂ ≅ forceᴺ _ (GᴺTΩ·2 ev z)
TΩ₂-indep ev z = forceᴺ-≅ (toZ-≅ (RTΩ·2 ev₀ zero ev z z≅)) certᵀ (GᴺTΩ·2 ev z)

fgh-indep : ∀ {ℓ} (ev : Ev ℓ (Fl ⊔ fk zero)) (z : zero <ᴵ ℓ) n → fgh n ≡ FGH (forceᴺ _ (GᴺTΩ·2 ev z)) n
fgh-indep ev z = FGH-≅ (TΩ₂-indep ev z)
```

## §2 有限测试

下面只是在几个具体输入上算值, 不是证明. `FS`, `Sh` 只为读形状.

**注.** `_ : fgh 1 ≡ 2` 用 `refl` 在 580 秒内没有检查完, 所以不列在这里 (判断: 慢在沿证书展开, 不是值大; [BTBOSemantics](../Align/BTBOSemantics.lagda.md) 已指出这类序数的 FGH 在 $n\le2$ 时退化). 这条是没有结果, 不是否定.

```agda
FS : Ordᶜ zero → ℕ → Ordᶜ zero
FS (lim f) n = f n
FS (suc x) n = x
FS x       n = x

data Sh : Set where
  sz ss sl : Sh

sh : Ordᶜ zero → Sh
sh zero    = sz
sh (suc _) = ss
sh (lim _) = sl

_ : fgh 0 ≡ 1
_ = refl

_ : sh TΩ₂ ≡ sl
_ = refl

_ : sh (FS TΩ₂ 0) ≡ sl
_ = refl

_ : sh (FS TΩ₂ 1) ≡ sl
_ = refl

_ : sh (FS TΩ₂ 2) ≡ sl
_ = refl

_ : sh (FS (FS TΩ₂ 1) 1) ≡ sl
_ = refl
```

## §3 提取说明了什么

**编译过的事实.** 主线 (21 个文件, 4874 行非空代码, 含本文件) 单独编译通过, `agda --dependency-graph` 给出的模块图与 `importclosure.py` 一致: 本地模块只有 `OCF.Free.*` 21 个与 `OCF.BTBO`. 对照: `OCF.Align.UniformNF5Main` 的闭包 61 个本地模块, 23597 行非空代码, 含 `OCF.Align.EBO` 与 27 个禁用模块; 脚本返回 1.

**没有暗中的依赖.** 切片看不见 Agda 求解的隐式参数, 这条疑虑现在由编译器回答: 提取时按切片留下的块就够, 没有一处要补回记号或标签的引理. 主线里非逐字的代码只有一行 (`ωᴵ ω′ : Ordᴵ` 去掉用不到的 `ω′`, 见 [Level](Level.lagda.md)), 其余是导入行. 下一层的证据是 [Lab/](Lab/): 7686 行标签侧代码逐字在主线的定义上重新通过, 见 [Bridge](Bridge.lagda.md).

**旧闭包是怎么脏的.** 全部是模块粒度的搭便车. 例子: `UniformNF5Omega`, `Class`, `Good` 从 `Stage2Label` 只取 `one⁰`; `Eval`, `Main` 从 `Symbolic` 只取 `Mlev`; 证书 `Goodᴺ` 与 `ofL` 同住 `NotFree`; 树的 `Z`, `Ordˢ` 与标签定理同住 `Prefix`. 这些定义本身都不读记号.

**切片的一个盲点 (编译发现).** `depslice.py` 看不见模块别名: `NoCumsum` 的 `module D = Diagonal Uniform`, 引用 `D.γ` 链到 `Diagonal` 内部, 块 `D` 与它的实参 `Uniform` 都不在切片里. 这条路径只在标签一侧; 主线没有模块别名, 所以不影响记号无关的结论. 其他语法切片的结论, 遇到别名要另查.

**规模 (主线非空代码行).**

| 层 | 文件 | 行 |
|---|---|---|
| 层号与值层 | Level, Aux | 438 |
| 符号树, 地板, 互模拟 | Prefix, Floor, Eq | 709 |
| 证书 | Force | 94 |
| 数据树与计值 | Tree | 166 |
| 闭包定理 | Base 到 Main (13 个) | 3416 |
| 闭项与 FGH | Closed | 51 |
