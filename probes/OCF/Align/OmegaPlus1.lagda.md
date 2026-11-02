# $\psi_0(\Omega_{\Omega+1})$ 阶段 (二): 标签定理、链上的下两点与后续阶段的评估

> 接 [OmegaPlus1Base](OmegaPlus1Base.lagda.md). 本文把替身的归约定理变成标签定理, 给出 $\psi_0(\Omega_{\Omega+1})$ 的链点逐点的精确依赖, 以及 $\Omega_{\Omega+k}$、$\Omega_{\Omega\cdot2}$、$\Omega_{\Omega_\Omega}$、$\Lambda$ 在这个形态上的纸面路线与代价.
>
> 结论先说:
>
> 1. **三条标签定理, 一个前提, 对任意塔 (§1).** 对任意满足 OmegaPlus1Base 接口 `Tower` 的好性塔 `𝕋`, 设 `HΩ̂ : ∀ d → G (suc d) (Ω̂A d) []` ($\Omega_\Omega$ 的闭包定理对一切深度). 则 $\psi_0(\Omega_{\Omega+1})$ (`TO-label`)、$\psi_0(\Omega_{\Omega+1}+1)$ (`TO+1-label`)、$\psi_0(\Omega_{\Omega+1}\cdot2)$ (`TO·2-label`) 的统一树带遗传证书与标签, 对一切环境层号与地板证据. 证明各一行: `labelE` 作用于 `goodΩ⁺`. 没有别的前提; 特别地, 不需要任何关于 $\Omega_{\Omega+1}$ 的支配论证. 实例化到弱塔 `weak` 与深度 1 取 `GA1` 的塔 `tow1` (`TO-label¹` 等).
> 2. **逐点的精确依赖 (§2).** $\psi_0(\Omega_{\Omega+1})[n]=\psi_0(\gamma_n)$ 的标签只用到深度 $\le n$ 的闭包定理 (`TO-pt`, 前提 `HΩ̂≤ n`). 第 0 点 $\psi_0(\Omega_\Omega)$ **无条件** (`TO-pt0`/`TO-pt0¹`: 深度 0 的闭包定理是 Uniform2Depth1 的 `goodΩ̂₀`). **第一个未标签的点是 $[1]=\psi_0(\Omega_\Omega^2)$**: 它要深度 1 的闭包定理, 对 `tow1` 字面是 `GA1 E ζ → GA1 (Ω̂A 1 E) (ζ ++ Ω_Ω)`, 即 Uniform2 §6 以 `BranchΩ` 为前提、Relative 证明 `BranchΩ` 无居留、(Ω_Ω)² 路线 (OmegaSqA) 正在用层对齐互模拟重做的那条定理. 本阶段没有引入新的障碍: $\Omega_{\Omega+1}$ 替身的全部新内容 (层 $\Omega$ 的极限行、深度提升、链点的好性、两个塔的接口字段) 都是无条件定理, 阻塞点与 (Ω_Ω)² 的阻塞点是**同一个**, 形状也相同.
> 3. **"新支配论证" 的答案.** 不需要. README 的警示针对把 $\Omega_{\Omega+1}$ 做成闭包帧的设计 (地板下标 $w=\Omega$ 要 `Idx`); 统一形态下 $\Omega_{\Omega+1}$ 是对象层的 $\mathbb N$-极限, 行是 `gl`, 记号侧只用 "$\Omega+1$ 大于一切可数下标" (`gtΩ`, SystemOmega 的 `cmp-ΩC`). 链点在层 $\Omega$ 处的 "支配" 由替身层本身承担: 一切可数目标 $i$ 都走规则 6, 界与链点从不被比较.
> 4. **后续阶段 (§3, 纸面).** $\Omega_{\Omega+k}$: 每升一级加一个 `Ψ⁺`-型的帧 ($\psi_{\Omega+j}$ 的指数前缀塔以上一级的符号项为底), 替身仍是 $\mathbb N$-极限, 估计每级 150–250 行定义 + 与本文同量级的行引理; $\Omega_{\Omega\cdot2}$: 下标 $\Omega+\alpha$ ($\alpha$ 可数树) 的比较在当前环境层号内做, 塔以 `Sym` 为底的一层递归 (TopDown §9 的 `A⁺`), 估计 400–600 行; $\Omega_{\Omega_\Omega}$: 下标是符号项, 比较其语法 (`Syn` 的字典序, 叶子用 `<ᴵ-dec`), 估计 800–1200 行; $\psi_0(\Lambda)$: 阶段对角线, 又一个 $\mathbb N$-极限, 阶段递归写一次约 300 行. 全部以 `HΩ̂` 型的 "各深度闭包定理" 为前提, 每个阶段一条; 它们是否可证取决于 (Ω_Ω)² 路线的层对齐互模拟能否推到一切深度 (§3 末的估计: 深度 $d$ 的归纳与深度 1 同形, 关键是 (a′)(b′) 在深度 1 做完后对 $d$ 的提升是 "同样的交换套 $d$ 层").
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaPlus1 where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-trans; ≤-refl; m≤n+m)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; walkˢ)
import OCF.Align.EBO as E
open E using (T; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.StandardOmega using (NF₁; tO-NF)
open import OCF.Align.Stage2 using (tO; Lab-uniq)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.UniformS using (s≅; z≅)
open import OCF.Align.GoodLBase using (forceᴸ)
open import OCF.Align.Uniform2Base
open import OCF.Align.Uniform2 using (good∅ᴿ; goodTl0; one₀; lab-one₀; BranchΩ; TΩ2-cond)
open import OCF.Align.Uniform2Depth1 using (goodΩ̂₀)
open import OCF.Align.OmegaPlus1Base
```

## §1 标签定理 (对任意塔)

**主定理.** 在空底上好的符号项 $X$ (标签 $x$), 其计值树 `ψᵀ X ev z` 在一切环境与证据下带证书与标签 $\psi_0(x)$ (`NF₁` 下): Uniform2 `label` 的 `GEd 0` 版 (塔的深度 0 定义为 `GA0`, 取空前缀 `∅ᴿ` 的目标 0 标签). 下面整节对任意满足接口的塔 `𝕋` 陈述, 前提是它的 `HΩ̂`.

```agda
module Labels (𝕋 : Tower) where
  open Generic 𝕋

  labelE : ∀ {φ} {X : Sym φ} {x} → GEd 0 X x → NF₁ (ψ₀ᵗ x) →
           ∀ {ℓ} (ev : Ev ℓ (fz ⊔ φ)) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ X ev z) (ψ₀ᵗ x)
  labelE G nf ev z = g0 (proj₂ (G good∅ᴿ)) ev z nf
```

**三条标签.** $\psi_0(\Omega_{\Omega+1})$ 是 `Ω⁺ ∅ᵀ`; $\psi_0(\Omega_{\Omega+1}+1)$ 是 `Ω⁺ ∅ᵀ ⊕ 1` (尾巴在深度 0, Uniform2 的 `goodTl0` 对任意底, 深度 0 的塔就是 `GA0` 所以直接可用); $\psi_0(\Omega_{\Omega+1}\cdot2)$ 是 `Ω⁺ (Ω⁺ ∅ᵀ)` (内层替身在空底上好, 对一切深度, 正是外层替身的前提). 前提只有 `HΩ̂`.

```agda
  module _ (H : HΩ̂) where
    GEΩ⁺ : ∀ d → GEd d (OmegaPlus.Ω⁺ ∅ᵀ) (Ω⁺¹ ∷ [])
    GEΩ⁺ = Reduce.goodΩ⁺ 𝕋 ∅ᵀ {x = []} H GE∅

    TO-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (OmegaPlus.Ω⁺ ∅ᵀ) ev z) tO
    TO-label = labelE {X = OmegaPlus.Ω⁺ ∅ᵀ} {x = Ω⁺¹ ∷ []} (GEΩ⁺ 0) tO-NF

    TO+1-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) →
                 Lab₀ (ψᵀ (OmegaPlus.Ω⁺ ∅ᵀ ⊕ tlᵀ (flo zero) (cvFlo zero) one₀) ev z) tO+1
    TO+1-label = labelE {X = OmegaPlus.Ω⁺ ∅ᵀ ⊕ tlᵀ (flo zero) (cvFlo zero) one₀} {x = Ω⁺¹ ∷ 𝟏 ∷ []}
                        (goodE⊕ 0 {X = OmegaPlus.Ω⁺ ∅ᵀ} {Y = tlᵀ (flo zero) (cvFlo zero) one₀} {x = Ω⁺¹ ∷ []} {y = 𝟏 ∷ []}
                                (GEΩ⁺ 0) (goodTl0 lab-one₀ (s≅ z≅) FlrLab-fz))
                        tO+1-NF

    TO·2-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (OmegaPlus.Ω⁺ (OmegaPlus.Ω⁺ ∅ᵀ)) ev z) tO·2
    TO·2-label = labelE {X = OmegaPlus.Ω⁺ (OmegaPlus.Ω⁺ ∅ᵀ)} {x = Ω⁺¹ ∷ Ω⁺¹ ∷ []}
                        (Reduce.goodΩ⁺ 𝕋 (OmegaPlus.Ω⁺ ∅ᵀ) {x = Ω⁺¹ ∷ []} H GEΩ⁺ 0) tO·2-NF
```

**读法.** 三条定理的证明都是 `labelE` 作用于 `goodΩ⁺` 的实例. $\psi_0(\Omega_{\Omega+1}\cdot2)$ 的链点 $\psi_0(\Omega_{\Omega+1}+\psi_\Omega(\Omega_{\Omega+1}+\gamma_k))$ 把 $\Omega_{\Omega+1}$ 带进 $\psi_\Omega$ 的指数 (深度 1), 又在那里展开成 $\mathbb N$-极限 (深度 1 的 `Ω⁺`), 其链点再进深度 2, …: 这是 "指数的指数" 的栈, 由前缀塔免费承担. 与 TopDown §9 的预期不同, 本阶段**不**需要把塔的底换成符号项: `Ω⁺` 本身就是符号项上的算子, 它把 "重放前缀" 的要求兑现在 `Sym` 的多态性上.

## §2 链点的精确依赖

`HΩ̂≤ N`: 深度 $\le N$ 的闭包定理. 链点 $\Gamma_n$ 在深度 $d$ 的好性只用到深度 $d,\dots,d+n$ (对 $n$ 归纳, 每一步深度加一).

```agda
  HΩ̂≤ : ℕ → Set
  HΩ̂≤ N = ∀ d → d ≤ N → G (suc d) (Ω̂A d) []

  module _ {φ} (X : Sym φ) where
    open OmegaPlus X

    goodΓ≤ : ∀ {x} N → HΩ̂≤ N → (∀ d → GEd d X x) → ∀ n d → n +ᴺ d ≤ N → GEd d (ΓS n) (x ++ γΩ x n)
    goodΓ≤ {x} N H GX zero d le =
      goodE⊕ d {X = X} {Y = Ψ ∅ᵀ} {x = x} {y = ψΩᵗ []} (GX d)
             (goodEΨ d {Y = ∅ᵀ} {y = []} (GE∅ (suc d)) (H d le))
    goodΓ≤ {x} N H GX (suc n) d le =
      goodE⊕ d {X = X} {Y = Ψ (ΓS n)} {x = x} {y = ψΩᵗ (x ++ γΩ x n)} (GX d)
             (goodEΨ d {Y = ΓS n} {y = x ++ γΩ x n}
                     (goodΓ≤ N H GX n (suc d) (subst (_≤ N) (sym (+-suc n d)) le))
                     (H d (≤-trans (m≤n+m d (suc n)) le)))
```

**$\psi_0(\Omega_{\Omega+1})$ 的第 $n$ 项.** 树 `ψᵀ (Ω⁺ ∅ᵀ) ev z` 的第 $n$ 项字面是 `wk 0 (leΓ n) (ΓS n 0 ∅ᴿ) ev z` (`walkˢ … (n ∷ [])`, `refl`), 标签 $\psi_0(\gamma_n)$, 前提 `HΩ̂≤ n`.

```agda
  module _ where
    open OmegaPlus ∅ᵀ

    pt : ℕ → ∀ {ℓ} → Ev ℓ (fz ⊔ (fz ⊔ fk zero)) → zero <ᴵ ℓ → Ordˢ zero
    pt n ev z = wk 0 (leΓ n) (ΓS n 0 ∅ᴿ) ev z

    pt-walk : ∀ n {ℓ} ev (z : zero <ᴵ ℓ) → walkˢ (ψᵀ Ω⁺ ev z) (n ∷ []) ≡ pt n ev z
    pt-walk n ev z = refl

    TO-pt : ∀ n → HΩ̂≤ n → ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (pt n ev z) (ψ₀ᵗ (γΩ [] n))
    TO-pt n H ev z =
      g0 (proj₂ (wkG 0 (leΓ n) (inΓ n) (goodΓ≤ ∅ᵀ {x = []} n H GE∅ n 0 (subst (_≤ n) (sym (+-identityʳ n)) ≤-refl) good∅ᴿ)))
         ev z (nfγ n)
```

**实例化.** 两个塔都给出同样的三条定理与逐点依赖. 第 0 点对两个塔都无条件 (深度 0 的闭包定理分别是 `HΩ̂₀` 与 `goodΩ̂₀` 本身).

```agda
module W = Labels weak
module T1 = Labels tow1

H≤0ʷ : W.HΩ̂≤ 0
H≤0ʷ zero z≤n = HΩ̂₀

H≤0¹ : T1.HΩ̂≤ 0
H≤0¹ zero z≤n = goodΩ̂₀

TO-pt0 : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (W.pt 0 ev z) (ψ₀ᵗ (ΩΩ ∷ []))
TO-pt0 = W.TO-pt 0 H≤0ʷ

TO-pt0¹ : ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (T1.pt 0 ev z) (ψ₀ᵗ (ΩΩ ∷ []))
TO-pt0¹ = T1.TO-pt 0 H≤0¹

TO-label¹ : Generic.HΩ̂ tow1 → ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (OmegaPlus.Ω⁺ ∅ᵀ) ev z) tO
TO-label¹ = T1.TO-label

TO·2-label¹ : Generic.HΩ̂ tow1 → ∀ {ℓ} ev (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (OmegaPlus.Ω⁺ (OmegaPlus.Ω⁺ ∅ᵀ)) ev z) tO·2
TO·2-label¹ = T1.TO·2-label
```

**第一个未标签的点.** 第 1 项要 `HΩ̂≤ 1`, 其中深度 1 的部分对 `tow1` 字面是 (OmegaPlus1Base §5 的 `refl` 类型等式) "对一切 `GA1`-好的深度 1 指数前缀 $E$ (标签 $\zeta$), $E+\Omega_\Omega$ 是 `GA1`-好的 (标签 $\zeta+\Omega_\Omega$)". Uniform2 §6 以 `BranchΩ` 为前提证了它 (`DepthOneΩ.goodΩ̂₁`, 见 `fromBranch`), Relative 证明 `BranchΩ` 无居留, (Ω_Ω)² 路线正在用层对齐互模拟重做. 本阶段的第 1 点与 Uniform2 的 $\psi_0(\Omega_\Omega^2)$ 树是同一个标签 (`tΩ2`, 由 `fs-tO 1` 的 `refl`), 两棵树在一切观测点同种 (OmegaPlus1Base §6), 字面不等 (地板类型 `fk zero ⊔ fz` 对 `fk zero`, 编译否定); 若两者都得到标签, 计值后 $\cong$ (`Lab-uniq`):

```agda
_ : ψ₀ᵗ (γΩ [] 1) ≡ tΩ2
_ = refl

agree-pt1 : (H : T1.HΩ̂≤ 1) (Br : BranchΩ (Ω̂A 0) []) → ∀ {ℓ ℓ′} ev (z : zero <ᴵ ℓ) ev′ (z′ : zero <ᴵ ℓ′) →
            forceᴸ _ (proj₁ (T1.TO-pt 1 H ev z)) ≅ forceᴸ _ (proj₁ (TΩ2-cond Br ev′ z′))
agree-pt1 H Br ev z ev′ z′ = Lab-uniq (proj₂ (T1.TO-pt 1 H ev z)) (proj₂ (TΩ2-cond Br ev′ z′))
```

**读法.** 依赖是精确的: 第 $n$ 点只要深度 $\le n$; 第 0 点是定理; 第 1 点起要的恰是 (Ω_Ω)² 的内容, 而且以 `tow1` 的形状 (`GA1 → GA1`) 要, 不多不少. 这说明 $\psi_0(\Omega_{\Omega+1})$ 阶段在统一形态上**没有新的数学障碍**: 替身、$\Omega$ 层的行、深度提升、链点的好性、两个塔的全部接口字段都是无条件定理, 剩下的是 $\Omega_\Omega$ 闭包定理对深度 $\ge1$ 的证明, 那是 (Ω_Ω)² 路线的任务; 深度 $\ge2$ 的闭包定理需要什么形状的记录, 由那条路线在深度 1 的做法决定, 本阶段只要它满足五个接口字段 (§4 的估计: 弱塔的 `limΩ` 证明按 $d$ 归纳, 对任何 "深度 $d+1$ 逐点是深度 $d$" 的记录同形).

## §3 后续阶段的评估 (纸面)

**$\psi_0(\Omega_{\Omega+k})$.** $\Omega_{\Omega+2}=\psi_{\Omega+2}(0)$ 正规, $\psi_i(P+\Omega_{\Omega+2})[n]=\psi_i(P+\gamma_n)$, $\gamma_{k+1}=\psi_{\Omega+1}(P+\gamma_k)$: 层 $\Omega+1$ 的链, 链点是新帧 $\psi_{\Omega+1}(\zeta)$ 的迭代. 新帧的指数 $\zeta<\Omega_{\Omega+2}$ 是 $\psi_{\Omega+1}(\cdot)$ 之和加上 $<\Omega_{\Omega+1}$ 的项 (本阶段的符号项). 它在可数目标 $i$ 处是什么: $\psi_i(P+\psi_{\Omega+1}(\zeta))$, 共尾度由 $\zeta$ 定: $\zeta$ 后继时 $\psi_{\Omega+1}(\zeta-1)\cdot m$ (压 $m$ 帧, `fold (suc d)` 的后继子句逐字), $\zeta$ ω-极限时逐点, $\zeta$ 共尾度 $\Omega_{\nu+1}$ 且 $\nu+1\le\Omega+1$ 时穿透 (对 $\nu$ 可数与 $\nu=\Omega$ 都穿透: `cmpᵀ (ν+1) (Ω+1)` 是 `lt`/`eq`), $\nu+1>\Omega+1$ 时折叠. 所以 $\psi_{\Omega+1}$ 帧的作用是: 指数前缀 (深度 $d+1$) 作用于 "$\Omega_{\Omega+1}$ 的替身" —— 与 `Ψ Y d P = Y (suc d) (Ω̂A d) P` 同形, 只把 `Ω̂A d` 换成 `Ω⁺` 在深度 $d$ 的作用 `Ω⁺ ∅ᵀ (suc d)`. 但有一处不同: $\Omega_{\Omega+1}$ 在 $\psi_{\Omega+1}$ 的指数里被弹出时 ($\psi_i(P+\psi_{\Omega+1}(\zeta+\Omega_{\Omega+1}))$, 共尾度 $\Omega_{\Omega+1}$ 穿透 $\psi_{\Omega+1}$ 再在 $\psi_i$ 处折叠), 链点是 $\psi_\Omega(P+\psi_{\Omega+1}(\zeta+\gamma_k))$: 含**整个外层前缀** $P$, 而 $P$ 是深度 $d$ 的值. 这就是 TopDown §9 说的 "前缀要以 `Sym` 的形式给出": 第 $k+1$ 级的塔要以第 $k$ 级的符号项为底. 本阶段躲过了它, 因为 $\Omega_{\Omega+1}$ 只在最外层出现 (`Ω⁺ X` 的 $X$ 就是整个前缀); 从 $\Omega_{\Omega+2}$ 起躲不过. 估计: 一层 "以符号项为底的塔" `A⁺ 0 = Sym`、`A⁺ (suc d) = A⁺ d → A⁺ d`, 本文的 §2–§4 在它上面重做 (约 300 行), 加 $\psi_{\Omega+1}$ 帧的闭包定理 (前提形如 `HΩ̂`, 一条) 与 $\Omega+1$ 对可数 $\nu+1$ 的派发表 (SystemOmega 已有 `cmp-CΩ`/`cmp-ΩC`, 推广到 $\Omega+c$ 对 $\Omega+c'$ 是 `refl`). $k$ 级的塔是这一层对 $k$ 的迭代, 不随 $k$ 增加新内容. 每级 150–250 行定义, 行引理与本文同量级 (约 250 行), 全部以各级的 "各深度闭包定理" 为前提.

**$\psi_0(\Omega_{\Omega\cdot2})$.** 下标 $\Omega+\alpha$, $\alpha$ 可数树. 新内容只有派发: 规则 5/6 要比较 $\nu+1$ 与 $u$, 二者形如 $\Omega+\alpha$、$\Omega+\beta$, 化为 $\alpha$ 与 $\beta$ 的比较, 它们是可数层号, 在当前环境层号内用 `<ᴵ-dec` —— 与 `limᵢA` 的派发同一机制, 交替不变量照旧 (被比较的只有同一 $\ell$ 的两个字面子项). $\Omega_{\Omega\cdot2}=\lim_\alpha\Omega_{\Omega+\alpha}$ 是奇异的, 共尾度 $\Omega_1$: 它的弹出是**闭包** (`ŝ`), 地板下标是 $\Omega$ 层的符号点, 分支 $\eta$ 处是 $\Omega_{\Omega+\eta}$ —— 这是 README 警示真正适用的地方: `gŝ` 行要地板下标的 `Idx`, 而链点 $\Omega+\eta$ 的 "层号" 是符号的. 预期的修正: `gŝ` 的地板字段推广为 "可数下标的 `Idx`, 或 $\Omega+c$ 且 $c$ 带 `Idx`" (与 StandardOmega 的 `Sb` 同形), 支配 `domᴸ` 的 `occ<` 对 $\Omega+c$ 的情形归结为 $c$ 的 `occ<` (SystemOmega 已有 `cmp-ΩC` 一半). 估计 400–600 行 (塔以 `Sym` 为底 300 + 派发 100 + `gŝ`/`domᴸ` 推广 150), 记号侧 `NF₁` 的 `Sb` 已含 $\Omega+c$ (StandardOmega §1), 不用改.

**$\psi_0(\Omega_{\Omega_\Omega})$.** 下标 $u<\Omega_\Omega$ 本身是本阶段的符号项 ($\Omega\cdot\alpha+\beta$、$\Omega^\alpha$、$\psi_\Omega(\cdots)$). 规则 5/6 要比较两个符号下标: 它们是函数, 要比较**语法** (`Syn`, TopDown §5) 的字典序 (EBO 的 `cmpᵀ` 逐字), 叶子是可数树, 在当前环境层号内比较. 交替不变量在符号层的形式: 两个被比较的符号下标的全部可数叶子要在同一环境层号之下 —— 由上一层闭包的分支现造 (`Mlev (Fc B) (suc η)`), 与现在相同. 下标宇宙与项宇宙相同 (`ψ̇ (sym X) ζ`), 帧的作用以下标的 `Syn` 为参数. $\Omega_{\Omega_\Omega}$ 奇异, 共尾度 $\Omega_1$ (下标 $\Omega_\Omega$ 的共尾度), 弹出是闭包, 分支 $\eta$ 处 $\Omega_{\Omega_\eta}$: 地板下标 $\Omega_\eta$ 带 `Idx`? 不带 (不可数), 但它的**语法**含可数叶 $\eta$, `gŝ` 的地板字段再推广一次为 "符号下标, 其可数叶带 `Idx`", 支配对叶子做. 估计 800–1200 行 (语法比较 200 + 符号下标的帧与闭包 300 + `gŝ`/`domᴸ`/`Sb` 的推广 300 + 记号侧 `NF₁` 把 `Sb` 换成一般符号下标 (StandardOmega 的 `vs`/`cofin` 同步推广) 200–400).

**$\psi_0(\Lambda)$.** 第 $s$ 阶段的符号项类型 `Sym⟨ s ⟩` 对 $s$ 递归 (都在 `Set`), 第 $s$ 阶段的顶 $\psi_0(\Omega$-塔$_s)$ 是它的对角线 (像 `Ω⁺ ∅ᵀ`: 替身是 $\mathbb N$-极限, 链点是上一阶段的帧的迭代), $\psi_0(\Lambda)=\lim_s$ 各阶段的顶: 又一个对象层的 $\mathbb N$-极限, 阶段号从不被比较. 阶段递归写一次约 300 行; 每阶段的内容是上面三种之一 (后继下标: $\Omega_{\Omega+k}$ 型; 极限下标: $\Omega_{\Omega\cdot2}$/$\Omega_{\Omega_\Omega}$ 型), 所以到 $\psi_0(\Lambda)$ 的定义本体估计 $1500$–$2500$ 行, 不含各阶段的闭包定理 (每阶段一条 `HΩ̂` 型假设, 其证明是 (Ω_Ω)² 路线在该阶段的重做, 按自下而上的经验是定义的 3–5 倍).

**本阶段的代价 (四层口径, 只给 "树侧 EBO" 一列的本次增量, 按 ```agda 块内非空行).** 层 1 (定义): `Ω⁺`/`ΓS`/`evΓ`/`leΓ`/`inΓ` 约 20 行, 接口 `Tower`/`Gof` 与 `GSd`/`GEd` 约 20 行, 两个塔的定义 `GAd`/`GAd1` 约 15 行; 层 2 (折叠): 0 (无新子句); 层 3–4 (证书与标签, 同一递归): 对任意塔的规则约 25 行, $\Omega$ 层极限行与两个塔的深度提升约 95 行, 两个塔的其余字段约 50 行, 替身好性约 15 行, 标签定理与链点约 50 行, 记号侧 (`gtΩ`、链、`NF₁`) 约 30 行. 合计约 370 行 (OmegaPlus1Base 约 300, OmegaPlus1 约 70; 两文件 ```agda 块内非空行实数 345 + 83, 其中 `refl` 检验与编译否定约 55 行不计), 其中无条件的约 345 行, 以 `HΩ̂` 为前提的是归约定理、三条标签定理与 `TO-pt` (约 25 行). 对照: GoodL 的 $\psi_0(\Omega_\Omega\cdot2)$ 阶段 1500 行, OmegaK 的 $\psi_0(\Omega_\Omega\cdot k)$ 1100 行, Uniform2 的统一形态 2000 行. 低一个数量级的原因: $\Omega_{\Omega+1}$ 在本形态上没有新的树构造, 只有新的**排列** (把已有的帧迭代排成一列), 而排列的标签是 ω-极限行, 它在 Uniform2Base 里已经对一切前缀证过; 两个塔实例的大部分行数是把同一个极限行按深度归纳搬运.

## §4 结论与边界

**成立 (无条件):** `Ω⁺` 的定义 (符号项上的算子, 无新折叠子句); 接口 `Tower` 与对任意塔的规则 (`Generic`: `good∅d`/`good⊕d`/`goodΨd`/`goodEΨ`); 两个实例的全部字段 (`weak`: `GAd`、`appGAd`、`wkGAd`、`limGAω`/`limGAΩ`; `tow1`: `GAd1`、`app1`、`wkGAd1`、`lim1ω`/`lim1Ω`/`lim1Gω`/`lim1GΩ`); `fromGA1`、`HΩ̂₀`、`H1₀`、`fromBranch`; $\Omega$ 层的规则 6 行 `limΩW`/`limΩ0`/`limΩGR`; 记号侧 `gtΩ`、`fsΩ⁺¹`、`fs-tO`、`nfγ`、`tO+1-NF`、`tO·2-NF`、`fs-tO+1`、`fs-tO·2`; 第 0 点 `TO-pt0`/`TO-pt0¹`; `refl`: 树种类检验 (OmegaPlus1Base §6), `walk tO [0]`、`walk tO [1] ≡ tΩ2`, `ψ₀(γ₁) ≡ tΩ2`, `pt-walk`, `tow1` 深度 1 假设的类型等式.

**成立 (以 `HΩ̂` 为前提, 对任意塔):** `Reduce.goodΓ`/`goodΩ⁺` (归约定理, 对一切空底好的符号前缀与一切深度), `TO-label`、`TO+1-label`、`TO·2-label` (实例 `TO-label¹`、`TO·2-label¹`); 逐点 `TO-pt n` 以 `HΩ̂≤ n` 为前提; `agree-pt1`.

**编译否定:** `walkˢ TOᵀ [1] ≡ TΩ2ᵀ` 的 `refl` 不成立 (`fk zero ⊔ fz != fk zero`, OmegaPlus1Base §6): 闭包把地板类型传给 `bound`, 两棵树只在观测上同种、在标签下 $\cong$.

**未做 / 精确停点:** `HΩ̂ d` 对 $d\ge1$, 即 $\Omega_\Omega$ 的闭包定理在深度 $\ge1$ (对 `tow1` 在深度 1 是 `GA1 → GA1` 的闭包; 深度 $\ge2$ 的记录形状待 (Ω_Ω)² 路线定, 换记录只需重做 OmegaPlus1Base §5 约 70 行); 第一个未标签的点 $\psi_0(\Omega_{\Omega+1})[1]=\psi_0(\Omega_\Omega^2)$, 与 (Ω_Ω)² 路线的停点相同 (Uniform2 §6: 深度 1、尾巴 $\Omega_\eta$、$\eta=3$、`¬AlignΩ₃`). 本阶段不引入新的停点. 不改 `src/`、`archive/` 与任何已有文件; README 未更新.
