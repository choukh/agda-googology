# 链的严格增长: 记号无关的 $\mathtt{lvl}\,\gamma'_m\prec^\mathsf I\mathtt{lvl}\,\gamma'_{m+1}$

> 接 [TreeNF](TreeNF.lagda.md). 那里 `Stop.popOcc₃`/`Stop.γ′₃-blocked` 唯一依赖记号的前提是链的严格增长 $\beta_0\prec^\mathsf I\eta_1$ ($\beta_0=\mathtt{lvl}\,\gamma'_1$, $\eta_1=\mathtt{lvl}\,\gamma'_2$), 只经标签证明 (`Accept.growth-lab`). 本文记号无关地证明它, 并证明一般的步进. 树的定义与证书不读记号; 标签只在 §8.
>
> 结论先说:
>
> 1. **严格单调性定理 (§5, `Mono`, `growth-mono`), 无条件.** 对一切层号 $\eta\prec^\mathsf I\eta'$ (即 $\eta+1\sqsubseteq^\mathsf I\eta'$)、一切环境、一切 Prefix 证书 $G,G'$: $\psi^{[\hat\Omega]}_0(\Omega_\eta)$ 的计值树 $\prec$ $\psi^{[\hat\Omega]}_0(\Omega_{\eta'})$ 的计值树, 层号 $\prec^\mathsf I$. 证明全在观测前序里, 不要任何中间证书: 把 $\psi_0(\Omega_\eta)+1$ 固定在左端, 右端沿 $\eta'$ 的结构攀升 (§4), 到 $\eta'=a+1$ 时取第 1 个链点 $\psi^{[\hat\Omega]}_0(\psi^{[\hat\Omega]}_a(\Omega_a))$, 再沿内层尾巴下降到弹栈闭包的第 0 点 $\psi^{[]}_a(\Omega_1)$ (§2 "B1 在 $\psi_0$ 之下"), 它含 $\psi_a(1)=\Omega_a\cdot\omega\ni\Omega_a\cdot2$, 于是 $\psi_0(\Omega_a+\Omega_a)\sqsupseteq^\mathsf o\psi_0(\Omega_a+1)=\psi_0(\Omega_a)\cdot\omega\ni\psi_0(\Omega_a)\cdot2\sqsupseteq^\mathsf o\psi_0(\Omega_a)+1$ (§3), 最后一步用 $1\sqsubseteq^\mathsf o$ 一切 $\psi^{[\hat\Omega]}_0$ 的输出 (§1).
> 2. **$m=1$ (§6, `Growth₁.growth₁`).** $\beta_0\prec^\mathsf I\eta_1$ 对 $\gamma'_2$ 的**任意**证书 $G$, 不读记号. TreeNF 的 `Stop.popOcc₃`/`Stop.γ′₃-blocked` 的前提由此解除 (`popOcc₃ᴺ`, `γ′₃-blockedᴺ`).
> 3. **$m=2$ 与链 (§6, `Growth₂.growth₂`, `growth-step`, `Chain.inc`).** 给 $\gamma'_3$ 的任意证书 $G_3$: $\eta_1\prec^\mathsf I\mathtt{lvl}\,\gamma'_3$. 一般形 **`growth-step`**: $\eta_m+1\sqsubseteq^\mathsf I\eta_{m+1}$ 与 $\gamma'_{m+1},\gamma'_{m+2}$ 的证书推出 $\eta_{m+1}\prec^\mathsf I\eta_{m+2}$ (就是 `growth-mono`). `Chain`: 给定链的证书序列与 "下一层号 = 计值树的层号", 整条链严格增长. 这是给 "悬置不变量" 一侧消费的形式, 类型见 §6.
> 4. **否定 (§7, `Chain.Diag.no-growth`, 编译).** 任务里设想的一致形式 "$\forall\eta\,G.\ \eta\prec^\mathsf I\mathtt{lvl}(\psi^{[\hat\Omega]}_0(\Omega_\eta))$" (膨胀性) 为假: 取链的对角 $\zeta_\infty=\lim_n\zeta_n$ ($=\mathtt{lvl}\,t_2$), $\psi_0(\Omega_{\zeta_\infty})$ 的计值树的层号 $\cong^\mathsf I\lim_n\zeta_{n+1}$, 若 $\zeta_\infty\prec^\mathsf I$ 它, 则 $\zeta_\infty\prec^\mathsf I\zeta_{n+1}\prec^\mathsf I\zeta_\infty$, 违反 `≺ᴵ-irrefl`. 以链的证书 (与 `Chain` 相同的前提) 为参数编译. 所以正确的一般形是**单调性** (结论 1), 不是**膨胀性**; 第一处失效恰在 $t_2$.
> 5. **验收 (§8, 记号只在这里).** `growth₁` 与 TreeNF 的 `A₂.growth-lab` 是同一命题 $\beta_0\prec^\mathsf I\eta_1$ 的两个证明.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Growth where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; addˢ; _+ˢ_; toZ; Goodᶻ; force; force-HS; z<suc; intoˢ; outˢ; out-intoˢ; tr⁻ˢ)
open import OCF.Align.UniformS
open import OCF.Align.Stage2Label using (Strict₁; t₀pop; gpop)
open import OCF.Align.Omega2 using (t₀ᵗ; gᵗ; G₀ᵗ)
open import OCF.Align.NotFree using (χ₀; hχ₀; dχ₀; ofZ-≅)
open import OCF.Align.TreeNFBase using (NZ; CovΛ; Occ≺ᴳ)
open import OCF.Align.TreeNF using (β₀; eG₀; Gγ′₂; ≺→⊑ᴵ; module Stop; module S₃)
```

导入说明: TreeNF 的 `β₀`, `eG₀`, `Gγ′₂`, `≺→⊑ᴵ`, `Stop`, `S₃` 都是记号无关的 (TreeNF §1–§3); 它的验收模块 `A₂` 只在 §8 导入.


## §1 $1\sqsubseteq^\mathsf o$ 一切 $\psi^{[\hat\Omega]}_0$ 的输出

单 $\hat\Omega$ 栈、目标 0 的 $\psi$ 对尾巴 0 弹栈成闭包 `ŝ 1 t₀ g`, 第 0 点 $t_0=\psi^{[]}_0(\Omega_1)\sqsupseteq^\mathsf o\Omega_0=1$ (UniformS 的 `B1₀`), 所以 $1\sqsubseteq^\mathsf o\psi^{[\hat\Omega]}_0(0)$ (`ŝ-r`), 再由 `B1₁` 推到一切自反尾巴. 这是 Stage2Label `Strict₁` 的第一半, 单独写出, 因为 §3 要在观测前序里用它 (不是在 `idO` 处).

`ψŝ-r`: 右端是 $\psi_0$ 包着的非零层闭包 `ŝ` 时, 按闭包所在层号 $i$ 分: $i=0$ 时 $\psi_0$ 把它变成 `ĉᴸ` (`ĉ-r`), 否则仍是 `ŝ` (`ŝ-r`). 这个按 $i$ 的分派让 §2–§3 不必对层号做模式匹配.

```agda
one⊑pop : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) → Ωˢ zero ⊑ᵒ ψ1 p σ z Ord₊ˢ.zero
one⊑pop p σ z =
  ŝ-r {k′ = zero} (B1₀ {q = zero} {σ = σ1 (z<suc z p)} (≅→⊑ᵒ (Ωˢ-refl zero)) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

one⊑ψ1 : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) (y : Ordˢ k) → y ≅ˢ y → Ωˢ zero ⊑ᵒ ψ1 p σ z y
one⊑ψ1 p σ z y ey = B1₁ {q = p} {σ = σ} {z₁ = z} (one⊑pop p σ z) y ey

ψŝ-r : ∀ {i k L} {p : zero <ᴵ L} {σ : Simᴵ i L} {z : zero <ᴵ L} {x : Ordˢ k} {c : Ordᴵ} {t₀ : Ordˢ i}
       {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ i} → x ⊑ᵒ ψ1 p σ z t₀ → x ⊑ᵒ ψ1 p σ z (Ord₊ˢ.ŝ c t₀ g)
ψŝ-r {i = zero}    h = ĉ-r h
ψŝ-r {i = suc _}   h = ŝ-r {k′ = zero} h
ψŝ-r {i = lim _ _} h = ŝ-r {k′ = zero} h
```


## §2 B1 在 $\psi_0$ 之下

UniformS 的 `B1₁`: 若 $x\sqsubseteq^\mathsf o\psi^{[\hat\Omega]}_q(0)$, 则对一切自反尾巴 $w$ 有 $x\sqsubseteq^\mathsf o\psi^{[\hat\Omega]}_q(w)$. 本文要的是它被外层 $\psi^{[\hat\Omega]}_0$ 包住的形式: 若 $x\sqsubseteq^\mathsf o\psi_0(\psi_q(0))$, 则 $x\sqsubseteq^\mathsf o\psi_0(\psi_q(w))$. 它**不能**由 `B1₁` 经观测 `ψo₁` 得到: 观测把左端也包进 $\psi_0$, 而我们的左端 ($\psi_0(\Omega_\eta)+1$) 不是 $\psi_0$ 的像. 也不能由 `B1₁` 与 `ψ1-cong` 复合: 观测前序的传递性需要中间项在每个观测处的证书 (UniformS §4 的 `⊑ᵒ-≅ʳ` 只对 $\cong$ 搬运证书). 所以对 $w$ 重做 `B1₁` 的递归, 每一步多穿一层 $\psi_0$:

- 后继: $\psi_q(w+1)=\lim_n\psi_q(w)\cdot n$, $\psi_0$ 逐点进入, 取第 1 项 ($\psi_q(w)+0=\psi_q(w)$).
- 极限: 取第 0 项.
- `limᵢ`: 内层按 `<ᴵ-dec (σ′ q′) q` 分派. 穿透 (`injᵃ`, 节点层 $\prec$ 目标 $q$) 时内层输出是节点层 $j''$ 上的 `limᵢ`, 外层 $\psi_0$ 对它再分派 `<ᴵ-dec (σ r) p`: 节点 $\prec0$ 不可能, 其余两支取第 0 项 $\psi_0(\psi_q(g(\Omega_{j''})))$, 经 `out-intoˢ` 的 `subst` 回到 $g$ 的自反输入. 折叠 (`injᵇ`/`injᶜ`) 时取第 0 项 $\psi_0(\psi_q(g(\Omega_{j'})))$.
- `up`: 换 `Sim`, 假设不变 (弹栈子句不读 `Sim`).
- `ŝ`: 内层按尾巴层号 $k$: $k=0$ 时内层输出 `ĉᴸ`, 外层仍 `ĉᴸ` (`ĉ-r`); 否则内层输出 `ŝ`, 外层由 `ψŝ-r`. `ĉᴸ`: `ĉ-r`.

两处嵌套 `with` 的工程注记: 内层 `with` 之后的省略号指内层左端, 所以外层剩下的分支必须写在嵌套 `with` **之前** (写在之后会被当成内层分支, 报 `Ωˢ j′ != tr⁻ˢ e₁ (…)`; 写成 `... | p | q` 则报 `[UnexpectedWithPatterns]`).

```agda
B1₁₀ : ∀ {i ℓ k k₀ L} {p : zero <ᴵ L} {σ : Simᴵ i L} {z : zero <ᴵ L} {q : i <ᴵ ℓ} {σ′ : Simᴵ k ℓ} {z₁ : zero <ᴵ ℓ}
        {x : Ordˢ k₀} → x ⊑ᵒ ψ1 p σ z (ψ1 q σ′ z₁ Ord₊ˢ.zero) → (w : Ordˢ k) → w ≅ˢ w → x ⊑ᵒ ψ1 p σ z (ψ1 q σ′ z₁ w)
B1₁₀ h Ord₊ˢ.zero e = h
B1₁₀ {p = p} {σ = σ} {z = z} {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.suc w) e =
  lim-r {h = λ n → ψ1 p σ z (iter (ψ1 q σ′ z₁ w +ˢ_) Ord₊ˢ.zero n)} 1 (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h w (s-invˢ e))
B1₁₀ {p = p} {σ = σ} {z = z} {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.lim f) e =
  lim-r {h = λ n → ψ1 p σ z (ψ1 q σ′ z₁ (f n))} 0 (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (f 0) (l-invˢ e 0))
B1₁₀ {p = p} {σ = σ} {z = z} {q = q} {σ′ = σ′} {z₁ = z₁} {x = x} h (Ord₊ˢ.limᵢ {i = j′} q′ g) e with <ᴵ-dec (σ′ q′) q
... | injᵇ _ = lim-r 0 (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (g (intoˢ (<→◃ q′) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-r 0 (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (g (intoˢ (<→◃ q′) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᵃ (via {a′ = j″} e₁ r) with <ᴵ-dec (σ r) p
...   | injᵃ (via _ ())
...   | injᵇ _ = lim-r 0 (subst (λ u → x ⊑ᵒ ψ1 p σ z (ψ1 q σ′ z₁ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ u))))) (sym (out-intoˢ (<→◃ r) (Ωˢ j″)))
                    (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ (Ωˢ j″)))) (i-respˢ e (self-tr⁻ˢ e₁ (Ωˢ-refl j″)))))
...   | injᶜ _ = lim-r 0 (subst (λ u → x ⊑ᵒ ψ1 p σ z (ψ1 q σ′ z₁ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ u))))) (sym (out-intoˢ (<→◃ r) (Ωˢ j″)))
                    (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ (Ωˢ j″)))) (i-respˢ e (self-tr⁻ˢ e₁ (Ωˢ-refl j″)))))
B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.up zero w) e     = B1₁₀ {q = q} {σ′ = λ r → σ′ (suc r)} {z₁ = z₁} h w (u-reflˢ zero e)
B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.up (self n) w) e = B1₁₀ {q = q} {σ′ = λ r → σ′ (lim n r)} {z₁ = z₁} h w (u-reflˢ (self n) e)
B1₁₀ {k = zero}    {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-r (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h t₀ (ŝ-refl₀ e))
B1₁₀ {k = suc _}   {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.ŝ c t₀ g) e = ψŝ-r (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h t₀ (ŝ-refl₀ e))
B1₁₀ {k = lim _ _} {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.ŝ c t₀ g) e = ψŝ-r (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h t₀ (ŝ-refl₀ e))
B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-r (B1₁₀ {q = q} {σ′ = σ′} {z₁ = z₁} h o₀ (ĉ-refl₀ e))
```


## §3 $\psi_0(\Omega_\eta)+1\sqsubseteq^\mathsf o\psi_0(\psi^{[\hat\Omega]}_a(\Omega_a))$ ($\eta\cong^\mathsf Ia$)

这是单调性的核心: 下一点 $\psi_0(\Omega_{a+1})$ 的折叠链的第 1 个链点 $c_1=\psi^{[\hat\Omega]}_0(\psi^{[\hat\Omega]}_a(\Omega_a))$ 严格超过上一点 $A=\psi_0(\Omega_\eta)$, 以 "$\sqsupseteq^\mathsf o A+1$" 的形式. 模块 `Direct` 以 $A$ 的环境 ($p_1,\sigma_1,z_1$)、$\eta\cong^\mathsf Ia$、外层环境 ($p,z$)、内层目标 $t:a<^\mathsf IL$ 与 `Sim` $\sigma'$ 为参数. 四步, 全部是右端的字面下降 (`lim-r` 选项, `with` 分派), 左端固定:

- **B3** $\psi_0(\Omega_a+\Omega_c)\sqsupseteq^\mathsf oA+1$, 对 $c$ 递归: $c=0$ 时 $\Omega_a+1$, $\psi_0(\Omega_a+1)=\lim_n\psi_0(\Omega_a)\cdot n$, 取 $n=2$: $\psi_0(\Omega_a)+\psi_0(\Omega_a)\sqsupseteq^\mathsf o A+1$ 由 `add-cong` ($A\cong\psi_0(\Omega_a)$, $1\sqsubseteq^\mathsf o\psi_0(\Omega_a)$ 即 §1). $c=c'+1$: $\Omega_a+\Omega_{c'+1}$ 是节点 $c'$ 上的 `limᵢ`, $\psi_0$ 分派后取第 0 项 $\psi_0(\Omega_a+\Omega_{c'})$ (`coeˢ` 经 `out-intoˢ` 消去). $c=\lim$: 取第 0 项.
- **B2** $\psi_0(\psi^{[]}_a(1))\sqsupseteq^\mathsf oA+1$: $\psi^{[]}_a(1)=\lim_n\Omega_a\cdot n$, 取 $n=2$, 即 B3 在 $c=a$.
- **B1** $\psi_0(\psi^{[]}_a(\Omega_1))\sqsupseteq^\mathsf oA+1$: $\Omega_1$ 是节点 0 上的 `limᵢ`, 内层按 `<ᴵ-dec (z<suc z t) zero` 分派 (0 与 $a$ 比较): $0\prec a$ 时穿透, 外层 $\psi_0$ 对节点 0 再分派 (两个 $\prec$ 支不可能, $\cong$ 支取第 0 项 $\psi_0(\psi_a(\mathrm{tr}^-\,1))$, `tr⁻ˢ z≅ (suc zero)` 定义性地是 `suc zero`); $a\prec0$ 不可能; $0\cong a$ 时内层折叠, 取第 0 项 $\psi_0(\psi_a(1))$. 两支都归到 B2.
- **B0** $\psi_0(\psi^{[\hat\Omega]}_a(0))\sqsupseteq^\mathsf oA+1$: 弹栈闭包的第 0 点就是 B1 的树 (`ψŝ-r`).
- **base** $\psi_0(\psi^{[\hat\Omega]}_a(\Omega_a))\sqsupseteq^\mathsf oA+1$: §2 的 `B1₁₀` 以 B0 为假设.

工程注记: `add-cong` 的左端 $x=\Omega_0$ 在第 0 层, 它的 `Sim` 是 `Simᴵ zero a`; 这里 $a$ 也是 0 层的 (两个被加数都是 `Ordˢ zero`), 所以 `λ q → q` 可用; 若左端在第 0 层而右端在层 $a$, 要写 `λ ()` (写 `λ q → q` 报 `a != zero`). $a$ 是模块参数, 不能对它模式匹配, 所以 $0\cong a$ 的分支不去精化 $a$, 直接取第 0 项 (那里尾巴是字面的 $\Omega_0$).

```agda
module Direct {η L₁} (p₁ : zero <ᴵ L₁) (σ₁ : Simᴵ η L₁) (z₁ : zero <ᴵ L₁)
  {a : Ordᴵ} (e : η ≅ᴵ a) {L} (p : zero <ᴵ L) (z : zero <ᴵ L) (t : a <ᴵ L) (σ′ : Simᴵ a L) where

  A : Ordˢ zero
  A = ψ1 p₁ σ₁ z₁ (Ωˢ η)

  A′ : Ordˢ zero
  A′ = ψ1 p σ′ z (Ωˢ a)

  eA′ : A ≅ˢ A′
  eA′ = ψ1-≅ {p = p₁} {σ = σ₁} {p′ = p} {σ′ = σ′} {z = z₁} {z′ = z} (≅ᴵ-refl zero) (Ωˢ-≅ e)

  B3 : ∀ c (τ : Simᴵ c a) → Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (addˢ (Ωˢ a) τ (Ωˢ c))
  B3 zero τ = lim-r {h = iter (A′ +ˢ_) Ord₊ˢ.zero} 2
                (add-cong {σ = λ q → q} {σ′ = λ q → q} refl eA′ (one⊑ψ1 p σ′ z (Ωˢ a) (Ωˢ-refl a)))
  B3 (suc c) τ with <ᴵ-dec (σ′ (τ zero)) p
  ... | injᵃ (via _ ())
  ... | injᵇ _ = lim-r 0 (subst (λ u → Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (addˢ (Ωˢ a) τ (Ord₊ˢ.up zero u)))
                           (sym (out-intoˢ (<→◃ (τ zero)) (Ωˢ c))) (B3 c (λ q → τ (suc q))))
  ... | injᶜ _ = lim-r 0 (subst (λ u → Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (addˢ (Ωˢ a) τ (Ord₊ˢ.up zero u)))
                           (sym (out-intoˢ (<→◃ (τ zero)) (Ωˢ c))) (B3 c (λ q → τ (suc q))))
  B3 (lim f s) τ = lim-r 0 (B3 (f 0) (λ q → τ (lim 0 q)))

  B2 : ∀ (σ₀ : Simᴵ zero (suc a)) → Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (ψ0 {ℓ = suc a} zero σ₀ (Ord₊ˢ.suc Ord₊ˢ.zero))
  B2 σ₀ = lim-r {h = λ j → ψ1 p σ′ z (iter (Ωˢ a +ˢ_) Ord₊ˢ.zero j)} 2 (B3 a (λ q → q))

  B1 : Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (ψ0 {ℓ = suc a} zero (σ1 (z<suc z t)) (Ωˢ (suc zero)))
  B1 with <ᴵ-dec (σ1 (z<suc z t) zero) zero
  ... | injᵇ (via _ ())
  ... | injᶜ _ = lim-r 0 (B2 (λ q → σ1 (z<suc z t) (suc q)))
  ... | injᵃ (via z≅ r) with <ᴵ-dec (σ′ r) p
  ...   | injᵃ (via _ ())
  ...   | injᵇ (via _ ())
  ...   | injᶜ _ = lim-r 0 (subst (λ u → Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (ψ0 {ℓ = suc a} zero (σ1 (z<suc z t)) (Ord₊ˢ.up zero (tr⁻ˢ z≅ u))))
                             (sym (out-intoˢ (<→◃ r) (Ωˢ zero))) (B2 (λ q → σ1 (z<suc z t) (suc q))))

  B0 : Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (ψ1 t σ′ z Ord₊ˢ.zero)
  B0 = ψŝ-r B1

  base : Ord₊ˢ.suc A ⊑ᵒ ψ1 p σ′ z (ψ1 t σ′ z (Ωˢ a))
  base = B1₁₀ {q = t} {σ′ = σ′} {z₁ = z} B0 (Ωˢ a) (Ωˢ-refl a)
```


## §4 攀升

从 $\eta'=a+1$ 到一般 $\eta'\sqsupseteq a+1$: 对 $q:a<^\mathsf I\eta'$ 递归, 左端 $X$ 任意. $\eta'=\lim f$: $\Omega_{\lim f}=\lim_n\Omega_{f n}$, 取第 $n$ 项 ($a<^\mathsf If\,n$). $\eta'=b+1$ 且 $a<^\mathsf Ib$: $\Omega_{b+1}$ 是节点 $b$ 上的 `limᵢ`, $\psi_0$ 分派 ($b\prec0$ 不可能), 取第 0 项 $\psi_0(\Omega_b)$. $\eta'=a+1$: 取第 1 项 $\psi_0(\psi_a(\Omega_a))$, 由 `base` 给出. `Sim` 沿 `up` 逐步变化, `base` 对一切 `Sim` 量化.

```agda
module Climb {X : Ordˢ zero} {L} (p : zero <ᴵ L) (z : zero <ᴵ L) {a : Ordᴵ}
  (base : ∀ (σ : Simᴵ (suc a) L) →
          X ⊑ᵒ ψ1 p (λ q → σ (suc q)) z (ψ1 (σ zero) (λ q → σ (suc q)) z (Ωˢ a))) where
  climb : ∀ {b} (q : a <ᴵ b) (σ : Simᴵ b L) → X ⊑ᵒ ψ1 p σ z (Ωˢ b)
  climb zero σ with <ᴵ-dec (σ zero) p
  ... | injᵃ (via _ ())
  ... | injᵇ _ = lim-r 1 (base σ)
  ... | injᶜ _ = lim-r 1 (base σ)
  climb (suc q) σ with <ᴵ-dec (σ zero) p
  ... | injᵃ (via _ ())
  ... | injᵇ _ = lim-r 0 (climb q (λ r → σ (suc r)))
  ... | injᶜ _ = lim-r 0 (climb q (λ r → σ (suc r)))
  climb (lim n q) σ = lim-r n (climb q (λ r → σ (lim n r)))
```


## §5 严格单调性定理

$\eta+1\sqsubseteq^\mathsf I\eta'$ 展开为 $\eta\cong^\mathsf Ia<^\mathsf I\eta'$ (`unpack`). `Mono`: 对 $\psi^{[\hat\Omega]}_0(\Omega_\eta)$、$\psi^{[\hat\Omega]}_0(\Omega_{\eta'})$ 的任意证书 $G_1,G_2$ (任意环境), $A+1\sqsubseteq^\mathsf o\psi_0(\Omega_{\eta'})$ (§3 + §4) 在观测 `idO` 处用证书 `gs G₁` 与 $G_2$ 实例化, 左端的计值字面是 `suc (force G₁)`, 于是 `force G₁ ≺ force G₂` (`≺z`), 层号经 `toLevel-≺`. **没有任何其他前提.**

`growth-mono` 是它在 Omega2 的符号树 `gᵗ` (环境 `Mlev 1 η e`) 上的实例, 就是任务要的 `growth-step` 的类型 (§6).

```agda
unpack : ∀ {η η′} → suc η ⊑ᴵ η′ → Σ Ordᴵ λ a → η ≅ᴵ a × a <ᴵ η′
unpack (s⊑ e q) = _ , e , q

module Mono {η η′ : Ordᴵ} (h : suc η ⊑ᴵ η′)
  {L₁} {p₁ : zero <ᴵ L₁} {σ₁ : Simᴵ η L₁} {z₁ : zero <ᴵ L₁}
  {L₂} {p₂ : zero <ᴵ L₂} {σ₂ : Simᴵ η′ L₂} {z₂ : zero <ᴵ L₂}
  (G₁ : Goodᶻ (toZ (ψ1 p₁ σ₁ z₁ (Ωˢ η)))) (G₂ : Goodᶻ (toZ (ψ1 p₂ σ₂ z₂ (Ωˢ η′)))) where

  A : Ordˢ zero
  A = ψ1 p₁ σ₁ z₁ (Ωˢ η)

  module Pt {a} (e : η ≅ᴵ a) (q : a <ᴵ η′) where
    sucA⊑ : Ord₊ˢ.suc A ⊑ᵒ ψ1 p₂ σ₂ z₂ (Ωˢ η′)
    sucA⊑ = Climb.climb {X = Ord₊ˢ.suc A} p₂ z₂ (λ σ → Direct.base p₁ σ₁ z₁ e p₂ z₂ (σ zero) (λ r → σ (suc r))) q σ₂

    tree : force _ G₁ ≺ force _ G₂
    tree = sucA⊑ idO (Goodᶻ.gs G₁) G₂ (≺z (≅-refl⁰ (force _ G₁)))

  tree : force _ G₁ ≺ force _ G₂
  tree = Pt.tree (proj₁ (proj₂ (unpack h))) (proj₂ (proj₂ (unpack h)))

  level : toLevel (force _ G₁) (force-HS _ G₁) ≺ᴵ toLevel (force _ G₂) (force-HS _ G₂)
  level = toLevel-≺ (force-HS _ G₁) (force-HS _ G₂) tree

growth-mono : ∀ {η η′} (e : suc zero ⊑ᴵ η) (e′ : suc zero ⊑ᴵ η′) → suc η ⊑ᴵ η′ →
              (G : Goodᶻ (toZ (gᵗ η e))) (G′ : Goodᶻ (toZ (gᵗ η′ e′))) →
              toLevel (force _ G) (force-HS _ G) ≺ᴵ toLevel (force _ G′) (force-HS _ G′)
growth-mono {η} {η′} e e′ h G G′ =
  Mono.level {η = η} {η′ = η′} h {p₁ = lim 0 zero} {σ₁ = λ q → lim 1 q} {z₁ = lim 0 zero}
             {p₂ = lim 0 zero} {σ₂ = λ q → lim 1 q} {z₂ = lim 0 zero} G G′
```


## §6 链: $m=1$, $m=2$, 一般步进

**$m=1$.** $\gamma'_1$ 的计值树是 Omega2 的 `t₀ᵗ` $=\psi^{[\hat\Omega]}_0(\Omega_1)$ (证书 `G₀ᵗ`, 环境层号 1), NotFree 的 $\chi_0\cong$ 它, $\beta_0=\mathtt{lvl}\,\chi_0$. `Strict₁` 给 $2\sqsubseteq^\mathsf I\beta_0$, 即 $1+1\sqsubseteq^\mathsf I\beta_0$, 正是 `Mono` 的前提 ($\eta=1$, $\eta'=\beta_0$). 对 $\gamma'_2=\psi^{[\hat\Omega]}_0(\Omega_{\beta_0})$ (`gᵗ β₀ dχ₀`) 的**任意**证书 $G$: $\chi_0\prec$ 它的计值树, $\beta_0\prec^\mathsf I\eta_1$. 于是 TreeNF `Stop` 里带增长前提的两条 (`popOcc₃`: $\gamma'_3$ 的每个弹栈闭包满足 `Occ≺ᴳ`; `γ′₃-blocked`: 单覆盖的 `Floor` 不能用于 $\gamma'_3$) 成为无前提的记号无关定理.

```agda
two⊑β₀ : two ⊑ᴵ β₀
two⊑β₀ = ⊑ᴵ-≅ʳ (Strict₁ {p = zero} {σ = σ1 zero} {z = zero} (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G₀ᵗ) eG₀

module Growth₁ (G : Goodᶻ (toZ (gᵗ β₀ dχ₀))) where
  module M = Mono {η = suc zero} {η′ = β₀} two⊑β₀
                  {p₁ = zero} {σ₁ = σ1 zero} {z₁ = zero}
                  {p₂ = lim 0 zero} {σ₂ = λ q → lim 1 q} {z₂ = lim 0 zero} G₀ᵗ G

  tree : χ₀ ≺ force _ G
  tree = ≺-respˡ (≅-sym (ofZ-≅ G₀ᵗ)) M.tree

  growth₁ : β₀ ≺ᴵ Stop.η₁ G
  growth₁ = toLevel-≺ hχ₀ (force-HS _ G) tree

  popOcc₃ᴺ : ∀ (e : suc zero ⊑ᴵ Stop.η₁ G) {i} → NZ i →
             (p : i <ᴵ Mlev (suc zero) (Stop.η₁ G) e) (z : zero <ᴵ Mlev (suc zero) (Stop.η₁ G) e) →
             Occ≺ᴳ (suc i) (t₀pop p z) (gpop p z)
  popOcc₃ᴺ = Stop.popOcc₃ G growth₁

  γ′₃-blockedᴺ : ∀ (e : suc zero ⊑ᴵ Stop.η₁ G) β → Mlev (suc zero) (Stop.η₁ G) e ⊑ᴵ β → ¬ CovΛ (suc zero) β
  γ′₃-blockedᴺ = Stop.γ′₃-blocked G growth₁
```

**$m=2$ 与一般步进.** $\gamma'_3$ 的符号树是 `gᵗ η₁ e₃`; 它的证书是 TreeNF 的停点, 本文不造, 以参数 $G_3$ 给出: 一旦有, $\eta_1\prec^\mathsf I\mathtt{lvl}\,\gamma'_3$. 一般的 `growth-step` 就是 `growth-mono` 换个名字, 类型按任务的形式写出, 供 "悬置不变量" 一侧消费:

> `growth-step : ∀ {η η′} (e : 1 ⊑ᴵ η) (e′ : 1 ⊑ᴵ η′) → suc η ⊑ᴵ η′ → (G : Goodᶻ (toZ (gᵗ η e))) (G′ : Goodᶻ (toZ (gᵗ η′ e′))) → lvl (force G) ≺ᴵ lvl (force G′)`

读法: $\eta=\eta_m$ 是 $\gamma'_m$ 的层号, $G$ 是 $\gamma'_{m+1}=\psi_0(\Omega_{\eta_m})$ 的证书, $\eta'=\eta_{m+1}=\mathtt{lvl}(\mathrm{force}\,G)$, $G'$ 是 $\gamma'_{m+2}$ 的证书; 前提 $\eta_m\prec^\mathsf I\eta_{m+1}$ 是上一步的结论 (写成 `s⊑′`). `Chain` 把这个归纳写出来: 给链的层号序列 $\zeta$、证书序列 $G_n$ (第 $n$ 个证书是 $\psi_0(\Omega_{\zeta n})$ 的) 与 "$\zeta(n+1)\cong^\mathsf I\mathtt{lvl}(\mathrm{force}\,G_n)$", 以及起点 $\zeta0\prec^\mathsf I\zeta1$, 则整条链严格增长. 任务里 "$\forall\eta\,e\,G.\ \eta\prec^\mathsf I\mathtt{lvl}(\mathrm{force}\,G)$" 的形式**不是**这个定理 (见 §7): 增长来自上一步, 不来自 $\eta$ 自身.

```agda
module Growth₂ (G : Goodᶻ (toZ (gᵗ β₀ dχ₀))) (e₃ : suc zero ⊑ᴵ Stop.η₁ G) (G₃ : Goodᶻ (toZ (gᵗ (Stop.η₁ G) e₃))) where
  growth₂ : Stop.η₁ G ≺ᴵ toLevel (force _ G₃) (force-HS _ G₃)
  growth₂ = growth-mono dχ₀ e₃ (s⊑′ (Growth₁.growth₁ G)) G G₃

growth-step : ∀ {η η′} (e : suc zero ⊑ᴵ η) (e′ : suc zero ⊑ᴵ η′) → suc η ⊑ᴵ η′ →
              (G : Goodᶻ (toZ (gᵗ η e))) (G′ : Goodᶻ (toZ (gᵗ η′ e′))) →
              toLevel (force _ G) (force-HS _ G) ≺ᴵ toLevel (force _ G′) (force-HS _ G′)
growth-step = growth-mono

module Chain (ζ : ℕ → Ordᴵ) (e : ∀ n → suc zero ⊑ᴵ ζ n) (G : ∀ n → Goodᶻ (toZ (gᵗ (ζ n) (e n))))
  (lv : ∀ n → toLevel (force _ (G n)) (force-HS _ (G n)) ≅ᴵ ζ (suc n)) (base : ζ 0 ≺ᴵ ζ 1) where

  inc : ∀ n → ζ n ≺ᴵ ζ (suc n)
  inc zero    = base
  inc (suc n) = ≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym (lv n)) (growth-step (e n) (e (suc n)) (s⊑′ (inc n)) (G n) (G (suc n)))) (lv (suc n))
```

`Chain` 对 $t_2$ 的链的实例: $\zeta0=1$, $\zeta1=\beta_0$, `base` 由 `two⊑β₀`; 证书序列从 `G₀ᵗ`, `Gγ′₂` 开始, 第三项起是未得的 (TreeNF §4). 下面 §7 继续用 `Chain` 的参数.


## §7 否定: 一致的膨胀性在对角处为假

设想的一致形式 $\forall\eta\,G.\ \eta\prec^\mathsf I\mathtt{lvl}(\psi^{[\hat\Omega]}_0(\Omega_\eta))$ 在链的对角失效. 在 `Chain` 的前提下 (链严格增长, 所以 `≺→⊑ᴵ (inc n)` 给出步进证据), $\zeta_\infty=\lim_n\zeta_n$ 是一个层号 (它就是 $\mathtt{lvl}\,t_2$: $t_2$ 的计值树是链点的 $\lim$, 层号是层号的 $\lim$). $\Omega_{\zeta_\infty}=\lim_n\Omega_{\zeta n}$ (Prefix 的 `Ωˢ` 对 `lim` 的子句), $\psi_0$ 逐点进入, 所以 $\psi_0(\Omega_{\zeta_\infty})$ 的任意证书 $G_\infty$ 是 `gl`, 计值树是 $\lim_n$ (第 $n$ 个分支的计值), 第 $n$ 个分支 $\cong$ `gᵗ (ζ n)` 的计值 (`ψ1-≅`, 环境不同), 层号 $\cong^\mathsf I\zeta(n+1)$. 所以 $\mathtt{lvl}(\mathrm{force}\,G_\infty)\cong^\mathsf I\lim_n\zeta(n+1)$ (`lv-lim`). 若 $\zeta_\infty\prec^\mathsf I$ 它, 则 $\zeta_\infty\cong a'<^\mathsf I\lim_n\zeta(n+1)$, 字面子项序在 `lim` 处给出某个 $n$ 使 $a'<^\mathsf I\zeta(n+1)$ (`split`), 而 $\zeta(n+1)\prec^\mathsf I\zeta(n+2)<^\mathsf I$-进入 $\zeta_\infty$ (`≺-lim`), 得 $\zeta_\infty\prec^\mathsf I\zeta_\infty$, 与 `≺ᴵ-irrefl` 矛盾.

读法. 否定以链的证书为参数, 没有造出它们 (那是 TreeNF 的停点); 它说的是: 一致膨胀性与 "链有证书" 不相容, 而链有证书正是整个纲领的目标, 所以一致膨胀性不是可以追求的一般形. 失效处精确在 $\mathtt{lvl}\,t_2$: 对 $\eta=\zeta_\infty$, $\psi_0(\Omega_\eta)$ 的树 $\cong$ 链的尾段, 层号与 $\eta$ 只差一个移位, 在 $\cong^\mathsf I$ 下不可比 ($\cong^\mathsf I$ 对 `lim` 逐点), 在 $\prec^\mathsf I$ 下循环. 这与 Stage2Label §11 关于 `Strictⱼ` "$j\ge\psi_0(\Omega_\Omega\cdot2)$ 时为假" 的纸面判断一致, 现在是编译过的、且不经值的.

工程注记: `lv-lim` 对参数 $G_\infty$ 直接模式匹配 `gl`, 因为类型 `toZ (gᵗ (lim ζ s) e∞)` 定义性地归约到 `lim`; `toLevel` 对 `lim` 的子句使层号也归约到 `lim`, 于是 `l≅` 逐点. 匹配要求 $G_\infty$ 是函数参数而不是模块参数.

```agda
  module Diag (e∞ : suc zero ⊑ᴵ lim ζ (λ n → ≺→⊑ᴵ (inc n))) where
    ζ∞ : Ordᴵ
    ζ∞ = lim ζ (λ n → ≺→⊑ᴵ (inc n))

    lv-lim : (G∞ : Goodᶻ (toZ (gᵗ ζ∞ e∞))) →
             toLevel (force _ G∞) (force-HS _ G∞) ≅ᴵ lim (λ n → ζ (suc n)) (λ n → ≺→⊑ᴵ (inc (suc n)))
    lv-lim (Goodᶻ.gl Gs st) = l≅ (λ n →
      ≅ᴵ-trans (toLevel-≅ _ (force-HS _ (G n))
                  (force-≅ (toZ-≅ (ψ1-≅ {p = lim 0 zero} {σ = λ q → lim 1 (lim n q)} {p′ = lim 0 zero} {σ′ = λ q → lim 1 q}
                                         {z = lim 0 zero} {z′ = lim 0 zero} (≅ᴵ-refl zero) (Ωˢ-refl (ζ n))))
                           (Gs n) (G n)))
               (lv n))

    split : ∀ {g t} → ζ∞ ≺ᴵ lim g t → Σ ℕ λ n → ζ∞ ≺ᴵ g n
    split (via d (lim n q)) = n , via d q

    no-growth : (G∞ : Goodᶻ (toZ (gᵗ ζ∞ e∞))) → ¬ (ζ∞ ≺ᴵ toLevel (force _ G∞) (force-HS _ G∞))
    no-growth G∞ g = ≺ᴵ-irrefl (≺ᴵ-trans (proj₂ sp) (≺-lim (suc (suc (proj₁ sp))) (inc (suc (proj₁ sp)))))
      where
      sp : Σ ℕ λ n → ζ∞ ≺ᴵ ζ (suc n)
      sp = split (≺ᴵ-respʳ g (lv-lim G∞))
```


## §8 验收 (记号只在这里)

`growth₁` 在 `Gγ′₂` 处的实例与 TreeNF 的 `A₂.growth-lab` (经 `Lab-oc`、`γ′-NF`、`γ′-mono`) 是同一命题 $\beta_0\prec^\mathsf I\eta_1$ 的两个证明; 这是 "记号无关的证明与经标签的证明给出同一不等式" 的验收. TreeNF 的 `S₃.popOcc₃`/`S₃.γ′₃-blocked` 现在既可以用 `growth-lab` 也可以用 `growth₁ᴳ` 解除前提, §6 已用后者.

```agda
open import OCF.Align.TreeNF using (module A₂)

growth₁ᴳ : β₀ ≺ᴵ S₃.η₁
growth₁ᴳ = Growth₁.growth₁ Gγ′₂

agree : (β₀ ≺ᴵ S₃.η₁) × (β₀ ≺ᴵ S₃.η₁)
agree = growth₁ᴳ , A₂.growth-lab
```


## §9 结论与边界

**定理 (编译, 记号无关).** `Mono`/`growth-mono`: 对一切 $\eta+1\sqsubseteq^\mathsf I\eta'$ 与一切证书, $\mathtt{lvl}(\psi^{[\hat\Omega]}_0(\Omega_\eta))\prec^\mathsf I\mathtt{lvl}(\psi^{[\hat\Omega]}_0(\Omega_{\eta'}))$, 树也 $\prec$. 实例: **`Growth₁.growth₁ : β₀ ≺ᴵ η₁`** 对 $\gamma'_2$ 的任意证书; `Growth₂.growth₂` 对 $\gamma'_3$ 的任意证书; `growth-step` (任务 2 的形式, 以上一步的增长为前提); `Chain.inc` (整条链). `popOcc₃ᴺ`/`γ′₃-blockedᴺ`: TreeNF `Stop` 的两条结论去掉增长前提.

**否定 (编译).** `Chain.Diag.no-growth`: 一致膨胀性 $\eta\prec^\mathsf I\mathtt{lvl}(\psi_0(\Omega_\eta))$ 在链的对角 $\zeta_\infty=\mathtt{lvl}\,t_2$ 处为假 (以链的证书为参数). 任务 2 原来的类型 `∀ η e G → η ≺ᴵ toLevel (force _ G) …` 因此**不可证**; 可证且够用的是 `growth-step` 的单调形式.

**为什么不需要中间证书.** 第一版 (已编译, 未保留) 走 "$A+1\sqsubseteq^\mathsf oA\cdot\omega$, $A\cdot\omega\sqsubseteq^\mathsf o\psi_0(\Omega_{\eta'})$" 两段, 在 `idO` 处复合要 $A\cdot\omega$ 的证书 (由 `Good-iter` 从链点的符号好性给出, 对 $m=1$ 用 UniformS 的 `Good`, 对 $m=2$ 用 TreeNF `F₀` 的 `Good`), 所以多一个前提且依赖好性所在的族. 本文把两段合成一段 (§2–§4): 左端始终是 $A+1$, 右端字面下降, 观测前序的每一步都是 UniformS 的上界引理 (`lim-r`, `ĉ-r`, `ŝ-r`) 或 `with` 分派, 没有传递性, 所以没有中间证书.

**边界.** 树族是 Prefix 的符号族, 栈 `[Ω̂]`, 目标 0; 定理对一切环境 (`Mlev` 或任何 $L$) 与一切 `Sim` 成立. 没有造任何新证书: $\gamma'_3$ 的证书仍是 TreeNF §4 的停点. 没有改任何已有文件, README 未改.
