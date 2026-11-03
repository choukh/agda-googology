> **机械克隆.** 由 `Prefix` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 前缀栈折叠 $\psi^P$: 实现、空栈桥接与 `Goodᶻ` 的缺口

> 接 [Symbolic](Symbolic.lagda.md) §10. 那里把 $\psi_0(\Omega_\Omega+\Omega_2)$ 与 $\psi_0(\Omega_\Omega\cdot2)$ 的遗传标签归结为三件事: (i) 前缀栈折叠 $\psi^P$, (ii) `Goodᶻ` 对其输出封闭, (iii) 记号侧假设 H1–H4. 本文实现 (i) 并做检验; (ii) 在无符号片段上完成, 一般情形精确定位缺口; (iii) 逐条对到 [StandardOmega](StandardOmega.lagda.md)/[SystemOmega](SystemOmega.lagda.md) 的定理.
>
> 结论先说:
>
> 1. **接口 (§1).** H1 由新证的 `H1-pen`/`H1-col`/`H1-fsT` 给出, 比假设强: 不要标准形, 对**一切非空**下标 $\delta$, 共尾度 $\Omega_1$ ($\mu=0$) 的参数在 $\psi_\delta$ 处穿透且逐点 (`fsT`), 只在 $\psi_0$ 处折叠; 奇异叶本身是 SystemOmega 的 `ΩΩlf`, $\Omega+c$ 下标是 `cmp-CΩ`. H2 就是 SystemOmega 的 `occ<` (推论 `dominate`), 实例 `H2-η₁`. H3 就是 StandardOmega 的 `cofin₁` (无额外前提), 实例 `H3-X₂`. H4 未做 (只 $\psi_0(\Omega_{\Omega+1})$ 需要).
> 2. **$\psi^P$ 编译通过 (§3).** 栈是 `Vec (Frame ℓ) n`, 长度 $n$ 作显式参数; 停机度量 ($n$, 尾巴) 的字典序由检查器自己找到, 一次通过, 没有子句需要改写. `List` 栈被拒, 确切报错在 §3. 与 Symbolic §10 (i) 的三处不同: (a) 规则 6 的链点**带同一个栈** (EBO 的 $b[\gamma_k]$ 含整个前缀; 设计里写的 "链点用空栈" 会丢前缀); (b) `ŝ` 在第 0 层就读作待计值的链 (Symbolic 的 `ĉ`), 所以尾巴 `ŝ` 与弹出 $\hat\Omega$ 两个子句不分目标层; `z0` 删去, `Z` 增加 `ĉᴸ`; (c) **闭包的界必须是紧的**: $c=i+1$ ($i$ 为目标层), 不能取环境层号 $\ell$. 环境层号经 `Mlev` 计值后膨胀到 $\cong\eta$; 在 $\gamma'_3$ 内部生成的 $A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$ 的闭包会以 $\cong\gamma'_2$ 为界, 而 $A$ 的第 0 点 $\eta_1<\gamma'_2$ (`A-in-γ′3`, `A0<γ′2`), 证书字段 `d₀` 不可能成立 (§7). 紧的界由 `rebase` 重建; 在受支配的层号 `Mlev 2 η e` 内部重算 $X_2$, $A$ 的闭包的界仍是 $2$ (`X₂ᴹ`, `refl`).
> 3. **`Goodᶻ`/`force` 推广到 `ĉᴸ` (§4).** 链与输出分开; 纯链 ($o=g$) 与 Symbolic 的 `Tᶜ` 逐项 `refl` (`force-chain`).
> 4. **空栈与 Level 的 $\psi$ 一致 (§5).** 无符号节点的新族树与 Level 的树之间的异族互模拟 `_~_`; `ψ~ : i ≅ᴵ i′ → a ~ b → ψᴾ 0 p σ [] a ~ ψ p′ σ′ b` 对任意相关输入成立 (不只 $\Omega$); 第 0 层 `force~`, 由旧树的 `HS` 造 `Goodᶻ` (`plainGood`); 推论 `empty-agree : force (toZ (ψᴾ 0 p σ [] (Ωˢ a))) G ≅ ψ⁰ (Ω a)` 与 `empty-good`.
> 5. **检验 1 通过 (§6).** $\psi^{[\hat\Omega]}(0)$ 字面就是闭包 `β₀` (`refl`), 证书 `Gβ` 的十个字段齐全 (单调用 Level 的 `Ψ⁰-mono`), **`βˢ≅ : ∀ G → force (toZ β₀) G ≅ BTBOᴵ`** (对任意证书; 恢复 Symbolic 的 `Tβ≅`), `βˢ-label : Lab (force (toZ β₀) G) ψ₀(Ω_Ω)`.
> 6. **检验 2、3 只到符号树 (§7).** 前缀暴露处确实成了闭包: $A=X_2[1][0][1]$, $B=X_2[2][0][1]$, 以及 $B$ 的第 0 点之下的 $[0][0]$, 都是界为 $2$ 的待计值链 (`refl`); Symbolic 的 `B0t` 在最后一处是静态的 `lim`, 那正是 `B0-unlabel` 的起点. $t_2$ 的符号树字面是 Symbolic 的 `C2` 的形状 (`t2ˢ-shape`). **计值树都未构造**: 缺 `Goodᶻ (toZ X₂ˢ)`; 第一个缺的实例是 $A$ 的闭包. 所以 `Lab (force (ψ⁰^{[fΩ̂ z]} (Ω 2)) G) (ctx (Ωt (natT 2)))` 与 `Lab T2 t2` 都未得, `PB` 与 `Q′` 两条路径只在符号层走到闭包, 未在计值层走完.
> 7. **`Goodᶻ` 闭包的缺口 (§8).** (a) Uniform 在新族上的移植 (新族互模拟 `≅ˢ`、以 `force` 为底的观测前序、带栈的 `B1`/`zero-l`、`ŝ`/`ĉᴸ` 的上界引理), 同形但未写; (b) 不是移植的数学: `dE` (闭包的界 $\sqsubseteq^\mathsf I$ 链点的层号). 界为 $\delta+1$ 时它是 "$\psi_\delta$ 出现在链点里 $\Rightarrow\delta\prec^\mathsf I$ 链点的层号", 即 `occ<` 的**树版本**. $\psi_0(\Omega_\Omega+\Omega_2)$ 的闭包的界都 $\le2$, 化为 "非零尾巴上的 $\psi_0$ 输出 $\succ1$", 初等但需要 $\prec$ 的严格性 (Level 的 $\sqsubseteq$ 是前驱包含, 对 `suc` 不单调); $\psi_0(\Omega_\Omega\cdot2)$ 的内层闭包的 $\delta$ 跑遍 $\gamma'_k$ 的层号的子项, 需要本阶段的序对应 (Label 的 `oc`/`Slt` 的阶段 2 版本), 而序对应又来自标签: 证书与标签在这一阶段互相依赖.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件 (Symbolic 的族声明不导入, 以同名在本文重新声明并修改, 见 §2).


```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZPrefix where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open Restr renaming (eq to eqᴿ; lt to ltᴿ)
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.Symbolic using (Fs; Fst; Mlev; Ctx; Pt; pt; lvP; Γᶜ; χᶜ; Tᶜ; χᶜ-step; σ1; Aᵗ; X₂ᵗ)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; Cmp; lt; eq; gt; cof; cofA; cofψ₊; cmpᵀ; natT; fsT; fsn; fsTc; cΩ; cω; _<ᵀ_) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.Stage2 using (one⊑; walkᵀ; Allω; γ′ᴱ; t2)
open import OCF.Align.Standard using (Ctbl; c[]; c∷) renaming (d₀ to d₀ᴰ)
import OCF.Align.ScafLadderZStandardOmega as SΩ
open SΩ using (NF₁; cofin₁; diag₁-desc-NF; walkD)
open import OCF.Align.ScafLadderZSystemOmega using (η₁; cur-holds; occ<; Occ; oh; od; ot)
```


## §1 接口核对: H1–H4

Symbolic §10 (iii) 的四条假设, 逐条对到记号侧已证的定理. 记号: $\Omega=$ `Ωᵗ`, $\Omega_\Omega=$ `βᴱ`, `ctx y` $=\psi_0(\Omega_\Omega+y)$, $\eta_1=\psi_0(\Omega_\Omega+\psi_1(\Omega_1))$ (SystemOmega), $A$, $X_2$ 取自 Symbolic.

**H1 (符号尾只在 $\psi_0$ 处折叠).** 符号尾的参数 $b$ 共尾度为 $\Omega_1$, 即 `cof b ≡ cΩ []`. EBO 对 $\psi_u(b)$ 的派发是 `cofψ₊ u [] (cmpᵀ (sucT []) u)`, 而 `sucT [] = natT 1`. 下面证明: 对任意非空 $u$ (不要标准形), `cmpᵀ (natT 1) u` 不是 `gt`, 所以 $\psi_u(b)$ 的共尾度仍是 $\Omega_1$ (穿透), 且 $\psi_u(b)[\eta]=\psi_u(b[\eta])$ (逐点); $u=0$ 时是 `cω` (折叠). 奇异叶 $\Omega_\Omega$ 本身由 SystemOmega 的 `ΩΩlf` (`cof Ωᵗ ≡ cΩ []`, $\Omega_\Omega[\eta]=\Omega_\eta$) 与 `leafSb _ sing` 给出; 目标下标为 $\Omega+c$ 时是 `cmp-CΩ` (恒 `lt`).


```agda
H1-cmp : ∀ x xs → cmpᵀ (natT 1) (x ∷ xs) ≡ gt → ⊥
H1-cmp (ψᵗ [] [])      []      ()
H1-cmp (ψᵗ [] [])      (_ ∷ _) ()
H1-cmp (ψᵗ [] (_ ∷ _)) _       ()
H1-cmp (ψᵗ (_ ∷ _) _)  _       ()

H1-pen : ∀ x xs → cofA (x ∷ xs) (cΩ []) ≡ cΩ []
H1-pen x xs = go (cmpᵀ (natT 1) (x ∷ xs)) (H1-cmp x xs) where
  go : ∀ m → (m ≡ gt → ⊥) → cofψ₊ (x ∷ xs) [] m ≡ cΩ []
  go lt _ = refl
  go eq _ = refl
  go gt h = ⊥-elim (h refl)

H1-col : cofA [] (cΩ []) ≡ cω
H1-col = refl

H1-fsT : ∀ x xs y ys → cof (y ∷ ys) ≡ cΩ [] → ∀ η →
         fsT (ψᵗ (x ∷ xs) (y ∷ ys) ∷ []) η ≡ ψᵗ (x ∷ xs) (fsT (y ∷ ys) η) ∷ []
H1-fsT x xs y ys e η with cof (y ∷ ys) | e
... | .(cΩ []) | refl = go (cmpᵀ (natT 1) (x ∷ xs)) (H1-cmp x xs) where
  go : ∀ m → (m ≡ gt → ⊥) → fsTc (x ∷ xs) (y ∷ ys) [] m η ≡ ψᵗ (x ∷ xs) (fsT (y ∷ ys) η) ∷ []
  go lt _ = refl
  go eq _ = refl
  go gt h = ⊥-elim (h refl)
```


**读法.** H1 比 Symbolic 写的假设更强: 它对一切项成立, 不需要 `NF₁`. 树侧的对应是 §3 中 `ψᴾ` 对尾巴 `ŝ` 的子句不分目标层: 目标层非 0 时 `ŝ` 逐点穿透, 目标层 0 时同一个公式读作链.

**H2 (交替不变量的记号版).** Symbolic 的陈述: $\psi_0(C[\Omega_\Omega])$ 的上下文 $C$ 里的可数下标 $v$ 都 $<$ 第一个链点. 这正是 SystemOmega 的 `occ< : NF₁ t → Ctbl t → Occ x t → Ctbl x → x <ᵀ t` 用在链点 $t$ 上 ($C$ 的下标都出现在 $t=\psi_0(C[\Omega_{\gamma_k}])$ 里), 推论 `dominate` 对一切后代. 树侧真正需要的形式见 §8: 闭包的界是 $\delta+1$, 其中 $\psi_\delta$ **出现在**链点里, 所以要的就是 "出现的下标小于项". 实例: $A$ 的第 0 点 $\eta_1$ 里出现下标 $1$, `H2-η₁ : 1 <ᵀ η₁` (这是界为 $2$ 的闭包的 `d₀` 的记号侧).

**H3 (符号尾的共尾性).** 就是 StandardOmega 的 `cofin₁ : NF₁ u → cof u ≡ cω → NF₁ v → v <ᵀ u → Σ n. v <ᵀ fsn u n`, 无额外前提; $u=\psi_0(C[\Omega_\Omega])$ 时 `fsn u n` 是第 $n+1$ 个链点 (同 Stage2 的 `diag2-fs`). 实例 `H3-X₂`.


```agda
toη₁ : List ℕ
toη₁ = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ []

_ : SΩ.walk t2 toη₁ ≡ η₁
_ = refl

η₁-NF : NF₁ η₁
η₁-NF = diag₁-desc-NF (walkD d₀ᴰ toη₁ (refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt))

H2-η₁ : natT 1 <ᵀ η₁
H2-η₁ = occ< η₁-NF (c∷ c[]) (od (ot oh)) (c∷ c[])

toX₂ : List ℕ
toX₂ = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []

_ : SΩ.walk t2 toX₂ ≡ X₂ᵗ
_ = refl

X₂-NF : NF₁ X₂ᵗ
X₂-NF = diag₁-desc-NF (walkD d₀ᴰ toX₂ (refl , refl , refl , refl , refl , refl , tt))

H3-X₂ : ∀ {v} → NF₁ v → v <ᵀ X₂ᵗ → Σ ℕ λ n → v <ᵀ fsn X₂ᵗ n
H3-X₂ = cofin₁ X₂-NF refl
```


**H4** ($\psi_\Omega$ 栈帧的 `Bnd`) 未做: 只有 $\psi_0(\Omega_{\Omega+1})$ 需要它, 本文没有走到那里 (§10).

**读法.** 四条里三条已是记号侧定理, 本文只补了 H1 的一个小引理. 合并时的真正缺口在树侧: H2 的树版本 (§8).

## §2 新树族 (Symbolic §3 的修改版)

与 Symbolic §3 的区别, 都由 §3 的 $\psi^P$ 决定:

- `Z` (第 0 层的待计值树) 去掉 `oldz` 与 `ĉ`, 增加 `ĉᴸ c t₀ g o₀ o`: 链 ($t_0$, $g$) 与输出 ($o_0$, $o$) 分开, 值是 $\lim_n o(\chi_n)$. 它来自 "前缀 + 待计值的链" ($a+\lim\chi_n=\lim(a+\chi_n)$) 与 "$\psi$ 作用于第 0 层的待计值链" ($\psi(P+\lim\chi_n)=\lim\psi(P+\chi_n)$). Symbolic 的 `ĉ c t₀ g` 是 `ĉᴸ c t₀ g t₀ g`.
- 新族 `Ord₊ˢ` 去掉 `z0`: 第 0 层的 `ŝ` 就是待计值的链 (Symbolic 的 `ĉ`), 第 $\ge1$ 层的 `ŝ` 是 $\Omega_1$-共尾的符号对象. 两种读法用同一个构造子, 因为 $\psi_i$ 作用于 $\Omega_1$-共尾尾巴的结果在 $i\ge1$ 时是逐点穿透, 在 $i=0$ 时是以同一组点为链 (§1 的 H1), 公式相同.
- `toZ` 把第 0 层的新族树读成 `Z`.

```agda
data Z : Set where
  zero : Z
  suc  : Z → Z
  lim  : (ℕ → Z) → Z
  ĉᴸ   : (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Z
```


族本身: Level 的五个构造子, 加 `ŝ` 与 `ĉᴸ`; `Uˢ`, `outˢ`/`intoˢ`, `liftˢ` 照 Level. `toZ` 在 `limᵢ`/`up` 处是空模式 (第 0 层没有).


```agda
module _ (ℓ : Ordᴵ) (Uˢ : (i : Ordᴵ) → i ◃ ℓ → Set) where
  data Ord₊ˢ : Set where
    zero : Ord₊ˢ
    suc  : Ord₊ˢ → Ord₊ˢ
    lim  : (f : ℕ → Ord₊ˢ) → Ord₊ˢ
    limᵢ : ∀ {i} (p : i <ᴵ ℓ) (f : Uˢ i (<→◃ p) → Ord₊ˢ) → Ord₊ˢ
    up   : ∀ {k} (r : k ◃₁ ℓ) (x : Uˢ k (◃₁→◃ r)) → Ord₊ˢ
    ŝ    : (c : Ordᴵ) → Ord₊ˢ → ((η : Ordᴵ) → c ⊑ᴵ η → Ord₊ˢ) → Ord₊ˢ
    ĉᴸ   : (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Ord₊ˢ → ((η : Ordᴵ) → c ⊑ᴵ η → Ord₊ˢ) → Ord₊ˢ

Uˢ : ∀ {ℓ} (i : Ordᴵ) → i ◃ ℓ → Set
Uˢ i zero         = Ord₊ˢ i Uˢ
Uˢ i (suc r)      = Uˢ i r
Uˢ _ (self {f} n) = Ord₊ˢ (f n) Uˢ
Uˢ i (lim n r)    = Uˢ i r

Ordˢ : Ordᴵ → Set
Ordˢ ℓ = Ord₊ˢ ℓ Uˢ

outˢ : ∀ {i ℓ} (r : i ◃ ℓ) → Uˢ i r → Ordˢ i
outˢ zero      x = x
outˢ (suc r)   x = outˢ r x
outˢ (self n)  x = x
outˢ (lim n r) x = outˢ r x

intoˢ : ∀ {i ℓ} (r : i ◃ ℓ) → Ordˢ i → Uˢ i r
intoˢ zero      x = x
intoˢ (suc r)   x = intoˢ r x
intoˢ (self n)  x = x
intoˢ (lim n r) x = intoˢ r x

out-intoˢ : ∀ {i ℓ} (r : i ◃ ℓ) (x : Ordˢ i) → outˢ r (intoˢ r x) ≡ x
out-intoˢ zero      x = refl
out-intoˢ (suc r)   x = out-intoˢ r x
out-intoˢ (self n)  x = refl
out-intoˢ (lim n r) x = out-intoˢ r x

coeˢ : ∀ {i ℓ₁ ℓ₂} (r : i ◃ ℓ₁) (r′ : i ◃ ℓ₂) → Uˢ i r → Uˢ i r′
coeˢ r r′ x = intoˢ r′ (outˢ r x)

liftˢ : ∀ {k ℓ} → k ◃ ℓ → Ordˢ k → Ordˢ ℓ
liftˢ zero      x = up zero x
liftˢ (suc r)   x = up zero (liftˢ r x)
liftˢ (self n)  x = up (self n) x
liftˢ (lim n r) x = up (self n) (liftˢ r x)

toZ : Ordˢ zero → Z
toZ zero             = zero
toZ (suc x)          = suc (toZ x)
toZ (lim f)          = lim (λ n → toZ (f n))
toZ (limᵢ () f)
toZ (up () x)
toZ (ŝ c t₀ g)       = ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (toZ t₀) (λ η e → toZ (g η e))
toZ (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (toZ o₀) (λ η e → toZ (o η e))
```


严格正性与 `Uˢ` 的停机照 Level 通过 (新构造子的分支以 `Ord₊ˢ` 或先定义的 `Z` 为值域, 定义域是先定义的 `Ordᴵ` 与 $\sqsubseteq^\mathsf I$).

**搬运.** `trˢ`/`tr⁻ˢ`/`resˢ`/`res⁻ˢ` 与 Level §4 逐字, 新构造子逐点 (`ĉᴸ` 的链在 `Z` 里, 不动).


```agda
record Restrˢ (j b : Ordᴵ) : Set where
  constructor restrˢ
  field
    {repˢ} : Ordᴵ
    eqˢ    : j ≅ᴵ repˢ
    ltˢ    : repˢ <ᴵ b
    backˢ  : Ordˢ repˢ → Ordˢ j
open Restrˢ

trˢ   : ∀ {a b} → a ≅ᴵ b → Ordˢ a → Ordˢ b
tr⁻ˢ  : ∀ {a b} → a ≅ᴵ b → Ordˢ b → Ordˢ a
resˢ  : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → Restrˢ j b
res⁻ˢ : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → Restrˢ j a

trˢ e zero    = zero
trˢ e (suc x) = suc (trˢ e x)
trˢ e (lim f) = lim (λ n → trˢ e (f n))
trˢ e (limᵢ q f) = limᵢ (ltˢ (resˢ q e)) (λ y → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) y)))))
trˢ (s≅ e) (up zero x)     = up zero (trˢ e x)
trˢ (l≅ h) (up (self n) x) = up (self n) (trˢ (h n) x)
trˢ e (ŝ c t₀ g)       = ŝ c (trˢ e t₀) (λ η d → trˢ e (g η d))
trˢ e (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (trˢ e o₀) (λ η d → trˢ e (o η d))

tr⁻ˢ e zero    = zero
tr⁻ˢ e (suc x) = suc (tr⁻ˢ e x)
tr⁻ˢ e (lim f) = lim (λ n → tr⁻ˢ e (f n))
tr⁻ˢ e (limᵢ q f) = limᵢ (ltˢ (res⁻ˢ q e)) (λ y → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) y)))))
tr⁻ˢ (s≅ e) (up zero x)     = up zero (tr⁻ˢ e x)
tr⁻ˢ (l≅ h) (up (self n) x) = up (self n) (tr⁻ˢ (h n) x)
tr⁻ˢ e (ŝ c t₀ g)       = ŝ c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
tr⁻ˢ e (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (tr⁻ˢ e o₀) (λ η d → tr⁻ˢ e (o η d))

resˢ zero      (s≅ e) = restrˢ e zero (tr⁻ˢ e)
resˢ (suc q)   (s≅ e) = restrˢ (eqˢ (resˢ q e)) (suc (ltˢ (resˢ q e))) (backˢ (resˢ q e))
resˢ (lim n q) (l≅ h) = restrˢ (eqˢ (resˢ q (h n))) (lim n (ltˢ (resˢ q (h n)))) (backˢ (resˢ q (h n)))

res⁻ˢ zero      (s≅ e) = restrˢ (≅ᴵ-sym e) zero (trˢ e)
res⁻ˢ (suc q)   (s≅ e) = restrˢ (eqˢ (res⁻ˢ q e)) (suc (ltˢ (res⁻ˢ q e))) (backˢ (res⁻ˢ q e))
res⁻ˢ (lim n q) (l≅ h) = restrˢ (eqˢ (res⁻ˢ q (h n))) (lim n (ltˢ (res⁻ˢ q (h n)))) (backˢ (res⁻ˢ q (h n)))
```


**$\Omega$ 与加法.** `Ωˢ` 逐字. `addˢ` 的新子句: 尾巴 `ŝ` 在第 0 层 (待计值的链) 时, $a+\lim\chi_n$ 成为 `ĉᴸ` (链不动, 输出加 $a$); 在第 $\ge1$ 层时逐点. 这里按尾巴的层号 `k` 分情况 (隐式参数用具名模式 `{k = zero}`; 写成 `{zero}` 在 `--hidden-argument-puns` 下报 `[InvalidPun.Constructor] A pun must not use the constructor zero`).


```agda
Ωˢ : (ℓ : Ordᴵ) → Ordˢ ℓ
Ωˢ zero      = suc zero
Ωˢ (suc ℓ)   = limᵢ zero (up zero)
Ωˢ (lim f s) = lim (λ n → up (self n) (Ωˢ (f n)))

addˢ : ∀ {k ℓ} → Ordˢ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ ℓ
addˢ a σ zero              = a
addˢ a σ (suc b)           = suc (addˢ a σ b)
addˢ a σ (lim f)           = lim (λ n → addˢ a σ (f n))
addˢ a σ (limᵢ q f)        = limᵢ (σ q) (λ y → addˢ a σ (f (coeˢ (<→◃ (σ q)) (<→◃ q) y)))
addˢ a σ (up zero x)       = addˢ a (λ q → σ (suc q)) x
addˢ a σ (up (self n) x)   = addˢ a (λ q → σ (lim n q)) x
addˢ {k = zero}    a σ (ŝ c t₀ g) = ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
addˢ {k = suc _}   a σ (ŝ c t₀ g) = ŝ c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
addˢ {k = lim _ _} a σ (ŝ c t₀ g) = ŝ c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
addˢ a σ (ĉᴸ c t₀ g o₀ o)  = ĉᴸ c t₀ g (addˢ a σ o₀) (λ η e → addˢ a σ (o η e))

infixl 6 _+ˢ_
_+ˢ_ : ∀ {ℓ} → Ordˢ ℓ → Ordˢ ℓ → Ordˢ ℓ
a +ˢ b = addˢ a (λ q → q) b
```


## §3 前缀栈折叠 $\psi^P$

**栈帧与栈.** 帧两种: `fΩ̂ z` (一个 $\Omega_\Omega$ 被加数, $z:0<^\mathsf I\ell$ 让第 0 点的 $\Omega_1$ 留在层 $\ell$) 与 `fT x σ` (可数层的树前缀). 栈是 `Vec (Frame ℓ) n`. `liftV` 把整个栈经一个 `Sim` 搬到别的层号 (长度不变).

**紧的界 `rebase`.** 弹出 $\hat\Omega$ 时要造闭包 `ŝ c t₀ g`, $g\,\eta\,e=\psi_i(P'+\Omega_\eta)$ 在公共层号 `Mlev c η e` 上计算. Symbolic §10 取 $c=\ell$ (环境层号). 本文取紧的界: 剩余栈 $P'$ 只含 $\hat\Omega$ 帧时 (阶段 2 的标准形只会产生这种栈: $\Omega_\Omega$ 被加数在和里排在一切更小的项之前), $c=i+1$, 栈在 $c$ 上重建; 否则退回 $c=\ell$. $0<^\mathsf I i+1$ 由 $z$ 与 $p$ 经有界三歧性得到 (`z<suc`; $0\cong^\mathsf I a'$ 迫使 $a'$ 字面为 `zero`). 为什么必须紧, 见 §7.


```agda
data Frame (ℓ : Ordᴵ) : Set where
  fΩ̂ : zero <ᴵ ℓ → Frame ℓ
  fT  : ∀ {k} → Ordˢ k → Simᴵ k ℓ → Frame ℓ

liftF : ∀ {ℓ ℓ′} → Simᴵ ℓ ℓ′ → Frame ℓ → Frame ℓ′
liftF ρ (fΩ̂ z)   = fΩ̂ (ρ z)
liftF ρ (fT x σ) = fT x (λ q → ρ (σ q))

liftV : ∀ {ℓ ℓ′ n} → Simᴵ ℓ ℓ′ → Vec (Frame ℓ) n → Vec (Frame ℓ′) n
liftV ρ []      = []
liftV ρ (f ∷ P) = liftF ρ f ∷ liftV ρ P

onlyΩ̂ : ∀ {ℓ n} → Vec (Frame ℓ) n → Bool
onlyΩ̂ []           = true
onlyΩ̂ (fΩ̂ _ ∷ P)   = onlyΩ̂ P
onlyΩ̂ (fT _ _ ∷ P) = false

z<suc : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → zero <ᴵ suc i
z<suc z p with <ᴵ-dec z p
... | injᵃ (via z≅ r) = suc r
... | injᵇ (via e ())
... | injᶜ z≅ = zero

record Base (i : Ordᴵ) (n : ℕ) : Set where
  constructor base
  field
    cb  : Ordᴵ
    tgt : i <ᴵ cb
    stk : Vec (Frame cb) n
    one : zero <ᴵ cb
open Base

rebase′ : ∀ {i ℓ n} → Bool → i <ᴵ ℓ → zero <ᴵ ℓ → Vec (Frame ℓ) n → Base i n
rebase′ {i} {n = n} true  p z P = base (suc i) zero (replicate n (fΩ̂ (z<suc z p))) (z<suc z p)
rebase′ {ℓ = ℓ}    false p z P = base ℓ p P z

rebase : ∀ {i ℓ n} → i <ᴵ ℓ → zero <ᴵ ℓ → Vec (Frame ℓ) n → Base i n
rebase p z P = rebase′ (onlyΩ̂ P) p z P
```


**折叠.** $\psi^P$ 的参数: 栈长 $n$ (显式), 目标证明 $p:i<^\mathsf I\ell$, 尾巴的 `Sim`, 栈, 尾巴. 子句:

- 尾巴 `suc`/`lim`/`limᵢ`/`up`: 照 Level 的 `ψ`, 栈原样携带. 规则 6 的链在节点层 $j$ 上, 链点是 $\psi^P_{\sigma q}(f\,x)$: **目标层 $j$, 同一个栈**. EBO 的规则 6 是 $\gamma_{k+1}=\psi_j(b[\gamma_k])$, $b$ 含整个前缀 (Symbolic 的 `X₂-at-A` 路径: $X_2[1]$ 的链点是 $\psi_1(\Omega_\Omega+\cdots)$, 前缀在 $\psi_1$ 里面).
- 尾巴 `ŝ c t₀ g`: 第 0 层尾巴 (待计值的链) 时产生 `ĉᴸ` (链不动, 输出逐点折叠); 第 $\ge1$ 层时逐点, 不分目标层.
- 尾巴 `ĉᴸ`: 输出逐点折叠.
- 尾巴 `zero`: 空栈给 $\Omega_i$; 栈顶 `fT x σ′` 弹出, 对 $x$ 继续; 栈顶 `fΩ̂ z` 弹出, 产生 `ŝ c t₀ g`, $t_0=\psi^{P'}(\Omega_1)$ (在 $c$ 上, 栈重建), $g\,\eta\,e=\psi^{P'\uparrow}_{\texttt{lim 0}\,t}(\Omega_\eta)$ (栈经 `lim 0` 搬到 `Mlev c η e`, $\Omega_\eta$ 经 `lim 1` 进入).


```agda
ψᴾ : ∀ (n : ℕ) {i k ℓ} → i <ᴵ ℓ → Simᴵ k ℓ → Vec (Frame ℓ) n → Ordˢ k → Ordˢ i
ψᴾ n p σ P (suc a) = lim (iter (ψᴾ n p σ P a +ˢ_) zero)
ψᴾ n p σ P (lim f) = lim (λ m → ψᴾ n p σ P (f m))
ψᴾ n p σ P (limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = limᵢ r (λ y → ψᴾ n p σ P (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = lim (λ m → ψᴾ n p σ P (f (intoˢ (<→◃ q) (iter (λ x → ψᴾ n (σ q) σ P (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = lim (λ m → ψᴾ n p σ P (f (intoˢ (<→◃ q) (iter (λ x → ψᴾ n (σ q) σ P (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψᴾ n p σ P (up zero x)     = ψᴾ n p (λ q → σ (suc q)) P x
ψᴾ n p σ P (up (self m) x) = ψᴾ n p (λ q → σ (lim m q)) P x
ψᴾ n {k = zero}    p σ P (ŝ c t₀ g) = ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψᴾ n p σ P t₀) (λ η e → ψᴾ n p σ P (g η e))
ψᴾ n {k = suc _}   p σ P (ŝ c t₀ g) = ŝ c (ψᴾ n p σ P t₀) (λ η e → ψᴾ n p σ P (g η e))
ψᴾ n {k = lim _ _} p σ P (ŝ c t₀ g) = ŝ c (ψᴾ n p σ P t₀) (λ η e → ψᴾ n p σ P (g η e))
ψᴾ n p σ P (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (ψᴾ n p σ P o₀) (λ η e → ψᴾ n p σ P (o η e))
ψᴾ zero    p σ []            zero = Ωˢ _
ψᴾ (suc n) p σ (fT x σ′ ∷ P) zero = ψᴾ n p σ′ P x
ψᴾ (suc n) p σ (fΩ̂ z ∷ P)    zero =
  ŝ (cb B) (ψᴾ n (tgt B) (σ1 (one B)) (stk B) (Ωˢ (suc zero)))
           (λ η e → ψᴾ n {ℓ = Mlev (cb B) η e} (lim 0 (tgt B)) (λ q → lim 1 q) (liftV (λ q → lim 0 q) (stk B)) (Ωˢ η))
  where B = rebase p z P
```


**停机.** 一次通过. 弹栈的两个调用 $n$ 下降 (尾巴是全新的树 $x$, $\Omega_1$, $\Omega_\eta$, 栈是重建的), 其余调用 $n$ 不变而尾巴是结构子项或 `f` 的值; 检查器自己找到 ($n$, 尾巴) 的字典序. `with` 生成的辅助函数 (派发) 不碍事. `ψᴾ (suc n) … (fΩ̂ z ∷ P) zero` 的 `where B = rebase p z P` 也不碍事 (没有 `subst`).

**否定: 栈用 `List`.** 同样的子句, 栈换成 `List (Frame ℓ)`、弹出 $\hat\Omega$ 时用 `map (liftF (λ q → lim 0 q)) P` (临时文件 `PL.agda`, 不进本文):

    [TerminationIssue]
    Termination checking failed for the following functions:
      ψᴸ
    Problematic calls:
      ψᴸ p σ P (limᵢ q f) | <ᴵ-dec (σ q) p
      ψᴸ (σ q) σ P (f (intoˢ (<→◃ q) x))
      ψᴸ (lim 0 p) (lim 1) (map (liftF (lim 0)) P) (Ωˢ η)

最后一个调用: `map …` 不是 `fΩ̂ z ∷ P` 的子项, 尾巴 `Ωˢ η` 也不是. 这就是 Symbolic §10 预言的 (提升后的栈是 `map`); 以长度为下标后, 下降的是 $n$.


## §4 `Goodᶻ`/`force` 对 `ĉᴸ`

Symbolic §5 的归纳-递归证书, `gc` 现在给 `ĉᴸ`: 前六个字段是链的 (与 Symbolic 的 `Ctx` 同), 后四个是输出的 (好性与单调). `force (ĉᴸ …)` 是 $\lim_n$ `outs`: 第 0 项是 $o_0$, 第 $k+1$ 项是 $o$ 在第 $k$ 个链点的层号处的值 (支配证据由链点携带). 证书 `force-HS` 的步进: 第 0 步是 $o_0\sqsubseteq o(\cdot)$, 其后用 $o$ 的单调与链点层号的一步 (`toLevel-⊑ … (χᶜ-step C k)`).


```agda
outs : (C : Ctx) → Ordᶜ zero → ((η : Ordᴵ) → Ctx.c C ⊑ᴵ η → Ordᶜ zero) → ℕ → Ordᶜ zero
outs C O₀ O zero    = O₀
outs C O₀ O (suc k) = O (lvP C (Γᶜ C k)) (Pt.dx (Γᶜ C k))

outs-HS : (C : Ctx) {O₀ : Ordᶜ zero} {O : (η : Ordᴵ) → Ctx.c C ⊑ᴵ η → Ordᶜ zero} →
          HS O₀ → (∀ η e → HS (O η e)) → ∀ n → HS (outs C O₀ O n)
outs-HS C h₀ h zero    = h₀
outs-HS C h₀ h (suc k) = h _ _

outs-step : (C : Ctx) {O₀ : Ordᶜ zero} {O : (η : Ordᴵ) → Ctx.c C ⊑ᴵ η → Ordᶜ zero} →
            (∀ η e → O₀ ⊑⁰ O η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → O η e ⊑⁰ O η′ e′) →
            ∀ n → outs C O₀ O n ⊑⁰ outs C O₀ O (suc n)
outs-step C m₀ m zero    = m₀ _ _
outs-step C m₀ m (suc k) = m _ _ _ _ (toLevel-⊑ (Pt.hx (Γᶜ C k)) (Pt.hx (Γᶜ C (suc k))) (χᶜ-step C k))

data Goodᶻ : Z → Set
force    : (x : Z) → Goodᶻ x → Ordᶜ zero
force-HS : (x : Z) (G : Goodᶻ x) → HS (force x G)

data Goodᶻ where
  gz : Goodᶻ zero
  gs : ∀ {x} → Goodᶻ x → Goodᶻ (suc x)
  gl : ∀ {f : ℕ → Z} (G : ∀ n → Goodᶻ (f n)) →
       (∀ n → force (f n) (G n) ⊑⁰ force (f (suc n)) (G (suc n))) → Goodᶻ (lim f)
  gc : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z}
       (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
       c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
       (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
       (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
       (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
       (Go₀ : Goodᶻ o₀) (Go : ∀ η e → Goodᶻ (o η e)) →
       (∀ η e → force o₀ Go₀ ⊑⁰ force (o η e) (Go η e)) →
       (∀ η e η′ e′ → η ⊑ᴵ η′ → force (o η e) (Go η e) ⊑⁰ force (o η′ e′) (Go η′ e′)) →
       Goodᶻ (ĉᴸ c t₀ g o₀ o)

force zero    gz        = zero
force (suc x) (gs G)    = suc (force x G)
force (lim f) (gl G st) = lim (λ n → force (f n) (G n))
force (ĉᴸ c t₀ g o₀ o) (gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lim (outs (record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
                    ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
                    ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE })
            (force o₀ Go₀) (λ η e → force (o η e) (Go η e)))

force-HS zero    gz        = hz
force-HS (suc x) (gs G)    = hs (force-HS x G)
force-HS (lim f) (gl G st) = hl (λ n → force-HS (f n) (G n)) st
force-HS (ĉᴸ c t₀ g o₀ o) (gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  hl (outs-HS C (force-HS o₀ Go₀) (λ η e → force-HS (o η e) (Go η e)))
     (outs-step C mo₀ mo)
  where C = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
                   ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
                   ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }

-- the pure chain (o = g) is literally Symbolic's Tᶜ
module _ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) d₀ dE m₀ mE where
  Cᶻ : Ctx
  Cᶻ = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
              ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
              ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }

  force-chain : ∀ n → outs Cᶻ (force t₀ G₀) (λ η e → force (g η e) (Gg η e)) n ≡ χᶜ Cᶻ n
  force-chain zero    = refl
  force-chain (suc n) = refl

  _ : force (ĉᴸ c t₀ g t₀ g) (gc G₀ Gg d₀ dE m₀ mE G₀ Gg m₀ mE) ≡ lim (outs Cᶻ (force t₀ G₀) (λ η e → force (g η e) (Gg η e)))
  _ = refl
```


**读法.** 停机与 Symbolic 相同 (`force` 对 `Z` 结构递归). `force-chain`: 纯链的输出逐项就是 Symbolic 的 `χᶜ` (`refl`); `lim` 的两种写法只差函数外延性, 所以整体只到逐项.

## §5 空栈与 Level 的 $\psi$: 异族互模拟

$\psi^P$ 的空栈片段在无符号节点的树上应当就是 Level 的 $\psi$. 两个族不同 (新族的 `limᵢ` 分支吃新族的树), 所以需要一个**异族**互模拟 `x ~ y` ($x$ 在新族, $y$ 在 Level 的族), 形状照 Level §5 的 `Eq₊`/`R`, 只是左右两边换了族; 不含 `ŝ`/`ĉᴸ` (无符号片段).


```agda
module _ (ℓ : Ordᴵ) (Rh : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set) where
  data H₊ : ∀ {ℓ′} → Ordˢ ℓ → Ordᶜ ℓ′ → Set where
    z~  : ∀ {ℓ′} → H₊ {ℓ′} zero zero
    s~  : ∀ {ℓ′} {a : Ordˢ ℓ} {b : Ordᶜ ℓ′} → H₊ a b → H₊ (suc a) (suc b)
    l~  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordᶜ ℓ′} → (∀ n → H₊ (f n) (g n)) → H₊ (lim f) (lim g)
    lᵢ~ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} {g : U j′ (<→◃ q) → Ordᶜ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordˢ j) (y : Ordᶜ j′) → Rh j (<→◃ p) (intoˢ (<→◃ p) x) y → H₊ (f (intoˢ (<→◃ p) x)) (g (into (<→◃ q) y))) →
          H₊ (limᵢ p f) (limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → Rh k (◃₁→◃ r) x b → H₊ (up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : U k (◃₁→◃ r)} {a : Ordˢ ℓ} → H₊ a (out (◃₁→◃ r) y) → H₊ a (up r y)

Rh : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set
Rh i zero         x b = H₊ i Rh x b
Rh i (suc r)      x b = Rh i r x b
Rh _ (self {f} n) x b = H₊ (f n) Rh x b
Rh i (lim n r)    x b = Rh i r x b

infix 4 _~_
_~_ : ∀ {ℓ₁ ℓ₂} → Ordˢ ℓ₁ → Ordᶜ ℓ₂ → Set
_~_ {ℓ₁} = H₊ ℓ₁ Rh

Rh→~ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordᶜ ℓ′} → Rh i r (intoˢ r x) b → x ~ b
Rh→~ zero      e = e
Rh→~ (suc r)   e = Rh→~ r e
Rh→~ (self n)  e = e
Rh→~ (lim n r) e = Rh→~ r e

~→Rh : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordᶜ ℓ′} → x ~ b → Rh i r (intoˢ r x) b
~→Rh zero      e = e
~→Rh (suc r)   e = ~→Rh r e
~→Rh (self n)  e = e
~→Rh (lim n r) e = ~→Rh r e
```


**搬运在两边都不可见.** 左边 (新族) 的 `trˢ-~` 等四个与 Level 的 `tr-≅` 组逐字同构. 右边 (旧族) 没有对称性可借 (异族关系不对称), 所以 `~-tr`/`~-tr⁻`/`~-back`/`~-back⁻` 直接对推导递归: `limᵢ` 情形把右边的节点搬到代表元上, 新分支经 `back`; `upʳ` 情形拆开 $\cong^\mathsf I$ 的证明一层. 停机度量 ($\cong^\mathsf I$ 证明, 推导), 一次通过.


```agda
-- 新族一侧的搬运不可见
trˢ-~    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ a} {y : Ordᶜ ℓ′} → x ~ y → trˢ e x ~ y
tr⁻ˢ-~   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ b} {y : Ordᶜ ℓ′} → x ~ y → tr⁻ˢ e x ~ y
backˢ-~  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {v : Ordᶜ ℓ′} → u ~ v → backˢ (resˢ q e) u ~ v
back⁻ˢ-~ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {v : Ordᶜ ℓ′} → u ~ v → backˢ (res⁻ˢ q e) u ~ v

trˢ-~ e z~      = z~
trˢ-~ e (s~ d)  = s~ (trˢ-~ e d)
trˢ-~ e (l~ h)  = l~ (λ n → trˢ-~ e (h n))
trˢ-~ e (lᵢ~ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej) λ u v d →
    subst (λ w → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ~ g (into (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
          (trˢ-~ e (h _ v (~→Rh (<→◃ q) (backˢ-~ q e (Rh→~ (<→◃ (ltˢ (resˢ q e))) d)))))
trˢ-~ (s≅ e) (upˡ {r = zero} d)   = upˡ (trˢ-~ e d)
trˢ-~ (l≅ h) (upˡ {r = self n} d) = upˡ (trˢ-~ (h n) d)
trˢ-~ e (upʳ d) = upʳ (trˢ-~ e d)

tr⁻ˢ-~ e z~      = z~
tr⁻ˢ-~ e (s~ d)  = s~ (tr⁻ˢ-~ e d)
tr⁻ˢ-~ e (l~ h)  = l~ (λ n → tr⁻ˢ-~ e (h n))
tr⁻ˢ-~ e (lᵢ~ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej) λ u v d →
    subst (λ w → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ~ g (into (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
          (tr⁻ˢ-~ e (h _ v (~→Rh (<→◃ q) (back⁻ˢ-~ q e (Rh→~ (<→◃ (ltˢ (res⁻ˢ q e))) d)))))
tr⁻ˢ-~ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr⁻ˢ-~ e d)
tr⁻ˢ-~ (l≅ h) (upˡ {r = self n} d) = upˡ (tr⁻ˢ-~ (h n) d)
tr⁻ˢ-~ e (upʳ d) = upʳ (tr⁻ˢ-~ e d)

backˢ-~ zero      (s≅ e) d = tr⁻ˢ-~ e d
backˢ-~ (suc q)   (s≅ e) d = backˢ-~ q e d
backˢ-~ (lim n q) (l≅ h) d = backˢ-~ q (h n) d

back⁻ˢ-~ zero      (s≅ e) d = trˢ-~ e d
back⁻ˢ-~ (suc q)   (s≅ e) d = back⁻ˢ-~ q e d
back⁻ˢ-~ (lim n q) (l≅ h) d = back⁻ˢ-~ q (h n) d

-- 旧族一侧的搬运不可见
~-tr    : ∀ {a b ℓ} (e : a ≅ᴵ b) {x : Ordˢ ℓ} {y : Ordᶜ a} → x ~ y → x ~ tr e y
~-tr⁻   : ∀ {a b ℓ} (e : a ≅ᴵ b) {x : Ordˢ ℓ} {y : Ordᶜ b} → x ~ y → x ~ tr⁻ e y
~-back  : ∀ {j a b ℓ} (q : j <ᴵ a) (e : a ≅ᴵ b) {x : Ordˢ ℓ} {u : Ordᶜ (rep (res q e))} → x ~ u → x ~ back (res q e) u
~-back⁻ : ∀ {j a b ℓ} (q : j <ᴵ b) (e : a ≅ᴵ b) {x : Ordˢ ℓ} {u : Ordᶜ (rep (res⁻ q e))} → x ~ u → x ~ back (res⁻ q e) u

~-tr e z~     = z~
~-tr e (s~ d) = s~ (~-tr e d)
~-tr e (l~ h) = l~ (λ n → ~-tr e (h n))
~-tr e (lᵢ~ {p = p} {q = q} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans ej (eqᴿ (res q e))) λ x v d →
    subst (λ w → f (intoˢ (<→◃ p) x) ~ tr e (g (into (<→◃ q) (back (res q e) w))))
          (sym (out-into (<→◃ (ltᴿ (res q e))) v))
          (~-tr e (h x _ (~→Rh (<→◃ p) (~-back q e (Rh→~ (<→◃ p) d)))))
~-tr e (upˡ {r = zero} d)   = upˡ (~-tr e d)
~-tr e (upˡ {r = self n} d) = upˡ (~-tr e d)
~-tr (s≅ e) (upʳ {r = zero} d)   = upʳ (~-tr e d)
~-tr (l≅ h) (upʳ {r = self n} d) = upʳ (~-tr (h n) d)

~-tr⁻ e z~     = z~
~-tr⁻ e (s~ d) = s~ (~-tr⁻ e d)
~-tr⁻ e (l~ h) = l~ (λ n → ~-tr⁻ e (h n))
~-tr⁻ e (lᵢ~ {p = p} {q = q} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans ej (eqᴿ (res⁻ q e))) λ x v d →
    subst (λ w → f (intoˢ (<→◃ p) x) ~ tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) w))))
          (sym (out-into (<→◃ (ltᴿ (res⁻ q e))) v))
          (~-tr⁻ e (h x _ (~→Rh (<→◃ p) (~-back⁻ q e (Rh→~ (<→◃ p) d)))))
~-tr⁻ e (upˡ {r = zero} d)   = upˡ (~-tr⁻ e d)
~-tr⁻ e (upˡ {r = self n} d) = upˡ (~-tr⁻ e d)
~-tr⁻ (s≅ e) (upʳ {r = zero} d)   = upʳ (~-tr⁻ e d)
~-tr⁻ (l≅ h) (upʳ {r = self n} d) = upʳ (~-tr⁻ (h n) d)

~-back zero      (s≅ e) d = ~-tr⁻ e d
~-back (suc q)   (s≅ e) d = ~-back q e d
~-back (lim n q) (l≅ h) d = ~-back q (h n) d

~-back⁻ zero      (s≅ e) d = ~-tr e d
~-back⁻ (suc q)   (s≅ e) d = ~-back⁻ q e d
~-back⁻ (lim n q) (l≅ h) d = ~-back⁻ q (h n) d
```


**$\Omega$, 加法, 折叠.** `Ω~`, `add~` 与 Level 的 `Ω-≅`, `add-≅` 同形. `ψ~` 是 Level 的 `ψ-≅` 的异族版: 目标层只需 $\cong^\mathsf I$, 派发不一致的四种组合由 Level 的 `clash₁`/`clash₂` 排除, 两边都穿透时分支经 `tr⁻ˢ-~` 与 `~-tr⁻` 对上, 两边都折叠时链逐项相关 (`iter-R`).


```agda
Ω~ : ∀ {a b} → a ≅ᴵ b → Ωˢ a ~ Ω b
Ω~ z≅     = s~ z~
Ω~ (s≅ e) = lᵢ~ e (λ x y d → upˡ (upʳ d))
Ω~ (l≅ h) = l~ (λ n → upˡ (upʳ (Ω~ (h n))))

add~ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ ℓ₁} {a′ : Ordᶜ ℓ₂} {b : Ordˢ k₁} {b′ : Ordᶜ k₂} →
       a ~ a′ → b ~ b′ → addˢ a σ b ~ add a′ σ′ b′
add~ ea z~     = ea
add~ ea (s~ e) = s~ (add~ ea e)
add~ ea (l~ h) = l~ (λ n → add~ ea (h n))
add~ ea (upˡ {r = zero} e)   = add~ ea e
add~ ea (upˡ {r = self n} e) = add~ ea e
add~ ea (upʳ {r = zero} e)   = add~ ea e
add~ ea (upʳ {r = self n} e) = add~ ea e
add~ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} ea (lᵢ~ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢ~ e λ x y d →
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ~ add a′ σ′ (g (into (<→◃ q′) v)))
         (sym (out-intoˢ (<→◃ (σ q)) x)) (sym (out-into (<→◃ (σ′ q′)) y))
         (add~ ea (h x y (~→Rh (<→◃ q) (Rh→~ (<→◃ (σ q)) d))))

ψ~ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
     {a : Ordˢ k₁} {b : Ordᶜ k₂} → i ≅ᴵ i′ → a ~ b → ψᴾ 0 p σ [] a ~ ψ p′ σ′ b
ψ~ ei z~ = Ω~ ei
ψ~ ei (s~ e) = l~ (iter-R _~_ (λ e′ → add~ (ψ~ ei e) e′) z~)
ψ~ ei (l~ h) = l~ (λ n → ψ~ ei (h n))
ψ~ ei (upˡ {r = zero} e)   = ψ~ ei e
ψ~ ei (upˡ {r = self n} e) = ψ~ ei e
ψ~ ei (upʳ {r = zero} e)   = ψ~ ei e
ψ~ ei (upʳ {r = self n} e) = ψ~ ei e
ψ~ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} ei (lᵢ~ {p = q} {q = q′} {f = f} {g = g} e h)
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ~ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψᴾ 0 p σ [] (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ~ ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-into (<→◃ r₂) y))
         (ψ~ ei (h _ _ (~→Rh (<→◃ q) (tr⁻ˢ-~ e₁ (~-tr⁻ e₂ (Rh→~ (<→◃ r₁) d))))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
... | injᵇ _ | injᶜ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
... | injᶜ _ | injᵇ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
... | injᶜ _ | injᶜ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
```


**第 0 层.** `force~`: 相关的第 0 层树, 新族一侧对任意证书计值后 $\cong$ 旧树. `plainGood`: 旧树有 `HS` 时新树有 `Goodᶻ` (步进经 $\cong$ 搬过来; `HS-≅` 是 `HS` 对 $\cong$ 的不变性). 推论: 空栈的 $\psi^P_0(\Omega_a)$ 计值后 $\cong\psi^0(\Omega_a)$ (`empty-agree`, 经 Level 的 `ψ⁰≅ψ`), 且有证书 (`empty-good`, 由 Uniform).


```agda
-- 第 0 层: 计值与旧树互模拟, 且无符号节点的输出有 Goodᶻ
force~ : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} → x ~ y → (G : Goodᶻ (toZ x)) → force (toZ x) G ≅ y
force~ z~     gz        = z≅
force~ (s~ d) (gs G)    = s≅ (force~ d G)
force~ (l~ h) (gl G st) = l≅ (λ n → force~ (h n) (G n))
force~ (lᵢ~ {p = ()} e h) G
force~ (upˡ {r = ()} e) G
force~ (upʳ {r = ()} e) G

HS-≅ : ∀ {x y : Ordᶜ zero} → x ≅ y → HS x → HS y
HS-≅ z≅     hz        = hz
HS-≅ (s≅ e) (hs h)    = hs (HS-≅ e h)
HS-≅ (l≅ k) (hl h st) = hl (λ n → HS-≅ (k n) (h n)) (λ n → ⊑-trans (≅→⊑ (≅-sym (k n))) (⊑-trans (st n) (≅→⊑ (k (suc n)))))
HS-≅ (lᵢ≅ {p = ()} e k) h
HS-≅ (upˡ {r = ()} e) h
HS-≅ (upʳ {r = ()} e) h

plainGood : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} → x ~ y → HS y → Goodᶻ (toZ x)
plainGood z~     hz        = gz
plainGood (s~ d) (hs h)    = gs (plainGood d h)
plainGood (l~ k) (hl h st) = gl (λ n → plainGood (k n) (h n))
  (λ n → ⊑-trans (≅→⊑ (force~ (k n) _)) (⊑-trans (st n) (≅→⊑ (≅-sym (force~ (k (suc n)) _)))))
plainGood (lᵢ~ {p = ()} e k) h
plainGood (upˡ {r = ()} e) h
plainGood (upʳ {r = ()} e) h

empty~ : ∀ {i ℓ a} (p : i <ᴵ ℓ) (σ : Simᴵ a ℓ) → ψᴾ 0 p σ [] (Ωˢ a) ~ ψ p σ (Ω a)
empty~ p σ = ψ~ (≅ᴵ-refl _) (Ω~ (≅ᴵ-refl _))

empty-agree : ∀ {ℓ a} (p : zero <ᴵ ℓ) (σ : Simᴵ a ℓ) (G : Goodᶻ (toZ (ψᴾ 0 p σ [] (Ωˢ a)))) →
              force (toZ (ψᴾ 0 p σ [] (Ωˢ a))) G ≅ ψ⁰ (Ω a)
empty-agree {a = a} p σ G = ≅-trans (force~ (empty~ p σ) G) (≅-sym (ψ⁰≅ψ {p = p} {σ = σ} (Ω-refl a)))

empty-good : ∀ {ℓ a} (p : zero <ᴵ ℓ) (σ : Simᴵ a ℓ) → Goodᶻ (toZ (ψᴾ 0 p σ [] (Ωˢ a)))
empty-good {a = a} p σ = plainGood (empty~ p σ) (HS-≅ (ψ⁰≅ψ {p = p} {σ = σ} (Ω-refl a)) (Uniform a))
```


**读法.** 这是任务要求的空栈健全性: 不是只对 $\Omega$ 输入, 而是对一切与旧树相关的无符号输入 (`ψ~`); 字面 `refl` 不可能 (两个族的 `lim` 下的函数不同), 结论模 $\cong$.

## §6 检验 1: $\psi^{[\hat\Omega]}(0)$ 的计值就是 `BTBOᴵ`

弹出唯一的 $\hat\Omega$ (目标层 0) 字面上给出闭包 `β₀`: 界 $c=1$, 第 0 点 $\psi^{[]}_0(\Omega_1)$, 在 $\eta$ 处为 $\psi^{[]}_0(\Omega_\eta)$ (层号 `Mlev 1 η e`). 与环境层号无关 (这里取 $\ell=2$; `rebase` 的 `z<suc` 在具体证明上算出 `zero`). 证书的十个字段: 好性来自 §5 的 `empty-good`; 支配 $1\sqsubseteq^\mathsf I$ 层号来自 Stage2 的 `one⊑`; 单调经 `empty-agree` 化为 Level 的 `Ψ⁰-mono`. `βˢ≅` 对**任意**证书成立: 链点逐个 $\cong$ NoCumsum 的 $\gamma_{k+1}$ (层号经 `toLevel-≅`), 输出亦然.


```agda
t₀β : Ordˢ zero
t₀β = ψᴾ 0 zero (σ1 zero) [] (Ωˢ (suc zero))

gβ : (η : Ordᴵ) → suc zero ⊑ᴵ η → Ordˢ zero
gβ η e = ψᴾ 0 {ℓ = Mlev (suc zero) η e} (lim 0 zero) (λ q → lim 1 q) [] (Ωˢ η)

β₀ : Ordˢ zero
β₀ = ŝ (suc zero) t₀β gβ

z2 : zero <ᴵ suc (suc zero)
z2 = suc zero

_ : ψᴾ 1 z2 (λ q → q) (fΩ̂ z2 ∷ []) zero ≡ β₀
_ = refl

G₀β : Goodᶻ (toZ t₀β)
G₀β = empty-good zero (σ1 zero)

Ggβ : ∀ η e → Goodᶻ (toZ (gβ η e))
Ggβ η e = empty-good (lim 0 zero) (λ q → lim 1 q)

agβ : ∀ η e G → force (toZ (gβ η e)) G ≅ ψ⁰ (Ω η)
agβ η e G = empty-agree (lim 0 zero) (λ q → lim 1 q) G

ag₀ : ∀ G → force (toZ t₀β) G ≅ ψ⁰ (Ω (suc zero))
ag₀ G = empty-agree zero (σ1 zero) G

d₀β : suc zero ⊑ᴵ toLevel (force (toZ t₀β) G₀β) (force-HS _ G₀β)
d₀β = toLevel-⊑ (hs hz) (force-HS _ G₀β) (⊑-trans (one⊑ {y = Ω (suc zero)}) (≅→⊑ (≅-sym (ag₀ G₀β))))

dEβ : ∀ η e → suc zero ⊑ᴵ toLevel (force (toZ (gβ η e)) (Ggβ η e)) (force-HS _ (Ggβ η e))
dEβ η e = toLevel-⊑ (hs hz) (force-HS _ (Ggβ η e)) (⊑-trans (one⊑ {y = Ω η}) (≅→⊑ (≅-sym (agβ η e (Ggβ η e)))))

m₀β : ∀ η e → force (toZ t₀β) G₀β ⊑⁰ force (toZ (gβ η e)) (Ggβ η e)
m₀β η e = ⊑-trans (≅→⊑ (ag₀ G₀β)) (⊑-trans (Ψ⁰-mono e) (≅→⊑ (≅-sym (agβ η e (Ggβ η e)))))

mEβ : ∀ η e η′ e′ → η ⊑ᴵ η′ → force (toZ (gβ η e)) (Ggβ η e) ⊑⁰ force (toZ (gβ η′ e′)) (Ggβ η′ e′)
mEβ η e η′ e′ h = ⊑-trans (≅→⊑ (agβ η e _)) (⊑-trans (Ψ⁰-mono h) (≅→⊑ (≅-sym (agβ η′ e′ _))))

Gβ : Goodᶻ (toZ β₀)
Gβ = gc G₀β Ggβ d₀β dEβ m₀β mEβ G₀β Ggβ m₀β mEβ

-- 对任意证书: 计值 ≅ BTBOᴵ
βˢ≅ : (G : Goodᶻ (toZ β₀)) → force (toZ β₀) G ≅ N.BTBOᴵ
βˢ≅ (gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = l≅ outs≅
  where
  C : Ctx
  C = record { c = suc zero ; t₀ = force (toZ t₀β) G₀ ; E = λ η e → force (toZ (gβ η e)) (Gg η e)
             ; h₀ = force-HS _ G₀ ; hE = λ η e → force-HS _ (Gg η e)
             ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  pts : ∀ k → Pt.x (Γᶜ C k) ≅ N.γ (suc k)
  pts zero    = ag₀ G₀
  pts (suc k) = ≅-trans (agβ _ _ (Gg _ _)) (ψ⁰-≅ (Ω-≅ (toLevel-≅ (Pt.hx (Γᶜ C k)) (N.cert (suc k)) (pts k))))
  outs≅ : ∀ n → outs C (force (toZ t₀β) Go₀) (λ η e → force (toZ (gβ η e)) (Go η e)) n ≅ N.γ (suc n)
  outs≅ zero    = ag₀ Go₀
  outs≅ (suc k) = ≅-trans (agβ _ _ (Go _ _)) (ψ⁰-≅ (Ω-≅ (toLevel-≅ (Pt.hx (Γᶜ C k)) (N.cert (suc k)) (pts k))))

βˢ-label : (G : Goodᶻ (toZ β₀)) → Lab (force (toZ β₀) G) (E.EBOψ 2)
βˢ-label G = Lab-≅ (βˢ≅ G) BTBO-label
```


**读法.** 这恢复了 Symbolic 的 `Tβ≅` (那里的链由 `Ctx` 在外面手工装配; 这里由 $\psi^P$ 的弹栈子句产生, 证书由 §5 机械给出), 标签是定理 `βˢ-label`. 检验 1 的第二、三项 ($\psi_0(\Omega_\Omega+1)$, $+\Omega$) 在符号树上要对 "加数是待计值链" 的和发证书 (`β₀ + β₀` 是 `ĉᴸ`, 输出是 `β₀` 加上 `β₀` 的链点), 需要计值后的加法对 `ĉᴸ` 尾巴单调, 未做; 它们的标签仍由 Stage2 的 `ts-label`/`χ1-label` (静态前缀, 在这一片段与符号前缀一致) 给出.

## §7 检验 2、3: 符号树的结构, 与界为什么必须紧

`Goodᶻ` 未对一般输出证出 (§8), 所以 $X_2$ 与 $t_2$ 的计值树不能构造. 但计值之前的符号树已经可以检查: 前缀在 $\psi_\delta$ ($\delta\ge1$) 之下暴露的地方, 是否真的成了闭包, 闭包的界是多少. `kind` 读出第 0 层符号树的首构造子 (`kc c` 是界为 $c$ 的待计值链); `walkˢ` 沿 `lim` 与链的第 0 点 (不需计值) 下降.


```agda
-- 结构检查: X₂ = ψ₀(Ω_Ω+Ω₂) 的符号树 (计值之前)
data Kind : Set where
  kz ks kl kĉ : Kind
  kc : Ordᴵ → Kind

kind : Ordˢ zero → Kind
kind zero             = kz
kind (suc _)          = ks
kind (lim _)          = kl
kind (limᵢ () _)
kind (up () _)
kind (ŝ c _ _)        = kc c
kind (ĉᴸ c _ _ _ _)   = kĉ

sqˢ : Ordˢ zero → ℕ → Ordˢ zero
sqˢ (lim f) n          = f n
sqˢ (ŝ c t₀ g) zero    = t₀
sqˢ (ĉᴸ c t₀ g o₀ o) zero = o₀
sqˢ x n                = x

walkˢ : Ordˢ zero → List ℕ → Ordˢ zero
walkˢ x []      = x
walkˢ x (n ∷ p) = walkˢ (sqˢ x n) p

X₂ˢ : Ordˢ zero
X₂ˢ = ψᴾ 1 z2 (λ q → q) (fΩ̂ z2 ∷ []) (Ωˢ (suc (suc zero)))

two : Ordᴵ
two = suc (suc zero)

_ : kind X₂ˢ ≡ kl
_ = refl

-- A = ψ₀(Ω_Ω+ψ₁(Ω_Ω)) = X₂[1][0][1]: 待计值的链, 界 c = 2 (目标层 1 的闭包)
_ : kind (walkˢ X₂ˢ (1 ∷ 0 ∷ 1 ∷ [])) ≡ kc two
_ = refl

-- B = X₂[2][0][1]; B[0] 是链的第 0 点 (不需计值); B[0][0][0] 处又是一个界为 2 的待计值链 (Symbolic 的 B0t 在此是静态的 lim)
_ : kind (walkˢ X₂ˢ (2 ∷ 0 ∷ 1 ∷ [])) ≡ kc two
_ = refl

_ : kind (walkˢ X₂ˢ (2 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ [])) ≡ kc two
_ = refl
```


**读法.** $X_2=\psi_0(\Omega_\Omega+\Omega_2)$ 取环境层号 $2$. 沿 Symbolic 的 `X₂-at-A` 的 $[1][0][1]$ 到达 $A=\psi_0(\Omega_\Omega+\psi_1(\Omega_\Omega))$: 它是界为 $2$ 的待计值链 (内层 $\psi_1(\Omega_\Omega)$ 是目标层 1 的闭包, 界 $1+1$; 外层 $\psi_0$ 以同一组点为链). 沿 `X₂-at-B` 的 $[2][0][1]$ 到达 $B$, 也是界为 $2$ 的链; 它的第 0 点 (不需计值) 再走 $[0][0]$ 又是界为 $2$ 的链. Symbolic 的 `B0t` 在这一处是静态前缀的 `lim`, 由此走 `RpA` 到 $0$ (`B0-unlabel`); 这里同一处是闭包, 计值在折叠内部发生. 但 `RpA` 的第一步 $[1]$ 是链的第 1 点, 要计值, 而这需要 `Goodᶻ`.

$t_2=\psi_0(\Omega_\Omega\cdot2)$ (栈 $[\hat\Omega,\hat\Omega]$, 环境层号 1): 弹出一个 $\hat\Omega$ 后字面就是 Symbolic 的 `C2` 的形状 (第 0 点 $\psi_0(\Omega_\Omega+\Omega_1)$, 在 $\eta$ 处 $\psi_0(\Omega_\Omega+\Omega_\eta)$, 栈剩一个 $\hat\Omega$ 搬到 `Mlev 1 η e`). 在 $\eta=2$ 处, 内层的 $A$ 形闭包的界是 $2$, 不是环境层号 `Mlev 1 2 e₂`.


```agda
z1 : zero <ᴵ suc zero
z1 = zero

t2ˢ : Ordˢ zero
t2ˢ = ψᴾ 2 z1 (λ q → q) (fΩ̂ z1 ∷ fΩ̂ z1 ∷ []) zero

t2ˢ-shape : t2ˢ ≡ ŝ (suc zero) (ψᴾ 1 zero (σ1 zero) (fΩ̂ zero ∷ []) (Ωˢ (suc zero)))
                    (λ η e → ψᴾ 1 {ℓ = Mlev (suc zero) η e} (lim 0 zero) (λ q → lim 1 q) (fΩ̂ (lim 0 zero) ∷ []) (Ωˢ η))
t2ˢ-shape = refl

e₂ : suc zero ⊑ᴵ two
e₂ = s⊑ z≅ (suc zero)

gt2 : Ordˢ zero
gt2 = ψᴾ 1 {ℓ = Mlev (suc zero) two e₂} (lim 0 zero) (λ q → lim 1 q) (fΩ̂ (lim 0 zero) ∷ []) (Ωˢ two)

_ : kind (walkˢ gt2 (1 ∷ 0 ∷ 1 ∷ [])) ≡ kc two
_ = refl
```


**界为什么必须紧.** 若按 Symbolic §10 (i) 取环境层号为界: $t_2$ 的链在 $\eta=\mathtt{lvl}\,\gamma'_2$ 处计值 $\gamma'_3=\psi_0(\Omega_\Omega+\Omega_{\gamma'_2})$, 环境层号是 `Mlev c (lvl γ′₂) e`, 其第 $\ge1$ 项都是 $\mathtt{lvl}\,\gamma'_2$. $\gamma'_3$ 沿 9 步到达 $A$ (`A-in-γ′3`, 全程 $\omega$-共尾), 在这次计值内部生成的 $A$ 的闭包就以 $\cong\mathtt{lvl}\,\gamma'_2$ 为界, 它的 `gc` 字段 `d₀` 要求 $\mathtt{lvl}\,\gamma'_2\sqsubseteq^\mathsf I\mathtt{lvl}(A[0])$; 而记号侧 $A[0]=\eta_1<\gamma'_2$ (`A0≡η₁`, `A0<γ′2`, 即 SystemOmega 的 `cur-holds`). 所以那样的闭包没有证书, 计值树不存在 (树侧的矛盾经序对应, 这一步是纸面的; 记号侧的三个事实已编译). 紧的界不随环境膨胀: 在 `Mlev 2 η e` 内部 (η 抽象) 重算 $X_2$, $A$ 的闭包的界仍是 $2$ (`refl`; 派发只比较第 0 位的下标, 不读 $e$).


```agda
-- 紧的界: A 在 γ′₃ 的闭包里 (9 步), 其第 0 点 η₁ 在 γ′₂ 之下
toA : List ℕ
toA = 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ []

A-in-γ′3 : walkᵀ (γ′ᴱ 3) toA ≡ Aᵗ
A-in-γ′3 = refl

A-in-γ′3-ω : Allω (γ′ᴱ 3) toA
A-in-γ′3-ω = refl , refl , refl , refl , refl , refl , refl , refl , refl , tt

A0≡η₁ : fsn Aᵗ 0 ≡ η₁
A0≡η₁ = refl

A0<γ′2 : fsn Aᵗ 0 <ᵀ γ′ᴱ 2
A0<γ′2 = cur-holds

-- 在受支配的层号 Mlev 2 η e 内部重算 X₂, A 的闭包的界仍是 2 (不随环境层号膨胀)
module _ (η : Ordᴵ) (e : two ⊑ᴵ η) where
  X₂ᴹ : Ordˢ zero
  X₂ᴹ = ψᴾ 1 {ℓ = Mlev two η e} (lim 0 z2) (λ q → lim 0 q) (fΩ̂ (lim 0 z2) ∷ []) (Ωˢ two)

  _ : kind (walkˢ X₂ᴹ (1 ∷ 0 ∷ 1 ∷ [])) ≡ kc two
  _ = refl
```


## §8 `Goodᶻ` 闭包: 已有的、缺的、为什么

**已有.** 无符号片段 (空栈作用于无符号输入): `plainGood`/`empty-good` 给 `Goodᶻ`, 经 §5 的桥接由 Uniform 的 `HS` 搬来; 弹出唯一 $\hat\Omega$ 的闭包 `β₀` 的完整证书 `Gβ`. 这覆盖检验 1 的第一项, 不覆盖任何含 "前缀 + 非空尾巴" 的输出.

**第一个缺的实例.** `Goodᶻ (toZ (walkˢ X₂ˢ (1 ∷ 0 ∷ 1 ∷ [])))`, 即 $A$ 的闭包. 它的链在 $\eta$ 处是 $\psi^{[\hat\Omega]}_0(\psi^{[]}_1(\Omega_\eta))$: 外层栈非空, 尾巴是第 1 层的无符号树. 计值过程中出现 $\psi_0(\Omega_\Omega+1)=\lim\beta_0\cdot n$ 这样的和 (加数是待计值的链, 新族里是 `ĉᴸ`), 以及第 1 层的链点 $\psi_1(\Omega_\Omega+\cdots)$ 弹栈产生的新闭包. 它的十个字段要两件东西:

(a) **Uniform 在新族上的移植 (同形, 未写).** 新族的互模拟 `≅ˢ` (Level §5 加 `ŝ`/`ĉᴸ` 两个子句; 传递性要求两个闭包的界 $\cong^\mathsf I$, 否则中间那个闭包的定义域里找不到与 $\eta$ 相关的点; 紧的界下相关目标给出相关的界, 环境层号下不行, 这是界必须紧的第二个理由); 观测前序以计值为底: $x\sqsubseteq^\mathsf o y$ 指对一切相似观测与一切证书 $G,G'$, `force (toZ (run O x)) G ⊑ force (toZ (run O′ y)) G′` (`Goodᶻ`/`force` 先定义, 所以良定); 观测 `ψo` 带栈 (相似: 同长的纯 $\hat\Omega$ 栈); 上界引理多 `ŝ-r`/`ĉᴸ-r`; `B1` 推广为 "$x\sqsubseteq^\mathsf o\Omega_j\Rightarrow x\sqsubseteq^\mathsf o\psi^P_q z$" 对 ($n$, $z$) 归纳 (弹 `fT` 递归到 $x$, 弹 $\hat\Omega$ 走闭包的第 0 点); `zero-l` 在 `ψo` 观测下变成 "$\psi^P(0)\sqsubseteq^\mathsf o\psi^P(y)$". `Good` 对 `ŝ` 的子句: $t_0$, $g$ 好, $t_0\sqsubseteq^\mathsf o g\,\eta\,e$, $g$ 单调, 外加 (b) 的支配字段.

(b) **支配字段 `dE`, 不是移植.** 弹栈时在目标层 $\delta$ 造的闭包界为 $\delta+1$; 它在某个外层 $\psi_0$ 的链里计值时, `d₀`/`dE` 要 $\delta+1\sqsubseteq^\mathsf I$ 链点的层号, 即 "$\psi_\delta$ 出现在链点里 $\Rightarrow\delta\prec^\mathsf I$ 链点的层号". 这是 SystemOmega 的 `occ<` (§1 的 H2) 的树版本. 两种情形:

- $\delta\le1$ (界 $\le2$): $X_2$ 取环境层号 $2$, 它的全部闭包都在这里. 需要 "非零尾巴上 $\psi_0$ 的输出 $\succ1$". 初等, 但不能由 $\sqsubseteq^\mathsf o$ 的同余推出: Level 的 $\sqsubseteq$ 是前驱包含, 对 `suc` 不单调 (纸面反例: $a=\lim_n n$, $b=\lim_n(n+1)$, $a\sqsubseteq b$, 但 $a$ 既不 $\cong b$ 也不 $\prec b$, 故 $a\not\prec\mathrm{suc}\,b$, $\mathrm{suc}\,a\not\sqsubseteq\mathrm{suc}\,b$), 所以 "$X\sqsupseteq1\Rightarrow X+X\sqsupseteq2$" 要一条直接产生 $\prec$ 的引理 (例如对纯栈的长度归纳 "$1\cong\psi^P_0(0)$ 或 $1\prec\psi^P_0(0)$").
- $\delta$ 任意: $t_2$ 的链在 $\eta=\mathtt{lvl}\,\chi_k$ 处计值, 内层闭包的 $\delta$ 跑遍 $\mathtt{lvl}\,\chi_k$ 的子项, 它们是别的计值树的层号. 比较 $\delta$ 与新的链点的层号, 需要本阶段的序对应 (Label 的 `Slt`/`Seq`, 由 Bachmann 的 `oc` 从标签读出). 记号侧的对应物已经齐全 (SystemOmega 的 `Next₁`: 逐步的界 `β-up`, 支配 `dom`, 共尾性 `Sub-cofin`). 树侧于是有一个循环: 第 $k+1$ 个链点的证书要用第 $\le k$ 个链点的标签. 可行的组织是沿链同时归纳 (Label 的 `St k = Next (prev k) …` 的阶段 2 版本), 本文未做.

## §9 对比表

| | Symbolic §10 设计 | 本文 |
|---|---|---|
| 栈 | `Vec`, 长度为下标 | 同, 长度作显式参数, 一次过停机; `List` 被拒 (§3 的报错) |
| 规则 6 的链点 | 空栈 | **同一个栈** (EBO 的 $b[\gamma_k]$ 含整个前缀) |
| 闭包的界 | 环境层号 $\ell$ | **紧**: 纯 $\hat\Omega$ 栈时 $i+1$, 否则 $\ell$; 环境层号使 $A$ 的闭包无证书 (`A-in-γ′3`, `A0<γ′2`) |
| 目标层 0 | 另产生 `z0 (ĉ …)` | `ŝ` 在第 0 层就是链; `z0` 删去, `Z` 加 `ĉᴸ` |
| `tr`/`tr⁻`/`res`, `Ω`/`lift`/`into`/`out` | 逐点 / 照抄 | 已写 (§2) |
| 空栈 = Level 的 $\psi$ | 未提 | `ψ~` (异族互模拟, 任意相关输入), `empty-agree`, `empty-good` |
| $\psi_0(\Omega_\Omega)$ | `Tβ≅` (链由 `Ctx` 在外面装配) | `βˢ≅` (链由弹栈产生, 任意证书), `βˢ-label` |
| `Goodᶻ` 闭包 | 设计 | 无符号片段完成; 一般情形缺 (a) 移植 (b) 支配字段 (§8) |
| $\psi_0(\Omega_\Omega+\Omega_2)$ | `B0-unlabel` | 符号树: $A$, $B$, $B[0][0][0]$ 都是界 $2$ 的闭包 (`refl`); 计值树未造 |
| $\psi_0(\Omega_\Omega\cdot2)$ | `C2-unlabel` | `t2ˢ-shape` (= `C2` 的形状); 计值树未造; `dE` 需要阶段 2 的序对应 |
| $\psi_0(\Omega_{\Omega+1})$ | 一步形状 | 未做 (H4, $\psi_\Omega$ 栈帧) |

## §10 结论与边界

**字面成立 (`refl`):** `ψᴾ 1 z2 (λ q → q) (fΩ̂ z2 ∷ []) zero ≡ β₀`; `t2ˢ-shape`; 符号树的首构造子 (`kind X₂ˢ`, $A$, $B$, $B[0][0][0]$, `X₂ᴹ` 在抽象 $\eta$ 下, `gt2`); `force-chain` (逐项); `H1-col`; 记号侧 `A-in-γ′3`, `A-in-γ′3-ω`, `A0≡η₁`, `walk t2 toX₂ ≡ X₂ᵗ`, `walk t2 toη₁ ≡ η₁`.

**定理 (模 $\cong$; 标签按 Correspond 的 `Lab`):**

1. 接口: `H1-cmp`, `H1-pen`, `H1-fsT` (新证, 不要标准形); `H2-η₁` (由 `occ<`); `H3-X₂` (由 `cofin₁`); `A0<γ′2` (由 `cur-holds`).
2. 新族 (§2) 及其 `trˢ`/`tr⁻ˢ`/`resˢ`/`res⁻ˢ`, `Ωˢ`, `addˢ`, `liftˢ`, `toZ`; $\psi^P$ (`ψᴾ`, §3, 过停机检查).
3. `Goodᶻ`/`force`/`force-HS` 对 `ĉᴸ` (§4).
4. 空栈健全性: `ψ~`, `force~`, `plainGood`, `empty-agree`, `empty-good` (§5).
5. 检验 1: `Gβ`, **`βˢ≅ : ∀ G → force (toZ β₀) G ≅ BTBOᴵ`**, **`βˢ-label`** ($\psi_0(\Omega_\Omega)$, 树由 $\psi^P$ 的弹栈产生).

**标签状态.** $\psi_0(\Omega_\Omega)$: 定理 (`βˢ-label`). $\psi_0(\Omega_\Omega+\Omega_2)$: **未得**, 计值树 `force (toZ X₂ˢ) G` 无法构造, 因为 `Goodᶻ (toZ X₂ˢ)` 未证; Symbolic 的 `PB` 在符号层到达闭包 (而非静态 `lim`), 在计值层未走. $\psi_0(\Omega_\Omega\cdot2)$: **未得**, `C2-unlabel` 与 Stage2 的 `Q′` 未解除; 符号树的外层就是 `C2`. $\psi_0(\Omega_{\Omega+1})$: 未做.

**边界.**

- 精确的停点: §8 的 (a) 与 (b). (a) 是 Uniform (约 370 行代码) 在新族上的移植, 外加 `ŝ`/`ĉᴸ`/栈的情形; (b) 在 $\delta\le1$ 时是一条初等的严格性引理, 在 $\delta$ 任意时需要阶段 2 的序对应, 与标签相互依赖.
- `fT` 帧: `ψᴾ` 处理它 (界退回环境层号), 但 §8 的闭包理论只针对纯 $\hat\Omega$ 栈. 阶段 2 ($<\Omega_{\Omega+1}$) 的标准形不产生 `fT` 帧 (和的各项非增, $\Omega_\Omega$ 被加数在前), 所以这不是检验的障碍; 到 $\psi_\Omega$ 栈帧 (§9 的 H4) 时要重新考虑.
- "界必须紧" 的否定: 记号侧三个事实已编译, 树侧的矛盾 ("`d₀` 不可能成立") 经序对应, 是纸面的.
- `List` 栈的否定是编译过的报错 (临时文件), 因不能编译不进本文.
- `βˢ≅` 只到 $\cong$ (`lim` 下的函数头不同, 字面相等要函数外延性).
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
