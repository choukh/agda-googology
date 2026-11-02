# 树侧的出现不变量 (二): 支配定理与 $t_2$ 的链上的证书

> 接 [TreeNFBase](TreeNFBase.lagda.md) (地板 `FlΛ`、覆盖 `CovΛ`、逐闭包的出现不变量 `Occ≺ᴳ`、支配定理 `dom-cov`、以 $\Omega_1$ 为地板的遗传好树 `Floor β cov`) 与 [NotFree](NotFree.lagda.md) (记号无关证书 `Goodᴺ`, 链骨架 `NextN`/`Gᴺ₂-of`, 停点 $k=1$). 任务 3–4: 用出现不变量代替 `Strictᵝ`, 在 $t_2=\psi_0(\Omega_\Omega\cdot2)$ 的链上记号无关地造证书.
>
> 结论先说:
>
> 1. **支配定理在 $t_2$ 的链上的实例 (§1).** 覆盖 `cov₁ : CovΛ 1 β₀` ($\beta_0=\mathtt{lvl}\,\chi_0$, $\chi_0$ 是 $\gamma'_1=\psi_0(\Omega_\Omega+\Omega_1)$ 的记号无关计值树): 覆盖链点 $\hat\chi_1$ 的证书由 Omega2 的 `G₀ᵗ` (观测前序与 `Strict₁`, 不读记号) 经 `Goodᶻ-tr` 搬来. 于是 `S⁺₀ = dom-cov · cov₁`: **一切以 $\Omega_1$ 为地板的尾巴, 其 $\psi^{[\hat\Omega]}_0$-折叠的层号 $\sqsupseteq\mathtt{lvl}\,\gamma'_1$**, 对一切折叠观测与一切证书. 这是被 `no-Bound` 否掉的 `Strictᵝ` 的相对版本: 不对一切尾巴, 只对有地板的尾巴; 不是全局界, 是 "在链点 $\gamma'_1$ 之下".
> 2. **$\gamma'_2$ 的记号无关证书 (§2).** `cert-g : ∀ η e → η ⊑ᴵ β₀ → Goodᶻ (toZ (gᵗ η e))`: $t_2$ 的外层链的计值点 $\psi^{[\hat\Omega]}_0(\Omega_\eta)$ 对**一切** $\eta\sqsubseteq^\mathsf I\mathtt{lvl}\,\gamma'_1$ 有 Prefix 证书, 由 `Floor.Good-ψ1` 无其他前提给出. 特例 **`Gγ′₂ : Goodᶻ (toZ (gᵗ β₀ dχ₀))`** 与 `Gᴺγ′₂ = ofZ Gγ′₂` 正是 NotFree 的停点 (链指标 $k=1$, `NextN.step 0` 的证书分量): **已解除**. `step0ᴺ = step₀ Gγ′₂` 给出 `NextN.step 0` 在 $\chi_0$ 处的三个分量 (证书、支配、单调), `step0′` 对一切 $Y\cong\chi_0$. Omega2 的 `first-wall`/`second-wall` 处的内部闭包的支配全部由地板 $\Omega_1$ + 覆盖 $\hat\chi_1$ 给出. 标签只在验收里出现 (§5).
> 3. **`Gᴺ₂` 未得; 新停点在链指标 $k=2$ (§3–§4).** `NextN` 要对一切 $k$ 给下一点; $k=1$ 的下一点 $\gamma'_3=\psi_0(\Omega_\Omega+\Omega_{\gamma'_2})$ (符号树 `gᵗ η₁ e`, $\eta_1=\mathtt{lvl}\,\gamma'_2$) 没有证书. 编译过的: (a) **`floor-wall`**: 地板 $\Omega_1$ 恰好走到 $\mathtt{lvl}\,\gamma'_1$ 为止 ($\beta\sqsupseteq\beta_0+1$ 时 `Strict⁺ β` 为假, `CovΛ 1 β` 无居留), 与 `Sβ-fails⁺` (全局界恰好走到 BTBO) 同构, 往上推了一个链点; (b) `γ′₃-blocked`: $\gamma'_3$ 的环境层号之上没有可用的单覆盖 `Floor`; (c) **正面: `popOcc₃`**: $\gamma'_3$ 里**每个刚弹出的闭包**都满足 `Occ≺ᴳ`, 覆盖取 $\hat\chi_1$ (界 $\sqsubseteq\beta_0$) 或 $\hat\chi_{\beta_0}=\gamma'_2$ (界 $\sqsubseteq\eta_1$, 证书就是 §2 的 `Gγ′₂`), 用有界三歧选层. 缺的恰是一条: **地板为 $\Omega_{\beta_0}$ 的闭包被目标 $d\prec\beta_0$ 的 $\psi_d$ 映射之后、被分支函数里目标 $\sqsupseteq\beta_0$ 的 $\psi_a$ 再次映射之前**, 这段 "悬置" 期间的不变量 (§4 给出路径与需要的引理).
> 4. (b)(c) 以链的严格增长 $\beta_0\prec^\mathsf I\eta_1$ 为前提; 本文只经标签证明它 (`growth-lab`, 验收侧), 记号无关的证明是另一个 (小) 缺口.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeNF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.Prefix using (Ordˢ; Ωˢ; toZ; Goodᶻ; force; force-HS; t2ˢ)
open import OCF.Align.UniformS using (_≅ˢ_; ψ1; ψ1-≅; Ωˢ-refl; Goodᶻ-tr; toZ-≅; force-≅; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ʳ; ≅→⊑ᵒ;
  ψ1-cong; Ω-monoᵒ; idO)
open import OCF.Align.Stage2Label using (t₀pop; gpop)
open import OCF.Align.Omega2 using (t₀ᵗ; gᵗ; G₀ᵗ; dom1; lab-g)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; ofZ; ofZ-≅; χ₀; hχ₀; dχ₀; χ₀-label; step₀; NextN; any-T2)
open import OCF.Align.TreeNFBase
```


## §1 覆盖链点 $\hat\chi_1$ 与 `Strict⁺` (支配定理的实例)

NotFree 的 $\chi_0$ 是 $\gamma'_1$ 的记号无关计值树 (`forceᴺ _ (ofZ G₀ᵗ)`), $\beta_0$ 是它的层号. TreeNFBase 的覆盖链点 $\hat\chi_1$ (环境层号 `Mlev 1 1 e₁`) 与 Omega2 的 `t₀ᵗ` (环境层号 1) 互模拟 (`ψ1-≅`), 所以证书由 `G₀ᵗ` 搬来, 计值 $\cong\chi_0$. 于是 `cov₁` 与它的弱化 `cov-low` (覆盖一切 $c\sqsubseteq\beta_0$). `S⁺₀` 是支配定理 `dom-cov` 对 $\varphi=1$ 的实例, 即 TreeNFBase 的 `Floor.Strict⁺`.

工程注记: `t₀≅χ̂` 的隐式参数 (`k₁`/`ℓ₁`/`k₂`/`ℓ₂`/`p`/`σ`/`p′`/`σ′`/`z`/`z′`) 不写出时报 `[UnsolvedMetaVariables]`, 剩下的约束卡在 `ψᴾ 1 _p_12 _σ_13 … | <ᴵ-dec (_σ_13 zero) _p_12` (折叠的 `with` 阻塞合一), 与 README 记的 "折叠引理的隐式参数要写出" 同.

```agda
β₀ : Ordᴵ
β₀ = toLevel χ₀ hχ₀

e₁ : suc zero ⊑ᴵ suc zero
e₁ = ⊑ᴵ-refl

t₀≅χ̂ : t₀ᵗ ≅ˢ χ̂ (suc zero) e₁
t₀≅χ̂ = ψ1-≅ {k₁ = suc zero} {ℓ₁ = suc zero} {k₂ = suc zero} {ℓ₂ = Mlev (suc zero) (suc zero) e₁}
             {p = zero} {σ = σ1 zero} {p′ = lim 0 zero} {σ′ = λ q → lim 1 q} {z = zero} {z′ = lim 0 zero}
             (≅ᴵ-refl zero) (Ωˢ-refl (suc zero))

G₁ : Goodᶻ (toZ (χ̂ (suc zero) e₁))
G₁ = Goodᶻ-tr (toZ-≅ t₀≅χ̂) G₀ᵗ

χ₀≅G₁ : χ₀ ≅ force _ G₁
χ₀≅G₁ = ≅-trans (ofZ-≅ G₀ᵗ) (force-≅ (toZ-≅ t₀≅χ̂) G₀ᵗ G₁)

cov₁ : CovΛ (suc zero) β₀
cov₁ = e₁ , G₁ , ≅ᴵ→⊑ᴵ (toLevel-≅ hχ₀ (force-HS _ G₁) χ₀≅G₁)

cov-low : ∀ {c} → c ⊑ᴵ β₀ → CovΛ (suc zero) c
cov-low h = e₁ , G₁ , ⊑ᴵ-trans h (proj₂ (proj₂ cov₁))

S⁺₀ : ∀ {k} {y : Ordˢ k} → Fl y → ColC β₀ y
S⁺₀ fl = dom-cov fl cov₁
```


## §2 $\gamma'_2$ 的记号无关证书

`Floor β₀ cov₁` 的闭包定理作用于 $t_2$ 的外层链的计值点 `gᵗ η e` $=\psi^{[\hat\Omega]}_0(\Omega_\eta)$ (环境层号 `Mlev 1 η e`): 前提 `Mlev 1 η e ⊑ᴵ β₀` 由 `Mlev⊑` 从 $\eta\sqsubseteq\beta_0$ 得到, 尾巴 $\Omega_\eta$ 好且自反. 结论对一切 $\eta\sqsubseteq^\mathsf I\beta_0$ 成立; $\eta=\beta_0$ 是 $\gamma'_2$. 证书内部的数学全部在 TreeNFBase: 弹栈闭包的界 $i{+}1\sqsubseteq\beta_0$ (`popDom`, 来自 $i<^\mathsf I\ell\sqsubseteq\beta_0$), 地板 $\Omega_1$ 由每个非零目标的映射者再生 (`one⊑`), 闭包到第 0 层时支配由 `S⁺₀` (`Dom-ψ1`). Omega2 §4 的 `first-wall` (目标 BTBO、界 $\mathtt{lvl}\,\mathrm{BTBO}+1$) 与 `second-wall` (目标 BTBO$+1$) 处的闭包都在其中: 它们的界 $\sqsubseteq\beta_0$, 第 0 点有地板 $\Omega_1$, 被折叠时链点 $\sqsupseteq\hat\chi_1\cong\gamma'_1$.

`step0ᴺ`: NotFree 的 `step₀` 就是 "给定 $\gamma'_2$ 的计值树的任意 Prefix 证书, `NextN.step 0` 的支配与单调记号无关地得出"; 现在证书有了. `step0′` 推广到一切 $Y\cong\chi_0$ (`NextN.step 0` 对不变量 "$Y\cong\chi_0$" 的形式): 证书经 `cert-g` ($\mathtt{lvl}\,Y\cong\beta_0$), 支配经 Omega2 的 `dom1` (`Strict₁`), 单调经 `ψ1-cong (Ω-monoᵒ e)` 在恒等观测下. 写成以证书为参数的模块 `Step0` 是工程上的: 把 `cert-g …` 直接写进 `where` 的类型签名, 检查超过 180 s (同 NotFree 的注记: 证书别名出现在类型里会被展开).

```agda
module F₀ = Floor β₀ cov₁

good-g : ∀ η (e : suc zero ⊑ᴵ η) → η ⊑ᴵ β₀ → F₀.Good (gᵗ η e)
good-g η e h = F₀.Good-ψ1 {p = lim 0 zero} {σ = λ q → lim 1 q} {z = lim 0 zero} (Mlev⊑ e h) (F₀.Good-Ω η) (Ωˢ-refl η)

cert-g : ∀ η (e : suc zero ⊑ᴵ η) → η ⊑ᴵ β₀ → Goodᶻ (toZ (gᵗ η e))
cert-g η e h = F₀.Good→Goodᶻ (good-g η e h)

Gγ′₂ : Goodᶻ (toZ (gᵗ β₀ dχ₀))
Gγ′₂ = cert-g β₀ dχ₀ ⊑ᴵ-refl

Gᴺγ′₂ : Goodᴺ (toZ (gᵗ β₀ dχ₀))
Gᴺγ′₂ = ofZ Gγ′₂

step0ᴺ : Σ (Goodᴺ (toZ (gᵗ β₀ dχ₀))) λ G →
           Σ (suc zero ⊑ᴵ toLevel (forceᴺ _ G) (forceᴺ-HS _ G)) λ _ → χ₀ ⊑⁰ forceᴺ _ G
step0ᴺ = step₀ Gγ′₂
```

```agda
module Step0 (Y : Ordᶜ zero) (hY : HS Y) (e : suc zero ⊑ᴵ toLevel Y hY) (eY : Y ≅ χ₀)
             (G : Goodᶻ (toZ (gᵗ (toLevel Y hY) e))) where
  η : Ordᴵ
  η = toLevel Y hY

  mono : force _ G₀ᵗ ⊑ force _ G
  mono = ψ1-cong {ℓ = suc zero} {ℓ′ = Mlev (suc zero) η e}
                 {p = zero} {p′ = lim 0 zero} {σ = σ1 zero} {σ′ = λ q → lim 1 q} {z = zero} {z′ = lim 0 zero}
                 {x = Ωˢ (suc zero)} {y = Ωˢ η} (Ω-monoᵒ e) idO G₀ᵗ G

  step : Σ (Goodᴺ (toZ (gᵗ η e))) λ G′ →
           Σ (suc zero ⊑ᴵ toLevel (forceᴺ _ G′) (forceᴺ-HS _ G′)) λ _ → Y ⊑⁰ forceᴺ _ G′
  step = ofZ G
       , ⊑ᴵ-≅ʳ (dom1 {L = Mlev (suc zero) η e} {k = η} {p = lim 0 zero} {σ = λ q → lim 1 q}
                     {z = lim 0 zero} {y = Ωˢ η} (Ωˢ-refl η) G)
               (toLevel-≅ (force-HS _ G) (forceᴺ-HS _ (ofZ G)) (≅-sym (ofZ-≅ G)))
       , ⊑-trans (≅→⊑ (≅-trans eY (ofZ-≅ G₀ᵗ))) (⊑-trans mono (≅→⊑ (≅-sym (ofZ-≅ G))))

step0′ : ∀ Y (hY : HS Y) (e : suc zero ⊑ᴵ toLevel Y hY) → Y ≅ χ₀ →
         Σ (Goodᴺ (toZ (gᵗ (toLevel Y hY) e))) λ G →
           Σ (suc zero ⊑ᴵ toLevel (forceᴺ _ G) (forceᴺ-HS _ G)) λ _ → Y ⊑⁰ forceᴺ _ G
step0′ Y hY e eY = Step0.step Y hY e eY (cert-g (toLevel Y hY) e (≅ᴵ→⊑ᴵ (toLevel-≅ hY hχ₀ eY)))
```


## §3 停点: 地板 $\Omega_1$ 的墙与 $\gamma'_3$

**`floor-wall`.** 若 $\beta_0+1\sqsubseteq^\mathsf I\beta$, 则 "一切以 $\Omega_1$ 为地板的尾巴被 $\beta$ 支配" 为假: 取尾巴 $\Omega_1$ 本身 (地板自反) 与观测 `col` (`t₀ᵗ` 的环境), 得 $\beta\sqsubseteq\mathtt{lvl}\,\gamma'_1\cong\beta_0$, 与 $\beta_0\prec\beta$ 矛盾. 推论 `no-cov`: `CovΛ 1 β` 无居留. 与 Omega2Base 的 `Sβ-fails⁺` 同构: 全局界 (`Strictᵝ`, 对一切尾巴) 恰好走到 $\mathtt{lvl}\,\psi^{[\hat\Omega]}_0(0)=\mathtt{lvl}\,\mathrm{BTBO}$; 地板 $\Omega_1$ 的界 (`Strict⁺`, 对有地板的尾巴) 恰好走到 $\mathtt{lvl}\,\psi^{[\hat\Omega]}_0(\Omega_1)=\mathtt{lvl}\,\gamma'_1$. 每抬高一次地板, 墙往上推一个链点.

**工程注记.** `floor-wall` 先在以证书为参数的模块 `Wall` 里证, 再实例化为 `G₀ᵗ`. 直接在 `where` 的类型里写 `force _ G₀ᵗ` 并调用 `S … G₀ᵗ` 时, 检查器为比较 `run (ψo₁ idO …) (Ωˢ 1)` 与 `t₀ᵗ` 展开证书, 400 s 未结束 (`timeout` 退出码 124; 二分定位到这一处). 下面的 `Stop` 与 §5 的 `Accept` 同样以 $\gamma'_2$ 的证书为模块参数, 文末才实例化为 `Gγ′₂`; `popOcc₃` 的三歧也不用 `with`, 而用对三歧结果做模式匹配的辅助函数 `pick`.

```agda
η⊑Mlev : ∀ {c η} (e : c ⊑ᴵ η) → η ⊑ᴵ Mlev c η e
η⊑Mlev e = Sim→⊑ᴵ (λ q → lim 1 q)

≺→⊑ᴵ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ᴵ h = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (s⊑′ h)

below-η : ∀ {i η} {e : suc zero ⊑ᴵ η} → NZ i → i <ᴵ Mlev (suc zero) η e → i ≺ᴵ η
below-η nz (lim zero zero) = ⊥-elim nz
below-η nz (lim (suc n) q) = via (≅ᴵ-refl _) q
```

```agda
module Wall (G : Goodᶻ (toZ (ψ1 {ℓ = suc zero} zero (σ1 zero) zero (Ωˢ (suc zero)))))
            (eG : toLevel (force _ G) (force-HS _ G) ≅ᴵ β₀) where
  floor-wall : ∀ β → suc β₀ ⊑ᴵ β → ¬ (∀ {k} {y : Ordˢ k} → Fl y → ColC β y)
  floor-wall β h S = ≺ᴵ-irrefl (≺ᴵ-respʳ (sim (⊑ᴵ-trans h w) zero) eG)
    where
    w : β ⊑ᴵ toLevel (force _ G) (force-HS _ G)
    w = S {y = Ωˢ (suc zero)} (≅→⊑ᵒ (Ωˢ-refl (suc zero))) (col {L = suc zero} {p = zero} {σ = σ1 zero} {z = zero}) G
```

```agda
eG₀ : toLevel (force _ G₀ᵗ) (force-HS _ G₀ᵗ) ≅ᴵ β₀
eG₀ = toLevel-≅ (force-HS _ G₀ᵗ) hχ₀ (≅-sym (ofZ-≅ G₀ᵗ))

floor-wall : ∀ β → suc β₀ ⊑ᴵ β → ¬ (∀ {k} {y : Ordˢ k} → Fl y → ColC β y)
floor-wall = Wall.floor-wall G₀ᵗ eG₀

no-cov : ∀ β → suc β₀ ⊑ᴵ β → ¬ CovΛ (suc zero) β
no-cov β h cv = floor-wall β h (λ fl → dom-cov fl cv)
```


**$\gamma'_3$.** 以 $\gamma'_2$ 的证书 $G$ 为参数, $\eta_1=\mathtt{lvl}(\mathrm{force}\,G)$. $\gamma'_3$ 的符号树是 `gᵗ η₁ e`, 环境层号 `Mlev 1 η₁ e` $\sqsupseteq\eta_1$; `Floor β` 要求环境 $\sqsubseteq\beta$, 而 $\beta\sqsupseteq\eta_1\succ\beta_0$ 时 `CovΛ 1 β` 无居留 (`γ′₃-blocked`). 单一覆盖 $\hat\chi_1$ 到此为止, 必须用 `Occ≺ᴳ` 的分层覆盖.

**分层覆盖在弹栈处成立 (`popOcc₃`).** $\gamma'_3$ 里在目标 $i$ 弹出的闭包 (界 $i{+}1$, $i<^\mathsf I$ 环境层号): 用有界三歧把 $i$ 与 $\beta_0$ 比较 (公共上界是环境层号; $\beta_0\cong b<^\mathsf I\eta_1$ 由增长前提给出, 经 `lim 1` 进入环境):

- $i\prec\beta_0$: 覆盖 $\hat\chi_1$ (`cov-low`, $i{+}1\sqsubseteq\beta_0$), 地板 $\Omega_1\sqsubseteq\Omega_i$ (`one⊑`);
- $i\cong\beta_0$ 或 $\beta_0\prec i$: 覆盖 $\hat\chi_{\beta_0}=\gamma'_2$ (`cov-high`, 证书就是参数 $G$; $i{+}1\sqsubseteq\eta_1$ 由 `below-η`), 地板 $\Omega_{\beta_0}\sqsubseteq\Omega_i$.

两个覆盖链点都已有记号无关的证书 ($\gamma'_1$: NotFree; $\gamma'_2$: §2). 这正是 "相对链" 的逐闭包不变量: 闭包的界落在哪一段 $(\mathtt{lvl}\,\gamma'_{m},\mathtt{lvl}\,\gamma'_{m+1}]$, 就由链点 $\gamma'_{m+1}$ 覆盖, 地板 $\Omega_{\mathtt{lvl}\,\gamma'_m}$.

```agda
module Stop (G : Goodᶻ (toZ (gᵗ β₀ dχ₀))) where
  η₁ : Ordᴵ
  η₁ = toLevel (force _ G) (force-HS _ G)

  cov-high : ∀ {c} → c ⊑ᴵ η₁ → CovΛ β₀ c
  cov-high h = dχ₀ , G , h

  γ′₃-blocked : β₀ ≺ᴵ η₁ → ∀ (e : suc zero ⊑ᴵ η₁) β → Mlev (suc zero) η₁ e ⊑ᴵ β → ¬ CovΛ (suc zero) β
  γ′₃-blocked g e β h = no-cov β (⊑ᴵ-trans (s⊑′ g) (⊑ᴵ-trans (η⊑Mlev e) h))

  pick : ∀ {b i} (e : suc zero ⊑ᴵ η₁) → β₀ ≅ᴵ b → NZ i →
         (p : i <ᴵ Mlev (suc zero) η₁ e) (z : zero <ᴵ Mlev (suc zero) η₁ e) →
         (i ≺ᴵ b ⊎ b ≺ᴵ i ⊎ i ≅ᴵ b) → Occ≺ᴳ (suc i) (t₀pop p z) (gpop p z)
  pick e eb nz p z (injᵃ r)  = Occ-pop (one⊑ z p nz) (cov-low (s⊑′ (≺ᴵ-respʳ r (≅ᴵ-sym eb)))) p z
  pick e eb nz p z (injᵇ r)  = Occ-pop (≺→⊑ᴵ (≺ᴵ-respˡ eb r)) (cov-high (s⊑′ (below-η nz p))) p z
  pick e eb nz p z (injᶜ ie) = Occ-pop (≅ᴵ→⊑ᴵ (≅ᴵ-trans eb (≅ᴵ-sym ie))) (cov-high (s⊑′ (below-η nz p))) p z

  popOcc₃ : β₀ ≺ᴵ η₁ → ∀ (e : suc zero ⊑ᴵ η₁) {i} → NZ i →
            (p : i <ᴵ Mlev (suc zero) η₁ e) (z : zero <ᴵ Mlev (suc zero) η₁ e) → Occ≺ᴳ (suc i) (t₀pop p z) (gpop p z)
  popOcc₃ (via eb b<) e nz p z = pick e eb nz p z (<ᴵ-dec p (lim 1 b<))
```


## §4 缺的引理: 悬置的闭包

把 `Floor` 推广成 "非零层 `Dom` = `Occ≺ᴳ`" 时, TreeNFBase 的保持引理覆盖了弹栈 (`popOcc₃` 给出分层)、加法 (前缀有地板)、搬运, 以及**目标 $\sqsupseteq\varphi$ 的**映射. 不覆盖的情形在 $\gamma'_3$ 的折叠里出现, 路径 (树侧, 纸面):

1. 尾巴 $\Omega_{\eta_1}$ 沿 $\eta_1$ 的结构下降到某个 $\Omega_{a+1}$, $a\sqsupseteq\beta_0$ ($\eta_1$ 是 $\gamma'_2$ 的计值树的层号, 其子层号跨过 $[\beta_0,\eta_1)$; `popOcc₃` 的第二、三支就是这一段).
2. 目标 0 在节点 $a$ 处折叠: 链点 $c_1=\psi^{[\hat\Omega]}_a(\Omega_a)$. $\Omega_a$ 的节点都 $\prec a$, 全部穿透, 在 $\Omega_a$ 的叶子 $0$ 处弹出界 $a{+}1$ 的闭包: 覆盖 $\hat\chi_{\beta_0}$, 地板 $\Omega_a\sqsupseteq\Omega_{\beta_0}$. 至此 `Occ≺ᴳ` 成立.
3. $c_1$ 继承 $\Omega_a$ 的穿透节点. $a$ 为极限时 $\Omega_a=\lim_n\Omega_{a[n]}$, 而 $a[n]$ 可以 $\prec\beta_0$; 于是 $c_1$ 含节点 $d\prec\beta_0$ 的 `limᵢ`, 分支是 $y\mapsto\psi^{[\hat\Omega]}_a(y)$.
4. 外层 $\psi^{[\hat\Omega]}_0$ 在 $d$ 处折叠 $c_1$ 的这一段: 链 $e_{n+1}=\psi^{[\hat\Omega]}_d(\psi^{[\hat\Omega]}_a(e_n))$. 第 2 步的闭包被 $\psi_d$ 映射, $d\prec\beta_0=\varphi$: **`Occ-ψ1ᴳ` 的条件 $\varphi\sqsubseteq i$ 不满足**, 再生的地板只有 $\Omega_d$; 而 $\psi_0(\Omega_\Omega+\psi_d(\cdots))<\psi_0(\Omega_\Omega+\Omega_{d+1})$ 不一定 $>a$ (NotFree 的 `dip` 正是这个形状). 闭包处于 "悬置": `ColC (a+1) (ψ_d t₀)` 一般为假, `Good` 的 `Dom` 在 $e_{n+1}$ 里写不出.
5. 但 $e_{n+1}$ 只作为分支的输入出现: 输出 $\psi^{[\hat\Omega]}_0(\psi^{[\hat\Omega]}_a(e_{n+1}))$ 里, 分支 $y\mapsto\psi^{[\hat\Omega]}_a(y)$ 先把悬置的闭包映到目标 $a\sqsupseteq\beta_0$, `Occ-ψ1ᴳ` 重新适用, 再被 $\psi_0$ 折叠时支配成立. 这就是 `NF₁` 的 `vs` 规则 ("只看穿下标 $\ge u$ 的节点") 的树侧形式: 悬置的闭包在 $\psi_d$ 之下不可见, 被 $\psi_a$ 包住才重新可见.

**缺的引理 (精确).** 遗传好树要有两层非零支配: `Occ≺ᴳ` (覆盖且已有支配) 与 "悬置" (只有覆盖 $\varphi$, 没有 `ColC`). `Good` 的 `bi` 子句 (分支对好输入给好输出) 要加**覆盖条件**: 分支 $f$ 把 "悬置覆盖 $\sqsubseteq\kappa$" 的输入映成在目标 0 的折叠可达处无悬置的输出, 其中 $\kappa$ 是 $f$ 的包裹目标 (上例 $f=y\mapsto\psi_a(y)$, $\kappa=a$). `Good-ψ1` 要带前提 "输入在目标 0 可达处无悬置", 并在折叠的链点处证明: 链点 $\psi_d(f(e_n))$ 里新出现的悬置闭包的覆盖都 $\sqsubseteq$ 该节点所在 `limᵢ` 的分支的包裹目标. 计数要按 "节点层号之上的闭包", 不能按尾巴层号: 对 $\Omega_{d+1}$ (分支 `up zero`, 没有包裹) 链点里只有 $d$ 处自己弹出的闭包 (覆盖 $\sqsubseteq d$), 按尾巴层号计则误报悬置. 这就是 Relative 的 `¬BranchΩ` 说的 "按闭包陈述、不按单次计值陈述" 在这里的具体形状. 外加一条小引理: 链的严格增长 $\mathtt{lvl}\,\gamma'_m\prec^\mathsf I\mathtt{lvl}\,\gamma'_{m+1}$ 的记号无关证明 (本文只有经标签的 `growth-lab`; `popOcc₃` 的分层选择要它在公共上界里给出字面子项).

**为什么在 $\gamma'_2$ 不出现.** $\gamma'_2$ 只有一层 ($\varphi=1$), 而 1 在一切非零目标之下 (`one⊑`), 所以没有映射会落在地板之下: 悬置在 $\gamma'_2$ 里不可能. 第一个可能的悬置在 $\gamma'_3$, 需要 $a\sqsupseteq\mathtt{lvl}\,\gamma'_1$ 且 $a$ 的基本列跌到 $\mathtt{lvl}\,\gamma'_1$ 之下. 记号侧的有界搜索 (从 $\gamma'_3$ 出发宽度 3、深度 11, 宽度 4、深度 9, 找形如 $\psi_d(\Omega_\Omega+\cdots+\psi_a(\Omega_\Omega+\cdots))$, $0<d<\gamma'_1<a$ 的子项) 没有找到实例: 这样的路径要先把外层下标的基本列走到后继再走到极限, 比这个深度长; 所以上面的路径是纸面的, 没有 `refl` 见证.


## §5 验收 (记号只在这里)

`γ′₂-label`: §2 的计值树带标签 $\gamma'_2=\psi_0(\Omega_\Omega+\Omega_{\gamma'_1})$, 由 Omega2 的 `lab-g` (对任意证书). `γ′₂ᴺ-label`: 记号无关证书的计值树同. 由 NotFree 的 `forceᴺ-≅`, 它 $\cong$ GoodL 的标签式证书在同一点的计值 (同一标签, `Lab-uniq`). `growth-lab`: 链的严格增长 $\beta_0\prec^\mathsf I\eta_1$, 经 `Lab-oc` 与 `γ′-mono`; 它是 §3 的 `γ′₃-blocked`/`popOcc₃` 的前提的**一个**证明, 不是记号无关的.

```agda
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Stage2 using (γ′ᴱ)
open import OCF.Align.StandardOmega using (γ′-NF; γ′-mono)
open import OCF.Align.Stage2Label using (Lab-oc)

module Accept (G : Goodᶻ (toZ (gᵗ β₀ dχ₀))) where
  γ′₂-label : Lab (force _ G) (γ′ᴱ 2)
  γ′₂-label = lab-g 0 hχ₀ χ₀-label dχ₀ G

  γ′₂ᴺ-label : Lab (forceᴺ _ (ofZ G)) (γ′ᴱ 2)
  γ′₂ᴺ-label = Lab-≅ (ofZ-≅ G) γ′₂-label

  growth-lab : β₀ ≺ᴵ Stop.η₁ G
  growth-lab = toLevel-≺ hχ₀ (force-HS _ G) (Lab-oc γ′₂-label (γ′-NF 2) χ₀-label (γ′-NF 1) (γ′-mono 1))

module S₃ = Stop Gγ′₂
module A₂ = Accept Gγ′₂
```


## §6 对比表: NotFree 的停点与本文

| | NotFree | 本文 |
|---|---|---|
| $\gamma'_1$ 的证书 | `G₀ᴺ` (记号无关) | 同 |
| $\gamma'_2$ 的证书 (`NextN.step 0`) | **缺** (停点 $k=1$) | **`Gγ′₂`/`Gᴺγ′₂`, 记号无关**; `step0ᴺ`, `step0′` |
| $\psi^{[\hat\Omega]}_0(\Omega_\eta)$ 的证书 | $\eta\sqsubseteq\mathtt{lvl}\,\mathrm{BTBO}$ (`Strict-BTBO`) | 一切 $\eta\sqsubseteq\mathtt{lvl}\,\gamma'_1$ (`cert-g`) |
| 内部闭包的支配来源 | 全局 `Strictᵝ`, 到 BTBO 为止 (`no-Bound`) | 地板 + 覆盖 (`dom-cov`), 单覆盖到 $\gamma'_1$ 为止 (`floor-wall`); 分层覆盖到 $\gamma'_3$ 的弹栈处 (`popOcc₃`) |
| $\gamma'_3$ 的证书 (`NextN.step 1`) | — | **缺**: 悬置的闭包 (§4) |
| `Gᴺ₂ : Goodᴺ (toZ t2ˢ)` | 骨架 `Gᴺ₂-of` 只差 `NextN` | 同; `NextN` 的 $k=0$ 已记号无关, $k\ge1$ 未得 |
| 标签 | `any-T2` (任意 `Goodᴺ` 的树 $\cong$ `T2ᴸ`) | 不变; $\gamma'_2$ 的标签只作验收 |


## §7 结论与边界

**定理 (编译, 记号无关).** `cov₁`, `cov-low`, `S⁺₀` (支配定理在 $\hat\chi_1$ 的实例); **`cert-g : ∀ η e → η ⊑ᴵ β₀ → Goodᶻ (toZ (gᵗ η e))`**, **`Gγ′₂`**, `Gᴺγ′₂`, `step0ᴺ`, `step0′` (NotFree 的 `NextN.step 0` 在一切 $Y\cong\chi_0$ 处); `Stop.cov-high` (以 $\gamma'_2$ 的证书为覆盖); 带增长前提的 `Stop.popOcc₃` ($\gamma'_3$ 的每个弹栈闭包满足 `Occ≺ᴳ`).

**否定 (编译).** `floor-wall`, `no-cov` (地板 $\Omega_1$ 恰好走到 $\mathtt{lvl}\,\gamma'_1$); 带增长前提的 `Stop.γ′₃-blocked` (单覆盖的 `Floor` 不能用于 $\gamma'_3$). 实例化 `S₃ = Stop Gγ′₂`, `A₂ = Accept Gγ′₂`; 增长前提由 `A₂.growth-lab` (经标签) 满足.

**字面与模 $\cong$.** `Gγ′₂` 是 Prefix 意义下 `toZ (gᵗ β₀ dχ₀)` 的**字面**证书 (对一切 $\eta$ 的分支证书与支配都有); `Gᴺγ′₂ = ofZ Gγ′₂` 是 `Goodᴺ` 证书; 两者的计值经 `ofZ-≅` 互模拟, 与任何其他证书的计值 $\cong$ (`force-≅`/`forceᴺ-≅`). 标签 $\gamma'_2$ 是验收 (`γ′₂ᴺ-label`).

**证书/标签状态.** 记号无关的证书: BTBO, $\gamma'_1$, $X_2$, $X_3$ (NotFree), **$\gamma'_2$ 与一切 $\psi_0(\Omega_\Omega+\Omega_\eta)$, $\eta\sqsubseteq\mathtt{lvl}\,\gamma'_1$ (本文)**. `Gᴺ₂ : Goodᴺ (toZ t2ˢ)` **未得**: 停在 `NextN.step 1` ($\gamma'_3$, 符号树 `gᵗ η₁ e`), 缺 §4 的悬置引理 (外加链的严格增长的记号无关证明). $\psi_0(\Omega_\Omega\cdot k)$ 与 $\psi_0(\Omega_\Omega\cdot\Omega_2)$ 未尝试 (在 $t_2$ 之后). $t_2$ 的标签定理仍是 GoodL 的经标签证书上的结果; 一旦 `Gᴺ₂` 存在, 标签由 NotFree 的 `any-T2-label` 直接验收.

**边界.** 树族是 Prefix 的符号族 (`ψᴾ`, 栈 `[]`/`[Ω̂]`), 即 `Goodᴺ (toZ t2ˢ)` 所在的族; 统一形 (Uniform2Base 的前缀塔) 上没有这套理论. 只导入已有模块, 不改任何已有文件, README 未改.
