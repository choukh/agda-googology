# 悬置不变量 (二): 链上的证书与 $\psi_0(\Omega_\Omega\cdot2)$

> 接 [PendingBase](PendingBase.lagda.md) (三层遗传好树, 闭包定理 `Fold.Good-ψ1`, 唯一的参数是弹栈覆盖 `PopCov`)、[Growth](Growth.lagda.md) (链的严格增长 `growth-mono`) 与 [NotFree](NotFree.lagda.md) (`NextN`, `Gᴺ₂-of`, `any-T2`). 决定性检验.
>
> 结论先说:
>
> 1. **`Gᴺ₂ : Goodᴺ (toZ t2ˢ)` 成立, 构造不读记号 (§4).** TreeNF 的停点 `NextN.step 1` ($\gamma'_3$) 与其后的一切 $k$ 由同一步 `stepL` 给出. 标签只在验收里 (§6): `A₂.tree : forceᴺ _ Gᴺ₂ ≅ T2ᴸ`, `A₂.label`.
> 2. **对链指标阶段无关 (§2–§3).** 每一阶段只做一件事: 把上一个链点的证书变成新一层的弹栈覆盖 (`PC-step`, 一次有界三歧). 内部闭包的支配全部由 `Fold.Good-ψ1` 自动得到, 没有按阶段定制的支配论证.
> 3. **悬置路径确实出现 (§5).** 对 $\gamma'_2$ 的任意证书, 编译出层号 $b\cong\beta_0$ ($b<^\mathsf I\eta_1$) 与非零的 $d<^\mathsf I b$, $d\prec\beta_0$; 穿透与链点的形状也编译了. 有界记号搜索没找到实例, 只是因为路径比搜索深度长. 所以两层机器不是虚设: 证明确实走 `biV` 的吸收情形 ($\kappa\succ j$). 但 "该闭包的 `ColC` 为假" 这一半没有树侧的编译否定, 见 §7.
> 4. **范围.** 阶段无关只对单 $\hat\Omega$ 的链 ($t_2$ 之内) 证明了; 更长的栈还没有证, 见 §7.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Pending where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Ordˢ; Ωˢ; toZ; Goodᶻ; force; force-HS; t2ˢ; intoˢ)
open import OCF.Align.UniformS using (Ωˢ-refl; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ʳ; ψ1-cong; Ω-monoᵒ; idO)
open import OCF.Align.Omega2 using (gᵗ; dom1)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; ofZ; ofZ-≅; χ₀; hχ₀; dχ₀; NextN; Gᴺ₂-of; module ChainN)
open import OCF.Align.TreeNFBase using (NZ; one⊑; CovΛ)
open import OCF.Align.TreeNF using (β₀; e₁; G₁; χ₀≅G₁; cov-low; below-η; ≺→⊑ᴵ)
open import OCF.Align.Growth using (growth-mono; two⊑β₀)
open import OCF.Align.PendingBase
```

## §1 弹栈覆盖 `PC`

`PC η`: 每个非零的 $i\prec\eta$ 都有一个 $\varphi\sqsubseteq i$ 覆盖 $i+1$. 这只说层号与链点证书, 与环境无关; `PC→PopCov` 把它转成 `Fold` 要的 `PopCov` (`below-η`: 环境 `Mlev 1 η e` 里的非零目标都 $\prec\eta$). **`cert-PC`**: 有 `PC η` 就有 $\psi^{[\hat\Omega]}_0(\Omega_\eta)$ 的证书. 这就是闭包定理在链上的全部用法.

## §2 一步: 从证书到下一层覆盖

`PC-base`: $\varphi=1$, 覆盖 $\hat\chi_1$ (`cov-low`), 即 TreeNF 的地板 $\Omega_1$. `PC-step`: 若 $\eta\prec\eta'$ 且 $\hat\chi_\eta$ 覆盖一切 $c\sqsubseteq\eta'$, 则 `PC η` 推出 `PC η′`. 证明是 TreeNF 的 `popOcc₃` 的三歧的一般形 (`pickP`, 不用 `with`): $i\prec\eta$ 用旧覆盖, 否则 $\varphi=\eta$.

```agda
PC : Ordᴵ → Set
PC η = ∀ {i L} → zero <ᴵ L → i <ᴵ L → NZ i → i ≺ᴵ η → Cvd i (suc i)

PC-≅ : ∀ {η η′} → η ≅ᴵ η′ → PC η → PC η′
PC-≅ e pc z p nz r = pc z p nz (≺ᴵ-respʳ r (≅ᴵ-sym e))

PC→PopCov : ∀ {η} (e : suc zero ⊑ᴵ η) → PC η → PopCov (Mlev (suc zero) η e)
PC→PopCov e pc p nz = pc (lim 0 zero) p nz (below-η nz p)

cert-PC : ∀ η (e : suc zero ⊑ᴵ η) → PC η → Goodᶻ (toZ (gᵗ η e))
cert-PC η e pc = Fold.Good-ψ1 (PC→PopCov e pc) {p = lim 0 zero} {σ = λ q → lim 1 q} {z = lim 0 zero} (Good-Ωⱽ η ⊑ᴵ-refl) (Ωˢ-refl η)

PC-base : PC β₀
PC-base z p nz r = suc zero , cov-low (s⊑′ r) , one⊑ z p nz

pickP : ∀ {η η′ i b b′} → PC η → η ≅ᴵ b → i ≅ᴵ b′ → (∀ {c} → c ⊑ᴵ η′ → CovΛ η c) → i ≺ᴵ η′ →
        ∀ {L} → zero <ᴵ L → i <ᴵ L → NZ i → (b′ ≺ᴵ b ⊎ b ≺ᴵ b′ ⊎ b′ ≅ᴵ b) → Cvd i (suc i)
pickP pc eb ei cov r z p nz (injᵃ s) = pc z p nz (≺ᴵ-respˡ ei (≺ᴵ-respʳ s (≅ᴵ-sym eb)))
pickP {η} pc eb ei cov r z p nz (injᵇ s) = η , cov (s⊑′ r) , ≺→⊑ᴵ (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ei)))
pickP {η} pc eb ei cov r z p nz (injᶜ c) = η , cov (s⊑′ r) , ≅ᴵ→⊑ᴵ (≅ᴵ-trans eb (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ei)))

PC-step : ∀ {η η′} → η ≺ᴵ η′ → (∀ {c} → c ⊑ᴵ η′ → CovΛ η c) → PC η → PC η′
PC-step (via eb q) cov pc z p nz r@(via ei q′) = pickP pc eb ei cov r z p nz (<ᴵ-dec q′ q)
```

## §3 链的不变量 `Link`

`Link Y`: $Y$ 是某个链点 $\psi^{[\hat\Omega]}_0(\Omega_{\eta_-})$ 的计值, $\eta_-\prec\mathtt{lvl}\,Y$, 且 `PC (lvl Y)`. `StepM` 以新证书 $G$ 为模块参数 (工程注记同 TreeNF: 证书别名别进类型): `growth-mono` 给 $\eta\prec\mathtt{lvl}\,G$, `PC-step` 给新覆盖, 证书本身当覆盖用 (`e , G , h`). 这里没有任何 $m$ 特有的内容.

## §4 决定性检验

`next : NextN` 的不变量取 `Link` (与 $k$ 无关), `Gᴺ₂ = Gᴺ₂-of next`. `link₀` 的增长由 `two⊑β₀` 给出.

```agda
record Link (Y : Ordᶜ zero) : Set where
  field
    η₋ : Ordᴵ
    e₋ : suc zero ⊑ᴵ η₋
    G₋ : Goodᶻ (toZ (gᵗ η₋ e₋))
    eY : Y ≅ force _ G₋
    g₋ : suc η₋ ⊑ᴵ toLevel (force _ G₋) (force-HS _ G₋)
    pc : PC (toLevel (force _ G₋) (force-HS _ G₋))

module StepM (Y : Ordᶜ zero) (hY : HS Y) (e : suc zero ⊑ᴵ toLevel Y hY) (l : Link Y)
             (G : Goodᶻ (toZ (gᵗ (toLevel Y hY) e))) where
  open Link l
  η : Ordᴵ
  η = toLevel Y hY

  eη : toLevel (force _ G₋) (force-HS _ G₋) ≅ᴵ η
  eη = toLevel-≅ (force-HS _ G₋) hY (≅-sym eY)

  hη₋ : suc η₋ ⊑ᴵ η
  hη₋ = ⊑ᴵ-≅ʳ g₋ eη

  grow : η ≺ᴵ toLevel (force _ G) (force-HS _ G)
  grow = ≺ᴵ-respˡ (≅ᴵ-sym eη) (growth-mono e₋ e hη₋ G₋ G)

  pcN : PC (toLevel (force _ G) (force-HS _ G))
  pcN = PC-step grow (λ h → e , G , h) (PC-≅ eη pc)

  new : Link (forceᴺ _ (ofZ G))
  new = record { η₋ = η ; e₋ = e ; G₋ = G ; eY = ofZ-≅ G ; g₋ = s⊑′ grow ; pc = pcN }

  one : suc zero ⊑ᴵ toLevel (forceᴺ _ (ofZ G)) (forceᴺ-HS _ (ofZ G))
  one = ⊑ᴵ-≅ʳ (⊑ᴵ-trans e (≺→⊑ᴵ grow)) (toLevel-≅ (force-HS _ G) (forceᴺ-HS _ (ofZ G)) (≅-sym (ofZ-≅ G)))

  mono : force _ G₋ ⊑ force _ G
  mono = ψ1-cong {ℓ = Mlev (suc zero) η₋ e₋} {ℓ′ = Mlev (suc zero) η e}
                 {p = lim 0 zero} {p′ = lim 0 zero} {σ = λ q → lim 1 q} {σ′ = λ q → lim 1 q} {z = lim 0 zero} {z′ = lim 0 zero}
                 {x = Ωˢ η₋} {y = Ωˢ η} (Ω-monoᵒ (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) hη₋)) idO G₋ G

  rise : Y ⊑⁰ forceᴺ _ (ofZ G)
  rise = ⊑-trans (≅→⊑ eY) (⊑-trans mono (≅→⊑ (≅-sym (ofZ-≅ G))))

stepL : ∀ Y (hY : HS Y) (e : suc zero ⊑ᴵ toLevel Y hY) → Link Y →
        Σ (Goodᴺ (toZ (gᵗ (toLevel Y hY) e))) λ G →
          Link (forceᴺ _ G) × Σ (suc zero ⊑ᴵ toLevel (forceᴺ _ G) (forceᴺ-HS _ G)) λ _ → Y ⊑⁰ forceᴺ _ G
stepL Y hY e l = go (cert-PC (toLevel Y hY) e (PC-≅ (StepM-η≅ l) (Link.pc l)))
  where
  StepM-η≅ : (l : Link Y) → toLevel (force _ (Link.G₋ l)) (force-HS _ (Link.G₋ l)) ≅ᴵ toLevel Y hY
  StepM-η≅ l = toLevel-≅ (force-HS _ (Link.G₋ l)) hY (≅-sym (Link.eY l))
  go : (G : Goodᶻ (toZ (gᵗ (toLevel Y hY) e))) →
       Σ (Goodᴺ (toZ (gᵗ (toLevel Y hY) e))) λ G′ →
         Link (forceᴺ _ G′) × Σ (suc zero ⊑ᴵ toLevel (forceᴺ _ G′) (forceᴺ-HS _ G′)) λ _ → Y ⊑⁰ forceᴺ _ G′
  go G = ofZ G , StepM.new Y hY e l G , StepM.one Y hY e l G , StepM.rise Y hY e l G

module Base (G : Goodᶻ (toZ (gᵗ (suc zero) e₁))) (eY : χ₀ ≅ force _ G) where
  eβ : β₀ ≅ᴵ toLevel (force _ G) (force-HS _ G)
  eβ = toLevel-≅ hχ₀ (force-HS _ G) eY

  link₀ : Link χ₀
  link₀ = record { η₋ = suc zero ; e₋ = e₁ ; G₋ = G ; eY = eY ; g₋ = ⊑ᴵ-≅ʳ two⊑β₀ eβ ; pc = PC-≅ eβ PC-base }

link₀ : Link χ₀
link₀ = Base.link₀ G₁ χ₀≅G₁

next : NextN
next = record { Inv = λ _ Y → Link Y ; inv₀ = link₀ ; step = λ k Y hY e l → stepL Y hY e l }

Gᴺ₂ : Goodᴺ (toZ t2ˢ)
Gᴺ₂ = Gᴺ₂-of next
```

## §5 悬置路径确实出现

**路径.** $\psi^{[\hat\Omega]}_0(\Omega_{\eta_1})$ 沿 $\eta_1$ 下降到 $\Omega_{b+1}$ (`b <ᴵ η₁`, 只经 `lim`/`suc`), 取链点 $c_1=\psi^{[\hat\Omega]}_b(\Omega_b)$, 其弹栈闭包界 $b+1$, 覆盖 $\varphi=\beta_0$ ($b\cong\beta_0$). $\Omega_b$ 下降到 $\Omega_{d+1}$ ($d<^\mathsf I b$), `pen` 给出 $\psi^{[\hat\Omega]}_b(\Omega_{d+1})=\mathrm{lim}_d(y\mapsto\psi^{[\hat\Omega]}_b(y))$, 于是外层目标 0 在 $d$ 处折叠, `chain-one` 给出链点 $\psi^{[\hat\Omega]}_d(\psi^{[\hat\Omega]}_b(\Omega_d))$: 界 $b+1$ 的闭包被 $d\prec\beta_0$ 映射, 地板只再生 $\Omega_d$, 处于悬置; 输出 $\psi^{[\hat\Omega]}_0(\psi^{[\hat\Omega]}_b(\cdot))$ 又把它托回 $\Omega_b$. 下降经过 `suc` 时 (层号 $a+1$, $b<^\mathsf I a$) 走的是 $\Omega_{a+1}$ 的链点 $\psi^{[\hat\Omega]}_a(\Omega_a)$, 外面多包一层 $\psi_a$, $a\succ b$; 形状不变, 被压低的闭包的界只会更高.

**编译了什么.** `node-of`/`Walk.node`: 对 $\gamma'_2$ 的任意证书, 这样的 $b,d$ 存在 (由增长与 $1\prec\beta_0$); `pen`, `chain-one`: 上面两步的形状. **没有编译的:** 从 $\Omega_{\eta_1}$ 到这个节点的整条折叠路径的 `refl` 见证 (要展开证书, 不可行), 以及该闭包的 `ColC` 为假 (见 §7). `Walk` 不用 `with`、把增长与 $1\prec\beta_0$ 作模块参数, 是因为在模块内直接写 `Growth₁.growth₁ G` 与 `sim two⊑β₀ zero` 再 `with` 时, 检查超过 180 s.

`PC-lim`: 覆盖对层号的极限封闭, 单行.

```agda
open import OCF.Align.Prefix using (Ord₊ˢ; outˢ; trˢ; tr⁻ˢ; Uˢ)
open import OCF.Align.UniformS using (ψ1)
open import OCF.Align.Stage2Label using (chain1)
open import OCF.Align.Growth using (module Growth₁)
open import OCF.Align.TreeNF using (module Stop)
open import OCF.Align.Symbolic using (σ1)

PC-lim : ∀ {f s} → (∀ n → PC (f n)) → PC (lim f s)
PC-lim h z p nz (via e (lim n q)) = h n z p nz (via e q)

pen : ∀ {d a ℓ} {p : a <ᴵ ℓ} {σ : Simᴵ (suc d) ℓ} {z : zero <ᴵ ℓ} → d ≺ᴵ a →
      Σ Ordᴵ λ b → Σ (b <ᴵ a) λ r → Σ (d ≅ᴵ b) λ e →
        ψ1 p σ z (Ωˢ (suc d)) ≡ Ord₊ˢ.limᵢ r (λ u → ψ1 p σ z (Ord₊ˢ.up zero (tr⁻ˢ e (outˢ (<→◃ r) u))))
pen {p = p} {σ = σ} h with <ᴵ-dec (σ zero) p
... | injᵃ (via e r) = _ , r , e , refl
... | injᵇ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans h c))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respˡ (≅ᴵ-sym c) h))

chain-one : ∀ {j k ℓ} (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) →
            chain1 σ z q f 1 ≡ ψ1 (σ q) σ z (f (intoˢ (<→◃ q) (Ωˢ j)))
chain-one σ z q f = refl

node-of : ∀ {B η} → suc zero ≺ᴵ B → B ≺ᴵ η →
          Σ Ordᴵ λ b → b <ᴵ η × B ≅ᴵ b × (Σ Ordᴵ λ d → d <ᴵ b × NZ d × d ≺ᴵ B)
node-of h (via eb q) = go (≺ᴵ-respʳ h eb)
  where
  go : suc zero ≺ᴵ _ → Σ Ordᴵ λ b → b <ᴵ _ × _ ≅ᴵ b × (Σ Ordᴵ λ d → d <ᴵ b × NZ d × d ≺ᴵ _)
  go (via e′ q′) = _ , q , eb , _ , q′ , NZ-≅ tt (≅ᴵ-sym e′) , ≺ᴵ-respʳ (via (≅ᴵ-refl _) q′) (≅ᴵ-sym eb)

module Walk (G : Goodᶻ (toZ (gᵗ β₀ dχ₀))) (g : β₀ ≺ᴵ Stop.η₁ G) (one≺ : suc zero ≺ᴵ β₀) where
  node : Σ Ordᴵ λ b → b <ᴵ Stop.η₁ G × β₀ ≅ᴵ b × (Σ Ordᴵ λ d → d <ᴵ b × NZ d × d ≺ᴵ β₀)
  node = node-of one≺ g

module WalkAny (G : Goodᶻ (toZ (gᵗ β₀ dχ₀))) = Walk G (Growth₁.growth₁ G) (sim two⊑β₀ zero)
```

```agda
PC-mono : ∀ {η η′} → η′ ⊑ᴵ η → PC η → PC η′
PC-mono h pc z p nz (via e q) = pc z p nz (≺ᴵ-respˡ e (sim h q))

cert-low : ∀ η (e : suc zero ⊑ᴵ η) → η ⊑ᴵ β₀ → Goodᶻ (toZ (gᵗ η e))
cert-low η e h = cert-PC η e (PC-mono h PC-base)

module CN = ChainN next
```

## §6 验收 (记号只在这里)

`any-T2`/`any-T2-label` 是 NotFree 的验收层: 任意 `Goodᴺ (toZ t2ˢ)` 证书的计值树 $\cong$ GoodL 的 `T2ᴸ`, 且带标签 $t_2$. 以证书为模块参数 (工程注记同 TreeNF), 文末实例化为 `Gᴺ₂`.

```agda
open import OCF.Align.NotFree using (any-T2; any-T2-label)
open import OCF.Align.GoodL using (T2ᴸ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.Stage2 using (t2)

module Accept (G : Goodᴺ (toZ t2ˢ)) where
  tree : forceᴺ _ G ≅ T2ᴸ
  tree = any-T2 G

  label : Lab (forceᴺ _ G) t2
  label = any-T2-label G

module A₂ = Accept Gᴺ₂
```

## §7 结论与边界

**定理 (编译).** `PC-base`, `PC-step`, `PC-lim`, `PC-mono`, `PC→PopCov`; **`cert-PC : PC η → Goodᶻ (toZ (gᵗ η e))`**; `cert-low` (TreeNF 的 `cert-g` 的结论, 不经 `Floor`); `Link`, `stepL`, `link₀`; **`next : NextN`**; **`Gᴺ₂ : Goodᴺ (toZ t2ˢ)`**; `CN.Gk k` (第 $k$ 个链点的 `Goodᴺ` 证书, 其中 `CN.Gk 1` 是 $\gamma'_3$, 即原停点 `NextN.step 1`). 验收: `A₂.tree : forceᴺ _ Gᴺ₂ ≅ T2ᴸ`, `A₂.label`.

**路径确实出现 (§5).** 结构部分编译 (`pen`, `chain-one`, `node-of`, `Walk.node`); "悬置闭包的 `ColC` 为假" 这一半**没有**树侧的编译否定 (缺树上 $\psi^{[\hat\Omega]}_0(\psi^{[\hat\Omega]}_d(\cdot))$ 的上界引理), 依据是记号侧的 `dip` (NotFree, `refl`) 与 TreeNF 的 `floor-wall`/`no-cov` (再生的低地板推不出支配).

**边界.** (i) 本文与 PendingBase 只在 Prefix 的符号族 (栈 `[]`/`[Ω̂]`) 上; 闭包定理的阶段无关是**对链指标 $m$** 的. 对 $\Omega_\Omega\cdot k$ ($k\ge3$)、$\Omega_\Omega\cdot\omega$、$\Omega_{\Omega+1}$ 的折叠还没有证: 那里栈更长, 不能从本文直接推出. (ii) 三层不变量是**充分**的; 本文没有证明任何不带悬置层的证明都不可能. (iii) `PC-lim` 之后的对角点 $\psi^{[\hat\Omega]}_0(\Omega_{\lim\zeta})$ 不再增长 (Growth 的 `no-growth`), 所以这条链在 $t_2$ 处停, 与 $\psi_0(\Omega_\Omega\cdot2)$ 是单 $\hat\Omega$ 的不动点一致. (iv) 只导入已有模块, 不改任何已有文件, README 未改.
