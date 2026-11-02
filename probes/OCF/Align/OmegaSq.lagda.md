# $\psi_0(\Omega_\Omega^2)$: 标签为什么止步于 $\psi_0(\Omega_\Omega\cdot\Omega_2)$

> 接 [OmegaSqBase](OmegaSqBase.lagda.md) (低目标反例、`ψᵉ′`、第 0/1 层指数的带前缀引理 `WE₀`/`ZE₀`/`WE₁`/`ZE₁` 与好栈 `GoodE₀`/`GoodE₁`). 本文是决定性检验 (任务 4).
>
> 结论先说:
>
> 1. **`TΩ2-label` 未得, 且在现有的紧界闭包下不可得 (§3).** 精确停点: 闭包 `TΩ2′ˢ` 的链证书在第一个链点 $Y_0$ (标签 $t_{\Omega2}[0]=\psi_0(\psi_\Omega(\Omega_1))$) 处的分支证书 `Gg 0 Y₀`, 即 $\psi_0(\Omega_\Omega\cdot\Omega_{\mathtt{lvl}\,Y_0})$ 的证书与标签 $t_{\Omega2}[1]$. 它的后代 $\psi_0(\psi_\Omega(\Omega_2+1))$ (从 $t_{\Omega2}[1]$ 走 $\omega$-路径 $[0,1,0,0,3,1,0,0,1,0,0,2,0,0]$, `refl`) 是 OmegaSqBase §1 的低目标帧: 第 2 层的后继指数在目标 0 处; 再走 $[2,0,0,1]$ 是第 2 层帧之上的 $\hat\Omega$ 弹栈, 紧界闭包的第 0 点要 `Simᴵ 2 1` (**`noSim21`**, 编译的否定). 树侧的同一位置 (`lowˢ`) 是占位值 $0$, 没有证书能给它这个标签 (**`low-unlab`**, 编译的否定). 缺的引理 (类型精确地写成 **`BranchΩ`**): 对一切带标签 $t_{\Omega2}[m]$ 的 $Y$, 分支 $\psi_0(\Omega_\Omega\cdot\Omega_{\mathtt{lvl}\,Y})$ 带标签 $t_{\Omega2}[m+1]$. **`TΩ2-cond : BranchΩ → Σ (Goodᴸ (toZ TΩ2′ˢ)) λ G → Lab (forceᴸ _ G) tΩ2`** 已证, `TΩ2-step` 在此条件下 `refl`: 链的其余部分 (第 0 点、支配、单调、外层规则 6) 都已无条件到位, 缺的只有这一个分支引理, 而它要求非紧的闭包.
> 2. **新的无条件标签: $\psi_0(\Omega_\Omega\cdot\Omega_2)$ (§2).** `TΩ₂-label : Lab TΩ₂ᴸ tΩ₂`, $t_{\Omega_2}=\psi_0(\psi_\Omega(\Omega_2))$ ($t_{\Omega2}$ 沿 $[1,0,1,0,0,2]$ 的后代). 指数 $\Omega_2$ 在目标 0 处沿第 1 层的链折叠, 链点 $\psi_1(S+\Omega_\Omega\cdot\omega^{\chi})$ 的指数 $\chi$ 在第 1 层 (由 `WE₁` 标), 分支 $\psi_0(\Omega_\Omega\cdot\omega^{\chi_m})$ 的指数在第 1 层 (由 `ZE₁` 标). 这是第一个需要**第 1 层后继指数的帧** (`▹[ σ1 ]`) 的定理: 后代 $\psi_0(\psi_\Omega(\Omega_1+1))$ (从 $t_{\Omega_2}$ 走 $[1,0,1,0,0,2,0]$, `refl`) 的指数是第 1 层的后继, 帧产生于目标 0 ($=1-1$, 不是低目标). $\psi_0(\Omega_\Omega\cdot\Omega_n)$, $n\ge3$ 都含低目标帧 ($n=3$ 即 OmegaSqBase §1 的路径, $n=4$ 见 §3 的 `refl`), 所以 $\Omega_2$ 是紧界设计下 $\Omega$-指数的上限.
> 3. **一致性 (§1).** 新折叠在第 0 层指数上与旧的给出 $\cong$ 的树 (`Tη-agree`, 一切带结构标签的 $\eta$); `TΩ2′ˢ` 的第 0 点由通用的第 1 层引理 `ZE₁` 直接标记 (`TΩ2-0′-label`), 与 OmegaExp 专门构造的 `TΩ2-0ᴸ` $\cong$ (`TΩ2-0-agree`).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块与 OmegaSqBase, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaSq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ; z<suc; z1; intoˢ)
import OCF.Align.EBO as E
open E using (T; natT; fsn; fsT; cof; cω; cΩ; Ωt; γT; []<; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; Lab-≅; l0; l1)
open import OCF.Align.Stage2 using (Lab-uniq; Ωᵗ; tO)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; walk; walkD; tO-desc-NF)
open import OCF.Align.Standard using (d₀)
open import OCF.Align.UniformS using (_≅ˢ_; z≅; s≅; ≅ˢ-sym; Ωˢ-refl; two)
open import OCF.Align.Decouple using (Idx)
open import OCF.Align.Stage2Label using (one⁰)
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaKBase using (tΩ2; tΩ2-NF)
open import OCF.Align.OmegaExpBase
open import OCF.Align.OmegaExp using (ψΩ₀; GLη; Tη-label; tΩ1; tΩ1-NF; TΩ2-0ᴸ; TΩ2-0-label)
open import OCF.Align.OmegaSqBase
```

## §1 一致性: 新折叠与旧定理

**第 0 层指数.** `Tη′ˢ X = (∅ˢ ▹[ s₀ ] X) z1 z1` 是新折叠下的 $\psi_0(\Omega_\Omega\cdot\omega^X)$, 证书与标签是 `GoodE₀ Good∅` 的目标 0 字段; 与 OmegaExp 的 `Tη-label` 同标签, 经 `Lab-uniq` $\cong$.

```agda
Tη′ˢ : Ordˢ zero → Ordˢ zero
Tη′ˢ X = (∅ˢ ▹[ s₀ ] X) z1 z1

GLη′ : ∀ {X η} → Lab0ᴸ X η → X ≅ˢ X → NF₁ (ψΩ₀ η) → Σ (Goodᴸ (toZ (Tη′ˢ X))) λ G → Lab (forceᴸ _ G) (ψΩ₀ η)
GLη′ l ex nf = h0 (GoodE₀ Good∅ l ex) z1 z1 nf

Tη-agree : ∀ {X η} (l : Lab0ᴸ X η) (ex : X ≅ˢ X) (nf : NF₁ (ψΩ₀ η)) →
           forceᴸ _ (proj₁ (GLη′ l ex nf)) ≅ forceᴸ _ (proj₁ (GLη l ex nf))
Tη-agree l ex nf = Lab-uniq (proj₂ (GLη′ l ex nf)) (Tη-label l ex nf)
```

**$\psi_0(\Omega_\Omega^2)$ 的树与第 0 点.** `TΩ2′ˢ = (∅ˢ ▹Ω̂²′) z1 z1`, 形状同 OmegaExp 的 `TΩ2ˢ` (`refl`). 第 0 点 `t₀′` $=\psi_0(\Omega_\Omega\cdot\Omega_1)$ 的指数 $\Omega_1$ 在第 1 层, 结构标签 `LabL-Ω`; 通用引理 `ZE₁` (目标 0) 直接给出证书与标签 $t_{\Omega2}[0]$. OmegaExp 用专门的链 `chainE`/`atomE` 证同一件事; 两者 $\cong$.

```agda
gΩ : (η : Ordᴵ) → suc zero ⊑ᴵ η → Ordˢ zero
gΩ η e = ψᵉ′ ∅ˢ {ℓ = Mlev (suc zero) η e} (lim 0 (z<suc z1 z1)) (lim 0 zero) (λ q → lim 1 q) (Ωˢ η)

t₀′ : Ordˢ zero
t₀′ = ψᵉ′ ∅ˢ (z<suc z1 z1) zero (σ1 (z<suc z1 z1)) (Ωˢ (suc zero))

TΩ2′ˢ : Ordˢ zero
TΩ2′ˢ = (∅ˢ ▹Ω̂²′) z1 z1

_ : TΩ2′ˢ ≡ Ord₊ˢ.ŝ (suc zero) t₀′ gΩ
_ = refl

LΩ1 : LabL (Ωˢ (suc zero)) (Ωt (natT 1))
LΩ1 = LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)

GLΩ0′ : Σ (Goodᴸ (toZ t₀′)) λ G → Lab (forceᴸ _ G) (fsn tΩ2 0)
GLΩ0′ = ZE₁ Good∅ LΩ1 (Ωˢ-refl (suc zero)) (z<suc z1 z1) zero (σ1 (z<suc z1 z1)) tΩ1-NF

TΩ2-0′-label : Lab (forceᴸ _ (proj₁ GLΩ0′)) (fsn tΩ2 0)
TΩ2-0′-label = proj₂ GLΩ0′

TΩ2-0-agree : forceᴸ _ (proj₁ GLΩ0′) ≅ TΩ2-0ᴸ
TΩ2-0-agree = Lab-uniq TΩ2-0′-label TΩ2-0-label
```

**读法.** `GLΩ0′` 的推导: `ZE₁` 在 `LΩ1` 的 `gi` 行 ($\Omega_1$ 的共尾度 $\Omega_1$, $j=0$) 走 `liLabE`, 链在第 0 层, 链点 $\psi_0(\Omega_\Omega\cdot\omega^{\chi})$ 由 `gu` 行降到 `ZE₀` (第 0 层指数), 后者在后继处压 `▹[ s₀ ]` 帧 (`repGood₀`). 没有专门的链构造.

## §2 新标签: $\psi_0(\Omega_\Omega\cdot\Omega_2)$

**记号.** $t_{\Omega_2}=\psi_0(\psi_\Omega(\Omega_2))$ 是 $t_{\Omega2}$ 的后代 (`refl`), 标准形由 `tO-desc-NF`. $\psi_\Omega(\Omega_2)$ 的共尾度是 $\Omega_2=\Omega_{1+1}$ ($\psi_\Omega$ 穿透, `cofΩ2`), $\psi_0$ 处 $2>0$, 折叠, 链 $\gamma_0=\Omega_1$, $\gamma_{m+1}=\psi_1(\psi_\Omega(\gamma_m))$, $t_{\Omega_2}[m]=\psi_0(\psi_\Omega(\gamma_m))$ (`gtW`). $\psi_\Omega(\Omega_2)[\theta]=\psi_\Omega(\theta)$ (`fsTΩ2`, `refl`).

```agda
tΩ₂ : T
tΩ₂ = ψΩ₀ Ω₂

_ : walk tΩ2 (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []) ≡ tΩ₂
_ = refl

tΩ₂-NF : NF₁ tΩ₂
tΩ₂-NF = tO-desc-NF (walkD d₀ (1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []) (refl , refl , refl , refl , refl , refl , refl , tt))

cofΩ2 : cof (ψΩ Ω₂) ≡ cΩ (natT 1)
cofΩ2 = refl

fsTΩ2 : ∀ θ → fsT (ψΩ Ω₂) θ ≡ ψΩ θ
fsTΩ2 θ = refl

I₁ : Idx (natT 1)
I₁ = one⁰ , hs hz , lab1 , nf1
```

**引理 `ZΩ₂`.** 对任意好栈 `G : Goodˢ S ps`, 目标 0 处 $\psi_0(ps+\Omega_\Omega\cdot\Omega_2)$ 的证书与标签. 树: `Ωˢ two = limᵢ zero (up zero)`, `ψᵉ′` 在目标 0 处折叠 (`fold1E`, $0\prec1$), 链 `chainΩ m` 在第 1 层, 第 $m+1$ 点是 `ψᵉ′ S z (σ zero) (λ q → σ (suc q)) (chainΩ m)` (目标 1; `up zero` 子句定义性地展开). 链点的标签由 `WE₁` (目标 1, `I₁`), 输出由 `ZE₁` (目标 0); 两者的指数都在第 1 层. 这是 OmegaExpBase `foldLabS` 在 $f$ = `up zero` 时的特例.

```agda
module _ {S : Stk} {ps : T} (G : Goodˢ S ps) {L} (z p : zero <ᴵ L) (σ : Simᴵ two L) where

  σ₁ : Simᴵ (suc zero) L
  σ₁ q = σ (suc q)

  chainΩ : ℕ → Ordˢ (suc zero)
  chainΩ = iter (λ x → ψᵉ′ S z (σ zero) σ₁ x) (Ωˢ (suc zero))

  chainΩ-≅ : ∀ m → chainΩ m ≅ˢ chainΩ m
  chainΩ-≅ zero    = Ωˢ-refl (suc zero)
  chainΩ-≅ (suc m) = ψᵉ′-≅ (hR G) {z = z} {p = σ zero} {σ = σ₁} {z′ = z} {p′ = σ zero} {σ′ = σ₁} lo1 lo1 (≅ᴵ-refl _) (chainΩ-≅ m)

  γΩ₂ : ℕ → T
  γΩ₂ = γW ps (ψΩ Ω₂) (natT 1)

  chainΩL : ∀ m → LabL (chainΩ m) (γΩ₂ m)
  chainΩL zero    = LΩ1
  chainΩL (suc m) = WE₁ G (chainΩL m) (chainΩ-≅ m) z (σ zero) σ₁ I₁ (≅ᴵ-refl _) refl

  ZΩ₂ : NF₁ (πw [] ps (ψΩ Ω₂)) → Σ (Goodᴸ (toZ (ψᵉ′ S z p σ (Ωˢ two)))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (ψΩ Ω₂))
  ZΩ₂ nu =
    subst (λ W → Σ (Goodᴸ (toZ W)) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (ψΩ Ω₂))) (sym eqf)
          (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (fsm m)) (proj₂ (outp m))))
    where
    eqf = fold1E {S = S} {z = z} {p = p} {σ = σ} {q = zero} {f = Ord₊ˢ.up zero} (inj₁ (via z≅ zero))
    cω′ : cof (πw [] ps (ψΩ Ω₂)) ≡ cω
    cω′ = cofW [] ps (ψᵗ Ωᵗ Ω₂) []
    fsm : ∀ m → fsn (πw [] ps (ψΩ Ω₂)) m ≡ πw [] ps (ψΩ (γΩ₂ m))
    fsm m = gtW [] ps (ψᵗ Ωᵗ Ω₂) [] (natT 1) refl refl m
    outp : ∀ m → Σ (Goodᴸ (toZ (ψᵉ′ S z p σ₁ (chainΩ m)))) λ G′ → Lab (forceᴸ _ G′) (πw [] ps (ψΩ (γΩ₂ m)))
    outp m = ZE₁ G (chainΩL m) (chainΩ-≅ m) z p σ₁ (subst NF₁ (fsm m) (NF₁-fsn nu cω′ m))
```

**读法.** `chainΩL (suc m)` 的类型要 `LabL (ψᵉ′ S z (σ zero) σ₁ (chainΩ m)) (γΩ₂ (suc m))`, 而 `γΩ₂ (suc m)` 定义性地是 $\psi_1(ps+\psi_\Omega(\Omega_2)[\gamma_m])=\psi_1(ps+\psi_\Omega(\gamma_m))$ (`fsTΩ2` 是 `refl`), 正是 `WE₁` 在 $w=1$ 处的结论; 第 1 层的 `LabL` 就是 `LabL₊ 1`, 无需 `frL₊`. `outp m` 的树是 `ψᵉ′ S z p σ (up zero (chainΩ m))` 的 `up` 展开, 与 `fold1E` 的右边定义性相同.

**定理.** 空栈, 目标 0, 环境层号 3 (`σ` 把第 2 层嵌进 3; `z3`/`three` 取自 OmegaSqBase §3).

```agda
TΩ₂ˢ : Ordˢ zero
TΩ₂ˢ = ψᵉ′ ∅ˢ z3 z3 (λ q → suc q) (Ωˢ two)

GLΩ₂ : Σ (Goodᴸ (toZ TΩ₂ˢ)) λ G → Lab (forceᴸ _ G) tΩ₂
GLΩ₂ = ZΩ₂ Good∅ z3 z3 (λ q → suc q) tΩ₂-NF

TΩ₂ᴸ : Ordᶜ zero
TΩ₂ᴸ = forceᴸ (toZ TΩ₂ˢ) (proj₁ GLΩ₂)

TΩ₂-label : Lab TΩ₂ᴸ tΩ₂
TΩ₂-label = proj₂ GLΩ₂
```

**读法.** 推导链: `ZΩ₂` → (链点) `WE₁` 于第 1 层的 `LabL`; (输出) `ZE₁`. 第 1 层的后继从哪里来: 链点 $\chi$ 是目标 1 的折叠输出, 本身从不是后继; 但它在目标 0 处被折叠访问时, 和 $\Omega_1+\Omega_1$ (来自 $\psi_1(1)=\lim\Omega_1\cdot m$) 的折叠链的第 0 点 $\Omega_0=1$ 落进和的末项, 给出第 1 层的后继 $\Omega_1+1$ (与 OmegaSqBase §1 的机制相同, 低一层). 下面的 `refl` 给出这个后代; 它的树在 `ZE₁` 的 `gs` 行由 `repGood₁`/`GoodE₁` 压 `▹[ σ1 ]` 帧. 这是 OmegaExpBase 的占位子句在第 1 层被真子句取代后的第一个用处; 与第 2 层不同, 这里帧在目标 $0=1-1$ 产生, 紧界闭包放得下 (`σ1` 只要 $0<^\mathsf I\ell$).

```agda
_ : walk tΩ₂ (1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []) ≡ ψΩ₀ (ψᵗ (natT 1) [] ∷ 𝟏 ∷ [])
_ = refl
```

## §3 任务 4: `TΩ2-label` 的状态

**条件定理.** 链证书的其余字段都已无条件: 第 0 点 (`GLΩ0′`), 第 0 点与分支的支配 (`one⊑lab`, 界 $1$), 输出的单调 (`ĉᴸ-mk` 由标签). 唯一的前提是分支引理 `BranchΩ`: 在带标签 $t_{\Omega2}[m]$ 的点 $Y$ 处, 分支 `gΩ (lvl Y) e` $=\psi_0(\Omega_\Omega\cdot\Omega_{\mathtt{lvl}\,Y})$ 的证书与标签 $t_{\Omega2}[m+1]$. 在此条件下树的外层 FGH 方程 (规则 6) 是 `refl`.

```agda
BranchΩ : Set
BranchΩ = ∀ m Y (hY : HS Y) → Lab Y (fsn tΩ2 m) → (e : suc zero ⊑ᴵ toLevel Y hY) →
          Σ (Goodᴸ (toZ (gΩ (toLevel Y hY) e))) λ G → Lab (forceᴸ _ G) (fsn tΩ2 (suc m))

TΩ2-cond : BranchΩ → Σ (Goodᴸ (toZ TΩ2′ˢ)) λ G → Lab (forceᴸ _ G) tΩ2
TΩ2-cond B =
  ĉᴸ-mk tΩ2-NF refl K (proj₁ GLΩ0′) (proj₂ GLΩ0′)
        (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
        (λ k → CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
  where
  K = ccᴸ (fsn tΩ2) (proj₁ GLΩ0′) (proj₂ GLΩ0′) (one⊑lab _ (proj₂ GLΩ0′) tΩ1-NF []<)
          (λ m Y hY lY e → proj₁ (B m Y hY lY e)) (λ m Y hY lY e → proj₂ (B m Y hY lY e))
          (λ m Y hY lY e → one⊑lab _ (proj₂ (B m Y hY lY e)) (NF₁-fsn tΩ2-NF refl (suc m)) []<)

module _ (B : BranchΩ) where
  TΩ2ᴸ : Ordᶜ zero
  TΩ2ᴸ = forceᴸ (toZ TΩ2′ˢ) (proj₁ (TΩ2-cond B))

  χΩ2 : ℕ → Ordᶜ zero
  χΩ2 n = sq′ TΩ2ᴸ n
    where
    sq′ : Ordᶜ zero → ℕ → Ordᶜ zero
    sq′ (Ord₊.lim f) n = f n
    sq′ x n = x

  _ : TΩ2ᴸ ≡ Ord₊.lim χΩ2
  _ = refl

  TΩ2-step : ∀ n → FGH TΩ2ᴸ n ≡ FGH (χΩ2 n) n
  TΩ2-step n = refl
```

**`BranchΩ` 不能在紧界设计下证明.** 它在 $m=0$ 就要 $t_{\Omega2}[1]=\psi_0(\psi_\Omega(\Omega_{t_{\Omega2}[0]}))$, 指数是 $\Omega_\eta$, $\eta=\mathtt{lvl}\,Y_0$ 是可数的大序数 (远大于 3). 它的一个 $\omega$-后代就是 OmegaSqBase §1 的低目标帧 (下面两个 `refl`), 其后 $[2,0,0,1]$ 是 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_\Omega)$ (`low-pop`). `Lab` 遗传, 所以 `BranchΩ 0` 蕴含这些点在 `gΩ` 的计值树里都带标签. 但:

- 现有的 `ψᵉ′` 在第 2 层后继处是占位值: 同一记号点的符号树 (`lowˢ`, OmegaSqBase §3) 是 $0$, 任何证书都不给它这个标签 (`low-unlab`);
- 把占位换成真帧也不行: 第 2 层指数的帧在 $\hat\Omega$ 弹出的紧界闭包里的第 0 点处, 环境层号是 $1$, 要 `Simᴵ 2 1` (`noSim21`); 分支处是 OmegaExp 的 `noSim2`.

```agda
_ : fsn tΩ2 1 ≡ ψΩ₀ (Ωt tΩ1)
_ = refl

branch-low : walk (fsn tΩ2 1) (0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ []) ≡ ψΩ₀ Ω₂+1
branch-low = refl

_ : walk (ψΩ₀ (Ωt (natT 4))) (1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ []) ≡ ψΩ₀ (ψᵗ (natT 3) [] ∷ 𝟏 ∷ [])
_ = refl
```

最后一个 `refl` 说明这不是 $\Omega_3$ 的偶然: $\psi_0(\psi_\Omega(\Omega_n))$ 沿 $[1,0^{n-1},1,0,0,2,0^{n-1}]$ 到达 $\psi_0(\psi_\Omega(\Omega_{n-1}+1))$ ($n=3$ 是 OmegaSqBase 的 9 步路径, $n=4$ 上面 `refl`, $n=5$ 由 `ebo.py` 核对), 对 $n\ge3$ 都是低目标帧. 所以 $\Omega_2$ 是紧界设计下能标记的最大的有限 $\Omega$-指数.

**缺的是什么 (精确).** 非紧的闭包与暴露地板的栈:

1. 树侧: 栈类型以帧指数的层号地板 $F$ 为下标 (`Stk F`, 计值时带 $F\prec^\mathsf I\ell$, 帧的 `Sim` 由它与 `tr`/`tr⁻` 现造); 弹出 $\hat\Omega$ (与 $\hat\Omega^2$) 时闭包的界取 $\max(i,F)+1$, 第 0 点的环境层号同. 本例 $F=2$ 的帧在目标 0 弹出, 界 $3$, 第 0 点 $\psi_0(\psi_\Omega(\Omega_2)+\Omega_1)$ 在环境层号 $3$ 上, 第 2 层帧的折叠链在目标 1 有地方落脚.
2. 标签侧: GoodLBase `gŝ` 行的地板字段已对任意出现于一切 $t[\theta]$ 的带 `Idx` 下标 $w$ 成立 (界 $c\sqsubseteq\mathtt{lvl}\,w+1$), 不必改; 支配 `domS` 不变. 要补的是 "树的层号地板 $F$ $\preceq$ 某个在帧指数的标签中出现的下标" 这一条, 它在推导上可以从 `gi` 行的 `Idx` 读出 (第 $F$ 层的帧指数在其 `limᵢ` 节点处的 $j\cong\mathtt{lvl}\,\nu$, $\nu$ 是标签的共尾度下标, 出现于标签), 但 `LabL` 对小标签的高层树不排斥, 所以要把它作为前提带进 `WE`/`ZE`.
3. 于是 `WEₖ`/`ZEₖ` 对一切 $k$ (而不只 $k\le1$), 且 `BranchΩ` 由对 `LabL-Ω` 推导的递归得到.

## §4 对比表

| | OmegaExp | 本文 |
|---|---|---|
| 指数折叠 | `ψᵉ`: 第 0 层后继真, 第 $\ge1$ 层占位 $\Omega_i$ | `ψᵉ′`: 第 0、1 层后继真 (`▹[ s₀ ]`, `▹[ σ1 ]`), 第 $\ge2$ 层占位 $0$ |
| 栈类型 | `Stk` | `Stk` (不变) |
| 指数作尾巴的带前缀引理 | 无 (只有 `GoodE` 的字段, `Sim` 固定) | `WE₀`/`ZE₀` (任意 `Sim`), `WE₁`/`ZE₁` |
| 好栈 | `Good∅`, `GoodΩ`, `GoodE` | 另加 `GoodE₀`, `GoodE₁` (`repGood₀`/`repGood₁`) |
| 互模拟 | `ψᵉ0-≅` (第 0 层) | `ψᵉ′-≅` (第 $\le1$ 层, `Lo`) |
| $\psi_0(\Omega_\Omega\cdot\omega^\eta)$, $\eta$ 可数 | `Tη-label` | `GLη′`, `Tη-agree` ($\cong$) |
| $\psi_0(\Omega_\Omega\cdot\Omega)$ | `TΩ2-0-label` (专门的链) | `TΩ2-0′-label` (通用 `ZE₁`), `TΩ2-0-agree` |
| $\psi_0(\Omega_\Omega\cdot\Omega_2)$ | — | **`TΩ₂-label`** |
| $\psi_0(\Omega_\Omega^2)$ | 首链点 | `TΩ2-cond` (以 `BranchΩ` 为前提), 条件下 `TΩ2-step` |
| 低目标情形 | 未定 (深 11 未见) | **出现** (`low-term`, 路径长 15); 树侧 `low-tree`/`low-unlab`; `noSim21` |

## §5 结论与边界

**字面成立 (`refl`):** OmegaSqBase 的 `low-walk` (`walk tΩ2 pathLow ≡ ψ₀(ψ_Ω(ψ₂(1)))`)、`[2] ↦ Ω₂+Ω₂`、`[2,0] ↦ Ω₂+Ω₁`、`low-term` (`[2,0,0] ↦ ψ₀(ψ_Ω(Ω₂+1))`)、`low-cof`、`low-c1`、`low-pop`、`low-tree` 与两个 `kl`; 本文的 `TΩ2′ˢ ≡ ŝ 1 t₀′ gΩ`、`walk tΩ2 [1,0,1,0,0,2] ≡ tΩ₂`、`walk tΩ₂ [1,0,1,0,0,2,0] ≡ ψ₀(ψ_Ω(Ω₁+1))`、`cofΩ2`、`fsTΩ2`、`fsn tΩ2 1 ≡ ψΩ₀ (Ωt tΩ1)`、`branch-low`; 条件下的 `TΩ2ᴸ ≡ lim χΩ2` 与 `TΩ2-step`.

**定理 (标签按 Correspond 的 `Lab`, 树只到 $\cong$):**

1. **`TΩ₂-label : Lab TΩ₂ᴸ tΩ₂`** ($\psi_0(\Omega_\Omega\cdot\Omega_2)$, 无条件), 一般形式 `ZΩ₂` (任意好栈前缀).
2. `TΩ2-0′-label` 与 `TΩ2-0-agree`; `GLη′` 与 `Tη-agree`.
3. **`TΩ2-cond : BranchΩ → Σ (Goodᴸ (toZ TΩ2′ˢ)) λ G → Lab (forceᴸ _ G) tΩ2`** (条件定理).
4. 编译的否定 (OmegaSqBase): **`noSim21 : Simᴵ 2 1 → ⊥`**, **`low-unlab`**.

**标签状态.** 按 README 的认证准则: $\psi_0(\Omega_\Omega\cdot\Omega_2)$ 的遗传标签是**无条件定理**; $\psi_0(\Omega_\Omega^2)$ 的标签**未得**, 精确停点是 `BranchΩ 0` (第一个链点处的分支), 精确的阻碍是低目标帧 (`low-term`, 从 $t_{\Omega2}[1]$ 走 `branch-low` 的路径), 在紧界闭包下不可克服 (`noSim21`, `noSim2`); 需要的是 §3 的非紧闭包 (树侧的新栈类型) 与 "帧层号由标签中的下标支配" 的前提 (标签侧). 封存的 src BTBO 不受影响.

**边界.**

- `ψᵉ′` 的第 $\ge2$ 层后继仍是占位值; 本文的无条件定理不经过它 (`ZΩ₂` 只把第 2 层的 $\Omega_2$ 作为 `limᵢ` 折叠, 链点与分支的指数都在第 1 层).
- 互模拟 `ψᵉ′-≅` 只对第 $\le1$ 层的指数; `ZΩ₂` 的链自互模拟经 `up` 展开落到第 1 层.
- 数值未算 (`FGH TΩ₂ᴸ 0` 未求值).
- 不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
