> **机械克隆.** 由 `DecoupleBase` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 前缀尾巴的一级标签: 带前缀的 $\psi_0$、$\psi_1$ 的上下文引理

> 接 [Stage2Label](Stage2Label.lagda.md) §9 与 [UniformS](UniformS.lagda.md). 本文是 [Decouple](Decouple.lagda.md) 的前半: 在符号树族 `Ordˢ` 上定义**一级遗传标签** `Lab₁` (尾巴在第 $\le1$ 层的项, 共尾度至多 $\Omega_1$), 证明两条上下文引理, 把 $\psi_0(\Omega_\Omega+\Omega_2)$ 的遗传标签归约为两条关于**不带前缀**的 $\psi_1(\Omega_\theta)$ 的引理 (模块参数 `H₀`、`Hθ`). 它们在 Decouple 里证出, `X₂-label` 的最终陈述也在那里.
>
> 结论先说:
>
> 1. **一级标签 (§1).** `Lab₁ x a` 对符号树 $x$ 的**字面**构造子归纳 (不是模 $\cong$ 的): `zero`/`suc`/`lim`/`up` 照 Correspond 的 `Lab`; `limᵢ` 只收节点层号字面为 `zero` 的 ($\Omega_1$-共尾), 分支对一切**原子** (第 0 层的符号树, 带证书, 计值后带标签) 匹配 `fsT a θ`; 非零层的 `ŝ` (闭包 $\psi_\delta(\Omega_\Omega)$) 的分支对一切**带标签的计值树** $Y$ 在层号 `toLevel Y` 处匹配; 第 0 层的 `ŝ` 与 `ĉᴸ` (待计值链) 对链的**一切证书**逐个输出匹配. 链点的标签不进定义, 只在用到时由调用者提供.
> 2. **`Pre0` (§4): 带前缀的 $\psi_0$.** `Lab₁ x a → x ≅ˢ x → NF₁ (ctx a) → ∀ G → Lab (force (toZ (ψ1 p σ z x)) G) (ctx a)`, 对任意环境层号、任意 `Sim`、任意证书. 规则 6 的两种链 (`limᵢ` 的折叠, 与闭包的计值) 都在这里: 第 $k$ 个链点的标签由第 $k-1$ 个链点的标签经 `Lab₁` 的分支得到 (`liBody`, `ŝLab`), 即 "链上的标签逐点前进", 不需要阶段系统.
> 3. **`Pre1` (§5): 带前缀的 $\psi_1$ 保持 `Lab₁`**, 以 `H₀`/`Hθ` 为参数: 弹栈闭包 $\psi_1(\Omega_\Omega)$ 的第 0 点是 $\psi_1(\Omega_1)$, 在带标签的 $Y$ 的层号处是 $\psi_1(\Omega_{\mathtt{lvl}\,Y})$, 这两棵树是不带前缀的.
> 4. **条件标签 (§6).** 模块 `Pre1M H₀ Hθ` 里 **`X₂-label : Lab X₂ᶠ X₂ᵗ`**: $X_2$ 的链 $c_0=\Omega_1$, $c_{m+1}=\psi^{[\hat\Omega]}_1(c_m)$ 逐个有 `Lab₁` (`LabcX`), 第 $m$ 项由 `Pre0` 标好. 证书用 Stage2Label 的 `GX₂`, 本文不造新证书.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.


```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZDecoupleBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Ctx; Pt; pt; lvP; Γᶜ; Mlev; σ1)
open import OCF.Align.ScafLadderZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; fΩ̂; ψᴾ;
  trˢ; tr⁻ˢ; outs; Goodᶻ; force; force-HS; z2; z1; X₂ˢ; X₂-NF; z<suc)
import OCF.Align.NoCumsum as N
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ)
open import OCF.Align.Symbolic using (X₂ᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (clash; fs-gt)
open import OCF.Align.Closure using (lt→<; fsT₊-pen′)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn)
open import OCF.Align.Stage2 using (ctx; Ωᵗ; Lab-+; Lab-uniq)
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZStage2Label using (chain1; chain1-≅; t₀pop; gpop; pop0-label; outsMap; GX₂; X₂ᶠ)
```


## §1 链证书、原子与一级标签

**链证书.** `CC c t₀ g` 是 Prefix 的 `gc` 的前六个字段 (第 0 点、分支的证书, 支配, 单调); `toC` 把它装成 Symbolic 的 `Ctx`, 与 `force` 内部造的记录逐字段相同, 于是 `force (ĉᴸ …) (gc …)` 的输出就是 `outs (toC K) …`. `lvK K k`/`dxK K k` 是第 $k$ 个链点的层号与支配证据, 即第 $k+1$ 个输出的计值位置.

```agda
record CC (c : Ordᴵ) (t₀ : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z) : Set where
  constructor cc
  field
    G₀ : Goodᶻ t₀
    Gg : ∀ η e → Goodᶻ (g η e)
    d₀ : c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀)
    dE : ∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))
    m₀ : ∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)
    mE : ∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)

toC : ∀ {c t₀ g} → CC c t₀ g → Ctx
toC {c} {t₀} {g} K = record { c = c ; t₀ = force t₀ (CC.G₀ K) ; E = λ η e → force (g η e) (CC.Gg K η e)
                            ; h₀ = force-HS t₀ (CC.G₀ K) ; hE = λ η e → force-HS (g η e) (CC.Gg K η e)
                            ; d₀ = CC.d₀ K ; dE = CC.dE K ; m₀ = CC.m₀ K ; mE = CC.mE K }

lvK : ∀ {c t₀ g} → CC c t₀ g → ℕ → Ordᴵ
lvK K k = lvP (toC K) (Γᶜ (toC K) k)

dxK : ∀ {c t₀ g} (K : CC c t₀ g) k → c ⊑ᴵ lvK K k
dxK K k = Pt.dx (Γᶜ (toC K) k)
```


**原子与 `Lab₁`.** 原子 `Atom x θ` 是第 0 层的符号树 $x$, 自反, 有一个证书, 计值后带标签 $\theta$ (`Lab` 模 $\cong$ 不变, 于是对一切证书都成立, 由 `force-≅`). 原子是 $\Omega_1$ 处被代入的东西: $X_2$ 的规则 6 链点都是带前缀的可数项 (Decouple §1 的搜索: 它们会一直被带进 $\psi_1(\psi_1(\cdots(\cdot)))$ 的参数).

`Lab₁` 的行:

- `lz`/`ls`/`ll`: 同 `Lab`, 但树是字面的 `zero`/`suc`/`lim`, 不经 $\cong$.
- `lu`: 透视 `up`.
- `li`: `limᵢ` 的节点层号字面为 `zero` (记号侧 `cof t ≡ cΩ []`); 分支在一切原子 $x$ 处匹配 $t[\theta]$.
- `lŝ`: 非零层的闭包 `ŝ c t₀ g` ($\psi_\delta(\Omega_\Omega+\cdots)$, 共尾度 $\Omega_1$): 第 0 点匹配 $t[1]$, 分支在一切带标签 $\theta$ 的计值树 $Y$ (标准形, $\theta>1$, 支配 $c\sqsubseteq^\mathsf I$ `toLevel Y`) 的层号处匹配 $t[\theta]$. 闭包只在链点的层号处被计值 (Prefix §4), 所以只需对这种 $Y$.
- `lŝ₀`/`lĉ`: 第 0 层的 `ŝ` 与任意层的 `ĉᴸ` (待计值链, 共尾度 $\omega$), 对链的一切证书 `K`, 第 0 个输出匹配 $t[0]$, 第 $k+1$ 个输出 (在 `lvK K k` 处) 匹配 $t[k+1]$.

链点的标签、下标的标签都**不**是 `Lab₁` 的字段, 而是分支的前提: 这就是本文与 Bachmann 的 `Generic` 的区别, 后者要求一个预先给定的下标系统 (`Slt`/`Seq`), 而这里在用到的那一刻由调用者提供. 字段都是正的 (`Atom` 与 `Lab` 是先定义的).

```agda
Atom : Ordˢ zero → T → Set
Atom x θ = (x ≅ˢ x) × Σ (Goodᶻ (toZ x)) (λ G → Lab (force (toZ x) G) θ)

data Lab₁ : ∀ {k} → Ordˢ k → T → Set where
  lz  : ∀ {k t} → cof t ≡ c0 → Lab₁ {k} Ord₊ˢ.zero t
  ls  : ∀ {k t} {y : Ordˢ k} → cof t ≡ c1 → Lab₁ y (pred t) → Lab₁ (Ord₊ˢ.suc y) t
  ll  : ∀ {k t} {F : ℕ → Ordˢ k} → cof t ≡ cω → (∀ n → Lab₁ (F n) (fsn t n)) → Lab₁ (Ord₊ˢ.lim F) t
  lu  : ∀ {k ℓ t} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → Lab₁ (outˢ (◃₁→◃ r) x) t → Lab₁ (Ord₊ˢ.up r x) t
  li  : ∀ {k t} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} → cof t ≡ cΩ [] →
        (∀ θ (x : Ordˢ zero) → Atom x θ → Lab₁ (f (intoˢ (<→◃ q) x)) (fsT t θ)) → Lab₁ (Ord₊ˢ.limᵢ q f) t
  lŝ  : ∀ {k t c} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → kd k ≡ false → cof t ≡ cΩ [] →
        Lab₁ t₀ (fsT t (natT 1)) →
        (∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
         Lab₁ (g (toLevel Y hY) e) (fsT t θ)) →
        Lab₁ (Ord₊ˢ.ŝ c t₀ g) t
  lŝ₀ : ∀ {t c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} → cof t ≡ cω →
        (∀ (K : CC c (toZ t₀) (λ η e → toZ (g η e))) → Lab₁ t₀ (fsn t 0)) →
        (∀ (K : CC c (toZ t₀) (λ η e → toZ (g η e))) k → Lab₁ (g (lvK K k) (dxK K k)) (fsn t (suc k))) →
        Lab₁ (Ord₊ˢ.ŝ {ℓ = zero} c t₀ g) t
  lĉ  : ∀ {k t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ k} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} → cof t ≡ cω →
        (∀ (K : CC c t₀ g) → Lab₁ o₀ (fsn t 0)) → (∀ (K : CC c t₀ g) k → Lab₁ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
        Lab₁ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t
```


## §2 计值与加法

`faddᶻ` 是 Stage2Label 的 `fadd` 的证书版: 三个证书都作为参数给出 (那里用 `Good` 现造), 因为在 `Pre0` 里只有 `force` 的总证书, 而规则 4 的和 $P\cdot n$ 的各项证书正好是它的分量 (`Gs 1` 字面就是 $P$ 的证书, 因为 `P +ˢ zero` 定义性地是 $P$). 尾巴是 `ŝ`/`ĉᴸ` 时两条链的证书不同, 链点经 Stage2Label 的 `outsMap` 对上. `ŝ-reflg` 是 UniformS 的 `ĉ-reflg` 的 `ŝ` 版.

```agda
ŝ-reflg : ∀ {k k′ c t₀ g} {b : Ordˢ k′} → Ord₊ˢ.ŝ {ℓ = k} c t₀ g ≅ˢ b → ∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′
ŝ-reflg (ŝ≅ _ ec _ eg) η e η′ e′ eη =
  ≅ˢ-trans (eg η e η′ (⊑ᴵ-≅ˡ ec e′) eη) (≅ˢ-sym (eg η′ e′ η′ (⊑ᴵ-≅ˡ ec e′) (≅ᴵ-refl η′)))
ŝ-reflg (upʳ {r = zero} d)   = ŝ-reflg d
ŝ-reflg (upʳ {r = self n} d) = ŝ-reflg d

faddᶻ : ∀ {a b : Ordˢ zero} → a ≅ˢ a → b ≅ˢ b → (G : Goodᶻ (toZ (a +ˢ b))) (Ga : Goodᶻ (toZ a)) (Gb : Goodᶻ (toZ b)) →
        force _ G ≅ force _ Ga + force _ Gb
faddᶻ {b = Ord₊ˢ.zero} ea eb G Ga Goodᶻ.gz = force-≅ (toZ-≅ ea) G Ga
faddᶻ {b = Ord₊ˢ.suc b} ea eb (Goodᶻ.gs G) Ga (Goodᶻ.gs Gb) = s≅ (faddᶻ ea (s-invˢ eb) G Ga Gb)
faddᶻ {b = Ord₊ˢ.lim f} ea eb (Goodᶻ.gl G _) Ga (Goodᶻ.gl Gb _) = l≅ (λ n → faddᶻ ea (l-invˢ eb n) (G n) Ga (Gb n))
faddᶻ {b = Ord₊ˢ.limᵢ () f} ea eb G Ga Gb
faddᶻ {b = Ord₊ˢ.up () x} ea eb G Ga Gb
faddᶻ {a = a} {b = Ord₊ˢ.ŝ c t₀ g} ea eb (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) Ga
      (Goodᶻ.gc G₀′ Gg′ d₀′ dE′ m₀′ mE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outsMap (toC (cc G₀ Gg d₀ dE m₀ mE)) (toC (cc G₀′ Gg′ d₀′ dE′ m₀′ mE′))
              (force-≅ (toZ-≅ et) G₀ G₀′) (λ η e η′ e′ eη → force-≅ (toZ-≅ (eg η e η′ e′ eη)) (Gg η e) (Gg′ η′ e′))
              (λ X → force _ Ga + X) (faddᶻ ea et Go₀ Ga Go₀′)
              (λ η e η′ e′ eη → ≅-trans (faddᶻ ea (eg η e η e (≅ᴵ-refl η)) (Go η e) Ga (Go′ η e))
                                        (add-≅ (≅-refl⁰ _) (force-≅ (toZ-≅ (eg η e η′ e′ eη)) (Go′ η e) (Go′ η′ e′)))))
  where et = ŝ-refl₀ eb
        eg = ŝ-reflg eb
faddᶻ {a = a} {b = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} ea eb (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) Ga
      (Goodᶻ.gc G₀′ Gg′ d₀′ dE′ m₀′ mE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outsMap (toC (cc G₀ Gg d₀ dE m₀ mE)) (toC (cc G₀′ Gg′ d₀′ dE′ m₀′ mE′))
              (force-≅ (≅ᶻ-refl₀ eb) G₀ G₀′) (λ η e η′ e′ eη → force-≅ (≅ᶻ-reflg eb η e η′ e′ eη) (Gg η e) (Gg′ η′ e′))
              (λ X → force _ Ga + X) (faddᶻ ea (ĉ-refl₀ eb) Go₀ Ga Go₀′)
              (λ η e η′ e′ eη → ≅-trans (faddᶻ ea (ĉ-reflg eb η e) (Go η e) Ga (Go′ η e))
                                        (add-≅ (≅-refl⁰ _) (force-≅ (toZ-≅ (ĉ-reflO eb η e η′ e′ eη)) (Go′ η e) (Go′ η′ e′)))))
```


`Lab-repᶻ`: 第 0 层 $\psi^{[\hat\Omega]}_0(y)\cdot n$ 的标签, 由 `faddᶻ` 与 Stage2 的 `Lab-+`.

```agda
lab0ᶻ : (G : Goodᶻ Z.zero) → Lab (force Z.zero G) []
lab0ᶻ Goodᶻ.gz = l0 refl z≅

iterRefl : ∀ {ℓ} {P : Ordˢ ℓ} → P ≅ˢ P → ∀ n → iter (P +ˢ_) Ord₊ˢ.zero n ≅ˢ iter (P +ˢ_) Ord₊ˢ.zero n
iterRefl eP n = iter-R _≅ˢ_ {G = _ +ˢ_} {G′ = _ +ˢ_} (addˢ-≅ refl eP) z≅ n

Lab-repᶻ : ∀ {P : Ordˢ zero} {x} → P ≅ˢ P → (Gs : ∀ n → Goodᶻ (toZ (iter (P +ˢ_) Ord₊ˢ.zero n))) →
           (∀ G → Lab (force (toZ P) G) (x ∷ [])) → ∀ n → Lab (force _ (Gs n)) (replicate n x)
Lab-repᶻ eP Gs lP zero    = lab0ᶻ (Gs 0)
Lab-repᶻ eP Gs lP (suc n) =
  Lab-≅ (faddᶻ eP (iterRefl eP n) (Gs (suc n)) (Gs 1) (Gs n)) (Lab-+ (lP (Gs 1)) (Lab-repᶻ eP Gs lP n))
```


## §3 $\psi_1$ 的派发, 记号侧的小事实

`fold1`/`pen1` 是 Bachmann 的 `fold⁺` 与 Closure 的 `pen⁺` 对单 $\hat\Omega$ 栈的 $\psi^P$ 的版本, 证法逐字 (对 `<ᴵ-dec` 的 `with`, 另两支由 `clash`/`≺ᴵ-irrefl` 排除). 记号侧: `ctx [] ≡ EBOψ 2` (`refl`), $\gamma$-链 `γP a` 是 $\psi_0(\Omega_\Omega+a)$ 的规则 6 链 ($\gamma_0=1$, $\gamma_{k+1}=\psi_0(\Omega_\Omega+a[\gamma_k])$), 链点都 $>1$ (`1<ctx`, `refl`).

```agda
fold1 : ∀ {i k ℓ j} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (i ≺ᴵ j) ⊎ (i ≅ᴵ j) →
        ψ1 p σ z (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψ1 p σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m))))
fold1 {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1 : ∀ {i k ℓ j N} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
       j ≅ᴵ N → N ≺ᴵ i →
       Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
       ψ1 p σ z (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen1 {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))

_ : ctx [] ≡ E.EBOψ 2
_ = refl

ΩΩ : PT
ΩΩ = ψᵗ Ωᵗ []

γP : T → ℕ → T
γP a = γT (ΩΩ ∷ a) []

1<ctx : ∀ a → natT 1 <ᵀ ctx a
1<ctx a = lt→< (natT 1) (ctx a) refl
```


## §4 `Pre0`: 带前缀的 $\psi_0$

`nfγ`/`nfω`: 链点与输出的标准形 (StandardOmega 的 `NF₁-fsn`, 经 Bachmann 的 `fs-gt` 与 Correspond 的 `fs-ω` 改写). `force-subst`: 计值沿 `≡` 搬运.

```agda
force-subst : ∀ {X X′ : Ordˢ zero} (eq : X ≡ X′) (G : Goodᶻ (toZ X)) →
              force (toZ X) G ≡ force (toZ X′) (subst (λ W → Goodᶻ (toZ W)) eq G)
force-subst refl G = refl

nfγ : ∀ {y ys} → NF₁ (ctx (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cΩ []) → ∀ m → NF₁ (ctx (fsT (y ∷ ys) (γP (y ∷ ys) m)))
nfγ {y} {ys} nu c m = subst NF₁ (fs-gt [] ΩΩ (y ∷ ys) [] c refl m) (NF₁-fsn nu (cong (E.cofA []) c) m)

nfω : ∀ {y ys} → NF₁ (ctx (y ∷ ys)) → (c : cof (y ∷ ys) ≡ cω) → ∀ m → NF₁ (ctx (fsn (y ∷ ys) m))
nfω {y} {ys} nu c m = subst NF₁ (fs-ω [] ΩΩ (y ∷ ys) c m) (NF₁-fsn nu (cong (E.cofA []) c) m)
```


**链的三个主体, 以递归调用为参数.** `liBody`: `limᵢ` 折叠时的符号链点 $c_m$ (`chain1`) 是原子, 标签逐个前进: $c_0=\Omega_0=1$; $c_{m+1}=\psi^{[\hat\Omega]}_0(f\,c_m)$ 与第 $m$ 个输出只差目标证明 (`ψ1-≅`), 证书由 `Goodᶻ-tr` 从输出的证书搬来, 标签由**递归调用** `rec` 在 $c_m$ 处给出. `ŝLab`/`ŝOut`: 闭包被计值时, 第 $m$ 个链点 (计值树) 的标签由 `rec` 在第 $m-1$ 个链点的层号处给出. `pOut`: 待计值链只是把输出逐个改写.

**否定 (编译报错).** 最初把这些主体写成与 `Pre0` 互递归的顶层函数 (`Pre0-li`/`atomC`/`ptLab`/`outS`/`outS₀`/`outC`, 各自对 `Lab₁` 推导做模式匹配, 再调用 `Pre0`), 报

    [TerminationIssue]
    Termination checking failed for the following functions:
      Pre0, Pre0-li, atomC, outS₀
    Problematic calls:
      Pre0 l (s-invˢ ex) (subst NF₁ (fs-rep [] ΩΩ (y ∷ ys) c 1) (NF₁-fsn nu (cong (E.cofA []) c) 1))
      …
      Pre0 (hk K m) (ŝ-reflg ex (lvK K m) (dxK K m) (lvK K m) (dxK K m) (≅ᴵ-refl (lvK K m))) (nfω nu c (suc m)) (Go (lvK K m) (dxK K m))

二分 (临时文件 `T2`/`T3`): 只有 `li` 那一组或只有 `lŝ₀` 那一组都通过, 两组同在才失败. 改成下面的写法即过: 主体不递归, 递归调用作为 λ 参数 (`rec`) 由 `Pre0` 的子句当场给出, 于是 `Pre0` 的每个递归调用都直接作用在自己的子句的模式子项 (`h θ x at`、`hg …`、`h₀ K`、`hk K m`) 上.

```agda
liBody : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
         cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (ctx (y ∷ ys)) →
         (rec : ∀ θ (x : Ordˢ zero) → Atom x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) → NF₁ (ctx (fsT (y ∷ ys) θ)) →
                ∀ G → Lab (force (toZ (ψ1 p σ z (f (intoˢ (<→◃ q) x)))) G) (ctx (fsT (y ∷ ys) θ))) →
         (Gs : ∀ m → Goodᶻ (toZ (ψ1 p σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m)))))) →
         ∀ m → Atom (chain1 σ z q f m) (γP (y ∷ ys) m)
liBody c ex nu rec Gs zero = Ωˢ-refl zero , Goodᶻ.gs Goodᶻ.gz , l1 refl (s≅ z≅) (l0 refl z≅)
liBody {p = p} {σ = σ} {z = z} {q = q} {f = f} c ex nu rec Gs (suc m) =
  ψ1-≅ {p = σ q} {σ = σ} {p′ = σ q} {σ′ = σ} {z = z} {z′ = z} z≅ br ,
  Goodᶻ-tr (toZ-≅ e′) (Gs m) ,
  Lab-≅ (force-≅ (toZ-≅ (≅ˢ-sym e′)) _ (Gs m)) (rec _ _ am br (nfγ nu c m) (Gs m))
  where
  am = liBody c ex nu rec Gs m
  br = i-respˢ ex (proj₁ am)
  e′ : ψ1 p σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m))) ≅ˢ ψ1 (σ q) σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m)))
  e′ = ψ1-≅ {p = p} {σ = σ} {p′ = σ q} {σ′ = σ} {z = z} {z′ = z} z≅ br

liLab : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {q : zero <ᴵ k} {f : Uˢ zero (<→◃ q) → Ordˢ k} {y ys} →
        cof (y ∷ ys) ≡ cΩ [] → Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → NF₁ (ctx (y ∷ ys)) →
        (rec : ∀ θ (x : Ordˢ zero) → Atom x θ → f (intoˢ (<→◃ q) x) ≅ˢ f (intoˢ (<→◃ q) x) → NF₁ (ctx (fsT (y ∷ ys) θ)) →
               ∀ G → Lab (force (toZ (ψ1 p σ z (f (intoˢ (<→◃ q) x)))) G) (ctx (fsT (y ∷ ys) θ))) →
        ∀ G → Lab (force (toZ (ψ1 p σ z (Ord₊ˢ.limᵢ q f))) G) (ctx (y ∷ ys))
liLab {p = p} {σ = σ} {z = z} {q = q} {f = f} {y = y} {ys = ys} c ex nu rec G =
  subst (λ W → Lab W (ctx (y ∷ ys))) (sym (force-subst eqf G)) (go (subst (λ W → Goodᶻ (toZ W)) eqf G))
  where
  eqf = fold1 {p = p} {σ = σ} {z = z} {q = q} {f = f} (inj₂ z≅)
  go : ∀ G′ → Lab (force (toZ (Ord₊ˢ.lim (λ m → ψ1 p σ z (f (intoˢ (<→◃ q) (chain1 σ z q f m)))))) G′) (ctx (y ∷ ys))
  go (Goodᶻ.gl Gs st) = lω (cong (E.cofA []) c) (l≅ (λ m → ≅-refl⁰ _))
    (λ m → subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) [] c refl m))
             (rec _ _ (liBody c ex nu rec Gs m) (i-respˢ ex (proj₁ (liBody c ex nu rec Gs m))) (nfγ nu c m) (Gs m)))

ŝLab : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} {y ys} →
       cof (y ∷ ys) ≡ cΩ [] → NF₁ (ctx (y ∷ ys)) →
       (rec₀ : ∀ G → Lab (force (toZ (ψ1 p σ z t₀)) G) (ctx (fsT (y ∷ ys) (natT 1)))) →
       (rec : ∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
              NF₁ (ctx (fsT (y ∷ ys) θ)) → ∀ G → Lab (force (toZ (ψ1 p σ z (g (toLevel Y hY) e))) G) (ctx (fsT (y ∷ ys) θ))) →
       (K : CC c (toZ (ψ1 p σ z t₀)) (λ η e → toZ (ψ1 p σ z (g η e)))) →
       ∀ m → Lab (Pt.x (Γᶜ (toC K) m)) (γP (y ∷ ys) (suc m))
ŝLab c nu rec₀ rec K zero    = rec₀ (CC.G₀ K)
ŝLab c nu rec₀ rec K (suc m) =
  rec _ (Pt.x (Γᶜ (toC K) m)) (Pt.hx (Γᶜ (toC K) m)) (ŝLab c nu rec₀ rec K m) (nfγ nu c m) (1<ctx _) (Pt.dx (Γᶜ (toC K) m))
      (nfγ nu c (suc m)) (CC.Gg K _ _)

ŝOut : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} {y ys} →
       cof (y ∷ ys) ≡ cΩ [] → NF₁ (ctx (y ∷ ys)) →
       (rec₀ : ∀ G → Lab (force (toZ (ψ1 p σ z t₀)) G) (ctx (fsT (y ∷ ys) (natT 1)))) →
       (rec : ∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
              NF₁ (ctx (fsT (y ∷ ys) θ)) → ∀ G → Lab (force (toZ (ψ1 p σ z (g (toLevel Y hY) e))) G) (ctx (fsT (y ∷ ys) θ))) →
       (K : CC c (toZ (ψ1 p σ z t₀)) (λ η e → toZ (ψ1 p σ z (g η e)))) →
       (Go₀ : Goodᶻ (toZ (ψ1 p σ z t₀))) (Go : ∀ η e → Goodᶻ (toZ (ψ1 p σ z (g η e)))) →
       ∀ n → Lab (outs (toC K) (force _ Go₀) (λ η e → force _ (Go η e)) n) (fsn (ctx (y ∷ ys)) n)
ŝOut {y = y} {ys = ys} c nu rec₀ rec K Go₀ Go zero = subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) [] c refl 0)) (rec₀ Go₀)
ŝOut {y = y} {ys = ys} c nu rec₀ rec K Go₀ Go (suc m) =
  subst (Lab _) (sym (fs-gt [] ΩΩ (y ∷ ys) [] c refl (suc m)))
    (rec _ (Pt.x (Γᶜ (toC K) m)) (Pt.hx (Γᶜ (toC K) m)) (ŝLab c nu rec₀ rec K m) (nfγ nu c m) (1<ctx _) (Pt.dx (Γᶜ (toC K) m))
         (nfγ nu c (suc m)) (Go _ _))

pOut : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Z} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z}
         {o₀ : Ordˢ k} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} {y ys} → cof (y ∷ ys) ≡ cω →
       (K : CC c t₀ g) →
       (Go₀ : Goodᶻ (toZ (ψ1 p σ z o₀))) (Go : ∀ η e → Goodᶻ (toZ (ψ1 p σ z (o η e)))) →
       Lab (force _ Go₀) (ctx (fsn (y ∷ ys) 0)) → (∀ m → Lab (force _ (Go (lvK K m) (dxK K m))) (ctx (fsn (y ∷ ys) (suc m)))) →
       ∀ n → Lab (outs (toC K) (force _ Go₀) (λ η e → force _ (Go η e)) n) (fsn (ctx (y ∷ ys)) n)
pOut {y = y} {ys = ys} c K Go₀ Go l₀ lk zero    = subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c 0)) l₀
pOut {y = y} {ys = ys} c K Go₀ Go l₀ lk (suc m) = subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c (suc m))) (lk m)
```


**定理 `Pre0`.** 对 `Lab₁` 推导递归:

- `lz`: 尾巴 0, 弹栈闭包, Stage2Label 的 `pop0-label` (任意环境层号).
- `ls`: 规则 4, `Lab-repᶻ` 与递归.
- `ll`/`lu`: 逐项, 透视 `up` (换 `Sim`, 要显式写出隐式参数).
- `li`: `fold1` (目标层与节点层都是 0, 故 `inj₂ z≅`), 链由 `liLab`.
- `lŝ` (非零层闭包, 按层号分 `suc`/`lim` 让 `ψᴾ` 计算): 输出是第 0 层的 `ŝ`, `toZ` 后是以自己为输出的链, 证书 `gc` 的前六个字段就是链证书 `K`; 链由 `ŝOut`.
- `lŝ₀`/`lĉ`: 待计值链, 输出逐个递归.

```agda
Pre0 : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {x : Ordˢ k} {a} →
       Lab₁ x a → x ≅ˢ x → NF₁ (ctx a) → (G : Goodᶻ (toZ (ψ1 p σ z x))) → Lab (force _ G) (ctx a)
Pre0 {a = []} (lz c) ex nu G = pop0-label _ _ _ G
Pre0 {a = y ∷ ys} (lz c) ex nu G = ⊥-elim (cof-ne y ys c)
Pre0 {a = []} (ls () l) ex nu G
Pre0 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (ls c l) ex nu (Goodᶻ.gl Gs st) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (λ n → subst (Lab _) (sym (fs-rep [] ΩΩ (y ∷ ys) c n))
                  (Lab-repᶻ (ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} z≅ (s-invˢ ex)) Gs
                            (λ G → Pre0 {p = p} {σ = σ} {z = z} l (s-invˢ ex)
                                        (subst NF₁ (fs-rep [] ΩΩ (y ∷ ys) c 1) (NF₁-fsn nu (cong (E.cofA []) c) 1)) G) n))
Pre0 {a = []} (ll () h) ex nu G
Pre0 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (ll c h) ex nu (Goodᶻ.gl Gs st) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (λ n → subst (Lab _) (sym (fs-ω [] ΩΩ (y ∷ ys) c n))
                  (Pre0 {p = p} {σ = σ} {z = z} (h n) (l-invˢ ex n) (nfω nu c n) (Gs n)))
Pre0 {p = p} {σ = σ} {z = z} (lu {r = zero} l) ex nu G =
  Pre0 {p = p} {σ = λ q → σ (suc q)} {z = z} l (u-reflˢ zero ex) nu G
Pre0 {p = p} {σ = σ} {z = z} (lu {r = self n} l) ex nu G =
  Pre0 {p = p} {σ = λ q → σ (lim n q)} {z = z} l (u-reflˢ (self n) ex) nu G
Pre0 {a = []} (li () h) ex nu G
Pre0 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (li c h) ex nu G =
  liLab {p = p} {σ = σ} {z = z} c ex nu (λ θ x at br nf G′ → Pre0 {p = p} {σ = σ} {z = z} (h θ x at) br nf G′) G
Pre0 {k = zero} (lŝ () c h₀ hg) ex nu G
Pre0 {k = suc _} {a = []} (lŝ kk () h₀ hg) ex nu G
Pre0 {k = suc _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lŝ kk c h₀ hg) ex nu (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (ŝOut {p = p} {σ = σ} {z = z} c nu (λ G′ → Pre0 {p = p} {σ = σ} {z = z} h₀ (ŝ-refl₀ ex) (nfγ nu c 0) G′)
           (λ θ Y hY lY nθ lt e nf G′ → Pre0 {p = p} {σ = σ} {z = z} (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) nf G′)
           (cc G₀ Gg d₀ dE m₀ mE) Go₀ Go)
Pre0 {k = lim _ _} {a = []} (lŝ kk () h₀ hg) ex nu G
Pre0 {k = lim _ _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lŝ kk c h₀ hg) ex nu (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (ŝOut {p = p} {σ = σ} {z = z} c nu (λ G′ → Pre0 {p = p} {σ = σ} {z = z} h₀ (ŝ-refl₀ ex) (nfγ nu c 0) G′)
           (λ θ Y hY lY nθ lt e nf G′ → Pre0 {p = p} {σ = σ} {z = z} (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) nf G′)
           (cc G₀ Gg d₀ dE m₀ mE) Go₀ Go)
Pre0 {a = []} (lŝ₀ () h₀ hk) ex nu G
Pre0 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lŝ₀ c h₀ hk) ex nu (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (pOut {p = p} {σ = σ} {z = z} c K Go₀ Go
           (Pre0 {p = p} {σ = σ} {z = z} (h₀ K) (ŝ-refl₀ ex) (nfω nu c 0) Go₀)
           (λ m → Pre0 {p = p} {σ = σ} {z = z} (hk K m) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)) (nfω nu c (suc m)) (Go _ _)))
  where K = cc G₀ Gg d₀ dE m₀ mE
Pre0 {a = []} (lĉ () h₀ hk) ex nu G
Pre0 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lĉ c h₀ hk) ex nu (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lω (cong (E.cofA []) c) (l≅ (λ n → ≅-refl⁰ _))
     (pOut {p = p} {σ = σ} {z = z} c K Go₀ Go
           (Pre0 {p = p} {σ = σ} {z = z} (h₀ K) (ĉ-refl₀ ex) (nfω nu c 0) Go₀)
           (λ m → Pre0 {p = p} {σ = σ} {z = z} (hk K m) (ĉ-reflO ex _ _ _ _ (≅ᴵ-refl _)) (nfω nu c (suc m)) (Go _ _)))
  where K = cc G₀ Gg d₀ dE m₀ mE
```


**读法.** 证书完全来自调用者 (`G`); `Pre0` 只读计值树的形状. 链上的递归是 "第 $k$ 点的标签 $\Rightarrow$ 第 $k+1$ 点的标签", 每一步只用到 `Lab₁` 推导的一个分支, 推导本身是有限高度的归纳对象 (分支无穷), 所以整条链、以及链点里面嵌套的链, 都在同一个结构递归里. Stage2Label §9 预言的 "沿 $A$ 的链做 Label 的阶段式归纳" 就是这个.

## §5 一级的和、原子的标签、带前缀的 $\psi_1$

`Lab₁-sum`/`Lab₁-rep`: 加法只动尾巴, 对尾巴的 `Lab₁` 归纳; 结果在被加数的层上, 闭包行要它非零 (`kd ℓ ≡ false`, 层号 $\le1$ 的用法里总是 `one`).

```agda
Lab₁-sum : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → Lab₁ a (x ∷ []) → Lab₁ b ys →
           Lab₁ (addˢ a σ b) (x ∷ ys)
Lab₁-sum {ys = []} kl la (lz c) = la
Lab₁-sum {ys = y ∷ ys} kl la (lz c) = ⊥-elim (cof-ne y ys c)
Lab₁-sum {ys = []} kl la (ls () l)
Lab₁-sum {ys = y ∷ ys} kl la (ls c l) = ls c (Lab₁-sum kl la l)
Lab₁-sum {ys = []} kl la (ll () h)
Lab₁-sum {ys = y ∷ ys} kl la (ll c h) = ll c (λ n → Lab₁-sum kl la (h n))
Lab₁-sum {σ = σ} kl la (lu {r = zero} l) = Lab₁-sum {σ = λ q → σ (suc q)} kl la l
Lab₁-sum {σ = σ} kl la (lu {r = self n} l) = Lab₁-sum {σ = λ q → σ (lim n q)} kl la l
Lab₁-sum {ys = []} kl la (li () h)
Lab₁-sum {a = a} {σ = σ} {x = x} {ys = y ∷ ys} kl la (li {q = q} {f = f} c h) =
  li c (λ θ w at → subst (λ v → Lab₁ (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) θ))
                         (sym (out-intoˢ (<→◃ (σ q)) w)) (Lab₁-sum kl la (h θ w at)))
Lab₁-sum {k = zero} kl la (lŝ () c h₀ hg)
Lab₁-sum {k = suc _} {ys = []} kl la (lŝ kk () h₀ hg)
Lab₁-sum {k = suc _} {ys = y ∷ ys} kl la (lŝ kk c h₀ hg) =
  lŝ kl c (Lab₁-sum kl la h₀) (λ θ Y hY lY nθ lt e → Lab₁-sum kl la (hg θ Y hY lY nθ lt e))
Lab₁-sum {k = lim _ _} {ys = []} kl la (lŝ kk () h₀ hg)
Lab₁-sum {k = lim _ _} {ys = y ∷ ys} kl la (lŝ kk c h₀ hg) =
  lŝ kl c (Lab₁-sum kl la h₀) (λ θ Y hY lY nθ lt e → Lab₁-sum kl la (hg θ Y hY lY nθ lt e))
Lab₁-sum {ys = []} kl la (lŝ₀ () h₀ hk)
Lab₁-sum {ys = y ∷ ys} kl la (lŝ₀ c h₀ hk) = lĉ c (λ K → Lab₁-sum kl la (h₀ K)) (λ K m → Lab₁-sum kl la (hk K m))
Lab₁-sum {ys = []} kl la (lĉ () h₀ hk)
Lab₁-sum {ys = y ∷ ys} kl la (lĉ c h₀ hk) = lĉ c (λ K → Lab₁-sum kl la (h₀ K)) (λ K m → Lab₁-sum kl la (hk K m))

Lab₁-rep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → kd ℓ ≡ false → Lab₁ P (x ∷ []) → ∀ n → Lab₁ (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
Lab₁-rep kl lP zero    = lz refl
Lab₁-rep kl lP (suc n) = Lab₁-sum kl lP (Lab₁-rep kl lP n)
```


`atomL`: 原子都有 `Lab₁` (对原子的树递归; `ŝ`/`ĉᴸ` 情形里, `Lab₁` 量化的链证书 `K` 与原子自带的证书不同, 两条链的链点经 UniformS 的 `chain≅` 与 `toLevel-≅` 对上, 分支在 $\cong^\mathsf I$ 的层号处 $\cong$). `Atom-tr⁻`: 原子沿 `tr⁻ˢ z≅` 搬运 (穿透时分支的输入要搬).

```agda
Atom-tr⁻ : ∀ {x : Ordˢ zero} {θ} → Atom x θ → Atom (tr⁻ˢ z≅ x) θ
Atom-tr⁻ (ex , G , l) = ≅ˢ-reflˡ d , Goodᶻ-tr (toZ-≅ (≅ˢ-sym d)) G , Lab-≅ (force-≅ (toZ-≅ d) _ G) l
  where d = tr⁻ˢ-≅ z≅ ex

atomL : ∀ {x : Ordˢ zero} {θ} → Atom x θ → Lab₁ x θ
atomL {x = Ord₊ˢ.zero} (ex , Goodᶻ.gz , l0 c e) = lz c
atomL {x = Ord₊ˢ.zero} (ex , Goodᶻ.gz , l1 c () l)
atomL {x = Ord₊ˢ.zero} (ex , Goodᶻ.gz , lω c () h)
atomL {x = Ord₊ˢ.suc x} (ex , Goodᶻ.gs G , l0 c ())
atomL {x = Ord₊ˢ.suc x} (ex , Goodᶻ.gs G , l1 c (s≅ e) l) = ls c (atomL (s-invˢ ex , G , Lab-≅ e l))
atomL {x = Ord₊ˢ.suc x} (ex , Goodᶻ.gs G , lω c () h)
atomL {x = Ord₊ˢ.lim f} (ex , Goodᶻ.gl G st , l0 c ())
atomL {x = Ord₊ˢ.lim f} (ex , Goodᶻ.gl G st , l1 c () l)
atomL {x = Ord₊ˢ.lim f} (ex , Goodᶻ.gl G st , lω c (l≅ k) h) = ll c (λ n → atomL (l-invˢ ex n , G n , Lab-≅ (k n) (h n)))
atomL {x = Ord₊ˢ.limᵢ () f} at
atomL {x = Ord₊ˢ.up () x} at
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo , l0 cc′ ())
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo , l1 cc′ () l)
atomL {x = Ord₊ˢ.ŝ c t₀ g} (ex , Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo , lω cw (l≅ k) h) =
  lŝ₀ cw (λ K → atomL (ŝ-refl₀ ex , Go₀ , Lab-≅ (k 0) (h 0)))
         (λ K m → atomL (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _) , CC.Gg K _ _ ,
                         Lab-≅ (force-≅ (toZ-≅ (ŝ-reflg ex _ _ _ _ (lv≅ K m))) (CC.Gg K _ _) (Go _ _))
                               (Lab-≅ (k (suc m)) (h (suc m)))))
  where
  C = toC (cc G₀ Gg d₀ dE m₀ mE)
  lv≅ : ∀ (K : CC c (toZ t₀) (λ η e → toZ (g η e))) m → lvK K m ≅ᴵ lvP C (Γᶜ C m)
  lv≅ K m = toLevel-≅ (Pt.hx (Γᶜ (toC K) m)) (Pt.hx (Γᶜ C m))
              (chain≅ (toC K) C (force-≅ (toZ-≅ (ŝ-refl₀ ex)) _ _)
                      (λ η e η′ e′ eη → force-≅ (toZ-≅ (ŝ-reflg ex η e η′ e′ eη)) _ _) m)
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo , l0 cc′ ())
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo , l1 cc′ () l)
atomL {x = Ord₊ˢ.ĉᴸ c t₀ g o₀ o} (ex , Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo , lω cw (l≅ k) h) =
  lĉ cw (λ K → atomL (ĉ-refl₀ ex , Go₀ , Lab-≅ (k 0) (h 0)))
        (λ K m → atomL (ĉ-reflO ex _ _ _ _ (≅ᴵ-refl _) , Go _ _ ,
                        Lab-≅ (force-≅ (toZ-≅ (ĉ-reflO ex _ _ _ _ (lv≅ K m))) (Go _ _) (Go _ _))
                              (Lab-≅ (k (suc m)) (h (suc m)))))
  where
  C = toC (cc G₀ Gg d₀ dE m₀ mE)
  lv≅ : ∀ (K : CC c t₀ g) m → lvK K m ≅ᴵ lvP C (Γᶜ C m)
  lv≅ K m = toLevel-≅ (Pt.hx (Γᶜ (toC K) m)) (Pt.hx (Γᶜ C m))
              (chain≅ (toC K) C (force-≅ (≅ᶻ-refl₀ ex) _ _)
                      (λ η e η′ e′ eη → force-≅ (≅ᶻ-reflg ex η e η′ e′ eη) _ _) m)
```


**带前缀的 $\psi_1$.** `ctx1 a` $=\psi_1(\Omega_\Omega+a)$, `ψ₁Ω θ` $=\psi_1(\Omega_\theta)$; $\psi_1(\Omega_\Omega)[\theta]=\psi_1(\Omega_\theta)$ 是 `refl`. `penT`: 尾巴 $\Omega_1$-共尾时 $\psi_1(\Omega_\Omega+a)$ 穿透 (比较 $1$ 与 $1$ 得 `eq`, Closure 的 `fsT₊-pen′`).

```agda
one : Ordᴵ
one = suc zero

ctx1 : T → T
ctx1 a = ψᵗ (natT 1) (ΩΩ ∷ a) ∷ []

ψ₁Ω : T → T
ψ₁Ω θ = ψᵗ (natT 1) (Ωt θ) ∷ []

_ : ∀ θ → fsT (ctx1 []) θ ≡ ψ₁Ω θ
_ = λ θ → refl

penT : ∀ {y ys} → cof (y ∷ ys) ≡ cΩ [] → ∀ θ → fsT (ctx1 (y ∷ ys)) θ ≡ ctx1 (fsT (y ∷ ys) θ)
penT {y} {ys} c θ = fsT₊-pen′ (natT 1) (ΩΩ ∷ y ∷ ys) [] (cof (y ∷ ys)) c (inj₂ refl) θ
```


**`Pre1`, 以两条不带前缀的引理为参数.** `H₀`: $\psi_1(\Omega_1)$ 的树 (弹栈闭包的第 0 点, 环境层号与 `Sim` 任意) 有 `Lab₁`; `Hθ`: 对带标签的计值树 $Y$ ($\theta$ 标准形, $\theta>1$), $\psi_1(\Omega_{\mathtt{toLevel}\,Y})$ 有 `ψ₁Ω θ` 的 `Lab₁`. 对 `Lab₁` 推导递归: `lz` 是弹栈闭包, 字面就是 `ŝ two (t₀pop p z) (gpop p z)` (Stage2Label §4), 两个字段正是 `H₀`、`Hθ`; `li` 由 `pen1` 穿透 (节点 0 对目标 1, 证据 `via z≅ zero`; 对 `pen1` 的结果 `with` 后 `z≅` 迫使新节点层号字面为 `zero`, 而 `zero <ᴵ suc zero` 的证明只有 `zero`), 分支的原子经 `Atom-tr⁻`; 闭包与待计值链逐点.

```agda
module Pre1M
  (H₀ : ∀ {ℓ} (p : one <ᴵ ℓ) (σ : Simᴵ one ℓ) → Lab₁ (ψ0 p σ (Ωˢ one)) (ψ₁Ω (natT 1)))
  (Hθ : ∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ →
        ∀ {ℓ} (p : one <ᴵ ℓ) (σ : Simᴵ (toLevel Y hY) ℓ) → Lab₁ (ψ0 p σ (Ωˢ (toLevel Y hY))) (ψ₁Ω θ))
  where

  Pre1 : ∀ {L k} {p : one <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {y : Ordˢ k} {a} → Lab₁ y a → Lab₁ (ψ1 p σ z y) (ctx1 a)
  Pre1 {p = p} {z = z} {a = []} (lz c) =
    lŝ refl refl (H₀ zero (σ1 (z<suc z p))) (λ θ Y hY lY nθ lt e → Hθ θ Y hY lY nθ lt (lim 0 zero) (λ q → lim 1 q))
  Pre1 {a = y ∷ ys} (lz c) = ⊥-elim (cof-ne y ys c)
  Pre1 {a = []} (ls () l)
  Pre1 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (ls c l) =
    ll (cong (E.cofA (natT 1)) c)
       (λ n → subst (Lab₁ _) (sym (fs-rep (natT 1) ΩΩ (y ∷ ys) c n)) (Lab₁-rep refl (Pre1 {p = p} {σ = σ} {z = z} l) n))
  Pre1 {a = []} (ll () h)
  Pre1 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (ll c h) =
    ll (cong (E.cofA (natT 1)) c) (λ n → subst (Lab₁ _) (sym (fs-ω (natT 1) ΩΩ (y ∷ ys) c n)) (Pre1 {p = p} {σ = σ} {z = z} (h n)))
  Pre1 {p = p} {σ = σ} {z = z} (lu {r = zero} l) = Pre1 {p = p} {σ = λ q → σ (suc q)} {z = z} l
  Pre1 {p = p} {σ = σ} {z = z} (lu {r = self n} l) = Pre1 {p = p} {σ = λ q → σ (lim n q)} {z = z} l
  Pre1 {a = []} (li () h)
  Pre1 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (li {q = q} {f = f} c h)
    with pen1 {p = p} {σ = σ} {z = z} {q = q} {f = f} z≅ (via z≅ zero)
  ... | .zero , z≅ , zero , eqn =
    subst (λ W → Lab₁ W (ctx1 (y ∷ ys))) (sym eqn)
          (li (cong (E.cofA (natT 1)) c)
              (λ θ x at → subst (Lab₁ _) (sym (penT c θ)) (Pre1 {p = p} {σ = σ} {z = z} (h θ (tr⁻ˢ z≅ x) (Atom-tr⁻ at)))))
  ... | .zero , z≅ , suc () , eqn
  Pre1 {k = zero} (lŝ () c h₀ hg)
  Pre1 {k = suc _} {a = []} (lŝ kk () h₀ hg)
  Pre1 {k = suc _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lŝ kk c h₀ hg) =
    lŝ refl (cong (E.cofA (natT 1)) c) (subst (Lab₁ _) (sym (penT c (natT 1))) (Pre1 {p = p} {σ = σ} {z = z} h₀))
       (λ θ Y hY lY nθ lt e → subst (Lab₁ _) (sym (penT c θ)) (Pre1 {p = p} {σ = σ} {z = z} (hg θ Y hY lY nθ lt e)))
  Pre1 {k = lim _ _} {a = []} (lŝ kk () h₀ hg)
  Pre1 {k = lim _ _} {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lŝ kk c h₀ hg) =
    lŝ refl (cong (E.cofA (natT 1)) c) (subst (Lab₁ _) (sym (penT c (natT 1))) (Pre1 {p = p} {σ = σ} {z = z} h₀))
       (λ θ Y hY lY nθ lt e → subst (Lab₁ _) (sym (penT c θ)) (Pre1 {p = p} {σ = σ} {z = z} (hg θ Y hY lY nθ lt e)))
  Pre1 {a = []} (lŝ₀ () h₀ hk)
  Pre1 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lŝ₀ c h₀ hk) =
    lĉ (cong (E.cofA (natT 1)) c)
       (λ K → subst (Lab₁ _) (sym (fs-ω (natT 1) ΩΩ (y ∷ ys) c 0)) (Pre1 {p = p} {σ = σ} {z = z} (h₀ K)))
       (λ K m → subst (Lab₁ _) (sym (fs-ω (natT 1) ΩΩ (y ∷ ys) c (suc m))) (Pre1 {p = p} {σ = σ} {z = z} (hk K m)))
  Pre1 {a = []} (lĉ () h₀ hk)
  Pre1 {p = p} {σ = σ} {z = z} {a = y ∷ ys} (lĉ c h₀ hk) =
    lĉ (cong (E.cofA (natT 1)) c)
       (λ K → subst (Lab₁ _) (sym (fs-ω (natT 1) ΩΩ (y ∷ ys) c 0)) (Pre1 {p = p} {σ = σ} {z = z} (h₀ K)))
       (λ K m → subst (Lab₁ _) (sym (fs-ω (natT 1) ΩΩ (y ∷ ys) c (suc m))) (Pre1 {p = p} {σ = σ} {z = z} (hk K m)))
```


## §6 $X_2$ 的链与条件标签

$X_2=\psi^{[\hat\Omega]}_0(\Omega_2)$ (Prefix 的 `X₂ˢ`): $\Omega_2$ 在第 2 层, 节点层号 1, 目标 0, `fold1` 给出链 `cX`: $c_0=\Omega_1$, $c_{m+1}=\psi^{[\hat\Omega]}_1(c_m)$, 第 $m$ 项是 $\psi^{[\hat\Omega]}_0(c_m)$. 记号侧 $X_2[m]=\psi_0(\Omega_\Omega+\gamma_m)$, $\gamma_0=\Omega_1$, $\gamma_{m+1}=\psi_1(\Omega_\Omega+\gamma_m)$ (`fsX₂`, `γX`; `refl` 的展开). `LabcX`: $\Omega_1$ 的 `Lab₁` 是 `li` 加 `atomL`, 其后每项由 `Pre1`. 第 $m$ 项由 `Pre0`, 标准形来自 Prefix 的 `X₂-NF`.

```agda
  cX : ℕ → Ordˢ one
  cX = chain1 {k = two} (λ q → q) z2 zero (Ord₊ˢ.up zero)

  γX : ℕ → T
  γX = γT (ΩΩ ∷ Ωt (natT 2)) (natT 1)

  LabcX : ∀ m → Lab₁ (cX m) (γX m)
  LabcX zero    = li refl (λ θ x at → lu (atomL at))
  LabcX (suc m) = Pre1 {k = two} {p = zero} {σ = λ q → q} {z = z2} {y = Ord₊ˢ.up zero (cX m)} (lu {r = zero} (LabcX m))

  eqX : X₂ˢ ≡ Ord₊ˢ.lim (λ m → ψ1 z2 (λ q → q) z2 (Ord₊ˢ.up zero (cX m)))
  eqX = fold1 {p = z2} {σ = λ q → q} {z = z2} {q = zero} {f = Ord₊ˢ.up zero} (inj₁ (via z≅ zero))

  fsX₂ : ∀ m → fsn X₂ᵗ m ≡ ctx (γX m)
  fsX₂ m = fs-gt [] ΩΩ (Ωt (natT 2) ) (natT 1) refl refl m

  X₂-label : Lab X₂ᶠ X₂ᵗ
  X₂-label = subst (λ W → Lab W X₂ᵗ) (sym (force-subst eqX GX₂)) (go (subst (λ W → Goodᶻ (toZ W)) eqX GX₂))
    where
    go : ∀ G′ → Lab (force (toZ (Ord₊ˢ.lim (λ m → ψ1 z2 (λ q → q) z2 (Ord₊ˢ.up zero (cX m))))) G′) X₂ᵗ
    go (Goodᶻ.gl Gs st) = lω refl (l≅ (λ m → ≅-refl⁰ _))
      (λ m → subst (Lab _) (sym (fsX₂ m))
               (Pre0 {p = z2} {σ = λ q → q} {z = z2} (lu (LabcX m))
                     (upˡ (upʳ (chain1-≅ (Ωˢ-refl two) m))) (subst NF₁ (fsX₂ m) (NF₁-fsn X₂-NF refl m)) (Gs m)))
```


**读法.** 这里的 `X₂-label` 是**条件**定理: 在 `Pre1M H₀ Hθ` 里. 证书一侧只用了 `GX₂` (Stage2Label 的 `Good-ψ1`, 环境层号 2), 计值树 `X₂ᶠ` 与 Stage2Label 的完全相同. 剩下的两条假设只关于**不带前缀**的 $\psi_1$, 其中会出现阶段 2 的项作 $\Omega$-下标 ($A[1]=\psi_0(\Omega_\Omega+\psi_1(\Omega_{\eta_1}))$ 就是 `Hθ` 在 $\theta=\eta_1$ 的实例), 所以要一个对任意带标签下标都成立的不带前缀的形状理论. 它在 [Decouple](Decouple.lagda.md) 里.

## §7 小结

| | Stage2Label (§9 的计划) | 本文 |
|---|---|---|
| 带前缀主项 $\psi_0(\Omega_\Omega+a)$ 的形状 | 要 "带前缀的 `Generic`" | `Pre0`: 对尾巴的一级标签递归, 不需要翻译、公共上界或下标系统 |
| 沿 $A$ 的链的阶段归纳 | Label 的 `St k` 的阶段 2 版本 | 链点标签逐点前进 (`liBody`/`ŝLab`), 在同一个结构递归里 |
| 原子 (带前缀的可数项进 $\Omega_1$ 位置) | 未提 | `Atom`, `atomL` |
| $\psi_1(\Omega_\Omega+\cdot)$ | 未处理 | `Pre1` (参数 `H₀`/`Hθ`) |
| $X_2$ 的标签 | 第 0 项 (`X₂-0`) | `Pre1M.X₂-label` (条件), 无条件版在 Decouple |

**字面成立:** `ctx [] ≡ EBOψ 2`, `fsT (ctx1 []) θ ≡ ψ₁Ω θ`, `1<ctx` 的比较, `X₂ˢ` 的折叠方程 `eqX` (由 `fold1`, 证明是 `refl` 的 `with` 展开).
**模 $\cong$ 成立:** `faddᶻ`; 一切 `Lab` 结论 (`Lab` 的行本身模 $\cong$).
