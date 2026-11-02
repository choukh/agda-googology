# $\psi_0(\Omega_{\Omega+1})$ 阶段 (一): $\Omega_{\Omega+1}$ 的符号替身、深度塔与 $\Omega$ 层的极限行

> 接 [Uniform2](Uniform2.lagda.md) (统一形态是定义, 九个标签在其上重证) 与 [TopDown](TopDown.lagda.md) §9 (对角线 `TOᵀ` 已编译). 本文是 EBO 第二个不可数下标阶段的前半: $\Omega_{\Omega+1}$ 在统一形态上的替身, 任意深度的好性塔, 以及把 $\Omega_{\Omega+1}$ 替身的标签归约到 "$\Omega_\Omega$ 闭包定理对一切深度成立" 这一个假设. 标签定理、链上的下一批点与后续阶段的评估在 [OmegaPlus1](OmegaPlus1.lagda.md).
>
> 结论先说:
>
> 1. **替身不是新帧, 是符号项上的算子 (§3).** $X+\Omega_{\Omega+1}$ 对符号前缀 $X$ (标签 $x$) 定义为 `Ω⁺ X d P = limA d (λ n → Γ n d P)`, 链 $\Gamma_0 = X\oplus\Psi\,\varnothing$, $\Gamma_{n+1}=X\oplus\Psi(\Gamma_n)$, 标签 $x+\gamma_n$, $\gamma_0=\Omega_\Omega$, $\gamma_{k+1}=\psi_\Omega(x+\gamma_k)$. 这正是 EBO 规则 6 在层 $\Omega$ 的链 (`γW x (Ω⁺¹ ∷ []) Ωᵗ`, 定义性相等), 链点含整个前缀 $x$ (TopDown §9 的 "前缀要以 `Sym` 的形式给出": 前缀是符号项时在深处重放它不需要任何新机制, `X` 本来就对一切深度有定义). **不加折叠子句, 不加构造子, 不加层号**: $\Omega_{\Omega+1}$ 在对象层只是一个 $\mathbb N$-极限 (交替原则), 链点是 `Ψ` 的迭代.
> 2. **"$w=\Omega$ 无 `Idx`" 的支配问题消失 (§2).** GoodL 的警示针对 "弹出 $\Omega_{\Omega+1}$ 的闭包": 闭包行 `gŝ` 要地板下标的 `Idx`, 而 $\Omega$ 没有. 这里没有闭包: $\Omega_{\Omega+1}$ 处的行是 `gl` (ω-极限行), 它只要 `cof ≡ cω` 与各项标签. 记号侧唯一要用到 "$\Omega$ 比一切可数下标大" 的地方是 `gtΩ : Idx w → cmpᵀ (Ω+1) w ≡ gt` (SystemOmega 的 `cmp-ΩC`, 不要标准形), 它让 $\psi_w(\cdots+\Omega_{\Omega+1})$ 的共尾度坍缩为 $\omega$, 基本列走规则 6 的链. 替代 `occ<`/`Lab-oc` 的是替身层本身: 一切可数目标都在 $\Omega$ 之下, 是常数事实, 不需要在每个链点处现场比较.
> 3. **好性塔的接口 (§2) 与两个实例 (§4, §5).** 本阶段对 "深度 $d$ 的好前缀" 只用五条封闭性, 写成接口 `Tower` (深度 0 定义为 Uniform2 的 `GA0`; 深度 $\ge1$ 任意, 带静态地板标签 `flG`、作用 `app`、弱化 `wkG`、$\Omega$ 层规则 6 的极限行 `limΩ`). 零、和、帧 `Ψ` 的规则对任意塔一次证出 (`Generic`: `good∅d`/`good⊕d`/`goodΨd`), `Ψ` 的规则只要指数前缀在**空底**上好 (`GEd`), 这是链点 $\Psi(\Gamma_n)$ 唯一需要的. 实例一 `weak`: TopDown `GoodA` 形的弱塔 (深度 $d+1$ = 静态地板标签 + "把好的深度 $d$ 前缀变成好的"), 全部字段是定理. 实例二 `tow1`: 深度 1 取 Uniform2Depth1 的完整记录 `GA1` (含目标非零标签与帧互模拟), 深度 $\ge2$ 弱形; 全部字段是定理, 它在深度 1 的闭包假设**字面**是 "`GA1 E ζ → GA1 (Ω̂A 1 E) (ζ ++ Ω_Ω)`" (`refl` 类型等式), 即 Uniform2 §6 `DepthOneΩ.goodΩ̂₁` 去掉 `BranchΩ` 的陈述、(Ω_Ω)² 路线的目标 (`fromBranch`).
> 4. **极限行的深度提升 (§4, §5).** 深度 0 的 ω-极限行 (`limW`/`lim0`/`limR`) 与新的 $\Omega$ 层规则 6 行 (`limΩW`/`limΩ0`) 提升到一切深度 (`limGAω`/`limGAΩ` 对弱塔, `lim1ω`/`lim1Ω`/`lim1Gω`/`lim1GΩ` 对 `tow1`, 都对 $d$ 归纳): 深度 $d+1$ 的极限在包装 $\psi_\Omega(\cdot)$ 之后又是深度 $d$ 的 ω-极限 (`ωW`/`gtW` 以 $w=\Omega$ 为目标, `cmpᵀ (Ω+1) Ω ≡ gt` 由计算给出). 这是接口里唯一有数学内容的字段.
> 5. **归约定理 (§3 `Reduce.goodΩ⁺`, 对任意塔).** 设 `HΩ̂ : ∀ d → G (suc d) (Ω̂A d) []` ($\Omega_\Omega$ 的闭包定理对一切深度; $d=0$ 对两个实例都是定理: `HΩ̂₀`、`goodΩ̂₀`). 则对一切在空底上好的符号前缀 $X$ (标签 $x$), `Ω⁺ X` 在空底上好, 标签 $x+\Omega_{\Omega+1}$, 对一切深度. 没有别的前提. $\psi_0(\Omega_{\Omega+1})$、$\psi_0(\Omega_{\Omega+1}+1)$、$\psi_0(\Omega_{\Omega+1}\cdot2)$ 的标签在 OmegaPlus1 由它得到.
> 6. **决定性检验 (§6, `refl`) 与一个编译否定.** 树 `TOᵀ = ψᵀ (Ω⁺ ∅ᵀ)` 是 ω-极限, 第 0 项是界 1 的闭包 ($\psi_0(\Omega_\Omega)$), 第 1 项与 Uniform2 的 $\psi_0(\Omega_\Omega^2)$ 树 `ψᵀ (Ψ (Ψ ∅ᵀ))` 在全部检验路径上同种, 但**字面不等** (`fk zero ⊔ fz != fk zero`: 闭包把地板类型传给 `bound`); 记号侧 `fsn tO n ≡ ψ₀(γ_n)` 对一切 $n$ (`fs-tO`), `walk tO [1] ≡ tΩ2`. $\psi_0(\Omega_{\Omega+1}+1)$ 与 $\psi_0(\Omega_{\Omega+1}\cdot2)$ 的标准形 `tO+1-NF`/`tO·2-NF` 手工给出.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OmegaPlus1Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; Ωˢ; kind; kl; kc; walkˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; c1; cω; cΩ; Ωt; sucT; cmpᵀ; gt; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.StandardOmega using (NF₁; NFᴾ₁; NF₁-fsn; n[]; n∷; nψ; sC; sΩ; bnd[]; flatBnd; f∷; f[]; f1; walk; tO-NF)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.SystemOmega using (Occ; od; cmp-ΩC)
open import OCF.Align.Stage2 using (Ωᵗ; tO)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.Decouple using (Idx; lvI)
open import OCF.Align.UniformS
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (πw; γW; gtW; ωW; repW; cofW)
open import OCF.Align.OmegaKBase using (tΩ2)
open import OCF.Align.Uniform2Base
open import OCF.Align.Uniform2Depth1 using (GA1; ga1; fl1; gw1; gv1; gr1; goodΩ̂₀; wkGR)
open import OCF.Align.Uniform2 using (good∅ᴿ; FlrLab-re; reassoc; wkGA1; BranchΩ; module DepthOneΩ)
```

## §1 记号侧: $\Omega_{\Omega+1}$ 与层 $\Omega$ 的规则 6

EBO 里 $\Omega_{\Omega+1}=\psi_{\Omega+1}(0)$ 是主项 `Ω⁺¹`; $\psi_0(\Omega_{\Omega+1})$ 是 Stage2 的 `tO`. 它的共尾度是 `cΩ Ωᵗ` ($\Omega_{\Omega+1}$ 正规, 规则 `cofψ0 … c1`), 基本列 $\Omega_{\Omega+1}[\eta]=\eta$ (正规叶). 两条都由计算给出.

```agda
Ω⁺¹ : PT
Ω⁺¹ = ψᵗ (sucT Ωᵗ) []

_ : tO ≡ ψ₀ᵗ (Ω⁺¹ ∷ [])
_ = refl

cofΩ⁺¹ : cof (Ω⁺¹ ∷ []) ≡ cΩ Ωᵗ
cofΩ⁺¹ = refl

fsTΩ⁺¹ : ∀ θ → fsT (Ω⁺¹ ∷ []) θ ≡ θ
fsTΩ⁺¹ θ = refl
```

**$\Omega+1$ 比一切可数下标大.** 对带 `Idx` 的下标 $w$ (可数, `Idx-Ctbl`), `cmpᵀ (Ω+1) w ≡ gt` 是 SystemOmega `cmp-ΩC` 的实例 (对任意可数项为常数 `gt`, 连标准形都不要). 这是本阶段记号侧唯一的 "$\Omega$ 专属" 事实: 它使 $\psi_w(\cdots+\Omega_{\Omega+1})$ 走规则 6 (共尾度坍缩为 $\omega$, 基本列是层 $\Omega$ 的链), 对可数目标 $w$ 与目标 $0$ 都一样 (目标 $0$ 时 `cmpᵀ (Ω+1) [] ≡ gt` 直接计算).

```agda
gtΩ : ∀ {w} → Idx w → cmpᵀ (sucT Ωᵗ) w ≡ gt
gtΩ Iw = cmp-ΩC (Idx-Ctbl Iw) (𝟏 ∷ [])

gtΩΩ : cmpᵀ (sucT Ωᵗ) Ωᵗ ≡ gt
gtΩΩ = refl
```

**层 $\Omega$ 的链.** 对前缀 $x$, $\gamma_0=\Omega_\Omega$, $\gamma_{k+1}=\psi_\Omega(x+\gamma_k)$. 这是 OmegaExpBase 的 `γW` 以 $\nu=\Omega$、尾巴 $\Omega_{\Omega+1}$ 的实例, 两条递推式定义性成立 (`fsT (Ω⁺¹ ∷ []) θ ≡ θ` 由计算). `fsΩ⁺¹` 是规则 6 在层 $\Omega$ 的形式: 任意前缀、任意满足 `gt` 的目标.

```agda
γΩ : T → ℕ → T
γΩ x = γW x (Ω⁺¹ ∷ []) Ωᵗ

_ : ∀ x → γΩ x 0 ≡ ΩΩ ∷ []
_ = λ x → refl

_ : ∀ x n → γΩ x (suc n) ≡ ψΩᵗ (x ++ γΩ x n)
_ = λ x n → refl

fsΩ⁺¹ : ∀ w ps → cmpᵀ (sucT Ωᵗ) w ≡ gt → ∀ n → fsn (πw w ps (Ω⁺¹ ∷ [])) n ≡ πw w ps (γΩ ps n)
fsΩ⁺¹ w ps em n = gtW w ps Ω⁺¹ [] Ωᵗ refl em n

fs-tO : ∀ n → fsn tO n ≡ ψ₀ᵗ (γΩ [] n)
fs-tO n = fsΩ⁺¹ [] [] refl n

nfγ : ∀ n → NF₁ (ψ₀ᵗ (γΩ [] n))
nfγ n = subst NF₁ (fs-tO n) (NF₁-fsn tO-NF refl n)

_ : walk tO (0 ∷ []) ≡ ψ₀ᵗ (ΩΩ ∷ [])
_ = refl

_ : walk tO (1 ∷ []) ≡ tΩ2
_ = refl
```

**链上的下两点.** $\psi_0(\Omega_{\Omega+1}+1)$ (后继, 规则 4: $[n]=\psi_0(\Omega_{\Omega+1})\cdot n$) 与 $\psi_0(\Omega_{\Omega+1}\cdot2)$ (规则 6, 链点含前缀 $\Omega_{\Omega+1}$: $[n]=\psi_0(\Omega_{\Omega+1}+\gamma_n)$, $\gamma_{k+1}=\psi_\Omega(\Omega_{\Omega+1}+\gamma_k)$). 标准形手工给出, 形状同 StandardOmega 的 `tO-NF` (下标 $\Omega+1$ 是 `sΩ`; 参数全为 $0$ 的项是 `Flat`, `flatBnd`).

```agda
tO+1 : T
tO+1 = ψ₀ᵗ (Ω⁺¹ ∷ 𝟏 ∷ [])

tO·2 : T
tO·2 = ψ₀ᵗ (Ω⁺¹ ∷ Ω⁺¹ ∷ [])

nfΩ+1 : NF₁ (sucT Ωᵗ)
nfΩ+1 = n∷ (nψ nf1 (sC (c∷ c[])) n[] bnd[]) nf1 (inj₁ refl)

nfΩ⁺¹ : NFᴾ₁ Ω⁺¹
nfΩ⁺¹ = nψ nfΩ+1 (sΩ (c∷ c[])) n[] bnd[]

tO+1-NF : NF₁ tO+1
tO+1-NF = n∷ (nψ n[] (sC c[]) (n∷ nfΩ⁺¹ nf1 (inj₁ refl)) (flatBnd (f∷ (f∷ f1 f1) f1))) n[] tt

tO·2-NF : NF₁ tO·2
tO·2-NF = n∷ (nψ n[] (sC c[]) (n∷ nfΩ⁺¹ (n∷ nfΩ⁺¹ n[] tt) (inj₂ refl)) (flatBnd (f∷ (f∷ f1 f1) (f∷ (f∷ f1 f1) f[])))) n[] tt

fs-tO+1 : ∀ n → fsn tO+1 n ≡ replicate n (ψᵗ [] ((Ω⁺¹ ∷ []) ++ []))
fs-tO+1 n = repW [] (Ω⁺¹ ∷ []) 𝟏 [] refl n

fs-tO·2 : ∀ n → fsn tO·2 n ≡ ψ₀ᵗ (Ω⁺¹ ∷ γΩ (Ω⁺¹ ∷ []) n)
fs-tO·2 n = fsΩ⁺¹ [] (Ω⁺¹ ∷ []) refl n

_ : walk tO·2 (1 ∷ []) ≡ ψ₀ᵗ (Ω⁺¹ ∷ ψΩᵗ (Ω⁺¹ ∷ ΩΩ ∷ []))
_ = refl
```

**读法.** `fs-tO·2` 的链点 $\psi_\Omega(\Omega_{\Omega+1}+\gamma_k)$ 把前缀 $\Omega_{\Omega+1}$ 带进 $\psi_\Omega$ 的指数. 树侧要在深度 $d+1$ 处重放深度 $d$ 的前缀; 前缀是 `Sym` (对一切深度有定义) 时这是免费的 (§3).

## §2 好性塔的接口

本阶段对 "深度 $d$ 的好前缀" 只用到几条封闭性, 与具体的好性记录是什么无关. 把它们写成接口 `Tower`: 一族谓词 `G d E ζ` (深度 $d$、前缀 $E$、标签 $\zeta$), 深度 0 **定义为** Uniform2 的 `GA0` (标签定理由此读出, 深度 0 的尾巴定理 `goodTl0` 直接可用), 深度 $\ge1$ 是字段 `G₊`; 带 (ii) 静态地板标签 `flG`; (iii) **作用** `app`: 深度 $d+1$ 的好前缀把好的深度 $d$ 前缀 $(P,\pi)$ 变成好的 $(E\,P,\ \pi+\psi_\Omega(\zeta))$ (TopDown `GoodA` 的定义性蕴含, 这里是接口字段); (iv) 弱化 `wkG`; (v) **$\Omega$ 层规则 6 的极限行** `limΩ` 在一切深度: 尾巴 $\Omega_{\Omega+1}$ 的 $\mathbb N$-极限, 第 $n$ 点标签 $ps+\gamma_n$ (`γW ps (y ∷ ys) Ωᵗ n`), 则极限好. 这是接口里唯一有数学内容的字段, 两个实例 (§4 弱塔 `weak`, §5 深度 1 取 `GA1` 的塔 `tow1`) 都把它证成定理. 之所以抽象: 深度 $\ge1$ 的好性记录的形状由 $\Omega_\Omega$ 闭包定理的**证明**决定 ((Ω_Ω)² 路线正在改它的互模拟字段), 而本阶段只用它的**封闭性**; 任何满足接口的记录都得到本阶段的全部定理.

```agda
Gof : (∀ d {φ} → A (suc d) φ → T → Set) → ∀ d {φ} → A d φ → T → Set
Gof G₊ zero    P π = GA0 P π
Gof G₊ (suc d) E ζ = G₊ d E ζ

record Tower : Set₁ where
  field
    G₊   : ∀ d {φ} → A (suc d) φ → T → Set
    flG  : ∀ d {φ} {E : A d φ} {ζ} → Gof G₊ d E ζ → FlrLab φ ζ
    app  : ∀ d {φ} {E : A (suc d) φ} {ζ} → Gof G₊ (suc d) E ζ →
           ∀ {fl} {P : A d fl} {π} → Gof G₊ d P π → Gof G₊ d (E P) (π ++ ψΩᵗ ζ)
    wkG  : ∀ d {φ ψ} {E : A d φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) →
           Gof G₊ d E ζ → Gof G₊ d (wk d le E) ζ
    limΩ : ∀ d {φ} {F : ℕ → A d φ} ps y ys → cof (y ∷ ys) ≡ cΩ Ωᵗ → FlrLab φ (ps ++ (y ∷ ys)) →
           (∀ n → Gof G₊ d (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → Gof G₊ d (limA d F) (ps ++ (y ∷ ys))
  G : ∀ d {φ} → A d φ → T → Set
  G = Gof G₊
```

**符号项的好性与规则 (对任意塔).** `GSd d X x`: 深度 $d$ 上把一切好前缀 $(P,\pi)$ 变成 $(X\,d\,P,\ \pi+x)$ (Uniform2 `GS0`/`GS1` 的任意深度版). `GEd d X x`: 只对**空底** ($\pi=[]$) 要求; 这是链点 $\Psi(\Gamma_n)$ 所需的全部, 因为 `Ψ Y d P = Y (suc d) (Ω̂A d) P` 而 $\Omega_\Omega$ 作为指数前缀的标签是 $[]$. 零与和是 `wkG` 加列表的结合律; 帧是 `app` 逐字. `HΩ̂`: $\Omega_\Omega$ 的闭包定理对一切深度 (塔的每一层各一条).

```agda
module Generic (𝕋 : Tower) where
  open Tower 𝕋 public

  GSd : ∀ d {φ} → Sym φ → T → Set
  GSd d X x = ∀ {fl} {P : A d fl} {π} → G d P π → G d (X d P) (π ++ x)

  GEd : ∀ d {φ} → Sym φ → T → Set
  GEd d X x = ∀ {fl} {P : A d fl} → G d P [] → G d (X d P) x

  GS→GE : ∀ d {φ} {X : Sym φ} {x} → GSd d X x → GEd d X x
  GS→GE d S GP = S GP

  strip∅ : ∀ {φ K} → InF K (φ ⊔ fz) → InF K φ
  strip∅ (inl k) = k
  strip∅ (inr ())

  good∅d : ∀ d → GSd d ∅ᵀ []
  good∅d d {fl} {P} {π} GP = subst (G d (∅ᵀ d P)) (sym (++-identityʳ π)) (wkG d proj₁ strip∅ GP)

  GE∅ : ∀ d → GEd d ∅ᵀ []
  GE∅ d = GS→GE d {X = ∅ᵀ} {x = []} (good∅d d)

  good⊕d : ∀ d {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → GSd d X x → GSd d Y y → GSd d (X ⊕ Y) (x ++ y)
  good⊕d d {X = X} {Y} {x} {y} GX GY {fl} {P} {π} GP =
    subst (G d ((X ⊕ Y) d P)) (++-assoc π x y) (wkG d (λ { (u , (v , w)) → (u , v) , w }) reassoc (GY (GX GP)))

  goodE⊕ : ∀ d {φ ψ} {X : Sym φ} {Y : Sym ψ} {x y} → GEd d X x → GSd d Y y → GEd d (X ⊕ Y) (x ++ y)
  goodE⊕ d GX GY GP = wkG d (λ { (u , (v , w)) → (u , v) , w }) reassoc (GY (GX GP))

  goodΨd : ∀ d {φ} {Y : Sym φ} {y} → G (suc d) (Y (suc d) (Ω̂A d)) y → GSd d (Ψ Y) (ψΩᵗ y)
  goodΨd d GY GP = app d GY GP

  HΩ̂ : Set
  HΩ̂ = ∀ d → G (suc d) (Ω̂A d) []

  goodEΨ : ∀ d {φ} {Y : Sym φ} {y} → GEd (suc d) Y y → G (suc d) (Ω̂A d) [] → GSd d (Ψ Y) (ψΩᵗ y)
  goodEΨ d GY H = goodΨd d (GY H)
```

**读法 (对 README 警示的回答).** "ψ_Ω 帧地板 $w=\Omega$ 无 `Idx`" 说的是**弹出** $\Omega_{\Omega+1}$ 的闭包: 若把 $\Omega_{\Omega+1}$ 做成一个像 `Ω̂A` 那样的闭包帧, 它的 `gŝ` 行要一个带 `Idx` 的地板下标, 而 $\Omega$ 没有 (它不在任何可数链点之下). 本文不弹出它: $\psi_i(P+\Omega_{\Omega+1})$ 在**一切可数目标** $i$ 处都是 ω-共尾的 (规则 6, `gtΩ`), 树是 `limA`, 行是 `gl`. 不需要支配论证, 因为没有界要被支配; 需要的只是 "$\Omega+1$ 大于一切可数下标" 这个常数事实 (接口字段 `limΩ` 在深度 0 的证明里用它一次, §4 `limΩW`). 这与交替原则一致: $\Omega$ 只在对象层做对角 $\mathbb N$-极限, 从不被比较.

## §3 $\Omega_{\Omega+1}$ 的替身

$X+\Omega_{\Omega+1}$ 对符号前缀 $X$ 定义. 链 $\Gamma_n$ 的地板 `ΓF n` 是 $\varphi$ 与 `fk zero` 的若干份, 都从 `Ev ℓ (φ ⊔ fk zero)` 造出 (`evΓ`), 所以替身的地板是 $\varphi\sqcup$ `fk zero`, 与 $n$ 无关. 定义与塔无关.

```agda
module OmegaPlus {φ} (X : Sym φ) where
  ΓF : ℕ → Flr
  ΓF zero    = φ ⊔ (fk zero ⊔ fz)
  ΓF (suc n) = φ ⊔ (fk zero ⊔ ΓF n)

  ΓS : ∀ n → Sym (ΓF n)
  ΓS zero    = X ⊕ Ψ ∅ᵀ
  ΓS (suc n) = X ⊕ Ψ (ΓS n)

  evΓ : ∀ n {ℓ} → Ev ℓ (φ ⊔ fk zero) → Ev ℓ (ΓF n)
  evΓ zero    e = proj₁ e , (proj₂ e , tt)
  evΓ (suc n) e = proj₁ e , (proj₂ e , evΓ n e)

  leΓ : ∀ n {fl ℓ} → Ev ℓ (fl ⊔ (φ ⊔ fk zero)) → Ev ℓ (fl ⊔ ΓF n)
  leΓ n e = proj₁ e , evΓ n (proj₂ e)

  inΓ : ∀ n {fl K} → InF K (fl ⊔ (φ ⊔ fk zero)) → InF K (fl ⊔ ΓF n)
  inΓ zero    (inl k)       = inl k
  inΓ zero    (inr (inl k)) = inr (inl k)
  inΓ zero    (inr (inr k)) = inr (inr (inl k))
  inΓ (suc n) (inl k)       = inl k
  inΓ (suc n) (inr (inl k)) = inr (inl k)
  inΓ (suc n) (inr (inr k)) = inr (inr (inl k))

  Ω⁺ : Sym (φ ⊔ fk zero)
  Ω⁺ d P = limA d (λ n → wk d (leΓ n) (ΓS n d P))
```

**链点的好性 (对任意塔).** 对 $n$ 归纳, 对一切深度同时: $\Gamma_0=X\oplus\Psi\varnothing$ 用零与帧的规则, $\Gamma_{n+1}=X\oplus\Psi(\Gamma_n)$ 用归纳假设在深度 $d+1$ 的实例 (空底 `Ω̂A d`, 由 `HΩ̂ d`). 标签 $x+\gamma_n$ 与 `γΩ x n` 定义性相等 (§1). **替身的好性 (归约定理)**: 底是空标签的好前缀, 各链点由 `goodΓ`, 极限由接口的 `limΩ` (前缀 $x$, 尾巴 $\Omega_{\Omega+1}$, 链点标签定义性地就是 `ps ++ fsT (y ∷ ys) (γW …)`). 地板标签: 底的地板由空标签支配, $X$ 的地板由 $x$ 里的出现见证 (取自 `flG`), `fk zero` 平凡.

```agda
module Reduce (𝕋 : Tower) {φ} (X : Sym φ) where
  open Generic 𝕋
  open OmegaPlus X

  goodΓ : ∀ {x} → HΩ̂ → (∀ d → GEd d X x) → ∀ n d → GEd d (ΓS n) (x ++ γΩ x n)
  goodΓ {x} H GX zero d =
    goodE⊕ d {X = X} {Y = Ψ ∅ᵀ} {x = x} {y = ψΩᵗ []} (GX d)
           (goodEΨ d {Y = ∅ᵀ} {y = []} (GE∅ (suc d)) (H d))
  goodΓ {x} H GX (suc n) d =
    goodE⊕ d {X = X} {Y = Ψ (ΓS n)} {x = x} {y = ψΩᵗ (x ++ γΩ x n)} (GX d)
           (goodEΨ d {Y = ΓS n} {y = x ++ γΩ x n} (goodΓ H GX n (suc d)) (H d))

  goodΩ⁺ : ∀ {x} → HΩ̂ → (∀ d → GEd d X x) → ∀ d → GEd d Ω⁺ (x ++ (Ω⁺¹ ∷ []))
  goodΩ⁺ {x} H GX d {fl} {P} GP =
    limΩ d {F = λ n → wk d (leΓ n) (ΓS n d P)} x Ω⁺¹ [] refl
         (FlrLab-⊔ (flG d GP) (FlrLab-⊔ (FlrLab-re inr (flG d (GX d GP))) FlrLab-z))
         (λ n → wkG d (leΓ n) (inΓ n) (goodΓ H GX n d GP))
```

**读法.** `goodΩ⁺` 的前提只有 `HΩ̂` 与 $X$ 的空底好性, 结论对一切深度. 所以 `Ω⁺` 可以嵌套 (`Ω⁺ (Ω⁺ ∅ᵀ)` 是 $\Omega_{\Omega+1}\cdot2$) 或作为 $\Psi$ 的指数 (`Ψ (Ω⁺ ∅ᵀ)` 是 $\psi_\Omega(\Omega_{\Omega+1})$, 需要 `GEd (suc d)`, 已在结论里). 唯一不能做的是把 `Ω⁺ X` 放到**非空**底上 (`GSd`): $\psi_i(P+X+\Omega_{\Omega+1})$ 的链点要含 $P$, 而 `Ω⁺ X` 只重放 $X$. 在 EBO 的标准形里这不是限制: $\Omega_{\Omega+1}$ 左边只能是 $\ge\Omega_{\Omega+1}$ 的项, 在本阶段就是 $\Omega_{\Omega+1}$ 自己的若干份, 都可以并进 $X$.

## §4 实例一: TopDown 形的弱塔

深度 0 是 `GA0`; 深度 $d+1$ 是静态地板标签加 "把好的深度 $d$ 前缀变成好的" (TopDown `GoodA` 形). 它是满足接口的**最弱**塔: 任何含更多字段 (互模拟、目标非零标签、依目标的地板见证) 的记录都蕴含它. 先是定义与形式字段, 然后是 `limΩ` 的证明 (§4 后半).

```agda
GAd′ : ∀ d {φ} → A d φ → T → Set
GAd  : ∀ d {φ} → A d φ → T → Set
GAd′ zero    P π = GR P π
GAd′ (suc d) E ζ = ∀ {fl} {P : A d fl} {π} → GAd d P π → GAd′ d (E P) (π ++ ψΩᵗ ζ)
GAd d {φ} X x = FlrLab φ x × GAd′ d X x

_ : ∀ {fl} (P : Run fl) π → GAd 0 P π ≡ GA0 P π
_ = λ P π → refl

fromGA1 : ∀ {φ} {E : A 1 φ} {ζ} → GA1 E ζ → GAd 1 E ζ
fromGA1 G = fl1 G , gv1 G

wkGAd′ : ∀ d {φ ψ} {E : A d φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → GAd′ d E ζ → GAd′ d (wk d le E) ζ
wkGAd′ zero    le G = wkGR le G
wkGAd′ (suc d) le G GP = wkGAd′ d (λ ev → proj₁ ev , le (proj₂ ev)) (G GP)

wkGAd : ∀ d {φ ψ} {E : A d φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) →
        GAd d E ζ → GAd d (wk d le E) ζ
wkGAd d le f (F , G) = FlrLab-re f F , wkGAd′ d le G

appGAd : ∀ d {φ} {E : A (suc d) φ} {ζ} → GAd (suc d) E ζ → ∀ {fl} {P : A d fl} {π} → GAd d P π → GAd d (E P) (π ++ ψΩᵗ ζ)
appGAd d (FE , HE) (FP , GP) = FlrLab-⊔ FP (FlrLab-mono (λ o → od o) FE) , HE (FP , GP)
```

**读法.** `GAd 1 E ζ` 恰是 `GA1` 去掉目标非零的 `GW1` 与帧互模拟 `gr1` 之后剩下的部分 (`gv1 : GV1 E ζ` 与 `GAd′ 1 E ζ` 定义性相同). 那两个字段是**证明**深度 1 的闭包定理时的归纳不变量, 不是**使用**它时需要的; 但正因如此, 弱塔的 `HΩ̂` 在深度 $\ge1$ 可能比可证的陈述更强 (对一切只满足弱条件的 $E$ 量化). 这是 §5 第二个实例存在的理由.

**$\Omega$ 层的极限行, 深度 0.** 目标 $w$ 带 `Idx` 时 `gtΩ` 给 `gt`, 共尾度坍缩为 $\omega$ (`cofW` + `cofA`), 第 $m$ 项是 `gtW` 给的 $\psi_w(ps+\gamma_m)$: 这是 Uniform2Base `limᵢW` 的 `fld` 分支去掉派发 (链点不再由 `chainA` 现造, 而是前提里的 `F m`). 目标 $0$ 同理 (`cmpᵀ (Ω+1) [] ≡ gt` 直接计算). 互模拟是 `limR`. ω-极限行 `limωGR` 是 Uniform2Base 的 `limW`/`lim0`/`limR` 打包.

```agda
module _ {φ} {ps : T} {y : PT} {ys : T} (c : cof (y ∷ ys) ≡ cΩ Ωᵗ) where
  limΩW : ∀ {F : ℕ → Run φ} → (∀ n → LW (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) →
          LW (limA 0 F) (ps ++ (y ∷ ys))
  limΩW {F} h {w = w} ev p Iw ei ki =
    gl (trans (cofW w ps y ys) (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w Ωᵗ) em)))
       (λ n → subst (LabL₊ _ Ll _) (sym (gtW w ps y ys Ωᵗ c em n)) (h n ev p Iw ei ki))
    where em = gtΩ Iw

  limΩ0 : ∀ {F : ℕ → Run φ} → (∀ n → L0 (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) →
          L0 (limA 0 F) (ps ++ (y ∷ ys))
  limΩ0 {F} h ev p nu =
    limᴸ nu cω′ (λ n → proj₁ (Rn n)) (λ n → subst (Lab _) (sym (gtW [] ps y ys Ωᵗ c refl n)) (proj₂ (Rn n)))
    where
    cω′ : cof (ψ₀ᵗ (ps ++ (y ∷ ys))) ≡ cω
    cω′ = trans (cofW [] ps y ys) (cong (E.cofA []) c)
    Rn = λ n → h n ev p (subst NF₁ (gtW [] ps y ys Ωᵗ c refl n) (NF₁-fsn nu cω′ n))

  limΩGR : ∀ {F : ℕ → Run φ} → (∀ n → GR (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) →
           GR (limA 0 F) (ps ++ (y ∷ ys))
  limΩGR h = gr (limΩW (λ n → gW (h n))) (limΩ0 (λ n → g0 (h n))) (limR (λ n → gR (h n)))

limωGR : ∀ {φ} {ps : T} {y : PT} {ys : T} {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω →
         (∀ n → GR (F n) (ps ++ fsn (y ∷ ys) n)) → GR (limA 0 F) (ps ++ (y ∷ ys))
limωGR {ps = ps} {y} {ys} {F} c h =
  gr (limW {ps = ps} {y} {ys} {F} c (λ n → gW (h n))) (lim0 {ps = ps} {y} {ys} {F} c (λ n → g0 (h n))) (limR (λ n → gR (h n)))
```

**深度提升.** 深度 $d+1$ 的极限 `limA (suc d) F` 作用于底 $P$ 逐点是深度 $d$ 的极限 `limA d (λ n → F n P)`, 标签从 $\zeta$ 变成 $\pi+\psi_\Omega(\zeta)$. ω-极限: $\psi_\Omega(\zeta)$ 仍 ω-共尾, $[n]$ 是 $\psi_\Omega(\zeta[n])$ (`ωW` 以 $w=\Omega$). $\Omega$ 层规则 6: $\psi_\Omega(ps+\Omega_{\Omega+1}+\cdots)$ 也 ω-共尾 (`cmpᵀ (Ω+1) Ω ≡ gt` 由计算), $[n]$ 是 $\psi_\Omega(ps+\gamma_n)$ (`gtW` 以 $w=\Omega$). 两者在深度 $d+1$ 都归约到深度 $d$ 的 ω-极限行. 两条引理对塔的递归部分 `GAd′` 陈述, 静态地板标签由调用处给.

```agda
cωΩ′ : ∀ ps y ys → cof (y ∷ ys) ≡ cω → cof (ψᵗ Ωᵗ (ps ++ (y ∷ ys)) ∷ []) ≡ cω
cωΩ′ ps y ys c = trans (cofW Ωᵗ ps y ys) (cong (E.cofA Ωᵗ) c)

cΩΩ′ : ∀ ps y ys → cof (y ∷ ys) ≡ cΩ Ωᵗ → cof (ψᵗ Ωᵗ (ps ++ (y ∷ ys)) ∷ []) ≡ cω
cΩΩ′ ps y ys c = trans (cofW Ωᵗ ps y ys) (cong (E.cofA Ωᵗ) c)

limGAω : ∀ d {φ} {F : ℕ → A d φ} ps y ys → cof (y ∷ ys) ≡ cω →
         (∀ n → GAd′ d (F n) (ps ++ fsn (y ∷ ys) n)) → GAd′ d (limA d F) (ps ++ (y ∷ ys))
limGAω zero    {F = F} ps y ys c h = limωGR {ps = ps} {y} {ys} {F} c h
limGAω (suc d) {F = F} ps y ys c h {fl} {P} {π} GP =
  limGAω d {F = λ n → F n P} π (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) [] (cωΩ′ ps y ys c)
          (λ n → subst (GAd′ d (F n P)) (cong (π ++_) (sym (ωW Ωᵗ ps y ys c n))) (h n GP))

limGAΩ : ∀ d {φ} {F : ℕ → A d φ} ps y ys → cof (y ∷ ys) ≡ cΩ Ωᵗ →
         (∀ n → GAd′ d (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → GAd′ d (limA d F) (ps ++ (y ∷ ys))
limGAΩ zero    {F = F} ps y ys c h = limΩGR {ps = ps} {y} {ys} c {F} h
limGAΩ (suc d) {F = F} ps y ys c h {fl} {P} {π} GP =
  limGAω d {F = λ n → F n P} π (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) [] (cΩΩ′ ps y ys c)
          (λ n → subst (GAd′ d (F n P)) (cong (π ++_) (sym (gtW Ωᵗ ps y ys Ωᵗ c refl n))) (h n GP))

GW : ∀ d {φ} → A d φ → T → Set
GW = Gof (λ d → GAd (suc d))

weak : Tower
weak = record { G₊ = λ d → GAd (suc d) ; flG = flW ; app = appW ; wkG = wkW ; limΩ = limΩW′ }
  where
  flW : ∀ d {φ} {E : A d φ} {ζ} → GW d E ζ → FlrLab φ ζ
  flW zero    = proj₁
  flW (suc d) = proj₁
  appW : ∀ d {φ} {E : A (suc d) φ} {ζ} → GW (suc d) E ζ → ∀ {fl} {P : A d fl} {π} → GW d P π → GW d (E P) (π ++ ψΩᵗ ζ)
  appW zero    = appGAd zero
  appW (suc d) = appGAd (suc d)
  wkW : ∀ d {φ ψ} {E : A d φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) → GW d E ζ → GW d (wk d le E) ζ
  wkW zero    = wkGAd zero
  wkW (suc d) = wkGAd (suc d)
  limΩW′ : ∀ d {φ} {F : ℕ → A d φ} ps y ys → cof (y ∷ ys) ≡ cΩ Ωᵗ → FlrLab φ (ps ++ (y ∷ ys)) →
           (∀ n → GW d (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → GW d (limA d F) (ps ++ (y ∷ ys))
  limΩW′ zero    {F = F} ps y ys c Fl h = Fl , limGAΩ zero {F = F} ps y ys c (λ n → proj₂ (h n))
  limΩW′ (suc d) {F = F} ps y ys c Fl h = Fl , limGAΩ (suc d) {F = F} ps y ys c (λ n → proj₂ (h n))

HΩ̂₀ : GAd 1 (Ω̂A 0) []
HΩ̂₀ = fromGA1 goodΩ̂₀
```

## §5 实例二: 深度 1 取 `GA1` 的塔

深度 0 是 `GA0`, 深度 1 是 Uniform2Depth1 的完整记录 `GA1` (含目标非零标签 `gw1` 与帧互模拟 `gr1`), 深度 $\ge2$ 是弱形 (以 `GA1` 为底). 它的闭包假设 `HΩ̂` 在深度  0 字面是 `goodΩ̂₀` (定理), 在深度 1 字面是 "对一切 `GA1`-好的指数前缀 $E$, $E+\Omega_\Omega$ 是 `GA1`-好的" —— 正是 Uniform2 §6 `DepthOneΩ.goodΩ̂₁` 去掉 `BranchΩ` 前提的陈述, (Ω_Ω)² 路线的目标. 深度 $\ge2$ 的弱形仍可能比将来可证的强 (同 §4 读法); 若将来的深度 2 记录含互模拟, 换成那个记录只需重做本节 (约 60 行), §2–§3 不动.

```agda
GAd1′ : ∀ d {φ} → A d φ → T → Set
GAd1  : ∀ d {φ} → A d φ → T → Set
GAd1′ zero          P π = GR P π
GAd1′ (suc zero)    E ζ = GA1 E ζ
GAd1′ (suc (suc d)) E ζ = ∀ {fl} {P : A (suc d) fl} {π} → GAd1 (suc d) P π → GAd1′ (suc d) (E P) (π ++ ψΩᵗ ζ)
GAd1 zero              P π = GA0 P π
GAd1 (suc zero)        E ζ = GA1 E ζ
GAd1 (suc (suc d)) {φ} E ζ = FlrLab φ ζ × GAd1′ (suc (suc d)) E ζ

toG′ : ∀ d {φ} {E : A (suc d) φ} {ζ} → GAd1 (suc d) E ζ → GAd1′ (suc d) E ζ
toG′ zero    G = G
toG′ (suc d) G = proj₂ G

flG1 : ∀ d {φ} {E : A d φ} {ζ} → GAd1 d E ζ → FlrLab φ ζ
flG1 zero          G = proj₁ G
flG1 (suc zero)    G = fl1 G
flG1 (suc (suc d)) G = proj₁ G

app1 : ∀ d {φ} {E : A (suc d) φ} {ζ} → GAd1 (suc d) E ζ → ∀ {fl} {P : A d fl} {π} → GAd1 d P π → GAd1 d (E P) (π ++ ψΩᵗ ζ)
app1 zero          G (FP , GP)  = FlrLab-⊔ FP (FlrLab-mono (λ o → od o) (fl1 G)) , gv1 G (FP , GP)
app1 (suc zero)    (FF , HF) GE = HF GE
app1 (suc (suc d)) (FF , HF) (FE , GE) = FlrLab-⊔ FE (FlrLab-mono (λ o → od o) FF) , HF (FE , GE)

wkGAd1′ : ∀ d {φ ψ} {E : A d φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) →
          GAd1′ d E ζ → GAd1′ d (wk d le E) ζ
wkGAd1′ zero          le f G = wkGR le G
wkGAd1′ (suc zero)    le f G = wkGA1 le f G
wkGAd1′ (suc (suc d)) le f H GP =
  wkGAd1′ (suc d) (λ ev → proj₁ ev , le (proj₂ ev)) (λ { (inl k) → inl k ; (inr k) → inr (f k) }) (H GP)

wkGAd1 : ∀ d {φ ψ} {E : A d φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) →
         GAd1 d E ζ → GAd1 d (wk d le E) ζ
wkGAd1 zero          le f (F , G) = FlrLab-re f F , wkGR le G
wkGAd1 (suc zero)    le f G       = wkGA1 le f G
wkGAd1 (suc (suc d)) le f (F , H) = FlrLab-re f F , wkGAd1′ (suc (suc d)) le f H
```

**`GA1` 的极限行.** 三个字段各自是深度 0 的极限行: `gw1` 用 `limW`, `gv1` 用 `limωGR`, `gr1` 用 `limR` (两列). 标签经 `ωW`/`gtW` 以 $w=\Omega$ 搬运.

```agda
lim1ω : ∀ {φ} {F : ℕ → A 1 φ} ps y ys → cof (y ∷ ys) ≡ cω → FlrLab φ (ps ++ (y ∷ ys)) →
        (∀ n → GA1 (F n) (ps ++ fsn (y ∷ ys) n)) → GA1 (limA 1 F) (ps ++ (y ∷ ys))
lim1ω {F = F} ps y ys c Fl h =
  ga1 Fl
      (λ {fl} {P} {π} FP hP → limW {ps = π} {ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {[]} {λ n → F n P} (cωΩ′ ps y ys c)
                                 (λ n → subst (LW (F n P)) (cong (π ++_) (sym (ωW Ωᵗ ps y ys c n))) (gw1 (h n) FP hP)))
      (λ {fl} {P} {π} GP → limωGR {ps = π} {ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {[]} {λ n → F n P} (cωΩ′ ps y ys c)
                                  (λ n → subst (GR (F n P)) (cong (π ++_) (sym (ωW Ωᵗ ps y ys c n))) (gv1 (h n) GP)))
      (λ s H → limR (λ n → gr1 (h n) s H))

lim1Ω : ∀ {φ} {F : ℕ → A 1 φ} ps y ys → cof (y ∷ ys) ≡ cΩ Ωᵗ → FlrLab φ (ps ++ (y ∷ ys)) →
        (∀ n → GA1 (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → GA1 (limA 1 F) (ps ++ (y ∷ ys))
lim1Ω {F = F} ps y ys c Fl h =
  ga1 Fl
      (λ {fl} {P} {π} FP hP → limW {ps = π} {ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {[]} {λ n → F n P} (cΩΩ′ ps y ys c)
                                 (λ n → subst (LW (F n P)) (cong (π ++_) (sym (gtW Ωᵗ ps y ys Ωᵗ c refl n))) (gw1 (h n) FP hP)))
      (λ {fl} {P} {π} GP → limωGR {ps = π} {ψᵗ Ωᵗ (ps ++ (y ∷ ys))} {[]} {λ n → F n P} (cΩΩ′ ps y ys c)
                                  (λ n → subst (GR (F n P)) (cong (π ++_) (sym (gtW Ωᵗ ps y ys Ωᵗ c refl n))) (gv1 (h n) GP)))
      (λ s H → limR (λ n → gr1 (h n) s H))
```

**深度 $\ge2$ 的提升** 与 §4 同形, 底换成深度 1 的 `GA1` 行.

```agda
lim1Gω : ∀ d {φ} {F : ℕ → A (suc d) φ} ps y ys → cof (y ∷ ys) ≡ cω → FlrLab φ (ps ++ (y ∷ ys)) →
         (∀ n → GAd1 (suc d) (F n) (ps ++ fsn (y ∷ ys) n)) → GAd1 (suc d) (limA (suc d) F) (ps ++ (y ∷ ys))
lim1Gω zero    {F = F} ps y ys c Fl h = lim1ω {F = F} ps y ys c Fl h
lim1Gω (suc d) {F = F} ps y ys c Fl h =
  Fl , λ {fl} {P} {π} GP →
    toG′ d (lim1Gω d {F = λ n → F n P} π (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) [] (cωΩ′ ps y ys c)
                   (FlrLab-⊔ (flG1 (suc d) GP) (FlrLab-mono (λ o → od o) Fl))
                   (λ n → subst (GAd1 (suc d) (F n P)) (cong (π ++_) (sym (ωW Ωᵗ ps y ys c n))) (app1 (suc d) (h n) GP)))

lim1GΩ : ∀ d {φ} {F : ℕ → A (suc d) φ} ps y ys → cof (y ∷ ys) ≡ cΩ Ωᵗ → FlrLab φ (ps ++ (y ∷ ys)) →
         (∀ n → GAd1 (suc d) (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → GAd1 (suc d) (limA (suc d) F) (ps ++ (y ∷ ys))
lim1GΩ zero    {F = F} ps y ys c Fl h = lim1Ω {F = F} ps y ys c Fl h
lim1GΩ (suc d) {F = F} ps y ys c Fl h =
  Fl , λ {fl} {P} {π} GP →
    toG′ d (lim1Gω d {F = λ n → F n P} π (ψᵗ Ωᵗ (ps ++ (y ∷ ys))) [] (cΩΩ′ ps y ys c)
                   (FlrLab-⊔ (flG1 (suc d) GP) (FlrLab-mono (λ o → od o) Fl))
                   (λ n → subst (GAd1 (suc d) (F n P)) (cong (π ++_) (sym (gtW Ωᵗ ps y ys Ωᵗ c refl n))) (app1 (suc d) (h n) GP)))

G1 : ∀ d {φ} → A d φ → T → Set
G1 = Gof (λ d → GAd1 (suc d))

tow1 : Tower
tow1 = record { G₊ = λ d → GAd1 (suc d) ; flG = fl1′ ; app = app1′ ; wkG = wk1′ ; limΩ = limΩ1 }
  where
  fl1′ : ∀ d {φ} {E : A d φ} {ζ} → G1 d E ζ → FlrLab φ ζ
  fl1′ zero    = flG1 zero
  fl1′ (suc d) = flG1 (suc d)
  app1′ : ∀ d {φ} {E : A (suc d) φ} {ζ} → G1 (suc d) E ζ → ∀ {fl} {P : A d fl} {π} → G1 d P π → G1 d (E P) (π ++ ψΩᵗ ζ)
  app1′ zero    = app1 zero
  app1′ (suc d) = app1 (suc d)
  wk1′ : ∀ d {φ ψ} {E : A d φ} {ζ} (le : ∀ {L} → Ev L ψ → Ev L φ) → (∀ {K} → InF K ψ → InF K φ) → G1 d E ζ → G1 d (wk d le E) ζ
  wk1′ zero    = wkGAd1 zero
  wk1′ (suc d) = wkGAd1 (suc d)
  limΩ1 : ∀ d {φ} {F : ℕ → A d φ} ps y ys → cof (y ∷ ys) ≡ cΩ Ωᵗ → FlrLab φ (ps ++ (y ∷ ys)) →
          (∀ n → G1 d (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) Ωᵗ n))) → G1 d (limA d F) (ps ++ (y ∷ ys))
  limΩ1 zero    {F = F} ps y ys c Fl h = Fl , limΩGR {ps = ps} {y} {ys} c {F} (λ n → proj₂ (h n))
  limΩ1 (suc d) {F = F} ps y ys c Fl h = lim1GΩ d {F = F} ps y ys c Fl h
```

**`tow1` 的闭包假设, 字面.** 深度 0 是 `goodΩ̂₀`; 深度 1 是 `GA1 → GA1` 的闭包 (下面的类型等式 `refl`), 它由 Uniform2 的 `DepthOneΩ.goodΩ̂₁` 在 `BranchΩ` 下给出 (`fromBranch`; `BranchΩ` 无居留, 所以这只说明形状, 不是证明).

```agda
H1₀ : GAd1 1 (Ω̂A 0) []
H1₀ = goodΩ̂₀

_ : GAd1 2 (Ω̂A 1) [] ≡ (FlrLab (fk zero) [] × (∀ {fl} {E : A 1 fl} {ζ} → GA1 E ζ → GA1 (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])))
_ = refl

fromBranch : (∀ {fl} {E : A 1 fl} {ζ} → GA1 E ζ → BranchΩ E ζ) → GAd1 2 (Ω̂A 1) []
fromBranch br = FlrLab-z , λ GE → DepthOneΩ.goodΩ̂₁ GE (br GE)
```

## §6 决定性检验

树 `TOᵀ = ψᵀ (Ω⁺ ∅ᵀ)`, 环境层号 1. 它是 ω-极限 (`kl`), 第 0 项是 $\psi_0(\Omega_\Omega)$ (界 1 的闭包, `kc one`), 第 1 项字面等于 Uniform2 的 $\psi_0(\Omega_\Omega^2)$ 树 `ψᵀ (Ψ (Ψ ∅ᵀ))` (证据重排后 `wk 0` 是恒等, Σ 与 ⊤ 的 η 让两边定义性相等). 记号侧 `walk tO [1] ≡ tΩ2` (§1).

```agda
one : Ordᴵ
one = suc zero

TOᵀ : Ordˢ zero
TOᵀ = ψᵀ (OmegaPlus.Ω⁺ ∅ᵀ) {i = zero} {ℓ = one} (tt , (tt , (λ q → q))) zero

TΩ2ᵀ : Ordˢ zero
TΩ2ᵀ = ψᵀ (Ψ (Ψ ∅ᵀ)) {i = zero} {ℓ = one} (tt , ((λ q → q) , ((λ q → q) , tt))) zero

_ : kind TOᵀ ≡ kl
_ = refl

_ : kind (walkˢ TOᵀ (0 ∷ [])) ≡ kc one
_ = refl

step1 : Ordˢ zero
step1 = walkˢ TOᵀ (1 ∷ [])

_ : kind step1 ≡ kc one
_ = refl
_ : kind TΩ2ᵀ ≡ kc one
_ = refl
_ : kind (walkˢ step1 (0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ step1 (0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ step1 (0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl
_ : kind (walkˢ step1 (0 ∷ 0 ∷ 2 ∷ [])) ≡ kc one
_ = refl
_ : kind (walkˢ TΩ2ᵀ (0 ∷ 0 ∷ 2 ∷ [])) ≡ kc one
_ = refl
```

**读法.** 第 1 项之下的路径 $[0]$、$[0][0]$、$[0][0][1]$、$[0][0][2]$ 分别到 $\psi_0(\psi_\Omega(\Omega_1))$ (ω-极限)、$\psi_0(\psi_\Omega(1))$ (ω-极限)、$\psi_0(\Omega_\Omega)$、$\psi_0(\Omega_\Omega\cdot2)$ (界 1 的闭包), 与 Uniform2 的 `TΩ2ᵀ` 逐点同种, 与 EBO 侧 (`walk tΩ2 [0,0,1]`, `[0,0,2]`, TopDown §7 检验 2) 同形. **字面相等不成立 (编译否定)**: `walkˢ TOᵀ (1 ∷ []) ≡ TΩ2ᵀ` 的 `refl` 报 `fk zero ⊔ fz != fk zero`. 原因不在值而在类型: 闭包 `cloA zero {φ}` 把地板**类型** $\varphi$ 作为显式参数传给 `bound`, 而链点 $\Gamma_1$ 里 $\Psi\varnothing$ 的地板是 `fk zero ⊔ fz` (零的地板 `fz` 留在类型里), `Ψ ∅ᵀ` 单独写时是 `fk zero`. 两棵树在一切观测点同种, 标签相同时经 `Lab-uniq` 计值后 $\cong$ (OmegaPlus1 §2), 但不是语法相等. 替身没有改变链点处的树的形状: 它只是把 Uniform2 已有的树排成一列.
