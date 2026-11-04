> **机械克隆, 验收用.** 由 `ScafLadderZUniform2Base` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform2Base` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 自上而下的统一形 (二): 字面地板证据、非紧界与第 1 阶段期望字段的证明

> 接 [TopDown](TopDown.lagda.md). 本文是 [Uniform2](Uniform2.lagda.md) 的前半: 任务 1 (两种地板设计的取舍) 与任务 2 (证明 `Stage1.Expected` 的字段). 校准与 $\psi_0(\Omega_\Omega^2)$ 在 Uniform2.
>
> 结论先说:
>
> 1. **TopDown 的 `Stage1.Expected` 无居留 (编译, `noExpected`).** `GoodR` 的静态字段 `fl : FlrLab φ ps` 对一切带标签尾巴不成立: 第 2 层的树 `up zero (up zero 1)` 带标签 $1$, 地板 `fk 1` 无下标可支配. 另外 `Emb` 的回搬是任意函数, `GoodR` 对一切证据量化也不可能成立.
> 2. **地板设计的取舍 (§1).** 保留 TopDown 的前缀塔、语法和地板 (弹栈时比较)、单一帧 `Ψ`、统一折叠; 证据改为字面 `Simᴵ` (NonTight 的选择: 字面证据天然诚实), 界由字面最大者 `suc (Mx B)` 给出、环境层号与界分开 (NonTight 的 `Mlev` 技巧); `up zero` 的地板收紧为 `flo`; `repA` 的第 1 份作用于原底 (NonTight 的设计修正, TopDown 缺; 类型地板会把帧的地板带进第 1 份的弹栈). `FlrLab` 改为 `GA` 的静态部分, `GoodR` 加回自互模拟.
> 3. **深度 0 全部是定理 (§7–§9).** 行引理 (`lim`/`suc`/`limᵢ`/`ĉ`/`ŝ`/弹栈, 各有 `…W`/`…0`/`…R` 三半) 对一般的 "前缀 + cons" 标签一次证出; `tlGR`: 深度 0 上一切带标签、自互模拟的尾巴 (任意层号) 的折叠是好前缀; `goodΩ̂0`: $P$ 好则 $P+\Omega_\Omega$ 好 (非紧界, 地板由前缀里的下标见证). 这合并了 OmegaExpBase 的 `PreW`/`Pre0`/`GoodΩ`、NonTightBase 的 `GoodΩᶠ`/`domP`、GoodLBase 的 `PreL₊`/`Pre0Vᴸ`.
> 4. **深度 1 (§10–§11, 在 Uniform2Depth1).** 层对齐的互模拟 `AlignD`/`lowA`/`fold-≅1`; 地板平凡 (第 0、1 层) 的尾巴的深度 1 折叠定理 `FullA`/`Full₁` (合并 OmegaExpBase `GoodE`/`repGood`、OmegaSqBase `WE₀`/`ZE₀`/`WE₁`/`ZE₁`、NonTightBase §7–§8). 第 2 层尾巴 $\Omega_2$、$\Omega_2+1$ 在 Uniform2 §1.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件; TopDown 的定义凡有改动都以同名复制在本文, 改动逐条记在 §1. 结论与边界在 §12.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform2Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; Fs; Fst)
open import OCF.Align.LadderLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; trˢ; tr⁻ˢ;
  H1-pen; H1-fsT)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; lt; eq; gt;
              []<; cofA) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Align.Closure using (Pen; fsT₊-pen′)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts; occ<)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP; Lab0[])
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZOmegaExpBase using (σ⊥; πw; onCons; cofΣ; predΣ; fsnΣ; fsTΣ; OccΣ; cofW; repW; ωW; γW; γW-eq;
  gtW; penW; H1W; ne-w; 1<γ; ++-ne; fsT-ne; snoc)
open import OCF.Align.LadderLabZOmegaSqBase using (ψΩ; cmpΩ; cofΩc; fsTΩ)
import OCF.Align.LadderLabZTopDown as TD
```

## §1 两种地板设计的取舍

**TopDown 的 `Expected` 不可满足.** `goodTl` 对一切带 `LabL` 标签的尾巴量化, 而 `GoodR` 的字段 `fl : FlrLab φ ps` 要求尾巴所在层号的地板被标签中出现的某个下标支配. `LabL` 允许高层树带小标签: 第 2 层的树 `up zero (up zero 1)` 带标签 $1$, 地板 `flo 2 = fk 1`, 而 $1=\psi_0(0)$ 里只出现下标 $0$, `lvI` 为 $0$, $1\not\sqsubseteq 0$. 于是在深度 0、空前缀上取 `goodTl` 的 `fl` 字段即得矛盾. 下面是编译的证明 (`noExpected`).

```agda
two′ : Ordᴵ
two′ = suc (suc zero)

t1² : Ordˢ two′
t1² = Ord₊ˢ.up zero (Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero))

lab-t1² : LabL t1² (natT 1)
lab-t1² = gu (gu (s≅ z≅ , gs gz , lab1))

occ1 : ∀ {w} → Occ w (natT 1) → w ≡ []
occ1 oh = refl
occ1 (od ())
occ1 (os ())
occ1 (oτ ())
occ1 (ot ())

lab[]≅0 : ∀ {Y} (hY : HS Y) → Lab Y [] → toLevel Y hY ≅ᴵ zero
lab[]≅0 hY (l0 c e) = toLevel-≅ hY hz e
lab[]≅0 hY (l1 () e l)
lab[]≅0 hY (lω () e h)

1⋢0 : ∀ {X} → X ≅ᴵ zero → suc zero ⊑ᴵ X → ⊥
1⋢0 z≅ (s⊑ e ())

noFlr : ∀ {w} (Iw : Idx w) → suc zero ⊑ᴵ lvI Iw → Occ w (natT 1) → ⊥
noFlr Iw le o with occ1 o
noFlr (Y , hY , lY , nY) le o | refl = 1⋢0 (lab[]≅0 hY lY) le

noExpected : TD.Expected → ⊥
noExpected Ex with TD.GoodR.fl (TD.Expected.goodTl Ex {k = two′} {t = t1²} lab-t1² zero (TD.Expected.good∅ᴿ Ex)) (TD.inr TD.ink)
... | w , Iw , le , o = noFlr Iw le o
```

**读法.** 失败与证明技巧无关: `Expected` 的类型本身无居留. 原因是 TopDown 把 "地板被支配" 写成了**静态**的、对一切尾巴的结构字段, 而尾巴的地板只在它成为后续弹栈的**底**时才被读到. 修正 (下面的第 4 条) 是把它变成 `goodTl` 的前提, 并只在真正产生 "底" 的地方 (深度 $\ge1$ 的后继行) 遗传地要求.

**第二个问题: `Emb` 的回搬是任意函数.** TopDown 的 `Emb k ℓ` 的值是 `Restrˢ c ℓ`, 其字段 `backˢ : Ordˢ c′ → Ordˢ c` 是任意函数; `GoodR` 对一切地板证据量化, 包括回搬为常函数的证据, 在那样的证据下 `limᵢA` 的穿透分支在一切输入处取同一棵树, 带不了 `gi` 行的标签. 这一条不需要单独的反例: 上面的 `noExpected` 已经让整个记录落空; 但即使去掉 `FlrLab`, 量化也必须限制在 "诚实" 的证据上. `Simᴵ` 是唯一天然诚实的证据 (它只把字面子项的证明映到字面子项的证明, 不搬运树), 所以下面改用字面证据.

**取舍.** 保留 TopDown 的: 前缀塔 `A d φ`、语法和地板 `Flr`/`fz`/`fk`/`_⊔_` (推帧时不比较, 弹栈时比较)、单一帧 `Ψ`、统一折叠 `fold d`、`repA`、`Sym`/`Rep`. 采纳 NonTight 的: 证据是字面的 `Simᴵ` (而不是 `Restrˢ`), 界与环境层号分开, 并用 `Mlev` 让一个字面层号同时装着目标与全部地板. NonTight 的设计修正 "抬地板的帧第一份在旧地板上折叠" 在本设计里自动成立: 地板是类型的一部分, 尾巴 $0$ 处 `wk d proj₁ P` 把尾巴的地板丢掉, 所以第 $m$ 份帧内部的弹栈只看到它下面的 $m-1$ 份的地板 (§4 读法). 逐条改动 (相对 TopDown):

1. `Ev ℓ (fk K) = Simᴵ (suc K) ℓ` (原为 `Emb (suc K) ℓ`); `Emb`/`simE`/`_∘ᴱ_`/`mkE` 删去; `liftEv` 沿 `Simᴵ` 搬运.
2. `limᵢA` 的地板证据 `ac : Ev ℓ φ → j <ᴵ ℓ` (原为 `Restrˢ j ℓ`), 派发与链与 OmegaExpBase 的 `ψˢ` 逐字 (穿透用 `tr⁻ˢ`).
3. 界: `Top` 记录字面的最大者 $M$ (目标或某个地板项, 字面 $<^\mathsf I\ell$) 与一个字面装着目标和全部地板的层号 $F\cong M+1$ (嵌套 `Mlev`). 闭包的界是 `suc M` (只依赖于谁最大, 地板全 $\preceq$ 目标时字面就是 `suc i`), 第 0 点在原环境 $\ell$ 上计值, 分支在 `Mlev F (suc η)` 上计值.
4. `up zero x` 子句的地板改为紧的 `flo k′` (TopDown 用 `fk k′`, 即 $x$ 的层号本身, 比 `flo` 多一). 于是第 1 层子树的地板是 `fk 0`, 平凡.
5. `FlrLab` 不再是 `GoodR` 的字段, 而是 `GoodA` 的静态部分 (§6), 支配写成 `≺ ⊎ ≅` (Level 的 $\sqsubseteq$ 对 `suc` 不单调, NonTight 的 `sB`), 并允许平凡项 $K\cong0$; `GoodR` 加回自互模拟 (TopDown §11 第 3 条).
6. `goodTl` 加前提: 尾巴地板的静态支配与后继行的遗传支配 (`HW`, §9).
7. `repA` 的第 1 份直接作用于底 $Q$ (§4 读法: TopDown 缺 NonTight 的设计修正).

## §2 字面证据与前缀塔

```agda
infixl 5 _⊔_
data Flr : Set where
  fz  : Flr
  fk  : Ordᴵ → Flr
  _⊔_ : Flr → Flr → Flr

Ev : Ordᴵ → Flr → Set
Ev ℓ fz      = ⊤
Ev ℓ (fk K)  = Simᴵ (suc K) ℓ
Ev ℓ (a ⊔ b) = Ev ℓ a × Ev ℓ b

data InF (K : Ordᴵ) : Flr → Set where
  ink : InF K (fk K)
  inl : ∀ {a b} → InF K a → InF K (a ⊔ b)
  inr : ∀ {a b} → InF K b → InF K (a ⊔ b)

liftEv : ∀ {ℓ ℓ′} (φ : Flr) → Simᴵ ℓ ℓ′ → Ev ℓ φ → Ev ℓ′ φ
liftEv fz      τ _       = tt
liftEv (fk K)  τ e       = λ q → τ (e q)
liftEv (a ⊔ b) τ (x , y) = liftEv a τ x , liftEv b τ y

Run : Flr → Set
Run φ = ∀ {i ℓ} → Ev ℓ φ → i <ᴵ ℓ → Ordˢ i

A : ℕ → Flr → Set
A zero    φ = Run φ
A (suc d) φ = ∀ {fl} → A d fl → A d (fl ⊔ φ)

wk : ∀ d {φ ψ} → (∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ) → A d φ → A d ψ
wk zero    le x ev p = x (le ev) p
wk (suc d) le x P    = wk d (λ { (u , v) → u , le v }) (x P)

limA : ∀ d {φ} → (ℕ → A d φ) → A d φ
limA zero    F ev p = Ord₊ˢ.lim (λ m → F m ev p)
limA (suc d) F P    = limA d (λ m → F m P)

limᵢA : ∀ d {φ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → A d φ) → A d φ
limᵢA zero {j = j} ac h ev p with <ᴵ-dec (ac ev) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → h (tr⁻ˢ e (outˢ (<→◃ r) y)) ev p)
... | injᵇ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ev (ac ev)) (Ωˢ j) m) ev p)
... | injᶜ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ev (ac ev)) (Ωˢ j) m) ev p)
limᵢA (suc d) ac h P = limᵢA d (λ ev → ac (proj₂ ev)) (λ x → h x P)

ŝA : ∀ d {φ} (c : Ordᴵ) → A d φ → ((η : Ordᴵ) → c ⊑ᴵ η → A d φ) → A d φ
ŝA zero    c t g ev p = Ord₊ˢ.ŝ c (t ev p) (λ η e → g η e ev p)
ŝA (suc d) c t g P    = ŝA d c (t P) (λ η e → g η e P)

ĉA : ∀ d {φ} (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → A d φ → ((η : Ordᴵ) → c ⊑ᴵ η → A d φ) → A d φ
ĉA zero    c t₀ g o₀ o ev p = Ord₊ˢ.ĉᴸ c t₀ g (o₀ ev p) (λ η e → o η e ev p)
ĉA (suc d) c t₀ g o₀ o P    = ĉA d c t₀ g (o₀ P) (λ η e → o η e P)
```

## §3 界: 字面的最大者

`Top i ℓ φ`: 已处理的地板 $\varphi$ 与目标 $i$ 的字面最大者 $M$ ($M<^\mathsf I\ell$), 它的来源 (`src`: 就是目标, 或是 $\varphi$ 的某一项且 $i\prec M$), 以及字面装着目标与全部已处理地板的层号 $F$ (`evF`, `iF`), $F\sqsubseteq M+1\sqsubseteq F$. `ins` 用有界三歧比较新项 $K$ 与 $M$ (二者都字面 $<^\mathsf I\ell$): $K\preceq M$ 时 $M$ 不变, $F' = [K+1, F, F, \dots]$; $M\prec K$ 时 $M'=K$, $F'=[F, K+1, K+1,\dots]$. 平凡项 ($K\cong0$) 永远走前者, 所以地板全平凡时 $M$ 字面就是目标.

```agda
⊑-suc : ∀ a → a ⊑ᴵ suc a
⊑-suc a = Sim→⊑ᴵ suc

FsUB : ∀ {a b c} → a ⊑ᴵ c → b ⊑ᴵ c → ∀ n → Fs a b n ⊑ᴵ c
FsUB ac bc zero    = ac
FsUB ac bc (suc n) = bc

record Top (i ℓ : Ordᴵ) (φ : Flr) : Set where
  constructor top
  field
    Mx  : Ordᴵ
    mx  : Mx <ᴵ ℓ
    src : (Mx ≡ i) ⊎ ((i ≺ᴵ Mx) × Σ Ordᴵ λ K → InF K φ × (Mx ≡ K))
    Fc  : Ordᴵ
    evF : Ev Fc φ
    iF  : i <ᴵ Fc
    FM  : Fc ⊑ᴵ suc Mx
    MF  : suc Mx ⊑ᴵ Fc
open Top public

top₀ : ∀ {i ℓ} → i <ᴵ ℓ → Top i ℓ fz
top₀ {i} p = top i p (inj₁ refl) (suc i) tt zero ⊑ᴵ-refl ⊑ᴵ-refl

srcL : ∀ {i M φ K} → (M ≡ i) ⊎ ((i ≺ᴵ M) × Σ Ordᴵ λ K′ → InF K′ φ × (M ≡ K′)) →
       (M ≡ i) ⊎ ((i ≺ᴵ M) × Σ Ordᴵ λ K′ → InF K′ (φ ⊔ fk K) × (M ≡ K′))
srcL (inj₁ e) = inj₁ e
srcL (inj₂ (s , K′ , k , e)) = inj₂ (s , K′ , inl k , e)

iM≼ : ∀ {i M φ} → (M ≡ i) ⊎ ((i ≺ᴵ M) × Σ Ordᴵ λ K → InF K φ × (M ≡ K)) → (i ≺ᴵ M) ⊎ (i ≅ᴵ M)
iM≼ {i} (inj₁ refl) = inj₂ (≅ᴵ-refl i)
iM≼ (inj₂ (s , _)) = inj₁ s

ins : ∀ {i ℓ φ K} → Top i ℓ φ → Simᴵ (suc K) ℓ → Top i ℓ (φ ⊔ fk K)
ins {i} {φ = φ} {K} (top M m sr Fx evF iF FM MF) ek with <ᴵ-dec (ek zero) m
... | injᵃ (via e r) =
  top M m (srcL sr) (Mlev (suc K) Fx (⊑ᴵ-trans (s⊑ e (suc r)) MF)) (liftEv φ (λ q → lim 1 q) evF , (λ q → lim 0 q))
      (lim 1 iF) (l⊑ (FsUB (s⊑ e (suc r)) FM)) (⊑ᴵ-trans MF (Sim→⊑ᴵ (λ q → lim 1 q)))
... | injᶜ e =
  top M m (srcL sr) (Mlev (suc K) Fx (⊑ᴵ-trans (s⊑ e zero) MF)) (liftEv φ (λ q → lim 1 q) evF , (λ q → lim 0 q))
      (lim 1 iF) (l⊑ (FsUB (s⊑ e zero) FM)) (⊑ᴵ-trans MF (Sim→⊑ᴵ (λ q → lim 1 q)))
... | injᵇ (via e r) =
  top K (ek zero) (inj₂ (≺ᴵ-trans′ sr (via e r) , K , inr ink , refl))
      (Mlev Fx (suc K) (⊑ᴵ-trans FM (s⊑ e (suc r)))) (liftEv φ (λ q → lim 0 q) evF , (λ q → lim 1 q))
      (lim 0 iF) (l⊑ (FsUB (⊑ᴵ-trans FM (s⊑ e (suc r))) ⊑ᴵ-refl)) (Sim→⊑ᴵ (λ q → lim 1 q))
  where
  ≺ᴵ-trans′ : ∀ {M′} → (M′ ≡ i) ⊎ ((i ≺ᴵ M′) × Σ Ordᴵ λ K′ → InF K′ φ × (M′ ≡ K′)) → M′ ≺ᴵ K → i ≺ᴵ K
  ≺ᴵ-trans′ (inj₁ refl) s = s
  ≺ᴵ-trans′ (inj₂ (s′ , _)) s = ≺ᴵ-trans s′ s
```

`accT` 依次并入地板的各项, `bound` 从目标出发处理整个地板. 地板的结合律搬运用 `mapTop`.

```agda
mapSrc : ∀ {i M φ ψ} → (∀ {K} → InF K φ → InF K ψ) →
         (M ≡ i) ⊎ ((i ≺ᴵ M) × Σ Ordᴵ λ K → InF K φ × (M ≡ K)) → (M ≡ i) ⊎ ((i ≺ᴵ M) × Σ Ordᴵ λ K → InF K ψ × (M ≡ K))
mapSrc g (inj₁ e)               = inj₁ e
mapSrc g (inj₂ (s , K , k , e)) = inj₂ (s , K , g k , e)

mapTop : ∀ {i ℓ φ ψ} → (∀ {L} → Ev L φ → Ev L ψ) → (∀ {K} → InF K φ → InF K ψ) → Top i ℓ φ → Top i ℓ ψ
mapTop f g t = top (Mx t) (mx t) (mapSrc g (src t)) (Fc t) (f (evF t)) (iF t) (FM t) (MF t)

accT : ∀ {i ℓ φ₁} → Top i ℓ φ₁ → (φ₂ : Flr) → Ev ℓ φ₂ → Top i ℓ (φ₁ ⊔ φ₂)
accT t fz      _       = mapTop (λ x → x , tt) inl t
accT t (fk K)  ek      = ins t ek
accT t (a ⊔ b) (x , y) =
  mapTop (λ { ((u , v) , w) → u , (v , w) })
         (λ { (inl (inl k)) → inl k ; (inl (inr k)) → inr (inl k) ; (inr k) → inr (inr k) })
         (accT (accT t a x) b y)

strip : ∀ {K φ} → InF K (fz ⊔ φ) → InF K φ
strip (inl ())
strip (inr k) = k

bound : ∀ {i ℓ} (φ : Flr) → Ev ℓ φ → i <ᴵ ℓ → Top i ℓ φ
bound φ ev p = mapTop proj₂ strip (accT (top₀ p) φ ev)

FB : ∀ {i ℓ φ} (B : Top i ℓ φ) {η} → suc (Mx B) ⊑ᴵ η → Fc B ⊑ᴵ suc η
FB B {η} e = ⊑ᴵ-trans (FM B) (⊑ᴵ-trans e (⊑-suc η))
```

**闭包.** 深度 0: 界 `suc (Mx B)`, 第 0 点 `t ev p` (原环境), 分支 $\eta$ 在 `Mlev (Fc B) (suc η)` 上, 地板经 `lim 0`, 尾巴 $\Omega_\eta$ 的地板 `fk η` 经 `lim 1`, 目标经 `lim 0 (iF B)`. 深度 $\ge1$ 与 TopDown 逐字.

```agda
cloA : ∀ d {φ} → A d (φ ⊔ fk zero) → ((η : Ordᴵ) → A d (φ ⊔ fk η)) → A d (φ ⊔ fk zero)
cloA zero {φ} t g {i} ev p =
  Ord₊ˢ.ŝ (suc (Mx B)) (t ev p)
          (λ η e → g η {ℓ = Mlev (Fc B) (suc η) (FB B e)} (liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q))
                         (lim 0 (iF B)))
  where B = bound (φ ⊔ fk zero) ev p
cloA (suc d) {φ} t g {fl} P =
  wk d (λ { (u , (v , w)) → (u , v) , w })
       (cloA d {fl ⊔ φ} (wk d (λ { ((u , v) , w) → u , (v , w) }) (t P))
                        (λ η → wk d (λ { ((u , v) , w) → u , (v , w) }) (g η P)))
```

## §4 统一折叠

与 TopDown 的 `fold` 只差两处: `limᵢ` 的地板证据是字面的 `Simᴵ`, `up zero` 的地板收紧为 `flo k′` (`toFlo` 从父层证据造出, `cvFlo` 读回; 第 0 层的 `Sim` 是唯一常量 `σ⊥`).

```agda
flo : Ordᴵ → Flr
flo zero      = fz
flo (suc k)   = fk k
flo (lim f s) = fk (lim f s)

cvFlo : ∀ k {ℓ} → Ev ℓ (flo k) → Simᴵ k ℓ
cvFlo zero      _ = σ⊥
cvFlo (suc k)   e = e
cvFlo (lim f s) e = λ q → e (suc q)

toFlo : ∀ k {ℓ} → Simᴵ (suc k) ℓ → Ev ℓ (flo k)
toFlo zero      σ = tt
toFlo (suc k)   σ = λ q → σ (suc q)
toFlo (lim f s) σ = σ

repA : ∀ d {fl ψ} → A d fl → A (suc d) ψ → ℕ → A d (fl ⊔ ψ)
repA d Q fr zero          = wk d proj₁ Q
repA d Q fr (suc zero)    = fr Q
repA d Q fr (suc (suc m)) = wk d (λ { (u , v) → (u , v) , v }) (fr (repA d Q fr (suc m)))

fold : ∀ d {fl k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → A d fl → Ordˢ k → A d (fl ⊔ φ)
fold d φ cv P Ord₊ˢ.zero = wk d proj₁ P
fold zero    φ cv P (Ord₊ˢ.suc a) ev p = Ord₊ˢ.lim (iter (fold zero φ cv P a ev p +ˢ_) Ord₊ˢ.zero)
fold (suc d) φ cv P (Ord₊ˢ.suc a) Q    = limA d (λ m → repA d Q (fold (suc d) φ cv P a) m)
fold d φ cv P (Ord₊ˢ.lim f) = limA d (λ m → fold d φ cv P (f m))
fold d φ cv P (Ord₊ˢ.limᵢ q f) = limᵢA d (λ ev → cv (proj₂ ev) q) (λ x → fold d φ cv P (f (intoˢ (<→◃ q) x)))
fold d {k = suc k′} φ cv P (Ord₊ˢ.up zero x) =
  wk d (λ { (u , v) → u , toFlo k′ (cv v) }) (fold d (flo k′) (cvFlo k′) P x)
fold d φ cv P (Ord₊ˢ.up (self n) x) = fold d φ (λ e q → cv e (lim n q)) P x
fold d {k = zero}    φ cv P (Ord₊ˢ.ŝ c t₀ g) =
  ĉA d c (toZ t₀) (λ η e → toZ (g η e)) (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d {k = suc _}   φ cv P (Ord₊ˢ.ŝ c t₀ g) = ŝA d c (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d {k = lim _ _} φ cv P (Ord₊ˢ.ŝ c t₀ g) = ŝA d c (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d φ cv P (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = ĉA d c t₀ g (fold d φ cv P o₀) (λ η e → fold d φ cv P (o η e))

Ω̂A : ∀ d → A (suc d) (fk zero)
Ω̂A d {fl} P = cloA d {fl} (fold d (fk zero) (λ e → e) P (Ωˢ (suc zero)))
                         (λ η → fold d (fk η) (λ e q → e (suc q)) P (Ωˢ η))
```

**读法 (第一份在旧地板上: 对 TopDown 的第 7 处改动).** TopDown 的 `repA d Q fr (suc m) = fr (repA d Q fr m)` 让第 1 份帧作用于 `repA d Q fr 0 = wk d proj₁ Q`; 它的值就是 $Q$, 但**类型**地板是 `fl ⊔ ψ`, 已含帧的尾巴地板 $\psi$. 帧内部到尾巴 $0$ 时弹栈的 `bound` 读的正是底的类型地板, 于是第 1 份里的弹栈拿到被抬高的界, 而前缀里还没有任何能支配它的下标: 这正是 NonTight 读法里记下的错误. 改为第 1 份直接作用于 $Q$ (类型地板 `fl`, 帧作用后才是 `fl ⊔ ψ`), 第 $m\ge2$ 份的底才含 $\psi$, 它们的标签里已有第 1 份帧的标签 (含 $\psi$ 的见证). 这就是 NonTight 的 `repᴿ`; 在统一折叠里是一个子句的差别. 地板作为类型的一部分本身不足以自动给出这条修正: 弱化 (`wk`) 只丢证据, 不缩类型.

## §5 符号项

```agda
Sym : Flr → Set
Sym φ = ∀ d → A (suc d) φ

∅ᵀ : Sym fz
∅ᵀ d P = wk d proj₁ P

tlᵀ : ∀ {k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → Ordˢ k → Sym φ
tlᵀ φ cv t d P = fold d φ cv P t

Ψ : ∀ {φ} → Sym φ → Sym (fk zero ⊔ φ)
Ψ Y d P = Y (suc d) (Ω̂A d) P

infixl 6 _⊕_
_⊕_ : ∀ {φ ψ} → Sym φ → Sym ψ → Sym (φ ⊔ ψ)
(X ⊕ Y) d P = wk d (λ { (u , (v , w)) → (u , v) , w }) (Y d (X d P))

∅ᴿ : Run fz
∅ᴿ {i} _ p = Ωˢ i

ψᵀ : ∀ {φ} → Sym φ → Run (fz ⊔ φ)
ψᵀ X = X zero ∅ᴿ
```

## §6 标签的形状

一个深度 0 的前缀 $R$ (地板 $\varphi$) 带标签 $u$ (它的参数和, 即 $R$ 在目标 $w$ 处是 $\psi_w(u)$) 指三件事: 一切非零带标签目标处的 `LabL₊` (`LW`), 目标 $0$ 处的证书与标签 (`L0`), 与自互模拟 (`≈ᴿ`). 这是 TopDown 的 `GoodR` 去掉 `fl` 再加回互模拟; `fl` 移到 §8 的 `GA` 里作为静态部分. 下面的引理都对 "前缀 + 一个 cons" 形的标签 `ps ++ (y ∷ ys)` 陈述 (OmegaExpBase 的 `πw` 记号), 于是 OmegaExpBase 的记号交换引理 (`cofW`、`ωW`、`gtW`、`penW`、`H1W`、`repW`) 原样可用.

```agda
ψ₀ᵗ : T → T
ψ₀ᵗ x = ψᵗ [] x ∷ []

ψΩᵗ : T → T
ψΩᵗ ζ = ψᵗ Ωᵗ ζ ∷ []

Lab₀ : Ordˢ zero → T → Set
Lab₀ x t = Σ (Goodᴸ (toZ x)) λ G → Lab (forceᴸ _ G) t

LW : ∀ {φ} → Run φ → T → Set
LW {φ} R u = ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
             LabL₊ i Ll (R ev p) (ψᵗ w u ∷ [])

L0 : ∀ {φ} → Run φ → T → Set
L0 {φ} R u = ∀ {ℓ} (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) → NF₁ (ψ₀ᵗ u) → Lab₀ (R ev p) (ψ₀ᵗ u)

infix 4 _≈ᴿ_
_≈ᴿ_ : ∀ {φ ψ} → Run φ → Run ψ → Set
_≈ᴿ_ {φ} {ψ} R R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → R ev p ≅ˢ R′ ev′ p′

record GR {φ} (R : Run φ) (u : T) : Set where
  constructor gr
  field
    gW : LW R u
    g0 : L0 R u
    gR : R ≈ᴿ R
open GR public
```

## §7 深度 0 的行引理

每条引理对应尾巴推导的一行 (或弹栈), 结论是组合前缀的 `LW`/`L0`/`≈ᴿ`, 前提是组成部分的同类陈述. 证明逐字取自 OmegaExpBase 的 `PreW`/`Pre0` (标签) 与 `ψˢ-≅` (互模拟), 只把 "对尾巴推导的递归调用" 换成前提. **极限行.**

```agda
module _ {φ} {ps : T} {y : PT} {ys : T} where
  limW : ∀ {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω → (∀ n → LW (F n) (ps ++ fsn (y ∷ ys) n)) → LW (limA 0 F) (ps ++ (y ∷ ys))
  limW {F} c h {w = w} ev p Iw ei ki =
    gl (trans (cofW w ps y ys) (cong (cofA w) c)) (λ n → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys c n)) (h n ev p Iw ei ki))

  lim0 : ∀ {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω → (∀ n → L0 (F n) (ps ++ fsn (y ∷ ys) n)) → L0 (limA 0 F) (ps ++ (y ∷ ys))
  lim0 {F} c h ev p nf =
    limᴸ nf cω′ (λ n → proj₁ (Rn n)) (λ n → subst (Lab _) (sym (ωW [] ps y ys c n)) (proj₂ (Rn n)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rn = λ n → h n ev p (subst NF₁ (ωW [] ps y ys c n) (NF₁-fsn nf cω′ n))

limR : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F n ≈ᴿ G n) → limA 0 F ≈ᴿ limA 0 G
limR h ev p ev′ p′ ei = l≅ (λ n → h n ev p ev′ p′ ei)
```

**后继行 (深度 0).** `fold 0` 的后继子句是输出重复 $\psi_i(P+a)\cdot m$.

```agda
sucRun : ∀ {φ} → Run φ → Run φ
sucRun R ev p = Ord₊ˢ.lim (iter (R ev p +ˢ_) Ord₊ˢ.zero)

module _ {φ} {ps : T} {y : PT} {ys : T} where
  sucW : ∀ {R : Run φ} → cof (y ∷ ys) ≡ c1 → LW R (ps ++ pred (y ∷ ys)) → LW (sucRun R) (ps ++ (y ∷ ys))
  sucW {R} c h {w = w} ev p Iw ei ki =
    gl (trans (cofW w ps y ys) (cong (cofA w) c))
       (λ m → subst (LabL₊ _ Ll _) (sym (repW w ps y ys c m)) (LRep ki (h ev p Iw ei ki) m))

  suc0 : ∀ {R : Run φ} → cof (y ∷ ys) ≡ c1 → L0 R (ps ++ pred (y ∷ ys)) → L0 (sucRun R) (ps ++ (y ∷ ys))
  suc0 {R} c h ev p nf =
    limᴸ nf cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repW [] ps y ys c m)) (proj₂ (Rs m)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rp = h ev p (subst NF₁ (repW [] ps y ys c 1) (NF₁-fsn nf cω′ 1))
    Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repW [] ps y ys c m) (NF₁-fsn nf cω′ m))

sucR : ∀ {φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈ᴿ R′ → sucRun R ≈ᴿ sucRun R′
sucR h ev p ev′ p′ ei = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ (kd-≅ ei) (h ev p ev′ p′ ei) e′) z≅)
```

**$\Omega_{j+1}$-共尾行.** `limᵢA` 的两个展开引理 (OmegaExpBase 的 `fold1S`/`pen1S`), 然后 `limᵢW` (目标 $w\ne0$, 照 `giPreS`) 与 `limᵢ0` (目标 $0$: 节点层 $0$ 照 `liLabS`, 节点层非零照 `foldLabS`).

```agda
chainA : ∀ {φ j ℓ} → (∀ {L} → Ev L φ → j <ᴵ L) → (Ordˢ j → Run φ) → Ev ℓ φ → ℕ → Ordˢ j
chainA {j = j} ac H ev = iter (λ x → H x ev (ac ev)) (Ωˢ j)

fold1A : ∀ {φ j i ℓ} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} →
         (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → limᵢA 0 ac H ev p ≡ Ord₊ˢ.lim (λ m → H (chainA ac H ev m) ev p)
fold1A {ac = ac} {ev = ev} {p = p} h with <ᴵ-dec (ac ev) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1A : ∀ {φ j i ℓ N} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} →
        j ≅ᴵ N → N ≺ᴵ i →
        Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
        limᵢA 0 ac H ev p ≡ Ord₊ˢ.limᵢ r (λ y → H (tr⁻ˢ e (outˢ (<→◃ r) y)) ev p)
pen1A {ac = ac} {ev = ev} {p = p} ej νi with <ᴵ-dec (ac ev) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))

module _ {φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ}
         (c : cof (y ∷ ys) ≡ cΩ ν) (Iν : Idx ν) (ej : j ≅ᴵ lvI Iν) where

  limᵢW : (∀ η x → LabL x η → LW (H x) (ps ++ fsT (y ∷ ys) η)) → LW (limᵢA 0 ac H) (ps ++ (y ∷ ys))
  limᵢW hW {i = i} {w = w} ev p Iw ei ki = go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → LabL₊ i Ll (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    pen pn with pen1A {ac = ac} {H = H} {ev = ev} {p = p} (≅ᴵ-refl j)
                      (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
    ... | j′ , e , r , eqn =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym eqn)
            (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
                (λ η x l → subst (λ v → LabL₊ i Ll (H (tr⁻ˢ e v) ev p) (fsT (πw w ps (y ∷ ys)) η))
                                 (sym (out-intoˢ (<→◃ r) x))
                                 (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν c pn η))
                                        (hW η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l)) ev p Iw ei ki))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) c) (cofP pn))
    fld : cmpᵀ (sucT ν) w ≡ gt → LabL₊ i Ll (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    fld em =
      subst (λ W → LabL₊ i Ll W (πw w ps (y ∷ ys))) (sym (fold1A {ac = ac} {H = H} {ev = ev} {p = p} ij))
            (gl (trans (cofW w ps y ys) (trans (cong (cofA w) c) (cong (E.cofψ₊ w ν) em)))
                (λ m → subst (LabL₊ i Ll _) (sym (gtW w ps y ys ν c em m)) (hW _ _ (chainL m) ev p Iw ei ki)))
      where
      gev : (lvI Iw ≺ᴵ lvI Iν) ⊎ (lvI Iw ≅ᴵ lvI Iν)
      gev with gt→≤ ν w em
      ... | inj₁ pw   = inj₁ (Ilt Iw Iν pw)
      ... | inj₂ refl = inj₂ (Ieq Iw Iν)
      ij : (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
      ij with gev
      ... | inj₁ s  = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ ei s) (≅ᴵ-sym ej))
      ... | inj₂ c′ = inj₂ (≅ᴵ-trans ei (≅ᴵ-trans c′ (≅ᴵ-sym ej)))
      kj : kd j ≡ false
      kj = trans (kd-≅ ej) (kdI′ Iν (gtν em (ne-w Iw ei ki)))
      chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) ν m)
      chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
      chainL (suc m) = frL₊ kj (hW _ _ (chainL m) ev (ac ev) Iν ej kj)
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabL₊ i Ll (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    go lt em = pen (inj₁ em)
    go eq em = pen (inj₂ em)
    go gt em = fld em
```

`limᵢ0`: 目标 $0$ 的前提分两半: 对一切带标签输入的 `LW` (链点在节点层 $j\ne0$ 时由它标记), 与对带自互模拟的输入的 `L0` 和互模拟 (链原子要 $c_{m+1}\cong^\mathsf s c_{m+1}$, 由组成部分的互模拟给出). 链点由 `chainA` 现造, 它们的自互模拟逐点归纳 (`selfC`).

```agda
H0 : ∀ {φ j} → (Ordˢ j → Run φ) → (T → T) → Set
H0 {j = j} H lab = ∀ η (x : Ordˢ j) → LabL x η → x ≅ˢ x → L0 (H x) (lab η) × (H x ≈ᴿ H x)

limᵢ0 : ∀ {φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} →
        cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
        (∀ η x → LabL x η → LW (H x) (ps ++ fsT (y ∷ ys) η)) → H0 H (λ η → ps ++ fsT (y ∷ ys) η) →
        L0 (limᵢA 0 ac H) (ps ++ (y ∷ ys))
limᵢ0 {j = zero} {ν = ν} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys [] c₀ refl m)) (proj₂ (outp m))))
  where
  c₀ : cof (y ∷ ys) ≡ cΩ []
  c₀ = trans c (cong cΩ (kdI Iν (sym (kd-≅ ej))))
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c₀)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₂ z≅)
  nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  nfγ m = subst NF₁ (gtW [] ps y ys [] c₀ refl m) (NF₁-fsn nu cω′ m)
  atm : ∀ m → Atomᴸ (chainA ac H ev m) (γW ps (y ∷ ys) [] m)
  atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
  atm (suc m) = proj₂ (h0 _ _ (atm m) (proj₁ (atm m))) ev (ac ev) ev (ac ev) z≅ ,
                proj₁ (h0 _ _ (atm m) (proj₁ (atm m))) ev (ac ev) (nfγ m)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  outp m = proj₁ (h0 _ _ (atm m) (proj₁ (atm m))) ev p (nfγ m)
limᵢ0 {j = suc j′} {ν = []} c Iν ej hW h0 ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0 {j = suc j′} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
  chainL (suc m) = hW _ _ (chainL m) ev (ac ev) Iν ej refl
  selfC : ∀ m → chainA ac H ev m ≅ˢ chainA ac H ev m
  selfC zero    = Ωˢ-refl _
  selfC (suc m) = proj₂ (h0 _ _ (chainL m) (selfC m)) ev (ac ev) ev (ac ev) (≅ᴵ-refl _)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = proj₁ (h0 _ _ (chainL m) (selfC m)) ev p (nf m)
limᵢ0 {j = lim f s} {ν = []} c Iν ej hW h0 ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0 {j = lim f s} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
  chainL (suc m) = hW _ _ (chainL m) ev (ac ev) Iν ej refl
  selfC : ∀ m → chainA ac H ev m ≅ˢ chainA ac H ev m
  selfC zero    = Ωˢ-refl _
  selfC (suc m) = proj₂ (h0 _ _ (chainL m) (selfC m)) ev (ac ev) ev (ac ev) (≅ᴵ-refl _)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = proj₁ (h0 _ _ (chainL m) (selfC m)) ev p (nf m)
```

`limᵢR`: OmegaExpBase 的 `liS`, 前提是分支对相关输入相关.

```agda
limᵢR : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
        {H : Ordˢ j → Run φ} {H′ : Ordˢ j′ → Run ψ} →
        j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → H x ≈ᴿ H′ y) → limᵢA 0 ac H ≈ᴿ limᵢA 0 ac′ H′
limᵢR {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ev p ev′ p′ ei with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → H (tr⁻ˢ e₁ u) ev p ≅ˢ H′ (tr⁻ˢ e₂ v) ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d))) ev p ev′ p′ ei)
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)
... | injᵇ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᵇ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᶜ _  = l≅ (λ m → h _ _ (iter-R _≅ˢ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ e) m) ev p ev′ p′ ei)
```

**待计值链行 (`ĉA`).** 链证书 `K` 由尾巴的标签行携带, 输出在它的链点处带标签.

```agda
module _ {φ c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {ps : T} {y : PT} {ys : T} where
  ĉW : ∀ {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} → cof (y ∷ ys) ≡ cω → (K : CCᴸ c t₀ g) →
       LW O₀ (ps ++ fsn (y ∷ ys) 0) → (∀ k → LW (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) →
       LW (ĉA 0 c t₀ g O₀ O) (ps ++ (y ∷ ys))
  ĉW cw K h₀ hk {w = w} ev p Iw ei ki =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) cw)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw 0)) (h₀ ev p Iw ei ki))
       (λ k → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw (suc k))) (hk k ev p Iw ei ki))

  ĉ0 : ∀ {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} → cof (y ∷ ys) ≡ cω → (K : CCᴸ c t₀ g) →
       L0 O₀ (ps ++ fsn (y ∷ ys) 0) → (∀ k → L0 (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) →
       L0 (ĉA 0 c t₀ g O₀ O) (ps ++ (y ∷ ys))
  ĉ0 cw K h₀ hk ev p nu =
    ĉᴸ-mk nu cω′ K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys cw 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys cw (suc k))) (proj₂ (Rk k)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) cw)
    R₀ = h₀ ev p (subst NF₁ (ωW [] ps y ys cw 0) (NF₁-fsn nu cω′ 0))
    Rk = λ k → hk k ev p (subst NF₁ (ωW [] ps y ys cw (suc k)) (NF₁-fsn nu cω′ (suc k)))

ĉR : ∀ {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
     {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {O₀′ : Run ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
     c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
     O₀ ≈ᴿ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≈ᴿ O′ η′ e′) → ĉA 0 c t₀ g O₀ O ≈ᴿ ĉA 0 c′ t₀′ g′ O₀′ O′
ĉR ec dt dg h₀ h ev p ev′ p′ ei = ĉ≅ ec dt dg (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)
```

**闭包行 (`ŝA`, 尾巴里第 $\ge1$ 层的闭包).** 地板字段一般化为 "下标 $w'$ 出现在每个 `ps ++ fsT (y ∷ ys) θ` 里" (`Ob`), 同时覆盖 `PreS₊` 的 `OccΣ ps` 与 §9 弹栈的地板见证. `domP` 是 OmegaExpBase `domS` 的这一推广.

```agda
Ob : T → T → PT → T → Set
Ob w ps y ys = ∀ θ → Occ w (ps ++ fsT (y ∷ ys) θ)

domP : ∀ {c w Y} ps′ (hY : HS Y) (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → Occ w ps′ → Lab Y (ψ₀ᵗ ps′) → NF₁ (ψ₀ᵗ ps′) →
       c ⊑ᴵ toLevel Y hY
domP ps′ hY (W , hW , lW , nW) bw o lY nb =
  ⊑ᴵ-trans bw (s⊑′ (toLevel-≺ hW hY (Lab-oc lY nb lW nW (occ< nb (c∷ c[]) (od o) (Lab→Ctbl lW nW)))))

module _ {φ c w′} {ps : T} {y : PT} {ys : T} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ}
         (cs : cof (y ∷ ys) ≡ cΩ []) (Iw′ : Idx w′) (bw : c ⊑ᴵ suc (lvI Iw′)) (ob : Ob w′ ps y ys) where
  ŝW : LW T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
       (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) → LW (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
       LW (ŝA 0 c T₀ G) (ps ++ (y ∷ ys))
  ŝW h₀ hg {w = []} ev p Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
  ŝW h₀ hg {w = x ∷ xs} ev p Iw ei ki =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) cs) (H1-pen x xs))) Iw′ bw
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys cs θ)) (od (ob θ)))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs (natT 1))) (h₀ ev p Iw ei ki))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs θ)) (hg θ Y hY lY nθ lt e ev p Iw ei ki))

  ŝ0 : L0 T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
       (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) → L0 (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
       L0 (ŝA 0 c T₀ G) (ps ++ (y ∷ ys))
  ŝ0 h₀ hg ev p nu =
    ĉᴸ-mk nu cω′ K (proj₁ R₀) (subst (Lab _) (sym (gtW [] ps y ys [] cs refl 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (gtW [] ps y ys [] cs refl (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) cs)
    nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    nfγ m = subst NF₁ (gtW [] ps y ys [] cs refl m) (NF₁-fsn nu cω′ m)
    R₀ = h₀ ev p (nfγ 0)
    Rg : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : c ⊑ᴵ toLevel Y hY) →
         Lab₀ (G (toLevel Y hY) e ev p) (γW ps (y ∷ ys) [] (suc (suc m)))
    Rg m Y hY lY e = hg _ Y hY lY (nfγ m) (1<γ ps y ys cs m) e ev p (nfγ (suc m))
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ R₀) (proj₂ R₀)
            (domP _ _ Iw′ bw (ob (natT 1)) (proj₂ R₀) (nfγ 0))
            (λ m Y hY lY e → proj₁ (Rg m Y hY lY e)) (λ m Y hY lY e → proj₂ (Rg m Y hY lY e))
            (λ m Y hY lY e → domP _ _ Iw′ bw (ob (γW ps (y ∷ ys) [] (suc m))) (proj₂ (Rg m Y hY lY e)) (nfγ (suc m)))

ŝR : ∀ {φ ψ c c′} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {T₀′ : Run ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
     c ≅ᴵ c′ → T₀ ≈ᴿ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → G η e ≈ᴿ G′ η′ e′) → ŝA 0 c T₀ G ≈ᴿ ŝA 0 c′ T₀′ G′
ŝR ec h₀ h ev p ev′ p′ ei = ŝ≅ (kd-≅ ei) ec (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)
```

**弹栈行 (`cloA`).** 地板见证 `FW`: 每个地板项要么平凡 ($\cong0$), 要么被某个出现在一切点标签里的带 `Idx` 的下标支配 (`≺ ⊎ ≅`). 界的来源 `src` 决定 `gŝ` 行的地板下标: 最大者是目标时取目标自己的下标 (出现于首项, `oh`), 是地板项时取它的见证 (`od`). 支配 `domC`: 最大者是目标 $0$ 时界为 $1$ (`one⊑lab`), 否则由见证 (`domP`).

```agda
FW : Flr → T → PT → T → Set
FW φ ps y ys = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Ob w ps y ys

≺0 : ∀ {a b} → a ≺ᴵ b → b ≅ᴵ zero → ⊥
≺0 (via e ()) z≅

sB : ∀ {a b} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → suc a ⊑ᴵ suc b
sB (inj₁ (via e r)) = s⊑ e (suc r)
sB (inj₂ e)         = s⊑ e zero

evη : ∀ {i ℓ} (φ : Flr) (B : Top i ℓ (φ ⊔ fk zero)) η (e : suc (Mx B) ⊑ᴵ η) → Ev (Mlev (Fc B) (suc η) (FB B e)) (φ ⊔ fk η)
evη φ B η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)

module _ {φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where

  pickW : ∀ {i M w} (Iw : Idx w) → i ≅ᴵ lvI Iw → (M ≡ i) ⊎ ((i ≺ᴵ M) × Σ Ordᴵ λ K → InF K (φ ⊔ fk zero) × (M ≡ K)) →
          Σ T λ w′ → Σ (Idx w′) λ Iw′ → (suc M ⊑ᴵ suc (lvI Iw′)) × (∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ []))
  pickW {w = w} Iw ei (inj₁ refl) = w , Iw , sB (inj₂ ei) , (λ θ → oh)
  pickW Iw ei (inj₂ (s , K , k , refl)) with fw k
  ... | inj₁ k0 = ⊥-elim (≺0 s k0)
  ... | inj₂ (w′ , Iw′ , kw , ob′) = w′ , Iw′ , sB kw , (λ θ → od (ob′ θ))

  domC : ∀ {M Y} (hY : HS Y) → (M ≡ zero) ⊎ ((zero ≺ᴵ M) × Σ Ordᴵ λ K → InF K (φ ⊔ fk zero) × (M ≡ K)) →
         ∀ θ → Lab Y (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → suc M ⊑ᴵ toLevel Y hY
  domC hY (inj₁ refl) θ lY nf = one⊑lab hY lY nf []<
  domC hY (inj₂ (s , K , k , refl)) θ lY nf with fw k
  ... | inj₁ k0 = ⊥-elim (≺0 s k0)
  ... | inj₂ (w′ , Iw′ , kw , ob′) = domP _ hY Iw′ (sB kw) (ob′ θ) lY nf

  cloW : LW t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → LW (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         LW (cloA 0 t g) (ps ++ (y ∷ ys))
  cloW h₀ hg {w = []} ev p Iw ei ki = ⊥-elim (ne-w Iw ei ki refl)
  cloW h₀ hg {w = x ∷ xs} ev p Iw ei ki =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) cs) (H1-pen x xs)))
       (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk)))
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys cs θ)) (proj₂ (proj₂ (proj₂ Pk)) θ))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs (natT 1))) (h₀ ev p Iw ei ki))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs θ))
            (hg θ Y hY lY nθ lt (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) Iw ei ki))
    where
    B = bound (φ ⊔ fk zero) ev p
    Pk = pickW Iw ei (src B)

  clo0 : L0 t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → L0 (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         L0 (cloA 0 t g) (ps ++ (y ∷ ys))
  clo0 h₀ hg ev p nu =
    ĉᴸ-mk nu cω′ K (proj₁ R₀) (subst (Lab _) (sym (gtW [] ps y ys [] cs refl 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (gtW [] ps y ys [] cs refl (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    B = bound (φ ⊔ fk zero) ev p
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) cs)
    nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    nfγ m = subst NF₁ (gtW [] ps y ys [] cs refl m) (NF₁-fsn nu cω′ m)
    R₀ = h₀ ev p (nfγ 0)
    Rg : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : suc (Mx B) ⊑ᴵ toLevel Y hY) →
         Lab₀ (g (toLevel Y hY) (evη φ B (toLevel Y hY) e) (lim 0 (iF B))) (γW ps (y ∷ ys) [] (suc (suc m)))
    Rg m Y hY lY e = hg _ Y hY lY (nfγ m) (1<γ ps y ys cs m) (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) (nfγ (suc m))
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ R₀) (proj₂ R₀)
            (domC _ (src B) (natT 1) (proj₂ R₀) (nfγ 0))
            (λ m Y hY lY e → proj₁ (Rg m Y hY lY e)) (λ m Y hY lY e → proj₂ (Rg m Y hY lY e))
            (λ m Y hY lY e → domC _ (src B) (γW ps (y ∷ ys) [] (suc m)) (proj₂ (Rg m Y hY lY e)) (nfγ (suc m)))
```

**界的互模拟.** 两个地板 "非平凡部分逐项 $\cong$" (`_∼ᶠ_`: 平凡项可以与空位对应) 且目标 $\cong$ 时, 两次 `bound` 的最大者 $\cong$. 证明对 `accT` 逐项: 比较结果由 `clash₁`/`clash₂` 保持一致, 平凡项永不成为最大者 (`≺0`).

```agda
infix 4 _∼ᶠ_
data _∼ᶠ_ : Flr → Flr → Set where
  fz∼ : fz ∼ᶠ fz
  fk∼ : ∀ {K K′} → K ≅ᴵ K′ → fk K ∼ᶠ fk K′
  zk∼ : ∀ {K′} → K′ ≅ᴵ zero → fz ∼ᶠ fk K′
  kz∼ : ∀ {K} → K ≅ᴵ zero → fk K ∼ᶠ fz
  ⊔∼  : ∀ {a a′ b b′} → a ∼ᶠ a′ → b ∼ᶠ b′ → a ⊔ b ∼ᶠ a′ ⊔ b′

∼ᶠ-refl : ∀ φ → φ ∼ᶠ φ
∼ᶠ-refl fz      = fz∼
∼ᶠ-refl (fk K)  = fk∼ (≅ᴵ-refl K)
∼ᶠ-refl (a ⊔ b) = ⊔∼ (∼ᶠ-refl a) (∼ᶠ-refl b)

insM : ∀ {i i′ ℓ ℓ′ φ φ′ K K′} (t : Top i ℓ φ) (t′ : Top i′ ℓ′ φ′) (ek : Simᴵ (suc K) ℓ) (ek′ : Simᴵ (suc K′) ℓ′) →
       Mx t ≅ᴵ Mx t′ → K ≅ᴵ K′ → Mx (ins t ek) ≅ᴵ Mx (ins t′ ek′)
insM t t′ ek ek′ eM eK with <ᴵ-dec (ek zero) (mx t) | <ᴵ-dec (ek′ zero) (mx t′)
... | injᵃ (via _ _) | injᵃ (via _ _) = eM
... | injᵃ (via _ _) | injᶜ _ = eM
... | injᶜ _ | injᵃ (via _ _) = eM
... | injᶜ _ | injᶜ _ = eM
... | injᵇ (via _ _) | injᵇ (via _ _) = eK
... | injᵃ r | injᵇ s = ⊥-elim (clash₁ eK eM r s)
... | injᶜ c | injᵇ s = ⊥-elim (clash₂ (≅ᴵ-sym eM) (≅ᴵ-sym eK) s (≅ᴵ-sym c))
... | injᵇ s | injᵃ r = ⊥-elim (clash₁ (≅ᴵ-sym eK) (≅ᴵ-sym eM) r s)
... | injᵇ s | injᶜ c = ⊥-elim (clash₂ eM eK s (≅ᴵ-sym c))

insT : ∀ {i ℓ φ K} (t : Top i ℓ φ) (ek : Simᴵ (suc K) ℓ) → K ≅ᴵ zero → Mx (ins t ek) ≡ Mx t
insT t ek k0 with <ᴵ-dec (ek zero) (mx t)
... | injᵃ (via _ _) = refl
... | injᶜ _ = refl
... | injᵇ s = ⊥-elim (≺0 s k0)

accM : ∀ {i i′ ℓ ℓ′ φ₁ φ₁′ φ₂ φ₂′} (t : Top i ℓ φ₁) (t′ : Top i′ ℓ′ φ₁′) → φ₂ ∼ᶠ φ₂′ →
       (ev : Ev ℓ φ₂) (ev′ : Ev ℓ′ φ₂′) → Mx t ≅ᴵ Mx t′ → Mx (accT t φ₂ ev) ≅ᴵ Mx (accT t′ φ₂′ ev′)
accM t t′ fz∼       ev ev′ eM = eM
accM t t′ (fk∼ eK)  ev ev′ eM = insM t t′ ev ev′ eM eK
accM t t′ (zk∼ k0)  ev ev′ eM = subst (λ M → Mx t ≅ᴵ M) (sym (insT t′ ev′ k0)) eM
accM t t′ (kz∼ k0)  ev ev′ eM = subst (λ M → M ≅ᴵ Mx t′) (sym (insT t ev k0)) eM
accM t t′ (⊔∼ a b) (x , y) (x′ , y′) eM = accM (accT t _ x) (accT t′ _ x′) b y y′ (accM t t′ a x x′ eM)

bound-≅ : ∀ {i i′ ℓ ℓ′ φ φ′} → φ ∼ᶠ φ′ → (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ φ′) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ →
          Mx (bound φ ev p) ≅ᴵ Mx (bound φ′ ev′ p′)
bound-≅ s ev p ev′ p′ ei = accM (top₀ p) (top₀ p′) s ev ev′ ei

cloR : ∀ {φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
       {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
       t ≈ᴿ t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ᴿ g′ η′) → cloA 0 t g ≈ᴿ cloA 0 t′ g′
cloR {φ} {φ′} s ht hg ev p ev′ p′ ei =
  ŝ≅ (kd-≅ ei) (s≅ (bound-≅ (⊔∼ s (fk∼ z≅)) ev p ev′ p′ ei)) (ht ev p ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ (lim 0 (iF (bound (φ ⊔ fk zero) ev p))) _ (lim 0 (iF (bound (φ′ ⊔ fk zero) ev′ p′))) ei)
```

## §8 深度 0 的折叠定理

**互模拟.** `fold-≅0`: 底互模拟、尾巴互模拟, 则深度 0 的折叠互模拟 (OmegaExpBase `ψˢ-≅` 的移植, 对 `≅ˢ` 推导递归, 各行交给 §7 的 `…R`). 深度 0 的尾巴里没有弹栈, 地板不影响值, 所以对任意两个地板成立.

```agda
wkR : ∀ {φ φ′ ψ ψ′} {R : Run φ} {R′ : Run φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
      R ≈ᴿ R′ → wk 0 le R ≈ᴿ wk 0 le′ R′
wkR le le′ h ev p ev′ p′ ei = h (le ev) p (le′ ev′) p′ ei

fold-≅0 : ∀ {fl fl′ φ φ′ k₁ k₂} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L}
          {P : Run fl} {P′ : Run fl′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
          P ≈ᴿ P′ → a ≅ˢ b → fold 0 φ cv P a ≈ᴿ fold 0 φ′ cv′ P′ b
fold-≅0 H z≅ ev p ev′ p′ ei = H (proj₁ ev) p (proj₁ ev′) p′ ei
fold-≅0 H (s≅ e) = sucR (fold-≅0 H e)
fold-≅0 H (l≅ h) = limR (λ n → fold-≅0 H (h n))
fold-≅0 {k₁ = suc k′} {cv = cv} {cv′ = cv′} H (upˡ {r = zero} e) =
  wkR (λ ev → proj₁ ev , toFlo k′ (cv (proj₂ ev))) (λ ev → ev) (fold-≅0 H e)
fold-≅0 H (upˡ {r = self n} e) = fold-≅0 H e
fold-≅0 {k₂ = suc k′} {cv = cv} {cv′ = cv′} H (upʳ {r = zero} e) =
  wkR (λ ev → ev) (λ ev → proj₁ ev , toFlo k′ (cv′ (proj₂ ev))) (fold-≅0 H e)
fold-≅0 H (upʳ {r = self n} e) = fold-≅0 H e
fold-≅0 {k₁ = zero} {k₂ = zero} H (ŝ≅ k ec et eg) =
  ĉR ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (fold-≅0 H et) (λ η e η′ e′ eη → fold-≅0 H (eg η e η′ e′ eη))
fold-≅0 {k₁ = zero} {k₂ = suc _}   H (ŝ≅ k ec et eg) = ⊥-elim (tf k)
fold-≅0 {k₁ = zero} {k₂ = lim _ _} H (ŝ≅ k ec et eg) = ⊥-elim (tf k)
fold-≅0 {k₁ = suc _}   {k₂ = zero} H (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0 {k₁ = lim _ _} {k₂ = zero} H (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
fold-≅0 {k₁ = suc _}   {k₂ = suc _}   H (ŝ≅ k ec et eg) = ŝR ec (fold-≅0 H et) (λ η e η′ e′ eη → fold-≅0 H (eg η e η′ e′ eη))
fold-≅0 {k₁ = suc _}   {k₂ = lim _ _} H (ŝ≅ k ec et eg) = ŝR ec (fold-≅0 H et) (λ η e η′ e′ eη → fold-≅0 H (eg η e η′ e′ eη))
fold-≅0 {k₁ = lim _ _} {k₂ = suc _}   H (ŝ≅ k ec et eg) = ŝR ec (fold-≅0 H et) (λ η e η′ e′ eη → fold-≅0 H (eg η e η′ e′ eη))
fold-≅0 {k₁ = lim _ _} {k₂ = lim _ _} H (ŝ≅ k ec et eg) = ŝR ec (fold-≅0 H et) (λ η e η′ e′ eη → fold-≅0 H (eg η e η′ e′ eη))
fold-≅0 H (ĉ≅ ec dt dg eo eO) = ĉR ec dt dg (fold-≅0 H eo) (λ η e η′ e′ eη → fold-≅0 H (eO η e η′ e′ eη))
fold-≅0 H (lᵢ≅ {p = q} e h) = limᵢR e (λ x y d → fold-≅0 H (h x y (≅→Rˢ (<→◃ q) d)))
```

**标签 (目标非零).** `tlW`: 对尾巴的 `LabL` 推导递归 (OmegaExpBase `PreS₊`/`PreAS`), 每行交给 §7 的 `…W`. 不需要尾巴的自互模拟.

```agda
zW : ∀ {φ fl} {P : Run fl} {π} → LW P π → LW (wk 0 (proj₁ {B = λ _ → Ev _ φ}) P) (π ++ [])
zW {π = π} h ev p Iw ei ki = subst (λ u → LabL₊ _ Ll _ (ψᵗ _ u ∷ [])) (sym (++-identityʳ π)) (h (proj₁ ev) p Iw ei ki)

module TlW {fl} {P : Run fl} {π : T} (hP : LW P π) where
  tlWA : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → Lab0ᴸ t y → LW (fold 0 φ cv P t) (π ++ y)
  tlWV : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL t y → LW (fold 0 φ cv P t) (π ++ y)
  tlW₊ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL₊ k Ll t y → LW (fold 0 φ cv P t) (π ++ y)

  tlWA {y = []} (lz c) = zW hP
  tlWA {y = y ∷ ys} (lz c) = ⊥-elim (cof-ne y ys c)
  tlWA {y = []} (ls () l)
  tlWA {y = y ∷ ys} (ls c l) = sucW c (tlWA l)
  tlWA {y = []} (ll () h)
  tlWA {y = y ∷ ys} (ll c h) = limW c (λ n → tlWA (h n))
  tlWA {y = []} (lŝ₀ () K h₀ hk)
  tlWA {φ = φ} {cv = cv} {y = y ∷ ys} (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) =
    ĉW {O₀ = fold 0 φ cv P t₀} {O = λ η e → fold 0 φ cv P (g η e)} c K (tlWA h₀) (λ k → tlWA (hk k))
  tlWA {y = []} (lĉ () K h₀ hk)
  tlWA {φ = φ} {cv = cv} {y = y ∷ ys} (lĉ {o₀ = o₀} {o = o} c K h₀ hk) =
    ĉW {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} c K (tlWA h₀) (λ k → tlWA (hk k))

  tlWV {k = zero}    at = tlWA (atomL at)
  tlWV {k = suc _}   h  = tlW₊ h
  tlWV {k = lim _ _} h  = tlW₊ h

  tlW₊ {y = []} (gz c) = zW hP
  tlW₊ {y = y ∷ ys} (gz c) = ⊥-elim (cof-ne y ys c)
  tlW₊ {y = []} (gs () l)
  tlW₊ {y = y ∷ ys} (gs c l) = sucW c (tlW₊ l)
  tlW₊ {y = []} (gl () h)
  tlW₊ {y = y ∷ ys} (gl c h) = limW c (λ n → tlW₊ (h n))
  tlW₊ {k = suc k′} {φ = φ} {cv = cv} (gu {r = zero} h) = λ ev p → tlWV {φ = flo k′} {cv = cvFlo k′} h (proj₁ ev , toFlo k′ (cv (proj₂ ev))) p
  tlW₊ {cv = cv} (gu {r = self n} h) = tlWV {cv = λ e q → cv e (lim n q)} h
  tlW₊ {y = []} (gi () I ej h)
  tlW₊ {y = y ∷ ys} (gi {q = q} c I ej h) = limᵢW c I ej (λ η x l → tlW₊ (h η x (→Ll (<→◃ q) l)))
  tlW₊ {y = []} (gĉ () K h₀ hk)
  tlW₊ {φ = φ} {cv = cv} {y = y ∷ ys} (gĉ {o₀ = o₀} {o = o} c K h₀ hk) =
    ĉW {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} c K (tlW₊ h₀) (λ k → tlW₊ (hk k))
  tlW₊ {k = zero} (gŝ () c Iw bw ob h₀ hg)
  tlW₊ {k = suc _} {y = []} (gŝ kk () Iw bw ob h₀ hg)
  tlW₊ {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) =
    ŝW {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} c Iw bw (λ θ → OccΣ π (ob θ)) (tlW₊ h₀) (λ θ Y hY lY nθ lt e → tlW₊ (hg θ Y hY lY nθ lt e))
  tlW₊ {k = lim _ _} {y = []} (gŝ kk () Iw bw ob h₀ hg)
  tlW₊ {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) =
    ŝW {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} c Iw bw (λ θ → OccΣ π (ob θ)) (tlW₊ h₀) (λ θ Y hY lY nθ lt e → tlW₊ (hg θ Y hY lY nθ lt e))
```

**标签 (目标 0).** `tl0`: OmegaExpBase `Pre0S₊`/`Pre0AS` 的移植, 要尾巴的自互模拟 (链原子). 节点层 $0$ 的链在 §7 `limᵢ0` 里由组成部分的互模拟 (`fold-≅0`) 给原子的 $\cong^\mathsf s$.

```agda
z0 : ∀ {φ fl} {P : Run fl} {π} → L0 P π → L0 (wk 0 (proj₁ {B = λ _ → Ev _ φ}) P) (π ++ [])
z0 {π = π} h ev p nf =
  subst (λ u → Lab₀ _ (ψ₀ᵗ u)) (sym (++-identityʳ π)) (h (proj₁ ev) p (subst (λ u → NF₁ (ψ₀ᵗ u)) (++-identityʳ π) nf))

module Tl0 {fl} {P : Run fl} {π : T} (hP : LW P π) (h0P : L0 P π) (hR : P ≈ᴿ P) where
  open TlW hP
  tl0A : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → Lab0ᴸ t y → t ≅ˢ t → L0 (fold 0 φ cv P t) (π ++ y)
  tl0V : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL t y → t ≅ˢ t → L0 (fold 0 φ cv P t) (π ++ y)
  tl0₊ : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → LabL₊ k Ll t y → t ≅ˢ t → L0 (fold 0 φ cv P t) (π ++ y)

  tl0A {φ = φ} {y = []} (lz c) ex = z0 {φ = φ} {P = P} h0P
  tl0A {y = y ∷ ys} (lz c) ex = ⊥-elim (cof-ne y ys c)
  tl0A {y = []} (ls () l) ex
  tl0A {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} (ls c l) ex = suc0 {R = fold 0 φ cv P a} c (tl0A {cv = cv} l (s-invˢ ex))
  tl0A {y = []} (ll () h) ex
  tl0A {φ = φ} {cv = cv} {t = Ord₊ˢ.lim F} {y = y ∷ ys} (ll c h) ex =
    lim0 {F = λ n → fold 0 φ cv P (F n)} c (λ n → tl0A {cv = cv} (h n) (l-invˢ ex n))
  tl0A {y = []} (lŝ₀ () K h₀ hk) ex
  tl0A {φ = φ} {cv = cv} {y = y ∷ ys} (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) ex =
    ĉ0 {O₀ = fold 0 φ cv P t₀} {O = λ η e → fold 0 φ cv P (g η e)} c K (tl0A h₀ (ŝ-refl₀ ex))
       (λ k → tl0A (hk k) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)))
  tl0A {y = []} (lĉ () K h₀ hk) ex
  tl0A {φ = φ} {cv = cv} {y = y ∷ ys} (lĉ {o₀ = o₀} {o = o} c K h₀ hk) ex =
    ĉ0 {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} c K (tl0A h₀ (ĉ-refl₀ ex))
       (λ k → tl0A (hk k) (ĉ-reflg ex _ _))

  tl0V {k = zero}    at ex = tl0A (atomL at) ex
  tl0V {k = suc _}   h  ex = tl0₊ h ex
  tl0V {k = lim _ _} h  ex = tl0₊ h ex

  tl0₊ {φ = φ} {y = []} (gz c) ex = z0 {φ = φ} {P = P} h0P
  tl0₊ {y = y ∷ ys} (gz c) ex = ⊥-elim (cof-ne y ys c)
  tl0₊ {y = []} (gs () l) ex
  tl0₊ {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} (gs c l) ex = suc0 {R = fold 0 φ cv P a} c (tl0₊ {cv = cv} l (s-invˢ ex))
  tl0₊ {y = []} (gl () h) ex
  tl0₊ {φ = φ} {cv = cv} {t = Ord₊ˢ.lim F} {y = y ∷ ys} (gl c h) ex =
    lim0 {F = λ n → fold 0 φ cv P (F n)} c (λ n → tl0₊ {cv = cv} (h n) (l-invˢ ex n))
  tl0₊ {k = suc k′} {φ = φ} {cv = cv} (gu {r = zero} h) ex =
    λ ev p → tl0V {φ = flo k′} {cv = cvFlo k′} h (u-reflˢ zero ex) (proj₁ ev , toFlo k′ (cv (proj₂ ev))) p
  tl0₊ {cv = cv} (gu {r = self n} h) ex = tl0V {cv = λ e q → cv e (lim n q)} h (u-reflˢ (self n) ex)
  tl0₊ {y = []} (gi () I ej h) ex
  tl0₊ {φ = φ} {cv = cv} {y = y ∷ ys} (gi {q = q} {f = f} c I ej h) ex =
    limᵢ0 {ac = λ ev → cv (proj₂ ev) q} {H = λ x → fold 0 φ cv P (f (intoˢ (<→◃ q) x))} c I ej
          (λ η x l → tlW₊ (h η x (→Ll (<→◃ q) l)))
          (λ η x l xx → tl0₊ (h η x (→Ll (<→◃ q) l)) (i-respˢ ex xx) , fold-≅0 hR (i-respˢ ex xx))
  tl0₊ {y = []} (gĉ () K h₀ hk) ex
  tl0₊ {φ = φ} {cv = cv} {y = y ∷ ys} (gĉ {o₀ = o₀} {o = o} c K h₀ hk) ex =
    ĉ0 {O₀ = fold 0 φ cv P o₀} {O = λ η e → fold 0 φ cv P (o η e)} c K (tl0₊ h₀ (ĉ-refl₀ ex))
       (λ k → tl0₊ (hk k) (ĉ-reflg ex _ _))
  tl0₊ {k = zero} (gŝ () c Iw bw ob h₀ hg) ex
  tl0₊ {k = suc _} {y = []} (gŝ kk () Iw bw ob h₀ hg) ex
  tl0₊ {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex =
    ŝ0 {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} c Iw bw (λ θ → OccΣ π (ob θ)) (tl0₊ h₀ (ŝ-refl₀ ex))
       (λ θ Y hY lY nθ lt e → tl0₊ (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)))
  tl0₊ {k = lim _ _} {y = []} (gŝ kk () Iw bw ob h₀ hg) ex
  tl0₊ {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} (gŝ {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex =
    ŝ0 {T₀ = fold 0 φ cv P t₀} {G = λ η e → fold 0 φ cv P (g η e)} c Iw bw (λ θ → OccΣ π (ob θ)) (tl0₊ h₀ (ŝ-refl₀ ex))
       (λ θ Y hY lY nθ lt e → tl0₊ (hg θ Y hY lY nθ lt e) (ŝ-reflg ex _ _ _ _ (≅ᴵ-refl _)))

tlGR : ∀ {fl} {P : Run fl} {π} → GR P π → ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} →
       LabL t y → t ≅ˢ t → GR (fold 0 φ cv P t) (π ++ y)
tlGR (gr hW h0 hR) l ex = gr (TlW.tlWV hW l) (Tl0.tl0V hW h0 hR l ex) (fold-≅0 hR ex)
```

**读法.** `tlGR` 是 TopDown `goodTl` 在深度 0 的全部内容, 对**一切层号**的尾巴成立 (地板在深度 0 不影响值: 尾巴里没有弹栈, 弹栈只在底 $P$ 里). 停机一次通过: 递归都在尾巴推导的子项上, 节点层的链在 §7 的 `limᵢ0` 里由前提给出.

## §9 地板标签与 $\Omega_\Omega$ 的闭包定理 (深度 0)

`FlrLab φ ps`: 每个地板项平凡, 或被某个出现在 `ps` 里的带 `Idx` 下标支配. 这是 `GA` 的静态部分: 它只在该前缀成为弹栈的底时被读到 (§7 的 `FW`). `GA0` = 静态部分 + 深度 0 的标签与互模拟.

```agda
FlrLab : Flr → T → Set
FlrLab φ ps = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Occ w ps

OccPre : ∀ {w ps} b → Occ w ps → Occ w (ps ++ b)
OccPre b oh     = oh
OccPre b (od o) = od o
OccPre b (os o) = os o
OccPre b (oτ t) = oτ t
OccPre b (ot o) = ot (OccPre b o)

FlrLab-mono : ∀ {φ ps qs} → (∀ {w} → Occ w ps → Occ w qs) → FlrLab φ ps → FlrLab φ qs
FlrLab-mono f F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , f o)

FlrLab-⊔ : ∀ {fl φ π x} → FlrLab fl π → FlrLab φ x → FlrLab (fl ⊔ φ) (π ++ x)
FlrLab-⊔ {x = x} F G (inl k) = FlrLab-mono (OccPre x) F k
FlrLab-⊔ {π = π} F G (inr k) = FlrLab-mono (OccΣ π) G k

FlrLab-z : ∀ {ps} → FlrLab (fk zero) ps
FlrLab-z ink = inj₁ z≅

FlrLab-fz : ∀ {ps} → FlrLab fz ps
FlrLab-fz ()

FW-pop : ∀ {fl π} → FlrLab fl π → FW (fl ⊔ fk zero) π ΩΩ []
FW-pop F (inr ink) = inj₁ z≅
FW-pop F (inl k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)

GA0 : ∀ {fl} → Run fl → T → Set
GA0 {fl} P π = FlrLab fl π × GR P π
```

**$\Omega_\Omega$ 的闭包定理, 深度 0 (`goodΩ̂0`).** 第 0 点是 $P+\Omega_1$, 分支是 $P+\Omega_\eta$, 都是 §8 `tlGR` 对 `LabL-Ω` 的实例; 地板见证由 `FW-pop`; 互模拟由 `cloR` 与 `fold-≅0`. 这是 OmegaExpBase `GoodΩ` 与 NonTightBase `GoodΩᶠ` 的合并, 对任意地板 (界非紧时由见证支配).

```agda
goodΩ̂0 : ∀ {fl} {P : Run fl} {π} → GA0 P π → GR (Ω̂A 0 P) (π ++ ΩΩ ∷ [])
goodΩ̂0 {fl} {P} {π} (F , GP) =
  gr (cloW {t = T₁} {g = Gη} (FW-pop F) refl (gW Lt) (λ θ Y hY lY nθ lt → gW (Lg θ Y hY lY nθ)))
     (clo0 {t = T₁} {g = Gη} (FW-pop F) refl (g0 Lt) (λ θ Y hY lY nθ lt → g0 (Lg θ Y hY lY nθ)))
     (cloR {t = T₁} {g = Gη} {t′ = T₁} {g′ = Gη} (∼ᶠ-refl fl) (fold-≅0 (gR GP) (Ωˢ-refl (suc zero)))
           (λ η η′ eη → fold-≅0 (gR GP) (Ωˢ-≅ eη)))
  where
  T₁ : Run (fl ⊔ fk zero)
  T₁ = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))
  Gη : (η : Ordᴵ) → Run (fl ⊔ fk η)
  Gη η = fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)
  Lt : GR T₁ (π ++ Ωt (natT 1))
  Lt = tlGR GP (LabL-Ω one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _)) (Ωˢ-refl (suc zero))
  Lg : ∀ θ Y (hY : HS Y) → Lab Y θ → NF₁ θ → GR (Gη (toLevel Y hY)) (π ++ Ωt θ)
  Lg θ Y hY lY nθ = tlGR GP (LabL-Ω Y hY lY nθ (≅ᴵ-refl _)) (Ωˢ-refl _)

GA0-Ω̂ : ∀ {fl} {P : Run fl} {π} → GA0 P π → GA0 (Ω̂A 0 P) (π ++ ΩΩ ∷ [])
GA0-Ω̂ (F , GP) = FlrLab-⊔ F FlrLab-z , goodΩ̂0 (F , GP)
```

**读法.** 地板非平凡时 (底里有第 $\ge2$ 层的帧) 界是 `suc K`, `pickW`/`domC` 取 `FlrLab` 给的见证下标 (它出现在前缀里, 于是出现在每个链点标签里, `occ<` + `Lab-oc` 给支配); 地板全平凡时界字面是 `suc i`, 与 OmegaExpBase 的紧界同. 两种情形同一个子句.

## §10–§11 深度 1

深度 1 (好帧、层对齐的互模拟 `AlignD`/`lowA`/`fold-≅1`, 地板平凡的尾巴的深度 1 折叠定理 `FullA`/`Full₁`) 在 [Uniform2Depth1](Uniform2Depth1.lagda.md), 节号沿用.

## §12 结论与边界

**取舍 (任务 1).** 两种地板设计的结合: 地板是**类型里的语法和** (TopDown), 证据是**字面的** `Simᴵ` (NonTight). 理由: (i) TopDown 的 `Restrˢ` 证据带任意回搬函数, 好性不可能对一切证据成立, 而字面 `Sim` 只搬运证明不搬运树; (ii) 有了字面证据, 自下而上的全部标签证明 (`ψˢ` 的派发用的就是字面 `σ q`) 逐字适用于统一折叠的深度 0 子句; (iii) 弹栈的比较在当前环境层号内做 (交替不变量), 结果用字面的 `Mlev` 嵌套装下目标与全部地板 (`Fc`), 而闭包的界只取字面最大者的后继 `suc (Mx B)` (`bound-≅`: 地板的非平凡部分 $\cong$ 时界 $\cong$, 平凡项不改界). 设计修正 "第一份在旧地板上" **必须**写进 `repA`: 弱化只丢证据不缩类型. `FlrLab` 在 `up (self n)` 下的紧性 (TopDown §11 第 2 条): 极限父层的地板保持父层的 `fk (lim …)`, 本文的定理不经过它 (第 0–2 层); 它属于下面的 (a′). `≈ˢ` (TopDown §11 第 3 条): 必须加回, 链原子 (`Atomᴸ`) 要自互模拟.

**`Expected` 的字段 (任务 2).** TopDown 的记录本身无居留, 所以证明的是调整后的 `Expected′` (Uniform2 §3, `expected′ : Expected′` 闭项, 无参数):

| TopDown 字段 | 调整 | 状态 |
|---|---|---|
| `good∅ᴿ` | `GA0 ∅ᴿ []` (加互模拟与地板标签) | 定理 (Uniform2 `good∅ᴿ`) |
| `good∅`, `good⊕` | 深度 0 与 1 (`GS0`/`GS1`) | 定理 (`good∅0`/`good∅1`/`good⊕0`/`good⊕1`) |
| `goodΩ̂ d` | 深度 0: `GA1 (Ω̂A 0) []` | 定理 (`goodΩ̂₀` = `goodΩ̂0` + `gwΩ̂0` + `selfΩ̂0`) |
| | 深度 1: `GA1 (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])` | 以 `BranchΩ E ζ` 为前提的定理 (Uniform2 `goodΩ̂₁`); 前提即下表的 (a′)(b′) |
| | 深度 $\ge2$ | 未做 (需要深度 $\ge2$ 的行引理提升与深度 1 的一般尾巴定理) |
| `goodTl` | 深度 0: 一切 `LabL` 尾巴 + 自互模拟 + 静态地板标签 | 定理 (`tlGR`, `goodTl0`) |
| | 深度 1: `TlOK` 尾巴 (第 0、1 层任意; 第 2 层的 $\Omega_2$、$\Omega_2+1$) | 定理 (`FullA`, `Full₁`, `FullΩ₂`, `FullΩ₂₊`) |
| | 深度 1 第 $\ge3$ 层; 深度 $\ge2$ | 未做, 精确停点见 Uniform2 §6 |
| `dom` | 字面界下的形式 `dom′` | 定理 (`domSrc`; 弹栈行里的 `pickW`/`domC`) |
| `topO` | $\psi_0(\Omega_{\Omega+1})$ | 未做 (要一切深度) |

**字面与模 $\cong$.** 字面 (`refl`): Uniform2 §5 的树种类检验 (`kind`、`bndOf popᵀ ≡ two`). 模 $\cong$: 一切标签 (Correspond 的 `Lab` 是模 $\cong$ 的), 统一树与自下而上的树经 `Lab-uniq` 计值后 $\cong$ (Uniform2 §5).

**工程注记 (编译失败的写法与原文错误).**

1. 用 `subst (λ u → L0 _ (π ++ u))` 搬运深度 1 的标签: `L0` 是对 `{ℓ}`、证据与目标 `zero` 量化的函数类型, 元变量出现在 `zero` 的位置上, 不是模式:

        error: [UnsolvedConstraints]
          _R_10727 ev p = fold 1 φ cv E (G n) P ev p : Ord₊ˢ zero Uˢ (blocked on _R_10727)

   改为显式给出前缀的搬运 `L0≡π R π` (Uniform2 里 `LW≡π` 同理).
2. `insM` 里写 `... | injᵃ _ | injᵃ _ = eM`: `ins` 在 `injᵃ (via e r)` 上匹配, 抽象掉的 with 函数不归约:

        error: [UnequalTerms]
        Mx t != Mx (ins (top (Mx t) …) ek | injᵃ x)

   改为 `injᵃ (via _ _)`.
3. `limᵢ0 {j = suc j′} {[]} …` 在 `--hidden-argument-puns` 下:

        error: [InvalidPun.Constructor] A pun must not use the constructor []

   改为 `{ν = []}`.
4. 对行引理的隐式前缀族 (`O₀`、`O`、`T₀`、`G`、`H`) 不给出时, 合一器要从 `fold … ev p` 解出族, 报 `[UnsolvedMetaVariables]`; 一律显式给出 (例如 `ĉW {O₀ = fold 0 φ cv P t₀} {O = λ η e → fold 0 φ cv P (g η e)}`).

**边界.** 深度 1 的一般尾巴定理只对地板平凡的尾巴; 第 2 层只做了 $\Omega_2$ 与 $\Omega_2+1$. 第 3 层起需要依目标的地板见证与依目标的层对齐互模拟 (Uniform2 §6, 编译的反例 `¬AlignΩ₃`). 深度 $\ge2$ 的行引理提升 (对 $d$ 归纳) 未写: 深度 1 的证明直接用深度 0 的行引理与 `ψΩ` 的交换 (`cΩΩ`/`penΩ`/`c1Ω`/`cωΩ`), 提升到深度 $d$ 是同样的交换套 $d$ 层, 但只有在 (a′)(b′) 之后才有用.
