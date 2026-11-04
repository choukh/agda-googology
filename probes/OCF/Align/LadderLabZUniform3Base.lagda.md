> **机械克隆, 验收用.** 由 `ScafLadderZUniform3Base` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform3Base` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (三): 极限层的紧地板 `fb`、逐点上确界的界与深度 0 的标签理论

> 接 [OmegaSqA](OmegaSqA.lagda.md) §5–§6. Uniform3 系列: `Uniform3Base` (本文, 定义与深度 0), [Uniform3Walk](Uniform3Walk.lagda.md) (失败路径上的 `refl`), [Uniform3Depth1](Uniform3Depth1.lagda.md)、[Uniform3](Uniform3.lagda.md) (九个标签重证), [Uniform3Rel](Uniform3Rel.lagda.md)、[Uniform3SqABase](Uniform3SqABase.lagda.md)、[Uniform3SqA](Uniform3SqA.lagda.md) (层对齐的标签理论, $\Omega_3$), [Uniform3Hon](Uniform3Hon.lagda.md)、[Uniform3Full](Uniform3Full.lagda.md) (**$\psi_0(\Omega_\Omega^2)$ 的无条件标签**), [Uniform3Plus1](Uniform3Plus1.lagda.md) (消费者).
>
> 结论先说:
>
> 1. **修正只有一处定义: `up (self n)` 的地板.** `fold d φ cv P (up (self n) x)` 现在与 `up zero` 同形: 地板换成目标层的紧地板 `flo (f n)`. `flo` 对极限层取新项 `fb K` ("严格在 $K$ 之下", 证据 `Simᴵ K ℓ`).
> 2. **OmegaSqA 的纸面方案有一个缺口, 这里补上.** 那里说 "弹栈时最大者取 $\max(i+1,K)$". 但极限 $K$ 只有 `Simᴵ K ℓ`, 没有 $K<^\mathsf I\ell$: 判定 $M\prec K$ 还是 $K\sqsubseteq M$ 蕴含 LPO, 比较做不了. 解法是**不比较**: 上确界是逐点的, $\sup(a,\lim h)=\lim_n\sup(a,h\,n)$, 比较只在叶子上发生, 那里两边都是 `Simᴵ` 给出的字面子项, `<ᴵ-dec` 可用 (§3). 字面容器 `Fc` 根本不比较 (两层 `Mlev`, 因为新界已经支配两边). 这也回答了 "字面证据问题有没有更深的原因": 它是有界三歧性只对字面子项成立的直接后果, 不会复现, 只要界的计算保持逐点.
> 3. **`Top` 不再有字面最大者.** `Mx`/`src` 换成界 `Bd` 与泛性质 `ubd`. `gŝ` 行要一个下标支配整个界: 见证都带 `Idx`, 在**记号**上比较 (`pickMax`, `cmpᵀ` + `Ilt`/`Ieq`). 没有 `fb` 时 `Bd` 字面地是原来的 `suc (Mx B)`.
> 4. **深度 0 的全部定理原样成立 (§7–§9).** 只有 `up (self n)` 的四个子句要改写成与 `up zero` 同形; 深度 0 不读地板.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform3Base where

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
open import OCF.Align.Bachmann using (fs-gt; pen→<; gt→≤; clash; gt→<)
open import OCF.Align.Closure using (Pen; fsT₊-pen′; lt→<; eq→≡)
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
```

## §1 改动清单 (相对 Uniform2Base)

1. `Flr` 加一个构造子 `fb K` ("严格在 $K$ 之下"), 证据 `Simᴵ K ℓ` (`fk K` 的证据是 `Simᴵ (suc K) ℓ`, 所以 `fk K` 与 `fb (suc K)` 证据相同).
2. `flo (lim f s) = fb (lim f s)` (原为 `fk (lim f s)`); `toFlo` 改收 `Simᴵ k ℓ`.
3. `fold` 的 `up (self n)` 子句与 `up zero` 同形: 地板换成 `flo (f n)`.
4. `Top` 不再记字面最大者: 界 `Bd` 是地板项与 $i+1$ 的**逐点上确界** (§3), 比较只发生在字面子项上; 字面容器 `Fc` 不作比较 (两层 `Mlev`).

## §2 字面证据与前缀塔

```agda
infixl 5 _⊔_
data Flr : Set where
  fz  : Flr
  fk  : Ordᴵ → Flr
  fb  : Ordᴵ → Flr
  _⊔_ : Flr → Flr → Flr

Ev : Ordᴵ → Flr → Set
Ev ℓ fz      = ⊤
Ev ℓ (fk K)  = Simᴵ (suc K) ℓ
Ev ℓ (fb K)  = Simᴵ K ℓ
Ev ℓ (a ⊔ b) = Ev ℓ a × Ev ℓ b

data InF (K : Ordᴵ) : Flr → Set where
  ink : InF K (fk K)
  inb : InF K (fb K)
  inl : ∀ {a b} → InF K a → InF K (a ⊔ b)
  inr : ∀ {a b} → InF K b → InF K (a ⊔ b)

liftEv : ∀ {ℓ ℓ′} (φ : Flr) → Simᴵ ℓ ℓ′ → Ev ℓ φ → Ev ℓ′ φ
liftEv fz      τ _       = tt
liftEv (fk K)  τ e       = λ q → τ (e q)
liftEv (fb K)  τ e       = λ q → τ (e q)
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

## §3 界: 逐点上确界

$K$ 为极限时 `Simᴵ K ℓ` 不给 $K<^\mathsf I\ell$, 所以 $K$ 与目标不能比较: 判定 $M\prec K$ 或 $K\sqsubseteq M$ 蕴含 LPO. 但上确界**不需要判定**: `lim` 是逐点的, $\sup(a,\lim h)=\lim_n\sup(a,h\,n)$, 比较只发生在叶子上, 那里两边都是 `Simᴵ` 给的字面子项, `<ᴵ-dec` 可用. 这就是字面证据问题在界上的解法. 平局与地板不高于当前值时保留原值, 所以没有 `fb` 时 `Bd` 字面地就是原来的 `suc (Mx B)`.

```agda
⊑-suc : ∀ a → a ⊑ᴵ suc a
⊑-suc a = Sim→⊑ᴵ suc


⊑L : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → f n ⊑ᴵ lim f s
⊑L n = Sim→⊑ᴵ (λ q → lim n q)

FsUB : ∀ {a b c} → a ⊑ᴵ c → b ⊑ᴵ c → ∀ n → Fs a b n ⊑ᴵ c
FsUB ac bc zero    = ac
FsUB ac bc (suc n) = bc

≺0 : ∀ {a b} → a ≺ᴵ b → b ≅ᴵ zero → ⊥
≺0 (via e ()) z≅

Max3 : ∀ y K → Set
Max3 y K = K ≺ᴵ y ⊎ y ≺ᴵ K ⊎ K ≅ᴵ y

maxS : ∀ {y K} → Max3 y K → Ordᴵ
maxS {y} (injᵃ _)    = suc y
maxS {K = K} (injᵇ _) = suc K
maxS {y} (injᶜ _)    = suc y

mutual
  sup₁ : ∀ {ℓ} (a K : Ordᴵ) → Simᴵ a ℓ → Simᴵ (suc K) ℓ → Ordᴵ
  sup₁ zero      K σ ek = suc K
  sup₁ (suc y)   K σ ek = maxS (<ᴵ-dec (ek zero) (σ zero))
  sup₁ (lim g s) K σ ek =
    lim (λ n → sup₁ (g n) K (λ q → σ (lim n q)) ek)
        (λ n → sup₁-lub (g n) K _ ek (⊑ᴵ-trans (s n) (sup₁-up (g (suc n)) K _ ek)) (sup₁-K (g (suc n)) K _ ek))

  sup₁-up : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → a ⊑ᴵ sup₁ a K σ ek
  sup₁-up zero      K σ ek = z⊑
  sup₁-up (suc y)   K σ ek with <ᴵ-dec (ek zero) (σ zero)
  ... | injᵃ _ = ⊑ᴵ-refl
  ... | injᵇ (via e r) = s⊑ e (suc r)
  ... | injᶜ _ = ⊑ᴵ-refl
  sup₁-up (lim g s) K σ ek = l⊑ (λ n → ⊑ᴵ-trans (sup₁-up (g n) K (λ q → σ (lim n q)) ek) (⊑L n))

  sup₁-K : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → suc K ⊑ᴵ sup₁ a K σ ek
  sup₁-K zero      K σ ek = ⊑ᴵ-refl
  sup₁-K (suc y)   K σ ek with <ᴵ-dec (ek zero) (σ zero)
  ... | injᵃ (via e r) = s⊑ e (suc r)
  ... | injᵇ _ = ⊑ᴵ-refl
  ... | injᶜ e = s⊑ e zero
  sup₁-K (lim g s) K σ ek = ⊑ᴵ-trans (sup₁-K (g 0) K (λ q → σ (lim 0 q)) ek) (⊑L 0)

  sup₁-lub : ∀ {ℓ η} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → a ⊑ᴵ η → suc K ⊑ᴵ η → sup₁ a K σ ek ⊑ᴵ η
  sup₁-lub zero      K σ ek h k = k
  sup₁-lub (suc y)   K σ ek h k with <ᴵ-dec (ek zero) (σ zero)
  ... | injᵃ _ = h
  ... | injᵇ _ = k
  ... | injᶜ _ = h
  sup₁-lub (lim g s) K σ ek (l⊑ h) k = l⊑ (λ n → sup₁-lub (g n) K (λ q → σ (lim n q)) ek (h n) k)

mutual
  sup : ∀ {ℓ} (a K : Ordᴵ) → Simᴵ a ℓ → Simᴵ K ℓ → Ordᴵ
  sup a zero      σ σK = a
  sup a (suc K)   σ σK = sup₁ a K σ σK
  sup a (lim h t) σ σK =
    lim (λ n → sup a (h n) σ (λ q → σK (lim n q)))
        (λ n → sup-lub a (h n) σ _ (sup-up a (h (suc n)) σ _) (⊑ᴵ-trans (t n) (sup-K a (h (suc n)) σ _)))

  sup-up : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → a ⊑ᴵ sup a K σ σK
  sup-up a zero      σ σK = ⊑ᴵ-refl
  sup-up a (suc K)   σ σK = sup₁-up a K σ σK
  sup-up a (lim h t) σ σK = ⊑ᴵ-trans (sup-up a (h 0) σ (λ q → σK (lim 0 q))) (⊑L 0)

  sup-K : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → K ⊑ᴵ sup a K σ σK
  sup-K a zero      σ σK = z⊑
  sup-K a (suc K)   σ σK = sup₁-K a K σ σK
  sup-K a (lim h t) σ σK = l⊑ (λ n → ⊑ᴵ-trans (sup-K a (h n) σ (λ q → σK (lim n q))) (⊑L n))

  sup-lub : ∀ {ℓ η} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → a ⊑ᴵ η → K ⊑ᴵ η → sup a K σ σK ⊑ᴵ η
  sup-lub a zero      σ σK h k = h
  sup-lub a (suc K)   σ σK h k = sup₁-lub a K σ σK h k
  sup-lub a (lim f t) σ σK h (l⊑ k) = l⊑ (λ n → sup-lub a (f n) σ (λ q → σK (lim n q)) h (k n))

sup₁-sim : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → Simᴵ (sup₁ a K σ ek) ℓ
sup₁-sim zero      K σ ek q = ek q
sup₁-sim (suc y)   K σ ek q with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = σ q
... | injᵇ _ = ek q
... | injᶜ _ = σ q
sup₁-sim (lim g s) K σ ek (lim n q) = sup₁-sim (g n) K (λ r → σ (lim n r)) ek q

sup-sim : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → Simᴵ (sup a K σ σK) ℓ
sup-sim a zero      σ σK q = σ q
sup-sim a (suc K)   σ σK q = sup₁-sim a K σ σK q
sup-sim a (lim h t) σ σK (lim n q) = sup-sim a (h n) σ (λ r → σK (lim n r)) q
```

`NZ`: 没有 `zero` 节点. `Bd` 永远 `NZ` (初值 `suc i`, `sup` 与 `sup₁` 都保持), 所以平凡项 `fk zero` 不改界 (`sup₁-triv`) 且可从上界条件里免去 (`sup₁-lub₀`; 退化层号 $\lim[0,0,\dots]$ 上 $0\not\prec\eta$).

```agda
NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim f s) = ∀ n → NZ (f n)

sup₁-NZ : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → NZ (sup₁ a K σ ek)
sup₁-NZ zero      K σ ek = tt
sup₁-NZ (suc y)   K σ ek with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = tt
... | injᵇ _ = tt
... | injᶜ _ = tt
sup₁-NZ (lim g s) K σ ek n = sup₁-NZ (g n) K (λ q → σ (lim n q)) ek

sup-NZ : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → NZ a → NZ (sup a K σ σK)
sup-NZ a zero      σ σK nz = nz
sup-NZ a (suc K)   σ σK nz = sup₁-NZ a K σ σK
sup-NZ a (lim h t) σ σK nz n = sup-NZ a (h n) σ (λ q → σK (lim n q)) nz

sup₁-lub₀ : ∀ {ℓ η} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → NZ a → K ≅ᴵ zero → a ⊑ᴵ η → sup₁ a K σ ek ⊑ᴵ η
sup₁-lub₀ (suc y)   K σ ek nz k0 h with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = h
... | injᵇ s = ⊥-elim (≺0 s k0)
... | injᶜ _ = h
sup₁-lub₀ (lim g s) K σ ek nz k0 (l⊑ h) = l⊑ (λ n → sup₁-lub₀ (g n) K (λ q → σ (lim n q)) ek (nz n) k0 (h n))

sup₁-triv : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → NZ a → K ≅ᴵ zero → sup₁ a K σ ek ≅ᴵ a
sup₁-triv (suc y)   K σ ek nz k0 with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = ≅ᴵ-refl _
... | injᵇ s = ⊥-elim (≺0 s k0)
... | injᶜ _ = ≅ᴵ-refl _
sup₁-triv (lim g s) K σ ek nz k0 = l≅ (λ n → sup₁-triv (g n) K (λ q → σ (lim n q)) ek (nz n) k0)
```

`Top i ℓ φ`: 目标 $i$ 与已处理地板 $\varphi$ 的界 `Bd` (字面地 `Simᴵ Bd ℓ`), 泛性质 `ubd`, 与字面容器 $F$ (`Fc`/`evF`/`iF`), $F\sqsubseteq\mathtt{Bd}\sqsubseteq F$. 容器不作比较: 新项 $D$ 进来时 $F'=[D, [F, B', B',\dots], [F,B',\dots],\dots]$. 地板的 `fk K` 项的要求写成 $K\prec\eta$ 或 $K\cong0$; `fb K` 的要求 $K\sqsubseteq\eta$ 由 $K\prec\eta$ 推出 (足够: 标签见证总给严格的).

```agda
≺→⊑ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ (via e q) = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ e) (Sim→⊑ᴵ (λ r → <ᴵ-trans r q))

isB : ∀ {K φ} → InF K φ → Bool
isB ink     = false
isB inb     = true
isB (inl k) = isB k
isB (inr k) = isB k

DemB : Bool → Ordᴵ → Ordᴵ → Set
DemB false η K = (K ≺ᴵ η) ⊎ (K ≅ᴵ zero)
DemB true  η K = K ⊑ᴵ η

Dem : ∀ {K φ} → Ordᴵ → InF K φ → Set
Dem {K} η k = DemB (isB k) η K

dem : ∀ {K φ η} (k : InF K φ) → (K ≺ᴵ η) ⊎ (K ≅ᴵ zero) → Dem η k
dem ink     h = h
dem inb     (inj₁ s)  = ≺→⊑ s
dem inb     (inj₂ z≅) = z⊑
dem (inl k) h = dem k h
dem (inr k) h = dem k h

record Top (i ℓ : Ordᴵ) (φ : Flr) : Set where
  constructor top
  field
    Bd  : Ordᴵ
    sb  : Simᴵ Bd ℓ
    nz  : NZ Bd
    ubd : ∀ {η} → i ≺ᴵ η → (∀ {K} (k : InF K φ) → Dem η k) → Bd ⊑ᴵ η
    Fc  : Ordᴵ
    evF : Ev Fc φ
    iF  : i <ᴵ Fc
    FM  : Fc ⊑ᴵ Bd
    MF  : Bd ⊑ᴵ Fc
open Top public

top₀ : ∀ {i ℓ} → i <ᴵ ℓ → Top i ℓ fz
top₀ {i} p = top (suc i) (λ { zero → p ; (suc q) → <ᴵ-trans q p }) tt
                 (λ { (via e q) _ → s⊑ e q }) (suc i) tt zero ⊑ᴵ-refl ⊑ᴵ-refl

module _ {i ℓ φ} (t : Top i ℓ φ) {D B′ : Ordᴵ} (bb : Bd t ⊑ᴵ B′) (dd : D ⊑ᴵ B′) where
  F₁ : Ordᴵ
  F₁ = Mlev (Fc t) B′ (⊑ᴵ-trans (FM t) bb)
  Fₙ : Ordᴵ
  Fₙ = Mlev D F₁ (⊑ᴵ-trans dd (⊑L 1))
  Fₙ-M : Fₙ ⊑ᴵ B′
  Fₙ-M = l⊑ (FsUB dd (l⊑ (FsUB (⊑ᴵ-trans (FM t) bb) ⊑ᴵ-refl)))
  Fₙ-B : B′ ⊑ᴵ Fₙ
  Fₙ-B = Sim→⊑ᴵ (λ q → lim 1 (lim 1 q))

ins : ∀ {i ℓ φ K} → Top i ℓ φ → Simᴵ (suc K) ℓ → Top i ℓ (φ ⊔ fk K)
ins {i} {φ = φ} {K} t ek =
  top B′ (sup₁-sim (Bd t) K (sb t) ek) (sup₁-NZ (Bd t) K (sb t) ek)
      (λ {η} iη h → ub iη (h (inr ink)) (λ k → h (inl k)))
      (Fₙ t bb dd) (liftEv φ (λ q → lim 1 (lim 0 q)) (evF t) , (λ q → lim 0 q)) (lim 1 (lim 0 (iF t))) (Fₙ-M t bb dd) (Fₙ-B t bb dd)
  where
  B′ = sup₁ (Bd t) K (sb t) ek
  bb = sup₁-up (Bd t) K (sb t) ek
  dd = sup₁-K (Bd t) K (sb t) ek
  ub : ∀ {η} → i ≺ᴵ η → (K ≺ᴵ η) ⊎ (K ≅ᴵ zero) → (∀ {K′} (k : InF K′ φ) → Dem η k) → B′ ⊑ᴵ η
  ub iη (inj₁ (via e q)) h = sup₁-lub (Bd t) K (sb t) ek (ubd t iη h) (s⊑ e q)
  ub iη (inj₂ k0) h = sup₁-lub₀ (Bd t) K (sb t) ek (nz t) k0 (ubd t iη h)

insB : ∀ {i ℓ φ K} → Top i ℓ φ → Simᴵ K ℓ → Top i ℓ (φ ⊔ fb K)
insB {i} {φ = φ} {K} t ek =
  top B′ (sup-sim (Bd t) K (sb t) ek) (sup-NZ (Bd t) K (sb t) ek (nz t))
      (λ {η} iη h → ub iη (h (inr inb)) (λ k → h (inl k)))
      (Fₙ t bb dd) (liftEv φ (λ q → lim 1 (lim 0 q)) (evF t) , (λ q → lim 0 q)) (lim 1 (lim 0 (iF t))) (Fₙ-M t bb dd) (Fₙ-B t bb dd)
  where
  B′ = sup (Bd t) K (sb t) ek
  bb = sup-up (Bd t) K (sb t) ek
  dd = sup-K (Bd t) K (sb t) ek
  ub : ∀ {η} → i ≺ᴵ η → K ⊑ᴵ η → (∀ {K′} (k : InF K′ φ) → Dem η k) → B′ ⊑ᴵ η
  ub iη le h = sup-lub (Bd t) K (sb t) ek (ubd t iη h) le
```

`accT` 依次并入地板的各项, `bound` 从目标出发处理整个地板.

```agda
mapTop : ∀ {i ℓ φ ψ} → (∀ {L} → Ev L φ → Ev L ψ) → (g : ∀ {K} → InF K φ → InF K ψ) → (∀ {K} (k : InF K φ) → isB (g k) ≡ isB k) → Top i ℓ φ → Top i ℓ ψ
mapTop f g gb t = top (Bd t) (sb t) (nz t)
  (λ {η} iη h → ubd t iη (λ {K} k → subst (λ b → DemB b η K) (gb k) (h (g k)))) (Fc t) (f (evF t)) (iF t) (FM t) (MF t)

accT : ∀ {i ℓ φ₁} → Top i ℓ φ₁ → (φ₂ : Flr) → Ev ℓ φ₂ → Top i ℓ (φ₁ ⊔ φ₂)
accT t fz      _       = mapTop (λ x → x , tt) inl (λ _ → refl) t
accT t (fk K)  ek      = ins t ek
accT t (fb K)  ek      = insB t ek
accT t (a ⊔ b) (x , y) =
  mapTop (λ { ((u , v) , w) → u , (v , w) })
         (λ { (inl (inl k)) → inl k ; (inl (inr k)) → inr (inl k) ; (inr k) → inr (inr k) })
         (λ { (inl (inl k)) → refl ; (inl (inr k)) → refl ; (inr k) → refl })
         (accT (accT t a x) b y)

strip : ∀ {K φ} → InF K (fz ⊔ φ) → InF K φ
strip (inl ())
strip (inr k) = k

bound : ∀ {i ℓ} (φ : Flr) → Ev ℓ φ → i <ᴵ ℓ → Top i ℓ φ
bound φ ev p = mapTop proj₂ strip (λ { (inl ()) ; (inr k) → refl }) (accT (top₀ p) φ ev)

FB : ∀ {i ℓ φ} (B : Top i ℓ φ) {η} → Bd B ⊑ᴵ η → Fc B ⊑ᴵ suc η
FB B {η} e = ⊑ᴵ-trans (FM B) (⊑ᴵ-trans e (⊑-suc η))
```

**闭包.** 深度 0: 界 `Bd B`, 第 0 点 `t ev p` (原环境), 分支 $\eta$ 在 `Mlev (Fc B) (suc η)` 上, 与 Uniform2Base 其余逐字.

```agda
cloA : ∀ d {φ} → A d (φ ⊔ fk zero) → ((η : Ordᴵ) → A d (φ ⊔ fk η)) → A d (φ ⊔ fk zero)
cloA zero {φ} t g {i} ev p =
  Ord₊ˢ.ŝ (Bd B) (t ev p)
          (λ η e → g η {ℓ = Mlev (Fc B) (suc η) (FB B e)} (liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q))
                         (lim 0 (iF B)))
  where B = bound (φ ⊔ fk zero) ev p
cloA (suc d) {φ} t g {fl} P =
  wk d (λ { (u , (v , w)) → (u , v) , w })
       (cloA d {fl ⊔ φ} (wk d (λ { ((u , v) , w) → u , (v , w) }) (t P))
                        (λ η → wk d (λ { ((u , v) , w) → u , (v , w) }) (g η P)))
```

## §4 统一折叠

与 Uniform2Base 只差三处: `flo` 的极限子句、`toFlo` 收 `Simᴵ k ℓ`、`up (self n)` 子句. `up zero` 与 `up (self n)` 现在同形: 地板是目标层 ($k'$ 或 $f\,n$) 的紧地板.

```agda
flo : Ordᴵ → Flr
flo zero      = fz
flo (suc k)   = fk k
flo (lim f s) = fb (lim f s)

cvFlo : ∀ k {ℓ} → Ev ℓ (flo k) → Simᴵ k ℓ
cvFlo zero      _ = σ⊥
cvFlo (suc k)   e = e
cvFlo (lim f s) e = e

toFlo : ∀ k {ℓ} → Simᴵ k ℓ → Ev ℓ (flo k)
toFlo zero      σ = tt
toFlo (suc k)   σ = σ
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
  wk d (λ { (u , v) → u , toFlo k′ (λ q → cv v (suc q)) }) (fold d (flo k′) (cvFlo k′) P x)
fold d {k = lim f s} φ cv P (Ord₊ˢ.up (self n) x) =
  wk d (λ { (u , v) → u , toFlo (f n) (λ q → cv v (lim n q)) }) (fold d (flo (f n)) (cvFlo (f n)) P x)
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

**弹栈行 (`cloA`).** 地板见证 `FW`: 每个地板项要么平凡 ($\cong0$), 要么被某个出现在一切点标签里的带 `Idx` 的下标支配 (`≺ ⊎ ≅`). `gŝ` 行要**一个**下标支配整个界. Uniform2Base 从字面最大者的来源 `src` 读它; 这里界是上确界, 没有字面最大者, 于是在**记号**上比较: 见证都带 `Idx`, `cmpᵀ` 可判定, `Ilt`/`Ieq` 把记号序搬到层号 (`pickMax`). 目标 0 的支配 `domC` 不需要比较, 直接用 `ubd`.

```agda
FW : Flr → T → PT → T → Set
FW φ ps y ys = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Ob w ps y ys

sB : ∀ {a b} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → suc a ⊑ᴵ suc b
sB (inj₁ (via e r)) = s⊑ e (suc r)
sB (inj₂ e)         = s⊑ e zero

_≼_ : Ordᴵ → Ordᴵ → Set
a ≼ b = (a ≺ᴵ b) ⊎ (a ≅ᴵ b)

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans (inj₁ s) (inj₁ s′) = inj₁ (≺ᴵ-trans s s′)
≼-trans (inj₁ s) (inj₂ e)  = inj₁ (≺ᴵ-respʳ s e)
≼-trans (inj₂ e) (inj₁ s)  = inj₁ (≺ᴵ-respˡ e s)
≼-trans (inj₂ e) (inj₂ e′) = inj₂ (≅ᴵ-trans e e′)

≼→≺s : ∀ {a b} → a ≼ b → a ≺ᴵ suc b
≼→≺s (inj₁ (via e r)) = via e (suc r)
≼→≺s (inj₂ e)         = via e zero

maxI : ∀ {w₀ w₁} (I₀ : Idx w₀) (I₁ : Idx w₁) → (lvI I₀ ≼ lvI I₁) ⊎ (lvI I₁ ≼ lvI I₀)
maxI {w₀} {w₁} I₀ I₁ with cmpᵀ w₀ w₁ in e
... | lt = inj₁ (inj₁ (Ilt I₀ I₁ (lt→< w₀ w₁ e)))
... | gt = inj₂ (inj₁ (Ilt I₁ I₀ (gt→< w₀ w₁ e)))
... | eq with eq→≡ w₀ w₁ e
...   | refl = inj₁ (inj₂ (Ieq I₀ I₁))

record Pick (P : T → Set) (φ : Flr) (Sk : ∀ {K} → InF K φ → Set) (c : Ordᴵ) : Set where
  constructor pk
  field
    pw  : T
    pI  : Idx pw
    pP  : P pw
    pc  : c ≼ lvI pI
    pF  : ∀ {K} (k : InF K φ) → Sk k ⊎ (K ≼ lvI pI)

pickMax : ∀ {P : T → Set} (φ : Flr) (Sk : ∀ {K} → InF K φ → Set) {c} →
          (∀ {K} (k : InF K φ) → Sk k ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × P w) →
          ∀ {w₀} (I₀ : Idx w₀) → P w₀ → c ≼ lvI I₀ → Pick P φ Sk c
pickMax fz      Sk wit I₀ p₀ c₀ = pk _ I₀ p₀ c₀ (λ ())
pickMax (fk K)  Sk wit I₀ p₀ c₀ with wit ink
... | inj₁ k0 = pk _ I₀ p₀ c₀ (λ { ink → inj₁ k0 })
... | inj₂ (w , Iw , kw , pw) with maxI I₀ Iw
...   | inj₁ le = pk w Iw pw (≼-trans c₀ le) (λ { ink → inj₂ kw })
...   | inj₂ le = pk _ I₀ p₀ c₀ (λ { ink → inj₂ (≼-trans kw le) })
pickMax (fb K)  Sk wit I₀ p₀ c₀ with wit inb
... | inj₁ k0 = pk _ I₀ p₀ c₀ (λ { inb → inj₁ k0 })
... | inj₂ (w , Iw , kw , pw) with maxI I₀ Iw
...   | inj₁ le = pk w Iw pw (≼-trans c₀ le) (λ { inb → inj₂ kw })
...   | inj₂ le = pk _ I₀ p₀ c₀ (λ { inb → inj₂ (≼-trans kw le) })
pickMax (a ⊔ b) Sk {c} wit I₀ p₀ c₀ =
  pk (Pick.pw B) (Pick.pI B) (Pick.pP B) (≼-trans (Pick.pc A′) (Pick.pc B))
     (λ { (inl k) → lftA (Pick.pF A′ k) ; (inr k) → Pick.pF B k })
  where
  A′ = pickMax a (λ k → Sk (inl k)) (λ k → wit (inl k)) I₀ p₀ c₀
  B  = pickMax b (λ k → Sk (inr k)) (λ k → wit (inr k)) (Pick.pI A′) (Pick.pP A′) (inj₂ (≅ᴵ-refl _))
  lftA : ∀ {K} {k : InF K a} → (Sk (inl k)) ⊎ (K ≼ lvI (Pick.pI A′)) → (Sk (inl k)) ⊎ (K ≼ lvI (Pick.pI B))
  lftA (inj₁ k0) = inj₁ k0
  lftA (inj₂ kw) = inj₂ (≼-trans kw (Pick.pc B))

Tr0 : ∀ {K φ} → InF K φ → Set
Tr0 {K} _ = K ≅ᴵ zero

evη : ∀ {i ℓ} (φ : Flr) (B : Top i ℓ (φ ⊔ fk zero)) η (e : Bd B ⊑ᴵ η) → Ev (Mlev (Fc B) (suc η) (FB B e)) (φ ⊔ fk η)
evη φ B η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)

≺-of-⊑ : ∀ {a b} → suc a ⊑ᴵ b → a ≺ᴵ b
≺-of-⊑ (s⊑ e q) = via e q

module _ {φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where

  pickW : ∀ {i ℓ w} (Iw : Idx w) → i ≅ᴵ lvI Iw → (B : Top i ℓ (φ ⊔ fk zero)) →
          Σ T λ w′ → Σ (Idx w′) λ Iw′ → (Bd B ⊑ᴵ suc (lvI Iw′)) × (∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ []))
  pickW {i} {ℓ} {w} Iw ei B = Pick.pw Pk , Pick.pI Pk ,
      ubd B (≼→≺s (≼-trans (inj₂ ei) (Pick.pc Pk))) (λ k → dem k (pd (Pick.pF Pk k))) , Pick.pP Pk
    where
    pw′ : ∀ {K} → (K ≅ᴵ zero) ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × Ob w₁ ps y ys) →
          (K ≅ᴵ zero) ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × (∀ θ → Occ w₁ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ [])))
    pw′ (inj₁ k0) = inj₁ k0
    pw′ (inj₂ (w₁ , I₁′ , kw , ob′)) = inj₂ (w₁ , I₁′ , kw , (λ θ → od (ob′ θ)))
    Pk : Pick (λ w′ → ∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ [])) (φ ⊔ fk zero) Tr0 (lvI Iw)
    Pk = pickMax (φ ⊔ fk zero) Tr0 (λ k → pw′ (fw k)) Iw (λ θ → oh) (inj₂ (≅ᴵ-refl _))
    pd : ∀ {K} → (K ≅ᴵ zero) ⊎ (K ≼ lvI (Pick.pI Pk)) → (K ≺ᴵ suc (lvI (Pick.pI Pk))) ⊎ (K ≅ᴵ zero)
    pd (inj₁ k0) = inj₂ k0
    pd (inj₂ kw) = inj₁ (≼→≺s kw)

  domC : ∀ {ℓ Y} (hY : HS Y) (B : Top zero ℓ (φ ⊔ fk zero)) →
         ∀ θ → Lab Y (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → Bd B ⊑ᴵ toLevel Y hY
  domC hY B θ lY nf = ubd B (≺-of-⊑ (one⊑lab hY lY nf []<)) (λ k → dem k (dm k))
    where
    dm : ∀ {K} → InF K (φ ⊔ fk zero) → (K ≺ᴵ toLevel _ hY) ⊎ (K ≅ᴵ zero)
    dm k with fw k
    ... | inj₁ k0 = inj₂ k0
    ... | inj₂ (w′ , Iw′ , kw , ob′) = inj₁ (≺-of-⊑ (domP _ hY Iw′ (sB kw) (ob′ θ) lY nf))

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
    Pk = pickW Iw ei B

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
    Rg : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : Bd B ⊑ᴵ toLevel Y hY) →
         Lab₀ (g (toLevel Y hY) (evη φ B (toLevel Y hY) e) (lim 0 (iF B))) (γW ps (y ∷ ys) [] (suc (suc m)))
    Rg m Y hY lY e = hg _ Y hY lY (nfγ m) (1<γ ps y ys cs m) (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) (nfγ (suc m))
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ R₀) (proj₂ R₀)
            (domC _ B (natT 1) (proj₂ R₀) (nfγ 0))
            (λ m Y hY lY e → proj₁ (Rg m Y hY lY e)) (λ m Y hY lY e → proj₂ (Rg m Y hY lY e))
            (λ m Y hY lY e → domC _ B (γW ps (y ∷ ys) [] (suc m)) (proj₂ (Rg m Y hY lY e)) (nfγ (suc m)))
```

**界的互模拟.** 两个地板 "非平凡部分逐项 $\cong$" (`_∼ᶠ_`: 平凡项可以与空位对应) 且目标 $\cong$ 时, 两次 `bound` 的界 $\cong$. 上确界对参数逐点 (`sup₁-≅`/`sup-≅`), 叶子的比较结果由 `clash₁`/`clash₂` 保持一致, 平凡项不改界 (`sup₁-triv`).

```agda
infix 4 _∼ᶠ_
data _∼ᶠ_ : Flr → Flr → Set where
  fz∼ : fz ∼ᶠ fz
  fk∼ : ∀ {K K′} → K ≅ᴵ K′ → fk K ∼ᶠ fk K′
  fb∼ : ∀ {K K′} → K ≅ᴵ K′ → fb K ∼ᶠ fb K′
  zk∼ : ∀ {K′} → K′ ≅ᴵ zero → fz ∼ᶠ fk K′
  kz∼ : ∀ {K} → K ≅ᴵ zero → fk K ∼ᶠ fz
  ⊔∼  : ∀ {a a′ b b′} → a ∼ᶠ a′ → b ∼ᶠ b′ → a ⊔ b ∼ᶠ a′ ⊔ b′

∼ᶠ-refl : ∀ φ → φ ∼ᶠ φ
∼ᶠ-refl fz      = fz∼
∼ᶠ-refl (fk K)  = fk∼ (≅ᴵ-refl K)
∼ᶠ-refl (fb K)  = fb∼ (≅ᴵ-refl K)
∼ᶠ-refl (a ⊔ b) = ⊔∼ (∼ᶠ-refl a) (∼ᶠ-refl b)

sup₁-≅ : ∀ {ℓ ℓ′ a a′ K K′} (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) (σ′ : Simᴵ a′ ℓ′) (ek′ : Simᴵ (suc K′) ℓ′) →
         a ≅ᴵ a′ → K ≅ᴵ K′ → sup₁ a K σ ek ≅ᴵ sup₁ a′ K′ σ′ ek′
sup₁-≅ σ ek σ′ ek′ z≅ eK = s≅ eK
sup₁-≅ σ ek σ′ ek′ (s≅ eM) eK with <ᴵ-dec (ek zero) (σ zero) | <ᴵ-dec (ek′ zero) (σ′ zero)
... | injᵃ (via _ _) | injᵃ (via _ _) = s≅ eM
... | injᵃ (via _ _) | injᶜ _ = s≅ eM
... | injᶜ _ | injᵃ (via _ _) = s≅ eM
... | injᶜ _ | injᶜ _ = s≅ eM
... | injᵇ (via _ _) | injᵇ (via _ _) = s≅ eK
... | injᵃ r | injᵇ s = ⊥-elim (clash₁ eK eM r s)
... | injᶜ c | injᵇ s = ⊥-elim (clash₂ (≅ᴵ-sym eM) (≅ᴵ-sym eK) s (≅ᴵ-sym c))
... | injᵇ s | injᵃ r = ⊥-elim (clash₁ (≅ᴵ-sym eK) (≅ᴵ-sym eM) r s)
... | injᵇ s | injᶜ c = ⊥-elim (clash₂ eM eK s (≅ᴵ-sym c))
sup₁-≅ σ ek σ′ ek′ (l≅ h) eK = l≅ (λ n → sup₁-≅ (λ q → σ (lim n q)) ek (λ q → σ′ (lim n q)) ek′ (h n) eK)

sup-≅ : ∀ {ℓ ℓ′ a a′ K K′} (σ : Simᴵ a ℓ) (ek : Simᴵ K ℓ) (σ′ : Simᴵ a′ ℓ′) (ek′ : Simᴵ K′ ℓ′) →
        a ≅ᴵ a′ → K ≅ᴵ K′ → sup a K σ ek ≅ᴵ sup a′ K′ σ′ ek′
sup-≅ σ ek σ′ ek′ eA z≅ = eA
sup-≅ σ ek σ′ ek′ eA (s≅ eK) = sup₁-≅ σ ek σ′ ek′ eA eK
sup-≅ σ ek σ′ ek′ eA (l≅ h) = l≅ (λ n → sup-≅ σ (λ q → ek (lim n q)) σ′ (λ q → ek′ (lim n q)) eA (h n))

accM : ∀ {i i′ ℓ ℓ′ φ₁ φ₁′ φ₂ φ₂′} (t : Top i ℓ φ₁) (t′ : Top i′ ℓ′ φ₁′) → φ₂ ∼ᶠ φ₂′ →
       (ev : Ev ℓ φ₂) (ev′ : Ev ℓ′ φ₂′) → Bd t ≅ᴵ Bd t′ → Bd (accT t φ₂ ev) ≅ᴵ Bd (accT t′ φ₂′ ev′)
accM t t′ fz∼       ev ev′ eM = eM
accM t t′ (fk∼ eK)  ev ev′ eM = sup₁-≅ (sb t) ev (sb t′) ev′ eM eK
accM t t′ (fb∼ eK)  ev ev′ eM = sup-≅ (sb t) ev (sb t′) ev′ eM eK
accM t t′ (zk∼ k0)  ev ev′ eM = ≅ᴵ-trans eM (≅ᴵ-sym (sup₁-triv (Bd t′) _ (sb t′) ev′ (nz t′) k0))
accM t t′ (kz∼ k0)  ev ev′ eM = ≅ᴵ-trans (sup₁-triv (Bd t) _ (sb t) ev (nz t) k0) eM
accM t t′ (⊔∼ a b) (x , y) (x′ , y′) eM = accM (accT t _ x) (accT t′ _ x′) b y y′ (accM t t′ a x x′ eM)

bound-≅ : ∀ {i i′ ℓ ℓ′ φ φ′} → φ ∼ᶠ φ′ → (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ φ′) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ →
          Bd (bound φ ev p) ≅ᴵ Bd (bound φ′ ev′ p′)
bound-≅ s ev p ev′ p′ ei = accM (top₀ p) (top₀ p′) s ev ev′ (s≅ ei)


cloR : ∀ {φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
       {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
       t ≈ᴿ t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ᴿ g′ η′) → cloA 0 t g ≈ᴿ cloA 0 t′ g′
cloR {φ} {φ′} s ht hg ev p ev′ p′ ei =
  ŝ≅ (kd-≅ ei) (bound-≅ (⊔∼ s (fk∼ z≅)) ev p ev′ p′ ei) (ht ev p ev′ p′ ei)
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
  wkR (λ ev → proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) (λ ev → ev) (fold-≅0 H e)
fold-≅0 {k₁ = lim f s} {cv = cv} {cv′ = cv′} H (upˡ {r = self n} e) =
  wkR (λ ev → proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))) (λ ev → ev) (fold-≅0 H e)
fold-≅0 {k₂ = suc k′} {cv = cv} {cv′ = cv′} H (upʳ {r = zero} e) =
  wkR (λ ev → ev) (λ ev → proj₁ ev , toFlo k′ (λ q → cv′ (proj₂ ev) (suc q))) (fold-≅0 H e)
fold-≅0 {k₂ = lim f s} {cv = cv} {cv′ = cv′} H (upʳ {r = self n} e) =
  wkR (λ ev → ev) (λ ev → proj₁ ev , toFlo (f n) (λ q → cv′ (proj₂ ev) (lim n q))) (fold-≅0 H e)
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
  tlW₊ {k = suc k′} {φ = φ} {cv = cv} (gu {r = zero} h) = λ ev p → tlWV {φ = flo k′} {cv = cvFlo k′} h (proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) p
  tlW₊ {k = lim f s} {φ = φ} {cv = cv} (gu {r = self n} h) = λ ev p → tlWV {φ = flo (f n)} {cv = cvFlo (f n)} h (proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))) p
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
    λ ev p → tl0V {φ = flo k′} {cv = cvFlo k′} h (u-reflˢ zero ex) (proj₁ ev , toFlo k′ (λ q → cv (proj₂ ev) (suc q))) p
  tl0₊ {k = lim f s} {φ = φ} {cv = cv} (gu {r = self n} h) ex =
    λ ev p → tl0V {φ = flo (f n)} {cv = cvFlo (f n)} h (u-reflˢ (self n) ex) (proj₁ ev , toFlo (f n) (λ q → cv (proj₂ ev) (lim n q))) p
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

## §12 边界

Uniform2Base §12 的取舍表仍然适用, 只是 "字面最大者" 换成逐点上确界. 结论见 [Uniform3Full](Uniform3Full.lagda.md) 文末.

**工程注记.** (1) `maxS` 把三歧结果放在一等辅助函数里, 证明侧 `with <ᴵ-dec …` 正好抽象掉它. (2) `sup₁`/`sup` 与上界、最小上界引理必须互递归: `lim` 的步进证据就用这两条. (3) `mapTop` 多一个 "映射保持 `isB`" 的前提 (`DemB` 依项的种类), 四处调用都是 `refl`.
