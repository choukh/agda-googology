# 悬置不变量 (一): 三层遗传好树与折叠闭包定理

> 接 [TreeNFBase](TreeNFBase.lagda.md) (地板、覆盖、`ColC`、`dom-cov`) 与 [TreeNF](TreeNF.lagda.md) §4 的缺口: 闭包被目标低于其覆盖的 $\psi_d$ 映射之后, `ColC` 丢失, 要等分支里目标足够高的映射者重新托起. 本文把这件事做成遗传好树的一部分, 证明折叠闭包定理; [Pending](Pending.lagda.md) 用它得到 `Gᴺ₂`.
>
> 结论先说:
>
> 1. **三层, 不是任务设想的两层 (§1).** `Good m K x`, 模式 $m$ 与水位 $K$: `mV` (可见: 闭包有覆盖 $\varphi\sqsubseteq K$ 且有 `ColC`), `mP` (悬置: 只有覆盖, 节点 $\sqsubseteq K$), `mC` (同 `mP` 但节点不受限). 第三层来自 $\psi^{[]}$: 弹栈闭包的尾巴 $\psi^{[]}_i(\Omega_\eta)$ 对一切 $\eta$ 出现, 其中节点任意高, 但 $\psi^{[]}$ 不弹栈, 高节点不产生新闭包; 而 $\psi^{[\hat\Omega]}$ 在高节点处折叠会产生高覆盖的闭包, 所以 `mP` 必须限节点.
> 2. **吸收条件 (`biV`).** 可见的 `limᵢ` 带包裹目标 $\kappa\sqsupseteq j$: 分支把 "悬置水位 $\kappa$" 的输入 (当 $\kappa\sqsubseteq j$ 时还要可见) 映成可见水位 $\kappa$ 的输出. 这是记号侧 `vs` 规则的树形式 (§8).
> 3. **闭包定理 (§6–§7), 唯一的参数是弹栈覆盖 `PopCov ℓ`:** `Fold.P-ψ1` (悬置 $\to$ 悬置, 目标 $\sqsubseteq K$), `Fold.V-ψ1` (悬置 $\to$ 可见, 水位 $\sqsubseteq$ 目标, 这是 "托起"), **`Fold.Good-ψ1 : Good mV K x → x ≅ˢ x → Goodᶻ (toZ (ψ1 p σ z x))`**. 支配全部由映射者再生的地板经 `dom-cov` 得到, 第 0 层直接读 `ColC`. 没有全局界, 没有链指标, 没有记号.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件. §5 的 $\psi^{[]}$ 引理与 §6 的 $\psi^{[\hat\Omega]}$ 引理的折叠子句沿用 TreeNFBase `Floor` 的写法.

## §0 导入

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.PendingBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev; σ1)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; Goodᶻ; force; force-HS; z<suc)
open Restrˢ
open import OCF.Align.UniformS hiding (Dom; Good₊; Gd; Good; Gd→Good; Good→Gd; Gd-conv; Good→Goodᶻ;
  Dom0-≅; Dom-tr; Dom-tr⁻; Good-tr; Good-tr⁻; Good-back; Good-back⁻; Good-Ω; Good-add; Good-iter;
  bz; bs; bl; bi; bu; bŝ; bĉ)
open import OCF.Align.Stage2Label using (Ok; Ok-Pl; Ok-suc; Ok-lim; Ok-up; Ok-col; Ok-pen; ~ŝ; ~ĉ; Pl-Ω;
  chain0; chain1; chain0-≅; chain1-≅; chain0-step; chain1-step; Strict₀; t₀pop; gpop)
open import OCF.Align.TreeNFBase using (NZ; one⊑; Mlev⊑; FlΛ; FlΛ-ψ0; FlΛ-t₀pop; FlΛ-gpop; FlΛ-ψ1; FlΛ-add; add-floor;
  χ̂; CovΛ; IsCol; col; ctr; ctr⁻; ColC; ColC-tr; ColC-tr⁻; dom-cov)
```

## §1 定义

**覆盖与可见.** `Cvd K c`: 有 $\varphi\sqsubseteq K$ 且 `CovΛ φ c`. `VisD`: 只有 `mV` 要求 `ColC`. 第 0 层的 `Dom` 与 `Floor` 相同, 不看模式.

**节点的四种子句.** 水位 $K$ 是高水位标记: 分支对一切 $a\sqsupseteq K$ 把水位 $a$ 的输入映成水位 $a$ 的输出 (`trans`), 所以外来的高覆盖输入不被混淆.

| 子句 | 模式 | 节点界 | 分支 |
|---|---|---|---|
| `biH` | `mC` | 无 | `mC a` 到 `mC a` |
| `biL` | `mC` | $j\sqsubseteq K$ | `mP a` 到 `mC a` |
| `biP` | `mP` | $j\sqsubseteq K$ | `mP a` 到 `mP a` |
| `biV` | `mV` | $j\sqsubseteq K$, $j\sqsubseteq\kappa\sqsubseteq K$ | `biP` 的 `trans`, 加吸收 |

`biH` 与 `biL` 分开是必须的: `mP` 到 `mC` 的转换 (`P→C`) 走 `biL`, 因为分支的输入逆变, 悬置树的分支不接受 `mC` 输入 (把 $\Omega_\eta$ 喂给 $y\mapsto\psi^{[\hat\Omega]}_c(y)$ 会产生高覆盖闭包). 反过来 $\psi^{[]}$ 在节点处折叠时, 构造子本身告诉我们链在哪一层, 不必比较 $j$ 与水位 (两者没有公共上界, 没有三歧可用).

```agda
data Mode : Set where
  mC mP mV : Mode

Cvd : Ordᴵ → Ordᴵ → Set
Cvd K c = Σ Ordᴵ λ φ → CovΛ φ c × φ ⊑ᴵ K

VisD : ∀ {ℓ} → Mode → (c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
VisD mC c t₀ g = ⊤
VisD mP c t₀ g = ⊤
VisD mV c t₀ g = ColC c t₀ × (∀ η e → ColC c (g η e))

Dom : Mode → Ordᴵ → (ℓ c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
Dom m K zero      c t₀ g = (∀ G → c ⊑ᴵ toLevel (force (toZ t₀) G) (force-HS _ G)) ×
                           (∀ η e G → c ⊑ᴵ toLevel (force (toZ (g η e)) G) (force-HS _ G))
Dom m K (suc _)   c t₀ g = Cvd K c × VisD m c t₀ g
Dom m K (lim _ _) c t₀ g = Cvd K c × VisD m c t₀ g

module _ (ℓ : Ordᴵ) (G< : Mode → Ordᴵ → (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set) where
  data Good₊ : Mode → Ordᴵ → Ordˢ ℓ → Set where
    bz : ∀ {m K} → Good₊ m K Ord₊ˢ.zero
    bs : ∀ {m K a} → Good₊ m K a → Good₊ m K (Ord₊ˢ.suc a)
    bl : ∀ {m K} {h : ℕ → Ordˢ ℓ} → (∀ n → Good₊ m K (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ m K (Ord₊ˢ.lim h)
    biH : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} →
          (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mC a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mC a (f (intoˢ (<→◃ p) z))) →
          (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
          Good₊ mC K (Ord₊ˢ.limᵢ p f)
    biL : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} → j ⊑ᴵ K →
          (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mP a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mC a (f (intoˢ (<→◃ p) z))) →
          (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
          Good₊ mC K (Ord₊ˢ.limᵢ p f)
    biP : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} → j ⊑ᴵ K →
          (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mP a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mP a (f (intoˢ (<→◃ p) z))) →
          (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
          Good₊ mP K (Ord₊ˢ.limᵢ p f)
    biV : ∀ {K j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} → j ⊑ᴵ K → (κ : Ordᴵ) → j ⊑ᴵ κ → κ ⊑ᴵ K →
          (∀ a → K ⊑ᴵ a → ∀ (z : Ordˢ j) → z ≅ˢ z → G< mP a j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ mP a (f (intoˢ (<→◃ p) z))) →
          (∀ (z : Ordˢ j) → z ≅ˢ z → G< mP κ j (<→◃ p) (intoˢ (<→◃ p) z) → (κ ⊑ᴵ j → G< mV κ j (<→◃ p) (intoˢ (<→◃ p) z)) →
             Good₊ mV κ (f (intoˢ (<→◃ p) z))) →
          (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
          Good₊ mV K (Ord₊ˢ.limᵢ p f)
    bu : ∀ {m K k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → G< m K k (◃₁→◃ r) x → Good₊ m K (Ord₊ˢ.up r x)
    bŝ : ∀ {m K c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
         Good₊ m K t₀ → (∀ η e → Good₊ m K (g η e)) →
         t₀ ≅ˢ t₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′) →
         (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
         Dom m K ℓ c t₀ g → Good₊ m K (Ord₊ˢ.ŝ c t₀ g)
    bĉ : ∀ {m K c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ}
         (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
         c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
         (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
         (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
         (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
         Good₊ m K o₀ → (∀ η e → Good₊ m K (o η e)) →
         (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
         Good₊ m K (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

Gd : ∀ {ℓ} → Mode → Ordᴵ → (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set
Gd m K i zero         x = Good₊ i Gd m K x
Gd m K i (suc r)      x = Gd m K i r x
Gd m K _ (self {f} n) x = Good₊ (f n) Gd m K x
Gd m K i (lim n r)    x = Gd m K i r x

Good : ∀ {ℓ} → Mode → Ordᴵ → Ordˢ ℓ → Set
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ m K} (r : i ◃ ℓ) {x : Ordˢ i} → Gd m K i r (intoˢ r x) → Good m K x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ m K} (r : i ◃ ℓ) {x : Ordˢ i} → Good m K x → Gd m K i r (intoˢ r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g

Gd-conv : ∀ {i ℓ ℓ′ m K} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordˢ i} → Gd m K i r (intoˢ r x) → Gd m K i r′ (intoˢ r′ x)
Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)

Good→Goodᶻ : ∀ {m K} {x : Ordˢ zero} → Good m K x → Goodᶻ (toZ x)
Good→Goodᶻ bz         = Goodᶻ.gz
Good→Goodᶻ (bs g)     = Goodᶻ.gs (Good→Goodᶻ g)
Good→Goodᶻ (bl hg st) = Goodᶻ.gl (λ n → Good→Goodᶻ (hg n)) (λ n → st n idO (Good→Goodᶻ (hg n)) (Good→Goodᶻ (hg (suc n))))
Good→Goodᶻ (biH {p = ()} hb hm)
Good→Goodᶻ (biL {p = ()} j hb hm)
Good→Goodᶻ (biP {p = ()} j hb hm)
Good→Goodᶻ (biV {p = ()} j κ jκ κK tr ab hm)
Good→Goodᶻ (bu {r = ()} g)
Good→Goodᶻ (bŝ g₀ gg et eg m mm (d₀ , dE)) =
  Goodᶻ.gc G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
           (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
           G₀ Gg (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
  where
  G₀ = Good→Goodᶻ g₀
  Gg = λ η e → Good→Goodᶻ (gg η e)
Good→Goodᶻ (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  Goodᶻ.gc G₀ Gg d₀ dE m₀ mE (Good→Goodᶻ go) (λ η e → Good→Goodᶻ (gO η e))
           (λ η e → mo η e idO (Good→Goodᶻ go) (Good→Goodᶻ (gO η e)))
           (λ η e η′ e′ h → mO η e η′ e′ h idO (Good→Goodᶻ (gO η e)) (Good→Goodᶻ (gO η′ e′)))
```

## §2 水位单调、模式转换、$\Omega$

```agda
Dom-mono : ∀ {m K K′} ℓ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → K ⊑ᴵ K′ → Dom m K ℓ c t₀ g → Dom m K′ ℓ c t₀ g
Dom-mono zero      h d = d
Dom-mono (suc _)   h ((φ , cv , φK) , v) = (φ , cv , ⊑ᴵ-trans φK h) , v
Dom-mono (lim _ _) h ((φ , cv , φK) , v) = (φ , cv , ⊑ᴵ-trans φK h) , v

Good-mono : ∀ {ℓ m K K′} {x : Ordˢ ℓ} → K ⊑ᴵ K′ → Good m K x → Good m K′ x
Good-mono h bz         = bz
Good-mono h (bs g)     = bs (Good-mono h g)
Good-mono h (bl hg st) = bl (λ n → Good-mono h (hg n)) st
Good-mono h (biH hb hm) = biH (λ a k → hb a (⊑ᴵ-trans h k)) hm
Good-mono h (biL j hb hm) = biL (⊑ᴵ-trans j h) (λ a k → hb a (⊑ᴵ-trans h k)) hm
Good-mono h (biP j hb hm) = biP (⊑ᴵ-trans j h) (λ a k → hb a (⊑ᴵ-trans h k)) hm
Good-mono h (biV j κ jκ κK tr ab hm) = biV (⊑ᴵ-trans j h) κ jκ (⊑ᴵ-trans κK h) (λ a k → tr a (⊑ᴵ-trans h k)) ab hm
Good-mono h (bu {r = zero} g)   = bu {r = zero} (Good-mono h g)
Good-mono h (bu {r = self n} g) = bu {r = self n} (Good-mono h g)
Good-mono {ℓ} h (bŝ g0 gg et eg m mm dm) = bŝ (Good-mono h g0) (λ η e → Good-mono h (gg η e)) et eg m mm (Dom-mono ℓ h dm)
Good-mono h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-mono h go) (λ η e → Good-mono h (gO η e)) mo mO

Dom-V→P : ∀ {K} ℓ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → Dom mV K ℓ c t₀ g → Dom mP K ℓ c t₀ g
Dom-V→P zero      d = d
Dom-V→P (suc _)   (cv , _) = cv , tt
Dom-V→P (lim _ _) (cv , _) = cv , tt

Dom-P→C : ∀ {K} ℓ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → Dom mP K ℓ c t₀ g → Dom mC K ℓ c t₀ g
Dom-P→C zero      d = d
Dom-P→C (suc _)   (cv , _) = cv , tt
Dom-P→C (lim _ _) (cv , _) = cv , tt

V→P : ∀ {ℓ K} {x : Ordˢ ℓ} → Good mV K x → Good mP K x
V→P bz         = bz
V→P (bs g)     = bs (V→P g)
V→P (bl hg st) = bl (λ n → V→P (hg n)) st
V→P (biV j κ jκ κK tr ab hm) = biP j tr hm
V→P (bu {r = zero} g)   = bu {r = zero} (V→P g)
V→P (bu {r = self n} g) = bu {r = self n} (V→P g)
V→P {ℓ} (bŝ g0 gg et eg m mm dm) = bŝ (V→P g0) (λ η e → V→P (gg η e)) et eg m mm (Dom-V→P ℓ dm)
V→P (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) = bĉ G₀ Gg d₀ dE m₀ mE (V→P go) (λ η e → V→P (gO η e)) mo mO

P→C : ∀ {ℓ K} {x : Ordˢ ℓ} → Good mP K x → Good mC K x
P→C bz         = bz
P→C (bs g)     = bs (P→C g)
P→C (bl hg st) = bl (λ n → P→C (hg n)) st
P→C (biP j tr hm) = biL j (λ a h z ez g → P→C (tr a h z ez g)) hm
P→C (bu {r = zero} g)   = bu {r = zero} (P→C g)
P→C (bu {r = self n} g) = bu {r = self n} (P→C g)
P→C {ℓ} (bŝ g0 gg et eg m mm dm) = bŝ (P→C g0) (λ η e → P→C (gg η e)) et eg m mm (Dom-P→C ℓ dm)
P→C (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) = bĉ G₀ Gg d₀ dE m₀ mE (P→C go) (λ η e → P→C (gO η e)) mo mO

Good-Ωᶜ : ∀ a K → Good mC K (Ωˢ a)
Good-Ωᶜ zero      K = bs bz
Good-Ωᶜ (suc c)   K = biH (λ a h z ez g → bu g) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
Good-Ωᶜ (lim g s) K = bl (λ n → bu (Good-Ωᶜ (g n) K)) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

Good-Ωᴾ : ∀ a {K} → a ⊑ᴵ K → Good mP K (Ωˢ a)
Good-Ωᴾ zero      h = bs bz
Good-Ωᴾ (suc c)   h = biP (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) h) (λ a k z ez g → bu g) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
Good-Ωᴾ (lim g s) h = bl (λ n → bu (Good-Ωᴾ (g n) (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → lim n q)) h))) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

Good-Ωⱽ : ∀ a {K} → a ⊑ᴵ K → Good mV K (Ωˢ a)
Good-Ωⱽ zero      h = bs bz
Good-Ωⱽ (suc c)   h = biV cK c ⊑ᴵ-refl cK (λ a k z ez g → bu g) (λ z ez gp gv → bu (gv ⊑ᴵ-refl)) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
  where cK = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) h
Good-Ωⱽ (lim g s) h = bl (λ n → bu (Good-Ωⱽ (g n) (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → lim n q)) h))) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))
```

## §3 搬运

TreeNFBase 的 `Good-tr` 等的逐字推广; `biV` 的吸收前提经 `eqˢ` 搬运. `Dom0-≅` 的 `m′`/`K′` 要写出 (第 0 层 `Dom` 不看它们, 合一解不出).

```agda
Dom0-≅ : ∀ {m m′ K K′ c} {t₀ t₀′ : Ordˢ zero} {g g′ : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} →
         Good m K t₀ → (∀ η d → Good m K (g η d)) → t₀′ ≅ˢ t₀ → (∀ η d → g′ η d ≅ˢ g η d) →
         Dom m′ K′ zero c t₀ g → Dom m′ K′ zero c t₀′ g′
Dom0-≅ g0 gg et eg (d₀ , dE) =
  (λ G → ⊑ᴵ-≅ʳ (d₀ (Good→Goodᶻ g0)) (toLevel-≅ (force-HS _ (Good→Goodᶻ g0)) (force-HS _ G)
            (force-≅ (toZ-≅ (≅ˢ-sym et)) (Good→Goodᶻ g0) G))) ,
  (λ η d G → ⊑ᴵ-≅ʳ (dE η d (Good→Goodᶻ (gg η d))) (toLevel-≅ (force-HS _ (Good→Goodᶻ (gg η d))) (force-HS _ G)
            (force-≅ (toZ-≅ (≅ˢ-sym (eg η d))) (Good→Goodᶻ (gg η d)) G)))

VisD-tr : ∀ m {c a b} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
          VisD m c t₀ g → VisD m c (trˢ e t₀) (λ η d → trˢ e (g η d))
VisD-tr mC e v = tt
VisD-tr mP e v = tt
VisD-tr mV e (c₀ , cg) = ColC-tr e c₀ , λ η d → ColC-tr e (cg η d)

VisD-tr⁻ : ∀ m {c a b} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
           VisD m c t₀ g → VisD m c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
VisD-tr⁻ mC e v = tt
VisD-tr⁻ mP e v = tt
VisD-tr⁻ mV e (c₀ , cg) = ColC-tr⁻ e c₀ , λ η d → ColC-tr⁻ e (cg η d)

Dom-tr : ∀ {m K a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
         Good m K t₀ → (∀ η d → Good m K (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
         Dom m K a c t₀ g → Dom m K b c (trˢ e t₀) (λ η d → trˢ e (g η d))
Dom-tr {m} {K} z≅ g0 gg et eg h = Dom0-≅ {m′ = m} {K′ = K} g0 gg (trˢ-≅ z≅ et) (λ η d → trˢ-≅ z≅ (eg η d)) h
Dom-tr {m} e@(s≅ _) g0 gg et eg (cv , v) = cv , VisD-tr m e v
Dom-tr {m} e@(l≅ _) g0 gg et eg (cv , v) = cv , VisD-tr m e v

Dom-tr⁻ : ∀ {m K a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
          Good m K t₀ → (∀ η d → Good m K (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
          Dom m K b c t₀ g → Dom m K a c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
Dom-tr⁻ {m} {K} z≅ g0 gg et eg h = Dom0-≅ {m′ = m} {K′ = K} g0 gg (tr⁻ˢ-≅ z≅ et) (λ η d → tr⁻ˢ-≅ z≅ (eg η d)) h
Dom-tr⁻ {m} e@(s≅ _) g0 gg et eg (cv , v) = cv , VisD-tr⁻ m e v
Dom-tr⁻ {m} e@(l≅ _) g0 gg et eg (cv , v) = cv , VisD-tr⁻ m e v

Good-tr    : ∀ {m K a b} (e : a ≅ᴵ b) {x : Ordˢ a} → Good m K x → Good m K (trˢ e x)
Good-tr⁻   : ∀ {m K a b} (e : a ≅ᴵ b) {x : Ordˢ b} → Good m K x → Good m K (tr⁻ˢ e x)
Good-back  : ∀ {m K j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → Good m K u → Good m K (backˢ (resˢ q e) u)
Good-back⁻ : ∀ {m K j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → Good m K u → Good m K (backˢ (res⁻ˢ q e) u)

subT : ∀ {m K j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ a) (z : Ordˢ (repˢ (resˢ q e))) →
       Good m K (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) z)))) →
       Good m K (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) (intoˢ (<→◃ (ltˢ (resˢ q e))) z))))))
subT {m} {K} q e f z g = subst (λ w → Good m K (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) g

subT⁻ : ∀ {m K j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ b) (z : Ordˢ (repˢ (res⁻ˢ q e))) →
        Good m K (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) z)))) →
        Good m K (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) (intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))))))
subT⁻ {m} {K} q e f z g = subst (λ w → Good m K (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) g

monT : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ a) →
       (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
       ∀ {z z′ : Ordˢ (repˢ (resˢ q e))} → z ⊑ᵒ z′ →
       trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) (intoˢ (<→◃ (ltˢ (resˢ q e))) z))))) ⊑ᵒ
       trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) (intoˢ (<→◃ (ltˢ (resˢ q e))) z′)))))
monT q e f hm {z} {z′} h = subst₂ (λ w w′ → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ⊑ᵒ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w′))))
                           (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′))
                           (tr-cong (hm (back-mono q e h)))

monT⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (f : Uˢ j (<→◃ q) → Ordˢ b) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
        ∀ {z z′ : Ordˢ (repˢ (res⁻ˢ q e))} → z ⊑ᵒ z′ →
        tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) (intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))))) ⊑ᵒ
        tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) (intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′)))))
monT⁻ q e f hm {z} {z′} h = subst₂ (λ w w′ → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ⊑ᵒ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w′))))
                            (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′))
                            (tr⁻-cong (hm (back⁻-mono q e h)))

Good-tr e bz         = bz
Good-tr e (bs g)     = bs (Good-tr e g)
Good-tr e (bl hg st) = bl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
Good-tr e (biH {p = q} {f = f} hb hm) = biH
  (λ a h z ez g → subT q e f z (Good-tr e (hb a h (backˢ (resˢ q e) z) (self-back q e ez)
                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g)))))) (monT q e f hm)
Good-tr e (biL {p = q} {f = f} j hb hm) = biL (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) j)
  (λ a h z ez g → subT q e f z (Good-tr e (hb a h (backˢ (resˢ q e) z) (self-back q e ez)
                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g)))))) (monT q e f hm)
Good-tr e (biP {p = q} {f = f} j hb hm) = biP (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) j)
  (λ a h z ez g → subT q e f z (Good-tr e (hb a h (backˢ (resˢ q e) z) (self-back q e ez)
                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g)))))) (monT q e f hm)
Good-tr e (biV {p = q} {f = f} j κ jκ κK tr ab hm) = biV (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) j) κ (⊑ᴵ-≅ˡ (eqˢ (resˢ q e)) jκ) κK
  (λ a h z ez g → subT q e f z (Good-tr e (tr a h (backˢ (resˢ q e) z) (self-back q e ez)
                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g))))))
  (λ z ez gp gv → subT q e f z (Good-tr e (ab (backˢ (resˢ q e) z) (self-back q e ez)
                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) gp)))
                   (λ κj → Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) (gv (⊑ᴵ-≅ʳ κj (eqˢ (resˢ q e))))))))))
  (monT q e f hm)
Good-tr (s≅ e) (bu {r = zero} g)   = bu (Good-tr e g)
Good-tr (l≅ f) (bu {r = self n} g) = bu (Good-tr (f n) g)
Good-tr e (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-tr e g0) (λ η d → Good-tr e (gg η d)) (self-trˢ e et)
     (λ η d η′ d′ eη → trˢ-≅ e (≅-trˢ e (eg η d η′ d′ eη)))
     (λ η d → tr-cong (m η d)) (λ η d η′ d′ h → tr-cong (mm η d η′ d′ h))
     (Dom-tr e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
Good-tr e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-tr e go) (λ η d → Good-tr e (gO η d))
     (λ η d → tr-cong (mo η d)) (λ η d η′ d′ h → tr-cong (mO η d η′ d′ h))

Good-tr⁻ e bz         = bz
Good-tr⁻ e (bs g)     = bs (Good-tr⁻ e g)
Good-tr⁻ e (bl hg st) = bl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
Good-tr⁻ e (biH {p = q} {f = f} hb hm) = biH
  (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (hb a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                   (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g)))))) (monT⁻ q e f hm)
Good-tr⁻ e (biL {p = q} {f = f} j hb hm) = biL (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) j)
  (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (hb a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                   (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g)))))) (monT⁻ q e f hm)
Good-tr⁻ e (biP {p = q} {f = f} j hb hm) = biP (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) j)
  (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (hb a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                   (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g)))))) (monT⁻ q e f hm)
Good-tr⁻ e (biV {p = q} {f = f} j κ jκ κK tr ab hm) = biV (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) j) κ (⊑ᴵ-≅ˡ (eqˢ (res⁻ˢ q e)) jκ) κK
  (λ a h z ez g → subT⁻ q e f z (Good-tr⁻ e (tr a h (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                   (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g))))))
  (λ z ez gp gv → subT⁻ q e f z (Good-tr⁻ e (ab (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                   (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) gp)))
                   (λ κj → Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) (gv (⊑ᴵ-≅ʳ κj (eqˢ (res⁻ˢ q e))))))))))
  (monT⁻ q e f hm)
Good-tr⁻ (s≅ e) (bu {r = zero} g)   = bu (Good-tr⁻ e g)
Good-tr⁻ (l≅ f) (bu {r = self n} g) = bu (Good-tr⁻ (f n) g)
Good-tr⁻ e (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-tr⁻ e g0) (λ η d → Good-tr⁻ e (gg η d)) (self-tr⁻ˢ e et)
     (λ η d η′ d′ eη → tr⁻ˢ-≅ e (≅-tr⁻ˢ e (eg η d η′ d′ eη)))
     (λ η d → tr⁻-cong (m η d)) (λ η d η′ d′ h → tr⁻-cong (mm η d η′ d′ h))
     (Dom-tr⁻ e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
Good-tr⁻ e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-tr⁻ e go) (λ η d → Good-tr⁻ e (gO η d))
     (λ η d → tr⁻-cong (mo η d)) (λ η d η′ d′ h → tr⁻-cong (mO η d η′ d′ h))

Good-back zero      (s≅ e) g = Good-tr⁻ e g
Good-back (suc q)   (s≅ e) g = Good-back q e g
Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

Good-back⁻ zero      (s≅ e) g = Good-tr e g
Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g
```

## §4 加法

`Good-add`: 前缀与尾巴同模式 (`mC`/`mP`), 不要地板. **`V-add`**: 前缀可见且地板 $\sqsupseteq\Omega_{a_0}$, 尾巴只要悬置水位 $\sqsubseteq a_0$: 前缀把悬置的闭包托起, 输出的 `biV` 的 $\kappa$ 取 $a_0$. `Good-add₀`: 第 0 层, 没有节点, 闭包都已封住, 水位无关.

```agda
NV : Mode → Set
NV mC = ⊤
NV mP = ⊤
NV mV = ⊥

NV-vis : ∀ m {ℓ c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → NV m → VisD m c t₀ g
NV-vis mC nv = tt
NV-vis mP nv = tt

subA : ∀ {m K j k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) (z : Ordˢ j) →
       Good m K (addˢ a σ (f (intoˢ (<→◃ q) z))) →
       Good m K (addˢ a σ (f (intoˢ (<→◃ q) (outˢ (<→◃ (σ q)) (intoˢ (<→◃ (σ q)) z)))))
subA {m} {K} {a = a} {σ = σ} q f z g = subst (λ u → Good m K (addˢ a σ (f (intoˢ (<→◃ q) u)))) (sym (out-intoˢ (<→◃ (σ q)) z)) g

monA : ∀ {j k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → a ≅ˢ a →
       (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
       ∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ →
       addˢ a σ (f (intoˢ (<→◃ q) (outˢ (<→◃ (σ q)) (intoˢ (<→◃ (σ q)) z)))) ⊑ᵒ
       addˢ a σ (f (intoˢ (<→◃ q) (outˢ (<→◃ (σ q)) (intoˢ (<→◃ (σ q)) z′))))
monA {a = a} {σ = σ} q f ea hm {z} {z′} h =
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) v)))
         (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong refl ea (hm h))

Good-add : ∀ {m K k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → NV m → NZ ℓ → Good m K a → a ≅ˢ a → Good m K b → Good m K (addˢ a σ b)
Good-add nv nz ga ea bz          = ga
Good-add nv nz ga ea (bs g)      = bs (Good-add nv nz ga ea g)
Good-add nv nz ga ea (bl hg st)  = bl (λ n → Good-add nv nz ga ea (hg n)) (λ n → add-cong refl ea (st n))
Good-add {σ = σ} nv nz ga ea (biH {p = q} {f = f} hb hm) = biH
  (λ a h z ez g → subA {σ = σ} q f z (Good-add nv nz (Good-mono h ga) ea (hb a h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (monA {σ = σ} q f ea hm)
Good-add {σ = σ} nv nz ga ea (biL {p = q} {f = f} j hb hm) = biL j
  (λ a h z ez g → subA {σ = σ} q f z (Good-add nv nz (Good-mono h ga) ea (hb a h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (monA {σ = σ} q f ea hm)
Good-add {σ = σ} nv nz ga ea (biP {p = q} {f = f} j hb hm) = biP j
  (λ a h z ez g → subA {σ = σ} q f z (Good-add nv nz (Good-mono h ga) ea (hb a h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (monA {σ = σ} q f ea hm)
Good-add () nz ga ea (biV j κ jκ κK tr ab hm)
Good-add nv nz ga ea (bu {r = zero} g)   = Good-add nv nz ga ea g
Good-add nv nz ga ea (bu {r = self n} g) = Good-add nv nz ga ea g
Good-add {k = zero} nv nz ga ea (bŝ g0 gg et eg m mm dm) =
  bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
     (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
     (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
  where
  G₀ = Good→Goodᶻ g0
  Gg = λ η e → Good→Goodᶻ (gg η e)
Good-add {k = suc _} {ℓ = zero} nv () ga ea (bŝ g0 gg et eg m mm dm)
Good-add {m = md} {k = suc _} {ℓ = suc _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
  bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
Good-add {m = md} {k = suc _} {ℓ = lim _ _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
  bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
Good-add {k = lim _ _} {ℓ = zero} nv () ga ea (bŝ g0 gg et eg m mm dm)
Good-add {m = md} {k = lim _ _} {ℓ = suc _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
  bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
Good-add {m = md} {k = lim _ _} {ℓ = lim _ _} nv nz ga ea (bŝ g0 gg et eg m mm (cv , _)) =
  bŝ (Good-add nv nz ga ea g0) (λ η e → Good-add nv nz ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) (cv , NV-vis md nv)
Good-add nv nz ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-add nv nz ga ea go) (λ η e → Good-add nv nz ga ea (gO η e))
     (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

Good-add₀ : ∀ {m K K′} {a : Ordˢ zero} {σ : Simᴵ zero zero} {b : Ordˢ zero} → Good m K a → a ≅ˢ a → Good m K′ b → Good m K (addˢ a σ b)
Good-add₀ ga ea bz          = ga
Good-add₀ ga ea (bs g)      = bs (Good-add₀ ga ea g)
Good-add₀ ga ea (bl hg st)  = bl (λ n → Good-add₀ ga ea (hg n)) (λ n → add-cong refl ea (st n))
Good-add₀ ga ea (biH {p = ()} hb hm)
Good-add₀ ga ea (biL {p = ()} j hb hm)
Good-add₀ ga ea (biP {p = ()} j hb hm)
Good-add₀ ga ea (biV {p = ()} j κ jκ κK tr ab hm)
Good-add₀ ga ea (bu {r = ()} g)
Good-add₀ ga ea (bŝ g0 gg et eg m mm dm) =
  bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
     (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
     (Good-add₀ ga ea g0) (λ η e → Good-add₀ ga ea (gg η e))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
  where
  G₀ = Good→Goodᶻ g0
  Gg = λ η e → Good→Goodᶻ (gg η e)
Good-add₀ ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-add₀ ga ea go) (λ η e → Good-add₀ ga ea (gO η e))
     (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

V-add : ∀ {K a₀ k ℓ} {c : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → NZ ℓ → Good mV a₀ c → (∀ {φ} → φ ⊑ᴵ a₀ → FlΛ φ c) → c ≅ˢ c →
        K ⊑ᴵ a₀ → Good mP K b → b ≅ˢ b → Good mV a₀ (addˢ c σ b)
V-add nz gc fc ec h bz eb       = gc
V-add nz gc fc ec h (bs g) eb   = bs (V-add nz gc fc ec h g (s-invˢ eb))
V-add nz gc fc ec h (bl hg st) eb = bl (λ n → V-add nz gc fc ec h (hg n) (l-invˢ eb n)) (λ n → add-cong refl ec (st n))
V-add {a₀ = a₀} {σ = σ} nz gc fc ec h (biP {p = q} {f = f} j tr hm) eb = biV (⊑ᴵ-trans j h) a₀ (⊑ᴵ-trans j h) ⊑ᴵ-refl
  (λ a k z ez g → subA {σ = σ} q f z (Good-add tt nz (Good-mono k (V→P gc)) ec (tr a (⊑ᴵ-trans h k) z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (λ z ez gp gv → subA {σ = σ} q f z (V-add nz gc fc ec ⊑ᴵ-refl (tr a₀ h z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) gp)) (i-respˢ eb ez)))
  (monA {σ = σ} q f ec hm)
V-add nz gc fc ec h (bu {r = zero} g) eb   = V-add nz gc fc ec h g (u-reflˢ zero eb)
V-add nz gc fc ec h (bu {r = self n} g) eb = V-add nz gc fc ec h g (u-reflˢ (self n) eb)
V-add {k = zero} nz gc fc ec h (bŝ g0 gg et eg m mm dm) eb =
  bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
     (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h′ → mm η e η′ e′ h′ idO (Gg η e) (Gg η′ e′))
     (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
  where
  G₀ = Good→Goodᶻ g0
  Gg = λ η e → Good→Goodᶻ (gg η e)
V-add {k = suc _} {ℓ = zero} () gc fc ec h (bŝ g0 gg et eg m mm dm) eb
V-add {k = suc _} {ℓ = suc _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
  bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
     (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
     (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
V-add {k = suc _} {ℓ = lim _ _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
  bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
     (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
     (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
V-add {k = lim _ _} {ℓ = zero} () gc fc ec h (bŝ g0 gg et eg m mm dm) eb
V-add {k = lim _ _} {ℓ = suc _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
  bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
     (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
     (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
V-add {k = lim _ _} {ℓ = lim _ _} nz gc fc ec h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) eb =
  bŝ (V-add nz gc fc ec h g0 et) (λ η e → V-add nz gc fc ec h (gg η e) (eg η e η e (≅ᴵ-refl η))) (addˢ-≅ refl ec et)
     (λ η e η′ e′ eη → addˢ-≅ refl ec (eg η e η′ e′ eη))
     (λ η e → add-cong refl ec (m η e)) (λ η e η′ e′ h′ → add-cong refl ec (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-add t₀ (fc (⊑ᴵ-trans φK h)) et) cv , λ η e → dom-cov (FlΛ-add (g η e) (fc (⊑ᴵ-trans φK h)) (eg η e η e (≅ᴵ-refl η))) cv)
V-add nz gc fc ec h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) eb =
  bĉ G₀ Gg d₀ dE m₀ mE (V-add nz gc fc ec h go (ĉ-refl₀ eb)) (λ η e → V-add nz gc fc ec h (gO η e) (ĉ-reflg eb η e))
     (λ η e → add-cong refl ec (mo η e)) (λ η e η′ e′ h′ → add-cong refl ec (mO η e η′ e′ h′))

Good-iter : ∀ {m K ℓ} {c : Ordˢ ℓ} → NV m → NZ ℓ → Good m K c → c ≅ˢ c → ∀ n → Good m K (iter (c +ˢ_) Ord₊ˢ.zero n)
Good-iter nv nz gc ec zero    = bz
Good-iter nv nz gc ec (suc n) = Good-add nv nz gc ec (Good-iter nv nz gc ec n)

V-iter : ∀ {a₀ ℓ} {c : Ordˢ ℓ} → NZ ℓ → Good mV a₀ c → (∀ {φ} → φ ⊑ᴵ a₀ → FlΛ φ c) → c ≅ˢ c → ∀ n →
         Good mV a₀ (iter (c +ˢ_) Ord₊ˢ.zero n) × (iter (c +ˢ_) Ord₊ˢ.zero n ≅ˢ iter (c +ˢ_) Ord₊ˢ.zero n)
V-iter nz gc fc ec zero    = bz , z≅
V-iter nz gc fc ec (suc n) = V-add nz gc fc ec ⊑ᴵ-refl (V→P (proj₁ (V-iter nz gc fc ec n))) (proj₂ (V-iter nz gc fc ec n))
                           , addˢ-≅ refl ec (proj₂ (V-iter nz gc fc ec n))

Good-iter₀ : ∀ {m K} {c : Ordˢ zero} → Good m K c → c ≅ˢ c → ∀ n → Good m K (iter (c +ˢ_) Ord₊ˢ.zero n)
Good-iter₀ gc ec zero    = bz
Good-iter₀ gc ec (suc n) = Good-add₀ gc ec (Good-iter₀ gc ec n)
```

## §5 $\psi^{[]}$: 只搬运闭包, 不产生闭包

`C-ψ0`: 目标任意 (非零), `mC K` 到 `mC K`. `P-ψ0`: 目标 $\sqsubseteq K$, 输出 `mP K` (输出的节点 $<$ 目标). `V-ψ0`: 水位 $\sqsubseteq$ 目标, 输出可见, 地板经 `FlΛ-ψ0` 再生. `Z-ψ0`: 目标 0, 沿用 Stage2Label 的 `Ok` 排除闭包; 节点 0 的链递归回 `Z-ψ0`.

```agda
NZ-≺ : ∀ {i j} → i ≺ᴵ j → NZ j
NZ-≺ {j = suc _}   _ = tt
NZ-≺ {j = lim _ _} _ = tt
NZ-≺ {j = zero} (via e ())

NZ-≅ : ∀ {i j} → NZ i → j ≅ᴵ i → NZ j
NZ-≅ {j = suc _}   nz e = tt
NZ-≅ {j = lim _ _} nz e = tt
NZ-≅ {j = zero} () z≅

<→⊑ : ∀ {a b} → a <ᴵ b → a ⊑ᴵ b
<→⊑ {a} r = ⊑ᴵ-trans (Sim→⊑ᴵ (λ q → suc q)) (s⊑′ (via (≅ᴵ-refl a) r))

mkĉ : ∀ {m K m′ K′ ℓ c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
      Good m′ K′ t₀ → (∀ η e → Good m′ K′ (g η e)) → (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
      Dom m′ K′ zero c t₀ g → Good m K o₀ → (∀ η e → Good m K (o η e)) →
      (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
      Good m K (Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) o₀ o)
mkĉ g0 gg m mm (d₀ , dE) go gO mo mO =
  bĉ G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
     (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
     go gO mo mO
  where
  G₀ = Good→Goodᶻ g0
  Gg = λ η e → Good→Goodᶻ (gg η e)

subψ0 : ∀ {m K i j b k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} (f : Uˢ j (<→◃ q) → Ordˢ k) (e : j ≅ᴵ b) (r : b <ᴵ i) (z : Ordˢ b) →
        Good m K (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e z)))) →
        Good m K (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) (intoˢ (<→◃ r) z))))))
subψ0 {m} {K} {p = p} {σ = σ} {q = q} f e r z g = subst (λ u → Good m K (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) z)) g

monψ0 : ∀ {i j b k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} (f : Uˢ j (<→◃ q) → Ordˢ k) (e : j ≅ᴵ b) (r : b <ᴵ i) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
        ∀ {z z′ : Ordˢ b} → z ⊑ᵒ z′ →
        ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) (intoˢ (<→◃ r) z))))) ⊑ᵒ
        ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) (intoˢ (<→◃ r) z′)))))
monψ0 {p = p} {σ = σ} {q = q} f e r hm {z} {z′} h =
  subst₂ (λ u v → ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
         (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (ψ0-cong (hm (tr⁻-cong h)))

inb : ∀ {m m′ K j b k k′} (cv : ∀ {ℓ} {x : Ordˢ ℓ} → Good m K x → Good m′ K x) {q : j <ᴵ k} {r : b <ᴵ k′} (e : j ≅ᴵ b) {z : Ordˢ b} →
      Gd m K b (<→◃ r) (intoˢ (<→◃ r) z) → Gd m′ K j (<→◃ q) (intoˢ (<→◃ q) (tr⁻ˢ e z))
inb cv {q} {r} e g = Good→Gd (<→◃ q) (cv (Good-tr⁻ e (Gd→Good (<→◃ r) g)))

C-ψ0 : ∀ {K i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → NZ i → Good mC K x → x ≅ˢ x → Good mC K (ψ0 p σ x)
P-ψ0 : ∀ {K i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → NZ i → i ⊑ᴵ K → Good mC K x → x ≅ˢ x → Good mP K (ψ0 p σ x)
chainH : ∀ {K a j k ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → NZ j → K ⊑ᴵ a →
         (∀ a′ → K ⊑ᴵ a′ → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd mC a′ j (<→◃ q) (intoˢ (<→◃ q) z) → Good mC a′ (f (intoˢ (<→◃ q) z))) →
         Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mC a (chain0 σ q f n)
chainL : ∀ {K a j k ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → NZ j → j ⊑ᴵ a → K ⊑ᴵ a →
         (∀ a′ → K ⊑ᴵ a′ → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd mP a′ j (<→◃ q) (intoˢ (<→◃ q) z) → Good mC a′ (f (intoˢ (<→◃ q) z))) →
         Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mP a (chain0 σ q f n)

chainH {a = a} {j = j} nj h hb e zero = Good-Ωᶜ j a
chainH {a = a} {σ = σ} {q = q} {f = f} nj h hb e (suc n) =
  C-ψ0 {p = σ q} {σ = σ} nj (hb a h (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainH nj h hb e n))) (i-respˢ e (chain0-≅ e n))
chainL {j = j} nj ja h hb e zero = Good-Ωᴾ j ja
chainL {a = a} {σ = σ} {q = q} {f = f} nj ja h hb e (suc n) =
  P-ψ0 {p = σ q} {σ = σ} nj ja (hb a h (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainL nj ja h hb e n))) (i-respˢ e (chain0-≅ e n))

C-ψ0 {K} {i} nz bz ex = Good-Ωᶜ i K
C-ψ0 {i = i} {p = p} {σ = σ} nz (bs g) ex =
  bl (Good-iter tt nz (C-ψ0 nz g ea) eψ) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ0-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
C-ψ0 nz (bl hg st) ex = bl (λ n → C-ψ0 nz (hg n) (l-invˢ ex n)) (λ n → ψ0-cong (st n))
C-ψ0 {p = p} {σ = σ} nz (biH {K} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = biH
  (λ a h z ez g → subψ0 {p = p} {σ = σ} {q = q} f e r z (C-ψ0 nz (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (monψ0 {p = p} {σ = σ} {q = q} f e r hm)
... | injᵇ c = bl (λ n → C-ψ0 nz (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainH (NZ-≺ c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → C-ψ0 nz (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainH (NZ-≅ nz c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
C-ψ0 {p = p} {σ = σ} nz (biL {K} {p = q} {f = f} j hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = biL (⊑ᴵ-≅ˡ e j)
  (λ a h z ez g → subψ0 {p = p} {σ = σ} {q = q} f e r z (C-ψ0 nz (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (monψ0 {p = p} {σ = σ} {q = q} f e r hm)
... | injᵇ c = bl (λ n → C-ψ0 nz (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainL (NZ-≺ c) j ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → C-ψ0 nz (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainL (NZ-≅ nz c) j ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
C-ψ0 nz (bu {r = zero} g) ex   = C-ψ0 nz g (u-reflˢ zero ex)
C-ψ0 nz (bu {r = self n} g) ex = C-ψ0 nz g (u-reflˢ (self n) ex)
C-ψ0 {i = suc _} {k = zero} nz (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (C-ψ0 nz g0 et) (λ η e → C-ψ0 nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
C-ψ0 {i = suc _} {k = suc _} {p = p} {σ = σ} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (C-ψ0 nz g0 et) (λ η e → C-ψ0 nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
C-ψ0 {i = suc _} {k = lim _ _} {p = p} {σ = σ} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (C-ψ0 nz g0 et) (λ η e → C-ψ0 nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
C-ψ0 {i = lim _ _} {k = zero} nz (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (C-ψ0 nz g0 et) (λ η e → C-ψ0 nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
C-ψ0 {i = lim _ _} {k = suc _} {p = p} {σ = σ} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (C-ψ0 nz g0 et) (λ η e → C-ψ0 nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
C-ψ0 {i = lim _ _} {k = lim _ _} {p = p} {σ = σ} nz (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (C-ψ0 nz g0 et) (λ η e → C-ψ0 nz (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
C-ψ0 nz (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
  bĉ G₀ Gg d₀ dE m₀ mE (C-ψ0 nz go (ĉ-refl₀ ex)) (λ η e → C-ψ0 nz (gO η e) (ĉ-reflg ex η e))
     (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))

P-ψ0 {i = i} nz ik bz ex = Good-Ωᴾ i ik
P-ψ0 {i = i} {p = p} {σ = σ} nz ik (bs g) ex =
  bl (Good-iter tt nz (P-ψ0 nz ik g ea) eψ) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ0-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
P-ψ0 nz ik (bl hg st) ex = bl (λ n → P-ψ0 nz ik (hg n) (l-invˢ ex n)) (λ n → ψ0-cong (st n))
P-ψ0 {p = p} {σ = σ} nz ik (biH {K} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = biP (⊑ᴵ-trans (<→⊑ r) ik)
  (λ a h z ez g → subψ0 {p = p} {σ = σ} {q = q} f e r z (P-ψ0 nz (⊑ᴵ-trans ik h) (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb P→C {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (monψ0 {p = p} {σ = σ} {q = q} f e r hm)
... | injᵇ c = bl (λ n → P-ψ0 nz ik (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainH (NZ-≺ c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → P-ψ0 nz ik (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainH (NZ-≅ nz c) ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
P-ψ0 {p = p} {σ = σ} nz ik (biL {K} {p = q} {f = f} j hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = biP (⊑ᴵ-≅ˡ e j)
  (λ a h z ez g → subψ0 {p = p} {σ = σ} {q = q} f e r z (P-ψ0 nz (⊑ᴵ-trans ik h) (hb a h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (monψ0 {p = p} {σ = σ} {q = q} f e r hm)
... | injᵇ c = bl (λ n → P-ψ0 nz ik (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainL (NZ-≺ c) j ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → P-ψ0 nz ik (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainL (NZ-≅ nz c) j ⊑ᴵ-refl hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
P-ψ0 nz ik (bu {r = zero} g) ex   = P-ψ0 nz ik g (u-reflˢ zero ex)
P-ψ0 nz ik (bu {r = self n} g) ex = P-ψ0 nz ik g (u-reflˢ (self n) ex)
P-ψ0 {i = suc _} {k = zero} nz ik (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (P-ψ0 nz ik g0 et) (λ η e → P-ψ0 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
P-ψ0 {i = suc _} {k = suc _} {p = p} {σ = σ} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (P-ψ0 nz ik g0 et) (λ η e → P-ψ0 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
P-ψ0 {i = suc _} {k = lim _ _} {p = p} {σ = σ} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (P-ψ0 nz ik g0 et) (λ η e → P-ψ0 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
P-ψ0 {i = lim _ _} {k = zero} nz ik (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (P-ψ0 nz ik g0 et) (λ η e → P-ψ0 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
P-ψ0 {i = lim _ _} {k = suc _} {p = p} {σ = σ} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (P-ψ0 nz ik g0 et) (λ η e → P-ψ0 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
P-ψ0 {i = lim _ _} {k = lim _ _} {p = p} {σ = σ} nz ik (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (P-ψ0 nz ik g0 et) (λ η e → P-ψ0 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
     ((φ , cv , φK) , tt)
P-ψ0 nz ik (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
  bĉ G₀ Gg d₀ dE m₀ mE (P-ψ0 nz ik go (ĉ-refl₀ ex)) (λ η e → P-ψ0 nz ik (gO η e) (ĉ-reflg ex η e))
     (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
```

```agda
V-ψ0 : ∀ {K a k ℓ} {p : a <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → NZ a → K ⊑ᴵ a → Good mC K x → x ≅ˢ x → Good mV a (ψ0 p σ x)
V-ψ0 {a = a} nz h bz ex = Good-Ωⱽ a ⊑ᴵ-refl
V-ψ0 {a = a} {p = p} {σ = σ} nz h (bs {a = y} g) ex =
  bl (λ n → proj₁ (V-iter nz (V-ψ0 nz h g ea) (λ h′ → FlΛ-ψ0 {p = p} {σ = σ} h′ y ea) eψ n)) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ0-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl a) ea
V-ψ0 nz h (bl hg st) ex = bl (λ n → V-ψ0 nz h (hg n) (l-invˢ ex n)) (λ n → ψ0-cong (st n))
V-ψ0 {a = a₀} {p = p} {σ = σ} nz h (biH {K} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = biV (<→⊑ r) a₀ (<→⊑ r) ⊑ᴵ-refl
  (λ a k z ez g → subψ0 {p = p} {σ = σ} {q = q} f e r z (P-ψ0 nz k (hb a (⊑ᴵ-trans h k) (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb P→C {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (λ z ez gp gv → subψ0 {p = p} {σ = σ} {q = q} f e r z (V-ψ0 nz ⊑ᴵ-refl (hb a₀ h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb P→C {q = q} {r = r} e gp)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (monψ0 {p = p} {σ = σ} {q = q} f e r hm)
... | injᵇ c = bl (λ n → V-ψ0 nz ⊑ᴵ-refl (hb a₀ h (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainH (NZ-≺ c) h hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → V-ψ0 nz ⊑ᴵ-refl (hb a₀ h (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainH (NZ-≅ nz c) h hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
V-ψ0 {a = a₀} {p = p} {σ = σ} nz h (biL {K} {p = q} {f = f} j hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = biV (<→⊑ r) a₀ (<→⊑ r) ⊑ᴵ-refl
  (λ a k z ez g → subψ0 {p = p} {σ = σ} {q = q} f e r z (P-ψ0 nz k (hb a (⊑ᴵ-trans h k) (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (λ z ez gp gv → subψ0 {p = p} {σ = σ} {q = q} f e r z (V-ψ0 nz ⊑ᴵ-refl (hb a₀ h (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (inb (λ x → x) {q = q} {r = r} e gp)) (i-respˢ ex (self-tr⁻ˢ e ez))))
  (monψ0 {p = p} {σ = σ} {q = q} f e r hm)
... | injᵇ c = bl (λ n → V-ψ0 nz ⊑ᴵ-refl (hb a₀ h (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainL (NZ-≺ c) (⊑ᴵ-trans j h) h hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → V-ψ0 nz ⊑ᴵ-refl (hb a₀ h (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainL (NZ-≅ nz c) (⊑ᴵ-trans j h) h hb ex n))) (i-respˢ ex (chain0-≅ ex n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
V-ψ0 nz h (bu {r = zero} g) ex   = V-ψ0 nz h g (u-reflˢ zero ex)
V-ψ0 nz h (bu {r = self n} g) ex = V-ψ0 nz h g (u-reflˢ (self n) ex)
V-ψ0 {a = suc _} {k = zero} nz h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (V-ψ0 nz h g0 et) (λ η e → V-ψ0 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h′ → ψ0-cong (mm η e η′ e′ h′))
V-ψ0 {a = suc _} {k = suc _} {p = p} {σ = σ} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (V-ψ0 nz h g0 et) (λ η e → V-ψ0 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h′ → ψ0-cong (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) t₀ et) cv ,
       λ η e → dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
V-ψ0 {a = suc _} {k = lim _ _} {p = p} {σ = σ} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (V-ψ0 nz h g0 et) (λ η e → V-ψ0 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h′ → ψ0-cong (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) t₀ et) cv ,
       λ η e → dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
V-ψ0 {a = lim _ _} {k = zero} nz h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (V-ψ0 nz h g0 et) (λ η e → V-ψ0 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h′ → ψ0-cong (mm η e η′ e′ h′))
V-ψ0 {a = lim _ _} {k = suc _} {p = p} {σ = σ} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (V-ψ0 nz h g0 et) (λ η e → V-ψ0 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h′ → ψ0-cong (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) t₀ et) cv ,
       λ η e → dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
V-ψ0 {a = lim _ _} {k = lim _ _} {p = p} {σ = σ} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
  bŝ (V-ψ0 nz h g0 et) (λ η e → V-ψ0 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h′ → ψ0-cong (mm η e η′ e′ h′))
     ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) t₀ et) cv ,
       λ η e → dom-cov (FlΛ-ψ0 {p = p} {σ = σ} (⊑ᴵ-trans φK h) (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
V-ψ0 nz h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
  bĉ G₀ Gg d₀ dE m₀ mE (V-ψ0 nz h go (ĉ-refl₀ ex)) (λ η e → V-ψ0 nz h (gO η e) (ĉ-reflg ex η e))
     (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h′ → ψ0-cong (mO η e η′ e′ h′))

Z-ψ0 : ∀ {K} (K′ : Ordᴵ) {k ℓ} {p : zero <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → Good mC K x → x ≅ˢ x → Ok zero x → Good mV K′ (ψ0 p σ x)
chainZH : ∀ {K j k ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
          (∀ a′ → K ⊑ᴵ a′ → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd mC a′ j (<→◃ q) (intoˢ (<→◃ q) z) → Good mC a′ (f (intoˢ (<→◃ q) z))) →
          Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → (∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n)))) → ∀ n → Good mC K (chain0 σ q f n)
chainZL : ∀ {K j k ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → j ⊑ᴵ K →
          (∀ a′ → K ⊑ᴵ a′ → ∀ (z : Ordˢ j) → z ≅ˢ z → Gd mP a′ j (<→◃ q) (intoˢ (<→◃ q) z) → Good mC a′ (f (intoˢ (<→◃ q) z))) →
          Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → (∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n)))) → ∀ n → Good mP K (chain0 σ q f n)

chainZH {K} {j} hb e ok zero = Good-Ωᶜ j K
chainZH {K} {j = zero} {σ = σ} {q = q} {f = f} hb e ok (suc n) =
  P→C (V→P (Z-ψ0 K {p = σ q} {σ = σ} (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainZH hb e ok n))) (i-respˢ e (chain0-≅ e n)) (ok n)))
chainZH {K} {j = suc _} {σ = σ} {q = q} {f = f} hb e ok (suc n) =
  C-ψ0 {p = σ q} {σ = σ} tt (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainZH hb e ok n))) (i-respˢ e (chain0-≅ e n))
chainZH {K} {j = lim _ _} {σ = σ} {q = q} {f = f} hb e ok (suc n) =
  C-ψ0 {p = σ q} {σ = σ} tt (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainZH hb e ok n))) (i-respˢ e (chain0-≅ e n))

chainZL {j = j} jK hb e ok zero = Good-Ωᴾ j jK
chainZL {K} {j = zero} {σ = σ} {q = q} {f = f} jK hb e ok (suc n) =
  V→P (Z-ψ0 K {p = σ q} {σ = σ} (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainZL jK hb e ok n))) (i-respˢ e (chain0-≅ e n)) (ok n))
chainZL {K} {j = suc _} {σ = σ} {q = q} {f = f} jK hb e ok (suc n) =
  P-ψ0 {p = σ q} {σ = σ} tt jK (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainZL jK hb e ok n))) (i-respˢ e (chain0-≅ e n))
chainZL {K} {j = lim _ _} {σ = σ} {q = q} {f = f} jK hb e ok (suc n) =
  P-ψ0 {p = σ q} {σ = σ} tt jK (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chainZL jK hb e ok n))) (i-respˢ e (chain0-≅ e n))

Z-ψ0 K′ bz ex ok = Good-Ωⱽ zero z⊑
Z-ψ0 K′ {p = p} {σ = σ} (bs g) ex ok = bl (Good-iter₀ (Z-ψ0 K′ g ea (Ok-suc zero ok)) eψ) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ0-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl zero) ea
Z-ψ0 K′ (bl hg st) ex ok = bl (λ n → Z-ψ0 K′ (hg n) (l-invˢ ex n) (Ok-lim zero ok n)) (λ n → ψ0-cong (st n))
Z-ψ0 K′ {p = p} {σ = σ} (biH {K} {p = q} {f = f} hb hm) ex ok with <ᴵ-dec (σ q) p
... | injᵃ (via e ())
... | injᵇ c = bl (λ n → Z-ψ0 K′ (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainZH hb ex (λ m → proj₁ (Ok-col σ (inj₁ c) ok m)) n)))
                                 (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₁ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → Z-ψ0 K′ (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainZH hb ex (λ m → proj₁ (Ok-col σ (inj₂ c) ok m)) n)))
                                 (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₂ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
Z-ψ0 K′ {p = p} {σ = σ} (biL {K} {p = q} {f = f} j hb hm) ex ok with <ᴵ-dec (σ q) p
... | injᵃ (via e ())
... | injᵇ c = bl (λ n → Z-ψ0 K′ (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainZL j hb ex (λ m → proj₁ (Ok-col σ (inj₁ c) ok m)) n)))
                                 (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₁ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → Z-ψ0 K′ (hb K ⊑ᴵ-refl (chain0 σ q f n) (chain0-≅ ex n) (Good→Gd (<→◃ q) (chainZL j hb ex (λ m → proj₁ (Ok-col σ (inj₂ c) ok m)) n)))
                                 (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₂ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
Z-ψ0 K′ (bu {r = zero} g) ex ok   = Z-ψ0 K′ g (u-reflˢ zero ex) (Ok-up zero zero ok)
Z-ψ0 K′ (bu {r = self n} g) ex ok = Z-ψ0 K′ g (u-reflˢ (self n) ex) (Ok-up zero (self n) ok)
Z-ψ0 K′ (bŝ g0 gg et eg m mm dm) ex (_ , _ , d) = ⊥-elim (~ŝ d)
Z-ψ0 K′ (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex (_ , _ , d) = ⊥-elim (~ĉ d)
```

## §6 $\psi^{[\hat\Omega]}$: 目标非零

`PopCov ℓ`: 环境 $\ell$ 里每个非零目标 $i$ 弹出的闭包 (界 $i+1$) 有覆盖 $\varphi\sqsubseteq i$. **这是闭包定理唯一的外部数据.** `P-ψ1` 的折叠链在水位 $K$ 内 (节点 $\sqsubseteq K$). `V-ψ1` 穿透时输出 `biV` 且 $\kappa$ 取目标: 这正是吸收的来源; 折叠时链停在目标水位.

```agda
PopCov : Ordᴵ → Set
PopCov ℓ = ∀ {i} → i <ᴵ ℓ → NZ i → Cvd i (suc i)

popG : ∀ {m K i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) →
       Good m K (t₀pop p z) → (∀ η e → Good m K (gpop p z η e)) → Dom m K i (suc i) (t₀pop p z) (gpop p z) →
       Good m K (ψ1 p σ z Ord₊ˢ.zero)
popG {i = i} p σ z g0 gg dm =
  bŝ g0 gg (ψ0-≅ (≅ᴵ-refl i) (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl i) (Ωˢ-≅ eη))
     (λ η e → ψ0-cong (Ω-monoᵒ (⊑ᴵ-trans (s⊑ z≅ (z<suc z p)) e))) (λ η e η′ e′ h → ψ0-cong (Ω-monoᵒ h)) dm

subψ1 : ∀ {m K i j b k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z₀ : zero <ᴵ ℓ} {q : j <ᴵ k} (f : Uˢ j (<→◃ q) → Ordˢ k) (e : j ≅ᴵ b) (r : b <ᴵ i) (y : Ordˢ b) →
        Good m K (ψ1 p σ z₀ (f (intoˢ (<→◃ q) (tr⁻ˢ e y)))) →
        Good m K (ψ1 p σ z₀ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) (intoˢ (<→◃ r) y))))))
subψ1 {m} {K} {p = p} {σ = σ} {z₀ = z₀} {q = q} f e r y g = subst (λ u → Good m K (ψ1 p σ z₀ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) y)) g

monψ1 : ∀ {i j b k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z₀ : zero <ᴵ ℓ} {q : j <ᴵ k} (f : Uˢ j (<→◃ q) → Ordˢ k) (e : j ≅ᴵ b) (r : b <ᴵ i) →
        (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
        ∀ {y y′ : Ordˢ b} → y ⊑ᵒ y′ →
        ψ1 p σ z₀ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) (intoˢ (<→◃ r) y))))) ⊑ᵒ
        ψ1 p σ z₀ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) (intoˢ (<→◃ r) y′)))))
monψ1 {p = p} {σ = σ} {z₀ = z₀} {q = q} f e r hm {y} {y′} h =
  subst₂ (λ u v → ψ1 p σ z₀ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ1 p σ z₀ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
         (sym (out-intoˢ (<→◃ r) y)) (sym (out-intoˢ (<→◃ r) y′)) (ψ1-cong (hm (tr⁻-cong h)))

module Fold {ℓ : Ordᴵ} (pc : PopCov ℓ) where
  P-ψ1 : ∀ {K i k} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → NZ i → i ⊑ᴵ K → Good mP K x → x ≅ˢ x → Good mP K (ψ1 p σ z x)
  V-ψ1 : ∀ {K a k} {p : a <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → NZ a → K ⊑ᴵ a → Good mP K x → x ≅ˢ x → Good mV a (ψ1 p σ z x)
  chain1P : ∀ {K a j k} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → NZ j → j ⊑ᴵ a → K ⊑ᴵ a →
            (∀ a′ → K ⊑ᴵ a′ → ∀ (y : Ordˢ j) → y ≅ˢ y → Gd mP a′ j (<→◃ q) (intoˢ (<→◃ q) y) → Good mP a′ (f (intoˢ (<→◃ q) y))) →
            Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mP a (chain1 σ z q f n)

  chain1P {j = j} nj ja h tr e zero = Good-Ωᴾ j ja
  chain1P {a = a} {σ = σ} {z = z} {q = q} {f = f} nj ja h tr e (suc n) =
    P-ψ1 {p = σ q} {σ = σ} {z = z} nj ja (tr a h (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (chain1P nj ja h tr e n))) (i-respˢ e (chain1-≅ e n))

  P-ψ1 {K} {suc i₀} {p = p} {σ = σ} {z = z} nz ik bz ex with pc p nz
  ... | (φ , cv , φi) = popG p σ z (P-ψ0 {p = zero} {σ = σ1 (z<suc z p)} nz ik (Good-Ωᶜ (suc zero) K) (Ωˢ-refl (suc zero)))
                                  (λ η e → P-ψ0 {p = lim 0 zero} {σ = λ q → lim 1 q} nz ik (Good-Ωᶜ η K) (Ωˢ-refl η))
                                  ((φ , cv , ⊑ᴵ-trans φi ik) , tt)
  P-ψ1 {K} {lim _ _} {p = p} {σ = σ} {z = z} nz ik bz ex with pc p nz
  ... | (φ , cv , φi) = popG p σ z (P-ψ0 {p = zero} {σ = σ1 (z<suc z p)} nz ik (Good-Ωᶜ (suc zero) K) (Ωˢ-refl (suc zero)))
                                  (λ η e → P-ψ0 {p = lim 0 zero} {σ = λ q → lim 1 q} nz ik (Good-Ωᶜ η K) (Ωˢ-refl η))
                                  ((φ , cv , ⊑ᴵ-trans φi ik) , tt)
  P-ψ1 {i = i} {p = p} {σ = σ} {z = z} nz ik (bs g) ex = bl (Good-iter tt nz (P-ψ1 nz ik g ea) eψ) (rule4ᵒ eψ)
    where ea = s-invˢ ex
          eψ = ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl i) ea
  P-ψ1 nz ik (bl hg st) ex = bl (λ n → P-ψ1 nz ik (hg n) (l-invˢ ex n)) (λ n → ψ1-cong (st n))
  P-ψ1 {p = p} {σ = σ} {z = z} nz ik (biP {K} {p = q} {f = f} j tr hm) ex with <ᴵ-dec (σ q) p
  ... | injᵃ (via e r) = biP (⊑ᴵ-≅ˡ e j)
    (λ a h y ey g → subψ1 {p = p} {σ = σ} {z₀ = z} {q = q} f e r y (P-ψ1 nz (⊑ᴵ-trans ik h) (tr a h (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ey))))
    (monψ1 {p = p} {σ = σ} {z₀ = z} {q = q} f e r hm)
  ... | injᵇ c = bl (λ n → P-ψ1 nz ik (tr K ⊑ᴵ-refl (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1P (NZ-≺ c) j ⊑ᴵ-refl tr ex n))) (i-respˢ ex (chain1-≅ ex n)))
                    (λ n → ψ1-cong (hm (chain1-step ex hm n)))
  ... | injᶜ c = bl (λ n → P-ψ1 nz ik (tr K ⊑ᴵ-refl (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1P (NZ-≅ nz c) j ⊑ᴵ-refl tr ex n))) (i-respˢ ex (chain1-≅ ex n)))
                    (λ n → ψ1-cong (hm (chain1-step ex hm n)))
  P-ψ1 nz ik (bu {r = zero} g) ex   = P-ψ1 nz ik g (u-reflˢ zero ex)
  P-ψ1 nz ik (bu {r = self n} g) ex = P-ψ1 nz ik g (u-reflˢ (self n) ex)
  P-ψ1 {i = suc _} {k = zero} nz ik (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (P-ψ1 nz ik g0 et) (λ η e → P-ψ1 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h))
  P-ψ1 {i = suc _} {k = suc _} nz ik (bŝ g0 gg et eg m mm (cv , _)) ex =
    bŝ (P-ψ1 nz ik g0 et) (λ η e → P-ψ1 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h)) (cv , tt)
  P-ψ1 {i = suc _} {k = lim _ _} nz ik (bŝ g0 gg et eg m mm (cv , _)) ex =
    bŝ (P-ψ1 nz ik g0 et) (λ η e → P-ψ1 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h)) (cv , tt)
  P-ψ1 {i = lim _ _} {k = zero} nz ik (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (P-ψ1 nz ik g0 et) (λ η e → P-ψ1 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h))
  P-ψ1 {i = lim _ _} {k = suc _} nz ik (bŝ g0 gg et eg m mm (cv , _)) ex =
    bŝ (P-ψ1 nz ik g0 et) (λ η e → P-ψ1 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h)) (cv , tt)
  P-ψ1 {i = lim _ _} {k = lim _ _} nz ik (bŝ g0 gg et eg m mm (cv , _)) ex =
    bŝ (P-ψ1 nz ik g0 et) (λ η e → P-ψ1 nz ik (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h)) (cv , tt)
  P-ψ1 nz ik (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
    bĉ G₀ Gg d₀ dE m₀ mE (P-ψ1 nz ik go (ĉ-refl₀ ex)) (λ η e → P-ψ1 nz ik (gO η e) (ĉ-reflg ex η e))
       (λ η e → ψ1-cong (mo η e)) (λ η e η′ e′ h → ψ1-cong (mO η e η′ e′ h))

  V-ψ1 {a = suc i₀} {p = p} {σ = σ} {z = z} nz h bz ex with pc p nz
  ... | (φ , cv , φi) = popG p σ z (V-ψ0 {p = zero} {σ = σ1 (z<suc z p)} nz ⊑ᴵ-refl (Good-Ωᶜ (suc zero) _) (Ωˢ-refl (suc zero)))
                                  (λ η e → V-ψ0 {p = lim 0 zero} {σ = λ q → lim 1 q} nz ⊑ᴵ-refl (Good-Ωᶜ η _) (Ωˢ-refl η))
                                  ((φ , cv , φi) , dom-cov (FlΛ-t₀pop φi p z) cv , λ η e → dom-cov (FlΛ-gpop φi p z η e) cv)
  V-ψ1 {a = lim _ _} {p = p} {σ = σ} {z = z} nz h bz ex with pc p nz
  ... | (φ , cv , φi) = popG p σ z (V-ψ0 {p = zero} {σ = σ1 (z<suc z p)} nz ⊑ᴵ-refl (Good-Ωᶜ (suc zero) _) (Ωˢ-refl (suc zero)))
                                  (λ η e → V-ψ0 {p = lim 0 zero} {σ = λ q → lim 1 q} nz ⊑ᴵ-refl (Good-Ωᶜ η _) (Ωˢ-refl η))
                                  ((φ , cv , φi) , dom-cov (FlΛ-t₀pop φi p z) cv , λ η e → dom-cov (FlΛ-gpop φi p z η e) cv)
  V-ψ1 {a = a} {p = p} {σ = σ} {z = z} nz h (bs {a = y} g) ex =
    bl (λ n → proj₁ (V-iter nz (V-ψ1 nz h g ea) (λ h′ → FlΛ-ψ1 h′ p σ z y ea) eψ n)) (rule4ᵒ eψ)
    where ea = s-invˢ ex
          eψ = ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl a) ea
  V-ψ1 nz h (bl hg st) ex = bl (λ n → V-ψ1 nz h (hg n) (l-invˢ ex n)) (λ n → ψ1-cong (st n))
  V-ψ1 {a = a₀} {p = p} {σ = σ} {z = z} nz h (biP {K} {p = q} {f = f} j tr hm) ex with <ᴵ-dec (σ q) p
  ... | injᵃ (via e r) = biV (<→⊑ r) a₀ (<→⊑ r) ⊑ᴵ-refl
    (λ a k y ey g → subψ1 {p = p} {σ = σ} {z₀ = z} {q = q} f e r y (P-ψ1 nz k (tr a (⊑ᴵ-trans h k) (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (inb (λ x → x) {q = q} {r = r} e g)) (i-respˢ ex (self-tr⁻ˢ e ey))))
    (λ y ey gp gv → subψ1 {p = p} {σ = σ} {z₀ = z} {q = q} f e r y (V-ψ1 nz ⊑ᴵ-refl (tr a₀ h (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (inb (λ x → x) {q = q} {r = r} e gp)) (i-respˢ ex (self-tr⁻ˢ e ey))))
    (monψ1 {p = p} {σ = σ} {z₀ = z} {q = q} f e r hm)
  ... | injᵇ c = bl (λ n → V-ψ1 nz ⊑ᴵ-refl (tr a₀ h (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1P (NZ-≺ c) (⊑ᴵ-trans j h) h tr ex n))) (i-respˢ ex (chain1-≅ ex n)))
                    (λ n → ψ1-cong (hm (chain1-step ex hm n)))
  ... | injᶜ c = bl (λ n → V-ψ1 nz ⊑ᴵ-refl (tr a₀ h (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1P (NZ-≅ nz c) (⊑ᴵ-trans j h) h tr ex n))) (i-respˢ ex (chain1-≅ ex n)))
                    (λ n → ψ1-cong (hm (chain1-step ex hm n)))
  V-ψ1 nz h (bu {r = zero} g) ex   = V-ψ1 nz h g (u-reflˢ zero ex)
  V-ψ1 nz h (bu {r = self n} g) ex = V-ψ1 nz h g (u-reflˢ (self n) ex)
  V-ψ1 {a = suc _} {k = zero} nz h (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (V-ψ1 nz h g0 et) (λ η e → V-ψ1 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h′ → ψ1-cong (mm η e η′ e′ h′))
  V-ψ1 {a = suc _} {k = suc _} {p = p} {σ = σ} {z = z} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
    bŝ (V-ψ1 nz h g0 et) (λ η e → V-ψ1 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h′ → ψ1-cong (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z t₀ et) cv ,
         λ η e → dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
  V-ψ1 {a = suc _} {k = lim _ _} {p = p} {σ = σ} {z = z} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
    bŝ (V-ψ1 nz h g0 et) (λ η e → V-ψ1 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h′ → ψ1-cong (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z t₀ et) cv ,
         λ η e → dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
  V-ψ1 {a = lim _ _} {k = zero} nz h (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (V-ψ1 nz h g0 et) (λ η e → V-ψ1 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h′ → ψ1-cong (mm η e η′ e′ h′))
  V-ψ1 {a = lim _ _} {k = suc _} {p = p} {σ = σ} {z = z} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
    bŝ (V-ψ1 nz h g0 et) (λ η e → V-ψ1 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h′ → ψ1-cong (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z t₀ et) cv ,
         λ η e → dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
  V-ψ1 {a = lim _ _} {k = lim _ _} {p = p} {σ = σ} {z = z} nz h (bŝ {t₀ = t₀} {g = g} g0 gg et eg m mm ((φ , cv , φK) , _)) ex =
    bŝ (V-ψ1 nz h g0 et) (λ η e → V-ψ1 nz h (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h′ → ψ1-cong (mm η e η′ e′ h′))
       ((φ , cv , ⊑ᴵ-trans φK h) , dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z t₀ et) cv ,
         λ η e → dom-cov (FlΛ-ψ1 (⊑ᴵ-trans φK h) p σ z (g η e) (eg η e η e (≅ᴵ-refl η))) cv)
  V-ψ1 nz h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
    bĉ G₀ Gg d₀ dE m₀ mE (V-ψ1 nz h go (ĉ-refl₀ ex)) (λ η e → V-ψ1 nz h (gO η e) (ĉ-reflg ex η e))
       (λ η e → ψ1-cong (mo η e)) (λ η e η′ e′ h′ → ψ1-cong (mO η e η′ e′ h′))
```

## §7 目标 0: 判别处

`F₀` 读输入的可见数据: 非零层闭包到第 0 层时 `Dom zero` 直接取 `ColC` 在观测 `col` 处的实例. 节点处, `chain1V` 证链点在吸收子句的输入类里: 节点 0 递归回 `F₀`; 非零节点 $j$ 由 `P-ψ1` 得到悬置, 当 $\kappa\sqsubseteq j$ 时由 `V-ψ1` 得到可见. 前提 "输入可见" 就是任务要的 "目标 0 可达处无悬置", 在链点处由吸收条件兑现. `Good-ψ1` 是合成.

```agda
  F₀ : ∀ {K} (K′ : Ordᴵ) {k} {p : zero <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → Good mV K x → x ≅ˢ x → Good mV K′ (ψ1 p σ z x)
  chain1V : ∀ {κ j k} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → j ⊑ᴵ κ →
            (∀ (y : Ordˢ j) → y ≅ˢ y → Gd mP κ j (<→◃ q) (intoˢ (<→◃ q) y) → (κ ⊑ᴵ j → Gd mV κ j (<→◃ q) (intoˢ (<→◃ q) y)) → Good mV κ (f (intoˢ (<→◃ q) y))) →
            Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good mP κ (chain1 σ z q f n) × (κ ⊑ᴵ j → Good mV κ (chain1 σ z q f n))

  chain1V {j = j} jκ ab e zero = Good-Ωᴾ j jκ , λ _ → Good-Ωⱽ j jκ
  chain1V {κ} {j = zero} {σ = σ} {z = z} {q = q} {f = f} jκ ab e (suc n) =
    V→P (F₀ κ {p = σ q} {σ = σ} {z = z} (ab (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab e n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab e n) h))) (i-respˢ e (chain1-≅ e n))) ,
    λ _ → F₀ κ {p = σ q} {σ = σ} {z = z} (ab (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab e n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab e n) h))) (i-respˢ e (chain1-≅ e n))
  chain1V {κ} {j = suc _} {σ = σ} {z = z} {q = q} {f = f} jκ ab e (suc n) =
    P-ψ1 {p = σ q} {σ = σ} {z = z} tt jκ (V→P (ab (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab e n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab e n) h)))) (i-respˢ e (chain1-≅ e n)) ,
    λ κj → Good-mono jκ (V-ψ1 {p = σ q} {σ = σ} {z = z} tt κj (V→P (ab (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab e n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab e n) h)))) (i-respˢ e (chain1-≅ e n)))
  chain1V {κ} {j = lim _ _} {σ = σ} {z = z} {q = q} {f = f} jκ ab e (suc n) =
    P-ψ1 {p = σ q} {σ = σ} {z = z} tt jκ (V→P (ab (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab e n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab e n) h)))) (i-respˢ e (chain1-≅ e n)) ,
    λ κj → Good-mono jκ (V-ψ1 {p = σ q} {σ = σ} {z = z} tt κj (V→P (ab (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab e n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab e n) h)))) (i-respˢ e (chain1-≅ e n)))

  F₀ K′ {p = p} {σ = σ} {z = z} bz ex =
    popG p σ z (Z-ψ0 K′ {p = zero} {σ = σ1 (z<suc z p)} (Good-Ωᶜ (suc zero) zero) (Ωˢ-refl (suc zero)) (Ok-Pl zero (Pl-Ω (suc zero))))
               (λ η e → Z-ψ0 K′ {p = lim 0 zero} {σ = λ q → lim 1 q} (Good-Ωᶜ η zero) (Ωˢ-refl η) (Ok-Pl zero (Pl-Ω η)))
               ((λ G → Strict₀ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G) , (λ η e G → Strict₀ (Ωˢ η) (Ωˢ-refl η) G))
  F₀ K′ {p = p} {σ = σ} {z = z} (bs g) ex = bl (Good-iter₀ (F₀ K′ g ea) eψ) (rule4ᵒ eψ)
    where ea = s-invˢ ex
          eψ = ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl zero) ea
  F₀ K′ (bl hg st) ex = bl (λ n → F₀ K′ (hg n) (l-invˢ ex n)) (λ n → ψ1-cong (st n))
  F₀ K′ {p = p} {σ = σ} {z = z} (biV {p = q} {f = f} j κ jκ κK tr ab hm) ex with <ᴵ-dec (σ q) p
  ... | injᵃ (via e ())
  ... | injᵇ c = bl (λ n → F₀ K′ (ab (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab ex n) h))) (i-respˢ ex (chain1-≅ ex n)))
                    (λ n → ψ1-cong (hm (chain1-step ex hm n)))
  ... | injᶜ c = bl (λ n → F₀ K′ (ab (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (proj₁ (chain1V jκ ab ex n))) (λ h → Good→Gd (<→◃ q) (proj₂ (chain1V jκ ab ex n) h))) (i-respˢ ex (chain1-≅ ex n)))
                    (λ n → ψ1-cong (hm (chain1-step ex hm n)))
  F₀ K′ (bu {r = zero} g) ex   = F₀ K′ g (u-reflˢ zero ex)
  F₀ K′ (bu {r = self n} g) ex = F₀ K′ g (u-reflˢ (self n) ex)
  F₀ K′ {k = zero} (bŝ g0 gg et eg m mm dm) ex =
    mkĉ g0 gg m mm dm (F₀ K′ g0 et) (λ η e → F₀ K′ (gg η e) (eg η e η e (≅ᴵ-refl η)))
        (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h))
  F₀ K′ {k = suc _} (bŝ g0 gg et eg m mm (_ , c₀ , cg)) ex =
    bŝ (F₀ K′ g0 et) (λ η e → F₀ K′ (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h))
       ((λ G → c₀ col G) , (λ η e G → cg η e col G))
  F₀ K′ {k = lim _ _} (bŝ g0 gg et eg m mm (_ , c₀ , cg)) ex =
    bŝ (F₀ K′ g0 et) (λ η e → F₀ K′ (gg η e) (eg η e η e (≅ᴵ-refl η)))
       (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
       (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ h → ψ1-cong (mm η e η′ e′ h))
       ((λ G → c₀ col G) , (λ η e G → cg η e col G))
  F₀ K′ (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
    bĉ G₀ Gg d₀ dE m₀ mE (F₀ K′ go (ĉ-refl₀ ex)) (λ η e → F₀ K′ (gO η e) (ĉ-reflg ex η e))
       (λ η e → ψ1-cong (mo η e)) (λ η e η′ e′ h → ψ1-cong (mO η e η′ e′ h))

  Good-ψ1 : ∀ {K k} {p : zero <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → Good mV K x → x ≅ˢ x → Goodᶻ (toZ (ψ1 p σ z x))
  Good-ψ1 {p = p} {σ = σ} {z = z} g ex = Good→Goodᶻ {m = mV} {K = zero} (F₀ zero {p = p} {σ = σ} {z = z} g ex)
```

## §8 对比表 (续 TreeNFBase §6)

| 记号侧 | 树侧 (本文) | 说明 |
|---|---|---|
| `Vis₁` 的 `vs`: 只看穿下标 $\ge u$ 的节点 | 模式 `mP`: 闭包有覆盖, `ColC` 暂缺; `V-ψ1`: 水位 $\sqsubseteq$ 目标时恢复 | 下标 $<u$ 的节点之内 "不可见" ⟷ 悬置 |
| 外层 $\psi_a$ 包住内层 | `biV` 的 $\kappa$: 分支的包裹目标 | 吸收; $\kappa\sqsubseteq j$ 时退化为输入须可见 |
| 前缀 $\Omega_{u+1}$ 托起被 $\psi_1$ 压低的闭包 | `V-add` | 前缀也是吸收者 |
| 下标 $<^\mathsf T$ 项 (由项的值保证) | 覆盖 `PopCov` + 水位 $K$ | 水位只比层号, 不读项 |
| $\psi^0$ 部分无 $G$-条件 | `mC`, `biH` | $\psi^{[]}$ 不弹栈, 节点可任意高 |

**为什么记号无关.** 定义与证明只提到 `Ordˢ`/`Z` 的树、`Ordᴵ`、观测前序、`Goodᶻ`; 导入的名字与 TreeNFBase 相同.

## §9 结论与边界

**定义 (编译).** `Mode`, `Cvd`, `VisD`, `Dom`, `Good₊`/`Gd`/`Good`, `PopCov`. **定理 (编译).** `Good-mono`, `V→P`, `P→C`, `Good-Ωᶜ/ᴾ/ⱽ`, `Good-tr`/`Good-tr⁻`, `Good-add`, `Good-add₀`, `V-add`, `C-ψ0`, `P-ψ0`, `V-ψ0`, `Z-ψ0`, `Fold.P-ψ1`, `Fold.V-ψ1`, `Fold.F₀`, **`Fold.Good-ψ1`**.

**边界.** (i) 只处理 Prefix 的栈 `[]`/`[Ω̂]`; 更长的栈没有这套理论. (ii) `Floor` 没有形式地嵌入 `Good`; 它的结论由 Pending 的 `cert-low` 独立得到 ($\varphi=1$ 处 `PopCov` 取 `one⊑`, 此时没有落到地板之下的映射). (iii) 只导入已有模块, 不改任何已有文件.
