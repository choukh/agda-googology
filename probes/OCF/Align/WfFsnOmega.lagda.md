# WfFsnOmega: Ω-基本列保标准形, 与下标的界

> **记号侧验收工作**, 不是最终定义, 不进成品. [WfFsn](WfFsn.lagda.md) 的第四段. 蓝本: Lean `OTFS_aux` 中非规则 6 的分支 (1635 起), `SubBound`/`subBound_lt` (651, 671), `G_dom_subset` (FS 1060); 在我方定义上重写, 改为沿视图结构递归 (Lean 对大小归纳).
>
> 1. **3.3 的 Ω 部分** `NFΩ`: $a$ 标准、共尾度 $\Omega_{\mu+1}$, $\eta$ 标准且 $\eta<\Omega_{\mu+1}$ ⟹ $a[\eta]$ 标准. 自成一个结构归纳, **不依赖 ω 部分, 不依赖 Bachmann 性质**: Ω-基本列里没有规则 6.
> 2. **下标的界** `SB` (Lean `SubBound`, 换了形状): $a$ 标准、共尾度 $\Omega_{\nu+1}$, $a[\Omega_\nu]\le c\le a$ ⟹ $G_u(\nu)\preceq G_u(c)\cup\{0\}$. Lean 界的是 $G_u(\nu+1)$, 再经 3.6 换到 $G_u(\nu)$ (`sub_G_le`); 这里直接界 $G_u(\nu)$, 省掉一步, 因为 $G_u(\nu)\subseteq G_u(\nu+1)$ 是句法事实 (`G-sucT`). 用到 3.3 的地方只有奇异叶 (要 $a[\Omega_\nu]$ 标准, 才能说门槛之上 $G$ 为空).
> 3. **脊上的可见性** `G-spine` (Lean `G_dom_subset`): $A\le\nu+1$ 时 $G_A(\nu+1)\subseteq G_A(b)$.
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfFsnOmega where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open E using (T; PT; ψ; _<ᵀ_; []<; hd<; tl<; lv<; ar<; cof; cΩ; c1; pred; sucT; Ωt; Ωs; pred-suc; <-sucT)
open import OCF.Align.Closure using (<ᵀ-trans)
open import OCF.Align.Bachmann using (<ᵀ-irrefl; <ᵀ-asym; <sucT)
open import OCF.Align.WfFsnBase
open import OCF.Align.WfFsnView
open import OCF.Align.WfFsnTrian
```

## §1 Buchholz 3.3, Ω 部分

和: 首项不动, 尾巴降而首项关系保持 (`hd-lt`). 正规叶: 值就是 $\eta$. 奇异叶: 归纳. 穿透 $\psi_u(b)$: $b[\eta]$ 标准 (归纳), $G_u(b[\eta])<b[\eta]$ 由 3.4 (`Gtri`) 与 3.6 (`TΩ`) 得到, 其中 $G_u(\eta)=\varnothing$, 因为 $\eta<\Omega_{\mu+1}\le\Omega_u$ (`noG-Ω`).

```agda
NFΩ : ∀ {a μ} → NF a → (v : VΩ a μ) → ∀ {η} → NF η → η <ᵀ Ωs μ → NF (fΩ v η)
NFΩ n (ωs v) nη p = n∷ (nf-hd n) (hd-lt (nf-le n) (t< (TΩ v p))) (NFΩ (nf-tl n) v nη p)
NFΩ n (ωr e) nη p = nη
NFΩ n (ωl e v) nη p = nf-Ω (NFΩ (nfp-u (nf-hd n)) v nη p)
NFΩ n (ωp {u = u} {μ = μ} be pen v) nη p =
  nf-ψ (nfp-u (nf-hd n)) (NFΩ (nfp-a (nf-hd n)) v nη p)
       (Gtri (TΩ v p) (nfp-g (nf-hd n)) (λ i → ⊥-elim (noG-Ω nη (<-≤ p (Ωs≤ μ u pen)) i)))

-- γ 的首级 Ω_ν 是标准的, 且在 Ω_{ν+1} 之下
nf-W : ∀ {a ν} → NF a → VΩ a ν → NF (Ωt ν)
nf-W n v = nf-Ω (nf-ν n v)

nf-fW : ∀ {a ν} → NF a → (v : VΩ a ν) → NF (fΩ v (Ωt ν))
nf-fW n v = NFΩ n v (nf-W n v) (γ< v zero)
```

## §2 下标的界

```agda
CovZ : T → T → T → Set
CovZ u c x = Cov u c x ⊎ (x ≡ [])

covz-lift : ∀ {u c₀ c x} → (∀ {y} → InG u y c₀ → InG u y c) → CovZ u c₀ x → CovZ u c x
covz-lift f (inj₁ cv) = inj₁ (cov-lift f cv)
covz-lift f (inj₂ e)  = inj₂ e

-- ν ≤ r ≤ ν+1 时 G_u(ν) ⊆ G_u(r): r 只能是 ν 或 ν+1
reg-sub : ∀ {u x ν r A} → sucT ν ≡ A → ν ≤ᵀ r → r ≤ᵀ A → InG u x ν → InG u x r
reg-sub e (inj₂ refl) _ i = i
reg-sub {ν = ν} refl (inj₁ p) (inj₂ refl) i = G-sucT ν i
reg-sub {ν = ν} refl (inj₁ p) (inj₁ q) i with <sucT ν q
... | inj₁ q′   = ⊥-elim (<ᵀ-asym p q′)
... | inj₂ refl = ⊥-elim (<ᵀ-irrefl p)

SB : ∀ {a ν} → NF a → (v : VΩ a ν) → ∀ u c → fΩ v (Ωt ν) ≤ᵀ c → c ≤ᵀ a → ∀ {x} → InG u x ν → CovZ u c x
SB n (ωs {x = x} v) u c (inj₂ refl) r i =
  covz-lift gtl (SB (nf-tl n) v u _ (inj₂ refl) (inj₁ (t< (TΩ v (γ< v zero)))) i)
SB n (ωs {x = x} v) u c (inj₁ q) r i with cons-btw q r
... | c₀ , refl , q₀ , r₀ = covz-lift gtl (SB (nf-tl n) v u c₀ (inj₁ q₀) r₀ i)
SB n w@(ωr {u = A} e) u c (inj₂ refl) r i with dec≤ u (pred A)
... | inj₁ m = inj₁ (_ , gp (gw m i) , inj₂ refl)
... | inj₂ p = ⊥-elim (noG-le (nf-ν n w) (inj₁ p) i)
SB n w@(ωr {u = A} e) u c (inj₁ q) r i with dec≤ u (pred A) | psi-sub-btw q r
... | inj₂ p | _ = ⊥-elim (noG-le (nf-ν n w) (inj₁ p) i)
... | inj₁ m | r′ , s , c₁ , refl , l₀ , r₀ =
  inj₁ (_ , gp (gw (≤-trans′ m l₀) (reg-sub (pred-suc A e) l₀ r₀ i)) , inj₂ refl)
SB n (ωl {u = A} {μ = ν} e v) u c (inj₂ refl) r i
  with SB (nfp-u (nf-hd n)) v u _ (inj₂ refl) (inj₁ (t< (TΩ v (γ< v zero)))) i
... | inj₂ e′ = inj₂ e′
... | inj₁ (y , j , xy) with dec≤ u (fΩ v (Ωt ν))
...   | inj₁ m = inj₁ (y , gp (gw m j) , xy)
...   | inj₂ p = ⊥-elim (noG-le (nf-fW (nfp-u (nf-hd n)) v) (inj₁ p) j)
SB n (ωl {u = A} {μ = ν} e v) u c (inj₁ q) r i with psi-sub-btw q r
... | r′ , s , c₁ , refl , l₀ , r₀ with dec≤ u r′
...   | inj₁ m = covz-lift (λ j → gp (gw m j)) (SB (nfp-u (nf-hd n)) v u r′ l₀ r₀ i)
...   | inj₂ p with SB (nfp-u (nf-hd n)) v u _ (inj₂ refl) (inj₁ (t< (TΩ v (γ< v zero)))) i
...     | inj₂ e′ = inj₂ e′
...     | inj₁ (y , j , xy) = ⊥-elim (noG-le (nf-fW (nfp-u (nf-hd n)) v) (inj₁ (≤-< l₀ p)) j)
SB n w@(ωp {u = A} {μ = ν} be pen v) u c l r i with dec≤ u A
... | inj₂ p = ⊥-elim (noG-le (nf-ν n w) (inj₁ (<-≤ (<-sucT ν) (inj₁ (≤-< (Pen→≤ (sucT ν) A pen) p)))) i)
... | inj₁ m with psi-btw l r
...   | c₀ , c₁ , refl , l₀ , r₀ = covz-lift (λ j → gp (gc m j)) (SB (nfp-a (nf-hd n)) v u c₀ l₀ r₀ i)
```

## §3 脊上的可见性

```agda
G-spine : ∀ {B ν A x} → NF B → VΩ B ν → A ≤ᵀ sucT ν → InG A x (sucT ν) → InG A x B
G-spine n (ωs w) l i = gtl (G-spine (nf-tl n) w l i)
G-spine {A = A} {x} n (ωr {u = u} e) l i =
  gp (gw (subst (A ≤ᵀ_) (pred-suc u e) l) (subst (InG A x) (pred-suc u e) i))
G-spine n (ωl {u = u} e w) l i =
  gp (gw (≤-trans′ l (inj₁ (dom< (nfp-u (nf-hd n)) w))) (G-spine (nfp-u (nf-hd n)) w l i))
G-spine n (ωp {u = u} {μ = ν} be pen w) l i =
  gp (gc (≤-trans′ l (Pen→≤ (sucT ν) u pen)) (G-spine (nfp-a (nf-hd n)) w l i))
```
