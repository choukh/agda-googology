# EboLean3Close: $\mathcal W(A)\cap\Omega_{l+1}$ 的封闭性 (Setzer Lemma 4.17 (b)(c) 的 EBO 版)

> **记号侧验收工作**, 读记号, 不进成品. [EboLean3](EboLean3.lagda.md) 的核心.
>
> **前提** (模块参数): $A\subseteq M(A)$ (`h`); $A$ 与 $\mathcal W(A)$ 在 $\Omega_l$ 以下一致 (`E`). **结论 (编译过的定理, 条件于这两个前提):** 记 $K=\Omega_{l+1}$, $\mathcal W(A)\cap K$ 对和 (`W-+`), $\Omega$ (`W-Ω`), 后继 (`W-suc`), $\psi_w$ ($w\le l$, `W-ψ`) 封闭; $K$ 以下由 $\mathcal W(A)\cap K$ 生成的 $C$-集元素都在 $\mathcal W(A)$ 里 (`under`).
>
> 与 Setzer 的差别: EBO 只有和与 $\psi$ ($\Omega_w=\psi_w(0)$), 没有 φ 与 I. 内层的归纳不按项的大小 (Setzer 的 `sizeRec` 加句法分情况), 而按 $C$-推导的结构: 推导的构造子就告诉我们是哪一种, 叶子直接用 `E`. 4.17 (c) 的 $\tilde C_\kappa$ 条件就是 $G_w(u)<y$ ([EboLean2](EboLean2.lagda.md) 的 `lt⇒GB`); Setzer 的 "$u<\tilde a$", "$u=\tilde a$" 两支在 EBO 里不出现 ($\psi_v(c)$ 由 `cψ` 推出时 $v\ge w$), 也不要 $\theta\in\mathcal W(A)$. 4.17 (b) 之后 Setzer 用 Remark 4.15 从 "弱封闭" 推 "封闭", 这里直接按 EBO 的列表结构写出需要的三条, 不要那套记录.
>
> `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3Close where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import OCF.Align.EboLeanDef using (T; ψ; Ωt; Ωs; sucT; _<ᵀ_; []<; hd<; tl<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-trans; ≤-trans′; ≤-<; <-≤; tri; dec≤; sub≤; ≤¬>;
  NF; nf-hd; nf-tl; nf-le; nfp-u; nfp-a; nf-Ω; gp; gtl; gw; gh; gc; GB; noG-le)
open import OCF.Align.EboLean2 using (Pred; hs; C; cl; c0; c+; cΩ; cψ; M; τ; 𝒲; sup; []≤; lt⇒GB)
open import OCF.Align.EboLean3Base

module L417 {ℓ} (A : Pred ℓ) (h : ∀ {y} → A y → M A y) (l : T) (E : Agree (Ωt l) A (𝒲 A)) where

  K : T
  K = Ωs l

  -- 层号 ≤ l 的 C-集里有 𝒲(A) 的一切元素 (Setzer 的 Side + 4.7 (b))
  side : ∀ {k y} → 𝒲 A y → k ≤ᵀ l → C A k y
  side {k} {y} w kl with tri (hs y) k
  ... | inj₁ p           = cl (proj₂ (E (<-≤ (hs<Ω p) (Ωt-mono kl))) w) (hs<Ω p)
  ... | inj₂ (inj₁ refl) = 𝒲-M w
  ... | inj₂ (inj₂ p)    = C-anti h (inj₁ p) (𝒲-M w)

  leaf : ∀ {k z} → k ≤ᵀ l → z <ᵀ Ωt k → A z → 𝒲 A z
  leaf kl p = proj₁ (E (<-≤ p (Ωt-mono kl)))
```

## (ii) 和: $x\in\mathcal W$ 主项, $y\in\mathcal W$, $x+y<K$ ⟹ $x+y\in\mathcal W$

对 $y$ 的 $\mathcal W$-推导递归. $d\in\tau^A(x+y)$: $d<x$ 时在 $\tau^A(x)$ 里; $d=x$; 否则 $d=x+d'$, $d'<y$, 而 $d$ 的推导 ($\ge\Omega_{\mathrm{hs}x}$, 不是叶子) 给出 $d'\in C$, 降层后 $d'\in\tau^A(y)$.

```agda
  W-+ : ∀ {v e ys} → 𝒲 A (ψ v e ∷ []) → 𝒲 A ys → NF (ψ v e ∷ ys) → (ψ v e ∷ ys) <ᵀ K → 𝒲 A (ψ v e ∷ ys)
  W-+ {ys = []} wx _ _ _ = wx
  W-+ {v} {e} {ψ w a ∷ ys} wx wy@(sup _ _ f) n k = sup n (c+ (𝒲-M wx) (side wy (lvl k))) τ⊆
    where
      τ⊆ : ∀ {d} → τ A (ψ v e ∷ ψ w a ∷ ys) d → 𝒲 A d
      τ⊆ (_ , _ , []<)                     = 0∈𝒲
      τ⊆ (nd , cd , hd< p)                 = 𝒲-τ wx (nd , cd , hd< p)
      τ⊆ {ψ _ _ ∷ []} (_ , _ , tl< _)      = wx
      τ⊆ {ψ _ _ ∷ _ ∷ _} (nd , cd , tl< q) =
        W-+ wx (f (nf-tl nd , C-anti h (sub≤ (nf-le n)) (proj₂ (inv+ cd)) , q)) nd (<ᵀ-trans (tl< q) k)
```

## (iv) Ω: $b\in\mathcal W$, $b\le l$ ⟹ $\Omega_b\in\mathcal W$

外层对 $b$ 的 $\mathcal W$-归纳, 内层对 $d\in C^b$ 的推导 ($d<\Omega_b$): 叶子用 `E`; 和用 (ii); $\Omega_w$ 有 $w<b$, $w\in\tau^A(b)$, 用外层归纳假设; `cψ` 与 $d<\Omega_b$ 矛盾.

```agda
  W-Ω : ∀ {b} → 𝒲 A b → b ≤ᵀ l → 𝒲 A (Ωt b)
  W-Ω = 𝒲-ind {B = λ b → b ≤ᵀ l → 𝒲 A (Ωt b)} step
    where
      step : ∀ {b} → 𝒲 A b → (∀ {y} → τ A b y → y ≤ᵀ l → 𝒲 A (Ωt y)) → b ≤ᵀ l → 𝒲 A (Ωt b)
      step {b} wb ih bl = sup (nf-Ω (𝒲-NF wb)) (cΩ (side wb bl)) (λ (nd , cd , p) → go nd cd p)
        where
          ΩK : Ωt b <ᵀ K
          ΩK = lvl⁻ bl
          go : ∀ {d} → NF d → C A b d → d <ᵀ Ωt b → 𝒲 A d
          go nd (cl a p) _              = leaf bl p a
          go nd c0 _                    = 0∈𝒲
          go nd (c+ {ψ _ _} dx dys) p   =
            W-+ (go (nf-h nd) dx (<ᵀ-trans h<s p)) (go (nf-tl nd) dys (<ᵀ-trans (t<s nd) p)) nd (<ᵀ-trans p ΩK)
          go nd (cΩ dw) p               =
            ih (nfp-u (nf-hd nd) , C-anti h (hs≤ b) dw , hd<Ω p) (≤-trans′ (inj₁ (hd<Ω p)) bl)
          go nd (cψ q _ _) p            = ⊥-elim (≤¬> q (hd<Ω p))

  W-suc : ∀ {t} → 𝒲 A t → sucT t <ᵀ K → 𝒲 A (sucT t)
  W-suc {t = []} _ _ = W-Ω 0∈𝒲 ([]≤ l)
  W-suc {ψ _ _ ∷ []} w k = W-+ w (W-Ω 0∈𝒲 ([]≤ l)) (nf-suc (𝒲-NF w)) k
  W-suc {ψ _ _ ∷ _ ∷ _} w k =
    W-+ (W-hd w) (W-suc (W-tl w) (<ᵀ-trans (t<s (nf-suc (𝒲-NF w))) k)) (nf-suc (𝒲-NF w)) k
```

## $K$ 以下的 $C$-闭包

```agda
  under : ∀ {ℓ′} {Z : Pred ℓ′} → (∀ {z} → Z z → z <ᵀ K → 𝒲 A z)
        → ∀ {d} → NF d → C Z (sucT l) d → d <ᵀ K → 𝒲 A d
  under zw nd (cl a p) _            = zw a p
  under zw nd c0 _                  = 0∈𝒲
  under zw nd (c+ {ψ _ _} dx dys) p =
    W-+ (under zw (nf-h nd) dx (<ᵀ-trans h<s p)) (under zw (nf-tl nd) dys (<ᵀ-trans (t<s nd) p)) nd p
  under zw nd (cΩ dv) p             = W-Ω (under zw (nfp-u (nf-hd nd)) dv (≤→<Ωs (lvl p))) (lvl p)
  under zw nd (cψ q _ _) p          = ⊥-elim (≤¬> q (hd<Ω p))
```

## (c) ψ: $w, y\in\mathcal W$, $w\le l$, $\mathrm{hs}(y)\le l$ ⟹ $\psi_w(y)\in\mathcal W$

外层对 $y$ 的 $\mathcal W$-归纳. $u\in\tau^A(\psi_w y)$ 时 $G_w(u)<y$ (`lt⇒GB`); 对 $u\in C^w$ 的推导递归 (`star`), 不变量是 $G_w(u)<y$ 与 $u<K$. `cψ` 支: $u=\psi_v(c)$, $v\ge w$, $c<y$; 递归得 $v, c\in\mathcal W$, 于是 $c\in\tau^A(y)$, 用外层归纳假设.

```agda
  W-ψ : ∀ {y} → 𝒲 A y → hs y ≤ᵀ l → ∀ {w} → 𝒲 A w → w ≤ᵀ l → NF (ψ w y ∷ []) → 𝒲 A (ψ w y ∷ [])
  W-ψ = 𝒲-ind {B = Q} step
    where
      Q : Pred ℓ
      Q y = hs y ≤ᵀ l → ∀ {w} → 𝒲 A w → w ≤ᵀ l → NF (ψ w y ∷ []) → 𝒲 A (ψ w y ∷ [])
      step : ∀ {y} → 𝒲 A y → (∀ {c} → τ A y c → Q c) → Q y
      step {y} wy ih yl {w} ww wl nf =
        sup nf (cψ (inj₂ refl) (side ww wl) (side wy wl))
               (λ (nu , cu , u<) → star nu cu (lt⇒GB nu u<) (<ᵀ-trans u< (lvl⁻ wl)))
        where
          yK : y <ᵀ K
          yK = lvl⁻ yl
          star : ∀ {u} → NF u → C A w u → GB w u y → u <ᵀ K → 𝒲 A u
          star nu (cl a p) g k = leaf wl p a
          star nu c0 g k = 0∈𝒲
          star nu (c+ {ψ _ _} dx dys) g k =
            W-+ (star (nf-h nu) dx (λ { (gp i) → g (gp i) ; (gtl ()) }) (<ᵀ-trans h<s k))
                (star (nf-tl nu) dys (λ i → g (gtl i)) (<ᵀ-trans (t<s nu) k)) nu k
          star nu (cΩ {w = v} dv) g k = W-Ω (star nv dv gv (≤→<Ωs (lvl k))) (lvl k)
            where
              nv = nfp-u (nf-hd nu)
              gv : GB w v y
              gv with dec≤ v w
              ... | inj₁ vw = λ i → ⊥-elim (noG-le nv vw i)
              ... | inj₂ wv = λ i → g (gp (gw (inj₁ wv) i))
          star nu (cψ {w = v} {c = c} wv dv dc) g k =
            ih (nc , side wc yl , c<y) (≤-trans′ (hs-mono (inj₁ c<y)) yl) wv′ (lvl k) nu
            where
              nc = nfp-a (nf-hd nu)
              c<y = g (gp (gh wv))
              wv′ = star (nfp-u (nf-hd nu)) dv (λ i → g (gp (gw wv i))) (≤→<Ωs (lvl k))
              wc  = star nc dc (λ i → g (gp (gc wv i))) (<ᵀ-trans c<y yK)
```
