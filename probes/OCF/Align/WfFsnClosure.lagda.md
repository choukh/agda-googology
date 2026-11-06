# WfFsnClosure: γ-链不变量, Buchholz 3.6 与 3.3 (ω 部分), `cl-fsn`

> **记号侧验收工作**, 不是最终定义, 不进成品. [WfFsn](WfFsn.lagda.md) 的第六段 (末段, 不导入归档). 蓝本: Lean `towerOT_of_Bachmann` (1554), `Trian_fs_aux` (1016), `OTFS_aux` (1635), `OTFS_thm` (1827); 在我方定义上重写, 沿视图结构递归.
>
> **结论 (编译过的定理, 无前提).**
>
> 1. `tow`: 规则 6 的位形 ($\psi_A(B)$ 标准, $B$ 共尾度 $\Omega_{\nu+1}$, $A\le\nu$) 下, 每一级 $\gamma_k$ 标准且 $G_A(\gamma_k)<B[\gamma_k]$ (Buchholz 的第二条塔不变量). 只靠 Bachmann 性质 (`bach`) 与 Ω 部分的 3.3/3.6.
> 2. `Tω` (3.6 的 ω 部分): $t$ 标准、共尾度 $\omega$ ⟹ $t[n]\lhd_0 t$.
> 3. `NFω` (3.3 的 ω 部分) 与 **`cl-fsn-NF`: 一切共尾度为 $\omega$ 的 EBO 标准形 $t$, $t[n]$ 标准.** 不要可数.
> 4. **`cl-fsn`**: [WfTauNF](WfTauNF.lagda.md) 的 `StdFsn` 要的前提, 原样的类型 (`Ctbl` 前提不用).
> 5. `cl-fsT`: Ω-基本列的封闭性 (`isOTᵉ` 形式), 作为副产品.
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfFsnClosure where

open import Data.Bool.Base using (Bool; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open E using (T; PT; ψ; _<ᵀ_; []<; hd<; tl<; lv<; ar<; cof; cω; cΩ; sucT; Ωt; Ωs; fsn; fsT; <-sucT)
open import OCF.Align.EBOI using (isOTᵉ)
open import OCF.Align.Standard using (Ctbl)
open import OCF.Align.Closure using (<ᵀ-trans)
open import OCF.Align.Bachmann using (gt→≤)
open import OCF.Align.WfFsnBase
open import OCF.Align.WfFsnView
open import OCF.Align.WfFsnTrian
open import OCF.Align.WfFsnOmega
open import OCF.Align.WfFsnBach
```

## §1 γ-链不变量 (Lean `towerOT_of_Bachmann`)

`hZ0`: $G_A(\nu)<B[\gamma_0]$: $G_A(\nu)\subseteq G_A(\nu+1)\subseteq G_A(B)$ (`G-sucT`, `G-spine`), 再用 Bachmann 性质. 归纳: $\gamma_0=\Omega_\nu$ 只看到 $0$ 与 $G_A(\nu)$; $\gamma_{k+1}=\psi_\nu(B[\gamma_k])$ 标准, 因为 $B[\gamma_k]$ 标准 (`NFΩ`, 要 $\gamma_k$ 标准) 且由 3.4 与 3.6 (`Gtri`, `TΩ`) $G_{u'}(B[\gamma_k])<B[\gamma_k]$ 对一切 $u'\ge A$; 它看到的 $B[\gamma_k]$, $G_A(\nu)$, $G_A(B[\gamma_k])$ 都 $<B[\gamma_{k+1}]$.

```agda
hZ0 : ∀ {A B ν} → NF (ψ A B ∷ []) → (w : VΩ B ν) → A ≤ᵀ sucT ν → ∀ {x} → InG A x ν → x <ᵀ fΩ w (γ w zero)
hZ0 {ν = ν} n w l i = bach n w (G-spine (nfp-a (nf-hd n)) w l (G-sucT ν i))

tow : ∀ {A B ν} → NF (ψ A B ∷ []) → (w : VΩ B ν) → A ≤ᵀ ν → ∀ k →
      NF (γ w k) × GB A (γ w k) (fΩ w (γ w k))
tow {A} {B} {ν} n w l zero = nf-W (nfp-a (nf-hd n)) w , g0 where
  g0 : GB A (γ w zero) (fΩ w (γ w zero))
  g0 (gp (gh _))   = fΩ-pos w []<
  g0 (gp (gw _ i)) = hZ0 n w (≤-trans′ l (inj₁ (<-sucT ν))) i
  g0 (gp (gc _ ()))
  g0 (gtl ())
tow {A} {B} {ν} n w l (suc k) = nf-ψ (nf-ν nB w) (NFΩ nB w (proj₁ ih) (γ< w k)) (hGY ν l) , gk where
  nB = nfp-a (nf-hd n)
  ih = tow n w l k
  hGY : ∀ u′ → A ≤ᵀ u′ → GB u′ (fΩ w (γ w k)) (fΩ w (γ w k))
  hGY u′ m = Gtri (TΩ w (γ< w k)) (λ i → nfp-g (nf-hd n) (G-mono m i)) (λ i → proj₂ ih (G-mono m i))
  gk : GB A (γ w (suc k)) (fΩ w (γ w (suc k)))
  gk (gp (gh _))   = val-mono w k
  gk (gp (gw _ i)) = <-≤ (hZ0 n w (≤-trans′ l (inj₁ (<-sucT ν))) i)
                         (≤-trans′ (val-le0 w k) (inj₁ (val-mono w k)))
  gk (gp (gc _ i)) = <ᵀ-trans (hGY A (inj₂ refl) i) (val-mono w k)
  gk (gtl ())
```

## §2 Buchholz 3.6, ω 部分

规则 6 用 `T-case4`, 它要的 γ-链界由下标的界 `SB` 经 `tower-bd` 给出; 这是 3.6 里唯一要标准形的地方.

```agda
Tω : ∀ {t} → NF t → (v : Vω t) → ∀ n → Trian [] (fω v n) t
Tω nt (ws {x = x} v) n = T-cons x (Tω (nf-tl nt) v n)
Tω nt (wl e v) n = T-sub (Tω (nfp-u (nf-hd nt)) v n)
Tω nt (w4 {u = u} {b} e) n = T-rep (T-psi u (T-pred b e)) n (rep< (t< (T-pred b e)) n)
Tω nt (w5 {u = u} e v) n = T-psi u (Tω (nfp-a (nf-hd nt)) v n)
Tω nt (w6 be g w) n = T-case4 w (tower-bd w (SB (nfp-a (nf-hd nt)) w)) n
```

## §3 Buchholz 3.3, ω 部分

```agda
NFω : ∀ {t} → NF t → (v : Vω t) → ∀ n → NF (fω v n)
NFω nt (ws v) n = n∷ (nf-hd nt) (hd-lt (nf-le nt) (t< (Tω (nf-tl nt) v n))) (NFω (nf-tl nt) v n)
NFω nt (wl e v) n = nf-Ω (NFω (nfp-u (nf-hd nt)) v n)
NFω nt (w4 {u = u} {b} e) n =
  nf-rep (nψ (nfp-u (nf-hd nt)) (nf-pred (nfp-a (nf-hd nt))) (Gtri (T-pred b e) (nfp-g (nf-hd nt)) GB[])) n
NFω nt (w5 e v) n =
  nf-ψ (nfp-u (nf-hd nt)) (NFω (nfp-a (nf-hd nt)) v n) (Gtri (Tω (nfp-a (nf-hd nt)) v n) (nfp-g (nf-hd nt)) GB[])
NFω nt (w6 {u = u} {ν = ν} be g w) n =
  nf-ψ (nfp-u (nf-hd nt)) (NFΩ (nfp-a (nf-hd nt)) w (proj₁ (tow nt w l n)) (γ< w n))
       (Gtri (TΩ w (γ< w n)) (nfp-g (nf-hd nt)) (proj₂ (tow nt w l n)))
  where l = gt→≤ ν u g
```

## §4 回到 EBO 的原定义

```agda
cl-fsn-NF : ∀ {t} → NF t → cof t ≡ cω → ∀ n → NF (fsn t n)
cl-fsn-NF {t} nt e n = subst NF (sym (fω-eq (vω t e) n)) (NFω nt (vω t e) n)

-- 3.3 (ω), bot 的 Bool 谓词形式: 对一切标准形, 不要可数
cl-fsnᵇ : ∀ {t} → isOTᵉ t ≡ true → cof t ≡ cω → ∀ n → isOTᵉ (fsn t n) ≡ true
cl-fsnᵇ {t} h e n = fromNF (cl-fsn-NF (toNF t h) e n)

-- WfTauNF.StdFsn 的前提, 原样的类型
cl-fsn : ∀ {t} → isOTᵉ t ≡ true → Ctbl t → cof t ≡ cω → ∀ n → isOTᵉ (fsn t n) ≡ true
cl-fsn h _ e n = cl-fsnᵇ h e n

-- 3.3 (Ω)
cl-fsT : ∀ {a μ η} → isOTᵉ a ≡ true → cof a ≡ cΩ μ → isOTᵉ η ≡ true → η <ᵀ Ωs μ → isOTᵉ (fsT a η) ≡ true
cl-fsT {a} {μ} {η} h e hη p =
  fromNF (subst NF (sym (fΩ-eq (vΩ a e) η)) (NFΩ (toNF a h) (vΩ a e) (toNF η hη) p))

-- 3.6 (ω, Ω), 在原定义上
trian-fsn : ∀ {t} → NF t → cof t ≡ cω → ∀ n → Trian [] (fsn t n) t
trian-fsn {t} nt e n = subst (λ s → Trian [] s t) (sym (fω-eq (vω t e) n)) (Tω nt (vω t e) n)

trian-fsT : ∀ {a μ} → cof a ≡ cΩ μ → ∀ {η} → η <ᵀ Ωs μ → Trian η (fsT a η) a
trian-fsT {a} e {η} p = subst (λ s → Trian η s a) (sym (fΩ-eq (vΩ a e) η)) (TΩ (vΩ a e) p)
```
