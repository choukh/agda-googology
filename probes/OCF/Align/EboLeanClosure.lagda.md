# EboLeanClosure: EBO 标准形对 ω-基本列封闭 (Buchholz 3.3, 3.6)

> **记号侧验收工作**, 读记号, 不进成品. 逐字取自 [WfFsnClosure](WfFsnClosure.lagda.md) (γ-链不变量 `tow`, 3.6 的 ω 部分 `Tω`, 3.3 的 ω 部分 `NFω`, `cl-fsn-NF`, `trian-fsn`), 只换导入. **删去的:** Bool 谓词形式的 `cl-fsnᵇ`, `cl-fsn` (这里标准形就是 `NF`) 与 Ω-基本列的 `cl-fsT`, `trian-fsT` (第 3 层用不到). **新增的:** 可数项的两条 (`Ctbl-cof`, `Ctbl-fsn`), 沿视图证, 代替 [Standard](Standard.lagda.md) 里沿另一套视图的证明. `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanClosure where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLeanBase
open import OCF.Align.EboLeanView
open import OCF.Align.EboLeanTrian
open import OCF.Align.EboLeanOmega
open import OCF.Align.EboLeanBach
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

Tω : ∀ {t} → NF t → (v : Vω t) → ∀ n → Trian [] (fω v n) t
Tω nt (ws {x = x} v) n = T-cons x (Tω (nf-tl nt) v n)
Tω nt (wl e v) n = T-sub (Tω (nfp-u (nf-hd nt)) v n)
Tω nt (w4 {u = u} {b} e) n = T-rep (T-psi u (T-pred b e)) n (rep< (t< (T-pred b e)) n)
Tω nt (w5 {u = u} e v) n = T-psi u (Tω (nfp-a (nf-hd nt)) v n)
Tω nt (w6 be g w) n = T-case4 w (tower-bd w (SB (nfp-a (nf-hd nt)) w)) n

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

cl-fsn-NF : ∀ {t} → NF t → cof t ≡ cω → ∀ n → NF (fsn t n)
cl-fsn-NF {t} nt e n = subst NF (sym (fω-eq (vω t e) n)) (NFω nt (vω t e) n)

-- 3.6 (ω): t[n] ◁₀ t, 其中含 t[n] < t
trian-fsn : ∀ {t} → NF t → cof t ≡ cω → ∀ n → Trian [] (fsn t n) t
trian-fsn {t} nt e n = subst (λ s → Trian [] s t) (sym (fω-eq (vω t e) n)) (Tω nt (vω t e) n)
```

## 可数项对 `fsn` 封闭, 且不是 Ω-共尾

沿视图: 可数项的 Ω-视图不存在 (正规叶的下标非零, 奇异叶与穿透都要非零下标); ω-视图的每支保持 "首项下标为 0".

```agda
Ctbl-noΩ : ∀ {t μ} → Ctbl t → VΩ t μ → ⊥
Ctbl-noΩ (c∷ c) (ωs v) = Ctbl-noΩ c v
Ctbl-noΩ (c∷ c) (ωr ())
Ctbl-noΩ (c∷ c) (ωl () v)
Ctbl-noΩ (c∷ c) (ωp {μ = μ} _ pen v) with pen-ne μ [] pen
... | ()

Ctbl-cof : ∀ {t μ} → Ctbl t → cof t ≡ cΩ μ → ⊥
Ctbl-cof {t} c e = Ctbl-noΩ c (vΩ t e)

Ctbl-rep : ∀ {a} n → Ctbl (replicate n (ψ [] a))
Ctbl-rep zero    = c[]
Ctbl-rep (suc n) = c∷ (Ctbl-rep n)

Ctbl-fω : ∀ {t} → Ctbl t → (v : Vω t) → ∀ n → Ctbl (fω v n)
Ctbl-fω (c∷ c) (ws v) n = c∷ (Ctbl-fω c v n)
Ctbl-fω (c∷ c) (wl () v) n
Ctbl-fω (c∷ c) (w4 e) n = Ctbl-rep n
Ctbl-fω (c∷ c) (w5 e v) n = c∷ c[]
Ctbl-fω (c∷ c) (w6 be g w) n = c∷ c[]

Ctbl-fsn : ∀ {t} → Ctbl t → cof t ≡ cω → ∀ n → Ctbl (fsn t n)
Ctbl-fsn {t} c e n = subst Ctbl (sym (fω-eq (vω t e) n)) (Ctbl-fω c (vω t e) n)
```
