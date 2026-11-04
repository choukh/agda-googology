# 和形式过 $\Omega_{\Omega+1}$: 验收

> **验收文件.** 读 `NoCumsum`, `BTBOFull` (标签树 `BTBOᴵ` 在这里, 标签本身的定理是 `Label.BTBO-label`). 入口 [SumOne](SumOne.lagda.md).
>
> 下界: `T₀≈`: 第 0 项 `T₀` 与 `BTBOᴵ` 互相 $\preccurlyeq$. `step-T₁`: `T₁` 严格高于 `BTBOᴵ`. 上界: 没有. `T₁` 与 $\psi_0(\Omega_{\Omega+1})$ 的对照树之间没有定理, 第一个障碍见 [SumOne](SumOne.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneAccept where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level hiding (below)
import OCF.Align.NoCumsum as NC
open NC using (BTBOᴵ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ≼-suc; ≺→s≼)
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl; SV-L; Pos; ps; pl; posF; z<SV; St-F; SV-toLevel)
open import OCF.Align.BTBOFull using (γ-step)
open import OCF.Align.BTBOFullV3 using (Fstep; Fʸ)
open import OCF.Align.BTBOValNeg using (HS-≅; ≼-irr)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; ψ₀Ω; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumUpAcceptSim using (fr; Y-sim)
import OCF.Align.TLRuleSum as Nₒ
open import OCF.Align.TLRuleMain using (Co)
open import OCF.Align.TLRuleAccept using (VE; vs; vz; vr; VEv; PEf; PEb; SV-VE; Pos-VE; lv; Ix-lv; forget-lv; CoV; Fψ; toFψ; Bump; Fψ≅)
open import OCF.Align.TLRuleVar using (natA′; ωᴬ; ≤→≼; ω≼F₀; trA)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; ⊲→≤)
import OCF.Align.SumOneTree as N
open N using (D; n0; n1; _⨾_; nl; nw; ni; nκ; sum; pt; drp; Lg-sum)
open import OCF.Align.SumOneClosed using (T₀; T₁; E₁; Cl; Sv; a; ap; av; wv; co; one; St; yc; τ₀)
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTop using (Cℓ; Δℓ; CIs; coᶜ)
```

## §1 层的序列

```agda
u : ℕ → A
u n = F.v (Cℓ n)

lu : ∀ n → Lg (u n)
lu n = F.lv (Cℓ n)

coS : ∀ n → Co (u (suc n)) (ψ₀Ω (u n) (lu n))
coS n = coᶜ (CIs (suc n)) (lu n)

aₙ : ℕ → Ordᴵ
aₙ n = lv (u n) (lu n)
```

## §2 第 0 层: $\omega$

`u 0` 就是 $1,2,3,\dots$ 的极限.

```agda
cc : D azero one
cc = (n1 ⨾ n0) ⨾ n0

pt≤ : ∀ n → pt {one} one (λ _ → cc) n ≤ natA′ (suc n)
pt≤ zero = s≤ z≤
pt≤ (suc n) = s≤ (pt≤ n)

u0≤ω : u 0 ≤ ωᴬ
u0≤ω = l≤ (λ n → ≤l (suc n) (pt≤ n))

SV-pt : ∀ n (w : Lg (pt {one} one (λ _ → cc) n)) → SV (lv (pt {one} one (λ _ → cc) n) w)
SV-pt zero w = svs svz
SV-pt (suc n) w = svs (SV-pt n w)

SV-u0 : SV (aₙ 0)
SV-u0 = svl (λ n → SV-pt n _) (λ n → _ , via (≅ᴵ-refl _) zero , ⊑ᴵ-refl)

Pos-u0 : Pos (aₙ 0)
Pos-u0 = pl

u0≼F₀ : forget (aₙ 0) ≼ Fʸ zero
u0≼F₀ = ≼-trans (≅→≼ (≅-sym (forget-lv (u 0) (lu 0)))) (≼-trans (≤→≼ u0≤ω) ω≼F₀)

F₀≼F₁ : Fʸ zero ≼ Fʸ (suc zero)
F₀≼F₁ = ≼-trans (≼-suc (≼-refl _)) (≺→s≼ (Fstep zero))
```

## §3 对角线

```agda
SP   : ∀ n → SV (aₙ n) × Pos (aₙ n)
STEP : ∀ n → VE (aₙ (suc n)) (toFψ (aₙ n))

STEP n =
  let E = Y-sim (lu n) (Ix-lv (u n) (lu n)) (z<SV (proj₁ (SP n)) (proj₂ (SP n)))
      h = HS-≅ E (Uniform (aₙ n))
  in vr (CoV (coS n) (lu (suc n)) h) (toLevel-≅ h (Uniform (aₙ n)) E)

SP zero = SV-u0 , Pos-u0
SP (suc n) =
  SV-VE (STEP n) sv′ , Pos-VE (STEP n) sv′ (posF (aₙ n) (Uniform (aₙ n)))
  where
  sv′ : SV (toFψ (aₙ n))
  sv′ = SV-toLevel (Fψ (aₙ n)) (Uniform (aₙ n)) (St-F (proj₁ (SP n)) (proj₂ (SP n)))

fa≼ : ∀ n → forget (aₙ (suc n)) ≼ Fψ (aₙ n)
fa≼ n = ≼-trans (proj₁ (VEv (STEP n))) (≅→≼ (forget-toLevel (Fψ (aₙ n)) (Uniform (aₙ n))))

≼fa : ∀ n → Fψ (aₙ n) ≼ forget (aₙ (suc n))
≼fa n = ≼-trans (≅→≼ (≅-sym (forget-toLevel (Fψ (aₙ n)) (Uniform (aₙ n))))) (proj₂ (VEv (STEP n)))

Lv : ℕ → Ordᴵ
Lv = NC.L

γ≼L : ∀ m → NC.γ m ≼ forget (Lv m)
γ≼L m = ≅→≼ (≅-sym (forget-toLevel (NC.γ m) (NC.cert m)))

L≼γ : ∀ m → forget (Lv m) ≼ NC.γ m
L≼γ m = ≅→≼ (forget-toLevel (NC.γ m) (NC.cert m))

toF≅ : ∀ m → toFψ (Lv m) ≅ᴵ Lv (suc m)
toF≅ m = toLevel-≅ (Uniform (Lv m)) (NC.cert (suc m)) (≅-refl⁰ (NC.γ (suc m)))

g h : ℕ → ℕ
g zero = 1
g (suc n) = suc (suc (g n))
h zero = 0
h (suc m) = suc (suc (h m))

Up : ∀ n → forget (aₙ n) ≼ forget (Lv (g n))
Up zero = ≼-trans u0≼F₀ (≼-trans F₀≼F₁ (γ≼L 1))
Up (suc n) =
  ≼-trans (fa≼ n)
  (≼-trans (Bump (proj₁ (SP n)) (SV-L (g n)) (Up n))
  (≼-trans (Fψ≅ (toF≅ (g n)))
           (γ≼L (suc (suc (g n))))))

L0≼a0 : forget (Lv 0) ≼ forget (aₙ 0)
L0≼a0 = ≼l 0 (s≼s z≼)

Dn : ∀ m → forget (Lv m) ≼ forget (aₙ (h m))
Dn zero = L0≼a0
Dn (suc m) =
  ≼-trans (L≼γ (suc m))
  (≼-trans (Bump (SV-L m) (proj₁ (SP (h m))) (Dn m))
  (≼-trans (Ψ-emb (PEb (STEP (h m))))
           (≼fa (suc (h m)))))
```

## §4 第 0 项就是 $\psi_0(\Omega_\Omega)$

`T₀` 是部分和的极限, 第 $n$ 个部分和与 `u n` $\cong$ (`drp` 只换世界).

```agda
sum-drp : ∀ {W W′} {a₁ b₁ : A} (x : D azero W) → trA a₁ ≅ trA b₁ → trA (sum a₁ (drp {W} {W′} x)) ≅ trA (sum b₁ x)
pt-drp  : ∀ {W W′} {a₁ b₁ : A} (F₁ : ℕ → D azero W) → trA a₁ ≅ trA b₁ → ∀ n → trA (pt a₁ (λ m → drp {W} {W′} (F₁ m)) n) ≅ trA (pt b₁ F₁ n)
sum-drp n0 e = e
sum-drp n1 e = s≅ e
sum-drp {W′ = W′} (x ⨾ y) e = sum-drp {W′ = W′} y (sum-drp {W′ = W′} x e)
sum-drp (nl F₁) e = l≅ (pt-drp F₁ e)
sum-drp (ni () u₁) e
sum-drp (nκ () u₁) e
sum-drp (nw p x) e = sum-drp x e
pt-drp F₁ e zero = e
pt-drp {W′ = W′} F₁ e (suc n) = sum-drp {W′ = W′} (F₁ n) (pt-drp F₁ e n)

d₀ₙ : ∀ n → D azero (u n)
d₀ₙ n = F.yc (Δℓ n) (inj₁ (C.z⊲ (u n))) tt

Dℓ : ℕ → D azero one
Dℓ n = drp (d₀ₙ n)

T₀-pt : ∀ n → trA (pt (u 0) Dℓ n) ≅ trA (u n)
T₀-pt zero = ≅-refl⁰ (trA (u 0))
T₀-pt (suc n) = sum-drp {W′ = one} (d₀ₙ n) (T₀-pt n)

T₀≅ : trA T₀ ≅ lim (λ n → trA (u n))
T₀≅ = l≅ T₀-pt

u≼B : ∀ n → trA (u n) ≼ BTBOᴵ
u≼B n = ≼l (g n) (≼-trans (≅→≼ (forget-lv (u n) (lu n))) (≼-trans (Up n) (≼-trans (L≼γ (g n)) (γ-step (g n)))))

T₀≈ : trA T₀ ≈ᵛ BTBOᴵ
T₀≈ =
  ≼-trans (≅→≼ T₀≅) (l≼ u≼B) ,
  ≼-trans (l≼ (λ m → ≼l (h (suc m)) (≼-trans (γ≼L (suc m)) (≼-trans (Dn (suc m)) (≅→≼ (≅-sym (forget-lv (u (h (suc m))) (lu (h (suc m))))))))))
          (≅→≼ (≅-sym T₀≅))
```

## §5 `T₁` 严格高于第 0 项

`NZ x`: 走 $x$ 至少多一. 这里不要归纳: `E₁ 0` 第一段就有 $\psi(\Omega_0)\cdot\omega$ 的第 1 项.

```agda
data NZ₀ {W : A} : D azero W → Set where
  nz1 : NZ₀ n1
  nzL : ∀ {x y} → NZ₀ x → NZ₀ (x ⨾ y)
  nzR : ∀ {x y} → NZ₀ y → NZ₀ (x ⨾ y)
  nzl : ∀ {d′} → NZ₀ (d′ 0) → NZ₀ (nl d′)

sum≥ : ∀ {W} b (x : D azero W) → b ≤ sum b x
sum≥ b x = ⊲→≤ (N.sum-fst b x)

nz≤ : ∀ {W} b {x : D azero W} → NZ₀ x → asuc b ≤ sum b x
nz≤ b nz1 = ≤-refl _
nz≤ b {x ⨾ y} (nzL d) = ≤-trans (nz≤ b d) (sum≥ (sum b x) y)
nz≤ b {x ⨾ y} (nzR d) = ≤-trans (s≤ (sum≥ b x)) (nz≤ (sum b x) d)
nz≤ b (nzl d) = ≤l 1 (nz≤ b d)

NZ-E : NZ₀ (E₁ 0)
NZ-E = nzR (nzL (nzl (nzL (nzL (nzl (nzL (nzL nz1)))))))

T₀<T₁ : asuc T₀ ≤ T₁
T₀<T₁ = ≤l 1 (nz≤ T₀ NZ-E)

step-T₁ : suc BTBOᴵ ≼ trA T₁
step-T₁ = ≼-trans (s≼s (proj₂ T₀≈)) (≤→≼ T₀<T₁)
```

## §6 基本列的差

第 0 项就不同: 和形式的回灌从当前输出读层, 第一个层是 $\omega$ (`u 0`), 对照树第 0 项已是 $\psi_0(\Omega_1)$. 这是定理, 只否定 $\cong$, 不否定序数值 (`T₀≈`).

```agda
gap₀ : suc (trA (u 0)) ≼ NC.γ 1
gap₀ = ≼-trans (s≼s (≼-trans (≅→≼ (forget-lv (u 0) (lu 0))) u0≼F₀)) (≺→s≼ (Fstep zero))

T₀≇ : trA T₀ ≅ BTBOᴵ → ⊥
T₀≇ e with T₀≅ | e
... | l≅ _ | l≅ h = ≼-irr (trA (u 0)) (≼-trans gap₀ (≅→≼ (≅-sym (h 0))))
```

**每个部分和的值就是上一个的折叠.** `step≈`: $u_{n+1}\approx\psi_0(\Omega_{u_n})$, 定理. 所以部分和不是 `Cumsum` 那种事后的累加: 没有多出来的值 (`overshoot` 那样的), 差只是起点错开一位 ($u_0=\omega=\psi_0(\Omega_0)$, 对照 $\gamma_1=\psi_0(\Omega_1)$).

```agda
step≈ : ∀ n → forget (aₙ (suc n)) ≈ᵛ Fψ (aₙ n)
step≈ n = fa≼ n , ≼fa n

u₀≈ω : trA (u 0) ≼ Fψ zero
u₀≈ω = ≼-trans (≤→≼ u0≤ω) ω≼F₀
```
