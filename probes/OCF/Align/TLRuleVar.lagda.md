# 折叠是和的作用: 换一步 (读旧树)

> 入口 [TLRule](TLRule.lagda.md). `Gen S`: 同一个折叠, 只换 `S`. 所有 `S` 都不要合法性证明 (`Lg-Ψ` 对一切 `S`). `S` 改了值就改了: $S=+1$ 时 $\psi_0(1)=2$, $\psi_0(\Omega_1)\preccurlyeq\omega$; $S=\cdot\omega$ 时 $\psi_0(\Omega_1)$ 严格高于 $\psi_0(1)=\omega$ (`gap-Ω₁`). 所以规格只有和的结构时, 值不被决定 (`blind`). 是否在 $\psi_0(\Omega_\Omega)$ 还不同: 只有判断和有限测试 ([TLRuleTest](TLRuleTest.lagda.md)).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleVar where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; z⊲; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.Level hiding (below)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ≼-suc; +-mono; ≺→s≼)
open import OCF.Align.BTBOValNeg using (≼-irr)
open import OCF.Align.BTBOFullV3 using (Fstep; Fʸ)
open import OCF.Align.CumUpAcceptSim using (fr)
import OCF.Align.TLRuleSum as N
open N using (D; n0; n1; _⨾_; nl; ni; sum; pt; module Gen; module Fold; accL; ω⋅)
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc)
open import OCF.Align.TLRuleAccept using (a; ≼fa; forget-lv)
```

## §1 $S=+1$

```agda
+1ˢ : ∀ {t} → D t → D t
+1ˢ _ = n1

module P = Gen +1ˢ

one : A
one = asuc azero

ωA : A
ωA = alim natA
  where
  natA : ℕ → A
  natA zero = azero
  natA (suc n) = asuc (natA n)
```

$\psi_0(1)$: 两个规则直接算.

```agda
_ : P.Ψ azero tt ≡ asuc (asuc azero)
_ = refl
```

$\psi_0(\Omega_1)$ 在 $+1$ 下: 链上每一段都是 `D₁`, 所以和只到 $\omega$. 这里只用计算和归纳.

```agda
natA′ : ℕ → A
natA′ zero = azero
natA′ (suc n) = asuc (natA′ n)

ωᴬ : A
ωᴬ = alim natA′

private
  open Fold one tt +1ˢ

  D₁ : D azero
  D₁ = (n0 ⨾ n1) ⨾ n0

  A₁ : D one → D azero → St → St
  A₁ w = Ai (accL one) C.zero C.self (N.acc≪ one C.zero) (λ _ Y → Step Y) w (λ _ → n1)

  ρ : azero ⊲ one
  ρ = C.suc C.self

  ac₀ = N.acc≪ one C.zero

  δ≡ : ∀ w (Y₀ : St) → Y₀ ρ ≡ D₁ → ∀ n → proj₁ (proj₂ (Chn ac₀ ρ (A₁ w) Y₀ n)) ≡ D₁
  δ≡ w Y₀ e zero = e
  δ≡ w Y₀ e (suc n) = cong (λ d → Run ac₀ ρ (A₁ w) (proj₁ (Chn ac₀ ρ (A₁ w) Y₀ n)) d (proj₂ (proj₂ (Chn ac₀ ρ (A₁ w) Y₀ n))) ρ) (δ≡ w Y₀ e n)

  E≡ : ∀ w (Y₀ : St) → Y₀ ρ ≡ D₁ → ∀ n → Run ac₀ ρ (A₁ w) (proj₁ (Chn ac₀ ρ (A₁ w) Y₀ n)) (proj₁ (proj₂ (Chn ac₀ ρ (A₁ w) Y₀ n))) (proj₂ (proj₂ (Chn ac₀ ρ (A₁ w) Y₀ n))) ρ ≡ D₁
  E≡ w Y₀ e n = cong (λ d → Run ac₀ ρ (A₁ w) (proj₁ (Chn ac₀ ρ (A₁ w) Y₀ n)) d (proj₂ (proj₂ (Chn ac₀ ρ (A₁ w) Y₀ n))) ρ) (δ≡ w Y₀ e n)

pt≤ : ∀ {b k} {E : ℕ → D azero} → b ≤ natA′ k → (∀ n → E n ≡ D₁) → ∀ n → pt b E n ≤ natA′ (n +ᴺ k)
pt≤ h eq zero = h
pt≤ {b} {k} {E} h eq (suc n) = subst (λ d → sum (pt b E n) d ≤ natA′ (suc (n +ᴺ k))) (sym (eq n)) (s≤ (pt≤ h eq n))

private
  A₀ : D one → St → St
  A₀ _ Y = Step Y

  Yz : St
  Yz _ = n0

  Y₁ : St
  Y₁ = Yz ⊕ Run (accL one) C.self A₀ n0 n1 Yz

  Y₂ : St
  Y₂ = Y₁ ⊕ Run (accL one) C.self A₀ (n0 ⨾ n1) n0 Y₁

Ψ⁺≤ω : P.Ψ one tt ≤ ωᴬ
Ψ⁺≤ω = l≤ (λ n → ≤l (n +ᴺ 2) (pt≤ (s≤ (s≤ z≤)) (E≡ ((n0 ⨾ n1) ⨾ n0) Y₂ refl) n))
```

## §2 值的差

第 0 层的 `A` 上的前序搬到 `Level` 的值. $\omega$ 就是 $\psi^0(\Omega_0)$.

```agda
trA : A → Ordᶜ zero
trA a₀ = fr (N.ord a₀)

≤→≼ : ∀ {x y} → x ≤ y → trA x ≼ trA y
≤→≼ z≤ = z≼
≤→≼ (s≤ p) = s≼s (≤→≼ p)
≤→≼ (≤l n p) = ≼l n (≤→≼ p)
≤→≼ (l≤ p) = l≼ (λ n → ≤→≼ (p n))

n1+ : ∀ n → trA (natA′ (suc n)) ≼ (suc zero + trA (natA′ n))
n1+ zero = ≼-refl _
n1+ (suc n) = s≼s (n1+ n)

iter≽ : ∀ n → trA (natA′ n) ≼ iter (suc zero +_) zero n
iter≽ zero = z≼
iter≽ (suc n) = ≼-trans (n1+ n) (+-mono (≼-refl (suc zero)) (iter≽ n))

ω≼F₀ : trA ωᴬ ≼ Fʸ zero
ω≼F₀ = l≼ (λ n → ≼l n (iter≽ n))

Fstep₀ : suc (Fʸ zero) ≼ Fʸ (suc zero)
Fstep₀ = ≺→s≼ (Fstep zero)
```

`gap-Ω₁`: 同一个层 $\Omega_1$, $+1$ 的折叠严格低于 $\cdot\omega$ 的折叠.

```agda
F₁≼Ψ : Fʸ (suc zero) ≼ trA (N.Ψ one tt)
F₁≼Ψ = ≼-trans (≼fa 0) (≅→≼ (≅-sym (forget-lv (N.Ψ one tt) (N.Lg-Ψ one tt))))

gap-Ω₁ : suc (trA (P.Ψ one tt)) ≼ trA (N.Ψ one tt)
gap-Ω₁ = ≼-trans (s≼s (≼-trans (≤→≼ Ψ⁺≤ω) ω≼F₀)) (≼-trans Fstep₀ F₁≼Ψ)

blind : (P.Ψ azero tt ≡ asuc (asuc azero)) × (¬ (trA (N.Ψ one tt) ≼ trA (P.Ψ one tt)))
blind = refl , λ le → ≼-irr (trA (P.Ψ one tt)) (≼-trans gap-Ω₁ le)
```

## §3 都不要证书

`Lg-Ψ` 与 `S` 无关: 下面是定义, 一行证明都没有. $S=\cdot2$ 也是闭项.

```agda
·2ˢ : ∀ {t} → D t → D t
·2ˢ c = c

module Q = Gen ·2ˢ

T⁺ T² : Ordᶜ zero
T⁺ = trA P.Top
T² = trA Q.Top

lg⁺ : ∀ y w → Lg (P.Ψ y w)
lg⁺ = P.Lg-Ψ

lg² : ∀ y w → Lg (Q.Ψ y w)
lg² = Q.Lg-Ψ
```
