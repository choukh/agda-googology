# 折叠是和的作用 (四): $\psi(a+1)=\psi(a)\cdot\omega$ 这一步对上旧折叠

> 不含记号. 入口 [TLRule](TLRule.lagda.md). `main-Rel`: 对任何字面合法的层 $y$, 和形式的 $\psi_0(\Omega_y)$ 与 `CumReadCF` 的 $\psi_0(\Omega_y)$ 对应. `Co`: 第 0 层上的对应, 结构只差极限开头的一项.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF hiding (_⊕_)
open import OCF.Align.CumReadCFEq
open import OCF.Align.CumReadCFThm using (_⊴_; ψL; z⊴)
import OCF.Align.CumReadCF as C
import OCF.Align.TLRuleSum as N
open N using (D; n0; n1; _⨾_; nl; ni; AccL; acc; accL; ω⋅; Ωd; Ψd; sum; pt; cell)
open import OCF.Align.TLRuleRel
```

## §1 顶层的被积函数

世界 $W$. 每一格 $\psi_t(X+1)-\psi_t(X)$ 是 $\psi_t(X)$ 的 $\omega$ 个.

```agda
module Top (W : A) (lW : Lg W) where
  open N.Fold W lW ω⋅
  open import OCF.Align.TLRuleSim W lW ω⋅

  id-ContF : ∀ {k} → ContF {k} {k} (λ r → r) (λ z → z)
  id-ContF = record { cq = λ e → e ; cl = λ g e → e ; cn = λ s₁ g e q → e ; cm = λ d → d }

  I₁ : ∀ {k} → Itg {k} {k} (λ r → r) (λ _ Y → Step Y) (λ z → z) (λ _ z → z ≈ z)
  I₁ {k} = record
    { ict = id-ContF
    ; i1 = i₁
    ; icw = λ _ D → relR D
    ; icr = λ _ _ p → p
    }
    where
    i₁ : ∀ w z₀ z₁ (Y : St) → z₀ ≈ z₀ → z₁ ≈ os z₀ → z₁ ≈ z₁ → Inv Y z₀ → Diff (Step Y) z₀ z₁
    i₁ w z₀ z₁ Y pz d p v {t} τ T l T′ l′ =
      rd (rep c) (ψQ z₁ (os z₀) T′ l′ T′ l′ d) (ψQ z₁ z₁ T′ l′ T′ l′ p) (rep≈ cc) (z⊴ _)
        (rl (λ m → rep c (suc m)) (λ n → rep≈ cc (suc n)) (λ n → rep≈ cc (suc n)) (λ n → rep≈ cc (suc n))
            (ψQ z₀ z₀ T l T′ l′ pz)
            (λ m → add-Rel (rep c (suc m)) (rep≈ cc (suc m)) B))
      where
      c = ψ t T′ l′ z₀
      cc : c ≈ c
      cc = ψQ z₀ z₀ T′ l′ T′ l′ pz
      B = rc (Ω-Rel t C.self (lg⊲ τ lW)) (v τ T′ l′)
```

## §2 主定理

```agda
main-Rel : ∀ y (w : Lg y) → Rel azero o0 (n1 ⨾ Ψd y w) (ψ₀Ω y w)
main-Rel y w = rc (rs tt tt)
  (RS (accL y) C.self I₁ {w = n0} {z₀ = o0} tt (Ω-Rel y C.self w) (λ _ → n0)
      (λ {t} τ T l → rz (Ω≈ t) (Ω≈ t)) (z⊲ y) T₀ w T₀ w)
  where
  open Top y w
  open import OCF.Align.TLRuleSim y w ω⋅
  T₀ : Tg azero y
  T₀ = inj₁ (z⊲ y)
```

## §3 第 0 层

`Co a y`: 字面合法的层 $a$ 与第 0 层旧树 $y$ 同形, 只差旧树的极限可以多开头的项.

```agda
data Co : A → O azero → Set where
  cz : Co azero o0
  cs : ∀ {a y} → Co a y → Co (asuc a) (os y)
  cl′ : ∀ {f g} → (∀ n → Co (f n) (g n)) → Co (alim f) (ol g)
  cd : ∀ {a} (g : ℕ → O azero) → Co a (ol (λ m → g (suc m))) → Co a (ol g)
  ce : ∀ {a y y′} → Co a y → y ≈ y′ → Co a y′
  ce′ : ∀ {a y y′} → Co a y → y′ ≈ y → Co a y′

Co-Rel : ∀ {a b x y} → Rel azero b x y → Co a b → Co (sum a x) y
Co-pt  : ∀ {a b} {d : ℕ → D azero} (g : ℕ → O azero) → Co a b → b ≈ g 0 → (∀ m → Rel azero (g m) (d m) (g (suc m))) → ∀ n → Co (pt a d n) (g n)
Co-Rel (rz e p) c = ce c e
Co-Rel (rs e p) c = ce′ (cs c) e
Co-Rel {a} (rc {x = x} D₁ D₂) c = Co-Rel {a = sum a x} D₂ (Co-Rel D₁ c)
Co-Rel (rb e p D) c = Co-Rel D (ce c e)
Co-Rel (rr D e p) c = ce (Co-Rel D c) e
Co-Rel (rl g e p q e₀ st) c = ce′ (cl′ (Co-pt g c e₀ st)) e
Co-Rel (rd g e p q f D) c = ce′ (cd g (Co-Rel D c)) e
Co-Rel (ri () u p H e pz e₀ C ds) c
Co-pt g c e st zero = ce c e
Co-pt {a} {d = d} g c e st (suc n) = Co-Rel {a = pt a d n} (st n) (Co-pt g c e st n)

Co-Ψ : ∀ y (w : Lg y) → Co (N.Ψ y w) (ψ₀Ω y w)
Co-Ψ y w = Co-Rel (main-Rel y w) cz
```
