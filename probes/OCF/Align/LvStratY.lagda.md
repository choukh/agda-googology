# 分层的 $\approx$: 地板与反例族 `y s` (底座)

> 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). [LvIRNeg](LvIRNeg.lagda.md) 的反例族 `y s` (`HS`, 严格, 规整), 与 [LvIRReach](LvIRReach.lagda.md) 的 `hard`, `ask`: $\psi_0(\Omega_{\Omega_2})$ 字面地含目标 $\omega+1$. 这里显式地检查这个阶段的地板. 全部对任何 `S`.
>
> - `¬y∈A₀`: 闭实例 ([LvStratOmega](LvStratOmega.lagda.md)) 的第 0 层地板不含任何 `y s`. **所以 `Cert-Ω₊`, `Cert-Ω·2` 不碰这个反例族.**
> - `floor-y→WLPO`: 任何 `Stage`, 第 0 层地板含全部 `y s` 与 $\omega+1$, 就有 WLPO. 这是 `cmpA` 的直接推论: **有界的地板必然排除这个族, 除非 WLPO.** 这把 "有界的 `A` 看来排除它" (判断) 变成定理, 条件是地板含 $\omega+1$.
> - `CV-y→WLPO`: 判决在全部 $(y_s,\omega+1)$ 上正确 (`CV`), 就有 WLPO. 这是 `ask` 的站点: 第 0 层的好输入 $y_s+1$ 进分支, 就问这一对. 所以依赖 `S` 在这个站点上正确的结果都是条件的, 而且这个条件在含 `y s` 的地板上不可满足.
> - `cv-ω′→ext`: `CV` 是字面的穿透, 副本 $\omega'$ 对目标 $\omega+1$ 的正确判决给函数外延性的实例. 所以地板比 $\omega$ 大时, `ask` 的站点上这里的 `CV` 不够宽.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratY where

open import Data.Nat using (ℕ; _+_)
open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; toLv; Verdict)
open import OCF.Align.InaccFloorTree using (Sib; natL)
open import OCF.Align.LvStratBase using (AdmOf; Fl; module Leaf; Stage)
open import OCF.Align.LvStratEq using (module Eqv)
open import OCF.Align.LvStratOmega using (module Base)
open import OCF.Align.LvIRBase using (O₀; _≅⁰_; _≺⁰_; _⊑⁰_; z≅; s≅; l≅; ≺z; ≺s; ≺l)
import OCF.Align.LvIRNeg as N
open N using (WLPO)
```

## §1 第 0 层的树

```agda
emb : O₀ → Ordᴸ zero
emb O₀.zero    = Tree.zero
emb (O₀.suc a) = Tree.suc (emb a)
emb (O₀.lim f) = Tree.lim (λ n → emb (f n))

Yₛ : (ℕ → Bool) → Ordᴸ zero
Yₛ s = emb (N.y s)

ω+1 : O₀
ω+1 = O₀.suc N.ω

Iω : Lv
Iω = toLv (emb ω+1)

adm-emb : ∀ {B} b r → AdmOf B (toLv (emb b)) r
adm-emb (O₀.suc b) (inj₁ _) = tt
adm-emb (O₀.suc b) (inj₂ r) = adm-emb b r
adm-emb (O₀.lim f) (n , r)  = adm-emb (f n) r

module Conv (F : Fl) where
  open Leaf F

  ≈→≅ : ∀ a b → toLv (emb a) ≈ᴮ toLv (emb b) → a ≅⁰ b
  ≈→≅ O₀.zero O₀.zero z≈ = z≅
  ≈→≅ (O₀.suc a) (O₀.suc b) (s≈ e) = s≅ (≈→≅ a b e)
  ≈→≅ (O₀.lim f) (O₀.lim g) (l≈ h) = l≅ (λ n → ≈→≅ (f n) (g n) (h n))

  ≅→≈ : ∀ {a b} → a ≅⁰ b → toLv (emb a) ≈ᴮ toLv (emb b)
  ≅→≈ z≅ = z≈
  ≅→≈ (s≅ e) = s≈ (≅→≈ e)
  ≅→≈ (l≅ h) = l≈ (λ n → ≅→≈ (h n))

  p→≺ : ∀ a b (r : Pre (toLv (emb b))) → toLv (emb a) ≈ᴮ at (toLv (emb b)) r → a ≺⁰ b
  p→≺ a (O₀.suc b) (inj₁ _) e = ≺z (≈→≅ a b e)
  p→≺ a (O₀.suc b) (inj₂ r) e = ≺s (p→≺ a b r e)
  p→≺ a (O₀.lim f) (n , r)  e = ≺l n (p→≺ a (f n) r e)

  ≺→p : ∀ {a b} → a ≺⁰ b → toLv (emb a) ≺ᴬ toLv (emb b)
  ≺→p (≺z e) = viaᴬ (inj₁ tt) tt (≅→≈ e)
  ≺→p (≺s q) with ≺→p q
  ... | viaᴬ r d e = viaᴬ (inj₂ r) d e
  ≺→p (≺l n q) with ≺→p q
  ... | viaᴬ r d e = viaᴬ (n , r) d e

  tri→vd : ∀ a → Tri (toLv (emb a)) Iω → N.Vd a
  tri→vd a (injᵃ (viaᴬ r _ e)) = N.pen (p→≺ a ω+1 r e)
  tri→vd a (injᵇ p) = N.rise (λ q → up (≺⊑ (≺→p q) (≺→⊑ p)))
    where
    up : ∀ {c} → toLv (emb c) ≺ᴬ toLv (emb a) → c ≺⁰ a
    up (viaᴬ r _ e) = p→≺ _ a r e
  tri→vd a (injᶜ e) = N.rise (λ q → up (≺⊑ (≺→p q) (≈⊑ (≈ᴮ-sym e))))
    where
    up : ∀ {c} → toLv (emb c) ≺ᴬ toLv (emb a) → c ≺⁰ a
    up (viaᴬ r _ e′) = p→≺ _ a r e′
```

## §2 有界的地板排除反例族

```agda
floor-y→WLPO : (St : Stage) → (∀ s → Fl.A (Stage.fl St) zero (Yₛ s)) → Fl.A (Stage.fl St) zero (emb ω+1) → WLPO
floor-y→WLPO St ay aω =
  N.no-verdict (λ a → Fl.A (Stage.fl St) zero (emb a)) ay
    (λ a g → Conv.tri→vd (Stage.fl St) a (Stage.cmpA St zero (emb a) (emb ω+1) g aω))

module InClosed (S : Sib) where
  open Base S using (A0; flω)
  open Leaf flω

  ¬y∈A₀ : ∀ s → A zero (Yₛ s) → ⊥
  ¬y∈A₀ s a with A0 {Yₛ s} a
  ... | ℕ.zero  , ()
  ... | ℕ.suc n , ()
```

## §3 判决的站点

`CV-y→WLPO`: 只问判决, 不问地板. 第 0 层的好输入 $y_s+1$ 进目标 $\omega+1$ 的分支时, 模式是 `sib`, 节点是它的前驱 $y_s$ ([LvIRReach](LvIRReach.lagda.md) 的 `ask`). 这是 `oks` 在这个站点上的内容.

```agda
module Site (S : Sib) (St : Stage) where
  open Eqv S St

  CV-y→WLPO : (∀ s → CV (S (toLv (Yₛ s)) Iω)) → WLPO
  CV-y→WLPO h s with S (toLv (Yₛ s)) Iω | h s
  ... | _ | cvp r e _ = inj₁ (N.flag→s s (N.read-yes s (Conv.p→≺ fl (N.y s) ω+1 r (≡→≈ (sym e)))))
  ... | _ | cvr k = inj₂ (λ e → go e (Conv.≺→p fl (N.all-false→ s e)))
    where
    go : ∀ e → toLv (Yₛ s) ≺ᴬ Iω → ⊥
    go _ (viaᴬ r d q) = k r (Adm→B Iω r d) (≈ᴮ-sym q)

  -- 字面的穿透不够宽: 副本 ω′ 的正确判决给外延性的实例
  ω′ : Lv
  ω′ = lim (λ n → natL (n + 0))

  ωL : Lv
  ωL = lim natL

  nat≢lim : ∀ m {f : ℕ → Lv} → natL m ≡ Lv.lim f → ⊥
  nat≢lim ℕ.zero ()
  nat≢lim (ℕ.suc m) ()

  at-nat′ : ∀ n (r : Pre (natL n)) → Σ ℕ λ m → at (natL n) r ≡ natL m
  at-nat′ (ℕ.suc n) (inj₁ _) = n , refl
  at-nat′ (ℕ.suc n) (inj₂ r) = at-nat′ n r

  +0 : ∀ a → a + 0 ≡ a
  +0 ℕ.zero    = refl
  +0 (ℕ.suc a) = cong ℕ.suc (+0 a)

  ≈ω′ : ωL ≈ᴮ ω′
  ≈ω′ = l≈ (λ n → ≡→≈ (cong natL (sym (+0 n))))

  cv-ω′→ext : ∀ {v : Verdict ω′ (suc ωL)} → CV v → natL ≡ (λ n → natL (n + 0))
  cv-ω′→ext (cvr k) = ⊥-elim (k (inj₁ tt) tt ≈ω′)
  cv-ω′→ext (cvp (inj₁ _) e _) = lim-inj e
    where
    lim-inj : ∀ {f g : ℕ → Lv} → Lv.lim f ≡ Lv.lim g → f ≡ g
    lim-inj refl = refl
  cv-ω′→ext (cvp (inj₂ (n , r)) e _) with at-nat′ n r
  ... | m , q = ⊥-elim (nat≢lim m (trans (sym q) e))
```
