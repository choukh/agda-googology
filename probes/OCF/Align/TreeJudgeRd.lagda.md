# 树侧判据的第一次使用: 带前缀的紧读法 (定义)

> 不含记号. 结论写在 [TreeJudge](TreeJudge.lagda.md). 盲测的目标 $\psi_1(1)\cdot m$, $\psi_1(2)$ 的闭包是 $W(\Omega\cdot(k+1)$ 的分支$)$, $W$ 是前缀 $a+(a+\cdots)$. [GuardTightRd](GuardTightRd.lagda.md) 的实例只到 $\Omega\cdot n$ 与 $a+\Omega_1$. 这里写一个对前缀 $W$ 一般的读法.
>
> **为什么是紧读法: 判据说的.** `ghost` ([TreeJudgeBase](TreeJudgeBase.lagda.md)): 把穿过的分支值读进界, 头不读, 就没有证书. 所以按 `Tail` 读: 分支 $b+1$ 就读到 $b+1$, 其余下降到第一支. 恒等读法 `Tc-id` 不选. 这一步不看目标.
>
> `Wr`: 前缀的视图. 只要 $W$ 与后继, 极限, 第 0 层的节点交换. 这些方程对 $a+\_$ 是字面的 (`W₁`), 对迭代由 `cong` 给 (`Wnext`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum using (Ordᴵ; Ordᶜ; add; _+_; Ω; zero; suc; lim; limᵢ; up; _⊑ᴵ_; U)
open import OCF.Align.GuardTightLv
open Lv Dom₀
import OCF.Align.GuardTightUni as Uni
private module Un = Uni Dom₀
open Un using (rb₁; em; ψ¹)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightRd

open RdIter using (c; Y; Ys; Yl; vsS; vlS; sub-adm; tcS; eqL; eqI)
```

## §1 前缀

```agda
record Wr : Set where
  field
    W   : Ordᶜ (suc zero) → Ordᶜ (suc zero)
    Ws  : ∀ u → W (suc u) ≡ suc (W u)
    Wl  : ∀ h → W (lim h) ≡ lim (λ n → W (h n))
    Wi  : ∀ (f : Ordᶜ zero → Ordᶜ (suc zero)) → W (limᵢ zero f) ≡ limᵢ zero (λ y → W (f y))
    Vs  : ∀ y → W (up zero (suc y)) ≡ suc (W (up zero y))
    Vl  : ∀ h → W (up zero (lim h)) ≡ lim (λ n → W (up zero (h n)))
    V0  : W (up zero zero) ≡ W zero
    tc0 : Tc (rb₁ (W zero))

module RdPre (R : Wr) where
  open Wr R

  sym′ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym′ refl = refl

  -- k = 0 的分支: W (up zero y), 即 W (Ω·1) 的分支
  G₀ : Ordᴵ → LG
  G₀ η = rb₁ (W (up zero (em η)))

  I₀ : TailI
  I₀ = record
    { G = G₀ ; t₁ = rb₁ (W (up zero (suc zero)))
    ; toT = λ P → subst (λ z → Cp _ (rb₁ z)) (sym′ (Vs zero)) (suc P)
    ; adT = λ P a → sub-adm (sym′ (Vs zero)) (suc P) a }

  vs₀ : ∀ b {x} (P : Cp x (G₀ (suc b))) → VS G₀ b P
  vs₀ b P with vsS (subst (λ z → Cp _ (rb₁ z)) (Vs (em b)) P)
  ... | inj₂ _ = vS₀
  ... | inj₁ (P′ , tr) = vS₁ P′ (λ E a → tr E (sub-adm (Vs (em b)) P a))

  vl₀ : ∀ f s {x} (P : Cp x (G₀ (lim f s))) → VL G₀ f s P
  vl₀ f s P with vlS {h = λ n → W (up zero (em (f n)))} (subst (λ z → Cp _ (rb₁ z)) (Vl (λ n → em (f n))) P)
  ... | inj₂ _ = vL₀
  ... | inj₁ (n , P′ , tr) = vL₁ n P′ (λ E a → tr E (sub-adm (Vl (λ n → em (f n))) P a))

  rd₀ : Rdr (suc zero) (rb₁ (W (up zero (suc zero)))) (λ η e → G₀ η)
  rd₀ = Tail.rdA I₀ vs₀ vl₀

  Tc-G₀ : ∀ η → Tc (G₀ η)
  Tc-G₀ zero = tcS V0 tc0
  Tc-G₀ (suc b) = tcS (Vs (em b)) (Tc-G₀ b)
  Tc-G₀ (lim f s) = tcS (Vl (λ n → em (f n))) (λ n → Tc-G₀ (f n))

  -- W (Ω·1): 第一个闭包
  Tc-Wc : Tc (rb₁ (W c))
  Tc-Wc = tcS (Wi (up zero)) (rd₀ , Tc-G₀ (suc zero) , (λ η e → Tc-G₀ η))

  -- k ≥ 0: W (Ω·(k+2)) 的分支
  Gk : ℕ → Ordᴵ → LG
  Gk k η = rb₁ (W (Y k (em η)))

  WYs : ∀ k x → W (Y k (suc x)) ≡ suc (W (Y k x))
  WYs k x = trans (cong W (Ys k x)) (Ws _)

  WYl : ∀ k (h : ℕ → Ordᶜ zero) → W (Y k (lim h)) ≡ lim (λ n → W (Y k (h n)))
  WYl k h = trans (cong W (Yl k h)) (Wl _)

  Ik : ℕ → TailI
  Ik k = record
    { G = Gk k ; t₁ = rb₁ (W (Y k (suc zero)))
    ; toT = λ P → subst (λ z → Cp _ (rb₁ z)) (sym′ (WYs k zero)) (suc P)
    ; adT = λ P a → sub-adm (sym′ (WYs k zero)) (suc P) a }

  vsk : ∀ k b {x} (P : Cp x (Gk k (suc b))) → VS (Gk k) b P
  vsk k b P with vsS (subst (λ z → Cp _ (rb₁ z)) (WYs k (em b)) P)
  ... | inj₂ _ = vS₀
  ... | inj₁ (P′ , tr) = vS₁ P′ (λ E a → tr E (sub-adm (WYs k (em b)) P a))

  vlk : ∀ k f s {x} (P : Cp x (Gk k (lim f s))) → VL (Gk k) f s P
  vlk k f s P with vlS {h = λ n → W (Y k (em (f n)))} (subst (λ z → Cp _ (rb₁ z)) (WYl k (λ n → em (f n))) P)
  ... | inj₂ _ = vL₀
  ... | inj₁ (n , P′ , tr) = vL₁ n P′ (λ E a → tr E (sub-adm (WYl k (λ n → em (f n))) P a))

  rdk : ∀ k → Rdr (suc zero) (rb₁ (W (Y k (suc zero)))) (λ η e → Gk k η)
  rdk k = Tail.rdA (Ik k) (vsk k) (vlk k)

  Tc-Y0 : ∀ k → Tc (rb₁ (W (Y k zero)))
  Tc-Gk : ∀ k η → Tc (Gk k η)

  Tc-Y0 zero = Tc-Wc
  Tc-Y0 (suc k) = tcS (trans (cong W (eqL k)) (Wi (Y k))) (rdk k , Tc-Gk k (suc zero) , (λ η e → Tc-Gk k η))

  Tc-Gk k zero = Tc-Y0 k
  Tc-Gk k (suc b) = tcS (WYs k (em b)) (Tc-Gk k b)
  Tc-Gk k (lim f s) = tcS (WYl k (λ n → em (f n))) (λ n → Tc-Gk k (f n))

  -- W (Ω·n)
  Tc-Witer : ∀ n → Tc (rb₁ (W (iter (c +_) zero n)))
  Tc-Witer zero = tc0
  Tc-Witer (suc k) = tcS (cong W (eqI k)) (Tc-Y0 k)

  -- W (ψ₁(1)): ψ₁(1) 是 Ω·n 的极限
  Tc-Wψ : Tc (rb₁ (W (ψ¹ (Ω zero))))
  Tc-Wψ = tcS (Wl (iter (c +_) zero)) Tc-Witer
```

## §2 实例: $a+\_$ 的迭代

`W₁ a tca`: 前缀 $a+\_$. `Wnext`: 前缀再加一个 $a+\_$. 方程都由 `add` 的定义给. `tc0` 是 $W\,0$ 的读法.

```agda
module Pre (a : Ordᶜ (suc zero)) where
  Wm : ℕ → Ordᶜ (suc zero) → Ordᶜ (suc zero)
  Wm zero x = a + x
  Wm (suc m) x = a + Wm m x

  sW : ∀ m u → Wm m (suc u) ≡ suc (Wm m u)
  sW zero u = refl
  sW (suc m) u = cong (a +_) (sW m u)

  lW : ∀ m h → Wm m (lim h) ≡ lim (λ n → Wm m (h n))
  lW zero h = refl
  lW (suc m) h = cong (a +_) (lW m h)

  iW : ∀ m (f : Ordᶜ zero → Ordᶜ (suc zero)) → Wm m (limᵢ zero f) ≡ limᵢ zero (λ y → Wm m (f y))
  iW zero f = refl
  iW (suc m) f = cong (a +_) (iW m f)

  -- a + up zero y 是 add a (suc) y: 对 y 的构造子字面
  Vm : ℕ → Ordᶜ zero → Ordᶜ (suc zero)
  Vm m y = Wm m (up zero y)

  vsW : ∀ m y → Vm m (suc y) ≡ suc (Vm m y)
  vsW zero y = refl
  vsW (suc m) y = cong (a +_) (vsW m y)

  vlW : ∀ m h → Vm m (lim h) ≡ lim (λ n → Vm m (h n))
  vlW zero h = refl
  vlW (suc m) h = cong (a +_) (vlW m h)

  v0W : ∀ m → Vm m zero ≡ Wm m zero
  v0W zero = refl
  v0W (suc m) = cong (a +_) (v0W m)

  -- a·(m+1) 的读法, 对 m 归纳
  x : Ordᶜ (suc zero)
  x = a

  module At (ea : a ≡ ψ¹ (Ω zero)) (tca : Tc (rb₁ a)) where
    Rm  : ℕ → Wr
    tcm : ∀ m → Tc (rb₁ (Wm m zero))

    Rm m = record { W = Wm m ; Ws = sW m ; Wl = lW m ; Wi = iW m ; Vs = vsW m ; Vl = vlW m ; V0 = v0W m ; tc0 = tcm m }

    step : ∀ m → Wm (suc m) zero ≡ Wm m a
    step zero = refl
    step (suc m) = cong (a +_) (step m)

    tcm zero = tca
    tcm (suc m) = tcS (trans (step m) (cong (Wm m) ea)) (RdPre.Tc-Wψ (Rm m))

    -- a + a 与 a·(m+2)
    Tc-m : ∀ m → Tc (rb₁ (Wm m a))
    Tc-m m = subst (λ u → Tc (rb₁ (Wm m u))) (sym′ ea) (RdPre.Tc-Wψ (Rm m))
      where
      sym′ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
      sym′ refl = refl
```
