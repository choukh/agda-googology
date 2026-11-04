# 换一步: 换初态 ($\psi(0)=\Omega_\tau$ 这一行)

> 不含记号, 不含旧树. 入口 [AddClo](AddClo.lagda.md). 折叠里 $\psi_t(0)=\Omega_t$ 是两件事: 初态 $Y=0$, 和 `Step` 里加上的 $\Omega_t$. 这里换两种:
>
> 1. **抬高初态**, $\psi_t(0)=\Omega_t+1$ (`GenI`). 同一个世界里不变小 (`RψI`); 也不超过下一个层上的原折叠 (`upI`: $\psi^{+1}_0(\Omega_y)\le\psi_0(\Omega_{y+1})$, 用 [AddCloLeaf](AddCloLeaf.lagda.md)). 对角线的下界在 [AddCloAccept](AddCloAccept.lagda.md).
> 2. **去掉地板**, $\psi_t(0)=0$: 一步仍是 $\cdot\omega$, 只是不加 $\Omega_t$ (`drop`). 一切状态的值都是 $0$ (`runZ`), 对角线的值不超过 $1$ (`TopD≤1`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddCloInit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSum using (D; n0; n1; _⨾_; nl; ni; Dif; Ωd; sum; pt; sum-fst; Lg-sum; AccL; acc; accL; module Fold; module Gen; ω⋅)
import OCF.Align.TLRuleSum as N
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans)
open import OCF.Align.AddCloRel using (Rel; r0; r1; r⨾; rf; rs; rp; rn; reflΩ; sum-mono; module Main)
open import OCF.Align.AddCloStr using (SA; Str; Pz; t0; t1; t⨾; strΩ; sa⊲; saSum; pos≪; SSt-ω; module Run)
open import OCF.Align.AddCloLeaf using (module Leaf)
```

## §1 初态 $\Omega_t+1$

```agda
module GenI where
  δ₁ : ∀ {W} → ∀ {t} → t ⊲ W → D t
  δ₁ _ = n1

  ΨdI : ∀ y → Lg y → D azero
  ΨdI y w = Act {y} C.self (Ωd y C.self w) δ₁ (z⊲ y)
    where open Fold y w ω⋅

  -- 第 0 层: Ω₀, 初态, 差
  XI : ∀ y → Lg y → D azero
  XI y w = n1 ⨾ (n1 ⨾ ΨdI y w)

  ΨI : ∀ y → Lg y → A
  ΨI y w = sum azero (XI y w)

  cellI : ℕ → Σ A Lg
  cellI zero = asuc azero , tt
  cellI (suc n) = ΨI (proj₁ (cellI n)) (proj₂ (cellI n)) , Lg-sum azero (XI (proj₁ (cellI n)) (proj₂ (cellI n))) tt

  TopI : A
  TopI = alim (λ n → proj₁ (cellI (suc n)))

  -- 严格: 初态正, 所以不用单独处理第一格
  strXI : ∀ y w → SA y → Str azero (XI y w)
  strXI y w s = t⨾ t1 (t⨾ t1 (runS (accL y) C.self (λ _ Y → Step Y) (λ _ hY _ → stS hY) (λ _ hY _ → stP hY) t0 (strΩ y C.self w s) (λ _ → t1) (λ _ → tt) (z⊲ y)))
    where
    open Fold y w ω⋅
    open Run y w ω⋅
    stS : ∀ {Y : St} → StS Y → StS (Step Y)
    stS hY {t} τ = proj₁ (SSt-ω (t⨾ (strΩ t C.self (lg⊲ τ w) (sa⊲ τ s)) (hY τ)) (inj₁ (inj₁ tt)))
    stP : ∀ {Y : St} → StS Y → PzS (Step Y)
    stP hY {t} τ = proj₂ (SSt-ω (t⨾ (strΩ t C.self (lg⊲ τ w) (sa⊲ τ s)) (hY τ)) (inj₁ (inj₁ tt)))

  SA-cellI : ∀ n → SA (proj₁ (cellI n))
  SA-cellI zero = tt
  SA-cellI (suc n) = saSum azero tt (strXI (proj₁ (cellI n)) (proj₂ (cellI n)) (SA-cellI n))

  z≪cellI : ∀ n → azero ≪ proj₁ (cellI n)
  z≪cellI zero = C.zero
  z≪cellI (suc n) = pos≪ azero (strXI (proj₁ (cellI n)) (proj₂ (cellI n)) (SA-cellI n)) (inj₁ tt)
```

## §2 同一个世界: 不变小

```agda
  RψI : ∀ y w → Rel azero (n1 ⨾ N.Ψd y w) (XI y w)
  RψI y w = r⨾ r1 (rs (main (accL y) (accL y) C.self C.self refl (λ _ Z → F₁.Step Z) (λ _ Z → F₂.Step Z) hA r0 (reflΩ y C.self w) (λ _ → r0) (z⊲ y)))
    where
    open Main y y C.self w ω⋅ ω⋅
    hA : HA {y} (λ _ Z → F₁.Step Z) (λ _ Z → F₂.Step Z)
    hA _ hY {t} τ = rp (λ _ → r⨾ (reflΩ t C.self (lg⊲ τ w)) (hY τ))

  ΨI≥ : ∀ y w → N.Ψ y w ≤ ΨI y w
  ΨI≥ y w = sum-mono z≤ (RψI y w)
```

## §3 下一个层盖住

$\Omega_{y+1}=\Omega_y+\sum_{z:y}1$. 最后这个节点对 $y$ 以下的目标是链, 链的第一段是状态在 $y$ 的差, 它 $\trianglerighteq\Omega_y$. 所以世界 $y$ 里从初态 $1$ 走 $\Omega_y$, 都被它盖住.

```agda
  upI : ∀ y (w : Lg y) → Rel azero (XI y w) (n1 ⨾ N.Ψd (asuc y) w)
  upI y w = r⨾ r1 (r⨾ (rn 0 (rf (rf r1))) (rs (L.upLeaf (accL y) dX hY (z⊲ y))))
    where
    module L = Leaf (asuc y) w ω⋅ ω⋅ (λ _ _ q → rp (λ _ → q)) {y} C.zero
    open Fold (asuc y) w ω⋅ using (St; Step; Run; _⊕_)
    Y₀ : St
    Y₀ _ = n0
    Y₁ : St
    Y₁ = Y₀ ⊕ Run (accL (asuc y)) C.self (λ _ Z → Step Z) n0 n1 Y₀
    Y₂ : St
    Y₂ = Y₁ ⊕ Run (accL (asuc y)) C.self (λ _ Z → Step Z) (n0 ⨾ n1) (Dif y (z⊲ y) (C.suc C.self) w) Y₁
    dX : Rel y (Ωd y C.self w) (Y₂ (C.suc C.self))
    dX = rf (rs (rn 0 (rf (reflΩ y C.self w))))
    hY : L.RS δ₁ Y₂
    hY τ = rf (rs (rn 0 (rf (rf r1))))

  ΨI≤ : ∀ y w → ΨI y w ≤ N.Ψ (asuc y) w
  ΨI≤ y w = sum-mono z≤ (upI y w)
```

## §4 去掉地板

`drop`: 一步是 $\cdot\omega$, 但扔掉传进来的 $\Omega_t$. 等于 $\psi_t(0)=0$, $\psi_t(a+1)=(\psi_t(a)-\Omega_t)\cdot\omega$ 的差, 从 $0$ 起永远是 $0$.

```agda
drop : ∀ {t} → D t → D t
drop (x ⨾ y) = nl (λ _ → y)
drop _ = n0

Zr : ∀ {k} → D k → Set
Zr n0 = ⊤
Zr n1 = ⊥
Zr (x ⨾ y) = Zr x × Zr y
Zr (nl d) = ∀ n → Zr (d n)
Zr (ni r u) = ∀ z → Zr (u z)

module RunZ (W : A) (lW : Lg W) where
  open Fold W lW drop

  ZS : St → Set
  ZS Y = ∀ {t} (τ : t ⊲ W) → Zr (Y τ)

  HZ : ∀ {k} → (D k → St → St) → Set
  HZ {k} A₀ = ∀ {w} {Y : St} → ZS Y → ZS (A₀ w Y)

  stepZ : ∀ {k} → HZ {k} (λ _ Y → Step Y)
  stepZ hY τ = λ _ → hY τ

  runZ  : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) → HZ A₀ → ∀ w x {Y : St} → ZS Y → ZS (Run ac kp A₀ w x Y)
  rptZ  : ∀ {k} (ac : AccL k) (kp : k ⊲ W) (A₀ : D k → St → St) → HZ A₀ → ∀ w d {Y : St} → ZS Y → ∀ n → ZS (proj₂ (Rpt ac kp A₀ w d Y n))
  chnZ  : ∀ {j} (ac : AccL j) (ρ : j ⊲ W) (A₀ : D j → St → St) → HZ A₀ → ∀ {Y : St} → ZS Y → ∀ n → ZS (proj₂ (proj₂ (Chn ac ρ A₀ Y n)))
  runKZ : ∀ {j k t} (ac : AccL k) (ac′ : AccL j) (r : j ≪ k) (kp : k ⊲ W) (A₀ : D k → St → St) → HZ A₀ → ∀ w u {Y : St} → ZS Y → (τ : t ⊲ W) (c : Rk j t) → Zr (RunK ac ac′ kp A₀ w r u Y τ c)
  aiZ   : ∀ {j k} (ac : AccL k) (ac′ : AccL j) (r : j ≪ k) (kp : k ⊲ W) (A₀ : D k → St → St) → HZ A₀ → ∀ w u → ∀ {z} {Y′ : St} → ZS Y′ → ZS (Ai ac r kp ac′ A₀ w u z Y′)

  runZ ac kp A₀ hA w n0 hY τ = tt
  runZ ac kp A₀ hA w n1 hY τ = hA hY τ
  runZ ac kp A₀ hA w (x ⨾ y) hY τ = runZ ac kp A₀ hA w x hY τ , runZ ac kp A₀ hA (w ⨾ x) y (λ τ′ → hY τ′ , runZ ac kp A₀ hA w x hY τ′) τ
  runZ ac kp A₀ hA w (nl d) hY τ = λ n → runZ ac kp A₀ hA _ (d n) (rptZ ac kp A₀ hA w d hY n) τ
  runZ (acc f) kp A₀ hA w (ni r u) hY τ = runKZ (acc f) (f r) r kp A₀ hA w u hY τ (cmpN (≪∘ r kp) τ lW)

  rptZ ac kp A₀ hA w d hY zero = hY
  rptZ ac kp A₀ hA w d hY (suc n) τ = rptZ ac kp A₀ hA w d hY n τ , runZ ac kp A₀ hA _ (d n) (rptZ ac kp A₀ hA w d hY n) τ

  chnZ ac ρ A₀ hA hY zero = hY
  chnZ ac ρ A₀ hA hY (suc n) τ = chnZ ac ρ A₀ hA hY n τ , runZ ac ρ A₀ hA _ _ (chnZ ac ρ A₀ hA hY n) τ

  aiZ ac ac′ r kp A₀ hA w u {z} hY′ = runZ ac kp A₀ hA _ _ hY′

  runKZ ac ac′ r kp A₀ hA w u hY τ (keep s) = λ y →
    runZ ac kp A₀ hA _ _ (λ τ′ → hY τ′ , runZ ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A₀ w u) (λ {w₁} {Y₁} h → aiZ ac ac′ r kp A₀ hA w u {w₁} {Y₁} h) n0 _ hY τ′) τ
  runKZ ac ac′ r kp A₀ hA w u hY τ (rise _) = λ n →
    runZ ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A₀ w u) (λ {w₁} {Y₁} h → aiZ ac ac′ r kp A₀ hA w u {w₁} {Y₁} h) _ _
      (chnZ ac′ (⊲-tr (≪⊲ r) kp) (Ai ac r kp ac′ A₀ w u) (λ {w₁} {Y₁} h → aiZ ac ac′ r kp A₀ hA w u {w₁} {Y₁} h) hY n) τ

sumZ : ∀ {x} b → Zr {azero} x → sum b x ≤ b
ptZ  : ∀ {d} b → (∀ n → Zr {azero} (d n)) → ∀ n → pt b d n ≤ b
sumZ {x = n0} b z = ≤-refl b
sumZ {x = x ⨾ y} b (zx , zy) = ≤-trans (sumZ (sum b x) zy) (sumZ b zx)
sumZ {x = nl d} b z = l≤ (ptZ b z)
sumZ {x = ni () u} b z
ptZ b z zero = ≤-refl b
ptZ {d = d} b z (suc n) = ≤-trans (sumZ (pt b d n) (z n)) (ptZ b z n)

module D₀ = Gen drop

ΨdZ : ∀ y w → Zr (D₀.Ψd y w)
ΨdZ y w = RunZ.runZ y w (accL y) C.self (λ _ Y → Fold.Step y w drop Y) (λ {w₁} {Y} → RunZ.stepZ y w {y} {w₁} {Y}) n0 (Ωd y C.self w) (λ τ → tt) (z⊲ y)

one : A
one = asuc azero

cellD≤ : ∀ n → proj₁ (D₀.cell n) ≤ one
cellD≤ zero = ≤-refl one
cellD≤ (suc n) = sumZ one (ΨdZ (proj₁ (D₀.cell n)) (proj₂ (D₀.cell n)))

TopD≤1 : D₀.Top ≤ one
TopD≤1 = l≤ (λ n → cellD≤ (suc n))
```
