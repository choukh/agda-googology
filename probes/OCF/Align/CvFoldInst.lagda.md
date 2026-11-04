# 折叠输出与 `Cv` (三): 第一个实例

> 不含记号. 入口 [CvFold](CvFold.lagda.md). `SumOneClosed.Δ₀` ($\psi_0(\Omega_\Omega)$ 一步) 在目标第 1 层的输出 `mid₁` 形如 `A ⨾ (Pk ⨾ nκ …)`:
>
> - `A`: `Step` 的输出 (`Ωd` 与 $\omega$-极限), 分支不读坐标.
> - `Pk`: 回灌闭包 `RunK` 先走到当前世界 (`Kp`) 那一段. 里面有一个由折叠产出、**读坐标**的 `ni`: 坐标 $z$ 上的分支是 `Step (Y₂ ⊕ Run z …)`, 折叠沿 $z$ 走.
> - `nκ …`: 回灌闭包在别的层保留成节点.
>
> 本文: `Step` 的值只单调地依赖状态的值 (`StepV`, 由 `CvFoldSub.S-congʸ`); 于是 `Pk` 满足 `Ok no` 与 `Cv` (**`Pk-CO`**), `round-Cv` 给值上互译 (**`Pk-round`**). `A` 同 (`A-round`). `nκ` 那一段不在 `Ok no` 里, 读不回 (`LayerTrFold.mid-κ`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CvFoldInst where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; ⊲-tr; cmpF; Tg)
import OCF.Align.CumReadCF as C
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; top)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; Sp; toB; Ok; difT)
open import OCF.Align.LayerTrRound using (S-mono; Cv; round-Cv; cw; ≈-refl)
open import OCF.Align.CvFoldSub using (S-congʸ; Cv⁰; Cv⁰→Cv)
import OCF.Align.CvFoldRun as R
open import OCF.Align.LayerTrFold using (mid₁)
```

## §1 `Step` 的值只依赖状态的值

```agda
vv : ∀ {W} → Lg W → one ⊲ W → F.St W → B₁ W
vv lW t1 Y = S C.self lW bz (F.yc (F.d Y) (inj₁ t1) tt)

StepV : ∀ {W} (lW : Lg W) (t1 : one ⊲ W) {c c′ : B₁ W} (Z Z′ : F.St W) → c ≼ c′ → vv lW t1 Z ≼ vv lW t1 Z′ →
        S C.self lW c (F.yc (F.Step Z) (inj₁ t1) tt) ≼ S C.self lW c′ (F.yc (F.Step Z′) (inj₁ t1) tt)
StepV lW t1 {c} {c′} Z Z′ r h = l≼ (λ n → ≼l n (go n))
  where
  yZ = F.yc (F.d Z) (inj₁ t1) tt
  yZ′ = F.yc (F.d Z′) (inj₁ t1) tt
  Ω₁ = OCF.Align.SumOneTree.Ωd one C.self tt
  go : ∀ n → Sp C.self lW c (λ _ → Ω₁ ⨾ yZ) n ≼ Sp C.self lW c′ (λ _ → Ω₁ ⨾ yZ′) n
  go zero = r
  go (suc n) = ≼-trans (S-mono C.self lW yZ (S-mono C.self lW Ω₁ (go n))) (S-congʸ C.self lW _ yZ yZ′ h)
```

## §2 不变量: 状态在目标第 1 层的差树没有 `nκ` 且 `Cv⁰`

```agda
CO : ∀ {W} → D one W → Set
CO x = Ok no x × Cv⁰ x

Gd : ∀ {W} → F.Df W → Set
Gd {W} Δ = ∀ (τ : Tg one W) → CO (F.yc Δ τ tt)

Gs : ∀ {W} → F.St W → Set
Gs Y = Gd (F.d Y)

CO⨾ : ∀ {W} {x y : D one W} → CO x → CO y → CO (x ⨾ y)
CO⨾ (a , b) (a′ , b′) = (a , a′) , (b , b′)

COnl : ∀ {W} {d : ℕ → D one W} → (∀ n → CO (d n)) → CO (nl d)
COnl h = (λ n → proj₁ (h n)) , (λ n → proj₂ (h n))

CO-Ω : ∀ {W} → CO {W} (OCF.Align.SumOneTree.Ωd one C.self tt)
CO-Ω = (tt , (tt , λ p l w → tt)) , (tt , (tt , λ p l w → tt , ≈-refl _))

Gd-⊕ : ∀ {W} (Y : F.St W) (Δ : F.Df W) → Gs Y → Gd Δ → Gs (Y F.⊕ Δ)
Gd-⊕ Y Δ g h τ = CO⨾ (g τ) (h τ)

Gd-Step : ∀ {W} (Y : F.St W) → Gs Y → Gd (F.Step Y)
Gd-Step Y g (inj₁ τ) = COnl (λ _ → CO⨾ CO-Ω (g (inj₁ τ)))
Gd-Step Y g (inj₂ τ) = COnl (λ _ → CO⨾ CO-Ω (g (inj₂ τ)))

Gd-cv : ∀ {W W′} (q : W ⊲ W′) (lW′ : Lg W′) (Y : F.St W) → Gs Y → Gs (F.cv q lW′ Y)
Gd-cv q lW′ Y g (inj₁ τ₁) with cmpF q τ₁ lW′
... | inj₁ t⊲W = g (inj₁ t⊲W)
... | inj₂ W⊲t = g (inj₂ W⊲t)
Gd-cv q lW′ Y g (inj₂ τ₂) = g (inj₂ (⊲-tr q τ₂))

Gd-Run : ∀ {W₀ W} (ac : F.AccY (cnt azero)) (lW : Lg W) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) →
         (∀ w Y → Gs Y → Gd (A₀ C.self lW w Y)) → (z : D azero W₀) (q : W₀ ⊲ W) → ∀ w Y → Gs Y → Gd (F.Run ac z q lW ll A₀ w Y)
Gd-Rpt : ∀ {W₀ W} (ac : F.AccY (cnt azero)) (lW : Lg W) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) →
         (∀ w Y → Gs Y → Gd (A₀ C.self lW w Y)) → (d : ℕ → D azero W₀) (q : W₀ ⊲ W) → ∀ w Y → Gs Y →
         ∀ n → Gs (proj₂ (F.Rpt ac d q lW ll A₀ w Y n))
Gd-Run ac lW ll A₀ ha n0 q w Y g τ = tt , tt
Gd-Run ac lW ll A₀ ha n1 q w Y g = ha w Y g
Gd-Run ac lW ll A₀ ha (x ⨾ y) q w Y g τ =
  CO⨾ (Gd-Run ac lW ll A₀ ha x q w Y g τ) (Gd-Run ac lW ll A₀ ha y q _ _ (Gd-⊕ Y (F.Run ac x q lW ll A₀ w Y) g (Gd-Run ac lW ll A₀ ha x q w Y g)) τ)
Gd-Run ac lW ll A₀ ha (nl d) q w Y g τ = COnl (λ n → Gd-Run ac lW ll A₀ ha (d n) q _ _ (Gd-Rpt ac lW ll A₀ ha d q w Y g n) τ)
Gd-Run ac lW ll A₀ ha (ni () u) q w Y g
Gd-Run ac lW ll A₀ ha (nκ () u) q w Y g
Gd-Run ac lW ll A₀ ha (nw p x) q w Y g = Gd-Run ac lW ll A₀ ha x (⊲-tr p q) w Y g
Gd-Rpt ac lW ll A₀ ha d q w Y g zero = g
Gd-Rpt ac lW ll A₀ ha d q w Y g (suc n) =
  Gd-⊕ (proj₂ (F.Rpt ac d q lW ll A₀ w Y n)) (F.Run ac (d n) q lW ll A₀ (proj₁ (F.Rpt ac d q lW ll A₀ w Y n)) (proj₂ (F.Rpt ac d q lW ll A₀ w Y n)))
    (Gd-Rpt ac lW ll A₀ ha d q w Y g n) (Gd-Run ac lW ll A₀ ha (d n) q _ _ (Gd-Rpt ac lW ll A₀ ha d q w Y g n))
```

## §3 读坐标的那个节点

折叠在目标第 1 层上走顶层节点 `ni self (λ _ _ _ → n1)` (就是 $\Omega_\Omega$ 回灌闭包里第 0 层上的那一格) 得到的树. 分支在坐标 $z$ 上是 `Step (Y₂ ⊕ Run z …)`.

```agda
StepA : F.Ig top one
StepA = F.Ig↾ C.self F.A₁

Kn : OCF.Align.SumOneTree.D̂ one → F.St one → D one one
Kn w Y = F.yc (F.Run F.accTop (ni {k = azero} C.self (λ _ _ _ → n1)) (C.suc C.self) tt tt StepA w Y) (inj₁ C.self) tt

Kn-CO : ∀ w Y → Gs Y → CO (Kn w Y)
Kn-CO w Y g = (λ p l z → proj₁ (brCO p l z)) , (λ p l z → proj₂ (brCO p l z) , brEq p l z)
  where
  kW : azero ⊲ one
  kW = ⊲-tr C.self (C.suc C.self)
  module _ {W′} (p : one ⊲ W′) (l : Lg W′) where
    p″ = ⊲-tr C.self p
    t′ = ⊲-tr C.self p
    ac′ = F.accCn azero
    ll′ = ⊲-tr kW p″
    A′ : F.Ig (cnt azero) W′
    A′ = F.Ig↾ p″ (F.Ai F.accTop C.self (λ _ _ _ → n1) (C.suc C.self) kW tt StepA w)
    Y₂ = F.cv p″ l Y
    gY₂ : Gs Y₂
    gY₂ = Gd-cv p″ l Y g
    Rz : D azero W′ → F.Df W′
    Rz z = F.Run ac′ z C.self l ll′ A′ n0 Y₂
    brCO : ∀ z → CO (F.yc (F.Step (Y₂ F.⊕ Rz z)) (inj₁ t′) tt)
    brCO z = Gd-Step (Y₂ F.⊕ Rz z) (Gd-⊕ Y₂ (Rz z) gY₂ (Gd-Run ac′ l ll′ A′ (λ w Y′ g′ → Gd-Step Y′ g′) z C.self n0 Y₂ gY₂)) (inj₁ t′)
    ha : R.HA l t′ ac′ ll′ A′
    ha w w′ Z Z′ r = StepV l t′ Z Z′ r r
    brEq : ∀ z → S C.self l bz (F.yc (F.Step (Y₂ F.⊕ Rz (cw z))) (inj₁ t′) tt) ≈ S C.self l bz (F.yc (F.Step (Y₂ F.⊕ Rz z)) (inj₁ t′) tt)
    brEq z = StepV l t′ _ _ z≼ (proj₁ c C.self C.self n0 n0 Y₂ Y₂ (≼-refl _)) ,
             StepV l t′ _ _ z≼ (proj₂ c C.self C.self n0 n0 Y₂ Y₂ (≼-refl _))
      where c = R.canon l t′ ac′ ll′ A′ ha z
```

## §4 `mid₁` 的两段

```agda
fstD : ∀ {W} → D one W → D one W
fstD (x ⨾ _) = x
fstD _ = n0

midD : ∀ {W} → D one W → D one W
midD (_ ⨾ (y ⨾ _)) = y
midD _ = n0

Aᵐ Pk : D one one
Aᵐ = fstD mid₁
Pk = midD mid₁

gY₀ : Gs F.Y₀
gY₀ τ = tt , tt

A-CO : CO Aᵐ
A-CO = Gd-Step F.Y₀ gY₀ (inj₁ C.self)

Y₁ : F.St one
Y₁ = F.cv C.self tt (F.Y₀ F.⊕ F.Step F.Y₀)

Pk-CO : CO Pk
Pk-CO = CO⨾ (tt , tt) (Kn-CO _ (Y₁ F.⊕ F.zeroD)
  (Gd-⊕ Y₁ F.zeroD (Gd-cv C.self tt (F.Y₀ F.⊕ F.Step F.Y₀) (Gd-⊕ F.Y₀ (F.Step F.Y₀) gY₀ (Gd-Step F.Y₀ gY₀))) (λ τ → tt , tt)))

Pk-round : toB tt (difT tt Pk (proj₁ Pk-CO)) ≈ toB tt Pk
Pk-round = round-Cv tt Pk (proj₁ Pk-CO) (Cv⁰→Cv Pk (proj₂ Pk-CO))

A-round : toB tt (difT tt Aᵐ (proj₁ A-CO)) ≈ toB tt Aᵐ
A-round = round-Cv tt Aᵐ (proj₁ A-CO) (Cv⁰→Cv Aᵐ (proj₂ A-CO))
```
