# 折叠的输出是否世界稳定 (二): `Step` 的状态与读坐标的节点

> 不含记号. 入口 [BrwHW](BrwHW.lagda.md). 折叠 `SumOneClosed` ($S=\cdot\omega$) 在目标第 1 层上的输出. 不变量 `Good Y` 有两半:
>
> - `RS Y Y` (`IY`): 状态在目标第 1 层的一切差 (对一切目标路径 $\tau,\tau'$) 两两 `R2`. 这比 `HW` 强: 要跨世界、跨路径.
> - `HWs Y`: 这些差都 `HW`.
>
> 保持: `⊕` (`⊕R`), `Step` (`StepR`), 换世界 `cv` (`cvR`, 对 `cmpF` 的两个结果), 沿第 0 层坐标的 `Run` (`RunR`, 两边坐标形状相同, 动作把 `RS` 的状态送到 `ΔR` 的差). `RunR` 是**跨世界的模拟**: 两边在不同的世界里沿形状相同的坐标折叠, 输出两两 `R2`.
>
> 由此, **读坐标的节点** `CvFoldInst.Kn` ($\Omega_\Omega$ 回灌闭包在第 0 层那一格的输出, 坐标 $z$ 上的分支是 `Step (Y₂ ⊕ Run z …)`) 对一切 `Good` 状态都 `HW` (`HW-Kn`); 所以 `mid₁` 的前两段 `Aᵐ`, `Pk` 都 `HW` (`HW-A`, `HW-Pk`). 这是第一个由折叠产出、分支读坐标、`HW` 成立的实例.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwHWFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; z⊲; ⊲-tr; cmpF; Tg)
import OCF.Align.CumReadCF as C
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTree using (D; D̂; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; top)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.BrwViewOne using (WSq; HW)
open import OCF.Align.BrwHWBase
open import OCF.Align.CvFoldInst using (Kn; StepA; Aᵐ; Pk; Y₁)
```

## §1 状态之间的关系

```agda
record ΔR {W W′} (Δ : F.Df W) (Δ′ : F.Df W′) : Set where
  constructor δr
  field rr : ∀ (τ : Tg one W) (τ′ : Tg one W′) → R2 (F.yc Δ τ tt) (F.yc Δ′ τ′ tt)
open ΔR public

record RS {W W′} (Z : F.St W) (Z′ : F.St W′) : Set where
  constructor sr
  field rs : ∀ (τ : Tg one W) (τ′ : Tg one W′) → R2 (F.yc (F.d Z) τ tt) (F.yc (F.d Z′) τ′ tt)
open RS public

ΔR-0 : ∀ {W W′} → ΔR (F.zeroD {W}) (F.zeroD {W′})
ΔR-0 = δr (λ τ τ′ → R2-n0)

⊕R : ∀ {W W′} {Z : F.St W} {Z′ : F.St W′} {Δ : F.Df W} {Δ′ : F.Df W′} → RS Z Z′ → ΔR Δ Δ′ → RS (Z F.⊕ Δ) (Z′ F.⊕ Δ′)
⊕R h k = sr (λ τ τ′ → R2-⨾ (rs h τ τ′) (rr k τ τ′))

StepR : ∀ {W W′} {Z : F.St W} {Z′ : F.St W′} → RS Z Z′ → ΔR (F.Step Z) (F.Step Z′)
StepR h = δr (λ τ τ′ → R2-nl (λ _ → R2-⨾ R2-Ω (rs h τ τ′)))

cvR : ∀ {W W′ V V′} (q : W ⊲ V) (lV : Lg V) (q′ : W′ ⊲ V′) (lV′ : Lg V′) {Y : F.St W} {Y′ : F.St W′} →
      RS Y Y′ → RS (F.cv q lV Y) (F.cv q′ lV′ Y′)
cvR q lV q′ lV′ {Y} {Y′} (sr h) = sr go
  where
  go : ∀ τ τ′ → R2 (F.yc (F.d (F.cv q lV Y)) τ tt) (F.yc (F.d (F.cv q′ lV′ Y′)) τ′ tt)
  go (inj₁ τ₁) (inj₁ τ₁′) with cmpF q τ₁ lV | cmpF q′ τ₁′ lV′
  ... | inj₁ a | inj₁ a′ = R2-nwL (R2-nwR (h (inj₁ a) (inj₁ a′)))
  ... | inj₁ a | inj₂ a′ = R2-nwL (R2-nwR (h (inj₁ a) (inj₂ a′)))
  ... | inj₂ a | inj₁ a′ = R2-nwL (R2-nwR (h (inj₂ a) (inj₁ a′)))
  ... | inj₂ a | inj₂ a′ = R2-nwL (R2-nwR (h (inj₂ a) (inj₂ a′)))
  go (inj₁ τ₁) (inj₂ τ₂′) with cmpF q τ₁ lV
  ... | inj₁ a = R2-nwL (h (inj₁ a) (inj₂ (⊲-tr q′ τ₂′)))
  ... | inj₂ a = R2-nwL (h (inj₂ a) (inj₂ (⊲-tr q′ τ₂′)))
  go (inj₂ τ₂) (inj₁ τ₁′) with cmpF q′ τ₁′ lV′
  ... | inj₁ a′ = R2-nwR (h (inj₂ (⊲-tr q τ₂)) (inj₁ a′))
  ... | inj₂ a′ = R2-nwR (h (inj₂ (⊲-tr q τ₂)) (inj₂ a′))
  go (inj₂ τ₂) (inj₂ τ₂′) = h (inj₂ (⊲-tr q τ₂)) (inj₂ (⊲-tr q′ τ₂′))
```

## §2 跨世界的模拟: 沿第 0 层坐标折叠

```agda
module _ {W W′} (lW : Lg W) (lW′ : Lg W′) (ll : azero ⊲ W) (ll′ : azero ⊲ W′)
         (A₀ : F.Ig (cnt azero) W) (A₀′ : F.Ig (cnt azero) W′)
         (hA : ∀ w w′ (Z : F.St W) (Z′ : F.St W′) → RS Z Z′ → ΔR (A₀ C.self lW w Z) (A₀′ C.self lW′ w′ Z′)) where
  RunR : ∀ {W₀ W₀′} (ac ac′ : F.AccY (cnt azero)) {z : D azero W₀} {z′ : D azero W₀′} → Sh z z′ →
         (q : W₀ ⊲ W) (q′ : W₀′ ⊲ W′) → ∀ w w′ Z Z′ → RS Z Z′ →
         ΔR (F.Run ac z q lW ll A₀ w Z) (F.Run ac′ z′ q′ lW′ ll′ A₀′ w′ Z′)
  RptR : ∀ {W₀ W₀′} (ac ac′ : F.AccY (cnt azero)) {d : ℕ → D azero W₀} {d′ : ℕ → D azero W₀′} → (∀ n → Sh (d n) (d′ n)) →
         (q : W₀ ⊲ W) (q′ : W₀′ ⊲ W′) → ∀ w w′ Z Z′ → RS Z Z′ →
         ∀ n → RS (proj₂ (F.Rpt ac d q lW ll A₀ w Z n)) (proj₂ (F.Rpt ac′ d′ q′ lW′ ll′ A₀′ w′ Z′ n))
  RunR ac ac′ sh0 q q′ w w′ Z Z′ h = ΔR-0
  RunR ac ac′ sh1 q q′ w w′ Z Z′ h = hA w w′ Z Z′ h
  RunR ac ac′ (sh⨾ hx hy) q q′ w w′ Z Z′ h = δr (λ τ τ′ →
    R2-⨾ (rr (RunR ac ac′ hx q q′ w w′ Z Z′ h) τ τ′)
         (rr (RunR ac ac′ hy q q′ _ _ _ _ (⊕R h (RunR ac ac′ hx q q′ w w′ Z Z′ h))) τ τ′))
  RunR ac ac′ (shl hd) q q′ w w′ Z Z′ h = δr (λ τ τ′ →
    R2-nl (λ n → rr (RunR ac ac′ (hd n) q q′ _ _ _ _ (RptR ac ac′ hd q q′ w w′ Z Z′ h n)) τ τ′))
  RunR ac ac′ (shwL {p = p} hs) q q′ w w′ Z Z′ h = RunR ac ac′ hs (⊲-tr p q) q′ w w′ Z Z′ h
  RunR ac ac′ (shwR {p = p} hs) q q′ w w′ Z Z′ h = RunR ac ac′ hs q (⊲-tr p q′) w w′ Z Z′ h
  RptR ac ac′ hd q q′ w w′ Z Z′ h zero = h
  RptR ac ac′ hd q q′ w w′ Z Z′ h (suc n) =
    ⊕R (RptR ac ac′ hd q q′ w w′ Z Z′ h n) (RunR ac ac′ (hd n) q q′ _ _ _ _ (RptR ac ac′ hd q q′ w w′ Z Z′ h n))
```

## §3 `HW` 那一半

```agda
record HWs {W} (Y : F.St W) : Set where
  constructor hs
  field hs′ : ∀ (τ : Tg one W) → HW (F.yc (F.d Y) τ tt)
open HWs public

record HWd {W} (Δ : F.Df W) : Set where
  constructor hd
  field hd′ : ∀ (τ : Tg one W) → HW (F.yc Δ τ tt)
open HWd public

HW-⊕ : ∀ {W} {Y : F.St W} {Δ : F.Df W} → HWs Y → HWd Δ → HWs (Y F.⊕ Δ)
HW-⊕ g h = hs (λ τ → hs′ g τ , hd′ h τ)

HW-Step : ∀ {W} {Y : F.St W} → HWs Y → HWd (F.Step Y)
HW-Step g = hd (λ τ → λ _ → HW-Ω , hs′ g τ)

HW-cv : ∀ {W V} (q : W ⊲ V) (lV : Lg V) {Y : F.St W} → HWs Y → HWs (F.cv q lV Y)
HW-cv q lV {Y} (hs g) = hs go
  where
  go : ∀ τ → HW (F.yc (F.d (F.cv q lV Y)) τ tt)
  go (inj₁ τ₁) with cmpF q τ₁ lV
  ... | inj₁ a = g (inj₁ a)
  ... | inj₂ a = g (inj₂ a)
  go (inj₂ τ₂) = g (inj₂ (⊲-tr q τ₂))

module _ {W} (lW : Lg W) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) (hA : ∀ w (Z : F.St W) → HWs Z → HWd (A₀ C.self lW w Z)) where
  HW-Run : ∀ {W₀} (ac : F.AccY (cnt azero)) (z : D azero W₀) (q : W₀ ⊲ W) → ∀ w Z → HWs Z → HWd (F.Run ac z q lW ll A₀ w Z)
  HW-Rpt : ∀ {W₀} (ac : F.AccY (cnt azero)) (d : ℕ → D azero W₀) (q : W₀ ⊲ W) → ∀ w Z → HWs Z →
           ∀ n → HWs (proj₂ (F.Rpt ac d q lW ll A₀ w Z n))
  HW-Run ac n0 q w Z g = hd (λ τ → tt)
  HW-Run ac n1 q w Z g = hA w Z g
  HW-Run ac (x ⨾ y) q w Z g = hd (λ τ → hd′ (HW-Run ac x q w Z g) τ , hd′ (HW-Run ac y q _ _ (HW-⊕ g (HW-Run ac x q w Z g))) τ)
  HW-Run ac (nl d) q w Z g = hd (λ τ → λ n → hd′ (HW-Run ac (d n) q _ _ (HW-Rpt ac d q w Z g n)) τ)
  HW-Run ac (ni () u) q w Z g
  HW-Run ac (nκ () u) q w Z g
  HW-Run ac (nw p x) q w Z g = HW-Run ac x (⊲-tr p q) w Z g
  HW-Rpt ac d q w Z g zero = g
  HW-Rpt ac d q w Z g (suc n) = HW-⊕ (HW-Rpt ac d q w Z g n) (HW-Run ac (d n) q _ _ (HW-Rpt ac d q w Z g n))
```

## §4 不变量

```agda
Good : ∀ {W} → F.St W → Set
Good Y = RS Y Y × HWs Y

Good-⊕Step : ∀ {W} {Y : F.St W} → Good Y → Good (Y F.⊕ F.Step Y)
Good-⊕Step (r , g) = ⊕R r (StepR r) , HW-⊕ g (HW-Step g)

Good-cv : ∀ {W V} (q : W ⊲ V) (lV : Lg V) {Y : F.St W} → Good Y → Good (F.cv q lV Y)
Good-cv q lV (r , g) = cvR q lV q lV r , HW-cv q lV g

Good-0 : ∀ {W} {Y : F.St W} → Good Y → Good (Y F.⊕ F.zeroD)
Good-0 (r , g) = ⊕R r ΔR-0 , HW-⊕ g (hd (λ τ → tt))

Good-Y₀ : Good F.Y₀
Good-Y₀ = sr (λ τ τ′ → R2-n0) , hs (λ τ → tt)
```

## §5 读坐标的节点 `Kn`

照 `CvFoldInst.Kn-CO` 的记法. 分支 `br p l z` 就是 `Kn w Y` 的 `ni` 节点在 $(W',p,l,z)$ 上的分支 (定义相等).

```agda
module KnB (w : D̂ one) (Y : F.St one) where
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
    Rz : D azero W′ → F.Df W′
    Rz z = F.Run ac′ z C.self l ll′ A′ n0 Y₂
    br : D azero W′ → D one W′
    br z = F.yc (F.Step (Y₂ F.⊕ Rz z)) (inj₁ t′) tt

  UI-br : RS Y Y → UI (λ {W′} p l z → br p l z) (λ {W′} p l z → br p l z)
  UI-br r p p′ l l′ sh =
    rr (StepR (⊕R (cvR (p″ p l) l (p″ p′ l′) l′ r)
              (RunR l l′ (ll′ p l) (ll′ p′ l′) (A′ p l) (A′ p′ l′) (λ w w′ Z Z′ h → StepR h)
                    (ac′ p l) (ac′ p′ l′) sh C.self C.self n0 n0 _ _ (cvR (p″ p l) l (p″ p′ l′) l′ r))))
          (inj₁ (t′ p l)) (inj₁ (t′ p′ l′))

  HW-br : HWs Y → ∀ {W′} (p : one ⊲ W′) (l : Lg W′) z → HW (br p l z)
  HW-br g p l z =
    hd′ (HW-Step (HW-⊕ (HW-cv (p″ p l) l g) (HW-Run l (ll′ p l) (A′ p l) (λ w Z g′ → HW-Step g′) (ac′ p l) z C.self n0 _ (HW-cv (p″ p l) l g))))
            (inj₁ (t′ p l))

HW-Kn : ∀ w (Y : F.St one) → Good Y → HW (Kn w Y)
HW-Kn w Y (r , g) = (λ p l z → KnB.HW-br w Y g p l z) ,
                    R2→WSq (R2-ni (λ p l z → KnB.br w Y p l z) (λ p l z → KnB.br w Y p l z) (KnB.UI-br w Y r))

R2-Kn : ∀ w (Y : F.St one) → Good Y → R2 (Kn w Y) (Kn w Y)
R2-Kn w Y (r , g) = R2-ni (λ p l z → KnB.br w Y p l z) (λ p l z → KnB.br w Y p l z) (KnB.UI-br w Y r)
```

## §6 `mid₁` 的前两段

```agda
Good-Y₁ : Good Y₁
Good-Y₁ = Good-cv C.self tt (Good-⊕Step Good-Y₀)

HW-A : HW Aᵐ
HW-A = hd′ (HW-Step (proj₂ Good-Y₀)) (inj₁ C.self)

HW-Pk : HW Pk
HW-Pk = tt , HW-Kn _ (Y₁ F.⊕ F.zeroD) (Good-0 Good-Y₁)
```
