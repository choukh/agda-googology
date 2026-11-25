# 抽象理论 (三): 框架的实填与三条否定的重推

> 验收文件 (实填与否定). 判决: 编译定理. 空白页的块连同 `YiPhiIface.Iface` 的任何实例填进 `YiAbsFrame` 的框架 (`blk`, `fold`); `phi` (YiPhi 的折叠) 与 `upφ` (YiUp 的上折折叠) 都是实例. 后继与 ℕ 极限层号上 `Hand` 成立 (`hand-suc`, `hand-lim`), 一致目标的 `HandU` 在三种层号上成立, `Mono`, `Pres` 成立.
> 三条具体否定由抽象定理重推: `wdec′` (即 `YiPhiNegB.wdec`, 经 `hand→wdec`), `flat-sep` (即 `YiUpNegFlat.flat→wdec` 的前提, 经 `Sep`), `fullSem→lpo′` (即 `YiPhiNegKSem.fullSem→lpo`, 经 `Slot.full→dec`). 前两条同属 (E), 第三条属 (S).
> 不否定什么: 两个实例都不满足 `Hand (tw 3)` (`phi-not-hand`, `up-not-hand`), 都满足 `Ωb-off`. 前提的实例: `off-phi`, `off-up`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; LN)
open import OCF.Lean.YiPhiBlock
import OCF.Lean.YiPhiIface as PI
import OCF.Lean.YiUpIface as UI
open import OCF.Lean.YiPhiCheck using (phi)
open import OCF.Lean.YiUpCheck using (upφ)
open import OCF.Lean.YiPhiNegB
  using (c₀; cα; ev; h₃; wc; y₀; y₁; top₁; isΩb; eq→allF; plus-ι; J2-Ωb; Ωb-off; off-phi; module Probe)
open import OCF.Lean.YiPhiNegKSem
  using (FullSem; Kα; hα; εα; t₂; Oα; two; isTwo; found→slot; two→true; hit; hit-found)
import OCF.Lean.YiUpNegFlat as NF
open import OCF.Lean.YiAbsObs
open import OCF.Lean.YiAbsFrame
```

## 块

```agda
incᴸ : ∀ {j} (ℓ : L) (c : Ch ℓ) → j ≤ chL ℓ c → j ≤ ℓ
incᴸ (suc a)  _ w = ins w
incᴸ (lim g)  n w = inl n w
incᴸ (Ωₗ k h) c w = inb c w

incUᴸ : ∀ {j} (ℓ : L) → Ch ℓ → ((c : Ch ℓ) → j ≤ chL ℓ c) → j ≤ ℓ
incUᴸ (suc a)  _ ws = ins (ws tt)
incUᴸ (lim g)  _ ws = inlu ws
incUᴸ (Ωₗ k h) _ ws = inu ws

blk : Block
blk = record
  { Lv = L ; Tr = Tr ; Ch = Ch ; chL = chL ; ChT = ChT ; chT = chT
  ; _⊑_ = _≤_ ; self = self ; inc = incᴸ ; incU = incUᴸ ; up = up ; hd = isΩb
  ; _◃_ = λ {ℓ} x y → ℓ ⊢ x ◃ y ; Leg = λ {ℓ} x → LN ℓ x }
```

## 折叠

底是层号证据与 `Base` 的对; 孩子的底按层号的形状取接口的 `dS`, `dL`, `dW`.

```agda
module _ (I : PI.Iface) where
  open PI.Iface I

  dnᴸ : (ℓ : L) → Ev ℓ × Base ℓ → (c : Ch ℓ) → Tr ℓ → Ev (chL ℓ c) × Base (chL ℓ c)
  dnᴸ (suc a)  (ε , B) _ x = ε , dS a ε B x
  dnᴸ (lim g)  (ε , B) n x = ε n , dL g ε B n x
  dnᴸ (Ωₗ k h) (ε , B) c x = proj₂ (proj₂ ε c) , dW k h ε B c x

  fold : Fold blk
  fold = record
    { Bs   = λ ℓ → Ev ℓ × Base ℓ
    ; LegB = λ ℓ b → PI.LegB ℓ (proj₂ b)
    ; Bt   = Tr
    ; LegT = LN
    ; ψ    = λ ℓ b j w β x → ψs ℓ (proj₁ b) (proj₂ b) j w β x
    ; ψβ   = λ ℓ b j w β x → ψs ℓ (proj₁ b) (proj₂ b) j w β x
    ; dn   = dnᴸ }

  open Fold fold using (Hand; HandU; Mono; Pres; Offᴾ)

  hand-suc : (a : L) → Hand (suc a)
  hand-suc a (ε , B) j c w β x y = J2-suc a ε B j w β x y

  hand-lim : (g : ℕ → L) → Hand (lim g)
  hand-lim g (ε , B) j n w β x y = J2-lim g ε B n j w β x y

  hand-Ω : J2-Ωb I → (k : L) (h : Tr k → L) → Hand (Ωₗ k h)
  hand-Ω J k h (ε , B) j c w β x y = J k h ε B j c w β x y

  handU-suc : (a : L) → HandU (suc a)
  handU-suc a (ε , B) j c₁ ws β x c y = J2-suc a ε B j (ws tt) β x y

  handU-lim : (g : ℕ → L) → HandU (lim g)
  handU-lim g (ε , B) j c₁ ws β x n y = J2-limu g ε B j ws β x n y

  handU-Ω : (k : L) (h : Tr k → L) → HandU (Ωₗ k h)
  handU-Ω k h (ε , B) j c₁ ws β x c y = J2-Ωu k h ε B j ws β x c y

  mono : Mono
  mono ℓ b j w β d = monos ℓ (proj₁ b) (proj₂ b) j w β d

  pres : Pres
  pres ℓ b lb j w β lβ x lx = press ℓ (proj₁ b) (proj₂ b) lb j w β lβ x (proj₁ lx)
```

## (E) 分支侧同支交接: `wdec` 的重推

探针取自 `YiPhiNegB`: 塔第 3 项, 目标 tw 1, 嵌入在孩子 c₀ 里. `on` 是接口的 `J2-limu` 与 `kstep` (孩子自己的折叠保留结点).

```agda
  probe : Fold.Probe fold (tw 3)
  probe = record
    { b = Ev-tw 3 , B₀ (tw 3) ; j = tw 1 ; β = Ωt (tw 1) ; x = zero ; c₀ = c₀ ; y = y₀ ; w = wc
    ; on = cong isΩb (trans (J2-limu (λ m → h₃ (ev m)) (proj₂ (proj₂ (Ev-tw 3) c₀)) _ (tw 1)
                                     (λ m → wc (ev m)) _ zero zero y₁)
                            (kstep 1 _ _ zero top₁ (λ _ → zero))) }

  offᴾ : Ωb-off I → Offᴾ probe
  offᴾ F = Probe.off I F

  wdec′ : Hand (tw 3) → Ωb-off I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
  wdec′ H F = Fold.hand→wdec fold H probe (offᴾ F)

  cantor : Cantor c₀
  cantor = record { cα = cα ; eq→allF = eq→allF }

  wdecα′ : Hand (tw 3) → Ωb-off I → ∀ α → AllF α ⊎ (c₀ ≡ cα α → ⊥)
  wdecα′ H F = Fold.hand→wdecα fold H probe (offᴾ F) cantor
```

两个实例都不满足 `Hand (tw 3)`: 对角上它们也回退, 头部为假.

```agda
  diag-head : Hand (tw 3) → isΩb (Probe.O I c₀) ≡ true
  diag-head H = trans (cong isΩb (H (Ev-tw 3 , B₀ (tw 3)) (tw 1) c₀ (wc c₀) (Ωt (tw 1)) zero y₀))
                      (Fold.Probe.on probe)

  fb-head : isΩb (Probe.fb I) ≡ false
  fb-head = plus-ι (ψs (tw 3) (Ev-tw 3) (B₀ _) (tw 1) (inb c₀ (wc c₀)) (Ωt (tw 1)) zero)
                   (ψ⊥ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (B₀ (h₃ c₀)) y₀) (Probe.nz I)

phi-not-hand : Fold.Hand (fold phi) (tw 3) → ⊥
phi-not-hand H = t≢f (trans (sym (diag-head phi H)) (fb-head phi))

off-up : Ωb-off upφ
off-up k h ε B j c c′ w β x y ne = refl

up-not-hand : Fold.Hand (fold upφ) (tw 3) → ⊥
up-not-hand H = t≢f (trans (sym (diag-head upφ H)) (fb-head upφ))
```

## (E) 摊平后的同支保留: `flat→wdec` 的前提是同一个 `Sep`

```agda
flat-sep : (I : UI.Iface) → NF.FlatKeep I → NF.FlatOff I → Sep c₀
flat-sep I K F = record
  { f   = λ c′ → isΩb (NF.O I (Ωt (tw 3)) c′)
  ; on  = NF.kept-isΩ _ (NF.keep₀ I K (Ωt (tw 3)))
  ; off = NF.off₀ I F (Ωt (tw 3)) }

flat→wdec′ : (I : UI.Iface) → NF.FlatKeep I → NF.FlatOff I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)
flat→wdec′ I K F = sep→wdec (flat-sep I K F)
```

## (S) 按层号相等的 "能保留处都保留": `fullSem→lpo` 的重推

```agda
rootT : ∀ {ℓ} → Tr ℓ → Maybe (Pos ℓ)
rootT (Ω q _) = just q
rootT _       = nothing

fullSem→lpo′ : (I : PI.Iface) → FullSem I → LPO
fullSem→lpo′ I F α =
  Slot.full→dec (at (Kα α)) two rootT isTwo refl (Oα I α) full (found→slot α) hp
  where
  full : Slot.Full (at (Kα α)) two rootT (Oα I α)
  full has with F (Kα α) (hα α) (εα α) (B₀ _) zero zero zero (t₂ α) (λ _ → zero) has
  ... | q , G′ , eq , l = q , cong rootT eq , l
  hp : (q : Pos (Kα α)) → isTwo (at (Kα α) q) ≡ true → Found α
  hp (m , s) e = hit-found α m (two→true (hit α m) s e)
```
