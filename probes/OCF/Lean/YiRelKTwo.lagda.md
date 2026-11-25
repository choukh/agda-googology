# 一般折叠引理在 k = 2 的实例: ψ₀(Ω_Ω+Ω₃) 的条件定理

验收文件. 接口 [YiRelKFold](YiRelKFold.lagda.md) `Pf` 在 k = 2 (前缀 `G₃`, 目标层 0, 1, 2) 上的实例 `P₂ᴵ`, 前提是 `Rel 2` 上的第 2 层对角定理 `Diag₂ᴿ` (模块参数); 除它外字段都是编译定理 (派发事实都是 `refl`). 编译定理 (条件): `e₃⊴γ₃ᴿ`, `sync₃ᴿ`, `X₃≼ᴿ : X₃ ≼ NA.read W.TΛ`; `X₃≼ᵀ : Diag₂ᵀ → X₃ ≼ NA.read W.TΛ` 经 `from2` 重新得到 [YiStepThree](YiStepThree.lagda.md) 的 `X₃≼ᵈ`; `X₃≼ʰ : Chain₂ᴿ → …` 把前提归约到 `Rel 2` 上的第 2 层 BTBO 链点 (未走通).
参照 `X₃` 读作 ψ₀(Ω_Ω+Ω₃), 读法是判断. 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRelKTwo where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; up≼)
open import OCF.Lean.YiDlVBtbo using (btbo-Tw2)
open import OCF.Lean.YiShpSq using (ψ₁)
open import OCF.Lean.YiShpTwo using (σB)
open import OCF.Lean.YiSyncFold using (Z⊴)
open import OCF.Lean.YiStepTree using (L2; R₂; G₃; G₃′; G₃″; K₀; ψ₂; γ₃; σ₃; σ₃′; e₃; X₃; Sync₃; X₃≼ᶜ)
open import OCF.Lean.YiStepPfx using (P₃′; mG₃′; module Pfx)
open import OCF.Lean.YiStepFold2 using (mG₃; sG₃; cp₂; cp₁; thrp)
open import OCF.Lean.YiStepThree using (Diag₂ᵀ; e₃-self)
open import OCF.Lean.YiStepTree using (Tψ₂; K₂)
open import OCF.Lean.YiStepDiag2 using (F₂; F₂0⊴K; Chain₂)
open import OCF.Lean.YiSyncDiag using (c₁)
open import OCF.Lean.YiShpOmega using (cpT)
open import OCF.Lean.YiL1Base using (ξ)
open import OCF.Align.YiLvVal2 using (ℓ₂)
import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiRelK
open import OCF.Lean.YiRelKInst using (from1; from2)
open import OCF.Lean.YiRelKFold
```

## 1 目标层与各层的折叠

```agda
T2 : ℕ → Set
T2 zero = ⊤
T2 (suc zero) = ⊤
T2 (suc (suc zero)) = ⊤
T2 (suc (suc (suc _))) = ⊥

open FoldK S2.ℓ₀ T2

ψt : ∀ t → Raw (tw 2) → Raw (Lk t)
ψt zero = Ψ₀
ψt (suc zero) = ψ₁
ψt (suc (suc zero)) = ψ₂
ψt (suc (suc (suc t))) _ = G.zero

ψt-cp : ∀ t → T2 t → ∀ {A B} → Cp (tw 2) A B → Cp (Lk t) (ψt t A) (ψt t B)
ψt-cp zero _ c = W.Ψ-cp zero V2 (λ _ → fold) c
ψt-cp (suc zero) _ c = cp₁ c
ψt-cp (suc (suc zero)) _ c = cp₂ c

ψt-s : ∀ t → T2 t → ∀ {A B} → Cp (tw 2) (G.suc A) B → Cp (Lk t) (succ (Lk t) (ψt t A)) (ψt t B)
ψt-s zero _ c = W.Ψ-cp zero V2 (λ _ → fold) c
ψt-s (suc zero) _ c = cp₁ c
ψt-s (suc (suc zero)) _ c = cp₂ c

limR : ∀ t {ℓ} {F : ℕ → L.Ordᶜ ℓ} {H : ℕ → Raw (Lk t)} → (∀ n → Rel t (F n) (H n)) → Rel t (L.lim F) (G.lim H)
limR t h = Rel-ll t (λ n → Rel-cp t (h n) (inj₂ (n , inj₁ refl)))

pb : ∀ {K j} → Path K j → j ≤ K
pb here = ≤-refl
pb (there π) = ≤-trans (n≤1+n _) (pb π)

no3 : ∀ {j} → suc (suc (suc j)) ≤ 2 → ⊥
no3 (s≤s (s≤s ()))

no2 : ∀ {j} → suc (suc j) ≤ 1 → ⊥
no2 (s≤s ())

no1 : ∀ {j} → suc j ≤ 0 → ⊥
no1 ()

one≺two : ℓk 1 ≺ᴵ ℓk 2
one≺two = L.via (L.≅ᴵ-refl _) L.zero
```

## 2 实例

`Diag₂ᴿ` 是唯一的前提; 第 1 层的对角线用 [YiSyncFold](YiSyncFold.lagda.md) 的 `Z⊴` (无前提), 第 0 层用 `btbo-Tw2`.

```agda
Diag₂ᴿ : Set
Diag₂ᴿ = Rel 2 (L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀)) (ψ₂ G.top)

module Inst (D₂ : Diag₂ᴿ) where

  Zᴳ : ∀ (B : Raw (tw 2)) t → T2 t → ∀ {i} (q : i <ᴵ S2.ℓ₀) → i ≅ᴵ ℓk t →
    Rel t (L.ψ q (λ r → r) (L.Ω S2.ℓ₀)) (ψt t (plus (tw 2) G.top B))
  Zᴳ B zero _ q L.z≅ = ≼-trans (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = q} {σ = λ r → r} (L.Ω-refl S2.ℓ₀))))
    (≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top B)))
  Zᴳ B (suc zero) _ q (L.s≅ L.z≅) =
    ≅⊴ (L.ψ-≅ {p = q} {σ = λ r → r} {p′ = σB L.zero} {σ′ = λ r → r} (L.≅ᴵ-refl _) (L.Ω-refl S2.ℓ₀))
      (from1 (Z⊴ B))
  Zᴳ B (suc (suc zero)) _ q (L.s≅ (L.s≅ L.z≅)) =
    ≅⊴ (L.ψ-≅ {p = q} {σ = λ r → r} {p′ = σ₃ L.zero} {σ′ = λ r → r} (L.≅ᴵ-refl _) (L.Ω-refl S2.ℓ₀))
      (Rel-cp 2 D₂ (cp₂ (plus-weak (tw 2) G.top B)))
```

第 0 层 (`G₃″`, 树在层号 0 的嵌入上):

```agda
  mG₃″ : ∀ {a b} → Cp zero a b → Cp (tw 2) (G₃″ a) (G₃″ b)
  mG₃″ c = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc K₀ (W.Ψ-cp (tw 2) WL.w0 _ c))

  P₀ᴵ : Pf zero (λ t a → ψt t (G₃″ a))
  P₀ᴵ = record
    { Z = λ t tg q ei η → Zᴳ _ t tg q ei
    ; mΦ = λ t tg c → ψt-cp t tg (mG₃″ c)
    ; sΦ = λ t tg η → ψt-s t tg (Pfx.sA P₃′ η)
    ; tgN = λ π → ⊥-elim (no1 (pb π))
    ; kΦ = λ t tg π → ⊥-elim (no1 (pb π))
    ; fΦ = λ t tg π → ⊥-elim (no1 (pb π))
    ; dkΦ = λ m tg ()
    ; dfΦ = λ ()
    ; tp = λ t tg → ψt-s t tg (Pfx.tA P₃′)
    ; dn = tt }
```

第 1 层 (`G₃′`): 唯一的结点位置是层号 0 的 `inj₁ tt`; 目标层 2, 1 保留, 目标层 0 折叠.

```agda
  kΦ₁ : ∀ t → T2 t → ∀ {j} (π : Path 1 (suc j)) → ℓk j ≺ᴵ ℓk t →
    ∀ {i ℓ} {p : i <ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} {g : Raw (Lk j) → Raw (Lk 1)} → i ≅ᴵ ℓk j →
    (∀ (y : L.Ordᶜ i) a → Rel j y a → y L.≅ y → Rel t (f (L.into (L.<→◃ p) y)) (ψt t (G₃′ (g a)))) →
    Rel t (L.limᵢ p f) (ψt t (G₃′ (bld π (inj₁ tt) g)))
  kΦ₁ zero _ here (L.via e ())
  kΦ₁ (suc zero) _ here lt e h = nd e h
  kΦ₁ (suc (suc zero)) _ here lt e h = nd e h
  kΦ₁ t _ (there π) = ⊥-elim (no2 (pb π))

  fΦ₁ : ∀ t → T2 t → ∀ {j} (π : Path 1 (suc j)) → ¬ (ℓk j ≺ᴵ ℓk t) →
    ∀ {g : Raw (Lk j) → Raw (Lk 1)} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
    (∀ n → Rel t (F n) (ψt t (G₃′ (g (chain (Lk j) (λ a → ψt j (G₃′ (g a))) n))))) →
    Rel t (L.lim F) (ψt t (G₃′ (bld π (inj₁ tt) g)))
  fΦ₁ zero _ here nl h = limR zero h
  fΦ₁ (suc zero) _ here nl h = ⊥-elim (nl (zero≺ 0))
  fΦ₁ (suc (suc zero)) _ here nl h = ⊥-elim (nl (zero≺ 1))
  fΦ₁ t _ (there π) = ⊥-elim (no2 (pb π))

  dkΦ₁ : ∀ m → T2 (suc m) → ∀ {r} (z : Z0 1 r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
    (∀ n a → Cp zero thr a → Rel (suc m) (F n) (ψt (suc m) (G₃′ (g (toA z a))))) →
    Rel (suc m) (L.lim F) (ψt (suc m) (G₃′ (G.lc r g)))
  dkΦ₁ zero _ z1 h = dg z1 h
  dkΦ₁ (suc zero) _ z1 h = dg (zs z1) h
  dkΦ₁ m _ (zs ())

  dfΦ₁ : ∀ {r} (z : Z0 1 r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
    (∀ n a → Cp zero thr a → Rel zero (F n) (Ψ₀ (G₃′ (g (toA z a))))) → Rel zero (L.lim F) (Ψ₀ (G₃′ (G.lc r g)))
  dfΦ₁ z1 h = Rel-ll zero (λ n → Rel-cp zero (h n _ (thrp _)) (inj₂ (1 , inj₁ refl)))
  dfΦ₁ (zs ())

  tp₁ : ∀ t → ψt t (G₃′ G.top) ≡ ψt t (G₃′ (G.lc (inj₁ tt) (λ a → G.em tt a)))
  tp₁ zero = refl
  tp₁ (suc zero) = refl
  tp₁ (suc (suc zero)) = refl
  tp₁ (suc (suc (suc t))) = refl

  P₁ᴵ : Pf 1 (λ t a → ψt t (G₃′ a))
  P₁ᴵ = record
    { Z = λ t tg q ei η → Zᴳ _ t tg q ei
    ; mΦ = λ t tg c → ψt-cp t tg (mG₃′ c)
    ; sΦ = λ t tg η → ψt-s t tg (Pfx.sG P₃′ η)
    ; tgN = λ { here → tt ; (there π) → ⊥-elim (no2 (pb π)) }
    ; kΦ = kΦ₁ ; fΦ = fΦ₁ ; dkΦ = dkΦ₁ ; dfΦ = dfΦ₁
    ; tp = tp₁
    ; dn = P₀ᴵ }
```

第 2 层 (`G₃`): 结点位置是层号 1 的 `inj₁ tt` (目标层 2 保留, 1, 0 折叠成层号 1 的链) 与层号 0 的 `inj₂ (inj₁ tt)` (目标层 2, 1 保留, 0 折叠).

```agda
  kΦ₂ : ∀ t → T2 t → ∀ {j} (π : Path 2 (suc j)) → ℓk j ≺ᴵ ℓk t →
    ∀ {i ℓ} {p : i <ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} {g : Raw (Lk j) → Raw (Lk 2)} → i ≅ᴵ ℓk j →
    (∀ (y : L.Ordᶜ i) a → Rel j y a → y L.≅ y → Rel t (f (L.into (L.<→◃ p) y)) (ψt t (G₃ (g a)))) →
    Rel t (L.limᵢ p f) (ψt t (G₃ (bld π (inj₁ tt) g)))
  kΦ₂ zero _ here (L.via e ())
  kΦ₂ (suc zero) _ here lt e h = ⊥-elim (L.≺ᴵ-irrefl lt)
  kΦ₂ (suc (suc zero)) _ here lt e h = nd e h
  kΦ₂ zero _ (there here) (L.via e ())
  kΦ₂ (suc zero) _ (there here) lt e h = nd e h
  kΦ₂ (suc (suc zero)) _ (there here) lt e h = nd e h
  kΦ₂ t _ (there (there π)) = ⊥-elim (no3 (pb π))

  fΦ₂ : ∀ t → T2 t → ∀ {j} (π : Path 2 (suc j)) → ¬ (ℓk j ≺ᴵ ℓk t) →
    ∀ {g : Raw (Lk j) → Raw (Lk 2)} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
    (∀ n → Rel t (F n) (ψt t (G₃ (g (chain (Lk j) (λ a → ψt j (G₃ (g a))) n))))) →
    Rel t (L.lim F) (ψt t (G₃ (bld π (inj₁ tt) g)))
  fΦ₂ zero _ here nl h = limR zero h
  fΦ₂ (suc zero) _ here nl h = limR 1 h
  fΦ₂ (suc (suc zero)) _ here nl h = ⊥-elim (nl one≺two)
  fΦ₂ zero _ (there here) nl h = limR zero h
  fΦ₂ (suc zero) _ (there here) nl h = ⊥-elim (nl (zero≺ 0))
  fΦ₂ (suc (suc zero)) _ (there here) nl h = ⊥-elim (nl (zero≺ 1))
  fΦ₂ t _ (there (there π)) = ⊥-elim (no3 (pb π))

  dkΦ₂ : ∀ m → T2 (suc m) → ∀ {r} (z : Z0 2 r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
    (∀ n a → Cp zero thr a → Rel (suc m) (F n) (ψt (suc m) (G₃ (g (toA z a))))) →
    Rel (suc m) (L.lim F) (ψt (suc m) (G₃ (G.lc r g)))
  dkΦ₂ zero _ (zs z1) h = dg z1 h
  dkΦ₂ (suc zero) _ (zs z1) h = dg (zs z1) h
  dkΦ₂ m _ (zs (zs ()))

  dfΦ₂ : ∀ {r} (z : Z0 2 r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
    (∀ n a → Cp zero thr a → Rel zero (F n) (Ψ₀ (G₃ (g (toA z a))))) → Rel zero (L.lim F) (Ψ₀ (G₃ (G.lc r g)))
  dfΦ₂ (zs z1) h = Rel-ll zero (λ n → Rel-cp zero (h n _ (thrp _)) (inj₂ (1 , inj₁ refl)))
  dfΦ₂ (zs (zs ()))

  tp₂ : ∀ t → ψt t (G₃ G.top) ≡ ψt t (G₃ (G.lc (inj₁ tt) (λ a → G.em tt a)))
  tp₂ zero = refl
  tp₂ (suc zero) = refl
  tp₂ (suc (suc zero)) = refl
  tp₂ (suc (suc (suc t))) = refl

  tgN₂ : ∀ {j} → Path 2 (suc j) → T2 j
  tgN₂ here = tt
  tgN₂ (there here) = tt
  tgN₂ (there (there π)) = ⊥-elim (no3 (pb π))

  P₂ᴵ : Pf 2 (λ t a → ψt t (G₃ a))
  P₂ᴵ = record
    { Z = λ t tg q ei η → Zᴳ _ t tg q ei
    ; mΦ = λ t tg c → ψt-cp t tg (mG₃ c)
    ; sΦ = λ t tg η → ψt-s t tg (sG₃ η)
    ; tgN = tgN₂
    ; kΦ = kΦ₂ ; fΦ = fΦ₂ ; dkΦ = dkΦ₂ ; dfΦ = dfΦ₂
    ; tp = tp₂
    ; dn = P₁ᴵ }
```

## 3 链上逐点与 ψ₀(Ω_Ω+Ω₃)

```agda
  e₃⊴γ₃ᴿ : ∀ n → Rel 2 (e₃ n) (γ₃ n)
  e₃⊴γ₃ᴿ zero = Ω⊴top 1
  e₃⊴γ₃ᴿ (suc n) = Rel-+ˡ 1 (γ₃ n)
    (Fold 2 P₂ᴵ 2 tt (σ₃ L.zero) (L.≅ᴵ-refl _) σ₃′ (e₃⊴γ₃ᴿ n) (e₃-self n))

  q₀ : L.zero <ᴵ S2.ℓ₀
  q₀ = L.lim 0 L.zero

  sync₃ᴿ : Sync₃
  sync₃ᴿ n = ≼-trans (≅→≼ (L.ψ⁰≅ψ {p = q₀} {σ = λ r → r} (L.add-≅ {σ = σ₃′} {σ′ = σ₃′} (L.Ω-refl S2.ℓ₀) (e₃-self n))))
    (Fold 2 P₂ᴵ 0 tt q₀ L.z≅ σ₃′ (e₃⊴γ₃ᴿ n) (e₃-self n))

X₃≼ᴿ : Diag₂ᴿ → X₃ ≼ NA.read W.TΛ
X₃≼ᴿ D₂ = X₃≼ᶜ (Inst.sync₃ᴿ D₂)

X₃≼ᵀ : Diag₂ᵀ → X₃ ≼ NA.read W.TΛ
X₃≼ᵀ D = X₃≼ᴿ (from2 D)
```

## 4 前提归约到 `Rel 2` 上的第 2 层 BTBO 链点

`Chain₂ᴿ` 是 [YiStepDiag2](YiStepDiag2.lagda.md) `Chain₂` 换成 `Rel 2` (`chain₂→`, 所以不更强); 第 0 项经 `from2` 用 `F₂0⊴K`.

```agda
Chain₂ᴿ : Set
Chain₂ᴿ = ∀ n → Σ ℕ (λ m → Rel 2 (F₂ (suc n)) (K₂ (G.suc (ξ m))))

chain₂→ : Chain₂ → Chain₂ᴿ
chain₂→ h n = proj₁ (h n) , from2 (proj₂ (h n))

chain→diagᴿ : Chain₂ᴿ → Diag₂ᴿ
chain→diagᴿ h = dg (zs z1) F⊴K
  where
  F⊴K : ∀ n a → Cp zero thr a → Rel 2 (F₂ n) (K₂ a)
  F⊴K zero a c = from2 (F₂0⊴K a c)
  F⊴K (suc n) a c = Rel-cp 2 (proj₂ (h n))
    (WL.Kfk-cp zero Tψ₂ (cpT zero (add-cp zero G.lc dnLc G.top (c₁ (proj₁ (h n)))) c))

X₃≼ʰ : Chain₂ᴿ → X₃ ≼ NA.read W.TΛ
X₃≼ʰ h = X₃≼ᴿ (chain→diagᴿ h)
```
