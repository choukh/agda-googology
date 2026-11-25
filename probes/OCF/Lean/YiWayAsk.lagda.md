# 产出端折叠的值问到的那个结点: 链的第一步在 ℕ 极限层号的位置上保留

验收文件. 编译定理 `askedᵖ : NA.read (Fo ξaᵖ) ≼ NA.read T⁺ʷᵖ`, `asked-nodeᵖ`, `asked-stepᵖ` (对一切 `m`, 不高于 `Stepᵖ` 结论里的 `Fo (dᵖ (suc m))`); 有限测试 (`refl`) `markedᵖ`, `keptᵖ`, `lostᵖ`: 坐标 `ξaᵖ` (照 [YiDlVLost](YiDlVLost.lagda.md), `Tw 2` 换成产出端内层折叠的根值 `Bi`) 处结点 `rNᵖ` 的链第一步里, 位置 `pNᵖ` (层号是 ℕ 极限, 同 [YiDlLost](YiDlLost.lagda.md) 的搜索路径) 上的结点带证据 `refl`, 派发保留; 不带证据时折叠.
不陈述保留后的值有多大.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWayAsk where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just; nothing)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; lev; dnLc; add-cp; plus-weak)
open import OCF.Lean.YiLamFold using (Kfk; nrmk; nrmk-lgl)
open import OCF.Lean.YiZipWay using (Way′; keep′; fold′)
open import OCF.Lean.YiCtxAnn using (noM; noP; Pv; pL; pB; pM; cmpe₀)
open import OCF.Lean.YiProdArith using (plusA-cp; KfkA-cp; fgC)
open import OCF.Lean.YiProdFold using (Ψᵖ; Φ; sub₂; T⁺ʷᵖ)
open import OCF.Lean.YiProdTest using (walk; pathN; unws)
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiUniNegCmp using (cp-trans)
open import OCF.Lean.YiWayOne using (V2; Sp; p₀; S₀; x₀; VT; XT; Tt′; μT; πT; gK′; πc; Fo; gk₁ᵖ; dᵖ; up≼; NEK)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)
```

## 1 坐标经第一位置在结点链第 1 点之下

```agda
Bi : R
Bi = Ψᵖ zero V2 Sp (cmpe₀ p₀) G.top noM noP

ξaᵖ : R
ξaᵖ = plus zero G.top (G.suc Bi)

c-gᵖ : Cp zero (G.suc Bi) (gk₁ᵖ G.top)
c-gᵖ = inj₂ (0 , inj₂ (0 , inj₂ (1 , inj₂ (0 , inj₂ (0 , inj₂ (0 , inj₁ refl))))))

c-dᵖ : Cp zero ξaᵖ (dᵖ 1)
c-dᵖ = add-cp zero G.lc dnLc G.top c-gᵖ

dchainᵖ : ∀ m → Cp zero (dᵖ 1) (dᵖ (suc m))
dchainᵖ zero = inj₁ refl
dchainᵖ (suc m) = cp-trans (dchainᵖ m) (plus-weak zero (dᵖ (suc m)) (gk₁ᵖ (dᵖ (suc m))))

up-gK : ∀ {ξ ξ′} → Cp zero ξ ξ′ → NA.read (Fo ξ) ≼ NA.read (Fo ξ′)
up-gK {ξ} {ξ′} c = up≼ x₀ (fgC Sp S₀ _ _ _ (plusA-cp noM noP (Kfk zero Tt′ ξ′) _ _ (NEK ξ′) (KfkA-cp zero μT πT c)))

askedᵖ : NA.read (Fo ξaᵖ) ≼ NA.read T⁺ʷᵖ
askedᵖ = ≼-trans (up-gK c-dᵖ) (≼l 1 (≼l 1 (≼-refl _)))

asked-stepᵖ : ∀ m → NA.read (Fo ξaᵖ) ≼ NA.read (Fo (dᵖ (suc m)))
asked-stepᵖ m = up-gK (cp-trans c-dᵖ (dchainᵖ m))
```

## 2 那个结点, 它的链的第一步

```agda
a₀ : R
a₀ = plus zero G.top Bi

gKcᵖ : ℕ → Raw (tw 2)
gKcᵖ n = plus (tw 2) G.top (acc (λ _ z → plus (tw 2) z (Tt′ ξaᵖ)) (Kfk zero Tt′ a₀) n)

gK-formᵖ : gK′ ξaᵖ ≡ G.lim gKcᵖ
gK-formᵖ = refl

rNᵖ : Pre (tw 2)
rNᵖ = nrmk zero ξaᵖ , nrmk-lgl zero ξaᵖ , inj₁ tt

LNᵖ : LF
LNᵖ = lev (tw 2) rNᵖ

gNᵖ : Raw LNᵖ → Raw (tw 2)
gNᵖ = Φ (tw 2) (unws (VT ξaᵖ)) (sub₂ (XT ξaᵖ))

bNᵖ : Raw LNᵖ → Raw (tw 2)
bNᵖ η = plus (tw 2) G.top (plus (tw 2) (Kfk zero Tt′ a₀) (gNᵖ η))

gKc-1ᵖ : gKcᵖ 1 ≡ G.lc rNᵖ bNᵖ
gKc-1ᵖ = refl

π₁ᵖ : Pv (G.lc rNᵖ bNᵖ)
π₁ᵖ = pL (pB πc ξaᵖ) 1

asked-nodeᵖ : NA.read (Ψᵖ zero V2 S₀ x₀ (G.lc rNᵖ bNᵖ) noM π₁ᵖ) ≼ NA.read T⁺ʷᵖ
asked-nodeᵖ = ≼-trans (≼l 1 (≼-refl _)) askedᵖ
```

链的第一步是内层折叠 `Ψᵖ LNᵖ V2 (SB (tw 2) rNᵖ) (cmpe₀ rNᵖ) (bNᵖ top) (pM π₁ᵖ top) (pB π₁ᵖ top)`; 沿 `pathN` 走到的结点及其标注:

```agda
sᵖ : Pre LNᵖ
sᵖ = 0 , 1 , 0 , 0 , 0 , inj₂ (inj₁ tt)

pNᵖ : Pre (tw 2)
pNᵖ = nrmk zero ξaᵖ , nrmk-lgl zero ξaᵖ , inj₂ sᵖ

markedᵖ : walk pathN (bNᵖ G.top) (pM π₁ᵖ G.top) ≡ just (pNᵖ , just refl)
markedᵖ = refl

IsK : ∀ {m j} → Way′ m j → Set
IsK (keep′ _ _) = ⊤
IsK fold′ = ⊥

keptᵖ : IsK (cmpe₀ rNᵖ pNᵖ (just refl))
keptᵖ = tt

lostᵖ : cmpe₀ rNᵖ pNᵖ nothing ≡ fold′
lostᵖ = refl
```
