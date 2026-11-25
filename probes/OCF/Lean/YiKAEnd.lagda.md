# 候选 A 的终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照, 严格高于 BTBO 的参照

> 验收文件 (读记号, 读回 `YiBRValue.readRW`), 树、折叠、合法性一行不改. 编译定理, 无前提: `tA≼EBOᴷ : (h : HC tA) → R2.Rt h ≼ readRW EBOᶜ`, 推论 `btbo≺EBOᴷ : L.suc D.BTBOᴵ ≼ readRW EBOᶜ` (`EBOᶜ` 是候选 A 的 `YiKVFold.EBOᶜ`).
> 做法: 第 2 支, `tw 2` 的第 0 行, `tw 1` 的第 1 行 (孩子 c₁), 落到不含 Ω 形状的层号 `zero ⊕ ↑ zero c₁` (`desc`); 那里的底在第 0 层的分量与第 1 支同值, 不低于 BTBO ([YiKABY](YiKABY.lagda.md)), 其余分量在标准底之上; 把底降成 "第 0 层取第 1 支, 其余取标准底" (`flK`), 再与 F2 逐构造子相关 (`AK`), 用 `YiEVReach.reach` 沿 c₁ 的形状走到层号 2.
> 不涉及上界; 不经候选 A 与主线之间的值关系.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKAEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiCertFold using (Base)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel hiding (RelE)
open import OCF.Lean.YiBROps hiding (emb-R; emb-mono-R)
open import OCF.Lean.YiBRFold using (W→L)
open import OCF.Lean.YiKARel
open import OCF.Lean.YiKATw1 using (h₁ᴷ; o₁)
open import OCF.Lean.YiKAMono using (flK; le⊴; geβ)
open import OCF.Lean.YiKABY using (τ₀; τ◃; τ₀-R; τ◃-R; BY; β₂Y; TY; TY≅; btbo-β₂Y)
open import OCF.Lean.YiVRRel using (Le; Ωt≼; NoΩ≤; NoΩ↑; refl₀)
open import OCF.Lean.YiVRFold using (_⊴_)
open import OCF.Lean.YiVRRead using (le→≼; ≼→le)
import OCF.Lean.YiLSTw1 as T1
open import OCF.Lean.YiLSFold using (OKB)
open import OCF.Lean.YiLSRead using (read; _⊢_⊴_; ⊴r; ⊴◃)
open import OCF.Lean.YiEVReach using (_⇐_; ⇐r; ⇐l; Hi; reach)
open import OCF.Lean.YiMEAnchor using (two)
open import OCF.Lean.YiEVEnd using (btbo≼row₂)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA; btbo≺A)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanTree using (hc-tower)
open import OCF.Lean.YiBRValue using (readRW; rel≅)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-trans; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
```

## 下降: 第 2 支, `tw 2` 的第 0 行, `tw 1` 的第 1 行

```agda
plusR : (a b : Tr zero) → readRW b ≼ readRW (a + b)
plusR a zero          = z≼
plusR a (suc b)       = s≼s (plusR a b)
plusR a (lim f r)     = l≼ (λ n → ≼l n (plusR a (f n)))
plusR a (Ω () g)
plusR a (up x () y e)

cumF : ℕ → Tr Λ
cumF = cum (λ n → proj₁ (upz {s = sL} {h = tw} n (Ωt (tw n))))

EB : ℕ → Tr⁺ zero
EB n = ψ Λ Ok-Λ (λ j _ → Ωt j) zero (z≤ Λ) (Ωt zero) (cumF n)

dB2 : Base (tw 2)
dB2 i u = ψ Λ Ok-Λ (λ j _ → Ωt j) i (inc 2 u) (Ωt i) (cumF 1)

Br0 : Base (tw 1)
Br0 i u = dB2 i (inc zero u)

G₁ : Tr zero → Tr⁺ zero
G₁ z = ψ (tw 1) o₁ Br0 zero (z≤ (tw 1)) (EB 1) (proj₁ (upz {s = sΩ zero} {h = h₁ᴷ} z (Ωt (h₁ᴷ z))))

c₁ : Tr zero
c₁ = proj₁ (ψ (tw 1) o₁ Br0 zero (ink self) (Br0 zero (ink self)) (proj₁ (upz {s = sΩ zero} {h = h₁ᴷ} zero (Ωt (h₁ᴷ zero)))))

B₁ : Base (h₁ᴷ c₁)
B₁ i u = Br0 i (inc c₁ u)

GE : Tr⁺ zero
GE = ψ (h₁ᴷ c₁) (proj₂ o₁ c₁) B₁ zero (z≤ (h₁ᴷ c₁)) (EB 1) (proj₁ (Ωt (h₁ᴷ c₁)))

desc : readRW (proj₁ GE) ≼ readRW EBOᶜ
desc = ≼l 2 (≼l 0 (≼l 1 (plusR (proj₁ (G₁ zero)) (proj₁ (G₁ c₁)))))
```

## 底降成标准底, 第 0 层取第 1 支

```agda
EB1≡ : EB 1 ≡ β₂Y
EB1≡ = refl

pickK : (i : L) → Tr⁺ i
pickK zero     = β₂Y
pickK (nd s h) = Ωt (nd s h)

B̃ : Base (h₁ᴷ c₁)
B̃ i u = pickK i

hB : B̃ ⊴ B₁
hB zero     w pr = ≼→le _ _ (≅→≼ (L.≅-sym (TY≅ c₁ w)))
hB (nd s h) w pr =
  le⊴ (le⊴ (Ωt≼ (nd s h) (NoΩ≤ w (NoΩ↑ c₁))) (geβ (tw 1) o₁ (λ i′ u′ → Ωt i′) (nd s h) (inc c₁ w) (Ωt (nd s h)) (up zero zero (suc zero) ◃s)))
      (geβ (tw 1) o₁ BY (nd s h) (inc c₁ w) (BY (nd s h) (inc c₁ w)) (proj₁ (Ωt (tw 1))))

lowered : readRW (proj₁ (ψ (h₁ᴷ c₁) (proj₂ o₁ c₁) B̃ zero (z≤ (h₁ᴷ c₁)) β₂Y (proj₁ (Ωt (h₁ᴷ c₁))))) ≼ readRW (proj₁ GE)
lowered = le→≼ (flK (h₁ᴷ c₁) (NoΩ↑ c₁) (proj₂ o₁ c₁) B̃ B₁ hB zero (z≤ (h₁ᴷ c₁)) β₂Y β₂Y (refl₀ (proj₁ β₂Y))
                    (Ωt≼ (h₁ᴷ c₁) (NoΩ↑ c₁)))
```

## F2 一侧的底与关系

```agda
pickF : (j′ : F.L) → F.Tr j′
pickF F.zero = τ₀ (proj₁ β₂Y)
pickF j′     = F.Ωt j′

pickFn : (j′ : F.L) → F._⊢_◃_ j′ F.zero (pickF j′)
pickFn F.zero     = τ◃ (proj₂ β₂Y)
pickFn (F.suc a)  = F.Ωt-nz (F.suc a)
pickFn (F.lim g)  = F.Ωt-nz (F.lim g)
pickFn (F.Ωₗ k h) = F.Ωt-nz (F.Ωₗ k h)

ℓ′ : F.L
ℓ′ = T1.h₁ (τ₀ c₁)

B̃′ : F.Base ℓ′
B̃′ = F.base (τ₀ (proj₁ β₂Y)) (τ◃ (proj₂ β₂Y)) (λ j′ _ → pickF j′) (λ j′ _ → pickFn j′)

reK : RelEK (h₁ᴷ c₁) ℓ′ (proj₂ o₁ c₁) (T1.εh (τ₀ c₁)) (T1.ρh (τ₀ c₁))
reK = h₁-EK (τ₀-R c₁)

rB̃ : RelBase (h₁ᴷ c₁) ℓ′ B̃ B̃′
rB̃ j j′ w w′ rw = pk (W→L (E→LK reK) rw)
  where
  pk : {j : L} {j′ : F.L} → RelL j j′ → RelT j j′ (proj₁ (pickK j)) (pickF j′) × RelD j j′ (proj₂ (pickK j)) (pickFn j′)
  pk lz           = τ₀-R (proj₁ β₂Y) , τ◃-R (proj₂ β₂Y)
  pk r@(lS _)     = Ωt-R r , Ωn-R r
  pk r@(lL _)     = Ωt-R r , Ωn-R r
  pk r@(lΩ _ _)   = Ωt-R r , Ωn-R r

rAK : RelT zero F.zero (proj₁ (ψ (h₁ᴷ c₁) (proj₂ o₁ c₁) B̃ zero (z≤ (h₁ᴷ c₁)) β₂Y (proj₁ (Ωt (h₁ᴷ c₁)))))
                       (F.ψ⊥ ℓ′ (T1.εh (τ₀ c₁)) (T1.ρh (τ₀ c₁)) B̃′ (F.Ωt ℓ′))
rAK = proj₁ (AK reK B̃ B̃′ rB̃ β₂Y (τ₀-R (proj₁ β₂Y)) (τ◃-R (proj₂ β₂Y)) (Ωt-R (E→LK reK)))
```

## F2 上沿 c₁ 的形状走到层号 2

c₁ 是 `next` 的链; 依次取极限的第 0, 0, 0, 1 项, 末项是 `suc (suc zero)` (由类型检查确认).

```agda
path₂ᴷ : two ⇐ ℓ′
path₂ᴷ = ⇐l 0 (⇐l 0 (⇐l 0 (⇐l 1 ⇐r)))

suc◃β₂ : zero ⊢ suc zero ◃ proj₁ β₂Y
suc◃β₂ with geβ (tw 1) o₁ BY zero (z≤ (tw 1)) (next⁺ (Ωt zero)) (proj₁ (Ωt (tw 1)))
... | inj₁ e = subst (λ t → zero ⊢ suc zero ◃ t) e (◃l 0)
... | inj₂ d = ◃t (◃l 0) d

okP : (j′ : F.L) → j′ ⊢ F.Ωt j′ ⊴ pickF j′
okP F.zero     = ⊴◃ (τ◃ suc◃β₂)
okP (F.suc a)  = ⊴r
okP (F.lim g)  = ⊴r
okP (F.Ωₗ k h) = ⊴r

ok̃ : OKB ℓ′ B̃′
ok̃ = ⊴◃ (τ◃ suc◃β₂) , λ j′ w′ → okP j′

btbo-τ : D.BTBOᴵ ≼ read (τ₀ (proj₁ β₂Y))
btbo-τ = ≼-trans btbo-β₂Y (≅→≼ (rel≅ (τ₀-R (proj₁ β₂Y))))

hĩ : Hi ℓ′ B̃′
hĩ = btbo-τ , λ w′ → btbo-τ
```

## 终点

```agda
tA≼EBOᴷ : (h : HC tA) → R2.Rt h ≼ readRW EBOᶜ
tA≼EBOᴷ h =
  ≼-trans (reach path₂ᴷ (T1.εh (τ₀ c₁)) (T1.ρh (τ₀ c₁)) B̃′ ok̃ hĩ h)
    (≼-trans (≅→≼ (L.≅-sym (rel≅ rAK))) (≼-trans lowered desc))

btbo≺EBOᴷ : L.suc D.BTBOᴵ ≼ readRW EBOᶜ
btbo≺EBOᴷ = ≼-trans (s≼s btbo≼row₂) (≼-trans (btbo≺A (hc-tower 2) hA) (tA≼EBOᴷ hA))
```
