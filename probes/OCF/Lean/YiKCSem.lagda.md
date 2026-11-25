# 候选 A: 判据归约到 A1 一条; 见证不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (验收)

> 验收文件 (读记号), 树、折叠、合法性一行不改. 编译定理: `critA1 : A1 → (h : HC tB) → Rt h ≼ readRW W` (条件, 前提只剩 A1; `YiKVValue.crit` 的前提 A0 换成 BTBO 的值下界); 无前提: `tA≼W` (最小见证 W 不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照), `B0≼W` (tB 的第 0 行).
> 做法: 第 0 层的关系由值序给出 (`sem→M⁰`, 照 `YiMWPre`), 起点与第 0 层底不低于 BTBO 的参照 (`btbo-tw1ᴷ` 与路径变体 `btbo-b′`); tA 一行用空前缀的 `PF` 与前缀 Ω_Ω 的 `QH`.
> 不给出 tB 的第 1 行及以上; 不涉及上界. A1 的归纳在 [YiKCStep](YiKCStep.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKCSem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel
open import OCF.Lean.YiKVCheck using (o¹; h₁; c2; βΩ; Wt; BW; A0f; cc)
open import OCF.Lean.YiKVValue using (Pre; Ω₂ᵗ; module At; A1; hβ₁; hΩ)
open import OCF.Lean.YiCertFold using (Base)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel hiding (RelE)
open import OCF.Lean.YiBRLem hiding (E→L; E-at; E-at⁼)
open import OCF.Lean.YiBROps hiding (emb-R; emb-mono-R)
open import OCF.Lean.YiBRTw using (↑-L)
open import OCF.Lean.YiKARel
open import OCF.Lean.YiKATw1 using (ab-W; ch; btbo-tw1ᴷ)
open import OCF.Lean.YiLSTw1 using (G; G-nz; K; pt; KG)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiDropRow using (limc≼cum)
import OCF.Lean.YiBRValue as BR
open import OCF.Lean.YiEXRow using (row₂-btbo)
import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; γT; natT)
open import OCF.Align.EboLeanTree using (hc-tower)
open import OCF.Align.Correspond using (cof-ne)
open import OCF.Lean.YiNFOCase using (tA; tB; hA; hB)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv)
import OCF.Align.Level as O
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼)
```

## 第 0 层: 值序给出关系

两个读回逐点同形. `sem→M⁰` 照 `YiMWPre.sem→M⁰`, 签名换成精简块的.

```agda
rr≼ : (x : Tr zero) → BR.readRW x ≼ readRW x
rr≼ zero      = z≼
rr≼ (suc x)   = s≼s (rr≼ x)
rr≼ (lim f _) = l≼ (λ n → ≼l n (rr≼ (f n)))

inv-suc : (x : Tr zero) {a : O.Ordᶜ O.zero} → O.suc a ≼ readRW x → Σ (Tr zero) λ x′ → (suc x′ ⊴ x) × (a ≼ readRW x′)
inv-suc zero      ()
inv-suc (suc x)   (s≼s p) = x , ⊴r , p
inv-suc (lim f a) (≼l n p) with inv-suc (f n) p
... | x′ , le , q = x′ , ⊴◃ (⊴-◃ le (◃l n)) , q

sem→M⁰ : ∀ {t} (h : HC t) (x : Tr zero) → Rt h ≼ readRW x → M⁰ t x
sem→M⁰ {t = []}     (h0 e)    x q = mz
sem→M⁰ {t = y ∷ ys} (h0 e)    x q = ⊥-elim (cof-ne y ys e)
sem→M⁰              (h1 e hp) x q with inv-suc x q
... | x′ , le , q′ = G⁰.m⊴ (m1 e (sem→M⁰ hp x′ q′)) le
sem→M⁰              (hω e hs) x q = mL e (λ n → sem→M⁰ (hs n) x (≼-trans (≼l n (≼-refl (Rt (hs n)))) q))

semR : ∀ {t} (h : HC t) (x : Tr zero) {Y : O.Ordᶜ O.zero} → Rt h ≼ Y → Y ≼ BR.readRW x → M⁰ t x
semR h x p q = sem→M⁰ h x (≼-trans p (≼-trans q (rr≼ x)))

sem0 : (x : Tr zero) → D.BTBOᴵ ≼ BR.readRW x → M⁰ (ψ₀ᵗ Pre) x
sem0 x q = semR (hc-tower 2) x row₂-btbo q
```

## 起点与第 0 层底不低于 BTBO 的参照

起点是塔第 1 项 (`btbo-tw1ᴷ`). 第 0 层底是同一条链上沿证书路径的折叠的部分和; 逐项与 F2 的 `K (pt n)` 相关, 后者读回与 `G (pt n)` 同值 (`KG`).

```agda
W : Tr zero
W = proj₁ (ψ₀ (tw 1) o¹ Wt)

β₀ : Tr⁺ zero
β₀ = ψ₀ (tw 1) o¹ βΩ

h₀ᵁ : M⁰ (ψ₀ᵗ Pre) (proj₁ β₀)
h₀ᵁ = sem0 (proj₁ β₀) btbo-tw1ᴷ

sK′ : Tr zero → Tr⁺ zero
sK′ z = A0f z (self ∙ ab→≤ (crt o¹ z))

b′ : Tr⁺ zero
b′ = limc⁺ (λ n → sK′ (cc n))

_ : BW zero (inc tt (inc tt self)) ≡ b′
_ = refl

K-nz : (x : F.Tr F.zero) → F._⊢_◃_ F.zero F.zero (K x)
K-nz x = F.nzs _ _ _ (F.B₀ _) F.zero _ (F.suc F.zero) F.◃s (F.Ωt _)

rK′ : {z : Tr zero} {z′ : F.Tr F.zero} (r : RelT zero F.zero z z′)
    → RelT zero F.zero (proj₁ (sK′ z)) (K z′) × RelD zero F.zero (proj₂ (sK′ z)) (K-nz z′)
rK′ r = SK (h₁-EK r) (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK (h₁-EK r)))
  (∙-R wself (ab-W (↑-L lz r))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (E→LK (h₁-EK r)))

b′-R : RelT zero F.zero (proj₁ b′) (F.limc (λ n → K (pt n)) (λ n → K-nz (pt n)))
b′-R = limc-R (λ n → sK′ (cc n)) (λ n → proj₁ (rK′ (ch n))) (λ n → proj₂ (rK′ (ch n)))

btbo-b′ : D.BTBOᴵ ≼ BR.readRW (proj₁ b′)
btbo-b′ = BR.up≼ b′-R (≼-trans btbo-tw1
  (limc≼cum (λ n → G (pt n)) (λ n → K (pt n)) (λ n → G-nz (pt n)) (λ n → ≅→≼ (O.≅-sym (KG (pt n))))))

hb′ᵁ : M⁰ (ψ₀ᵗ Pre) (proj₁ (BW zero (inc tt (inc tt self))))
hb′ᵁ = sem0 (proj₁ b′) btbo-b′
```

## 判据归约到 A1

```agda
o2 : Ok two
o2 = proj₂ o¹ c2

critA1 : A1 → (h : HC tB) → Rt h ≼ readRW W
critA1 a1 h = lower⁰ (At.lowerM Pre o2 BW β₀ (hβ₁ a1) hΩ h₀ᵁ hb′ᵁ) h
```

## 无前提的两行

第 1 层的链 `z` 用空前缀的 `PF` (底只需在 Ω₁ 之上, `hΩ`), 对着 ψ₁(Ω₂) 的 γ-链; 折到第 0 层用前缀 Ω_Ω 的 `QH`.

```agda
o1 : Ok one
o1 = proj₂ o2 tt

B1 : Base one
B1 i u = ψ two o2 BW i (inc tt u) (BW i (inc tt u)) zero

module P0 = PFm [] o1 B1 (BW one (inc tt self)) hΩ
module Q  = QHm Pre o1 B1 hb′ᵁ

z : ℕ → Tr one
z = iter (λ c → proj₁ (next⁺ (P0.F⁺ c))) zero

W-form : W ≡ proj₁ (limc⁺ (λ k → next⁺ (Q.H⁺ (z≤ one) β₀ (z k))))
W-form = refl

sγ₀ : ∀ n → M¹ (γT Ω₂ᵗ u₁ n) (z (suc n))
sγ₀ zero    = mw hΩ (◃l zero)
sγ₀ (suc n) = mw (P0.PF (sγ₀ n)) (◃l zero)

rowA : ∀ n → M⁰ (ψ₀ᵗ (Pre ++ ψ₁ᵗ (γT Ω₂ᵗ u₁ n))) W
rowA n = G⁰.m-cum (λ k → next⁺ (Q.H⁺ (z≤ one) β₀ (z k))) (suc (suc n))
  (mw (Q.QH (z≤ one) β₀ h₀ᵁ (mw (P0.PF (sγ₀ n)) (◃l zero))) (◃l zero))

tA-M : M⁰ tA W
tA-M = mL refl rowA

tA≼W : (h : HC tA) → Rt h ≼ readRW W
tA≼W = lower⁰ tA-M

B0-M : M⁰ (E.fsn tB 0) W
B0-M = G⁰.m-cum (λ k → next⁺ (Q.H⁺ (z≤ one) β₀ (z k))) 1 (mw (Q.QH (z≤ one) β₀ h₀ᵁ (sγ₀ zero)) (◃l zero))

B0≼W : (h : HC (E.fsn tB 0)) → Rt h ≼ readRW W
B0≼W = lower⁰ B0-M
```

实例 (前提可满足): `YiNFOCase.hA`, `hB` 是 tA, tB 的推导.

```agda
inst-A : Rt hA ≼ readRW W
inst-A = tA≼W hA

inst-B0 : Rt (hω-inv hB refl 0) ≼ readRW W
inst-B0 = B0≼W (hω-inv hB refl 0)
```
