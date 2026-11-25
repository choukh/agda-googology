# 同步对象孩子 2 上的 TightStep: 只能空真
验收文件 (读记号); 编译定理: `no-tight′ : (t : E.T) → PrefixU (D.dn Bᴱ (suc (suc zero))) t → TightStep (suc zero) → ⊥` (`TightStep` 的 `OK` 前提已实填, `okᴱ`). 即 `TightStep 1` 成立当且仅当它自己的前缀前提对一切 t 都不可满足 (另一方向 `vacuous`).
机制同 `YiTFTw1`: 分支函数 `gT` 把同一棵孩子 2 的直接嵌入沿第一孩子放进 `hh 1 z` 的 tw 1 叶子; 折叠对一切证据与路径都给出 "第 1 层继承底加可数尾巴" (`LA`–`LD`), 继承底是 Ω₁ 树加两段可数, 第二段是 `twᶻ 1` (`β-form`, `Y₂-tw`, `sβ`), 读法低于 Ω₁+Ω₁; 记号要 ψ₁((t ++ Ω₂)[Ω₁]).
不否定 `KeepOut`, `KeepFeed`, `FirstMissing` 或任何值; `PrefixU (D.dn Bᴱ 2) t` 可满足与否未判定. 否定的是 GR.R 量化分支的陈述.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTFTight where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ₀ʳ)
import OCF.Lean.YiTBRow as TB
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiLKIface using (OK) renaming (feed to feedᴸ)
open import OCF.Lean.YiKVRel using (one)
open import OCF.Lean.YiSYReduce using (a₁; h₁; oᴱ; Bᴱ)
open import OCF.Lean.YiTLReduce using (TightStep; hh)
import OCF.Lean.YiSYDesc as D
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (<ᵀ-irrefl; <ᵀ-trans)
open import OCF.Lean.YiTFBound
open import OCF.Lean.YiTFTw1 using (c₂; g₁; cΩ₁; low0; rg; rd1; a₂)
open import OCF.Lean.YiSYReduce using (c₁; p*)
open import OCF.Lean.YiKSDesc using (_⊑¹_; r¹; n¹)
open import OCF.Lean.YiGIInst using (pre)
open import OCF.Lean.YiTBFam using (ψ-⊵)
```

## 路径一般的折叠: 叶子, 后继形状, 下标第 0 层的 Ω 形状

叶子上目标第 1 层的路径只能经指定孩子 (`inu`, `ink` 都要第 1 层 ≤ 第 0 层); 孩子 2 对孩子 2 在最小表里缺项. Ω 形状层号经孩子 0 以外的指定孩子时也走退路, 同样是加可数尾巴.

```agda
one≰zero : one ≤ zero → ⊥
one≰zero ()

x′ : Tr (tw 1)
x′ = g₁ cΩ₁

LA : ∀ (o : Ok (tw 1)) (B : Base (tw 1)) (v : one ≤ tw 1) (β : Tr⁺ one) → S (proj₁ β)
  → S (proj₁ (TB.ψ (tw 1) o (rbᶻ (tw 1)) B one v β x′))
LA o B (inu vs) β s = ⊥-elim (one≰zero (vs zero))
LA o B (ink v) β s = ⊥-elim (one≰zero v)
LA o B (inc zero v) β s = ⊥-elim (one≰zero v)
LA o B (inc (suc c′) v) β s =
  S-⊞⁺ β (ψ₀ʳ (zero ⊕ ↑ zero c₂) (proj₂ o c₂) (rbᶻ (zero ⊕ ↑ zero c₂)) (up zero tt (suc cΩ₁) (z◃ cΩ₁ ◃s))) s
LA o B (inc (lim f a) v) β s =
  S-⊞⁺ β (ψ₀ʳ (zero ⊕ ↑ zero c₂) (proj₂ o c₂) (rbᶻ (zero ⊕ ↑ zero c₂)) (up zero tt (suc cΩ₁) (z◃ cΩ₁ ◃s))) s

LB : (h : ⊤ → L) → (h tt ≡ zero → ⊥) → (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y)
  → (∀ (o : Ok (h tt)) (B : Base (h tt)) (v : one ≤ h tt) (β : Tr⁺ one) → S (proj₁ β)
      → S (proj₁ (TB.ψ (h tt) o (rbᶻ (h tt)) B one v β y)))
  → ∀ (o : Ok (nd sS h)) (B : Base (nd sS h)) (v : one ≤ nd sS h) (β : Tr⁺ one) → S (proj₁ β)
  → S (proj₁ (TB.ψ (nd sS h) o (rbᶻ (nd sS h)) B one v β (up zero tt y e)))
LB h hne y e P o B self β s = ⊥-elim (hne refl)
LB h hne y e P o B (inu vs) β s = P (proj₂ o tt) _ (vs tt) β s
LB h hne y e P o B (inc tt v) β s = P (proj₂ o tt) _ v β s

ex′ : tw 1 ⊢ zero ◃ x′
ex′ = ◃u zero c₂ (up zero tt (suc cΩ₁) (z◃ cΩ₁ ◃s)) (◃u zero tt (suc cΩ₁) (z◃ cΩ₁ ◃s))

Yz : L
Yz = tw 1 ⊕ (zero ⊕ (zero ⊕ ↑ one cΩ₁))

y₀ : Tr (tw 1 ⊕ one)
y₀ = up zero tt x′ ex′

e₀ : tw 1 ⊕ one ⊢ zero ◃ y₀
e₀ = ◃u zero tt x′ ex′

LB1 : ∀ (o : Ok (tw 1 ⊕ one)) (B : Base (tw 1 ⊕ one)) (v : one ≤ tw 1 ⊕ one) (β : Tr⁺ one) → S (proj₁ β)
  → S (proj₁ (TB.ψ (tw 1 ⊕ one) o (rbᶻ (tw 1 ⊕ one)) B one v β y₀))
LB1 = LB (λ _ → tw 1) (λ ()) x′ ex′ LA

LC : ∀ (o : Ok Yz) (B : Base Yz) (v : one ≤ Yz) (β : Tr⁺ one) → S (proj₁ β)
  → S (proj₁ (TB.ψ Yz o (rbᶻ Yz) B one v β (up zero zero y₀ e₀)))
LC o B (inu vs) β s = LB1 (proj₂ o zero) _ (vs zero) β s
LC o B (ink v) β s = ⊥-elim (one≰zero v)
LC o B (inc zero v) β s = LB1 (proj₂ o zero) _ v β s
LC o B (inc (suc c′) v) β s = S-⊞⁺ β (ψ₀ʳ (tw 1 ⊕ one) (proj₂ o zero) (rbᶻ (tw 1 ⊕ one)) y₀) s
LC o B (inc (lim f a) v) β s = S-⊞⁺ β (ψ₀ʳ (tw 1 ⊕ one) (proj₂ o zero) (rbᶻ (tw 1 ⊕ one)) y₀) s

W₁ : Tr (hh (suc zero) cΩ₁)
W₁ = up zero tt (up zero zero y₀ e₀) (◃u zero zero y₀ e₀)

LD : ∀ (o : Ok (hh (suc zero) cΩ₁)) (B : Base (hh (suc zero) cΩ₁)) (v : one ≤ hh (suc zero) cΩ₁) (β : Tr⁺ one) → S (proj₁ β)
  → S (proj₁ (TB.ψ (hh (suc zero) cΩ₁) o (rbᶻ (hh (suc zero) cΩ₁)) B one v β W₁))
LD = LB (λ _ → Yz) (λ ()) (up zero zero y₀ e₀) (◃u zero zero y₀ e₀) LC
```

## 分支函数与继承底

```agda
emb₁ : ∀ X → Tr⁺ (tw 1) → Tr⁺ (tw 1 ⊕ X)
emb₁ zero y = y
emb₁ (nd s h) y = upz (c₀ s) (emb₁ (h (c₀ s)) y)

Xz : Tr one → L
Xz z = zero ⊕ nd sS (λ _ → zero ⊕ ↑ (h₁ (suc zero)) z)

gT : Tr one → Tr (a₁ (suc (suc zero)))
gT z = proj₁ (upz {s = sΩ one} {h = hh (suc zero)} z (emb₁ (Xz z) (x′ , ex′)))

gT-form : gT cΩ₁ ≡ up zero cΩ₁ W₁ (◃u zero tt (up zero zero y₀ e₀) (◃u zero zero y₀ e₀))
gT-form = refl

Y₁ Y₂ : Tr⁺ zero
Y₁ = ψ₀ʳ (tw 1 ⊕ ↑ (tw 1) zero) (proj₂ (Ok-tw 2) zero) (proj₂ (rbᶻ (tw 2)) zero) (up zero zero (suc zero) ◃s)
Y₂ = ψ₀ʳ (tw 1 ⊕ ↑ (tw 1) zero) (proj₂ (Ok-tw 2) zero) (proj₂ (rbᶻ (tw 2)) zero) (proj₁ (Ωt (tw 1)))

sβ : S (proj₁ (D.dn Bᴱ (suc (suc zero)) one (ink self)))
sβ = S-⊞⁺ (Ωt one ⊞ Y₁) Y₂ (S-⊞⁺ (Ωt one) Y₁ sb)

-- 继承底在第 1 层是两次退路的结果, 第二段就是塔第 1 项的闭项.
β-form : proj₁ (D.dn Bᴱ (suc (suc zero)) one (ink self)) ≡ proj₁ ((Ωt one ⊞ Y₁) ⊞ Y₂)
β-form = refl

Y₂-tw : proj₁ Y₂ ≡ twᶻ 1
Y₂-tw = refl
```

## 否定

```agda
rprem : GR.R (a₁ (suc (suc zero))) (E.Ωt (E.natT 1)) (gT cΩ₁)
rprem = H.mU H.mz (H.mU H.mz (H.mU H.mz (H.mU H.mz (rg low0))))

feedT : Tr one
feedT = feedᴸ (a₁ (suc (suc zero))) (proj₂ oᴱ (suc (suc zero))) (rbᶻ (a₁ (suc (suc zero))))
  (D.dn Bᴱ (suc (suc zero))) (inj₁ (inj₁ tt)) gT cΩ₁

sfeed : S feedT
sfeed = LD (proj₂ (proj₂ oᴱ (suc (suc zero))) cΩ₁) _
  (self ∙ proj₂ (proj₁ (proj₂ oᴱ (suc (suc zero)))) cΩ₁) (D.dn Bᴱ (suc (suc zero)) one (ink self)) sβ

fsT-ne : ∀ t → [] <ᵀ E.fsT (t ++ a₂) (E.Ωt (E.natT 1))
fsT-ne [] = []<
fsT-ne (x ∷ []) = []<
fsT-ne (x ∷ y ∷ ys) = []<

no-tight : OK (D.dn Bᴱ (suc (suc zero))) → (t : E.T) → PrefixU (D.dn Bᴱ (suc (suc zero))) t
  → TightStep (suc zero) → ⊥
no-tight ok t pf ts = <ᵀ-irrefl (<ᵀ-trans
  (bS (ts ok t pf a₂ (E.natT 1) rd1 refl gT 0 cΩ₁ low0 rprem) sfeed) (hd< (ar< (fsT-ne t))))

P¹ : ∀ {j ℓ} → j ⊑¹ ℓ → ∀ {i} → i ≤ j → i ≤ ℓ
P¹ r¹ u = u
P¹ (n¹ {s} p) u = inc (c₀ s) (P¹ p u)

okᴱ : OK (D.dn Bᴱ (suc (suc zero)))
okᴱ i u = ψ-⊵ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) i (inc 2 (inc c₁ (P¹ p* (inc (suc (suc zero)) u)))) (Ωt i) (pre 2)

no-tight′ : (t : E.T) → PrefixU (D.dn Bᴱ (suc (suc zero))) t → TightStep (suc zero) → ⊥
no-tight′ = no-tight okᴱ

vacuous : ((t : E.T) → PrefixU (D.dn Bᴱ (suc (suc zero))) t → ⊥) → TightStep (suc zero)
vacuous np ok t pf = ⊥-elim (np t pf)
```
