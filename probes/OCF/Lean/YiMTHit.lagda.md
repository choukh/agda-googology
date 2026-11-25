# 最小比较表: 那一行在闭项里走哪条分支

> 验收文件 (不读记号), 不进成品; 树、折叠、表一行不改. `Hit` 照 `YiNRHit.Hit` 写在 `YiTBRow` 的折叠上, 到那一行处把表的条目也交给谓词; 见证路径与 `YiNRTw2.hit-tw2`, `YiNREbo.hit-Λ2`, `hit-Λ1` 逐字相同.
> 编译定理, 无前提: 塔第 2 项那一处 (`hit-tw2ᶻ`) 与终点 tw 2 那一处 (`hit-Λ2ᶻ`) 的条目是 `just (inj₁ _)`, 在嵌入所在孩子的层上折 (两处 c′ = c = 0, 两条分支同层); 终点 tw 1 那一处 (`hit-Λ1ᶻ`) 的条目是 `just (inj₂ _)`, 把孩子树嵌进指定孩子 c′ 的层再折.
> 不否定什么; 只跟踪 `ψ` 自身的递归, 到那一行为止, 条目之后的折叠不再跟踪. 见证沿旧路径成立, 不说明它是新折叠里最先到的一处.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMTHit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiNRHit using (cW₁; HN)
```

## 谓词

```agda
Ent : (k : L) (h : Tr k → L) (c′ c : Tr k) → Set
Ent k h c′ c = Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))

Site : Set₁
Site = (k : L) (h : Tr k → L) (j : L) (c′ c : Tr k) → Ent k h c′ c → Set

Hit : Site → (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → ((i : L) → i ≤ ℓ → Set) → (j : L) → j ≤ ℓ → Tr⁺ j → Set → Tr ℓ → Set
Hit P ℓ o r B HB j w β Hβ zero      = Hβ
Hit P ℓ o r B HB j w β Hβ (suc x)   = Hit P ℓ o r B HB j w β Hβ x
Hit P ℓ o r B HB j w β Hβ (lim f a) = Σ ℕ λ n → Hit P ℓ o r B HB j w β Hβ (f n)
Hit P ℓ o r B HB j w β Hβ (Ω p g)   = HN (kp ℓ o p w) (λ z → Hit P ℓ o r B HB j w β Hβ (g z))
  (λ z → fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  (λ z → Hit P ℓ o r B HB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (HB (at ℓ p) (posW ℓ p)) (g z))
Hit P (nd s h) o r B HB _ self β Hβ (up x c y e) = Hit P (nd s h) o r B HB _ self β Hβ x
Hit P (nd s h) o r B HB j (inu ws) β Hβ (up x c y e) =
  Hit P (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd s h) o r B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j (ws c) (ψ (nd s h) o r B j (inu ws) β x) (Hit P (nd s h) o r B HB j (inu ws) β Hβ x) y
Hit P (nd (sΩ k) h) o r B HB j (ink v) β Hβ (up x c y e) =
  Hit P (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd (sΩ k) h) o r B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o r B j (ink v) β x) (Hit P (nd (sΩ k) h) o r B HB j (ink v) β Hβ x) y
Hit P (nd sS h) o r B HB j (inc c′ v) β Hβ (up x c y e) =
  Hit P (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ (nd sS h) o r B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd sS h) o r B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j v (ψ (nd sS h) o r B j (inc c′ v) β x) (Hit P (nd sS h) o r B HB j (inc c′ v) β Hβ x) y
Hit P (nd sL g) o r B HB j (inc n v) β Hβ (up x m y e) = cW₁ (way g (proj₁ o) m n)
  (λ u → Hit P (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x)
           (λ i u′ → Hit P (nd sL g) o r B HB i (inc n u′) (B i (inc n u′)) (HB i (inc n u′)) x) j v
           (ψ (nd sL g) o r B j (inc n v) β x) (Hit P (nd sL g) o r B HB j (inc n v) β Hβ x)
           (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
  (λ u → Hit P (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x)
           (λ i u′ → Hit P (nd sL g) o r B HB i (inc m u′) (B i (inc m u′)) (HB i (inc m u′)) x) j (v ∙ u)
           (ψ (nd sL g) o r B j (inc n v) β x) (Hit P (nd sL g) o r B HB j (inc n v) β Hβ x) y)
Hit P (nd (sΩ k) h) o r B HB j (inc c′ v) β Hβ (up x c y e) = P k h j c′ c (proj₁ r c c′)

HitTw : Site → ℕ → Set
HitTw P n = Hit P (tw n) (Ok-tw n) (rbᶻ (tw n)) (B₀ (tw n)) (λ _ _ → ⊥) zero (z≤ (tw n)) (Ωt zero) ⊥ (proj₁ (Ωt (tw n)))

HitΛ : Site → Set
HitΛ P = Hit P Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) (λ _ _ → ⊥) zero (z≤ Λ) (Ωt zero) ⊥ (proj₁ (Ωt Λ))

step : (P : Site) (n : ℕ) → HitTw P n → HitTw P (suc n)
step P n h = 0 , inj₁ h
```

## 三处的条目

`Is₁`: 条目在, 取第一支 (在孩子 c 的层上沿 `v ∙ u` 折). `Is₂`: 条目在, 取第二支 (嵌进孩子 c′ 的层再折). 参数谓词是 `YiNRTw2.P₂`, `YiNREbo.PΛ2`, `PΛ1` 各加一条.

```agda
data Is₁ {A B : Set} : Maybe (A ⊎ B) → Set where
  is₁ : (a : A) → Is₁ (just (inj₁ a))
data Is₂ {A B : Set} : Maybe (A ⊎ B) → Set where
  is₂ : (b : B) → Is₂ (just (inj₂ b))

b₁ : Tr (tw 1)
b₁ = proj₁ (Ωt (tw 1))

P₂ᶻ : Site
P₂ᶻ k h j c′ c m = (nd (sΩ k) h ≡ tw 1 ⊕ ↑ (tw 1) (b₁ + b₁)) × (j ≡ tw 1 ⊕ ↑ (tw 1) b₁)
              × (_≡_ {A = Σ L Tr} (k , c′) (zero , zero)) × (_≡_ {A = Σ L Tr} (k , c) (zero , zero)) × Is₁ m

hit-tw2ᶻ : HitTw P₂ᶻ 2
hit-tw2ᶻ = 1 , inj₂ (zero , (1 , (zero , (0 , inj₂ (refl , refl , refl , refl , is₁ self)))))

PΛ2ᶻ : Site
PΛ2ᶻ k h j c′ c m = (nd (sΩ k) h ≡ tw 2) × (j ≡ zero)
               × (_≡_ {A = Σ L Tr} (k , c′) (tw 1 , zero)) × (_≡_ {A = Σ L Tr} (k , c) (tw 1 , zero)) × Is₁ m

hit-Λ2ᶻ : HitΛ PΛ2ᶻ
hit-Λ2ᶻ = 2 , (0 , inj₁ (0 , inj₂ (refl , refl , refl , refl , is₁ self)))

PΛ1ᶻ : Site
PΛ1ᶻ k h j c′ c m = (nd (sΩ k) h ≡ tw 1) × (j ≡ zero)
               × (_≡_ {A = Σ L Tr} (k , c′) (zero , proj₁ (next⁺ (next⁺ (Ωt zero)))))
               × (_≡_ {A = Σ L Tr} (k , c) (zero , zero)) × Is₂ m

hit-Λ1ᶻ : HitΛ PΛ1ᶻ
hit-Λ1ᶻ = 1 , (1 , inj₁ (0 , (0 , (0 , inj₂ (refl , refl , refl , refl , is₂ _)))))

hit-tw≥2ᶻ : (n : ℕ) → HitTw P₂ᶻ (suc (suc n))
hit-tw≥2ᶻ zero    = hit-tw2ᶻ
hit-tw≥2ᶻ (suc n) = step P₂ᶻ (suc (suc n)) (hit-tw≥2ᶻ n)
```
