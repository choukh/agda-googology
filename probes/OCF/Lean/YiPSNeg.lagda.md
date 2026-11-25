# 转移引理 "现折叠不高于 ψ★" 对一切合法输入不成立

> 验收文件. 编译定理, 对一切排中律 `lem` (条件（排中律）): 主线 (`YiTBRow.ψ` 配 `rbᶻ`) 与 `Ideal lem` 之间的转移 "val 现 ≼ val ψ★" 在第 1 层 (`no-transferⱼ`) 与第 0 层的读回 (`no-transfer₀`) 都有反例, 换基候选同样 (`k6-lowerᴮ`); 反例用 K6 格上分支取常值的退化结点与按构造子取值的分支, 不在读回域内, 读作 "谓词太宽".
> 两行各要一条引理: K6 那一行要 "部分和被保留分支吸收" (条件引理 `chain≼keep`, 前提有实例), 退化结点上不成立 (`k6-lower`); 链那一行两边的链点不同 (`chains-split`), 要 "ψ★ 对分支参数按值单调", 对一般合法树不成立 (`no-mon`).
> 不否定读回域上的转移引理, 不否定 ψ★ 的值; 单结点的正面实例在 [YiPSCell](YiPSCell.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPSNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; node⁺)
import OCF.Lean.YiTBRow as T
open import OCF.Lean.YiMTTab using (rbᶻ; ψ₀ᶻ)
open import OCF.Lean.YiPSStar
import OCF.Lean.YiVWVal as W
open import OCF.Lean.YiBRValue using (readRW)
import OCF.Align.Level as Lv
import OCF.Align.Value as A
import OCF.Lean.YiBSFold as BS
import OCF.Lean.YiBSBase as BB
import OCF.Lean.YiPSStarB as SB
```

## 两种值序上的 "后继不低于自身"

```agda
irrV : ∀ {ℓ} (a : W.V ℓ) → ¬ (W.suc a W.≼ a)
irrV W.zero    ()
irrV (W.suc a) (W.s≼s d)  = irrV a d
irrV (W.lim f) (W.≼l n d) = irrV (f n) (W.≼-trans (W.s≼s (W.≼l n (W.≼-refl (f n)))) d)
irrV (W.Ω p g) (W.≼Ω z d) = irrV (g z) (W.≼-trans (W.s≼s (W.≼Ω z (W.≼-refl (g z)))) d)

irrRW : (x : Tr zero) → ¬ (Lv.suc (readRW x) A.≼ readRW x)
irrRW zero      d = A.s≼0 d
irrRW (suc x)   d = irrRW x (A.s≼s⁻ d)
irrRW (lim f a) d with A.≼lim⁻ d
... | n , d′ = irrRW (f n) (A.≼-trans (A.s≼s (A.≼l n (A.≼-refl (readRW (f n))))) d′)
irrRW (Ω () g)
irrRW (up x () y e)
```

## K6 格

层号 `ℓ₁` 的孩子都是第 1 层 `one`; 槽位 `p₁` 在孩子 0 的第 1 层里的第 0 层, 目标是孩子 0 的第 1 层 (路径 `w₁` 经指定孩子). 主线的表在两个孩子都是 `zero` 时给 `self`, 所以理想比较在这一格逐字给出保留.

```agda
one : L
one = nd sS (λ _ → zero)

ℓ₁ : L
ℓ₁ = nd (sΩ zero) (λ _ → one)

o₁ : Ok ℓ₁
o₁ = (tt , λ _ → z≤ one) , λ _ → tt , λ _ → tt

p₁ : Pos ℓ₁
p₁ = inj₂ (zero , inj₂ (inj₂ (tt , inj₁ tt)))

w₁ : one ≤ ℓ₁
w₁ = inc zero self

D₆ : Tr ℓ₁
D₆ = Ω p₁ (λ _ → zero)

V₁ : W.V one
V₁ = W.val one (proj₁ (Ωt one))

act₁ : Tr⁺ one
act₁ = T.ψ ℓ₁ o₁ (rbᶻ ℓ₁) (B₀ ℓ₁) one w₁ (Ωt one) D₆

ideal-keeps : ∀ lem → Σ _ λ K → Keep★.kp★ (cmpᴵ lem) ℓ₁ o₁ p₁ w₁ ≡ just K
ideal-keeps lem = _ , refl

actual-chains : T.ψ ℓ₁ o₁ (rbᶻ ℓ₁) (B₀ ℓ₁) one w₁ (Ωt one) D₆ ≡ limc⁺ (λ _ → Ωt one)
actual-chains = refl
```

保留结点的分支都是 β 时, 值不超过 β; 链的第 1 个部分和已是 β + β.

```agda
keep-out : ∀ {X : Set} {x₀ : X} (m : Keep one X x₀) (s : X → X) K → m ≡ just K
         → W.val one (proj₁ (node⁺ m (λ _ → Ωt one) s)) W.≼ V₁
keep-out _ s K refl = W.Ω≼ (λ z → W.≼-refl V₁)

two≽ : W.suc V₁ W.≼ W.val one (proj₁ (Ωt one) + proj₁ (Ωt one))
two≽ = W.≼-trans (W.≼Ω zero (W.≼-refl (W.suc V₁))) (proj₂ (W.val-+ (proj₁ (Ωt one)) (proj₁ (Ωt one))))

module _ (cmpK cmpE : Cmp) where
  open Star cmpK cmpE

  k6-lower : ∀ K → kp★ ℓ₁ o₁ p₁ w₁ ≡ just K
    → ¬ (W.val one (proj₁ act₁) W.≼ W.val one (proj₁ (ψ★ ℓ₁ o₁ (B₀ ℓ₁) one w₁ (Ωt one) D₆)))
  k6-lower K e d = irrV V₁ (W.≼-trans two≽ (W.≼-trans (W.lim⁻ 1 d) (keep-out (kp★ ℓ₁ o₁ p₁ w₁) _ K e)))

no-transferⱼ : ∀ (lem : LEM) → ¬ (∀ ℓ o B j w β x →
  W.val j (proj₁ (T.ψ ℓ o (rbᶻ ℓ) B j w β x)) W.≼ W.val j (proj₁ (Ideal.ψ★ lem ℓ o B j w β x)))
no-transferⱼ lem T1 =
  k6-lower (cmpᴵ lem) (cmpᴵ lem) (proj₁ (ideal-keeps lem)) refl (T1 ℓ₁ o₁ (B₀ ℓ₁) one w₁ (Ωt one) D₆)
```

## 第 0 层

外层结点 `X₃` 在孩子 0 的第 1 层上分支, 回灌目标正是上面的格. 链点在两边的构造子不同 (对 K6 格上的任意分支都如此, `chains-split`); 分支 `G₃` 在链点是 ℕ 极限时取 D₆, 是 Ω 结点时取 0. 于是现折叠是 ω̂·ω 型, ψ★ 是 ω̂ + ω 型.

```agda
chains-split : ∀ lem (g : Tr zero → Tr ℓ₁) →
    (Σ _ λ f → Σ _ λ a → proj₁ (T.ψ ℓ₁ o₁ (rbᶻ ℓ₁) (B₀ ℓ₁) one w₁ (Ωt one) (Ω p₁ g)) ≡ lim f a)
  × (Σ _ λ q → Σ _ λ G → proj₁ (Ideal.ψ★ lem ℓ₁ o₁ (B₀ ℓ₁) one w₁ (Ωt one) (Ω p₁ g)) ≡ Ω q G)
chains-split lem g = (_ , _ , refl) , (_ , _ , refl)

G₃ : Tr one → Tr ℓ₁
G₃ zero         = D₆
G₃ (suc _)      = zero
G₃ (lim _ _)    = D₆
G₃ (Ω _ _)      = zero
G₃ (up _ _ _ _) = zero

X₃ : Tr ℓ₁
X₃ = Ω (inj₂ (zero , inj₁ tt)) G₃

ω̂ : Tr zero
ω̂ = proj₁ (limc⁺ {Sig zero} (λ _ → Ωt zero))

c₁ : ℕ → Tr zero
c₁ = cum (λ _ → suc zero)

act-lo : Lv.suc (readRW (ω̂ + ω̂)) A.≼ readRW (proj₁ (ψ₀ᶻ ℓ₁ o₁ X₃))
act-lo = A.≼l 2 (A.≼l 0 (A.≼-refl (Lv.suc (readRW (ω̂ + ω̂)))))

module N₀ (lem : LEM) where
  open Ideal lem

  s★ : Tr one → Tr one
  s★ z = proj₁ (ψ★ ℓ₁ o₁ (B₀ ℓ₁) one w₁ (Ωt one) (G₃ z))

  F★ : ℕ → Tr zero
  F★ n = proj₁ (ψ★ ℓ₁ o₁ (B₀ ℓ₁) zero (z≤ ℓ₁) (Ωt zero) (G₃ (iter s★ zero n)))

  IsΩ : Tr one → Set
  IsΩ (Ω _ _) = ⊤
  IsΩ _       = ⊥

  s★-Ω : ∀ t → IsΩ t → IsΩ (s★ t)
  s★-Ω zero         ()
  s★-Ω (suc _)      ()
  s★-Ω (lim _ _)    ()
  s★-Ω (Ω _ _)      _ = tt
  s★-Ω (up _ _ _ _) ()

  iterΩ : ∀ m → IsΩ (iter s★ zero (suc m))
  iterΩ zero    = tt
  iterΩ (suc m) = s★-Ω (iter s★ zero (suc m)) (iterΩ m)

  G₃-Ω : ∀ t → IsΩ t → G₃ t ≡ zero
  G₃-Ω zero         ()
  G₃-Ω (suc _)      ()
  G₃-Ω (lim _ _)    ()
  G₃-Ω (Ω _ _)      _ = refl
  G₃-Ω (up _ _ _ _) ()

  eqF : ∀ m → F★ (suc m) ≡ suc zero
  eqF m = cong (λ t → proj₁ (ψ★ ℓ₁ o₁ (B₀ ℓ₁) zero (z≤ ℓ₁) (Ωt zero) t)) (G₃-Ω _ (iterΩ m))

  claim : ∀ n → readRW (cum F★ n) A.≼ readRW (ω̂ + c₁ n)
  claim zero    = A.≼-suc (A.≼-refl (readRW ω̂))
  claim (suc m) = subst (λ Z → Z A.≼ Lv.suc (readRW (ω̂ + c₁ m)))
    (sym (cong (λ y → readRW (cum F★ m + y)) (eqF m))) (A.s≼s (claim m))

  ideal-hi : readRW (proj₁ (ψ₀★ ℓ₁ o₁ X₃)) A.≼ readRW (ω̂ + ω̂)
  ideal-hi = A.l≼ (λ n → A.≼l n (claim n))

  k6-lower₀ : ¬ (readRW (proj₁ (ψ₀ᶻ ℓ₁ o₁ X₃)) A.≼ readRW (proj₁ (ψ₀★ ℓ₁ o₁ X₃)))
  k6-lower₀ d = irrRW (ω̂ + ω̂) (A.≼-trans act-lo (A.≼-trans d ideal-hi))

no-transfer₀ : ∀ (lem : LEM) → ¬ (∀ ℓ o x → readRW (proj₁ (ψ₀ᶻ ℓ o x)) A.≼ readRW (proj₁ (Ideal.ψ₀★ lem ℓ o x)))
no-transfer₀ lem T1 = N₀.k6-lower₀ lem (T1 ℓ₁ o₁ X₃)
```

## 保留那一行要的引理: 部分和被保留分支吸收

在第 j 层, 链 (部分和极限) 的每个部分和若不高于保留结点的某个分支, 链就不高于保留结点. 前提可满足: 常值 1 的链对 `Ωt one` 的分支 (第 n 个部分和对分支 `nat n`).

```agda
chain≼keep : ∀ {j} (F : ℕ → Tr⁺ j) (q : Pos j) (G : Br j q → Tr⁺ j)
  → (∀ n → Σ (Br j q) λ z → W.val j (cum (λ k → proj₁ (F k)) n) W.≼ W.val j (proj₁ (G z)))
  → W.val j (proj₁ (limc⁺ F)) W.≼ W.val j (proj₁ (Ω⁺ q G))
chain≼keep F q G ab = W.l≼ (λ n → W.≼Ω (proj₁ (ab n)) (proj₂ (ab n)))

nat : ℕ → Tr zero
nat zero    = zero
nat (suc n) = suc (nat n)

absorb-one : ∀ n → W.val one (cum (λ _ → suc zero) n)
                   W.≼ W.val one (up zero tt (suc (nat n)) (z◃ (nat n) ◃s))
absorb-one zero    = W.≼-refl _
absorb-one (suc n) = W.s≼s (absorb-one n)

chain≼keep-inst : W.val one (proj₁ (limc⁺ {Sig one} (λ _ → suc zero , ◃s)))
                  W.≼ W.val one (proj₁ (Ωt one))
chain≼keep-inst = chain≼keep (λ _ → suc zero , ◃s) (inj₂ (tt , inj₁ tt))
  (λ c → upz tt (suc c , z◃ c ◃s)) (λ n → nat n , absorb-one n)
```

## 链那一行要的引理: 对分支参数的值单调

链点在两边不同 (`chains-split`), 所以链那一行要 "ψ★ 对分支参数按值单调". 对一般的合法树不成立: 第 1 层的 ω 型链 (值不高于 Ω 结点 `Ωt one`, 即上面的实例) 被 `G₃` 送到 D₆, `Ωt one` 被送到 0.

```agda
zlim : Tr one
zlim = proj₁ (limc⁺ {Sig one} (λ _ → suc zero , ◃s))

no-mon : ∀ (lem : LEM) → ¬ (∀ (z z′ : Tr one) → W.val one z W.≼ W.val one z′
  → readRW (proj₁ (Ideal.ψ₀★ lem ℓ₁ o₁ (G₃ z))) A.≼ readRW (proj₁ (Ideal.ψ₀★ lem ℓ₁ o₁ (G₃ z′))))
no-mon lem M = A.s≼0 (A.s≼s⁻ (A.≼-trans (A.≼l 1 (A.≼-refl (readRW (c₁ 1))))
  (M zlim (proj₁ (Ωt one)) chain≼keep-inst)))
```

## 换基候选同样不成立

换基候选的 Ω 结点一行与主线相同 (`kp` 来自 `YiRWFold`), 所以同一个退化结点给出同一个反例, 对任意证据 r 与 `seen` 的两种底.

```agda
k6-lowerᴮ : ∀ (lem : LEM) ctx (r : BB.Rb ℓ₁)
  → ¬ (W.val one (proj₁ (BS.ψ ℓ₁ o₁ r (B₀ ℓ₁) one w₁ (Ωt one) D₆))
       W.≼ W.val one (proj₁ (SB.StarB.ψ (cmpᴵ lem) ctx ℓ₁ o₁ r (B₀ ℓ₁) one w₁ (Ωt one) D₆)))
k6-lowerᴮ lem ctx r d = irrV V₁ (W.≼-trans two≽ (W.≼-trans (W.lim⁻ 1 d)
  (keep-out (Keep★.kp★ (cmpᴵ lem) ℓ₁ o₁ p₁ w₁) (λ z → z) (proj₁ (ideal-keeps lem)) refl)))
```
