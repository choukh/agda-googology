# 理想折叠 ψ★: 主线一份

> 验收文件, 不进成品. 编译定义: 按两个比较函数参数化的折叠 `Star cmpK cmpE` (`cmpK` 管保留判定的 K6 一行, `cmpE` 管嵌入行), 经典实例 `Ideal lem` (排中律作模块参数, 结论读作 "条件（排中律）"); 来源 P4 的 `P4Star`, 改为两个比较函数, 理想比较先查主线的表 `tbᶻ`.
> 编译定理: `kp★-refine` (现保留判定给出保留时, ψ★ 逐字给同一保留), `kp★-cmp₀`, `cmpᴵ-no` (理想比较只在两方向都没有路径时缺项), 两行在空比较下逐字退回 (`k6-cmp₀`, `emb-cmp₀`).
> 不否定什么; 转移引理的止损与否定在 [YiPSNeg](YiPSNeg.lagda.md), 换基候选的一份在 [YiPSStarB](YiPSStarB.lagda.md), 最小格在 [YiPSCell](YiPSCell.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPSStar where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; kp; kp⁼; node⁺; nodeLe)
open import OCF.Lean.YiTBRow using (dW; dW-ind; dW-ind₂; IsNat; isn; isNat)
open import OCF.Lean.YiMTTab using (tbᶻ)
```

## 比较函数

`Cmp` 的条目与 `YiTBRow.RbS (sΩ k) h` 同型 (c 是嵌入或槽位所在的孩子, c′ 是目标经过的孩子). `m ▹ n` 先查 m, 缺项再查 n.

```agda
Cmp : Set
Cmp = ∀ {k : L} (h : Tr k → L) (c c′ : Tr k) → Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))

orElse : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
orElse (just a) _ = just a
orElse nothing  m = m

infixr 5 _▹_
_▹_ : Cmp → Cmp → Cmp
(m ▹ n) h c c′ = orElse (m h c c′) (n h c c′)

cmp₀ : Cmp
cmp₀ h c c′ = nothing

cmpᶻ : Cmp
cmpᶻ {k} h c c′ = tbᶻ k h c c′

sameNat : ∀ {h : Tr zero → L} {c c′ : Tr zero} → Maybe (IsNat c) → Maybe (IsNat c′)
        → Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))
sameNat (just (isn n)) (just (isn m)) with n ≟ m
... | yes refl = just (inj₁ self)
... | no _     = nothing
sameNat _ _ = nothing

cmpN : Cmp
cmpN {k = zero}   h c c′ = sameNat {h = h} (isNat c) (isNat c′)
cmpN {k = nd _ _} h c c′ = nothing

LEM : Set₁
LEM = (A : Set) → A ⊎ (A → ⊥)

pick : ∀ {A B : Set} → A ⊎ (A → ⊥) → B ⊎ (B → ⊥) → Maybe (A ⊎ B)
pick (inj₁ a) _        = just (inj₁ a)
pick (inj₂ _) (inj₁ b) = just (inj₂ b)
pick (inj₂ _) (inj₂ _) = nothing

cmpL : LEM → Cmp
cmpL lem h c c′ = pick (lem (h c′ ≤ h c)) (lem (h c ≤ h c′))

cmpᴵ : LEM → Cmp
cmpᴵ lem = cmpᶻ ▹ cmpN ▹ cmpL lem
```

理想比较扩展主线的表, 只在两个方向都没有路径时缺项.

```agda
orElse-ext : ∀ {A : Set} {a : A} (m n : Maybe A) → m ≡ just a → orElse m n ≡ just a
orElse-ext (just a) n refl = refl
orElse-ext nothing  n ()

orElse-no : ∀ {A : Set} (m n : Maybe A) → orElse m n ≡ nothing → n ≡ nothing
orElse-no nothing  n e  = e
orElse-no (just a) n ()

pick-no : ∀ {A B : Set} (x : A ⊎ (A → ⊥)) (y : B ⊎ (B → ⊥)) → pick x y ≡ nothing → (A → ⊥) × (B → ⊥)
pick-no (inj₁ a)  _         ()
pick-no (inj₂ na) (inj₁ b)  ()
pick-no (inj₂ na) (inj₂ nb) _ = na , nb

cmpᴵ-ext : ∀ lem {k} (h : Tr k → L) c c′ {a} → tbᶻ k h c c′ ≡ just a → cmpᴵ lem h c c′ ≡ just a
cmpᴵ-ext lem {k} h c c′ e = orElse-ext (tbᶻ k h c c′) _ e

cmpᴵ-no : ∀ lem {k} (h : Tr k → L) c c′ → cmpᴵ lem h c c′ ≡ nothing
        → ((h c′ ≤ h c) → ⊥) × ((h c ≤ h c′) → ⊥)
cmpᴵ-no lem {k} h c c′ e =
  pick-no (lem (h c′ ≤ h c)) (lem (h c ≤ h c′))
    (orElse-no (cmpN h c c′) _ (orElse-no (tbᶻ k h c c′) _ e))
```

## 保留判定

与 `YiRWFold.kp` 逐行相同, 只改 K6 一行 (原行恒为 `nothing`): 查 `cmpK h c c′`, 有路径就把槽位推进同一个孩子, 写法同 ℕ 极限一行.

```agda
Ref : ∀ {A : Set} → Maybe A → Maybe A → Set
Ref m m★ = (m ≡ nothing) ⊎ (m★ ≡ m)

mapK-ref : ∀ {j X Y x₀ y₀} (f : X → Y) (e : f x₀ ≡ y₀) {m m★ : Keep j X x₀}
         → Ref m m★ → Ref (mapK f e m) (mapK f e m★)
mapK-ref f e (inj₁ refl) = inj₁ refl
mapK-ref f e (inj₂ refl) = inj₂ refl

module Keep★ (cmpK : Cmp) where
  mutual
    kp★ : (ℓ : L) → Ok ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)
    kp★ ℓ             o               p              self      = just (p , (λ z → z) , refl)
    kp★ (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼★ (h c) (oc c) t (vs c)
    kp★ (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kp⁼★ (h c) (oc c) t (v ∙ kh c)
    kp★ (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼★ (h c) (oc c) t v
    kp★ (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
      cW (way g r m n) (λ u → mapK (pshBr u t) (pshFirst u t) (kp⁼★ (g n) (oc n) (psh u t) v))
                       (λ u → kp⁼★ (g m) (oc m) t (v ∙ u))
    kp★ (nd (sΩ k) h) (_ , oc)        (inj₂ (c , t)) (inc c′ v) =
      dW (cmpK h c c′)
        (λ u → kp⁼★ (h c) (oc c) t (v ∙ u))
        (λ u → mapK (pshBr u t) (pshFirst u t) (kp⁼★ (h c′) (oc c′) (psh u t) v))
        nothing
    kp★ (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼★ k ok t v
    kp★ (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
      mapK (pshBr (kh c) t) (pshFirst (kh c) t) (kp⁼★ (h c) (oc c) (psh (kh c) t) v)
    kp★ (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
      mapK (pshBr (kh zero) t) (pshFirst (kh zero) t) (kp⁼★ (h zero) (oc zero) (psh (kh zero) t) (vs zero))

    kp⁼★ : (a : L) → Ok a → (t : Pos⁼ a) → ∀ {j} → j ≤ a → Keep j (Br⁼ a t) (bz⁼ a t)
    kp⁼★ a o (inj₁ _) w = nothing
    kp⁼★ a o (inj₂ p) w = kp★ a o p w
```

现保留判定给出保留时, ψ★ 给同一个保留 (对任意 `cmpK`). 所以保留判定只在 "现判定走链" 的格上分开 (嵌入行另算).

```agda
  mutual
    kp★-refine : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → Ref (kp ℓ o p w) (kp★ ℓ o p w)
    kp★-refine ℓ             o               p              self      = inj₂ refl
    kp★-refine (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼★-refine (h c) (oc c) t (vs c)
    kp★-refine (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kp⁼★-refine (h c) (oc c) t (v ∙ kh c)
    kp★-refine (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼★-refine (h c) (oc c) t v
    kp★-refine (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
      cW-ind₂ (λ Z Z★ → Ref Z Z★) (way g r m n)
        (λ u → mapK-ref (pshBr u t) (pshFirst u t) (kp⁼★-refine (g n) (oc n) (psh u t) v))
        (λ u → kp⁼★-refine (g m) (oc m) t (v ∙ u))
    kp★-refine (nd (sΩ k) h) (_ , oc)        (inj₂ (c , t)) (inc c′ v) = inj₁ refl
    kp★-refine (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼★-refine k ok t v
    kp★-refine (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
      mapK-ref (pshBr (kh c) t) (pshFirst (kh c) t) (kp⁼★-refine (h c) (oc c) (psh (kh c) t) v)
    kp★-refine (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
      mapK-ref (pshBr (kh zero) t) (pshFirst (kh zero) t) (kp⁼★-refine (h zero) (oc zero) (psh (kh zero) t) (vs zero))

    kp⁼★-refine : (a : L) (o : Ok a) (t : Pos⁼ a) {j : L} (w : j ≤ a) → Ref (kp⁼ a o t w) (kp⁼★ a o t w)
    kp⁼★-refine a o (inj₁ _) w = inj₁ refl
    kp⁼★-refine a o (inj₂ p) w = kp★-refine a o p w

```

空比较下 ψ★ 的保留判定就是现判定.

```agda
mutual
  kp★-cmp₀ : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → Keep★.kp★ cmp₀ ℓ o p w ≡ kp ℓ o p w
  kp★-cmp₀ ℓ             o               p              self      = refl
  kp★-cmp₀ (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼★-cmp₀ (h c) (oc c) t (vs c)
  kp★-cmp₀ (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kp⁼★-cmp₀ (h c) (oc c) t (v ∙ kh c)
  kp★-cmp₀ (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼★-cmp₀ (h c) (oc c) t v
  kp★-cmp₀ (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind₂ _≡_ (way g r m n)
      (λ u → cong (mapK (pshBr u t) (pshFirst u t)) (kp⁼★-cmp₀ (g n) (oc n) (psh u t) v))
      (λ u → kp⁼★-cmp₀ (g m) (oc m) t (v ∙ u))
  kp★-cmp₀ (nd (sΩ k) h) (_ , oc)        (inj₂ (c , t)) (inc c′ v) = refl
  kp★-cmp₀ (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼★-cmp₀ k ok t v
  kp★-cmp₀ (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
    cong (mapK (pshBr (kh c) t) (pshFirst (kh c) t)) (kp⁼★-cmp₀ (h c) (oc c) (psh (kh c) t) v)
  kp★-cmp₀ (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
    cong (mapK (pshBr (kh zero) t) (pshFirst (kh zero) t)) (kp⁼★-cmp₀ (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kp⁼★-cmp₀ : (a : L) (o : Ok a) (t : Pos⁼ a) {j : L} (w : j ≤ a) → Keep★.kp⁼★ cmp₀ a o t w ≡ kp⁼ a o t w
  kp⁼★-cmp₀ a o (inj₁ _) w = refl
  kp⁼★-cmp₀ a o (inj₂ p) w = kp★-cmp₀ a o p w
```

## 折叠

与 `YiTBRow.ψ` 逐行相同; 保留判定换成 `kp★`, 嵌入行的表换成 `cmpE`. `Star cmp₀ cmpᶻ` 的各行就是主线 (`YiTBRow.ψ` 配 `rbᶻ`) 的各行; `Star cmp₀ cmp₀` 的各行就是 `YiRWFold.ψ` 的各行.

```agda
module Star (cmpK cmpE : Cmp) where
  open Keep★ cmpK public using (kp★; kp⁼★)

  mutual
    ψ★ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
    ψ★ ℓ o B j w β zero      = β
    ψ★ ℓ o B j w β (suc x)   = next⁺ (ψ★ ℓ o B j w β x)
    ψ★ ℓ o B j w β (lim f a) = lim⁺ (λ n → ψ★ ℓ o B j w β (f n)) (λ n → mono★ ℓ o B j w β (a n))
    ψ★ ℓ o B j w β (Ω p g)   = node⁺ (kp★ ℓ o p w) (λ z → ψ★ ℓ o B j w β (g z))
      (λ z → fromBr ℓ p (proj₁ (ψ★ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    ψ★ (nd s h) o B _ self β (up x c y e) = Up (h c) (down stop c) (ψ★ (nd s h) o B _ self β x) y
    ψ★ (nd s h) o B j (inu ws) β (up x c y e) =
      ψ★ (h c) (proj₂ o c) (λ i u → ψ★ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ★ (nd s h) o B j (inu ws) β x) y
    ψ★ (nd (sΩ k) h) o B j (ink v) β (up x c y e) =
      ψ★ (h c) (proj₂ o c) (λ i u → ψ★ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ★ (nd (sΩ k) h) o B j (ink v) β x) y
    ψ★ (nd sS h) o B j (inc c′ v) β (up x c y e) =
      ψ★ (h c) (proj₂ o c) (λ i u → ψ★ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ★ (nd sS h) o B j (inc c′ v) β x) y
    ψ★ (nd sL g) o B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
      (λ u → ψ★ (g n) (proj₂ o n) (λ i u′ → ψ★ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ★ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → ψ★ (g m) (proj₂ o m) (λ i u′ → ψ★ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ★ (nd sL g) o B j (inc n v) β x) y)
    ψ★ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) = dW (cmpE h c c′)
      (λ u → ψ★ (h c) (proj₂ o c) (λ i u′ → ψ★ (nd (sΩ k) h) o B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
               (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x) y)
      (λ u → ψ★ (h c′) (proj₂ o c′) (λ i u′ → ψ★ (nd (sΩ k) h) o B i (inc c′ u′) (B i (inc c′ u′)) x) j v
               (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x) (proj₁ (emb (h c′) (proj₂ o c′) u (y , e))))
      (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ★ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)

    mono★ : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
          → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ★ ℓ o B j w β x) ◃ proj₁ (ψ★ ℓ o B j w β y)
    mono★ ℓ o B j w β ◃s           = ◃l zero
    mono★ ℓ o B j w β (◃l n)       = ◃l n
    mono★ ℓ o B j w β (◃w {p = p}) = nodeLe (kp★ ℓ o p w) _ _
    mono★ (nd s h) o B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ★ (nd s h) o B _ self β x) e
    mono★ (nd s h) o B j (inu ws) β (◃u x c y e) =
      mono★ (h c) (proj₂ o c) (λ i u → ψ★ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ★ (nd s h) o B j (inu ws) β x) e
    mono★ (nd (sΩ k) h) o B j (ink v) β (◃u x c y e) =
      mono★ (h c) (proj₂ o c) (λ i u → ψ★ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ★ (nd (sΩ k) h) o B j (ink v) β x) e
    mono★ (nd sS h) o B j (inc c′ v) β (◃u x c y e) =
      mono★ (h c) (proj₂ o c) (λ i u → ψ★ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ★ (nd sS h) o B j (inc c′ v) β x) e
    mono★ (nd sL g) o B j (inc n v) β (◃u x m y e) =
      cW-ind (λ Z → j ⊢ proj₁ (ψ★ (nd sL g) o B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
        (λ u → mono★ (g n) (proj₂ o n) (λ i u′ → ψ★ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ★ (nd sL g) o B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
        (λ u → mono★ (g m) (proj₂ o m) (λ i u′ → ψ★ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ★ (nd sL g) o B j (inc n v) β x) e)
    mono★ (nd (sΩ k) h) o B j (inc c′ v) β (◃u x c y e) =
      dW-ind (λ Z → j ⊢ proj₁ (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x) ◃ proj₁ Z) (cmpE h c c′)
        (λ u → mono★ (h c) (proj₂ o c) (λ i u′ → ψ★ (nd (sΩ k) h) o B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
                 (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x) e)
        (λ u → mono★ (h c′) (proj₂ o c′) (λ i u′ → ψ★ (nd (sΩ k) h) o B i (inc c′ u′) (B i (inc c′ u′)) x) j v
                 (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x) (proj₂ (emb (h c′) (proj₂ o c′) u (y , e))))
        (+-mono _ (ι-mono j (proj₂ (ψ★ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))
    mono★ (nd s h) o B _ self β (◃c x c d) = Upm (h c) (down stop c) (ψ★ (nd s h) o B _ self β x) d
    mono★ (nd s h) o B j (inu ws) β (◃c x c d) =
      mono★ (h c) (proj₂ o c) (λ i u → ψ★ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ★ (nd s h) o B j (inu ws) β x) d
    mono★ (nd (sΩ k) h) o B j (ink v) β (◃c x c d) =
      mono★ (h c) (proj₂ o c) (λ i u → ψ★ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
        (ψ★ (nd (sΩ k) h) o B j (ink v) β x) d
    mono★ (nd sS h) o B j (inc c′ v) β (◃c x c d) =
      mono★ (h c) (proj₂ o c) (λ i u → ψ★ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ★ (nd sS h) o B j (inc c′ v) β x) d
    mono★ (nd sL g) o B j (inc n v) β (◃c x m d) =
      cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
        (λ u → mono★ (g n) (proj₂ o n) (λ i u′ → ψ★ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
                 (ψ★ (nd sL g) o B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u d))
        (λ u → mono★ (g m) (proj₂ o m) (λ i u′ → ψ★ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
                 (ψ★ (nd sL g) o B j (inc n v) β x) d)
    mono★ (nd (sΩ k) h) o B j (inc c′ v) β (◃c x c d) =
      dW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (cmpE h c c′)
        (λ u → mono★ (h c) (proj₂ o c) (λ i u′ → ψ★ (nd (sΩ k) h) o B i (inc c u′) (B i (inc c u′)) x) j (v ∙ u)
                 (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x) d)
        (λ u → mono★ (h c′) (proj₂ o c′) (λ i u′ → ψ★ (nd (sΩ k) h) o B i (inc c′ u′) (B i (inc c′ u′)) x) j v
                 (ψ★ (nd (sΩ k) h) o B j (inc c′ v) β x) (emb-mono (h c′) (proj₂ o c′) u d))
        (+-mono _ (ι-mono j (mono★ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))
    mono★ ℓ o B j w β (◃t d d′) = ◃t (mono★ ℓ o B j w β d) (mono★ ℓ o B j w β d′)

  ψ₀★ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
  ψ₀★ ℓ o = ψ★ ℓ o (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

  tw★ : ℕ → Tr zero
  tw★ n = proj₁ (ψ₀★ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))

  EBO★ : Tr zero
  EBO★ = proj₁ (ψ₀★ Λ Ok-Λ (proj₁ (Ωt Λ)))

module Ideal (lem : LEM) = Star (cmpᴵ lem) (cmpᴵ lem)
```

## 两行在空比较下逐字退回

```agda
k6-cmp₀ : ∀ k h (o : Ok (nd (sΩ k) h)) c t {j} c′ (v : j ≤ h c′)
  → Keep★.kp★ cmp₀ (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ nothing
k6-cmp₀ k h o c t c′ v = refl

emb-cmp₀ : ∀ (cmpK : Cmp) k h (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → Star.ψ★ cmpK cmp₀ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
  ≡ (Star.ψ★ cmpK cmp₀ (nd (sΩ k) h) o B j (inc c′ v) β x
       ⊞ Star.ψ★ cmpK cmp₀ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)
emb-cmp₀ cmpK k h o B j c′ v β x c y e = refl
```
