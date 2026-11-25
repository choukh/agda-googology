# 合流关系族上的 LowKeep: 不含 Ω 形状的层号, 槽位标签取 `Lblᵒ`

> 验收文件 (读记号)。编译定理, 无前提: 槽位标签取 `YiELOmega.Lblᵒ` 时不含 Ω 形状的层号有框架、路径证据与 `IndexTree` (`frameᵒ`, `index-allᵒ`, `index-treeᵒ`), 所以 `YiXPFold Lblᵒ` 的保持无条件成立 (`pres-noΩᵒ`); 经 `Rᵐ` 与 `YiXPRel Lblᵒ` 的 `R` 互相给出 (`toX`, `ofX`), 得 `lowKeepAtᵐ-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtᵐ ℓ`; 最小实例各孩子层号的实例 `lowKeep-child`, 前提全部填上的 `keep-child-zero`。
> 用到 `Lblᵒ` 的性质: `uniqᵒ`, `belowᵒ` (`PosOk` 在不含 Ω 形状的层号上恒成立, `allok-noΩ`), 标签沿路径不降 (`lbl-pathᵒ`, 本文新证)。来源: 框架各行逐行搬自 `YiXPFrame`, 只把 `Lbl` 换成 `Lblᵒ`。
> 不涉及 Ω 形状层号 (见 [YiMGNeck](YiMGNeck.lagda.md)); 不否定什么。关系族在 [YiMGRel](YiMGRel.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMGFrame where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; kp⁼; mapK)
open import OCF.Lean.YiKVRel using (⊴r)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK)
open import OCF.Lean.YiFMMap using (mapᴴ)
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-<)
open import OCF.Align.EboLean3Base using (sucT≤)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Lean.YiGLFrame using (pred<; <→gt; ≤→pen)
open import OCF.Lean.YiELOmega using (Lblᵒ; uniqᵒ; belowᵒ; PosOk; PosOk⁼)
open import OCF.Lean.YiXPFrame using (NoΩ; noΩ-ch)
open import OCF.Lean.YiMGRel using (Rᵐ; Lowᵐ; Low⁼ᵐ; noΩ-at; noΩ-child; topᵐ)
open import OCF.Lean.YiXPRel Lblᵒ
open import OCF.Lean.YiXPRows Lblᵒ
open import OCF.Lean.YiXPFold Lblᵒ
```

## `Rᵐ` 与 `YiXPRel Lblᵒ` 互相给出

两者槽位标签相同, 分支前提只在颈槽位不同; 不含 Ω 形状的层号没有颈槽位。

```agda
mutual
  toX : ∀ ℓ → NoΩ ℓ → ∀ {t x} → Rᵐ ℓ t x → R ℓ t x
  toX zero _ m = m
  toX (nd s h) nω m = mapᴴ (lowOfX (nd s h) nω) (λ c → toX (h c) (noΩ-ch s h nω c)) (λ p q → q) m

  ofX : ∀ ℓ → NoΩ ℓ → ∀ {t x} → R ℓ t x → Rᵐ ℓ t x
  ofX zero _ m = m
  ofX (nd s h) nω m = mapᴴ (lowToX (nd s h) nω) (λ c → ofX (h c) (noΩ-ch s h nω c)) (λ p q → q) m

  lowOfX : ∀ ℓ → NoΩ ℓ → ∀ p {η c} → Low ℓ p η c → Lowᵐ ℓ p η c
  lowOfX (nd s h) nω (inj₂ (c , t)) = lowOf⁼X (h c) (noΩ-ch s h nω c) t
  lowOfX (nd (sΩ k) h) () (inj₁ t)

  lowOf⁼X : ∀ a → NoΩ a → ∀ t {η c} → Low⁼ a t η c → Low⁼ᵐ a t η c
  lowOf⁼X a nω (inj₁ _) = ofX a nω
  lowOf⁼X a nω (inj₂ p) = lowOfX a nω p

  lowToX : ∀ ℓ → NoΩ ℓ → ∀ p {η c} → Lowᵐ ℓ p η c → Low ℓ p η c
  lowToX (nd s h) nω (inj₂ (c , t)) = lowTo⁼X (h c) (noΩ-ch s h nω c) t
  lowToX (nd (sΩ k) h) () (inj₁ t)

  lowTo⁼X : ∀ a → NoΩ a → ∀ t {η c} → Low⁼ᵐ a t η c → Low⁼ a t η c
  lowTo⁼X a nω (inj₁ _) = toX a nω
  lowTo⁼X a nω (inj₂ p) = lowToX a nω p
```

## 读回域恒成立, 标签沿路径不降, 沿 `psh` 换型

```agda
mutual
  allok-noΩ : ∀ a → NoΩ a → (p : Pos a) → PosOk a p
  allok-noΩ (nd sS h) nω (inj₁ ())
  allok-noΩ (nd sS h) nω (inj₂ (tt , t)) = tt , allok⁼-noΩ (h tt) nω t
  allok-noΩ (nd sL g) nω (inj₁ ())
  allok-noΩ (nd sL g) nω (inj₂ (n , t)) = tt , allok⁼-noΩ (g n) (nω n) t
  allok-noΩ (nd (sΩ k) h) () p

  allok⁼-noΩ : ∀ a → NoΩ a → (t : Pos⁼ a) → PosOk⁼ a t
  allok⁼-noΩ a nω (inj₁ _) = tt
  allok⁼-noΩ a nω (inj₂ p) = allok-noΩ a nω p

noΩ-path : ∀ {j a} → j ≤ a → NoΩ a → NoΩ j
noΩ-path self nω = nω
noΩ-path {a = nd s h} (inc c v) nω = noΩ-path v (noΩ-ch s h nω c)
noΩ-path {a = nd s h} (inu vs) nω = noΩ-path (vs (c₀ s)) (noΩ-ch s h nω (c₀ s))
noΩ-path (ink v) ()

lbl-pathᵒ : ∀ {j a} → j ≤ a → NoΩ a → ∀ {ν κ} → Lblᵒ j ν → Lblᵒ a κ → ν ≤ᵀ κ
lbl-pathᵒ {j} self nω lν lκ = inj₂ (uniqᵒ j lν lκ)
lbl-pathᵒ {a = nd sS h} (inc tt v) nω {κ = κ} lν (e , q) = inj₁ (≤-< (lbl-pathᵒ v nω lν q) (pred< κ e))
lbl-pathᵒ {a = nd sL g} (inc n v) nω lν (e , _ , f) =
  inj₁ (≤-< (lbl-pathᵒ v (nω n) lν (proj₁ (proj₂ (f n)))) (proj₂ (proj₂ (proj₂ (f n)))))
lbl-pathᵒ {a = nd (sΩ k) h} (inc c v) () lν lκ
lbl-pathᵒ {a = nd sS h} (inu vs) nω {κ = κ} lν (e , q) = inj₁ (≤-< (lbl-pathᵒ (vs tt) nω lν q) (pred< κ e))
lbl-pathᵒ {a = nd sL g} (inu vs) nω lν (e , _ , f) =
  inj₁ (≤-< (lbl-pathᵒ (vs 0) (nω 0) lν (proj₁ (proj₂ (f 0)))) (proj₂ (proj₂ (proj₂ (f 0)))))
lbl-pathᵒ {a = nd (sΩ k) h} (inu vs) () lν lκ
lbl-pathᵒ (ink v) () lν lκ

lbl-pshᵒ : ∀ {k a} (u : k ≤ a) (t : Pos⁼ k) {κ}
  → Lblᵒ (proj₁ (sl⁼ k t)) κ → Lblᵒ (proj₁ (sl⁼ a (psh u t))) κ
lbl-pshᵒ self t l = l
lbl-pshᵒ (inc c v) t l = lbl-pshᵒ v t l
lbl-pshᵒ {a = nd s h} (inu vs) t l = lbl-pshᵒ (vs (c₀ s)) t l
lbl-pshᵒ (ink v) t l = lbl-pshᵒ v t l

low-pshᵒ : ∀ {k a} (u : k ≤ a) (t : Pos⁼ k) {η z}
  → Low⁼ a (psh u t) η z → Low⁼ k t η (pshBr u t z)
low-pshᵒ self t l = l
low-pshᵒ (inc c v) t l = low-pshᵒ v t l
low-pshᵒ {a = nd s h} (inu vs) t l = low-pshᵒ (vs (c₀ s)) t l
low-pshᵒ (ink v) t l = low-pshᵒ v t l

keep-mapᵒ : ∀ {k a} (u : k ≤ a) (t : Pos⁼ k) {j ν κ}
  (K : Keep j (Br⁼ a (psh u t)) (bz⁼ a (psh u t)))
  → KeepG j ν (Low⁼ a (psh u t)) κ K
  → KeepG j ν (Low⁼ k t) κ (mapK (pshBr u t) (pshFirst u t) K)
keep-mapᵒ u t nothing g = g
keep-mapᵒ u t (just (q , cv , eq)) (pen , l , low) = pen , l , λ η c x → low-pshᵒ u t (low η c x)
```

## 框架, 路径证据, IndexTree

逐条同 `YiXPFrame.frame`/`route`/`index-tree`。

```agda
mutual
  frameᵒ : ∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) {ν κ}
    → Lblᵒ j ν → Lblᵒ (at ℓ p) κ → KeepSpec ℓ j ν p κ (kp ℓ o p w)
  frameᵒ ℓ nω o p self lν lκ = ≤→pen (sucT≤ (belowᵒ ℓ p (allok-noΩ ℓ nω p) lκ lν)) , lκ , λ η c l → l
  frameᵒ (nd s h) nω (_ , oc) (inj₂ (c , t)) (inu vs) lν lκ =
    frame⁼ᵒ (h c) (noΩ-ch s h nω c) (oc c) t (vs c) lν lκ
  frameᵒ (nd sS h) nω (_ , oc) (inj₂ (c , t)) (inc _ v) lν lκ =
    frame⁼ᵒ (h c) nω (oc c) t v lν lκ
  frameᵒ (nd sL g) nω (r , oc) (inj₂ (m , t)) (inc n v) {ν} {κ} lν lκ =
    cW-ind (KeepG _ ν (Low⁼ (g m) t) κ) (way g r m n)
      (λ u → keep-mapᵒ u t (kp⁼ (g n) (oc n) (psh u t) v)
        (frame⁼ᵒ (g n) (nω n) (oc n) (psh u t) v lν (lbl-pshᵒ u t lκ)))
      (λ u → frame⁼ᵒ (g m) (nω m) (oc m) t (v ∙ u) lν lκ)
  frameᵒ (nd (sΩ k) h) () o p w lν lκ

  frame⁼ᵒ : ∀ a → NoΩ a → (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) {ν κ}
    → Lblᵒ j ν → Lblᵒ (proj₁ (sl⁼ a t)) κ → KeepG j ν (Low⁼ a t) κ (kp⁼ a o t w)
  frame⁼ᵒ a nω o (inj₁ _) w {ν} {κ} lν lκ = <→gt (≤-< (lbl-pathᵒ w nω lν lκ) (<-sucT κ))
  frame⁼ᵒ a nω o (inj₂ p) w lν lκ = frameᵒ a nω o p w lν lκ

cwᵒ : ∀ {A B : Set} (W : A ⊎ B) {F : A → Set} {G : B → Set}
  → ((a : A) → F a) → ((b : B) → G b) → CWReq W F G
cwᵒ (inj₁ a) f g = f a
cwᵒ (inj₂ b) f g = g b

mutual
  index-allᵒ : ∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (r : Rb ℓ) → ∀ {j} (w : j ≤ ℓ) {ν}
    → Lblᵒ j ν → IndexOK ℓ o r j w ν
  index-allᵒ ℓ nω o r w lν = (λ p κ lκ → frameᵒ ℓ nω o p w lν lκ) , routeᵒ ℓ nω o r w lν

  routeᵒ : ∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (r : Rb ℓ) → ∀ {j} (w : j ≤ ℓ) {ν}
    → Lblᵒ j ν → RouteOK ℓ o r j w ν
  routeᵒ ℓ nω o r self lν = tt
  routeᵒ (nd s h) nω o r (inu ws) lν c =
    index-allᵒ (h c) (noΩ-ch s h nω c) (proj₂ o c) (proj₂ r c) (ws c) lν
  routeᵒ (nd sS h) nω o r (inc c′ v) lν = index-allᵒ (h c′) nω (proj₂ o c′) (proj₂ r c′) v lν
  routeᵒ (nd sL h) nω o r (inc n v) lν m = cwᵒ (way h (proj₁ o) m n)
    (λ u → index-allᵒ (h n) (nω n) (proj₂ o n) (proj₂ r n) v lν)
    (λ u → index-allᵒ (h m) (nω m) (proj₂ o m) (proj₂ r m) (v ∙ u) lν)
  routeᵒ (nd (sΩ k) h) () o r w lν

index-treeᵒ : ∀ ℓ → NoΩ ℓ → IndexTree ℓ
index-treeᵒ zero _ = tt
index-treeᵒ (nd s h) nω =
  (λ o r p ν lν → index-allᵒ (nd s h) nω o r (posW (nd s h) p) lν)
  , λ c → index-treeᵒ (h c) (noΩ-ch s h nω c)

pres-noΩᵒ : ∀ ℓ → NoΩ ℓ → PresAt ℓ
pres-noΩᵒ ℓ nω = pres ℓ (kit ℓ (index-treeᵒ ℓ nω))
```

## LowKeep 在 `Rᵐ` 上

陈述照 `YiGLExact.LowKeepAtˣ`, 关系换成 `Rᵐ`, 标签换成 `Lblᵒ`。

```agda
Prefixᵐ : ∀ {ℓ} → Base ℓ → E.T → Set
Prefixᵐ {ℓ} B t = (p : Pos ℓ) (κ : E.T) → Lblᵒ (at ℓ p) κ
  → Rᵐ (at ℓ p) (E.ψ κ t ∷ []) (proj₁ (B (at ℓ p) (posW ℓ p)))

LowKeepAtᵐ : L → Set
LowKeepAtᵐ ℓ = ∀ {j} (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ) (β : Tr⁺ j) (ν t : E.T)
  → Lblᵒ j ν → OK B → Prefixᵐ B t → Rᵐ j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → Rᵐ ℓ a x → Rᵐ j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))

lowKeepAtᵐ-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtᵐ ℓ
lowKeepAtᵐ-noΩ ℓ nω {j} o r B w β ν t lν gb pref mb m =
  ofX j (noΩ-path w nω) (pres-noΩᵒ ℓ nω o r B gb t
    (λ p κ l → toX (at ℓ p) (noΩ-at ℓ nω p) (pref p κ l))
    j w ν (index-allᵒ ℓ nω o r w lν) β (toX j (noΩ-path w nω) mb) (toX ℓ nω m))

lowKeep-child : ∀ d → LowKeepAtᵐ (S.child d)
lowKeep-child d = lowKeepAtᵐ-noΩ (S.child d) (noΩ-child d)
```

前提可满足: 标准底对空前缀满足 `Prefixᵐ` (Leaf `topᵐ`); 孩子层号折到第 0 层的实例。

```agda
ok-B₀ : ∀ ℓ → OK (B₀ ℓ)
ok-B₀ ℓ i u = ⊴r

prefixᵐ-B₀ : ∀ ℓ → Prefixᵐ (B₀ ℓ) []
prefixᵐ-B₀ ℓ p κ l = topᵐ (at ℓ p) l

keep-child-zero : ∀ d (r : Rb (S.child d)) {a x} → Rᵐ (S.child d) a x
  → Rᵐ zero (E.ψ [] ([] ++ a) ∷ [])
      (proj₁ (ψ (S.child d) (proj₂ S.okay d) r (B₀ (S.child d)) zero (z≤ (S.child d)) (Ωt zero) x))
keep-child-zero d r m = lowKeep-child d (proj₂ S.okay d) r (B₀ (S.child d)) (z≤ (S.child d))
  (Ωt zero) [] [] refl (ok-B₀ (S.child d)) (prefixᵐ-B₀ (S.child d)) (topᵐ zero refl) m
```
