# 精确标签下的框架与路径证据: 不含 Ω 形状的层号

> 验收文件 (读记号)。编译定理, 无前提: 槽位标签取 `YiGLFrame.Lbl` 时, 不含 Ω 形状的层号 (`NoΩ`) 对任意表、证据、路径与带标签的目标都有框架 (`frame`)、路径证据 (`index-all`) 与 `IndexTree` (`index-tree`), 所以 `YiXPFold` 的一般保持无条件成立 (`pres-noΩ`)。
> 用到 `Lbl` 的性质: 唯一 (`uniq`)、槽位低于层号 (`below`)、标签沿路径不降 (`lbl-path`, 本文新证); 换型沿 `psh` 保持层号与分支关系 (`lbl-psh`, `low-psh`)。
> 不涉及 Ω 形状层号 (`Lbl` 在那里取 ⊥); 不否定什么。入口: `pres-noΩ`, 出口在 [YiXPExact](YiXPExact.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXPFrame where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Keep; kp; kp⁼; mapK)
open import OCF.Lean.YiTBRow using (Rb)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-<)
open import OCF.Align.EboLean3Base using (sucT≤)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Lean.YiGLFrame using (Lbl; uniq; below; pred<; <→gt; ≤→pen)
open import OCF.Lean.YiXPRel Lbl
open import OCF.Lean.YiXPRows Lbl
open import OCF.Lean.YiXPFold Lbl
```

## 不含 Ω 形状的层号; 标签沿路径不降

```agda
NoΩ : L → Set
NoΩ zero = ⊤
NoΩ (nd sS h) = NoΩ (h tt)
NoΩ (nd sL g) = ∀ n → NoΩ (g n)
NoΩ (nd (sΩ k) h) = ⊥

noΩ-ch : ∀ s h → NoΩ (nd s h) → (c : Ch s) → NoΩ (h c)
noΩ-ch sS h nω tt = nω
noΩ-ch sL g nω n = nω n
noΩ-ch (sΩ k) h ()

lbl-noΩ : ∀ a {ν} → Lbl a ν → NoΩ a
lbl-noΩ zero _ = tt
lbl-noΩ (nd sS h) (e , q) = lbl-noΩ (h tt) q
lbl-noΩ (nd sL g) (_ , _ , _ , f) n = lbl-noΩ (g n) (proj₁ (proj₂ (f n)))
lbl-noΩ (nd (sΩ k) h) ()

lbl-path : ∀ {j a} → j ≤ a → ∀ {ν κ} → Lbl j ν → Lbl a κ → ν ≤ᵀ κ
lbl-path {j} self lν lκ = inj₂ (uniq j lν lκ)
lbl-path {a = nd sS h} (inc tt v) {κ = κ} lν (e , q) = inj₁ (≤-< (lbl-path v lν q) (pred< κ e))
lbl-path {a = nd sL g} (inc n v) lν (e , _ , _ , f) =
  inj₁ (≤-< (lbl-path v lν (proj₁ (proj₂ (f n)))) (proj₂ (proj₂ (proj₂ (f n)))))
lbl-path {a = nd (sΩ k) h} (inc c v) lν ()
lbl-path {a = nd sS h} (inu vs) {κ = κ} lν (e , q) = inj₁ (≤-< (lbl-path (vs tt) lν q) (pred< κ e))
lbl-path {a = nd sL g} (inu vs) lν (e , _ , _ , f) =
  inj₁ (≤-< (lbl-path (vs 0) lν (proj₁ (proj₂ (f 0)))) (proj₂ (proj₂ (proj₂ (f 0)))))
lbl-path {a = nd (sΩ k) h} (inu vs) lν ()
lbl-path (ink v) lν ()
```

## 沿 `psh` 的换型

```agda
lbl-psh : ∀ {k a} (u : k ≤ a) (t : Pos⁼ k) {κ}
  → Lbl (proj₁ (sl⁼ k t)) κ → Lbl (proj₁ (sl⁼ a (psh u t))) κ
lbl-psh self t l = l
lbl-psh (inc c v) t l = lbl-psh v t l
lbl-psh {a = nd s h} (inu vs) t l = lbl-psh (vs (c₀ s)) t l
lbl-psh (ink v) t l = lbl-psh v t l

low-psh : ∀ {k a} (u : k ≤ a) (t : Pos⁼ k) {η z}
  → Low⁼ a (psh u t) η z → Low⁼ k t η (pshBr u t z)
low-psh self t l = l
low-psh (inc c v) t l = low-psh v t l
low-psh {a = nd s h} (inu vs) t l = low-psh (vs (c₀ s)) t l
low-psh (ink v) t l = low-psh v t l

keep-map : ∀ {k a} (u : k ≤ a) (t : Pos⁼ k) {j ν κ}
  (K : Keep j (Br⁼ a (psh u t)) (bz⁼ a (psh u t)))
  → KeepG j ν (Low⁼ a (psh u t)) κ K
  → KeepG j ν (Low⁼ k t) κ (mapK (pshBr u t) (pshFirst u t) K)
keep-map u t nothing g = g
keep-map u t (just (q , cv , eq)) (pen , l , low) = pen , l , λ η c x → low-psh u t (low η c x)
```

## 框架

逐条跟随 `kp`: 目标就是源层号时全保留; 槽位就是路径经过的层号时走链 (`lbl-path`); 其余递归进孩子, ℕ 极限形状按 `way` 分两支。

```agda
mutual
  frame : ∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) {ν κ}
    → Lbl j ν → Lbl (at ℓ p) κ → KeepSpec ℓ j ν p κ (kp ℓ o p w)
  frame ℓ nω o p self lν lκ = ≤→pen (sucT≤ (below ℓ p lκ lν)) , lκ , λ η c l → l
  frame (nd s h) nω (_ , oc) (inj₂ (c , t)) (inu vs) lν lκ =
    frame⁼ (h c) (noΩ-ch s h nω c) (oc c) t (vs c) lν lκ
  frame (nd sS h) nω (_ , oc) (inj₂ (c , t)) (inc _ v) lν lκ =
    frame⁼ (h c) nω (oc c) t v lν lκ
  frame (nd sL g) nω (r , oc) (inj₂ (m , t)) (inc n v) {ν} {κ} lν lκ =
    cW-ind (KeepG _ ν (Low⁼ (g m) t) κ) (way g r m n)
      (λ u → keep-map u t (kp⁼ (g n) (oc n) (psh u t) v)
        (frame⁼ (g n) (nω n) (oc n) (psh u t) v lν (lbl-psh u t lκ)))
      (λ u → frame⁼ (g m) (nω m) (oc m) t (v ∙ u) lν lκ)
  frame (nd (sΩ k) h) () o p w lν lκ

  frame⁼ : ∀ a → NoΩ a → (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) {ν κ}
    → Lbl j ν → Lbl (proj₁ (sl⁼ a t)) κ → KeepG j ν (Low⁼ a t) κ (kp⁼ a o t w)
  frame⁼ a nω o (inj₁ _) w {ν} {κ} lν lκ = <→gt (≤-< (lbl-path w lν lκ) (<-sucT κ))
  frame⁼ a nω o (inj₂ p) w lν lκ = frame a nω o p w lν lκ
```

## 路径证据与 IndexTree

```agda
cw : ∀ {A B : Set} (W : A ⊎ B) {F : A → Set} {G : B → Set}
  → ((a : A) → F a) → ((b : B) → G b) → CWReq W F G
cw (inj₁ a) f g = f a
cw (inj₂ b) f g = g b

mutual
  index-all : ∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (r : Rb ℓ) → ∀ {j} (w : j ≤ ℓ) {ν}
    → Lbl j ν → IndexOK ℓ o r j w ν
  index-all ℓ nω o r w lν = (λ p κ lκ → frame ℓ nω o p w lν lκ) , route ℓ nω o r w lν

  route : ∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (r : Rb ℓ) → ∀ {j} (w : j ≤ ℓ) {ν}
    → Lbl j ν → RouteOK ℓ o r j w ν
  route ℓ nω o r self lν = tt
  route (nd s h) nω o r (inu ws) lν c =
    index-all (h c) (noΩ-ch s h nω c) (proj₂ o c) (proj₂ r c) (ws c) lν
  route (nd sS h) nω o r (inc c′ v) lν = index-all (h c′) nω (proj₂ o c′) (proj₂ r c′) v lν
  route (nd sL h) nω o r (inc n v) lν m = cw (way h (proj₁ o) m n)
    (λ u → index-all (h n) (nω n) (proj₂ o n) (proj₂ r n) v lν)
    (λ u → index-all (h m) (nω m) (proj₂ o m) (proj₂ r m) (v ∙ u) lν)
  route (nd (sΩ k) h) () o r w lν

index-tree : ∀ ℓ → NoΩ ℓ → IndexTree ℓ
index-tree zero _ = tt
index-tree (nd s h) nω =
  (λ o r p ν lν → index-all (nd s h) nω o r (posW (nd s h) p) lν)
  , λ c → index-tree (h c) (noΩ-ch s h nω c)

pres-noΩ : ∀ ℓ → NoΩ ℓ → PresAt ℓ
pres-noΩ ℓ nω = pres ℓ (kit ℓ (index-tree ℓ nω))
```
