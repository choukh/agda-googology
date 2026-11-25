# 值关系: 折叠保持 (树侧)

> 判决: 工具, 树侧. 编译定理 `fl`: 在主线精简块上, 对一切层号 ℓ (前提 `Dflt ℓ`), 两个底在一切非 `self` 的路径上相关 (`B ⊴ B′`), 两个起点相关, 两棵树相关, 则两次折叠的输出在目标层相关; 对 (层号, 推导) 递归.
> 前提 `Dflt ℓ` 只在 Ω 形状处有内容 (分支侧一行用默认底, 要它自相关); 不含 Ω 形状的层号 (含第 1 层) 与塔第 1 项满足 (`Dflt-noΩ`, `Dflt-tw1`), 塔第 2 项不满足 (`Dflt-tw2-not`, 读作关系太窄). 规范域对折叠的输出封闭 (`can-fold`).
> 不否定什么. 关系不比较不同孩子的嵌入, 所以塔第 1 项的 Ω 树不在域里 (`YiVRRel.β-not`). 读回与用例在 `YiVRRead`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVRFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
open import OCF.Lean.YiVRRel
```

## 底的关系与前提

折叠只在 `posW` 与 `inc c u` 这样的路径上读底, 从不读 `self` 上的分量; 所以底的关系只对非 `self` 的路径要求.

```agda
Pr : ∀ {b j ℓ} → Pth b j ℓ → Set
Pr self    = ⊥
Pr (inc _ _) = ⊤
Pr (inu _)   = ⊤
Pr (ink _)   = ⊤

infix 4 _⊴_
_⊴_ : ∀ {ℓ} → Base ℓ → Base ℓ → Set
_⊴_ {ℓ} B B′ = (j : L) (w : j ≤ ℓ) → Pr w → Le j (proj₁ (B j w)) (proj₁ (B′ j w))

posW-pr : (ℓ : L) (p : Pos ℓ) → Pr (posW ℓ p)
posW-pr (nd s h)      (inj₂ (c , t)) = tt
posW-pr (nd (sΩ k) h) (inj₁ t)       = tt

DfS : (s : Sh) → (Ch s → L) → Set
DfS sS     h = ⊤
DfS sL     h = ⊤
DfS (sΩ k) h = (c : Tr k) → B₀ (h c) ⊴ B₀ (h c)

Dflt : L → Set
Dflt zero     = ⊤
Dflt (nd s h) = DfS s h × ((c : Ch s) → Dflt (h c))
```

## 保留判定的换型保持分支上的关系

```agda
KR : ∀ {j X x₀} → (X → X → Set) → Keep j X x₀ → Set
KR {j} RX (just (q , cv , _)) = (z z′ : Br j q) → LB j q z z′ → RX (cv z) (cv z′)
KR     RX nothing             = ⊤

mapKR : ∀ {j X Y x₀ y₀} {RX : X → X → Set} {RY : Y → Y → Set} (f : X → Y) (e : f x₀ ≡ y₀)
      → (∀ {x x′} → RX x x′ → RY (f x) (f x′)) → (m : Keep j X x₀) → KR RX m → KR RY (mapK f e m)
mapKR f e fr (just (q , cv , g)) kr = λ z z′ r → fr (kr z z′ r)
mapKR f e fr nothing             kr = tt

mutual
  kpR : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → KR (LB ℓ p) (kp ℓ o p w)
  kpR ℓ             o               p              self      = λ z z′ r → r
  kpR (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kpR⁼ (h c) (oc c) t (vs c)
  kpR (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kpR⁼ (h c) (oc c) t (v ∙ kh c)
  kpR (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kpR⁼ (h c) (oc c) t v
  kpR (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind (KR (LB⁼ (g m) t)) (way g r m n)
      (λ u → mapKR (pshBr u t) (pshFirst u t) (pshLB u t) (kp⁼ (g n) (oc n) (psh u t) v) (kpR⁼ (g n) (oc n) (psh u t) v))
      (λ u → kpR⁼ (g m) (oc m) t (v ∙ u))
  kpR (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = tt
  kpR (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kpR⁼ k ok t v
  kpR (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
    mapKR (pshBr (kh c) t) (pshFirst (kh c) t) (pshLB (kh c) t) (kp⁼ (h c) (oc c) (psh (kh c) t) v)
          (kpR⁼ (h c) (oc c) (psh (kh c) t) v)
  kpR (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
    mapKR (pshBr (kh zero) t) (pshFirst (kh zero) t) (pshLB (kh zero) t) (kp⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero))
          (kpR⁼ (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kpR⁼ : (a : L) (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) → KR (LB⁼ a t) (kp⁼ a o t w)
  kpR⁼ a o (inj₁ _) w = tt
  kpR⁼ a o (inj₂ p) w = kpR a o p w
```

## 结点

`node≼ʳ`: 结点不低于第一分支上的值 (`nodeLe` 的关系版). `node≼`: 两侧的保留判定相同; 保留时逐分支, 否则两条回灌链逐项相关.

```agda
node≼ʳ : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (s : X → X) {a : Tr j}
       → Le j a (proj₁ (G x₀)) → Le j a (proj₁ (node⁺ m G s))
node≼ʳ {j} (just (q , cv , e)) G s {a} d = ≼w (subst (λ t → Le j a (proj₁ (G t))) (sym e) d)
node≼ʳ nothing                 G s d     = ≼l 0 d

node≼ : ∀ {j X x₀} (RX : X → X → Set) (m : Keep j X x₀) → KR RX m → (G G′ : X → Tr⁺ j) (s s′ : X → X)
      → RX x₀ x₀ → ((z z′ : X) → RX z z′ → Le j (proj₁ (G z)) (proj₁ (G′ z′))) → ((z z′ : X) → RX z z′ → RX (s z) (s′ z′))
      → Le j (proj₁ (node⁺ m G s)) (proj₁ (node⁺ m G′ s′))
node≼ RX (just (q , cv , _)) kr G G′ s s′ r₀ hG hs = w≼w (λ z z′ r → hG (cv z) (cv z′) (kr z z′ r))
node≼ {x₀ = x₀} RX nothing   kr G G′ s s′ r₀ hG hs =
  limc≼ (λ n → G (iter s x₀ n)) (λ n → G′ (iter s′ x₀ n)) (λ n → hG _ _ (ch n))
  where
  ch : (n : ℕ) → RX (iter s x₀ n) (iter s′ x₀ n)
  ch zero    = r₀
  ch (suc n) = hs _ _ (ch n)
```

## 折叠不低于起点

对一切树, 一切底, 无前提.

```agda
cb : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (c : Ch s) (x : Tr (nd s h)) → Base (h c)
cb s h o B c x i u = ψ (nd s h) o B i (inc c u) (B i (inc c u)) x

infl : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ) {a : Tr j}
     → Le j a (proj₁ β) → Le j a (proj₁ (ψ ℓ o B j w β x))
infl ℓ o B j w β zero      d = d
infl ℓ o B j w β (suc x)   d = ≼l 0 (infl ℓ o B j w β x d)
infl ℓ o B j w β (lim f a) d = ≼l 0 (infl ℓ o B j w β (f 0) d)
infl ℓ o B j w β (Ω p g)   d = node≼ʳ (kp ℓ o p w) _ _ (infl ℓ o B j w β (g (fromBr ℓ p zero)) d)
infl (nd s h) o B _ self β (up x c y e) d =
  ≼Up (h c) (down stop c) (ψ (nd s h) o B _ self β x) y (infl (nd s h) o B _ self β x d)
infl (nd s h) o B j (inu ws) β (up x c y e) d =
  infl (h c) (proj₂ o c) (cb s h o B c x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) y (infl (nd s h) o B j (inu ws) β x d)
infl (nd (sΩ k) h) o B j (ink v) β (up x c y e) d =
  infl (h c) (proj₂ o c) (cb (sΩ k) h o B c x) j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (ink v) β x) y
       (infl (nd (sΩ k) h) o B j (ink v) β x d)
infl (nd sS h) o B j (inc c′ v) β (up x c y e) d =
  infl (h c) (proj₂ o c) (cb sS h o B c x) j v (ψ (nd sS h) o B j (inc c′ v) β x) y (infl (nd sS h) o B j (inc c′ v) β x d)
infl (nd sL g) o B j (inc n v) β (up x m y e) {a} d =
  cW-ind (λ Z → Le j a (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → infl (g n) (proj₂ o n) (cb sL g o B n x) j v (ψ (nd sL g) o B j (inc n v) β x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (infl (nd sL g) o B j (inc n v) β x d))
    (λ u → infl (g m) (proj₂ o m) (cb sL g o B m x) j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) y
             (infl (nd sL g) o B j (inc n v) β x d))
infl (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) d = ≼+ (infl (nd (sΩ k) h) o B j (inc c′ v) β x d) _
```

## 折叠保持关系

先是不看层号形状的各行 (零, 后继, ℕ 极限, 结点), 再是嵌入的各行, 与 `ψ` 逐行对应. 孩子的底由本层的 `fl` 给出相关; 分支侧一行 (Ω 形状, 经指定孩子的路径) 用默认底, 由 `Dflt` 给出自相关.

```agda
fl : (ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B B′ : Base ℓ) → B ⊴ B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j)
   → Le j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′
   → Le j (proj₁ (ψ ℓ o B j w β x)) (proj₁ (ψ ℓ o B′ j w β′ x′))
fl ℓ o D B B′ hB j w β β′ hβ {x′ = x′} z≼ = infl ℓ o B′ j w β′ x′ hβ
fl ℓ o D B B′ hB j w β β′ hβ (s≼s d)  = next≼ _ _ (fl ℓ o D B B′ hB j w β β′ hβ d)
fl ℓ o D B B′ hB j w β β′ hβ (≼s d)   = ≼l 0 (fl ℓ o D B B′ hB j w β β′ hβ d)
fl ℓ o D B B′ hB j w β β′ hβ (≼l n d) = ≼l n (fl ℓ o D B B′ hB j w β β′ hβ d)
fl ℓ o D B B′ hB j w β β′ hβ (l≼ h)   = l≼ (λ n → fl ℓ o D B B′ hB j w β β′ hβ (h n))
fl ℓ o D B B′ hB j w β β′ hβ (≼w {p = p} d) = node≼ʳ (kp ℓ o p w) _ _ (fl ℓ o D B B′ hB j w β β′ hβ d)
fl ℓ o D B B′ hB j w β β′ hβ (w≼w {p = p} {g = g} {g′ = g′} h) =
  node≼ (LB ℓ p) (kp ℓ o p w) (kpR ℓ o p w)
    (λ z → ψ ℓ o B j w β (g z)) (λ z → ψ ℓ o B′ j w β′ (g′ z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B′ (at ℓ p) (posW ℓ p) (B′ (at ℓ p) (posW ℓ p)) (g′ z))))
    (fromBr≼ ℓ p z≼)
    (λ z z′ r → fl ℓ o D B B′ hB j w β β′ hβ (h z z′ r))
    (λ z z′ r → fromBr≼ ℓ p (fl ℓ o D B B′ hB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (B′ (at ℓ p) (posW ℓ p))
                               (hB (at ℓ p) (posW ℓ p) (posW-pr ℓ p)) (h z z′ r)))
-- 右边多一层嵌入
fl (nd s h) o D B B′ hB _ self β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  ≼Up (h c) (down stop c) (ψ (nd s h) o B′ _ self β′ x) y (fl (nd s h) o D B B′ hB _ self β β′ hβ d)
fl (nd s h) o D B B′ hB j (inu ws) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  infl (h c) (proj₂ o c) (cb s h o B′ c x) j (ws c) (ψ (nd s h) o B′ j (inu ws) β′ x) y
       (fl (nd s h) o D B B′ hB j (inu ws) β β′ hβ d)
fl (nd (sΩ k) h) o D B B′ hB j (ink v) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  infl (h c) (proj₂ o c) (cb (sΩ k) h o B′ c x) j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B′ j (ink v) β′ x) y
       (fl (nd (sΩ k) h) o D B B′ hB j (ink v) β β′ hβ d)
fl (nd sS h) o D B B′ hB j (inc c′ v) β β′ hβ (≼u {x = x} {c = c} {y = y} d) =
  infl (h c) (proj₂ o c) (cb sS h o B′ c x) j v (ψ (nd sS h) o B′ j (inc c′ v) β′ x) y
       (fl (nd sS h) o D B B′ hB j (inc c′ v) β β′ hβ d)
fl (nd sL g) o D B B′ hB j (inc n v) β β′ hβ {x = a} (≼u {x = x} {c = m} {y = y} {e = e} d) =
  cW-ind (λ Z → Le j (proj₁ (ψ (nd sL g) o B j (inc n v) β a)) (proj₁ Z)) (way g (proj₁ o) m n)
    (λ u → infl (g n) (proj₂ o n) (cb sL g o B′ n x) j v (ψ (nd sL g) o B′ j (inc n v) β′ x)
             (proj₁ (emb (g n) (proj₂ o n) u (y , e))) (fl (nd sL g) o D B B′ hB j (inc n v) β β′ hβ d))
    (λ u → infl (g m) (proj₂ o m) (cb sL g o B′ m x) j (v ∙ u) (ψ (nd sL g) o B′ j (inc n v) β′ x) y
             (fl (nd sL g) o D B B′ hB j (inc n v) β β′ hβ d))
fl (nd (sΩ k) h) o D B B′ hB j (inc c′ v) β β′ hβ (≼u d) = ≼+ (fl (nd (sΩ k) h) o D B B′ hB j (inc c′ v) β β′ hβ d) _
-- 两边都是同一个孩子的嵌入
fl (nd s h) o D B B′ hB _ self β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  Up≼ (h c) (down stop c) (ψ (nd s h) o B _ self β x) (ψ (nd s h) o B′ _ self β′ x′) (fl (nd s h) o D B B′ hB _ self β β′ hβ dx) dy
fl (nd s h) o D B B′ hB j (inu ws) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (h c) (proj₂ o c) (proj₂ D c) (cb s h o B c x) (cb s h o B′ c x′)
     (λ i u _ → fl (nd s h) o D B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j (ws c) (ψ (nd s h) o B j (inu ws) β x) (ψ (nd s h) o B′ j (inu ws) β′ x′)
     (fl (nd s h) o D B B′ hB j (inu ws) β β′ hβ dx) dy
fl (nd (sΩ k) h) o D B B′ hB j (ink v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (h c) (proj₂ o c) (proj₂ D c) (cb (sΩ k) h o B c x) (cb (sΩ k) h o B′ c x′)
     (λ i u _ → fl (nd (sΩ k) h) o D B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (ink v) β x) (ψ (nd (sΩ k) h) o B′ j (ink v) β′ x′)
     (fl (nd (sΩ k) h) o D B B′ hB j (ink v) β β′ hβ dx) dy
fl (nd sS h) o D B B′ hB j (inc c′ v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = c} dx dy) =
  fl (h c) (proj₂ o c) (proj₂ D c) (cb sS h o B c x) (cb sS h o B′ c x′)
     (λ i u _ → fl (nd sS h) o D B B′ hB i (inc c u) (B i (inc c u)) (B′ i (inc c u)) (hB i (inc c u) tt) dx)
     j v (ψ (nd sS h) o B j (inc c′ v) β x) (ψ (nd sS h) o B′ j (inc c′ v) β′ x′)
     (fl (nd sS h) o D B B′ hB j (inc c′ v) β β′ hβ dx) dy
fl (nd sL g) o D B B′ hB j (inc n v) β β′ hβ (u≼u {x = x} {x′ = x′} {c = m} {y = y} {y′ = y′} {e = e} {e′ = e′} dx dy) =
  cW-ind₂ (λ Z Z′ → Le j (proj₁ Z) (proj₁ Z′)) (way g (proj₁ o) m n)
    (λ u → fl (g n) (proj₂ o n) (proj₂ D n) (cb sL g o B n x) (cb sL g o B′ n x′)
             (λ i u′ _ → fl (nd sL g) o D B B′ hB i (inc n u′) (B i (inc n u′)) (B′ i (inc n u′)) (hB i (inc n u′) tt) dx)
             j v (ψ (nd sL g) o B j (inc n v) β x) (ψ (nd sL g) o B′ j (inc n v) β′ x′)
             (fl (nd sL g) o D B B′ hB j (inc n v) β β′ hβ dx)
             (emb≼ (g n) (proj₂ o n) u {y = y , e} {y′ = y′ , e′} dy))
    (λ u → fl (g m) (proj₂ o m) (proj₂ D m) (cb sL g o B m x) (cb sL g o B′ m x′)
             (λ i u′ _ → fl (nd sL g) o D B B′ hB i (inc m u′) (B i (inc m u′)) (B′ i (inc m u′)) (hB i (inc m u′) tt) dx)
             j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) (ψ (nd sL g) o B′ j (inc n v) β′ x′)
             (fl (nd sL g) o D B B′ hB j (inc n v) β β′ hβ dx) dy)
fl (nd (sΩ k) h) o D B B′ hB j (inc c′ v) β β′ hβ (u≼u {c = c} dx dy) =
  +≼ (fl (nd (sΩ k) h) o D B B′ hB j (inc c′ v) β β′ hβ dx)
     (ι≼ j (fl (h c) (proj₂ o c) (proj₂ D c) (B₀ (h c)) (B₀ (h c)) (proj₁ D c) zero (z≤ (h c)) (Ωt zero) (Ωt zero) (s≼s z≼) dy))
```

## 前提的实例, 规范域的封闭

```agda
B₀⊴ : (ℓ : L) → ((i : L) (u : i ≤ ℓ) → Pr u → NoΩ i) → B₀ ℓ ⊴ B₀ ℓ
B₀⊴ ℓ ν i u pr = Ωt≼ i (ν i u pr)

Dflt-noΩ : (ℓ : L) → NoΩ ℓ → Dflt ℓ
Dflt-noΩ zero      _ = tt
Dflt-noΩ (nd sS h) ν = tt , λ _ → Dflt-noΩ (h tt) ν
Dflt-noΩ (nd sL g) ν = tt , λ n → Dflt-noΩ (g n) (ν n)

Dflt-tw1 : Dflt (tw 1)
Dflt-tw1 = (λ c → B₀⊴ (zero ⊕ ↑ zero c) (λ i u _ → NoΩ≤ u (NoΩ↑ c))) , λ c → Dflt-noΩ (zero ⊕ ↑ zero c) (NoΩ↑ c)

B₀⊴-noΩ : (ℓ : L) → NoΩ ℓ → B₀ ℓ ⊴ B₀ ℓ
B₀⊴-noΩ ℓ ν = B₀⊴ ℓ (λ i u _ → NoΩ≤ u ν)

pr-tw1 : (i : L) (u : i ≤ tw 1) → Pr u → NoΩ i
pr-tw1 i (inc c u) _ = NoΩ≤ u (NoΩ↑ c)
pr-tw1 i (inu us)  _ = NoΩ≤ (us zero) tt
pr-tw1 i (ink u)   _ = NoΩ≤ u tt

B₀⊴-tw1 : B₀ (tw 1) ⊴ B₀ (tw 1)
B₀⊴-tw1 = B₀⊴ (tw 1) pr-tw1

-- 前提在塔第 2 项不成立: 孩子 `suc zero` 的层里有一条非 `self` 的路径通到 `tw 1`, 要 `Ωt (tw 1)` 自相关
Dflt-tw2-not : Dflt (tw 2) → ⊥
Dflt-tw2-not D = β-not (proj₁ D (suc zero) (tw 1) (inc tt self) tt)

can-fold : (ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B : Base ℓ) → B ⊴ B → (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) → Can j (proj₁ β)
         → (x : Tr ℓ) → Can ℓ x → Can j (proj₁ (ψ ℓ o B j w β x))
can-fold ℓ o D B hB j w β hβ x hx = fl ℓ o D B B hB j w β β hβ hx
```

## 第 1 层

层号 1 是 `nd sS (λ _ → zero)`; 证据与前提都是平凡的. 第 1 层的 Ω 树与默认底在规范域.

```agda
L1 : L
L1 = nd sS (λ _ → zero)

fl₁ : (B B′ : Base L1) → B ⊴ B′ → (j : L) (w : j ≤ L1) (β β′ : Tr⁺ j) → Le j (proj₁ β) (proj₁ β′)
    → {x x′ : Tr L1} → Le L1 x x′
    → Le j (proj₁ (ψ L1 (tt , λ _ → tt) B j w β x)) (proj₁ (ψ L1 (tt , λ _ → tt) B′ j w β′ x′))
fl₁ = fl L1 (tt , λ _ → tt) (tt , λ _ → tt)

Ω₁-can : Can L1 (proj₁ (Ωt L1))
Ω₁-can = Ωt≼ L1 tt

B₀⊴₁ : B₀ L1 ⊴ B₀ L1
B₀⊴₁ = B₀⊴-noΩ L1 tt
```
