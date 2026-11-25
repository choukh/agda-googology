# 从头重写: 验收

> 编译定理: 嵌入一致的各行 (除分支侧回退那一行, 那一行只陈述它的形状), 自身行, 结点行, 到第 0 层时结点不保留 (`kp-z`), ℕ 极限比较的两条, 下一站 k 侧第一个孩子的保留 (`kstep`); 非零是折叠值的类型, 单调是 `YiRWFold.mono`.
> 有限测试: 塔第 1 项的证据给 ω+1 那一层的相邻路径 (`tw1-adj`), 孩子 2 的底是结点 (`bω-tw`), 结点经两条路径都保留 (`cω-A`, `cω-B`); 闭项的根是 ℕ 极限.
> 不否定什么. 对照: F2 的 `YiLegCheck`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRWCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
```

## 嵌入一致

孩子 c 的底 `cb`: x 对同一目标经孩子 c 的折叠.

```agda
cb : ∀ {s h} (o : Ok (nd s h)) (B : Base (nd s h)) (c : Ch s) (x : Tr (nd s h)) → Base (h c)
cb {s} {h} o B c x i u = ψ (nd s h) o B i (inc c u) (B i (inc c u)) x

J2-u : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (j : L) (ws : (c : Ch s) → j ≤ h c)
  (β : Tr⁺ j) (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd s h) o B j (inu ws) β (up x c y e) ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) y
J2-u s h o B j ws β x c y e = refl

J2⊥ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ zero) (x : Tr (nd s h))
  (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd s h) o B zero (z≤ (nd s h)) β (up x c y e)
  ≡ ψ (h c) (proj₂ o c) (cb o B c x) zero (z≤ (h c)) (ψ (nd s h) o B zero (z≤ (nd s h)) β x) y
J2⊥ s h o B β x c y e = refl

J2-k : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (v : j ≤ k)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd (sΩ k) h) o B j (ink v) β (up x c y e)
  ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (ink v) β x) y
J2-k k h o B j v β x c y e = refl

J2-s : (h : ⊤ → L) (o : Ok (nd sS h)) (B : Base (nd sS h)) (j : L) (v : j ≤ h tt)
  (β : Tr⁺ j) (x : Tr (nd sS h)) (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y)
  → ψ (nd sS h) o B j (inc tt v) β (up x tt y e) ≡ ψ (h tt) (proj₂ o tt) (cb o B tt x) j v (ψ (nd sS h) o B j (inc tt v) β x) y
J2-s h o B j v β x y e = refl

way-refl : (g : ℕ → L) (r : (n : ℕ) → g n ≤ g (suc n)) (n : ℕ) → way g r n n ≡ inj₂ self
way-refl g r zero    = refl
way-refl g r (suc n) = way-refl (λ i → g (suc i)) (λ i → r (suc i)) n

J2-lim : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (n : ℕ) (j : L) (v : j ≤ g n)
  (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g n)) (e : g n ⊢ zero ◃ y)
  → ψ (nd sL g) o B j (inc n v) β (up x n y e) ≡ ψ (g n) (proj₂ o n) (cb o B n x) j v (ψ (nd sL g) o B j (inc n v) β x) y
J2-lim g o B n j v β x y e rewrite way-refl g (proj₁ o) n = refl

J2-lim-fwd : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (m n : ℕ) (j : L) (v : j ≤ g n)
  (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (u : g m ≤ g n) → way g (proj₁ o) m n ≡ inj₁ u
  → ψ (nd sL g) o B j (inc n v) β (up x m y e)
  ≡ ψ (g n) (proj₂ o n) (cb o B n x) j v (ψ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e)))
J2-lim-fwd g o B m n j v β x y e u eq rewrite eq = refl

J2-lim-bwd : (g : ℕ → L) (o : Ok (nd sL g)) (B : Base (nd sL g)) (m n : ℕ) (j : L) (v : j ≤ g n)
  (β : Tr⁺ j) (x : Tr (nd sL g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (u : g n ≤ g m) → way g (proj₁ o) m n ≡ inj₂ u
  → ψ (nd sL g) o B j (inc n v) β (up x m y e) ≡ ψ (g m) (proj₂ o m) (cb o B m x) j (v ∙ u) (ψ (nd sL g) o B j (inc n v) β x) y
J2-lim-bwd g o B m n j v β x y e u eq rewrite eq = refl
```

分支侧 (Ω 形状, 经指定孩子 c′ 的路径, 嵌入在孩子 c): 回退到 x 的折叠加上孩子树对第 0 层的折叠 (只陈述形状). 自身行是上折.

```agda
J2-b : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
  ≡ ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ₀ (h c) (proj₂ o c) y
J2-b k h o B j c′ v β x c y e = refl

self-up : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ (nd s h)) (x : Tr (nd s h))
  (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd s h) o B (nd s h) self β (up x c y e) ≡ Up (h c) (down stop c) (ψ (nd s h) o B (nd s h) self β x) y
self-up s h o B β x c y e = refl
```

## 结点

结点行; 到第 0 层 (任何路径) 时保留判定总是 "不保留", 所以结点折成链的部分和极限.

```agda
step : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → Br ℓ p → Br ℓ p
step ℓ o B p g z = fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z)))

node : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ)
  → ψ ℓ o B j w β (Ω p g) ≡ node⁺ (kp ℓ o p w) (λ z → ψ ℓ o B j w β (g z)) (step ℓ o B p g)
node ℓ o B j w β p g = refl

mutual
  kp-z : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) (w : zero ≤ ℓ) → kp ℓ o p w ≡ nothing
  kp-z (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼-z (h c) (oc c) t (vs c)
  kp-z (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kp⁼-z (h c) (oc c) t (v ∙ kh c)
  kp-z (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼-z (h c) (oc c) t v
  kp-z (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind (λ Z → Z ≡ nothing) (way g r m n) (λ u → cong (mapK _ _) (kp⁼-z (g n) (oc n) (psh u t) v))
                                             (λ u → kp⁼-z (g m) (oc m) t (v ∙ u))
  kp-z (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = refl
  kp-z (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼-z k ok t v
  kp-z (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) = cong (mapK _ _) (kp⁼-z (h c) (oc c) (psh (kh c) t) v)
  kp-z (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
    cong (mapK _ _) (kp⁼-z (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kp⁼-z : (a : L) (o : Ok a) (t : Pos⁼ a) (w : zero ≤ a) → kp⁼ a o t w ≡ nothing
  kp⁼-z a o (inj₁ _) w = refl
  kp⁼-z a o (inj₂ p) w = kp-z a o p w

node⊥ : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (w : zero ≤ ℓ) (β : Tr⁺ zero) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ)
  → ψ ℓ o B zero w β (Ω p g) ≡ limc⁺ (λ n → ψ ℓ o B zero w β (g (iter (step ℓ o B p g) (fromBr ℓ p zero) n)))
node⊥ ℓ o B w β p g rewrite kp-z ℓ o p w = refl

kp-fwd : (g : ℕ → L) (o : Ok (nd sL g)) (m n : ℕ) (t : Pos⁼ (g m)) {j : L} (v : j ≤ g n) (u : g m ≤ g n)
  → way g (proj₁ o) m n ≡ inj₁ u
  → kp (nd sL g) o (inj₂ (m , t)) (inc n v) ≡ mapK (pshBr u t) (pshFirst u t) (kp⁼ (g n) (proj₂ o n) (psh u t) v)
kp-fwd g o m n t v u eq rewrite eq = refl

kp-bwd : (g : ℕ → L) (o : Ok (nd sL g)) (m n : ℕ) (t : Pos⁼ (g m)) {j : L} (v : j ≤ g n) (u : g n ≤ g m)
  → way g (proj₁ o) m n ≡ inj₂ u → kp (nd sL g) o (inj₂ (m , t)) (inc n v) ≡ kp⁼ (g m) (proj₂ o m) t (v ∙ u)
kp-bwd g o m n t v u eq rewrite eq = refl
```

下一站 `Nx a` (塔第 n+1 项是 `Nx (tw n)`, 证据逐字是 `Ok-Nx`): 折到下标层 a (路径 `ink self`) 时, 第一个孩子 (层号 a ⊕ ↑0, 即 a) 里的结点原样保留.

```agda
Nx : L → L
Nx a = nd (sΩ a) λ c → a ⊕ ↑ a c

Ok-Nx : (a : L) → Ok a → Ok (Nx a)
Ok-Nx a oa = (oa , λ c → lift a (↑ a c)) , λ c → Ok⊕ a (↑ a c) oa (OkO↑ a a oa self c)

tw-Nx : (n : ℕ) → tw (suc n) ≡ Nx (tw n)
tw-Nx n = refl

kstep : (a : L) (oa : Ok a) (B : Base (Nx a)) (β : Tr⁺ a) (x : Tr (Nx a)) (p : Pos a) (g : Br a p → Tr a)
  (e : a ⊢ zero ◃ Ω p g)
  → ψ (Nx a) (Ok-Nx a oa) B a (ink self) β (up x zero (Ω p g) e)
  ≡ Ω⁺ p (λ z → ψ a (proj₂ (Ok-Nx a oa) zero) (cb (Ok-Nx a oa) B zero x) a self (ψ (Nx a) (Ok-Nx a oa) B a (ink self) β x) (g z))
kstep a oa B β x p g e = refl
```

## 必带路线可满足

`YiLimCheck.no-req` 的反例 `lim (1,0,0,…)` 在这里不是树 (要交 1 ◃ 0); 塔第 n+1 项的每个孩子层都带证据 (对一切分支 c); Λ 的相邻路径是 `ink self`.

```agda
¬◃z : ∀ {ℓ} {x : Tr ℓ} → ℓ ⊢ x ◃ zero → ⊥
¬◃z (◃t d e) = ¬◃z e

no-bad : ∀ {ℓ} {x : Tr ℓ} → ℓ ⊢ suc x ◃ zero → ⊥
no-bad = ¬◃z

req-child : (n : ℕ) (c : Tr (tw n)) → Ok (tw n ⊕ ↑ (tw n) c)
req-child n c = proj₂ (Ok-tw (suc n)) c

adj-Λ : proj₁ Ok-Λ ≡ (λ n → ink self)
adj-Λ = refl
```

## 有限测试

塔第 1 项的孩子 `suc ω₀` 的层号是 ω+1 (`nd sS (λ _ → nd sL gω)`); 它的必带相邻路径由 `Ok-tw 1` 读出.

```agda
ω₀ : Tr zero
ω₀ = lim (iter suc zero) (λ n → ◃s)

gω : ℕ → L
gω n = zero ⊕ ↑ zero (iter suc zero n)

oω : Ok (nd sL gω)
oω = proj₂ (proj₂ (Ok-tw 1) (suc ω₀)) tt

tw1-adj : proj₁ oω ≡ (λ n → inc tt self)
tw1-adj = refl

tw1-way : way gω (proj₁ oω) 1 2 ≡ inj₁ (inc tt self)
tw1-way = refl

isΩ isLim : {ℓ : L} → Tr ℓ → Set
isΩ (Ω _ _) = ⊤
isΩ _       = ⊥
isLim (lim _ _) = ⊤
isLim _         = ⊥

one : L
one = nd sS λ _ → zero

preω : Tr (nd sL gω)
preω = up (up zero 0 (suc zero) ◃s) 1 (proj₁ (Ωt one)) (proj₂ (Ωt one))

bω-tw : isΩ (proj₁ (cb oω (B₀ _) 2 preω one (inc tt self)))
bω-tw = tt

nodeω : (Tr zero → Tr (nd sL gω)) → Tr (nd sL gω)
nodeω G = Ω (inj₂ (1 , inj₂ (inj₂ (tt , inj₁ tt)))) G

cω-A : (B : Base (nd sL gω)) (G : Tr zero → Tr (nd sL gω)) → isΩ (proj₁ (ψ (nd sL gω) oω B one (inc 1 self) (Ωt one) (nodeω G)))
cω-A B G = tt

cω-B : (B : Base (nd sL gω)) (G : Tr zero → Tr (nd sL gω))
  → isΩ (proj₁ (ψ (nd sL gω) oω B one (inc 2 (inc tt self)) (Ωt one) (nodeω G)))
cω-B B G = tt

EBOᶜ-lim : isLim EBOᶜ
EBOᶜ-lim = tt

tw1ᶜ-lim : isLim (twᶜ 1)
tw1ᶜ-lim = tt
```
