# 取尾部的上确界构造子 (原型): 验收, 形状测试, 与否定的关系

> 编译定理: `YiRWCheck` 的各行律在新块上逐条仍成立 (`up` 的各行未动, `J2-b` 仍是回退); `sup` 的四行 (`sup-self`, `sup-u`, `sup-k`, `sup-tail`, `sup-fb`); 塔上分支侧取尾部无前提 (`sup-tail-tw`).
> 有限测试 (形状, `refl`): 塔第 1 项上孩子 2 在 x = Ω 树之后的第 1, 2 层的底是结点, 各支是 x 的尾项 `Ωt (h (2 + z))` 朝该层的折叠 (`b1-form`, `b2-form`), 对任意孩子树族也是 (`top-any`).
> 与否定的关系 (编译): `up` 行在 x 是零时对指定孩子是常值 (`up-const`, `up-no-sep`); `sup` 行在下一站形如 `w ∙ lift` 的指定孩子路径上对一切 c′ 头部都是 ℕ 极限 (`sup-head`). 不否定什么; 值没有证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSupCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import OCF.Lean.YiSupBlock
open import OCF.Lean.YiSupOps
open import OCF.Lean.YiSupPath
open import OCF.Lean.YiSupFold
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
  ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (v ∙ khΩ o c) (ψ (nd (sΩ k) h) o B j (ink v) β x) y
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
  kp-z (nd (sΩ k) h) ((_ , kh , _) , oc) (inj₂ (c , t)) (ink v)   = kp⁼-z (h c) (oc c) t (v ∙ kh c)
  kp-z (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼-z (h c) (oc c) t v
  kp-z (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind (λ Z → Z ≡ nothing) (way g r m n) (λ u → cong (mapK _ _) (kp⁼-z (g n) (oc n) (psh u t) v))
                                             (λ u → kp⁼-z (g m) (oc m) t (v ∙ u))
  kp-z (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = refl
  kp-z (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼-z k ok t v
  kp-z (nd (sΩ k) h) ((_ , kh , _) , oc) (inj₁ t)       (inc c v) = cong (mapK _ _) (kp⁼-z (h c) (oc c) (psh (kh c) t) v)
  kp-z (nd (sΩ k) h) ((_ , kh , _) , oc) (inj₁ t)       (inu vs)  =
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
Ok-Nx a oa = (oa , (λ c → lift a (↑ a c)) , inj₂ (λ c z → wk (⊕⊑ a (↑+ a c z)))) , λ c → Ok⊕ a (↑ a c) oa (OkO↑ a a oa self c)

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

## `sup` 的各行

`sup q x Y e` 读作 x 加上孩子树族 Y 的上确界. 自身行: 顶槽位的结点, 逐孩子上折. 一致路径与下标层侧: 顶槽位的结点行, 第 z 支是 `Y z` 在孩子 z 里的折叠 (底是 x 经孩子 z 的折叠 `cb`). 反馈 `fbS` 把孩子树折到下标层 k.

```agda
top : ∀ {k h} → Pos (nd (sΩ k) h)
top = inj₁ (inj₁ tt)

fbS : ∀ {k h} (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (x : Tr (nd (sΩ k) h)) (Y : (c : Tr k) → Tr (h c)) → Tr k → Tr k
fbS {k} {h} o B x Y z = proj₁ (ψ (h z) (proj₂ o z) (cb o B z x) k (khΩ o z) (ψ (nd (sΩ k) h) o B k (ink self) (B k (ink self)) x) (Y z))

sup-self : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (β : Tr⁺ (nd (sΩ k) h)) (x : Tr (nd (sΩ k) h))
  (Y : (c : Tr k) → Tr (h c)) (e : (c : Tr k) → h c ⊢ zero ◃ Y c)
  → ψ (nd (sΩ k) h) o B (nd (sΩ k) h) self β (sup tt x Y e)
  ≡ Ω⁺ top (λ c → Up (h c) (down stop c) (ψ (nd (sΩ k) h) o B (nd (sΩ k) h) self β x) (Y c))
sup-self k h o B β x Y e = refl

sup-u : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (ws : (c : Tr k) → j ≤ h c)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (Y : (c : Tr k) → Tr (h c)) (e : (c : Tr k) → h c ⊢ zero ◃ Y c)
  → ψ (nd (sΩ k) h) o B j (inu ws) β (sup tt x Y e)
  ≡ node⁺ (kp (nd (sΩ k) h) o top (inu ws))
      (λ z → ψ (h z) (proj₂ o z) (cb o B z x) j (ws z) (ψ (nd (sΩ k) h) o B j (inu ws) β x) (Y z)) (fbS o B x Y)
sup-u k h o B j ws β x Y e = refl

sup-k : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (v : j ≤ k)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (Y : (c : Tr k) → Tr (h c)) (e : (c : Tr k) → h c ⊢ zero ◃ Y c)
  → ψ (nd (sΩ k) h) o B j (ink v) β (sup tt x Y e)
  ≡ node⁺ (kp (nd (sΩ k) h) o top (ink v))
      (λ z → ψ (h z) (proj₂ o z) (cb o B z x) j (v ∙ khΩ o z) (ψ (nd (sΩ k) h) o B j (ink v) β x) (Y z)) (fbS o B x Y)
sup-k k h o B j v β x Y e = refl
```

分支侧 (指定孩子 c′, 路径 v : j ≤ h c′). 层号带尾部路径 tl 时: 顶槽位的结点行, 第 z 支是尾项 `Y (c′ + z)` 在孩子 `c′ + z` 里的折叠, 路径 `v ∙ tl c′ z`, 底是 x 经孩子 `c′ + z` 的折叠. 右边只在 `c′ + z` 处读 Y, 不比较 c′ 与任何孩子下标. 不带时回退 (`fbN` 的链只读 Y 的可数折叠).

```agda
sup-tail : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (Y : (c : Tr k) → Tr (h c)) (e : (c : Tr k) → h c ⊢ zero ◃ Y c)
  (tl : (c z : Tr k) → h c ≤ h (c + z)) → tlΩ o ≡ inj₂ tl
  → ψ (nd (sΩ k) h) o B j (inc c′ v) β (sup tt x Y e)
  ≡ node⁺ (kp (nd (sΩ k) h) o top (inc c′ v))
      (λ z → ψ (h (c′ + z)) (proj₂ o (c′ + z)) (cb o B (c′ + z) x) j (v ∙ tl c′ z) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (Y (c′ + z)))
      (λ z → fbS o B x Y (c′ + z))
sup-tail k h o B j c′ v β x Y e tl eq rewrite eq = refl

fbN : ∀ {k h} (o : Ok (nd (sΩ k) h)) (Y : (c : Tr k) → Tr (h c)) → ℕ → Tr k
fbN {k} {h} o Y = iter (λ z → proj₁ (ψ (h z) (proj₂ o z) (B₀ (h z)) k (khΩ o z) (Ωt k) (Y z))) zero

sup-fb : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (Y : (c : Tr k) → Tr (h c)) (e : (c : Tr k) → h c ⊢ zero ◃ Y c)
  → tlΩ o ≡ inj₁ tt
  → ψ (nd (sΩ k) h) o B j (inc c′ v) β (sup tt x Y e)
  ≡ ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ limc⁺ (λ n → ψ₀ (h (fbN o Y n)) (proj₂ o (fbN o Y n)) (Y (fbN o Y n)))
sup-fb k h o B j c′ v β x Y e eq rewrite eq = refl
```

下一站 `Nx a` (塔第 n+1 项) 带尾部路径, 所以分支侧取尾部无前提; 读回层号 (`Ok⊕`) 不带.

```agda
tlN : (a : L) (c z : Tr a) → a ⊕ ↑ a c ≤ a ⊕ ↑ a (c + z)
tlN a c z = wk (⊕⊑ a (↑+ a c z))

tl-Nx : (a : L) (oa : Ok a) → tlΩ (Ok-Nx a oa) ≡ inj₂ (tlN a)
tl-Nx a oa = refl

tl-tw : (n : ℕ) → tlΩ (Ok-tw (suc n)) ≡ inj₂ (tlN (tw n))
tl-tw n = refl

tl-⊕ : (a : L) (k : L) (h : Tr k → L) (oa : Ok a) (ob : OkO a (nd (sΩ k) h)) → tlΩ (Ok⊕ a (nd (sΩ k) h) oa ob) ≡ inj₁ tt
tl-⊕ a k h oa ob = refl

sup-tail-tw : (n : ℕ) (B : Base (tw (suc n))) (j : L) (c′ : Tr (tw n)) (v : j ≤ tw n ⊕ ↑ (tw n) c′)
  (β : Tr⁺ j) (x : Tr (tw (suc n))) (Y : (c : Tr (tw n)) → Tr (tw n ⊕ ↑ (tw n) c)) (e : (c : Tr (tw n)) → (tw n ⊕ ↑ (tw n) c) ⊢ zero ◃ Y c)
  → ψ (tw (suc n)) (Ok-tw (suc n)) B j (inc c′ v) β (sup tt x Y e)
  ≡ node⁺ (kp (tw (suc n)) (Ok-tw (suc n)) top (inc c′ v))
      (λ z → ψ (tw n ⊕ ↑ (tw n) (c′ + z)) (proj₂ (Ok-tw (suc n)) (c′ + z)) (cb (Ok-tw (suc n)) B (c′ + z) x) j (v ∙ tlN (tw n) c′ z)
               (ψ (tw (suc n)) (Ok-tw (suc n)) B j (inc c′ v) β x) (Y (c′ + z)))
      (λ z → fbS (Ok-tw (suc n)) B x Y (c′ + z))
sup-tail-tw n B j c′ v β x Y e = refl
```

规范的 Ω 树用新构造子; 序 `◃p` 的单调是 `YiSupFold.mono` 的四行 (第一位置合法性: 前驱只取 x).

```agda
Ωt-sup : (k : L) (h : Tr k → L) → proj₁ (Ωt (nd (sΩ k) h)) ≡ sup tt zero (λ c → proj₁ (Ωt (h c))) (λ c → proj₂ (Ωt (h c)))
Ωt-sup k h = refl

sup-mono : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (w : j ≤ nd (sΩ k) h) (β : Tr⁺ j)
  (x : Tr (nd (sΩ k) h)) (Y : (c : Tr k) → Tr (h c)) (e : (c : Tr k) → h c ⊢ zero ◃ Y c)
  → j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j w β x) ◃ proj₁ (ψ (nd (sΩ k) h) o B j w β (sup tt x Y e))
sup-mono k h o B j w β x Y e = mono (nd (sΩ k) h) o B j w β (◃p tt x Y e)
```

## 形状测试 (有限测试): 最小见证上孩子的底

塔第 1 项 `tw 1`, 孩子 2, 左边 x = `βΩ` (本层的 Ω 树, 读作 Ω_Ω). 对照 R15 的 `b1-form`, `b2-form` (旧块上是 `Ω_j + Ω(G)`, 各支只含可数加项): 这里第 2, 1 层的底是结点, 第 z 支是 x 的尾项 `Ωt (h₁ (2 + z))` 朝该层的折叠.

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

o¹ : Ok (tw 1)
o¹ = Ok-tw 1

two : Tr zero
two = suc (suc zero)

L1 L2 : L
L1 = nd sS λ _ → zero
L2 = nd sS λ _ → L1

L2-eq : h₁ two ≡ L2
L2-eq = refl

βΩ : Tr (tw 1)
βΩ = proj₁ (Ωt (tw 1))

BW : Base L2
BW = cb o¹ (B₀ (tw 1)) two βΩ

q2 : Pos L2
q2 = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))

q1 : Pos L1
q1 = inj₂ (tt , inj₁ tt)

b2-form : proj₁ (BW L2 self)
  ≡ Ω q2 (λ z → proj₁ (ψ (h₁ (two + z)) (proj₂ o¹ (two + z)) (B₀ (h₁ (two + z))) L2 (self ∙ tlN zero two z) (Ωt L2) (proj₁ (Ωt (h₁ (two + z))))))
b2-form = refl

b1-form : proj₁ (BW L1 (inc tt self))
  ≡ Ω q1 (λ z → proj₁ (ψ (h₁ (two + z)) (proj₂ o¹ (two + z)) (B₀ (h₁ (two + z))) L1 (inc tt self ∙ tlN zero two z) (Ωt L1) (proj₁ (Ωt (h₁ (two + z))))))
b1-form = refl
```

第 1 层的底的第一支 (z = 0) 是 Ω₂ 朝第 1 层的折叠, 头部是 ℕ 极限 (对角链); 对任意孩子树族 Y (左边是 `sup tt zero Y e`), 第 1 层的底的各支是 `Y (2 + z)` 朝第 1 层的折叠 (对照 R15 的 `top-any`: 旧块上只见各 `Y c` 的可数折叠).

```agda
b1-first : isLim (proj₁ (ψ (h₁ two) (proj₂ o¹ two) (B₀ (h₁ two)) L1 (inc tt self ∙ tlN zero two zero) (Ωt L1) (proj₁ (Ωt (h₁ two)))))
b1-first = tt

top-any : (Y : (c : Tr zero) → Tr (h₁ c)) (e : (c : Tr zero) → h₁ c ⊢ zero ◃ Y c)
  → proj₁ (cb o¹ (B₀ (tw 1)) two (sup tt zero Y e) L1 (inc tt self))
  ≡ Ω q1 (λ z → proj₁ (ψ (h₁ (two + z)) (proj₂ o¹ (two + z)) (B₀ (h₁ (two + z))) L1 (inc tt self ∙ tlN zero two z) (Ωt L1) (Y (two + z))))
top-any Y e = refl
```

最小见证 `up βΩ two y` (y 取 `Ωt L2` 时读作 Ω_Ω+Ω₂): 它的第 0 层折叠是孩子 2 上以 `BW` 为底的折叠 (对照 R15 的 `all-y`).

```agda
wit : (y : Tr L2) (e : L2 ⊢ zero ◃ y)
  → ψ₀ (tw 1) o¹ (up βΩ two y e) ≡ ψ L2 (proj₂ o¹ two) BW zero (z≤ L2) (ψ₀ (tw 1) o¹ βΩ) y
wit y e = refl

witᶜ : Tr zero
witᶜ = proj₁ (ψ₀ (tw 1) o¹ (up βΩ two (proj₁ (Ωt L2)) (proj₂ (Ωt L2))))

witᶜ-lim : isLim witᶜ
witᶜ-lim = tt
```

## 与已编译的否定的关系

`up` 行 (未动): 分支侧对一切 c′, c 回退 (`J2-b`), 所以不主张 `YiAbsFrame.Hand`; x 是零时输出与指定孩子及其路径无关, 任何布尔观察对 c′ 是常值, `branch→sep` 的 `on` 与 `off` 在 `up zero c y e` 上不能同时成立.

```agda
up-const : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (β : Tr⁺ j)
  (c′ c″ : Tr k) (v′ : j ≤ h c′) (v″ : j ≤ h c″) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd (sΩ k) h) o B j (inc c′ v′) β (up zero c y e) ≡ ψ (nd (sΩ k) h) o B j (inc c″ v″) β (up zero c y e)
up-const k h o B j β c′ c″ v′ v″ c y e = refl

up-no-sep : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (β : Tr⁺ j) (hd : Tr j → Bool)
  (w : (c′ : Tr k) → j ≤ h c′) (c₁ c′ : Tr k) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → hd (proj₁ (ψ (nd (sΩ k) h) o B j (inc c₁ (w c₁)) β (up zero c y e))) ≡ true
  → hd (proj₁ (ψ (nd (sΩ k) h) o B j (inc c′ (w c′)) β (up zero c y e))) ≡ false → ⊥
up-no-sep k h o B j β hd w c₁ c′ c y e on off with trans (sym on) off
... | ()
```

`sup` 行不新增保留判定 (复用 `kp`, 槽位由路径末端算出), 派发只看层号的证据 `tlΩ o` (对孩子是常值), 不看孩子下标. 在下一站 `Nx a` 上, 目标 j ≤ a 经指定孩子 c′ 的路径 `w ∙ lift` (`YiAltCheck.no-sep` 的那一族) 时, 顶槽位对一切 c′ 都不保留, 输出的头部对一切 c′ 都是 ℕ 极限.

```agda
qOf : ∀ {j X x₀} → Keep j X x₀ → Maybe (Pos j)
qOf (just (q , _)) = just q
qOf nothing        = nothing

qOf-mapK : ∀ {j X Y x₀ y₀} (f : X → Y) (e : f x₀ ≡ y₀) (m : Keep j X x₀) → qOf (mapK f e m) ≡ qOf m
qOf-mapK f e (just _) = refl
qOf-mapK f e nothing  = refl

lemL : (a b : L) (oa : Ok a) (ob : OkO a b) (t : Pos⁼ a) {j : L} (u : j ≤ a)
  → qOf (kp⁼ (a ⊕ b) (Ok⊕ a b oa ob) (psh (lift a b) t) (u ∙ lift a b)) ≡ qOf (kp⁼ a oa t u)
lemL a zero     oa ob        t u = refl
lemL a (nd s h) oa (os , ob) t u = lemL a (h (c₀ s)) oa (ob (c₀ s)) t u

wL : (a : L) {j : L} → j ≤ a → (c′ : Tr a) → j ≤ a ⊕ ↑ a c′
wL a w c′ = w ∙ lift a (↑ a c′)

top-drop : (a : L) (oa : Ok a) (j : L) (w : j ≤ a) (c′ : Tr a)
  → qOf (kp (Nx a) (Ok-Nx a oa) top (inc c′ (wL a w c′))) ≡ nothing
top-drop a oa j w c′ =
  trans (qOf-mapK _ _ (kp⁼ (a ⊕ ↑ a c′) (Ok⊕ a (↑ a c′) oa (OkO↑ a a oa self c′)) (psh (lift a (↑ a c′)) (inj₁ tt)) (wL a w c′)))
        (lemL a (↑ a c′) oa (OkO↑ a a oa self c′) (inj₁ tt) w)

nodeLim : ∀ {j X x₀} (m : Keep j X x₀) (G : X → Tr⁺ j) (s : X → X) → qOf m ≡ nothing → isLim (proj₁ (node⁺ m G s))
nodeLim nothing G s _ = tt

sup-head : (a : L) (oa : Ok a) (B : Base (Nx a)) (j : L) (w : j ≤ a) (β : Tr⁺ j) (c′ : Tr a)
  (x : Tr (Nx a)) (Y : (c : Tr a) → Tr (a ⊕ ↑ a c)) (e : (c : Tr a) → (a ⊕ ↑ a c) ⊢ zero ◃ Y c)
  → isLim (proj₁ (ψ (Nx a) (Ok-Nx a oa) B j (inc c′ (wL a w c′)) β (sup tt x Y e)))
sup-head a oa B j w β c′ x Y e = nodeLim (kp (Nx a) (Ok-Nx a oa) top (inc c′ (wL a w c′))) _ _ (top-drop a oa j w c′)
```
