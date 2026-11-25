# 原型 (a): 验收

> 编译定理: 精简块的其余各行逐字保住 (`J2-u`, `J2⊥`, `J2-k`, `J2-s`, `J2-lim` 三条, `self-up`, `node`, `kp-z`, `node⊥`, `kstep`); 新的分支侧一行对一切 Ω 形状层号是同一个式子 (`J2-φ`), `φ` 的各行 (`φ-here`, `φ-via`, `φ-up`, `φ-node`); 非零是值的类型, 单调是 `YiCertFold.mono`.
> 有限测试 (`refl`): 塔第 1 项上孩子 two 在 x = Ω 树之后第 1, 2 层的底是保留的结点, 各支是左项该支的孩子树的 `φ` (`b1-form`, `b2-form`; 对任意孩子树族 `top-any`, 对 `up` 形左项 `up-any`); 闭项的根是 ℕ 极限.
> 不否定什么; 值没有定理. 判据的其余两项与否定的前提在 `YiCertNeg`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCertCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiCertPath
open import OCF.Lean.YiCertFold
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
  ≡ ψ (h c) (proj₂ o c) (cb o B c x) j (v ∙ kh o c) (ψ (nd (sΩ k) h) o B j (ink v) β x) y
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

分支侧 (Ω 形状, 经指定孩子 c′ 的路径, 嵌入在孩子 c): 对一切层号, 一切 c, c′ 是同一个式子. 锚是孩子 c′ 的层, 证据, 底与路径; 源是孩子 c 的层, 证据, 证书与底. 自身行是上折.

```agda
J2-φ : (k : L) (h : Tr k → L) (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) (j : L) (c′ : Tr k) (v : j ≤ h c′)
  (β : Tr⁺ j) (x : Tr (nd (sΩ k) h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e)
  ≡ φ (h c′) (proj₂ o c′) (cb o B c′ x) (kh o c′) j v (h c) (proj₂ o c) (proj₂ (proj₁ o) c) (cb o B c x)
      (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) y
J2-φ k h o B j c′ v β x c y e = refl

self-up : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (B : Base (nd s h)) (β : Tr⁺ (nd s h)) (x : Tr (nd s h))
  (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ (nd s h) o B (nd s h) self β (up x c y e) ≡ Up (h c) (down stop c) (ψ (nd s h) o B (nd s h) self β x) y
self-up s h o B β x c y e = refl
```

`φ` 的各行. 叶子 `here`: 树 (前面加一, 保证非零) 嵌进锚层, 按锚层正常折叠. 叶子 `via`: 先折到 k. 中间: 嵌入逐孩子下行, 底是源层自己的 "x 朝该层的折叠"; 结点按 `kpA`, 链在源层回灌.

```agda
module _ {k : L} (a : L) (oa : Ok a) (Ba : Base a) (kk : k ≤ a) (j : L) (v : j ≤ a) where

  φ-here : (ok : Ok k) (Bm : Base k) (β : Tr⁺ j) (y : Tr k)
    → φ a oa Ba kk j v k ok here Bm β y ≡ ψ a oa Ba j v β (proj₁ (emb a oa kk (s+ y)))
  φ-here ok Bm β y = refl

  φ-via : (m : L) (om : Ok m) (w : k ≤ m) (Bm : Base m) (β : Tr⁺ j) (y : Tr m)
    → φ a oa Ba kk j v m om (via w) Bm β y ≡ ψ a oa Ba j v β (proj₁ (emb a oa kk (ψ m om Bm k w (Ωt k) y)))
  φ-via m om w Bm β y = refl

  φ-up : (s : Sh) (h : Ch s → L) (om : Ok (nd s h)) (f : (c : Ch s) → Ab k (h c)) (Bm : Base (nd s h)) (β : Tr⁺ j)
    (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
    → φ a oa Ba kk j v (nd s h) om (ab f) Bm β (up x c y e)
    ≡ φ a oa Ba kk j v (h c) (proj₂ om c) (f c) (cb om Bm c x) (φ a oa Ba kk j v (nd s h) om (ab f) Bm β x) y
  φ-up s h om f Bm β x c y e = refl

  φ-node : (s : Sh) (h : Ch s → L) (om : Ok (nd s h)) (f : (c : Ch s) → Ab k (h c)) (Bm : Base (nd s h)) (β : Tr⁺ j)
    (p : Pos (nd s h)) (g : Br (nd s h) p → Tr (nd s h))
    → φ a oa Ba kk j v (nd s h) om (ab f) Bm β (Ω p g)
    ≡ node⁺ (kpA a oa kk v (ab f) (inj₂ p)) (λ z → φ a oa Ba kk j v (nd s h) om (ab f) Bm β (g z))
        (λ z → fromBr (nd s h) p (proj₁ (ψ (nd s h) om Bm (at (nd s h) p) (posW (nd s h) p) (Bm (at (nd s h) p) (posW (nd s h) p)) (g z))))
  φ-node s h om f Bm β p g = refl

  kpA-here : (t : Pos⁼ k) → kpA a oa kk v here t ≡ mapK (pshBr kk t) (pshFirst kk t) (kp⁼ a oa (psh kk t) v)
  kpA-here t = refl
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
  kp-z (nd (sΩ k) h) o@(_ , oc)      (inj₂ (c , t)) (ink v)   = kp⁼-z (h c) (oc c) t (v ∙ kh o c)
  kp-z (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼-z (h c) (oc c) t v
  kp-z (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind (λ Z → Z ≡ nothing) (way g r m n) (λ u → cong (mapK _ _) (kp⁼-z (g n) (oc n) (psh u t) v))
                                             (λ u → kp⁼-z (g m) (oc m) t (v ∙ u))
  kp-z (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = refl
  kp-z (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼-z k ok t v
  kp-z (nd (sΩ k) h) o@(_ , oc)      (inj₁ t)       (inc c v) = cong (mapK _ _) (kp⁼-z (h c) (oc c) (psh (kh o c) t) v)
  kp-z (nd (sΩ k) h) o@(_ , oc)      (inj₁ t)       (inu vs)  =
    cong (mapK _ _) (kp⁼-z (h zero) (oc zero) (psh (kh o zero) t) (vs zero))

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
Ok-Nx a oa = (oa , λ c → ab⊕ here (↑ a c)) , λ c → Ok⊕ a (↑ a c) oa (OkO↑ a a oa self c)

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

## 判据 (形状): 最小见证的底

塔第 1 项, 左项 `βΩ` (本层的 Ω 树), 孩子 two. `br c′ j v z`: 左项第 z 支的孩子树 (孩子 z 的 Ω 树) 以孩子 c′ 的层为锚朝 j 的 `φ`. 对照 R15A 的 `b1-form`, `b2-form` (旧块上各支是 `Ωt j + ι j (G c)`).

```agda
o¹ : Ok (tw 1)
o¹ = Ok-tw 1

h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

c1 c2 : Tr zero
c1 = suc zero
c2 = suc c1

L1 L2 : L
L1 = h₁ c1
L2 = h₁ c2

βΩ : Tr (tw 1)
βΩ = proj₁ (Ωt (tw 1))

BW : Base L2
BW = cb o¹ (B₀ (tw 1)) c2 βΩ

BW1 : Base L1
BW1 = cb o¹ (B₀ (tw 1)) c1 βΩ

q1 : Pos L1
q1 = inj₂ (tt , inj₁ tt)

q2 : Pos L2
q2 = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))

brY : (c′ : Tr zero) (j : L) → j ≤ h₁ c′ → (z : Tr zero) → Tr (h₁ z) → Tr⁺ j
brY c′ j v z y = φ (h₁ c′) (proj₂ o¹ c′) (B₀ (h₁ c′)) (kh o¹ c′) j v (h₁ z) (proj₂ o¹ z) (proj₂ (proj₁ o¹) z) (B₀ (h₁ z)) (Ωt j) y

br : (c′ : Tr zero) (j : L) → j ≤ h₁ c′ → Tr zero → Tr⁺ j
br c′ j v z = brY c′ j v z (proj₁ (Ωt (h₁ z)))

b2-form : proj₁ (BW L2 self) ≡ Ω q2 (λ z → proj₁ (br c2 L2 self z))
b2-form = refl

b1-form : proj₁ (BW L1 (inc tt self)) ≡ Ω q1 (λ z → proj₁ (br c2 L1 (inc tt self) z))
b1-form = refl

s1-form : proj₁ (BW1 L1 self) ≡ Ω q1 (λ z → proj₁ (br c1 L1 self z))
s1-form = refl

top-any : (Y : (c : Tr zero) → Tr (h₁ c)) (e : (c : Tr zero) → h₁ c ⊢ zero ◃ Y c)
  → proj₁ (cb o¹ (B₀ (tw 1)) c2 (Ω (inj₁ (inj₁ tt)) (λ c → up zero c (Y c) (e c))) L1 (inc tt self))
  ≡ Ω q1 (λ z → proj₁ (brY c2 L1 (inc tt self) z (Y z)))
top-any Y e = refl

up-any : (c : Tr zero) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
  → cb o¹ (B₀ (tw 1)) c2 (up zero c y e) L1 (inc tt self) ≡ brY c2 L1 (inc tt self) c y
up-any c y e = refl
```

各支的头 (有限测试): 第 1 支 (左项里的 Ω₁ 树) 在第 1 层保留成结点; 第 2 支 (Ω₂ 树) 是 ℕ 极限, 它的第 n 项是源层回灌链第 n 项的 `φ`.

```agda
br1-Ω : isΩ (proj₁ (br c2 L1 (inc tt self) c1))
br1-Ω = tt

br2-lim : isLim (proj₁ (br c2 L1 (inc tt self) c2))
br2-lim = tt

wit : (y : Tr L2) (e : L2 ⊢ zero ◃ y)
  → ψ₀ (tw 1) o¹ (up βΩ c2 y e) ≡ ψ L2 (proj₂ o¹ c2) BW zero (z≤ L2) (ψ₀ (tw 1) o¹ βΩ) y
wit y e = refl
```
