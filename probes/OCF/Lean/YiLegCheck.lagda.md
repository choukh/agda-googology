# 合法性进块: 证据可满足, J2 的各条, 决定性测试

> 验收文件. 编译定理: 必带路线对塔各项的每个孩子层可满足 (`req-child`, 对照 `YiLimCheck.no-req`); `lim (1,0,0,…)` 不是树 (`no-bad`); 塔第 1 项给 ω+1 那一层的相邻路径是 `ins self` (`tw1-adj`); J2 的各条与不同号孩子两行的一般式.
> 有限测试: 用塔第 1 项自己的证据 (`Ev-tw 1`, `Rt-tw 1`), ω+1 那一层孩子 2 的底是结点 (`bω-tw`, 对照 `YiLimCheck.bω-tw` 是极限); 结点对两条目标路径都保留 (`cω-A`, `cω-B`).
> 不否定什么. 这里没有值定理; `(Ωₗ k h, inb c′, up x c y)` 一行仍是回退 (`J2-Ωb`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLegCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
```

## 必带路线可满足

`YiLimCheck.no-req` 的反例是 `lim (1,0,0,…)`; 这里造 ℕ 极限要交 1 ◃ 0, 没有这样的推导.
塔第 n+1 项的每个孩子层 tw n ⊕ ↑c 都带必带的路线, 对一切分支 c (分支只取合法树).

```agda
no-bad : {ℓ : L} {x : Tr ℓ} → ℓ ⊢ suc x ◃ zero → ⊥
no-bad d = ¬◃z d

req-child : (n : ℕ) (c : Tr (tw n)) → Rt (tw n ⊕ ↑ (tw n) c)
req-child n c = proj₂ (Rt-tw (suc n)) c

req-lim : (n : ℕ) (f : ℕ → Tr (tw n)) (a : (i : ℕ) → tw n ⊢ f i ◃ f (suc i))
  → Adj (λ i → tw n ⊕ ↑ (tw n) (f i))
req-lim n f a = proj₂ (req-child n (lim f a))
```

ω+1 那一层: 塔第 1 项经 `Rt-tw` 给它的相邻路径是 `ins self` (对照 `YiLimCheck.tw1-none`: 那里是 `nothing`).

```agda
ω₀ : Tr zero
ω₀ = lim (iter suc zero) (λ n → ◃s)

gω : ℕ → L
gω n = zero ⊕ ↑ zero (iter suc zero n)

εω : Ev (lim gω)
εω = proj₂ (proj₂ (Ev-tw 1) (suc ω₀))

ρω : Rt (lim gω)
ρω = proj₂ (Rt-tw 1) (suc ω₀)

tw1-adj : proj₂ ρω ≡ (λ n → ins self)
tw1-adj = refl

tw1-way : way gω (proj₂ ρω) 1 2 ≡ fwd (ins self)
tw1-way = refl
```

## J2 的各条

孩子层的折叠以 x 对同一目标的折叠为底 (同号孩子, 一切孩子的路径, `Ωₗ` 的下标层侧); 到第 0 层的三条; 自身行是上折; 结点行是保留判定.

```agda
J2-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (j : L) (w : j ≤ a) (β : Tr j)
  (nβ : j ⊢ zero ◃ β) (x : Tr (suc a)) (y : Tr a) (e : a ⊢ zero ◃ y)
  → ψs (suc a) ε ρ B j (ins w) β nβ (up x tt y e)
  ≡ ψs a ε ρ (dS a ε ρ B x) j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) y
J2-suc a ε ρ B j w β nβ x y e = refl

J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n)
  (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g n)) (e : g n ⊢ zero ◃ y)
  → ψs (lim g) ε ρ B j (inl n w) β nβ (up x n y e)
  ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w
      (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) y
J2-lim g ε ρ B n j w β nβ x y e rewrite way-refl g (proj₂ ρ) n = refl

J2-lim-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
  (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y)
  (v : g n ≤ g m) → way g (proj₂ ρ) m n ≡ bwd v
  → ψs (lim g) ε ρ B j (inl n w) β nβ (up x m y e)
  ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (w ∙ v)
      (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) y
J2-lim-bwd g ε ρ B m n j w β nβ x y e v q rewrite q = refl

J2-lim-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
  (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y)
  (v : g m ≤ g n) → way g (proj₂ ρ) m n ≡ fwd v
  → ψs (lim g) ε ρ B j (inl n w) β nβ (up x m y e)
  ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w
      (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) (emb (g n) (ε n) v y e)
J2-lim-fwd g ε ρ B m n j w β nβ x y e v q rewrite q = refl

J2-limu : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (j : L) (ws : (n : ℕ) → j ≤ g n)
  (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (m : ℕ) (y : Tr (g m)) (e : g m ⊢ zero ◃ y)
  → ψs (lim g) ε ρ B j (inlu ws) β nβ (up x m y e)
  ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (ws m)
      (ψs (lim g) ε ρ B j (inlu ws) β nβ x) (nzs (lim g) ε ρ B j (inlu ws) β nβ x) y
J2-limu g ε ρ B j ws β nβ x m y e = refl

J2-Ωk : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (w : j ≤ k)
  (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψs (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (w ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) y
J2-Ωk k h ε ρ B j w β nβ x c y e = refl

J2-Ωu : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
  (ws : (c : Tr k) → j ≤ h c) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
  (e : h c ⊢ zero ◃ y)
  → ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e)
  ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (ws c)
      (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) y
J2-Ωu k h ε ρ B j ws β nβ x c y e = refl

J2-Ωb : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (c′ : Tr k)
  (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
  ≡ ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y)
J2-Ωb k h ε ρ B j c′ w β nβ x c y e = refl

J2⊥-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a)
  (e : a ⊢ zero ◃ y) → ψ⊥ (suc a) ε ρ B (up x tt y e) ≡ ψ⊥ a ε ρ (dS a ε ρ B x) y
J2⊥-suc a ε ρ B x y e = refl

J2⊥-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (x : Tr (lim g)) (n : ℕ)
  (y : Tr (g n)) (e : g n ⊢ zero ◃ y)
  → ψ⊥ (lim g) ε ρ B (up x n y e) ≡ ψ⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) y
J2⊥-lim g ε ρ B x n y e = refl

J2⊥-Ω : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (x : Tr (Ωₗ k h))
  (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → ψ⊥ (Ωₗ k h) ε ρ B (up x c y e) ≡ ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) y
J2⊥-Ω k h ε ρ B x c y e = refl

self-up : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (β : Tr ℓ) (nβ : ℓ ⊢ zero ◃ β) (x : Tr ℓ) (c : Ch ℓ)
  (y : ChT ℓ c) (e : RCh ℓ c (chZ ℓ c) y)
  → ψs ℓ ε ρ B ℓ self β nβ (up x c y e)
  ≡ Upc ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y
self-up ℓ ε ρ B β nβ x c y e = refl

node-self : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (β : Tr ℓ) (nβ : ℓ ⊢ zero ◃ β) (p : Pos ℓ)
  (G : Br ℓ p → Tr ℓ)
  → ψs ℓ ε ρ B ℓ self β nβ (Ω p G) ≡ Ω p (λ z → ψs ℓ ε ρ B ℓ self β nβ (G z))
node-self ℓ ε ρ B β nβ p G = refl
```

链步的回灌: 结点到第 0 层的折叠是部分和的极限, 第 n 项的分支是折叠输出回灌 n 次; 回灌的分支是 `Br ℓ p` 的元素, 即合法树, 不需要另证.

```agda
step : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (G : Br ℓ p → Tr ℓ) → Br ℓ p → Br ℓ p
step ℓ ε ρ B p G z =
  fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (G z))

kstep : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (G : Br ℓ p → Tr ℓ)
  → ψ⊥ ℓ ε ρ B (Ω p G)
  ≡ limc (λ n → ψ⊥ ℓ ε ρ B (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n)))
         (λ n → nz⊥ ℓ ε ρ B (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n)))
kstep ℓ ε ρ B p G = refl
```

## 相邻孩子的一般式

```agda
cmp-suc : (n : ℕ) → cmp n (suc n) ≡ lt here
cmp-suc zero = refl
cmp-suc (suc n) rewrite cmp-suc n = refl

cmp-pre : (n : ℕ) → cmp (suc n) n ≡ gt here
cmp-pre zero = refl
cmp-pre (suc n) rewrite cmp-pre n = refl

adj-up : (g : ℕ → L) (ε : Ev (lim g)) (ρc : (n : ℕ) → Rt (g n)) (r : Adj g) (B : Base (lim g)) (n : ℕ)
  (j : L) (w : j ≤ g (suc n)) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g n))
  (e : g n ⊢ zero ◃ y)
  → ψs (lim g) ε (ρc , r) B j (inl (suc n) w) β nβ (up x n y e)
  ≡ ψs (g (suc n)) (ε (suc n)) (ρc (suc n)) (dL g ε (ρc , r) B (suc n) x) j w
      (ψs (lim g) ε (ρc , r) B j (inl (suc n) w) β nβ x) (nzs (lim g) ε (ρc , r) B j (inl (suc n) w) β nβ x)
      (emb (g (suc n)) (ε (suc n)) (r n) y e)
adj-up g ε ρc r B n j w β nβ x y e rewrite cmp-suc n = refl

adj-dn : (g : ℕ → L) (ε : Ev (lim g)) (ρc : (n : ℕ) → Rt (g n)) (r : Adj g) (B : Base (lim g)) (n : ℕ)
  (j : L) (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g (suc n)))
  (e : g (suc n) ⊢ zero ◃ y)
  → ψs (lim g) ε (ρc , r) B j (inl n w) β nβ (up x (suc n) y e)
  ≡ ψs (g (suc n)) (ε (suc n)) (ρc (suc n)) (dL g ε (ρc , r) B (suc n) x) j (w ∙ r n)
      (ψs (lim g) ε (ρc , r) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , r) B j (inl n w) β nβ x) y
adj-dn g ε ρc r B n j w β nβ x y e rewrite cmp-pre n = refl

adj-kp : (g : ℕ → L) (ε : Ev (lim g)) (ρc : (n : ℕ) → Rt (g n)) (r : Adj g) (n : ℕ) (p : Pos⁼ (g n))
  {j : L} (w : j ≤ g (suc n)) {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g n) p) → X) (d : X)
  → kp (lim g) ε (ρc , r) (n , p) (inl (suc n) w) K d
  ≡ kp⁼ (g (suc n)) (ε (suc n)) (ρc (suc n)) (psh (r n) p) w (λ q cv → K q (λ z → pshBr (r n) p (cv z))) d
adj-kp g ε ρc r n p w K d rewrite cmp-suc n = refl
```

## 决定性测试 (有限测试)

ω+1 那一层 (层号 `lim gω`, 孩子 n 是层号 n), 证据取塔第 1 项自己给的 `εω`, `ρω`.
前缀里孩子 1 的 Ω 树对 "孩子 2 里的第 1 层" 的折叠, 即折孩子 2 时的底在该目标上的分量, 是结点.

```agda
isΩ : {ℓ : L} → Tr ℓ → Set
isΩ (Ω _ _) = ⊤
isΩ _       = ⊥

isLim : {ℓ : L} → Tr ℓ → Set
isLim (lim _ _) = ⊤
isLim _         = ⊥

one : L
one = suc zero

preω : Tr (lim gω)
preω = up (up zero 0 (suc zero) ◃s) 1 (Ωt one) (Ωt-nz one)

bω-tw : isΩ (bs (dL gω εω ρω (B₀ _) 2 preω) one (ins self))
bω-tw = tt

bω-form : bs (dL gω εω ρω (B₀ _) 2 preω) one (ins self)
        ≡ Ω (inj₁ tt) (λ z → ψs one tt tt
            (dS one tt tt (dL gω εω ρω (B₀ _) 2 (up zero 0 (suc zero) ◃s)) zero) one self
            (ψs (lim gω) εω ρω (B₀ _) one (inl 2 (ins self)) (Ωt one) (Ωt-nz one) (up zero 0 (suc zero) ◃s))
            (nzs (lim gω) εω ρω (B₀ _) one (inl 2 (ins self)) (Ωt one) (Ωt-nz one) (up zero 0 (suc zero) ◃s))
            (up zero tt (suc z) (z◃s z)))
bω-form = refl
```

结点在孩子 1 的第 0 层槽位, 目标是第 1 层, 经孩子 1 (`pA`) 与经孩子 2 (`pB`) 两条路径都保留.

```agda
nodeω : (Tr zero → Tr (lim gω)) → Tr (lim gω)
nodeω G = Ω (1 , inj₂ (inj₁ tt)) G

pA pB : one ≤ lim gω
pA = inl 1 self
pB = inl 2 (ins self)

cω-A : (B : Base (lim gω)) (G : Tr zero → Tr (lim gω)) → isΩ (ψs (lim gω) εω ρω B one pA (Ωt one) (Ωt-nz one) (nodeω G))
cω-A B G = tt

cω-B : (B : Base (lim gω)) (G : Tr zero → Tr (lim gω)) → isΩ (ψs (lim gω) εω ρω B one pB (Ωt one) (Ωt-nz one) (nodeω G))
cω-B B G = tt
```

读法的闭项: `EBOᶜ = ψ₀(Ω_Λ)` 与塔各项的 `twᶜ n` 是第 0 层的树 (类型即合法); `EBOᶜ` 的根是 ℕ 极限.

```agda
EBOᶜ-lim : isLim EBOᶜ
EBOᶜ-lim = tt

tw1ᶜ-lim : isLim (twᶜ 1)
tw1ᶜ-lim = tt
```
