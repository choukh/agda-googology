# ℕ 极限层号的路线: 接口实填, 回归与决定性测试

> 验收文件. 编译定理: 接口 `YiLimIface.Iface` 由 `YiLimFold` 实填 (`limI`, 对一切带 `Ev` 与 `Rt` 的层号); 相邻孩子的两行的一般式 (`adj-up`, `adj-kp`, `adj-dn`); 必带路径的证据在塔第 1 项不可满足 (`no-req`), 合法树读出的层号可满足 (`req-leg`).
> 有限测试: (a) 没有路径时与 `YiUpFold` 相同; (b) `lim cumΩ` 里孩子 1 的底是前缀折到目标层的结点, 原来是极限; (c) `limA`, `limB` 一对在新折叠下一致, 都保留.
> 不否定什么. `no-req` 的反例是不合法的树, 读作 "必带路径的量化域太宽", 所以 `Rt` 里路径是可选的; 塔第 1 项的孩子层 (含 ω+1) 经 `Rt-tw` 得到的是 "没有路径" (`tw1-none`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLimCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; Leg)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiCheck using (isΩ; isLim)
open import OCF.Lean.YiPhiNegK using (InB; ib0; ibS; ibL; ibW; ibK; prE; brE; liftBr; evc; Kept)
open import OCF.Lean.YiUpBlock
import OCF.Lean.YiUpFold as U
import OCF.Lean.YiUpLegal as UL
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimFold
open import OCF.Lean.YiLimLegal
import OCF.Lean.YiLimIface as LI
```

## 接口的实填

```agda
J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n)
  (β : Tr j) (x : Tr (lim g)) (y : Tr (g n))
  → ψs (lim g) ε ρ B j (inl n w) β (up x n y)
  ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w (ψs (lim g) ε ρ B j (inl n w) β x) y
J2-lim g ε ρ B n j w β x y rewrite way-refl g (proj₂ ρ) n = refl

J2-lim-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
  (w : j ≤ g n) (β : Tr j) (x : Tr (lim g)) (y : Tr (g m)) (v : g n ≤ g m)
  → way g (proj₂ ρ) m n ≡ bwd v
  → ψs (lim g) ε ρ B j (inl n w) β (up x m y)
  ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (w ∙ v) (ψs (lim g) ε ρ B j (inl n w) β x) y
J2-lim-bwd g ε ρ B m n j w β x y v e rewrite e = refl

J2-lim-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
  (w : j ≤ g n) (β : Tr j) (x : Tr (lim g)) (y : Tr (g m)) (v : g m ≤ g n)
  → way g (proj₂ ρ) m n ≡ fwd v
  → ψs (lim g) ε ρ B j (inl n w) β (up x m y)
  ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w (ψs (lim g) ε ρ B j (inl n w) β x)
      (emb (g n) (ε n) v y)
J2-lim-fwd g ε ρ B m n j w β x y v e rewrite e = refl

J2-lim-none : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
  (w : j ≤ g n) (β : Tr j) (x : Tr (lim g)) (y : Tr (g m))
  → way g (proj₂ ρ) m n ≡ none
  → ψs (lim g) ε ρ B j (inl n w) β (up x m y)
  ≡ ψs (lim g) ε ρ B j (inl n w) β x + ι j (ψ⊥ (g m) (ε m) (proj₁ ρ m) (B₀ (g m)) y)
J2-lim-none g ε ρ B m n j w β x y e rewrite e = refl

kp-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
  {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g m ≤ g n)
  → way g (proj₂ ρ) m n ≡ fwd v
  → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d
  ≡ kp⁼ (g n) (ε n) (proj₁ ρ n) (psh v p) w (λ q cv → K q (λ z → pshBr v p (cv z))) d
kp-fwd g ε ρ m n p w K d v e rewrite e = refl

kp-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
  {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g n ≤ g m)
  → way g (proj₂ ρ) m n ≡ bwd v
  → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ kp⁼ (g m) (ε m) (proj₁ ρ m) p (w ∙ v) K d
kp-bwd g ε ρ m n p w K d v e rewrite e = refl

kp-none : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
  {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X)
  → way g (proj₂ ρ) m n ≡ none
  → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ d
kp-none g ε ρ m n p w K d e rewrite e = refl
```

`kall`: 与 `YiPhiNegK.lemA`, `lemB`, `child-kept` 同文, 多传路线; 沿 `lift` 下行只经 `inlu` 与 `inu` 的行, 不经改过的那一行.

```agda
lemA : (a b : L) (ea : Ev a) (eb : EvO a b) (ra : Rt a) (rb : RtP b) {K : L} (v : K ≤ a) (t : Pos⁼ K)
  {j : L} (u : j ≤ a) {X : Set}
  (Kc : (q : Pos j) → (Br j q → Br⁼ (a ⊕ b) (psh (v ∙ lift a b) t)) → X) (d : X)
  → kp⁼ (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) (psh (v ∙ lift a b) t) (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea ra (psh v t) u (λ q cv → Kc q (λ z → liftBr a b v t (cv z))) d
lemA a zero     ea eb            ra rb        v t u Kc d = refl
lemA a (suc b)  ea eb            ra rb        v t u Kc d = lemA a b ea eb ra rb v t u Kc d
lemA a (lim g)  ea eb            ra (rb , R)  v t u Kc d = lemA a (g zero) ea (eb zero) ra (rb zero) v t u Kc d
lemA a (Ωₗ k h) ea (w , ek , eb) ra (rk , rb) v t u Kc d = lemA a (h zero) ea (eb zero) ra (rb zero) v t u Kc d

lemB : (a b : L) (ea : Ev a) (ra : Rt a) {t : Pos (a ⊕ b)} (i : InB a b t) (eb : EvO a b) (rb : RtP b)
  {j : L} (u : j ≤ a) {X : Set} (Kc : (q : Pos j) → (Br j q → Br (a ⊕ b) t) → X) (d : X)
  → kp (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) t (u ∙ lift a b) Kc d
  ≡ kp⁼ a ea ra (prE i eb) u (λ q cv → Kc q (λ z → brE i eb (cv z))) d
lemB a _ ea ra (ib0 p)   eb            rb        u Kc d = refl
lemB a _ ea ra (ibS i)   eb            rb        u Kc d = lemB a _ ea ra i eb rb u Kc d
lemB a _ ea ra (ibL n i) eb            (rb , R)  u Kc d = lemB a _ ea ra i (eb n) (rb n) u Kc d
lemB a _ ea ra (ibW c i) (w , ek , eb) (rk , rb) u Kc d = lemB a _ ea ra i (eb c) (rb c) u Kc d
lemB a _ ea ra (ibK {h = h} t) (w , ek , eb) (rk , rb) u Kc d =
  lemA a (h zero) ea (eb zero) ra (rb zero) w t u _ d

kept-self : (a : L) (ea : Ev a) (ra : Rt a) (s : Pos⁼ a) (p : Pos a) → s ≡ inj₂ p
  → (F : (q : Pos a) → (Br a q → Br⁼ a s) → Br a q → Tr a) (d : Tr a)
  → Kept p (kp⁼ a ea ra s self (λ q cv → Ω q (F q cv)) d)
kept-self a ea ra .(inj₂ p) p refl F d = F p (λ z → z) , refl

child-kept : (a b : L) (ea : Ev a) (eb : EvO a b) (ra : Rt a) (rb : RtP b) (B : Base (a ⊕ b)) (β : Tr a)
  {t : Pos (a ⊕ b)} (G : Br (a ⊕ b) t → Tr (a ⊕ b)) (i : InB a b t) (p : Pos a) → prE i eb ≡ inj₂ p
  → Kept p (ψs (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) B a (self ∙ lift a b) β (Ω t G))
child-kept a b ea eb ra rb B β G i p e =
  subst (Kept p)
    (sym (lemB a b ea ra i eb rb self
      (λ q cv → Ω q (λ z → ψs (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) B a (self ∙ lift a b) β (G (cv z)))) _))
    (kept-self a ea ra (prE i eb) p e
      (λ q cv z → ψs (a ⊕ b) (Ev⊕ a b ea eb) (Rt⊕ a b ra rb) B a (self ∙ lift a b) β (G (brE i eb (cv z)))) _)

limI : LI.Iface
limI = record
  { ψ⊥ = ψ⊥
  ; ψs = ψs
  ; kp⁼ = kp⁼
  ; J2-suc  = λ a ε ρ B j w β x y → refl
  ; J2-lim  = J2-lim
  ; J2-limu = λ g ε ρ B j ws β x n y → refl
  ; J2-Ωk   = λ k h ε ρ B j w β x c y → refl
  ; J2-Ωu   = λ k h ε ρ B j ws β x c y → refl
  ; J2⊥-suc = λ a ε ρ B x y → refl
  ; J2⊥-lim = λ g ε ρ B x n y → refl
  ; J2⊥-Ω   = λ k h ε ρ B x c y → refl
  ; mono⊥ = mono⊥
  ; monos = monos
  ; pres⊥ = pres⊥
  ; press = press
  ; tw-leg = twᶜ-leg
  ; EBO-leg = EBOᶜ-leg
  ; kstep = λ n B β x p g → refl
  ; self-up = λ ℓ ε ρ B β x c y → refl
  ; kall = λ n B β x c G i p e →
      child-kept (tw n) (↑ (tw n) c) (Ev-tw n) (evc n c) (Rt-tw n) (RtP₀ (↑ (tw n) c)) _ _ G i p e
  ; node = λ ℓ ε ρ B j w β p G → refl
  ; kp-fwd = kp-fwd
  ; kp-bwd = kp-bwd
  ; kp-none = kp-none
  ; J2-lim-bwd = J2-lim-bwd
  ; J2-lim-fwd = J2-lim-fwd
  ; J2-lim-none = J2-lim-none
  }
```

## 相邻孩子的一般式

带相邻路径 r 的 ℕ 极限层号上, 孩子 n 的嵌入对孩子 n+1 里的目标: 孩子树沿 r n 搬进孩子 n+1, 交孩子 n+1 的折叠, 底是 x 对同一目标的折叠.
对照 `YiUpLimRows.lim-up` (同一输入上是 x 的折叠加孩子以 `B₀` 折到第 0 层的值). 反方向 (`adj-dn`) 目标沿 r n 搬进孩子 n+1.

```agda
cmp-suc : (n : ℕ) → cmp n (suc n) ≡ lt here
cmp-suc zero = refl
cmp-suc (suc n) rewrite cmp-suc n = refl

cmp-pre : (n : ℕ) → cmp (suc n) n ≡ gt here
cmp-pre zero = refl
cmp-pre (suc n) rewrite cmp-pre n = refl

adj-up : (g : ℕ → L) (ε : Ev (lim g)) (ρc : (n : ℕ) → Rt (g n)) (r : Adj g) (B : Base (lim g)) (n : ℕ)
  (j : L) (w : j ≤ g (suc n)) (β : Tr j) (x : Tr (lim g)) (y : Tr (g n))
  → ψs (lim g) ε (ρc , just r) B j (inl (suc n) w) β (up x n y)
  ≡ ψs (g (suc n)) (ε (suc n)) (ρc (suc n)) (dL g ε (ρc , just r) B (suc n) x) j w
      (ψs (lim g) ε (ρc , just r) B j (inl (suc n) w) β x) (emb (g (suc n)) (ε (suc n)) (r n) y)
adj-up g ε ρc r B n j w β x y rewrite cmp-suc n = refl

adj-dn : (g : ℕ → L) (ε : Ev (lim g)) (ρc : (n : ℕ) → Rt (g n)) (r : Adj g) (B : Base (lim g)) (n : ℕ)
  (j : L) (w : j ≤ g n) (β : Tr j) (x : Tr (lim g)) (y : Tr (g (suc n)))
  → ψs (lim g) ε (ρc , just r) B j (inl n w) β (up x (suc n) y)
  ≡ ψs (g (suc n)) (ε (suc n)) (ρc (suc n)) (dL g ε (ρc , just r) B (suc n) x) j (w ∙ r n)
      (ψs (lim g) ε (ρc , just r) B j (inl n w) β x) y
adj-dn g ε ρc r B n j w β x y rewrite cmp-pre n = refl

adj-kp : (g : ℕ → L) (ε : Ev (lim g)) (ρc : (n : ℕ) → Rt (g n)) (r : Adj g) (n : ℕ) (p : Pos⁼ (g n))
  {j : L} (w : j ≤ g (suc n)) {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g n) p) → X) (d : X)
  → kp (lim g) ε (ρc , just r) (n , p) (inl (suc n) w) K d
  ≡ kp⁼ (g (suc n)) (ε (suc n)) (ρc (suc n)) (psh (r n) p) w (λ q cv → K q (λ z → pshBr (r n) p (cv z))) d
adj-kp g ε ρc r n p w K d rewrite cmp-suc n = refl
```

## 必带路径的证据: 塔第 1 项不可满足, 合法树读出的层号可满足

`Req ℓ`: ℓ 里每个 ℕ 极限都带相邻路径. 塔第 1 项的孩子层由任意第 0 层的树读出; 取 `bad = lim (1, 0, 0, …)`, 相邻路径要 1 ≤ 0.
这条的反例不合法, 所以它只说明 "对一切分支必带路径" 这个量化域太宽. 对合法树 t, 读回层号 `↑ zero t` 满足 `Req` (`req-leg`).

```agda
Req : L → Set
Req zero     = ⊤
Req (suc a)  = Req a
Req (lim g)  = ((n : ℕ) → Req (g n)) × Adj g
Req (Ωₗ k h) = Req k × ((c : Tr k) → Req (h c))

badf : ℕ → Tr zero
badf zero    = suc zero
badf (suc n) = zero

bad : Tr zero
bad = lim badf

¬s≤z : {a : L} → suc a ≤ zero → ⊥
¬s≤z ()

no-req : Req (tw 1) → ⊥
no-req (_ , rc) = ¬s≤z (proj₂ (rc bad) zero)

req-leg : (t : Tr zero) → Leg zero t → Req (↑ zero t)
req-leg zero       h = tt
req-leg (suc t)    h = req-leg t h
req-leg (lim f)    (hf , adj) = (λ n → req-leg (f n) (hf n)) , (λ n → ⊑→≤ (◃→⊑ (adj n)))
req-leg (Ω () _)   h
req-leg (up _ () _) h
```

塔第 1 项经 `Rt-tw` 给孩子层的路线: 由任意树读出的 ℕ 极限处没有路径. 所以链点里的 ω+1 那一层, 新折叠走的仍是 `none` 的行 (与 `YiUpFold` 同文).

```agda
ω₀ : Tr zero
ω₀ = lim (iter suc zero)

tw1-none : proj₂ (proj₂ (Rt-tw 1) (suc ω₀)) ≡ nothing
tw1-none = refl

tw1-none-all : (f : ℕ → Tr zero) → proj₂ (proj₂ (Rt-tw 1) (lim f)) ≡ nothing
tw1-none-all f = refl
```

合法树读出的层号的路线 (闭项): ω+1 那一层, 相邻路径是 `ins self`.

```agda
ω₀-leg : Leg zero ω₀
ω₀-leg = (hf , λ n → ◃s)
  where
  hf : (n : ℕ) → Leg zero (iter suc zero n)
  hf zero    = tt
  hf (suc n) = hf n

Rt-ω+1 : Rt (zero ⊕ ↑ zero (suc ω₀))
Rt-ω+1 = Rt⊕ zero (↑ zero (suc ω₀)) tt (RtP↑ zero (suc ω₀) ω₀-leg)

Rt-ω+1-adj : proj₂ Rt-ω+1 ≡ just (λ n → ins self)
Rt-ω+1-adj = refl
```

## (a) 没有路径时与 `YiUpFold` 相同 (有限测试)

两个折叠是两个不同的互递归定义, 输出里极限的项是未化简的调用, 不能整棵用 `refl` 比; 这里比有限截断 `cut₀`, `cut₁` (深度 d, 极限与结点各取前两项).
层号 `lim gL` (g 0 = 1, g (n+1) = g n + 1), 路线取 `Rt₀`. 样本含不同号孩子的嵌入与结点 (这时两边都走回退与默认).

```agda
data Fo : Set where
  ze cutoff : Fo
  su : Fo → Fo
  li om uu : Fo → Fo → Fo

cut₀ : ℕ → Tr zero → Fo
cut₀ zero    _       = cutoff
cut₀ (suc d) zero    = ze
cut₀ (suc d) (suc x) = su (cut₀ d x)
cut₀ (suc d) (lim f) = li (cut₀ d (f 0)) (cut₀ d (f 1))
cut₀ (suc d) (Ω () _)
cut₀ (suc d) (up _ () _)

one two : L
one = suc zero
two = suc one

cut₁ : ℕ → Tr one → Fo
cut₁ zero    _          = cutoff
cut₁ (suc d) zero       = ze
cut₁ (suc d) (suc x)    = su (cut₁ d x)
cut₁ (suc d) (lim f)    = li (cut₁ d (f 0)) (cut₁ d (f 1))
cut₁ (suc d) (Ω (inj₁ tt) g) = om (cut₁ d (g zero)) (cut₁ d (g (suc zero)))
cut₁ (suc d) (up x tt y) = uu (cut₁ d x) (cut₀ d y)

gL : ℕ → L
gL zero    = one
gL (suc n) = suc (gL n)

εL : Ev (lim gL)
εL zero    = tt
εL (suc n) = εL n

ρ₀ : Rt (lim gL)
ρ₀ = Rt₀ (lim gL)

nodeL : (Tr zero → Tr (lim gL)) → Tr (lim gL)
nodeL G = Ω (0 , inj₂ (inj₁ tt)) G

pA pB : one ≤ lim gL
pA = inl 0 self
pB = inl 1 (ins self)

pre₀ x₀₁ : Tr (lim gL)
pre₀ = up zero 0 (Ωt one)
x₀₁ = up pre₀ 1 (Ωt two)

a-up : cut₁ 4 (ψs (lim gL) εL ρ₀ (B₀ _) one pB (Ωt one) x₀₁)
     ≡ cut₁ 4 (U.ψs (lim gL) εL (B₀ _) one pB (Ωt one) x₀₁)
a-up = refl

a-up′ : cut₁ 4 (ψs (lim gL) εL ρ₀ (B₀ _) one pA (Ωt one) x₀₁)
      ≡ cut₁ 4 (U.ψs (lim gL) εL (B₀ _) one pA (Ωt one) x₀₁)
a-up′ = refl

a-node : cut₁ 4 (ψs (lim gL) εL ρ₀ (B₀ _) one pB (Ωt one) (nodeL (λ c → up zero 0 (Ωt one))))
       ≡ cut₁ 4 (U.ψs (lim gL) εL (B₀ _) one pB (Ωt one) (nodeL (λ c → up zero 0 (Ωt one))))
a-node = refl

a-⊥ : cut₀ 4 (ψ⊥ (lim gL) εL ρ₀ (B₀ _) x₀₁) ≡ cut₀ 4 (U.ψ⊥ (lim gL) εL (B₀ _) x₀₁)
a-⊥ = refl

a-Ω : cut₀ 4 (ψ₀ (lim gL) εL ρ₀ (Ωt (lim gL))) ≡ cut₀ 4 (U.ψ₀ (lim gL) εL (Ωt (lim gL)))
a-Ω = refl

a-suc : cut₁ 4 (ψs two tt tt (B₀ two) one (ins self) (Ωt one) (up (suc zero) tt (Ωt one)))
      ≡ cut₁ 4 (U.ψs two tt (B₀ two) one (ins self) (Ωt one) (up (suc zero) tt (Ωt one)))
a-suc = refl
```

带路径时同号孩子的输入也相同 (同号走 `bwd self`, 即原来的同号行).

```agda
rL : Adj gL
rL n = ins self

ρL : Rt (lim gL)
ρL = (λ n → Rt₀ (gL n)) , just rL

a-same : cut₁ 4 (ψs (lim gL) εL ρL (B₀ _) one pB (Ωt one) (up zero 1 (Ωt two)))
       ≡ cut₁ 4 (U.ψs (lim gL) εL (B₀ _) one pB (Ωt one) (up zero 1 (Ωt two)))
a-same = refl
```

## (b) 孩子 1 的底是前缀折到目标层的树

`Ωt (lim gL) = lim cumΩ`, `cumΩ 1 = up (cumΩ 0) 1 (Ωt 2)`, `cumΩ 0 = up zero 0 (Ωt 1)`. 折孩子 1 时的底在目标 "孩子 1 里的第 1 层" 上的分量是前缀 `cumΩ 0` 对这个目标的折叠.
带路径: 前缀里孩子 0 的 Ω 树搬进孩子 1, 折到第 1 层, 根结点保留, 是结点. 没有路径或原折叠: `Ωt 1 + ι …`, 是极限.

```agda
b-new : isΩ (bs (dL gL εL ρL (B₀ _) 1 pre₀) one (ins self))
b-new = tt

b-new-form : bs (dL gL εL ρL (B₀ _) 1 pre₀) one (ins self)
           ≡ ψs two tt tt (dL gL εL ρL (B₀ _) 1 zero) one (ins self) (Ωt one) (up zero tt (Ωt one))
b-new-form = refl

b-none : isLim (bs (dL gL εL ρ₀ (B₀ _) 1 pre₀) one (ins self))
b-none = tt

b-old : isLim (bs (UL.dL gL εL (B₀ _) 1 pre₀) one (ins self))
b-old = tt
```

ω+1 那一层本身 (层号 `h₁ (suc ω₀)`, 孩子 n 是层号 n): 前缀里孩子 1 的 Ω 树对 "孩子 2 里的第 1 层" 的折叠.
路线取合法性给出的 `Rt-ω+1` 时是结点; 取塔第 1 项给的 `Rt-tw 1` 时是极限 (回退行).

```agda
gω : ℕ → L
gω n = zero ⊕ ↑ zero (iter suc zero n)

εω : Ev (lim gω)
εω = proj₂ (proj₂ (Ev-tw 1) (suc ω₀))

ρω-tw : Rt (lim gω)
ρω-tw = proj₂ (Rt-tw 1) (suc ω₀)

preω : Tr (lim gω)
preω = up (up zero 0 (suc zero)) 1 (Ωt one)

bω-leg : isΩ (bs (dL gω εω Rt-ω+1 (B₀ _) 2 preω) one (ins self))
bω-leg = tt

bω-tw : isLim (bs (dL gω εω ρω-tw (B₀ _) 2 preω) one (ins self))
bω-tw = tt
```

## (c) `limA`, `limB` 一对

结点在孩子 0 的第 0 层槽位, 目标层 1 经两条路径. 带路径时两条都保留 (同一个目标层里的槽位); 没有路径时与原折叠一样, 一条保留一条不保留.

```agda
c-A : (B : Base (lim gL)) (G : Tr zero → Tr (lim gL)) → isΩ (ψs (lim gL) εL ρL B one pA (Ωt one) (nodeL G))
c-A B G = tt

c-B : (B : Base (lim gL)) (G : Tr zero → Tr (lim gL)) → isΩ (ψs (lim gL) εL ρL B one pB (Ωt one) (nodeL G))
c-B B G = tt

c-B-slot : (B : Base (lim gL)) (G : Tr zero → Tr (lim gL))
  → Kept (inj₁ tt) (ψs (lim gL) εL ρL B one pB (Ωt one) (nodeL G))
c-B-slot B G = _ , refl

c-A-slot : (B : Base (lim gL)) (G : Tr zero → Tr (lim gL))
  → Kept (inj₁ tt) (ψs (lim gL) εL ρL B one pA (Ωt one) (nodeL G))
c-A-slot B G = _ , refl

c-B-none : (B : Base (lim gL)) (G : Tr zero → Tr (lim gL))
  → isLim (ψs (lim gL) εL ρ₀ B one pB (Ωt one) (nodeL G))
c-B-none B G = tt
```
