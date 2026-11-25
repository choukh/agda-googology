# 实验 E2 在规范域内: `ψ₀ (suc (tw 2)) (Ωt (suc (tw 2)))` 链里 ℕ 极限层号的结点

> 验收文件 (空白页的块, 对照 [YiDlLost](YiDlLost.lagda.md), [YiScopeE2](YiScopeE2.lagda.md)). 判决: **保留**. 编译定理 (`keep-self`, `keep-suc`, `ι-noΩ`) 与有限测试 (`refl` 与构造出的出现证据), 无前提; 测试对象都在 `Top` 域内 (`*-top`), 不用非顶槽位.
> 结点: 链 γ 第 1 点的第 0 分量 (`Ωt (tw 2)`) 的根结点链在 δ₁ 处的孩子, 再沿两层 ℕ 极限分量到后继层号 `suc LN` 的根结点 N; N 的链第二步的源里有下标层为 ℕ 极限 (`limP`)、`LN` 有其槽位 (`couldP`) 的结点 (`occP`), 输出里原样保留, 分支相同 (`keptP`, `kept-branch`). 空白页的链从 0 起, 第一步输出 `next (Ωt LN)`; 旧块与作用域块的链从 Ω 树起, 它们第一步的源对应这里第二步的源. tw 3 同 (`*³`).
> 对照 (k 侧, 有限测试): 同一条件的结点在 `Ωₗ` 层号根结点的链步里随整个孩子折到第 0 层 (`occK`, `couldK`, `stepK`, `ι-noΩ`), 是已知回退 (`R13Base`), 不在旧派发的那个位置上.
> 不陈述值. 规范域见 [YiTopDom](YiTopDom.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTopE2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold
open import OCF.Lean.YiFreshLegal using (dS; dL; dW; iterInv)
open import OCF.Lean.YiTopDom
```

## 1 出现

`Occ ℓ t m s`: 树 t 沿 `suc`, `lim` 的分量, 结点的分支, `up` 的偏移与孩子走到 m 层的子树 s. `Node ℓ t m q`: t 里有 m 层槽位 q 上的结点.

```agda
data Occ : (ℓ : L) → Tr ℓ → (m : L) → Tr m → Set where
  here : ∀ {ℓ t} → Occ ℓ t ℓ t
  inS  : ∀ {ℓ x m s} → Occ ℓ x m s → Occ ℓ (suc x) m s
  inL  : ∀ {ℓ f m s} n → Occ ℓ (f n) m s → Occ ℓ (lim f) m s
  inΩ  : ∀ {ℓ p g m s} z → Occ ℓ (g z) m s → Occ ℓ (Ω p g) m s
  inX  : ∀ {ℓ x c y m s} → Occ ℓ x m s → Occ ℓ (up x c y) m s
  inC  : ∀ {ℓ x c y m s} → Occ (chL ℓ c) (chT ℓ c y) m s → Occ ℓ (up x c y) m s

Node : (ℓ : L) → Tr ℓ → (m : L) → Pos m → Set
Node ℓ t m q = Σ (Br m q → Tr m) λ g → Occ ℓ t m (Ω q g)
```

## 2 编译定理: 目标为 self 时一切结点保留; 后继层号结点的链步是孩子层的 self

```agda
keep-self : (ℓ : L) (B : Base ℓ) (t : Tr ℓ) {m : L} {q : Pos m} → Node ℓ t m q → Node ℓ (ψs ℓ B ℓ self t) m q
keep-self ℓ B t (g , o) = go t o
  where
  go : (t : Tr ℓ) {m : L} {q : Pos m} {g : Br m q → Tr m} → Occ ℓ t m (Ω q g) → Node ℓ (ψs ℓ B ℓ self t) m q
  go (Ω q g) here = _ , here
  go (suc x) (inS o) with go x o
  ... | g′ , o′ = g′ , inL 0 o′
  go (lim f) (inL n o) with go (f n) o
  ... | g′ , o′ = g′ , inL n o′
  go (Ω p g) (inΩ z o) with go (g z) o
  ... | g′ , o′ = g′ , inΩ z o′
  go (up x c y) (inX o) with go x o
  ... | g′ , o′ = g′ , inX o′
  go (up x c y) (inC o) = _ , inC o

keep-suc : (a : L) (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a) {m : L} {q : Pos m}
  → Node a y m q → Node a (ψs (suc a) B a (ins self) (up x tt y)) m q
keep-suc a B x y n = keep-self a (dS a B x) y n

ι-noΩ : (j : L) (a : Tr zero) {m : L} {q : Pos m} {g : Br m q → Tr m} → Occ j (ι j a) m (Ω q g) → ⊥
ι-noΩ j zero ()
ι-noΩ j (suc a) (inS o) = ι-noΩ j a o
ι-noΩ j (lim f) (inL n o) = ι-noΩ j (f n) o
ι-noΩ j (Ω () _) o
ι-noΩ j (up _ () _) o
```

## 3 外层链的第一、二步

```agda
stp : Tr (tw 2) → Tr (tw 2)
stp z = ψs (suc (tw 2)) (B₀ _) (tw 2) (ins self) (up zero tt (suc z))

γ : ℕ → Tr (tw 2)
γ = iter stp zero

T⁺-form : ψ₀ (suc (tw 2)) (Ωt (suc (tw 2))) ≡ lim (cum (λ n → ψ⊥ (suc (tw 2)) (B₀ _) (up zero tt (suc (γ n)))))
T⁺-form = refl

γ-1 : γ 1 ≡ next (Ωt (tw 2))
γ-1 = refl

γ-2 : γ 2 ≡ next (ψs (tw 2) (B₀ _) (tw 2) self (γ 1))
γ-2 = refl

cp : ∀ {P B C D} → ℕ → T P B C D → T P B C D
cp n (lim f) = f n
cp n x = x

γ₁₀ : cp 0 (γ 1) ≡ Ωt (tw 2)
γ₁₀ = refl
```

## 4 从 γ₁ 走到孩子根上的结点 N

γ₁ 的第 0 分量是 `Ωt (tw 2)`; 它折到第 0 层时根结点的链 δ 在 tw 1 层. δ₁ 处的孩子层号是 ℕ 极限, 沿第 0, 0 分量到后继层号 `suc LN`.

```agda
h₁ : Tr (tw 1) → L
h₁ c = tw 1 ⊕ ↑ (tw 1) c

G0 : Tr (tw 1) → Tr (tw 2)
G0 z = up zero z (Ωt (h₁ z))

st0 : Tr (tw 1) → Tr (tw 1)
st0 z = ψs (tw 2) (B₀ _) (tw 1) (ink self) (G0 z)

δ : ℕ → Tr (tw 1)
δ = iter st0 zero

fold-Ωt₂ : ψ⊥ (tw 2) (B₀ _) (Ωt (tw 2))
         ≡ lim (cum (λ m → ψ⊥ (h₁ (δ m)) (dW (tw 1) h₁ (B₀ _) (δ m) zero) (Ωt (h₁ (δ m)))))
fold-Ωt₂ = refl

Tw₁ : Tr zero
Tw₁ = ψ₀ (tw 1) (Ωt (tw 1))

δ-1 : δ 1 ≡ Ωt (tw 1) + ι (tw 1) Tw₁
δ-1 = refl

LN : L
LN = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))

g₁ g₂ : ℕ → L
g₁ n = chL (h₁ (δ 1)) n
g₂ n = chL (g₁ 0) n

lvN : g₂ 0 ≡ suc LN
lvN = refl

B₁ : Base (lim g₁)
B₁ = dW (tw 1) h₁ (B₀ _) (δ 1) zero

B₂ : Base (lim g₂)
B₂ = dL g₁ B₁ 0 zero

BN : Base (suc LN)
BN = dL g₂ B₂ 0 zero

reach : cp 0 (cp 0 (ψ⊥ (tw 2) (B₀ _) (G0 (δ 1)))) ≡ ψ⊥ (suc LN) BN (Ωt (suc LN))
reach = refl
```

## 5 N 的链与第二步

```agda
stN : Tr LN → Tr LN
stN z = ψs (suc LN) BN LN (ins self) (up zero tt (suc z))

η : ℕ → Tr LN
η = iter stN zero

N-fold : ψ⊥ (suc LN) BN (Ωt (suc LN)) ≡ lim (cum (λ n → ψ⊥ (suc LN) BN (up zero tt (suc (η n)))))
N-fold = refl

η-1 : η 1 ≡ next (Ωt LN)
η-1 = refl

η-2 : η 2 ≡ next (ψs LN (dS LN BN zero) LN self (next (Ωt LN)))
η-2 = refl

ω₀ c₀ : Tr zero
ω₀ = ψ₀ zero (Ωt zero)
c₀ = suc ω₀

occP : Node (suc LN) (up zero tt (suc (η 1))) (chL LN c₀) (inj₁ (inj₁ tt))
occP = _ , inC (inS (inL 0 (inΩ c₀ (inC here))))

limP : Σ (ℕ → L) λ f → at (chL LN c₀) (inj₁ (inj₁ tt)) ≡ lim f
limP = _ , refl

couldP : Σ (Pos LN) λ p → at LN p ≡ at (chL LN c₀) (inj₁ (inj₁ tt))
couldP = inj₂ (c₀ , inj₂ (inj₁ (inj₁ tt))) , refl

keptP : Node LN (η 2) (chL LN c₀) (inj₁ (inj₁ tt))
keptP = _ , inL 0 (inL 0 (inΩ c₀ (inC here)))

kept-branch : proj₁ keptP ≡ proj₁ occP
kept-branch = refl
```

## 6 对照: k 侧 (有限测试)

同一个结点在 δ₁ 处的源 `G0 (δ 1)` 里 (经 N 在 `Ωt LN` 处的分支); 它的下标层是 tw 1 的槽位; 链步走 `ink` 的回退, 整个孩子折到第 0 层再以 ι 抬回, ι 的像里没有结点 (`ι-noΩ`).

```agda
occK : Node (tw 2) (G0 (δ 1)) (chL LN c₀) (inj₁ (inj₁ tt))
occK = _ , inC (inL 0 (inC (inL 0 (inC (inΩ (Ωt LN) (inC (inS (inΩ c₀ (inC here)))))))))

couldK : Σ (Pos (tw 1)) λ p → at (tw 1) p ≡ at (chL LN c₀) (inj₁ (inj₁ tt))
couldK = inj₂ (ω₀ , inj₁ tt) , refl

stepK : st0 (δ 1) ≡ Ωt (tw 1) + ι (tw 1) (ψ₀ (h₁ (δ 1)) (Ωt (h₁ (δ 1))))
stepK = refl
```

## 7 测试对象在 `Top` 域内

```agda
dL-top : (g : ℕ → L) (B : Base (lim g)) → TopB (lim g) B → (n : ℕ) (x : Tr (lim g)) → Top (lim g) x
       → TopB (g n) (dL g B n x)
dL-top g B hB n x hx = top⊥ (lim g) B hB x hx , λ j w → tops (lim g) B hB j (inl n w) x hx

dW-top : (k : L) (h : Tr k → L) (B : Base (Ωₗ k h)) → TopB (Ωₗ k h) B → (c : Tr k) (x : Tr (Ωₗ k h))
       → Top (Ωₗ k h) x → TopB (h c) (dW k h B c x)
dW-top k h B hB c x hx = top⊥ (Ωₗ k h) B hB x hx , λ j w → tops (Ωₗ k h) B hB j (inb c w) x hx

T⁺-top : Top (suc (tw 2)) (Ωt (suc (tw 2)))
T⁺-top = Ωt-top (suc (tw 2))

γ-top : (n : ℕ) → Top (tw 2) (γ n)
γ-top = iterInv (Top (tw 2)) stp zero tt
  (λ z hz → tops (suc (tw 2)) (B₀ _) (TopB₀ _) (tw 2) (ins self) (up zero tt (suc z)) (tt , hz))

δ-top : (n : ℕ) → Top (tw 1) (δ n)
δ-top = iterInv (Top (tw 1)) st0 zero tt
  (λ z hz → tops (tw 2) (B₀ _) (TopB₀ _) (tw 1) (ink self) (G0 z) (tt , Ωt-top (h₁ z)))

BN-top : TopB (suc LN) BN
BN-top = dL-top g₂ B₂ (dL-top g₁ B₁ (dW-top (tw 1) h₁ (B₀ _) (TopB₀ _) (δ 1) zero tt) 0 zero tt) 0 zero tt

η-top : (n : ℕ) → Top LN (η n)
η-top = iterInv (Top LN) stN zero tt
  (λ z hz → tops (suc LN) BN BN-top LN (ins self) (up zero tt (suc z)) (tt , hz))

src-top : Top (suc LN) (up zero tt (suc (η 1)))
src-top = tt , η-top 1

node-top : Top (chL LN c₀) (Ωt (chL LN c₀))
node-top = Ωt-top (chL LN c₀)

srcK-top : Top (tw 2) (G0 (δ 1))
srcK-top = tt , Ωt-top (h₁ (δ 1))
```

## 8 tw 3 的对应情形

结构同上, 孩子层号多一层 ℕ 极限.

```agda
h₂ : Tr (tw 2) → L
h₂ c = tw 2 ⊕ ↑ (tw 2) c

G0³ : Tr (tw 2) → Tr (tw 3)
G0³ z = up zero z (Ωt (h₂ z))

st0³ : Tr (tw 2) → Tr (tw 2)
st0³ z = ψs (tw 3) (B₀ _) (tw 2) (ink self) (G0³ z)

δ³ : ℕ → Tr (tw 2)
δ³ = iter st0³ zero

LN³ : L
LN³ = tw 2 ⊕ ↑ (tw 2) (Ωt (tw 2))

g₁³ g₂³ g₃³ : ℕ → L
g₁³ n = chL (h₂ (δ³ 1)) n
g₂³ n = chL (g₁³ 0) n
g₃³ n = chL (g₂³ 0) n

lvN³ : g₃³ 0 ≡ suc LN³
lvN³ = refl

BN³ : Base (suc LN³)
BN³ = dL g₃³ (dL g₂³ (dL g₁³ (dW (tw 2) h₂ (B₀ _) (δ³ 1) zero) 0 zero) 0 zero) 0 zero

reach³ : cp 0 (cp 0 (cp 0 (ψ⊥ (tw 3) (B₀ _) (G0³ (δ³ 1))))) ≡ ψ⊥ (suc LN³) BN³ (Ωt (suc LN³))
reach³ = refl

stN³ : Tr LN³ → Tr LN³
stN³ z = ψs (suc LN³) BN³ LN³ (ins self) (up zero tt (suc z))

η³ : ℕ → Tr LN³
η³ = iter stN³ zero

η³-1 : η³ 1 ≡ next (Ωt LN³)
η³-1 = refl

c₀³ : Tr (tw 1)
c₀³ = suc (ι (tw 1) ω₀)

occP³ : Node (suc LN³) (up zero tt (suc (η³ 1))) (chL LN³ c₀³) (inj₁ (inj₁ tt))
occP³ = _ , inC (inS (inL 0 (inΩ c₀³ (inC here))))

limP³ : Σ (ℕ → L) λ f → at (chL LN³ c₀³) (inj₁ (inj₁ tt)) ≡ lim f
limP³ = _ , refl

couldP³ : Σ (Pos LN³) λ p → at LN³ p ≡ at (chL LN³ c₀³) (inj₁ (inj₁ tt))
couldP³ = inj₂ (c₀³ , inj₂ (inj₁ (inj₁ tt))) , refl

keptP³ : Node LN³ (η³ 2) (chL LN³ c₀³) (inj₁ (inj₁ tt))
keptP³ = _ , inL 0 (inL 0 (inΩ c₀³ (inC here)))

kept-branch³ : proj₁ keptP³ ≡ proj₁ occP³
kept-branch³ = refl

BN³-top : TopB (suc LN³) BN³
BN³-top = dL-top g₃³ _ (dL-top g₂³ _ (dL-top g₁³ _
  (dW-top (tw 2) h₂ (B₀ _) (TopB₀ _) (δ³ 1) zero tt) 0 zero tt) 0 zero tt) 0 zero tt

η³-top : (n : ℕ) → Top LN³ (η³ n)
η³-top = iterInv (Top LN³) stN³ zero tt
  (λ z hz → tops (suc LN³) BN³ BN³-top LN³ (ins self) (up zero tt (suc z)) (tt , hz))

src³-top : Top (suc LN³) (up zero tt (suc (η³ 1)))
src³-top = tt , η³-top 1
```
