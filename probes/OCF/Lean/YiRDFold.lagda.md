# 换基 (目标层 ⊕ c): 折叠

> 定义候选 (换基), 未经作者采纳. 复制 `YiRWFold`, 只换 "Ω 形状层号, 目标经指定孩子 c′, 嵌入在孩子 c" 一行: `cmp` 从 `Ok` 的 `k ≤ h c′` 与目标路径读出 `k ≤ j` 时, 在 `j ⊕ ↑ k c` 上折该层的 Ω 树 (调用已定义的主线折叠 `YiRWFold.ψ`, 起点是左项 x 的折叠), 再 ⊞ 原来的回退项; 读不出时逐字是原来那一行 (`row-in`). 不改块, 不加证据字段.
> 编译定理, 无前提: 塔第 1 项上一切目标路径都读出 `k ≤ j` (`cmp-z`, `row-1`); 塔各项上目标路径停在偏移部分时读出 (`cmp-up`), 那一行就是换基的折叠 (`row-up`); 塔第 2 项起, 目标是第 0 层时 `k ≤ j` 不存在 (`no-kj`), 读不出 (`in-2`).
> 不否定什么; 不涉及值. 层号偏移在 `YiRDLvl`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRDFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; kp; node⁺; nodeLe)
import OCF.Lean.YiRWFold as R
open import OCF.Lean.YiAltCmp using (cM; cM-ind; cM-ind₂; cmp; Ok-≤)
```

## 折叠与单调

换基的一行调用 `R.ψ` 而不是正在定义的 ψ: 层号 `j ⊕ ↑ k c` 与树 `Ωt` 都不是结构上更小的; 调用同一个 ψ 的写法不过停机检查 (临时试验, 有限测试).

```agda
mutual
  ψ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
  ψ ℓ o B j w β zero      = β
  ψ ℓ o B j w β (suc x)   = next⁺ (ψ ℓ o B j w β x)
  ψ ℓ o B j w β (lim f a) = lim⁺ (λ n → ψ ℓ o B j w β (f n)) (λ n → mono ℓ o B j w β (a n))
  ψ ℓ o B j w β (Ω p g)   = node⁺ (kp ℓ o p w) (λ z → ψ ℓ o B j w β (g z))
    (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  ψ (nd s h) o B _ self β (up x c y e) = Up (h c) (down stop c) (ψ (nd s h) o B _ self β x) y
  ψ (nd s h) o B j (inu ws) β (up x c y e) =
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) y
  ψ (nd (sΩ k) h) o B j (ink v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o B j (ink v) β x) y
  ψ (nd sS h) o B j (inc c′ v) β (up x c y e) =
    ψ (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) y
  ψ (nd sL g) o B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → ψ (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
             (ψ (nd sL g) o B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → ψ (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
             (ψ (nd sL g) o B j (inc n v) β x) y)
  ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) = cM (cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v)
    (λ u → R.ψ (j ⊕ ↑ k c) (Ok⊕ j (↑ k c) (Ok-≤ (h c′) (proj₂ o c′) v) (OkO↑ j k (proj₁ (proj₁ o)) u c))
             (B₀ (j ⊕ ↑ k c)) j (lift j (↑ k c)) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (proj₁ (Ωt (j ⊕ ↑ k c)))
           ⊞ ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)
    (ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)

  mono : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o B j w β x) ◃ proj₁ (ψ ℓ o B j w β y)
  mono ℓ o B j w β ◃s           = ◃l zero
  mono ℓ o B j w β (◃l n)       = ◃l n
  mono ℓ o B j w β (◃w {p = p}) = nodeLe (kp ℓ o p w) _ _
  mono (nd s h) o B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) e
  mono (nd s h) o B j (inu ws) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) e
  mono (nd (sΩ k) h) o B j (ink v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o B j (ink v) β x) e
  mono (nd sS h) o B j (inc c′ v) β (◃u x c y e) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) e
  mono (nd sL g) o B j (inc n v) β (◃u x m y e) =
    cW-ind (λ Z → j ⊢ proj₁ (ψ (nd sL g) o B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → mono (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o B j (inc n v) β x) e)
  mono (nd (sΩ k) h) o B j (inc c′ v) β (◃u x c y e) =
    cM-ind (λ Z → j ⊢ proj₁ (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) ◃ proj₁ Z) (cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v)
      (λ u → ◃t (R.mono (j ⊕ ↑ k c) (Ok⊕ j (↑ k c) (Ok-≤ (h c′) (proj₂ o c′) v) (OkO↑ j k (proj₁ (proj₁ o)) u c))
                   (B₀ (j ⊕ ↑ k c)) j (lift j (↑ k c)) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (proj₂ (Ωt (j ⊕ ↑ k c))))
                (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))))
      (+-mono _ (ι-mono j (proj₂ (ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))
  mono (nd s h) o B _ self β (◃c x c d) = Upm (h c) (down stop c) (ψ (nd s h) o B _ self β x) d
  mono (nd s h) o B j (inu ws) β (◃c x c d) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ (nd s h) o B j (inu ws) β x) d
  mono (nd (sΩ k) h) o B j (ink v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ (nd (sΩ k) h) o B j (ink v) β x) d
  mono (nd sS h) o B j (inc c′ v) β (◃c x c d) =
    mono (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x) j v (ψ (nd sS h) o B j (inc c′ v) β x) d
  mono (nd sL g) o B j (inc n v) β (◃c x m d) =
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
      (λ u → mono (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ (nd sL g) o B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u d))
      (λ u → mono (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ (nd sL g) o B j (inc n v) β x) d)
  mono (nd (sΩ k) h) o B j (inc c′ v) β (◃c x c d) =
    cM-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v)
      (λ u → +-mono _ (ι-mono j (mono (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))
      (+-mono _ (ι-mono j (mono (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) d)))
  mono ℓ o B j w β (◃t d d′) = ◃t (mono ℓ o B j w β d) (mono ℓ o B j w β d′)
```

## 闭项

```agda
ψ₀ᵈ : (ℓ : L) → Ok ℓ → Tr ℓ → Tr⁺ zero
ψ₀ᵈ ℓ o = ψ ℓ o (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)

twᵈ : ℕ → Tr zero
twᵈ n = proj₁ (ψ₀ᵈ (tw n) (Ok-tw n) (proj₁ (Ωt (tw n))))

EBOᵈ : Tr zero
EBOᵈ = proj₁ (ψ₀ᵈ Λ Ok-Λ (proj₁ (Ωt Λ)))
```

## 塔上的证据 `k ≤ j`

`a ⊕ b` 里不经下标层侧、停在偏移部分的路径 `wk (⊕⊑ a u)` 对 `lift a b` 比较, 交出 `lift a b′`. 塔第 n+1 项的 `k ≤ h c′` 就是 `lift (tw n) (↑ (tw n) c′)`.

```agda
cmp-up : (a : L) {b′ b : L} (o : Ok (a ⊕ b)) (u : b′ ⊑ b) → cmp (a ⊕ b) o (lift a b) (wk (⊕⊑ a u)) ≡ just (lift a b′)
cmp-up a         o        self      = refl
cmp-up a         (_ , oc) (inc c u) = cmp-up a (oc c) u
cmp-up a {b = nd s h} (_ , oc) (inu us) = cmp-up a (oc (c₀ s)) (us (c₀ s))

no-kj : (n : ℕ) → tw (suc n) ≤ zero → ⊥
no-kj n ()
```

下标层是第 0 层时, 进 `zero ⊕ b` 的一切路径都读出 (经下标层侧的路径经证据搬回孩子, 按层号 b 递归).

```agda
cmp-z : (b : L) (o : Ok (zero ⊕ b)) {j : L} (v : j ≤ zero ⊕ b) → Σ (zero ≤ j) λ u → cmp (zero ⊕ b) o (lift zero b) v ≡ just u
cmp-z zero          o                 self      = self , refl
cmp-z (nd s h)      o                 self      = lift zero (nd s h) , refl
cmp-z (nd s h)      (_ , oc)          (inc c v) = cmp-z (h c) (oc c) v
cmp-z (nd s h)      (_ , oc)          (inu vs)  = cmp-z (h (c₀ s)) (oc (c₀ s)) (vs (c₀ s))
cmp-z (nd (sΩ k) h) ((_ , kh) , oc)   (ink v)   = cmp-z (h zero) (oc zero) (v ∙ kh zero)
```

塔上那一行: 读出时是换基的折叠, 读不出时是原来那一行.

```agda
cM-just : ∀ {A X : Set} {m : Maybe A} {a : A} (F : A → X) (d : X) → m ≡ just a → cM m F d ≡ F a
cM-just F d refl = refl

row-up : ∀ n (B : Base (tw (suc n))) c′ {b′ : L} (u : b′ ⊑ ↑ (tw n) c′) β x c y e
  → ψ (tw (suc n)) (Ok-tw (suc n)) B (tw n ⊕ b′) (inc c′ (wk (⊕⊑ (tw n) u))) β (up x c y e)
  ≡ R.ψ ((tw n ⊕ b′) ⊕ ↑ (tw n) c)
        (Ok⊕ (tw n ⊕ b′) (↑ (tw n) c) (Ok-≤ (tw n ⊕ ↑ (tw n) c′) (proj₂ (Ok-tw (suc n)) c′) (wk (⊕⊑ (tw n) u)))
             (OkO↑ (tw n ⊕ b′) (tw n) (Ok-tw n) (lift (tw n) b′) c))
        (B₀ ((tw n ⊕ b′) ⊕ ↑ (tw n) c)) (tw n ⊕ b′) (lift (tw n ⊕ b′) (↑ (tw n) c))
        (ψ (tw (suc n)) (Ok-tw (suc n)) B (tw n ⊕ b′) (inc c′ (wk (⊕⊑ (tw n) u))) β x)
        (proj₁ (Ωt ((tw n ⊕ b′) ⊕ ↑ (tw n) c)))
    ⊞ ψ₀ᵈ (tw n ⊕ ↑ (tw n) c) (proj₂ (Ok-tw (suc n)) c) y
row-up n B c′ u β x c y e = cM-just _ _ (cmp-up (tw n) (proj₂ (Ok-tw (suc n)) c′) u)

row-1 : ∀ (B : Base (tw 1)) j c′ (v : j ≤ zero ⊕ ↑ zero c′) β x c y e
  → ψ (tw 1) (Ok-tw 1) B j (inc c′ v) β (up x c y e)
  ≡ R.ψ (j ⊕ ↑ zero c)
        (Ok⊕ j (↑ zero c) (Ok-≤ (zero ⊕ ↑ zero c′) (proj₂ (Ok-tw 1) c′) v)
             (OkO↑ j zero tt (proj₁ (cmp-z (↑ zero c′) (proj₂ (Ok-tw 1) c′) v)) c))
        (B₀ (j ⊕ ↑ zero c)) j (lift j (↑ zero c)) (ψ (tw 1) (Ok-tw 1) B j (inc c′ v) β x) (proj₁ (Ωt (j ⊕ ↑ zero c)))
    ⊞ ψ₀ᵈ (zero ⊕ ↑ zero c) (proj₂ (Ok-tw 1) c) y
row-1 B j c′ v β x c y e = cM-just _ _ (proj₂ (cmp-z (↑ zero c′) (proj₂ (Ok-tw 1) c′) v))

row-in : ∀ k h (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v ≡ nothing
  → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) ≡ ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ₀ᵈ (h c) (proj₂ o c) y
row-in k h o B j c′ v β x c y e q rewrite q = refl
```

塔第 2 项的一例: 目标经孩子 3 直到第 0 层 (路径进了下标层 `tw 1`), 读不出.

```agda
n̂ : ℕ → Tr (tw 1)
n̂ zero    = zero
n̂ (suc n) = suc (n̂ n)

in-2 : cmp (tw 1 ⊕ ↑ (tw 1) (n̂ 3)) (proj₂ (Ok-tw 2) (n̂ 3)) (lift (tw 1) (↑ (tw 1) (n̂ 3))) (z≤ (tw 1 ⊕ ↑ (tw 1) (n̂ 3))) ≡ nothing
in-2 = refl
```
