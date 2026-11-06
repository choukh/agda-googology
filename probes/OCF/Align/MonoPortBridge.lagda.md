# 单调的移植 (一): 第 0 层的两种差树是同一种

> 不含记号. 入口 [MonoPort](MonoPort.lagda.md). `HtFeedTree.D hz` (高度树主线的第 0 层差树) 与 `SumOneTree.D azero` (`DValCanon.Gen` 写死的那一种) 构造子一样: `n0`, `n1`, `⨾`, `nl`, `nw`; 节点 `ni` 与 `nκ` 在两边都是空的 (层 $0$ 没有节点种类, `NZ` 是 $\bot$). 这里写两个方向的翻译 `toS`, `ofS`, 它们与构造子定义性地交换. 用处: [MonoPortZero](MonoPortZero.lagda.md) 把 `DValCanon.Gen` 的规范形论证**原样**用在高度树的折叠上, 不重抄那 200 行.
>
> - `toS`, `ofS`: 翻译. `ofS-pre`: 翻译与部分和交换 (命题相等, 对 $k$ 归纳, 不用外延性).
> - `sumT≤`, `sumT≥`: `sum` 在翻译下不变 (底可以变大).
> - `smono`: 高度树一侧 `sum` 对底与树的值单调. `toV`: 值的比较搬到 `SumOne` 一侧的 `toA`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPortBridge where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-refl; ≤-trans; ⊞-mono)
open import OCF.Align.HtFeedTree using (D; hz; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt)
import OCF.Align.SumOneTree as SO
open import OCF.Align.BrwMidZero using (toA; sum₀; sum-toA)
import OCF.Align.DValCanon as DC
```

## §1 翻译

```agda
toS : ∀ {V} → D hz V → SO.D azero V
toS n0 = SO.n0
toS n1 = SO.n1
toS (x ⨾ y) = toS x SO.⨾ toS y
toS (nl d) = SO.nl (λ n → toS (d n))
toS (ni () u)
toS (nκ () u)
toS (nw p x) = SO.nw p (toS x)

ofS : ∀ {V} → SO.D azero V → D hz V
ofS SO.n0 = n0
ofS SO.n1 = n1
ofS (x SO.⨾ y) = ofS x ⨾ ofS y
ofS (SO.nl d) = nl (λ n → ofS (d n))
ofS (SO.ni () u)
ofS (SO.nκ () u)
ofS (SO.nw p x) = nw p (ofS x)

-- 高度树一侧的部分和
preH : ∀ {V} → (ℕ → D hz V) → ℕ → D hz V
preH d zero = n0
preH d (suc k) = preH d k ⨾ d k

ofS-pre : ∀ {V} (d : ℕ → SO.D azero V) k → ofS (DC.pre d k) ≡ preH (λ n → ofS (d n)) k
ofS-pre d zero = refl
ofS-pre d (suc k) = cong (λ t → t ⨾ ofS (d k)) (ofS-pre d k)
```

## §2 和在翻译下不变

```agda
sumT≤ : ∀ {V b b′} → b ≤ b′ → (x : D hz V) → sum b x ≤ SO.sum b′ (toS x)
ptT≤  : ∀ {V b b′} → b ≤ b′ → (d : ℕ → D hz V) (n : ℕ) → pt b d n ≤ SO.pt b′ (λ m → toS (d m)) n
sumT≤ h n0 = h
sumT≤ h n1 = OCF.Align.TLRuleSpec.s≤ h
sumT≤ h (x ⨾ y) = sumT≤ (sumT≤ h x) y
sumT≤ h (nl d) = l≤ (λ n → ≤l n (ptT≤ h d n))
sumT≤ h (ni () u)
sumT≤ h (nκ () u)
sumT≤ h (nw p x) = sumT≤ h x
ptT≤ h d zero = h
ptT≤ h d (suc n) = sumT≤ (ptT≤ h d n) (d n)

sumT≥ : ∀ {V b b′} → b ≤ b′ → (x : D hz V) → SO.sum b (toS x) ≤ sum b′ x
ptT≥  : ∀ {V b b′} → b ≤ b′ → (d : ℕ → D hz V) (n : ℕ) → SO.pt b (λ m → toS (d m)) n ≤ pt b′ d n
sumT≥ h n0 = h
sumT≥ h n1 = OCF.Align.TLRuleSpec.s≤ h
sumT≥ h (x ⨾ y) = sumT≥ (sumT≥ h x) y
sumT≥ h (nl d) = l≤ (λ n → ≤l n (ptT≥ h d n))
sumT≥ h (ni () u)
sumT≥ h (nκ () u)
sumT≥ h (nw p x) = sumT≥ h x
ptT≥ h d zero = h
ptT≥ h d (suc n) = sumT≥ (ptT≥ h d n) (d n)
```

## §3 单调

```agda
val : ∀ {V} → D hz V → A
val x = sum azero x

-- 值的比较搬到 toA
toV : ∀ {V V′} (x : D hz V) (x′ : D hz V′) → val x ≤ val x′ → proj₁ (toA (toS x)) ≤ proj₁ (toA (toS x′))
toV x x′ le =
  ≤-trans (proj₂ (sum₀ (toS x))) (≤-trans (sumT≥ (≤-refl azero) x)
    (≤-trans le (≤-trans (sumT≤ (≤-refl azero) x′) (proj₁ (sum₀ (toS x′))))))

smono : ∀ {V V′} {b b′ : A} {x : D hz V} {x′ : D hz V′} → b ≤ b′ → val x ≤ val x′ → sum b x ≤ sum b′ x′
smono {b = b} {b′} {x} {x′} h hx =
  ≤-trans (sumT≤ (≤-refl b) x) (≤-trans (proj₁ (sum-toA b (toS x)))
    (≤-trans (⊞-mono h (toV x x′ hx)) (≤-trans (proj₂ (sum-toA b′ (toS x′))) (sumT≥ (≤-refl b′) x′))))
```
