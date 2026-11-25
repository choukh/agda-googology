# 累加的读回: 块的增量 (F3 原型)

> 判决: 成品候选 (块的增量). 读回 `↑ᶜ` 在 ℕ 极限处取部分和 (`cumₗ`), 相邻项之间的路径是 `⊑lift`, 对一切树全定义; 塔 `twᶜ`, `Λᶜ` 照 `tw`, `Λ` 只换读回.
> 编译定理, 无前提: 必带相邻路径的证据 `Req` 对塔各项与 `Λᶜ` 成立 (`Req-twᶜ`, `Req-Λᶜ`), 对照 `YiLimCheck.no-req`; 折叠用的路线 `Rtᶜ-tw` 由它得出, 处处是 `just`. 层号证据 `Ev-twᶜ` 照 `Ev-tw`.
> 不否定什么. 改的是层号的值 (见 `YiCumVal`). 折叠不改 (`YiLimFold`), 闭项合法在 `YiCumLegal`, 测试在 `YiCumCheck`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCumBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiLimBlock
```

## 读回与塔

`cumₗ s n = s 0 ⊕ … ⊕ s n`. 与 `↑` 不同的只有 ℕ 极限一行; 有限的树读回相同 (`YiCumCheck.fin-same`).

```agda
cumₗ : (ℕ → L) → ℕ → L
cumₗ s zero    = s zero
cumₗ s (suc n) = cumₗ s n ⊕ s (suc n)

mutual
  ↑ᶜ : (k : L) → Tr k → L
  ↑ᶜ k zero       = zero
  ↑ᶜ k (suc x)    = suc (↑ᶜ k x)
  ↑ᶜ k (lim f)    = lim (cumₗ (λ n → ↑ᶜ k (f n)))
  ↑ᶜ k (Ω p g)    = Ωₗ (at k p) (λ c → ↑ᶜ k (g (fromBr k p c)))
  ↑ᶜ k (up x c y) = ↑ᶜ k x ⊕ ↑ᶜch k c y

  ↑ᶜch : (k : L) (c : Ch k) → ChT k c → L
  ↑ᶜch (suc a)  _ y = ↑ᶜ a y
  ↑ᶜch (lim g)  n y = ↑ᶜ (g n) y
  ↑ᶜch (Ωₗ k h) c y = ↑ᶜ (h c) y

twᶜ : ℕ → L
twᶜ zero    = zero
twᶜ (suc n) = Ωₗ (twᶜ n) (λ c → twᶜ n ⊕ ↑ᶜ (twᶜ n) c)

Λᶜ : L
Λᶜ = lim twᶜ
```

## 必带路径的证据

`Req` 与 `YiLimCheck.Req` 同文 (那里是验收文件, 这里重写以免导入). `ReqP` 是偏移用的, 相邻路径取 `⊑` (在左加之下保持).

```agda
Req : L → Set
Req zero     = ⊤
Req (suc a)  = Req a
Req (lim g)  = ((n : ℕ) → Req (g n)) × Adj g
Req (Ωₗ k h) = Req k × ((c : Tr k) → Req (h c))

ReqP : L → Set
ReqP zero     = ⊤
ReqP (suc b)  = ReqP b
ReqP (lim g)  = ((n : ℕ) → ReqP (g n)) × AdjP g
ReqP (Ωₗ k h) = Req k × ((c : Tr k) → ReqP (h c))

Req⊕ : (a b : L) → Req a → ReqP b → Req (a ⊕ b)
Req⊕ a zero     ra rb        = ra
Req⊕ a (suc b)  ra rb        = Req⊕ a b ra rb
Req⊕ a (lim g)  ra (rb , r)  = (λ n → Req⊕ a (g n) ra (rb n)) , (λ n → ⊑→≤ (⊕⊑ a (r n)))
Req⊕ a (Ωₗ k h) ra (rk , rb) = rk , λ c → Req⊕ a (h c) ra (rb c)

ReqP⊕ : (b₁ b₂ : L) → ReqP b₁ → ReqP b₂ → ReqP (b₁ ⊕ b₂)
ReqP⊕ b₁ zero     r₁ r₂        = r₁
ReqP⊕ b₁ (suc b)  r₁ r₂        = ReqP⊕ b₁ b r₁ r₂
ReqP⊕ b₁ (lim g)  r₁ (r₂ , r)  = (λ n → ReqP⊕ b₁ (g n) r₁ (r₂ n)) , (λ n → ⊕⊑ b₁ (r n))
ReqP⊕ b₁ (Ωₗ k h) r₁ (rk , r₂) = rk , λ c → ReqP⊕ b₁ (h c) r₁ (r₂ c)

ReqP-cum : (s : ℕ → L) → ((n : ℕ) → ReqP (s n)) → (n : ℕ) → ReqP (cumₗ s n)
ReqP-cum s r zero    = r zero
ReqP-cum s r (suc n) = ReqP⊕ (cumₗ s n) (s (suc n)) (ReqP-cum s r n) (r (suc n))

AdjP-cum : (s : ℕ → L) → AdjP (cumₗ s)
AdjP-cum s n = ⊑lift (cumₗ s n) (s (suc n))

mutual
  Req-at : (ℓ : L) → Req ℓ → (p : Pos ℓ) → Req (at ℓ p)
  Req-at (suc a)  r        t              = Req-at⁼ a r t
  Req-at (lim g)  (r , _)  (n , t)        = Req-at⁼ (g n) (r n) t
  Req-at (Ωₗ k h) (rk , r) (inj₁ t)       = Req-at⁼ k rk t
  Req-at (Ωₗ k h) (rk , r) (inj₂ (c , t)) = Req-at⁼ (h c) (r c) t

  Req-at⁼ : (a : L) → Req a → (t : Pos⁼ a) → Req (at⁼ a t)
  Req-at⁼ a r (inj₁ _) = r
  Req-at⁼ a r (inj₂ p) = Req-at a r p
```

读回的偏移对一切树带路径: ℕ 极限处是 `AdjP-cum`, 不看树是否合法.

```agda
mutual
  ReqP↑ᶜ : (k : L) → Req k → (t : Tr k) → ReqP (↑ᶜ k t)
  ReqP↑ᶜ k r zero       = tt
  ReqP↑ᶜ k r (suc x)    = ReqP↑ᶜ k r x
  ReqP↑ᶜ k r (lim f)    =
    ReqP-cum (λ n → ↑ᶜ k (f n)) (λ n → ReqP↑ᶜ k r (f n)) , AdjP-cum (λ n → ↑ᶜ k (f n))
  ReqP↑ᶜ k r (Ω p g)    = Req-at k r p , λ c → ReqP↑ᶜ k r (g (fromBr k p c))
  ReqP↑ᶜ k r (up x c y) = ReqP⊕ (↑ᶜ k x) (↑ᶜch k c y) (ReqP↑ᶜ k r x) (ReqP↑ᶜch k r c y)

  ReqP↑ᶜch : (k : L) → Req k → (c : Ch k) (y : ChT k c) → ReqP (↑ᶜch k c y)
  ReqP↑ᶜch (suc a)  r       _ y = ReqP↑ᶜ a r y
  ReqP↑ᶜch (lim g)  (r , _) n y = ReqP↑ᶜ (g n) (r n) y
  ReqP↑ᶜch (Ωₗ k h) (_ , r) c y = ReqP↑ᶜ (h c) (r c) y

Req-twᶜ : (n : ℕ) → Req (twᶜ n)
Req-twᶜ zero    = tt
Req-twᶜ (suc n) = Req-twᶜ n , λ c →
  Req⊕ (twᶜ n) (↑ᶜ (twᶜ n) c) (Req-twᶜ n) (ReqP↑ᶜ (twᶜ n) (Req-twᶜ n) c)

Adj-Λᶜ : Adj twᶜ
Adj-Λᶜ n = ink self

Req-Λᶜ : Req Λᶜ
Req-Λᶜ = Req-twᶜ , Adj-Λᶜ
```

## 折叠用的路线与层号证据

```agda
Req→Rt : (ℓ : L) → Req ℓ → Rt ℓ
Req→Rt zero     r        = tt
Req→Rt (suc a)  r        = Req→Rt a r
Req→Rt (lim g)  (r , a)  = (λ n → Req→Rt (g n) (r n)) , just a
Req→Rt (Ωₗ k h) (rk , r) = Req→Rt k rk , λ c → Req→Rt (h c) (r c)

Rtᶜ-tw : (n : ℕ) → Rt (twᶜ n)
Rtᶜ-tw n = Req→Rt (twᶜ n) (Req-twᶜ n)

Rt-Λᶜ : Rt Λᶜ
Rt-Λᶜ = Req→Rt Λᶜ Req-Λᶜ

EvO-cum : (a : L) (s : ℕ → L) → ((n : ℕ) → EvO a (s n)) → (n : ℕ) → EvO a (cumₗ s n)
EvO-cum a s e zero    = e zero
EvO-cum a s e (suc n) = EvO⊕ a (cumₗ s n) (s (suc n)) (EvO-cum a s e n) (e (suc n))

mutual
  EvO↑ᶜ : (a k : L) → Ev k → k ≤ a → (t : Tr k) → EvO a (↑ᶜ k t)
  EvO↑ᶜ a k ek v zero       = tt
  EvO↑ᶜ a k ek v (suc x)    = EvO↑ᶜ a k ek v x
  EvO↑ᶜ a k ek v (lim f)    = EvO-cum a (λ n → ↑ᶜ k (f n)) (λ n → EvO↑ᶜ a k ek v (f n))
  EvO↑ᶜ a k ek v (Ω p g)    = posW k p ∙ v , Ev-at k ek p , λ c → EvO↑ᶜ a k ek v (g (fromBr k p c))
  EvO↑ᶜ a k ek v (up x c y) = EvO⊕ a (↑ᶜ k x) (↑ᶜch k c y) (EvO↑ᶜ a k ek v x) (EvO↑ᶜch a k ek v c y)

  EvO↑ᶜch : (a k : L) → Ev k → k ≤ a → (c : Ch k) (y : ChT k c) → EvO a (↑ᶜch k c y)
  EvO↑ᶜch a (suc k)  ek       v _ y = EvO↑ᶜ a k ek (ins self ∙ v) y
  EvO↑ᶜch a (lim g)  ek       v n y = EvO↑ᶜ a (g n) (ek n) (inl n self ∙ v) y
  EvO↑ᶜch a (Ωₗ k h) (_ , ek) v c y = EvO↑ᶜ a (h c) (proj₂ (ek c)) (inb c self ∙ v) y

Ev-twᶜ : (n : ℕ) → Ev (twᶜ n)
Ev-twᶜ zero    = tt
Ev-twᶜ (suc n) = Ev-twᶜ n , λ c →
  lift (twᶜ n) (↑ᶜ (twᶜ n) c) , Ev⊕ (twᶜ n) (↑ᶜ (twᶜ n) c) (Ev-twᶜ n) (EvO↑ᶜ (twᶜ n) (twᶜ n) (Ev-twᶜ n) self c)

Ev-Λᶜ : Ev Λᶜ
Ev-Λᶜ = Ev-twᶜ
```
