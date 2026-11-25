# 完整候选折叠: 保留行接换基路径, 换基行, 替身内部递归到同一个折叠

> 判决: 定义候选, 不替换主线, 不读记号; 合法性是类型, `mono` 保持第一位置. 与 `YiBSFold` 的三处不同: 保留判定 `kp` 带证据, 下标侧槽位、目标经指定孩子且 `route` 给 "地板 ≤ 目标" 时用 `YiCMCross.keepS` 的路径; 嵌入行同 `YiBSFold` 的换基行; 替身 `seen` 调用本折叠自己 (证据 `rb-row`), 不用 `rb-no`.
> 停机: 不带参数的互递归写法不过停机检查 (有限测试, 一种写法); 这里加一个自然数 d, 只在进替身时减一, d = 0 时那一行回退. 所以是一族折叠 `ψ d`, 第 d 个在替身里用第 d − 1 个.
> 不否定什么; 没有值的定理. 闭项 `closed d n`, `EBOᶜ d` 在文末. 来源: 行与 `mono` 搬自 `YiBSFold` (加参数 d 与证据), `kp` 搬自 `YiRWFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUFFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; node⁺; nodeLe)
open import OCF.Lean.YiRBSib using (rb; rb-ind; rb-ind₂)
open import OCF.Lean.YiBSBase using (Schema; floor; offsets; ok-offsets; route; back; raiseO; downOk)
open import OCF.Lean.YiCMCross using (keepS)
open import OCF.Lean.YiUFBase
```

## 保留判定

与 `YiRWFold.kp` 逐行相同, 只有 "Ω 形状, 下标侧槽位, 目标经指定孩子" 一行不同: 有 `Schema` 且 `route` 给 `inj₂ u` (地板 ≤ 目标) 时取 `keepS S t u`; 其余 (无 `Schema`, 或目标在地板之下) 是原来的推进. `route` 只读目标路径, 不读孩子下标.

```agda
mutual
  kp : (ℓ : L) → Ok ℓ → Rb ℓ → (p : Pos ℓ) → ∀ {j} → j ≤ ℓ → Keep j (Br ℓ p) (fromBr ℓ p zero)
  kp ℓ             o               r        p              self      = just (p , (λ z → z) , refl)
  kp (nd s h)      (_ , oc)        (_ , rc) (inj₂ (c , t)) (inu vs)  = kp⁼ (h c) (oc c) (rc c) t (vs c)
  kp (nd (sΩ k) h) ((_ , kh) , oc) (_ , rc) (inj₂ (c , t)) (ink v)   = kp⁼ (h c) (oc c) (rc c) t (v ∙ kh c)
  kp (nd sS h)     (_ , oc)        (_ , rc) (inj₂ (c , t)) (inc _ v) = kp⁼ (h c) (oc c) (rc c) t v
  kp (nd sL g)     (r , oc)        (_ , rc) (inj₂ (m , t)) (inc n v) =
    cW (way g r m n) (λ u → mapK (pshBr u t) (pshFirst u t) (kp⁼ (g n) (oc n) (rc n) (psh u t) v))
                     (λ u → kp⁼ (g m) (oc m) (rc m) t (v ∙ u))
  kp (nd (sΩ k) h) _               _        (inj₂ _)       (inc _ _) = nothing
  kp (nd (sΩ k) h) ((ok , _) , _)  ((rk , _) , _) (inj₁ t) (ink v)   = kp⁼ k ok rk t v
  kp (nd (sΩ k) h) ((_ , kh) , oc) ((_ , m) , rc) (inj₁ t) (inc c v) = rb m
    (λ S → cW (route S _ c v)
      (λ _ → mapK (pshBr (kh c) t) (pshFirst (kh c) t) (kp⁼ (h c) (oc c) (rc c) (psh (kh c) t) v))
      (λ u → keepS S t u))
    (mapK (pshBr (kh c) t) (pshFirst (kh c) t) (kp⁼ (h c) (oc c) (rc c) (psh (kh c) t) v))
  kp (nd (sΩ k) h) ((_ , kh) , oc) (_ , rc) (inj₁ t)       (inu vs)  =
    mapK (pshBr (kh zero) t) (pshFirst (kh zero) t) (kp⁼ (h zero) (oc zero) (rc zero) (psh (kh zero) t) (vs zero))

  kp⁼ : (a : L) → Ok a → Rb a → (t : Pos⁼ a) → ∀ {j} → j ≤ a → Keep j (Br⁼ a t) (bz⁼ a t)
  kp⁼ a o r (inj₁ _) w = nothing
  kp⁼ a o r (inj₂ p) w = kp a o r p w

```

## 折叠与单调

d 只在换基行进替身时减一 (`seen d` 在 `ψ (suc d)` 里); 其余各行 d 不变. `seen` 的层号 `j ⊕ offsets S c` 不是结构上的孩子, 停机靠 d.

```agda
mutual
  seen : ℕ → ∀ {k h} (S : Schema k h) (j : L) → Ok j → Rb j → floor S ≤ j → Tr⁺ j → Tr k → Tr⁺ j
  seen-step : ∀ d {k h} (S : Schema k h) j oj rj u β c → j ⊢ proj₁ β ◃ proj₁ (seen d S j oj rj u β c)
  ψ : ℕ → (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j
  ψ d ℓ o r B j w β zero      = β
  ψ d ℓ o r B j w β (suc x)   = next⁺ (ψ d ℓ o r B j w β x)
  ψ d ℓ o r B j w β (lim f a) = lim⁺ (λ n → ψ d ℓ o r B j w β (f n)) (λ n → mono d ℓ o r B j w β (a n))
  ψ d ℓ o r B j w β (Ω p g)   = node⁺ (kp ℓ o r p w) (λ z → ψ d ℓ o r B j w β (g z))
    (λ z → fromBr ℓ p (proj₁ (ψ d ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  ψ d (nd s h) o r B _ self β (up x c y e) = Up (h c) (down stop c) (ψ d (nd s h) o r B _ self β x) y
  ψ d (nd s h) o r B j (inu ws) β (up x c y e) =
    ψ d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ d (nd s h) o r B j (inu ws) β x) y
  ψ d (nd (sΩ k) h) o r B j (ink v) β (up x c y e) =
    ψ d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ d (nd (sΩ k) h) o r B j (ink v) β x) y
  ψ d (nd sS h) o r B j (inc c′ v) β (up x c y e) =
    ψ d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ d (nd sS h) o r B j (inc c′ v) β x) y
  ψ d (nd sL g) o r B j (inc n v) β (up x m y e) = cW (way g (proj₁ o) m n)
    (λ u → ψ d (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ d (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
             (ψ d (nd sL g) o r B j (inc n v) β x) (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
    (λ u → ψ d (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ d (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
             (ψ d (nd sL g) o r B j (inc n v) β x) y)
  ψ zero (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) =
    ψ zero (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ zero (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
  ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e) = rb (proj₂ (proj₁ r))
    (λ S → cW (route S j c′ v)
      (λ u → ψ (suc d) (h c) (proj₂ o c) (proj₂ r c)
        (λ i u′ → ψ (suc d) (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
        (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
      (λ u → seen d S j (downOk (h c′) (proj₂ o c′) j v) (rb≤ (h c′) (proj₂ r c′) v) u
        (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) c
        ⊞ ψ (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))
    (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)

  mono : ∀ d (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ}
       → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ d ℓ o r B j w β x) ◃ proj₁ (ψ d ℓ o r B j w β y)
  mono d ℓ o r B j w β ◃s           = ◃l zero
  mono d ℓ o r B j w β (◃l n)       = ◃l n
  mono d ℓ o r B j w β (◃w {p = p}) = nodeLe (kp ℓ o r p w) _ _
  mono d (nd s h) o r B _ self β (◃u x c y e) = Upm (h c) (down stop c) (ψ d (nd s h) o r B _ self β x) e
  mono d (nd s h) o r B j (inu ws) β (◃u x c y e) =
    mono d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ d (nd s h) o r B j (inu ws) β x) e
  mono d (nd (sΩ k) h) o r B j (ink v) β (◃u x c y e) =
    mono d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ d (nd (sΩ k) h) o r B j (ink v) β x) e
  mono d (nd sS h) o r B j (inc c′ v) β (◃u x c y e) =
    mono d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ d (nd sS h) o r B j (inc c′ v) β x) e
  mono d (nd sL g) o r B j (inc n v) β (◃u x m y e) =
    cW-ind (λ Z → j ⊢ proj₁ (ψ d (nd sL g) o r B j (inc n v) β x) ◃ proj₁ Z) (way g (proj₁ o) m n)
      (λ u → mono d (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ d (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ d (nd sL g) o r B j (inc n v) β x) (proj₂ (emb (g n) (proj₂ o n) u (y , e))))
      (λ u → mono d (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ d (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ d (nd sL g) o r B j (inc n v) β x) e)
  mono zero (nd (sΩ k) h) o r B j (inc c′ v) β (◃u x c y e) =
    +-mono _ (ι-mono j (proj₂ (ψ zero (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)))
  mono (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β (◃u x c y e) =
    rb-ind (λ Z → j ⊢ proj₁ (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (proj₂ (proj₁ r))
      (λ S → cW-ind (λ Z → j ⊢ proj₁ (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) ◃ proj₁ Z) (route S j c′ v)
        (λ u → mono (suc d) (h c) (proj₂ o c) (proj₂ r c)
          (λ i u′ → ψ (suc d) (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
          (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) e)
        (λ u → ◃t (seen-step d S j (downOk (h c′) (proj₂ o c′) j v) (rb≤ (h c′) (proj₂ r c′) v) u
          (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) c)
          (+-mono _ (ι-mono j (proj₂ (ψ (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))))
      (+-mono _ (ι-mono j (proj₂ (ψ (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y))))

  mono d (nd s h) o r B _ self β (◃c x c q) = Upm (h c) (down stop c) (ψ d (nd s h) o r B _ self β x) q
  mono d (nd s h) o r B j (inu ws) β (◃c x c q) =
    mono d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c) (ψ d (nd s h) o r B j (inu ws) β x) q
  mono d (nd (sΩ k) h) o r B j (ink v) β (◃c x c q) =
    mono d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd (sΩ k) h) o r B i (inc c u) (B i (inc c u)) x) j (v ∙ proj₂ (proj₁ o) c)
      (ψ d (nd (sΩ k) h) o r B j (ink v) β x) q
  mono d (nd sS h) o r B j (inc c′ v) β (◃c x c q) =
    mono d (h c) (proj₂ o c) (proj₂ r c) (λ i u → ψ d (nd sS h) o r B i (inc c u) (B i (inc c u)) x) j v (ψ d (nd sS h) o r B j (inc c′ v) β x) q
  mono d (nd sL g) o r B j (inc n v) β (◃c x m q) =
    cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (way g (proj₁ o) m n)
      (λ u → mono d (g n) (proj₂ o n) (proj₂ r n) (λ i u′ → ψ d (nd sL g) o r B i (inc n u′) (B i (inc n u′)) x) j v
               (ψ d (nd sL g) o r B j (inc n v) β x) (emb-mono (g n) (proj₂ o n) u q))
      (λ u → mono d (g m) (proj₂ o m) (proj₂ r m) (λ i u′ → ψ d (nd sL g) o r B i (inc m u′) (B i (inc m u′)) x) j (v ∙ u)
               (ψ d (nd sL g) o r B j (inc n v) β x) q)
  mono zero (nd (sΩ k) h) o r B j (inc c′ v) β (◃c x c q) =
    +-mono _ (ι-mono j (mono zero (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) q))
  mono (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β (◃c x c q) =
    rb-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (proj₂ (proj₁ r))
      (λ S → cW-ind₂ (λ Z Z′ → j ⊢ proj₁ Z ◃ proj₁ Z′) (route S j c′ v)
        (λ u → mono (suc d) (h c) (proj₂ o c) (proj₂ r c)
          (λ i u′ → ψ (suc d) (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x) j (back S c u)
          (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) q)
        (λ u → +-mono _ (ι-mono j (mono (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) q))))
      (+-mono _ (ι-mono j (mono (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) q)))

  mono d ℓ o r B j w β (◃t q q′) = ◃t (mono d ℓ o r B j w β q) (mono d ℓ o r B j w β q′)

  seen d S j oj rj u β c = ψ d (j ⊕ offsets S c)
    (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
    (rbO j (offsets S c) rj oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
    (B₀ _) j (lift j (offsets S c)) β (proj₁ (Ωt (j ⊕ offsets S c)))

  seen-step d S j oj rj u β c = mono d (j ⊕ offsets S c)
    (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
    (rbO j (offsets S c) rj oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
    (B₀ _) j (lift j (offsets S c)) β (proj₂ (Ωt (j ⊕ offsets S c)))
```

## 闭项

塔各项与 EBO, 对每个 d; 合法性是类型.

```agda
ψ₀ : ℕ → (ℓ : L) → Ok ℓ → Rb ℓ → Tr ℓ → Tr⁺ zero
ψ₀ d ℓ o r = ψ d ℓ o r (B₀ ℓ) zero (z≤ ℓ) (Ωt zero)
closed : ℕ → (n : ℕ) → Tr⁺ zero
closed d n = ψ₀ d (tw n) (Ok-tw n) (rb-tw n) (proj₁ (Ωt (tw n)))
EBOᶜ : ℕ → Tr⁺ zero
EBOᶜ d = ψ₀ d Λ Ok-Λ rb-Λ (proj₁ (Ωt Λ))
```
