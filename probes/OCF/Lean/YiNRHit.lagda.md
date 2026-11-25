# 那一行是否出现: 出现的谓词

> 检验文件 (不读记号), 不进成品; 树、折叠一行不改. `Hit P …` 与 `YiRWFold.ψ` 同样递归: 零处取底的出现 `Hβ`, 链只在保留判定为 `nothing` 时计入, 底只在被调用处计入 (`HB`), 到 "Ω 形状、目标经指定孩子 c′、树是嵌入 `up x c y e`" 那一行处取 `P k h j c′ c`; 见证就是从闭项到那一行的一条有限调用路径.
> 编译定理, 无前提: 塔第 n 项触发则第 n+1 项也触发 (`step`: 第 n+1 项顶层第一个和项的出现类型就是第 n 项的); 塔第 1 项对任何 `P` 都不触发 (`no-tw1`: 它的孩子层号没有 Ω 形状).
> 不否定什么; 只跟踪 `ψ` 自身的递归, 不跟踪 `mono` 与证明项里的计算. 实例在 `YiNRTw2`, `YiNREbo`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNRHit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
```

## 谓词

`HN`: 结点处保留则取某个分支, 否则取某一步的链元 `G` 或算出下一个链元的那次折叠 `C`. 自身行 (`self`) 的上折不调用 `ψ`, 只用左项的折叠.

```agda
cW₁ : ∀ {A B : Set} → A ⊎ B → (A → Set) → (B → Set) → Set
cW₁ (inj₁ a) F G = F a
cW₁ (inj₂ b) F G = G b

HN : ∀ {j X x₀} → Keep j X x₀ → (X → Set) → (X → X) → (X → Set) → Set
HN (just (q , cv , _)) G s C = Σ _ λ z → G (cv z)
HN {x₀ = x₀} nothing G s C = Σ ℕ λ n → G (iter s x₀ n) ⊎ C (iter s x₀ n)

Site : Set₁
Site = (k : L) → (Tr k → L) → (j : L) → Tr k → Tr k → Set

Hit : Site → (ℓ : L) → Ok ℓ → Base ℓ → ((i : L) → i ≤ ℓ → Set) → (j : L) → j ≤ ℓ → Tr⁺ j → Set → Tr ℓ → Set
Hit P ℓ o B HB j w β Hβ zero      = Hβ
Hit P ℓ o B HB j w β Hβ (suc x)   = Hit P ℓ o B HB j w β Hβ x
Hit P ℓ o B HB j w β Hβ (lim f a) = Σ ℕ λ n → Hit P ℓ o B HB j w β Hβ (f n)
Hit P ℓ o B HB j w β Hβ (Ω p g)   = HN (kp ℓ o p w) (λ z → Hit P ℓ o B HB j w β Hβ (g z))
  (λ z → fromBr ℓ p (proj₁ (ψ ℓ o B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g z))))
  (λ z → Hit P ℓ o B HB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (HB (at ℓ p) (posW ℓ p)) (g z))
Hit P (nd s h) o B HB _ self β Hβ (up x c y e) = Hit P (nd s h) o B HB _ self β Hβ x
Hit P (nd s h) o B HB j (inu ws) β Hβ (up x c y e) =
  Hit P (h c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd s h) o B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j (ws c) (ψ (nd s h) o B j (inu ws) β x) (Hit P (nd s h) o B HB j (inu ws) β Hβ x) y
Hit P (nd (sΩ k) h) o B HB j (ink v) β Hβ (up x c y e) =
  Hit P (h c) (proj₂ o c) (λ i u → ψ (nd (sΩ k) h) o B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd (sΩ k) h) o B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j (v ∙ proj₂ (proj₁ o) c) (ψ (nd (sΩ k) h) o B j (ink v) β x) (Hit P (nd (sΩ k) h) o B HB j (ink v) β Hβ x) y
Hit P (nd sS h) o B HB j (inc c′ v) β Hβ (up x c y e) =
  Hit P (h c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd sS h) o B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j v (ψ (nd sS h) o B j (inc c′ v) β x) (Hit P (nd sS h) o B HB j (inc c′ v) β Hβ x) y
Hit P (nd sL g) o B HB j (inc n v) β Hβ (up x m y e) = cW₁ (way g (proj₁ o) m n)
  (λ u → Hit P (g n) (proj₂ o n) (λ i u′ → ψ (nd sL g) o B i (inc n u′) (B i (inc n u′)) x)
           (λ i u′ → Hit P (nd sL g) o B HB i (inc n u′) (B i (inc n u′)) (HB i (inc n u′)) x) j v
           (ψ (nd sL g) o B j (inc n v) β x) (Hit P (nd sL g) o B HB j (inc n v) β Hβ x)
           (proj₁ (emb (g n) (proj₂ o n) u (y , e))))
  (λ u → Hit P (g m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x)
           (λ i u′ → Hit P (nd sL g) o B HB i (inc m u′) (B i (inc m u′)) (HB i (inc m u′)) x) j (v ∙ u)
           (ψ (nd sL g) o B j (inc n v) β x) (Hit P (nd sL g) o B HB j (inc n v) β Hβ x) y)
Hit P (nd (sΩ k) h) o B HB j (inc c′ v) β Hβ (up x c y e) = P k h j c′ c

HitTw : Site → ℕ → Set
HitTw P n = Hit P (tw n) (Ok-tw n) (B₀ (tw n)) (λ _ _ → ⊥) zero (z≤ (tw n)) (Ωt zero) ⊥ (proj₁ (Ωt (tw n)))

HitΛ : Site → Set
HitΛ P = Hit P Λ Ok-Λ (B₀ Λ) (λ _ _ → ⊥) zero (z≤ Λ) (Ωt zero) ⊥ (proj₁ (Ωt Λ))

step : (P : Site) (n : ℕ) → HitTw P n → HitTw P (suc n)
step P n h = 0 , inj₁ h
```

## 塔第 1 项不触发

层号里没有 Ω 形状 (`NoΩ`) 时, 出现只能来自底的出现或某次底的调用 (`noHit`).

```agda
NoΩ : L → Set
NoΩ zero          = ⊤
NoΩ (nd sS h)     = (c : ⊤) → NoΩ (h c)
NoΩ (nd sL g)     = (n : ℕ) → NoΩ (g n)
NoΩ (nd (sΩ k) h) = ⊥

chN : (s : Sh) (h : Ch s → L) → NoΩ (nd s h) → (c : Ch s) → NoΩ (h c)
chN sS     h n c = n c
chN sL     h n c = n c
chN (sΩ k) h () c

Out : (ℓ : L) → ((i : L) → i ≤ ℓ → Set) → Set → Set
Out ℓ HB Hβ = Hβ ⊎ Σ L λ i → Σ (i ≤ ℓ) (HB i)

lo : ∀ {ℓ HB Hβ i u} → Out ℓ HB (HB i u) → Out ℓ HB Hβ
lo {i = i} {u} (inj₁ b) = inj₂ (i , u , b)
lo (inj₂ r) = inj₂ r

eo : ∀ {ℓ HB Hβ} {R : Set} → Out ℓ HB Hβ → (Hβ → R) → ((i : L) (u : i ≤ ℓ) → HB i u → R) → R
eo (inj₁ b)           f g = f b
eo (inj₂ (i , u , b)) f g = g i u b

hn : ∀ {j X x₀} (m : Keep j X x₀) {G : X → Set} {s : X → X} {C : X → Set} {R : Set}
   → ((z : X) → G z → R) → ((z : X) → C z → R) → HN m G s C → R
hn (just (q , cv , _)) fG fC (z , h)      = fG (cv z) h
hn nothing             fG fC (n , inj₁ h) = fG _ h
hn nothing             fG fC (n , inj₂ h) = fC _ h

cw : ∀ {A B : Set} (W : A ⊎ B) {F : A → Set} {G : B → Set} {R : Set}
   → ((a : A) → F a → R) → ((b : B) → G b → R) → cW₁ W F G → R
cw (inj₁ a) fF fG h = fF a h
cw (inj₂ b) fF fG h = fG b h

noHit : (P : Site) (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (B : Base ℓ) (HB : (i : L) → i ≤ ℓ → Set) (j : L) (w : j ≤ ℓ)
      → (β : Tr⁺ j) (Hβ : Set) (x : Tr ℓ) → Hit P ℓ o B HB j w β Hβ x → Out ℓ HB Hβ
noHit P ℓ n o B HB j w β Hβ zero      h       = inj₁ h
noHit P ℓ n o B HB j w β Hβ (suc x)   h       = noHit P ℓ n o B HB j w β Hβ x h
noHit P ℓ n o B HB j w β Hβ (lim f a) (m , h) = noHit P ℓ n o B HB j w β Hβ (f m) h
noHit P ℓ n o B HB j w β Hβ (Ω p g)   h       = hn (kp ℓ o p w)
  (λ z h′ → noHit P ℓ n o B HB j w β Hβ (g z) h′)
  (λ z h′ → lo (noHit P ℓ n o B HB (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (HB (at ℓ p) (posW ℓ p)) (g z) h′)) h
noHit P (nd s h) n o B HB _ self β Hβ (up x c y e) r = noHit P (nd s h) n o B HB _ self β Hβ x r
noHit P (nd s h) n o B HB j (inu ws) β Hβ (up x c y e) r =
  eo (noHit P (h c) (chN s h n c) (proj₂ o c) (λ i u → ψ (nd s h) o B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd s h) o B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j (ws c) (ψ (nd s h) o B j (inu ws) β x) (Hit P (nd s h) o B HB j (inu ws) β Hβ x) y r)
    (λ b → noHit P (nd s h) n o B HB j (inu ws) β Hβ x b)
    (λ i u hb → lo (noHit P (nd s h) n o B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x hb))
noHit P (nd (sΩ k) h) () o B HB j (ink v) β Hβ (up x c y e) r
noHit P (nd sS h) n o B HB j (inc c′ v) β Hβ (up x c y e) r =
  eo (noHit P (h c) (n c) (proj₂ o c) (λ i u → ψ (nd sS h) o B i (inc c u) (B i (inc c u)) x)
      (λ i u → Hit P (nd sS h) o B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x)
      j v (ψ (nd sS h) o B j (inc c′ v) β x) (Hit P (nd sS h) o B HB j (inc c′ v) β Hβ x) y r)
    (λ b → noHit P (nd sS h) n o B HB j (inc c′ v) β Hβ x b)
    (λ i u hb → lo (noHit P (nd sS h) n o B HB i (inc c u) (B i (inc c u)) (HB i (inc c u)) x hb))
noHit P (nd sL g) n o B HB j (inc m v) β Hβ (up x m′ y e) r = cw (way g (proj₁ o) m′ m)
  (λ u r′ → eo (noHit P (g m) (n m) (proj₂ o m) (λ i u′ → ψ (nd sL g) o B i (inc m u′) (B i (inc m u′)) x)
           (λ i u′ → Hit P (nd sL g) o B HB i (inc m u′) (B i (inc m u′)) (HB i (inc m u′)) x) j v
           (ψ (nd sL g) o B j (inc m v) β x) (Hit P (nd sL g) o B HB j (inc m v) β Hβ x)
           (proj₁ (emb (g m) (proj₂ o m) u (y , e))) r′)
     (λ b → noHit P (nd sL g) n o B HB j (inc m v) β Hβ x b)
     (λ i u′ hb → lo (noHit P (nd sL g) n o B HB i (inc m u′) (B i (inc m u′)) (HB i (inc m u′)) x hb)))
  (λ u r′ → eo (noHit P (g m′) (n m′) (proj₂ o m′) (λ i u′ → ψ (nd sL g) o B i (inc m′ u′) (B i (inc m′ u′)) x)
           (λ i u′ → Hit P (nd sL g) o B HB i (inc m′ u′) (B i (inc m′ u′)) (HB i (inc m′ u′)) x) j (v ∙ u)
           (ψ (nd sL g) o B j (inc m v) β x) (Hit P (nd sL g) o B HB j (inc m v) β Hβ x) y r′)
     (λ b → noHit P (nd sL g) n o B HB j (inc m v) β Hβ x b)
     (λ i u′ hb → lo (noHit P (nd sL g) n o B HB i (inc m′ u′) (B i (inc m′ u′)) (HB i (inc m′ u′)) x hb))) r
noHit P (nd (sΩ k) h) () o B HB j (inc c′ v) β Hβ (up x c y e) r

noΩ↑ : (c : Tr zero) → NoΩ (zero ⊕ ↑ zero c)
noΩ↑ zero      = tt
noΩ↑ (suc x)   = λ _ → noΩ↑ x
noΩ↑ (lim f a) = λ n → noΩ↑ (f n)
noΩ↑ (Ω () g)
noΩ↑ (up x () y e)
```

塔第 1 项: 顶层结点不保留; 链元与和项都是嵌入 `up zero z …`, 进孩子层 `0 ⊕ ↑ 0 z` 之后底与底的出现都是 `⊥`.

```agda
h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

B₁′ : (z : Tr zero) → Base (tw 1) → Base (h₁ z)
B₁′ z B i u = ψ (tw 1) (Ok-tw 1) B i (inc z u) (B i (inc z u)) zero

HB₁′ : Site → (z : Tr zero) → (i : L) → i ≤ h₁ z → Set
HB₁′ P z i u = Hit P (tw 1) (Ok-tw 1) (B₀ (tw 1)) (λ _ _ → ⊥) i (inc z u) (B₀ (tw 1) i (inc z u)) ⊥ zero

kill : ∀ {ℓ} {HB : (i : L) → i ≤ ℓ → Set} → ((i : L) (u : i ≤ ℓ) → HB i u → ⊥) → Out ℓ HB ⊥ → ⊥
kill k (inj₁ ())
kill k (inj₂ (i , u , b)) = k i u b

no-sum : (P : Site) (z : Tr zero)
       → Hit P (tw 1) (Ok-tw 1) (B₀ (tw 1)) (λ _ _ → ⊥) zero (z≤ (tw 1)) (Ωt zero) ⊥
             (proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z)))) → ⊥
no-sum P z r = kill (λ i u ()) (noHit P (h₁ z) (noΩ↑ z) (proj₂ (Ok-tw 1) z) (B₁′ z (B₀ (tw 1))) (HB₁′ P z) zero
  (z≤ (h₁ z)) (ψ (tw 1) (Ok-tw 1) (B₀ (tw 1)) zero (z≤ (tw 1)) (Ωt zero) zero) ⊥ (proj₁ (Ωt (h₁ z))) r)

no-chain : (P : Site) (z : Tr zero)
         → Hit P (tw 1) (Ok-tw 1) (B₀ (tw 1)) (λ _ _ → ⊥) zero (ink self) (B₀ (tw 1) zero (ink self)) ⊥
               (proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z)))) → ⊥
no-chain P z r = kill (λ i u ()) (noHit P (h₁ z) (noΩ↑ z) (proj₂ (Ok-tw 1) z) (B₁′ z (B₀ (tw 1))) (HB₁′ P z) zero
  _ (ψ (tw 1) (Ok-tw 1) (B₀ (tw 1)) zero (ink self) (B₀ (tw 1) zero (ink self)) zero) ⊥ (proj₁ (Ωt (h₁ z))) r)

no-tw1 : (P : Site) → HitTw P 1 → ⊥
no-tw1 P (n , inj₁ r) = no-sum P _ r
no-tw1 P (n , inj₂ r) = no-chain P _ r
```
