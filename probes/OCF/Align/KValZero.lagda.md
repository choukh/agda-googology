# `nκ` 的值语义 (三): 第 0 层输入, 跨世界

> 不含记号. 入口 [KVal](KVal.lagda.md). [DValZero](DValZero.lagda.md) 的跨世界版: 两边各带自己的世界 $W$, 路径 `kW`, 动作与它的路径一致证明 (下标 `S₀`). 证明逐条照 `DValZero` 搬, 只多两件: 状态带路径一致 (`CohY`), 新状态的一致由 `KValSem.coh₀` 给出. 规范形一段照旧套 [DValCanon](DValCanon.lagda.md) 的 `Gen`, 下标取 `S₀`.
>
> 用处: 第 1 层的 `ni` 在两边不同世界里上升 (`nκ` 的两个格), 两条链各用自己世界里的动作.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValZero where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲; ⊲-tr; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_; ⊞-mono; ⊞-asso; ⊞-assoʳ)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; cnt)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (toA; sum₀; sum-toA; z⊞; pts)
open import OCF.Align.DValCanon using (pre; module Gen)
open import OCF.Align.KValTree using (V0)
open import OCF.Align.KValSem
```

## §1 下标, 值, 关系

```agda
ac₀ : F.AccY (cnt azero)
ac₀ = F.accCn azero

record S₀ : Set where
  constructor s0
  field
    W₀  : A
    lW₀ : Lg W₀
    kW₀ : azero ⊲ W₀
    act : F.Ig (cnt azero) W₀
    coh : CohA act
open S₀ public

vY₀ : (i : S₀) → F.St (W₀ i) → A
vY₀ i Y = vYk (kW₀ i) Y

Rn : (i : S₀) → ∀ {V} → D azero V → V ⊲ W₀ i → D azero (W₀ i) → F.St (W₀ i) → F.Df (W₀ i)
Rn i z q w Y = F.Run ac₀ z q (lW₀ i) (kW₀ i) (act i) w Y

Ob : (i : S₀) → A → ∀ {V} → D azero V → V ⊲ W₀ i → D azero (W₀ i) → F.St (W₀ i) → A
Ob i c z q w Y = sum c (F.yc (Rn i z q w Y) (inj₁ (kW₀ i)) tt)

cR : (i : S₀) → ∀ {V} (z : D azero V) (q : V ⊲ W₀ i) w Y → CohY Y → CohY (Y F.⊕ Rn i z q w Y)
cR i z q w Y cY = coh⊕ cY (coh₀ ac₀ z q (lW₀ i) (kW₀ i) (act i) w Y (coh i) cY)

HAᶜ : S₀ → S₀ → Set
HAᶜ i j = ∀ w w′ c c′ Y Y′ → CohY Y → CohY Y′ → val w ≤ val w′ → c ≤ c′ → vY₀ i Y ≤ vY₀ j Y′ →
          sum c (F.yc (act i C.self (lW₀ i) w Y) (inj₁ (kW₀ i)) tt) ≤ sum c′ (F.yc (act j C.self (lW₀ j) w′ Y′) (inj₁ (kW₀ j)) tt)

OutLe : S₀ → S₀ → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
OutLe i j z z′ = ∀ q q′ w w′ c c′ Y Y′ → CohY Y → CohY Y′ → val w ≤ val w′ → c ≤ c′ → vY₀ i Y ≤ vY₀ j Y′ →
                 Ob i c z q w Y ≤ Ob j c′ z′ q′ w′ Y′

Rl : S₀ → S₀ → ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
Rl i j z z′ = OutLe i j z z′ × (V0 z ≤ V0 z′)

ptsV : ∀ {V₁ V₂} (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) → (∀ n → V0 (d n) ≤ V0 (d′ n)) →
       ∀ k → proj₁ (pts (azero , tt) (λ n → toA (d n)) k) ≤ proj₁ (pts (azero , tt) (λ n → toA (d′ n)) k)
ptsV d d′ h zero = ≤-refl azero
ptsV d d′ h (suc k) = ⊞-mono (ptsV d d′ h k) (h k)

preV : ∀ {V₁ V₂} (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) → (∀ n → V0 (d n) ≤ V0 (d′ n)) →
       ∀ k → V0 (pre d k) ≤ proj₁ (pts (azero , tt) (λ n → toA (d′ n)) k)
preV d d′ h zero = ≤-refl azero
preV d d′ h (suc k) = ⊞-mono (preV d d′ h k) (h k)

preV′ : ∀ {V₁ V₂} (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) → (∀ n → V0 (d n) ≤ V0 (d′ n)) →
        ∀ k → proj₁ (pts (azero , tt) (λ n → toA (d n)) k) ≤ V0 (pre d′ k)
preV′ d d′ h zero = ≤-refl azero
preV′ d d′ h (suc k) = ⊞-mono (preV′ d d′ h k) (h k)
```

## §2 结构律

```agda
module _ {i j : S₀} where
  ⨾-mono : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → Rl i j x x′ → Rl i j y y′ → Rl i j (x ⨾ y) (x′ ⨾ y′)
  ⨾-mono {x = x} {x′ = x′} (hx , ax) (hy , ay) =
    (λ q q′ w w′ b b′ Y Y′ cY cY′ c cb r →
      hy q q′ _ _ _ _ _ _ (cR i x q w Y cY) (cR j x′ q′ w′ Y′ cY′) (smono c ax)
         (hx q q′ w w′ b b′ Y Y′ cY cY′ c cb r) (hx q q′ w w′ _ _ Y Y′ cY cY′ c r r)) ,
    ⊞-mono ax ay

  nl-mono : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → Rl i j (d n) (d′ n)) → Rl i j (nl d) (nl d′)
  nl-mono {d = d} {d′} h = O , l≤ (λ n → ≤l n (ptsV d d′ (λ m → proj₂ (h m)) n))
    where
    O : OutLe i j (nl d) (nl d′)
    O q q′ w w′ b b′ Y Y′ cY cY′ c cb r = l≤ (λ n → ≤l n (proj₁ (proj₂ (go n))))
      where
      P = λ n → F.Rpt ac₀ d q (lW₀ i) (kW₀ i) (act i) w Y n
      P′ = λ n → F.Rpt ac₀ d′ q′ (lW₀ j) (kW₀ j) (act j) w′ Y′ n
      go : ∀ n → (val (proj₁ (P n)) ≤ val (proj₁ (P′ n))) ×
                 ((pt b (λ m → F.yc (Rn i (d m) q (proj₁ (P m)) (proj₂ (P m))) (inj₁ (kW₀ i)) tt) n ≤
                   pt b′ (λ m → F.yc (Rn j (d′ m) q′ (proj₁ (P′ m)) (proj₂ (P′ m))) (inj₁ (kW₀ j)) tt) n) ×
                  ((vY₀ i (proj₂ (P n)) ≤ vY₀ j (proj₂ (P′ n))) × (CohY (proj₂ (P n)) × CohY (proj₂ (P′ n)))))
      go zero = c , (cb , (r , (cY , cY′)))
      go (suc n) = let (gc , (gb , (gs , (g1 , g2)))) = go n in
        smono gc (proj₂ (h n)) ,
        (proj₁ (h n) q q′ _ _ _ _ _ _ g1 g2 gc gb gs ,
         (proj₁ (h n) q q′ _ _ _ _ _ _ g1 g2 gc gs gs ,
          (cR i (d n) q _ _ g1 , cR j (d′ n) q′ _ _ g2)))

  nw-l : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₂} → Rl i j x z → Rl i j (nw p x) z
  nw-l {p = p} (h , a) = (λ q q′ → h (⊲-tr p q) q′) , a

  nw-r : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₁} → Rl i j z x → Rl i j z (nw p x)
  nw-r {p = p} (h , a) = (λ q q′ → h q (⊲-tr p q′)) , a

  n1⊑ : HAᶜ i j → ∀ {V₁ V₂} → Rl i j (n1 {W = V₁}) (n1 {W = V₂})
  n1⊑ ha = (λ q q′ w w′ b b′ Y Y′ cY cY′ c cb r → ha w w′ b b′ Y Y′ cY cY′ c cb r) , ≤-refl _

  infl : ∀ {V₁ V₂} (z : D azero V₂) → Rl i j (n0 {W = V₁}) z
  infl z = (λ q q′ w w′ b b′ Y Y′ cY cY′ c cb r → ≤-trans cb (⊲→≤ (sum-fst b′ (F.yc (Rn j z q′ w′ Y′) (inj₁ (kW₀ j)) tt)))) , z≤

  refl⊑ : HAᶜ i j → ∀ {V} (z : D azero V) → Rl i j z z
  refl⊑ ha n0 = infl n0
  refl⊑ ha n1 = n1⊑ ha
  refl⊑ ha (x ⨾ y) = ⨾-mono (refl⊑ ha x) (refl⊑ ha y)
  refl⊑ ha (nl d) = nl-mono (λ n → refl⊑ ha (d n))
  refl⊑ ha (ni () u)
  refl⊑ ha (nκ () u)
  refl⊑ ha (nw p x) = nw-l (nw-r (refl⊑ ha x))

  pre-le : ∀ {V₁ V₂} (x : D azero V₁) (x′ : D azero V₂) (d : ℕ → D azero V₁) (d′ : ℕ → D azero V₂) →
           Rl i j x x′ → (∀ n → Rl i j (d n) (d′ n)) → ∀ k → Rl i j (x ⨾ pre d k) (x′ ⨾ nl d′)
  pre-le x x′ d d′ hx hd k =
    (λ q q′ w w′ b b′ Y Y′ cY cY′ c cb r →
      ≤l k (proj₁ (proj₂ (go q q′ k (cR i x q w Y cY) (cR j x′ q′ w′ Y′ cY′) (smono c (proj₂ hx))
                                (proj₁ hx q q′ w w′ b b′ Y Y′ cY cY′ c cb r) (proj₁ hx q q′ w w′ _ _ Y Y′ cY cY′ c r r))))) ,
    ⊞-mono (proj₂ hx) (≤l k (preV d d′ (λ m → proj₂ (hd m)) k))
    where
    go : ∀ q q′ k {w₁ w₁′ e e′ Z Z′} → CohY Z → CohY Z′ → val w₁ ≤ val w₁′ → e ≤ e′ → vY₀ i Z ≤ vY₀ j Z′ →
         (val (w₁ ⨾ nw q (pre d k)) ≤ val (proj₁ (F.Rpt ac₀ d′ q′ (lW₀ j) (kW₀ j) (act j) w₁′ Z′ k))) ×
         ((Ob i e (pre d k) q w₁ Z ≤
           pt e′ (λ m → F.yc (Rn j (d′ m) q′ (proj₁ (F.Rpt ac₀ d′ q′ (lW₀ j) (kW₀ j) (act j) w₁′ Z′ m))
                               (proj₂ (F.Rpt ac₀ d′ q′ (lW₀ j) (kW₀ j) (act j) w₁′ Z′ m))) (inj₁ (kW₀ j)) tt) k) ×
          ((vY₀ i (Z F.⊕ Rn i (pre d k) q w₁ Z) ≤ vY₀ j (proj₂ (F.Rpt ac₀ d′ q′ (lW₀ j) (kW₀ j) (act j) w₁′ Z′ k))) ×
           (CohY (Z F.⊕ Rn i (pre d k) q w₁ Z) × CohY (proj₂ (F.Rpt ac₀ d′ q′ (lW₀ j) (kW₀ j) (act j) w₁′ Z′ k)))))
    go q q′ zero g1 g2 c′ e r′ = c′ , (e , (r′ , (cR i n0 q _ _ g1 , g2)))
    go q q′ (suc k) {w₁} {Z = Z} g1 g2 c′ e r′ = let (gc , (gb , (gs , (h1 , h2)))) = go q q′ k g1 g2 c′ e r′ in
      smono gc (proj₂ (hd k)) ,
      (proj₁ (hd k) q q′ _ _ _ _ _ _ (cR i (pre d k) q w₁ Z g1) h2 gc gb gs ,
       (proj₁ (hd k) q q′ _ _ _ _ _ _ (cR i (pre d k) q w₁ Z g1) h2 gc gs gs ,
        (cR i (pre d (suc k)) q w₁ Z g1 , cR j (d′ k) q′ _ _ h2)))

module _ {i : S₀} (ha : HAᶜ i i) where
  private rf = refl⊑ {i} {i} ha

  unit-l : ∀ {V} (x : D azero V) → Rl i i (n0 ⨾ x) x × Rl i i x (n0 ⨾ x)
  unit-l x = ((λ q q′ w w′ b b′ Y Y′ cY cY′ c cb r → proj₁ (rf x) q q′ _ w′ _ b′ _ Y′ (cR i n0 q w Y cY) cY′ c cb r) , proj₂ (z⊞ (V0 x))) ,
             ((λ q q′ w w′ b b′ Y Y′ cY cY′ c cb r → proj₁ (rf x) q q′ w _ b _ Y _ cY (cR i n0 q′ w′ Y′ cY′) c cb r) , proj₁ (z⊞ (V0 x)))

  unit-r : ∀ {V} (x : D azero V) → Rl i i (x ⨾ n0) x × Rl i i x (x ⨾ n0)
  unit-r x = (proj₁ (rf x) , ≤-refl _) , (proj₁ (rf x) , ≤-refl _)

  assoc : ∀ {V} (x y z : D azero V) → Rl i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z)) × Rl i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
  assoc x y z = (A1 , ⊞-assoʳ (V0 x) (V0 y) (V0 z)) , (A1′ , ⊞-asso (V0 x) (V0 y) (V0 z))
    where
    A1 : OutLe i i ((x ⨾ y) ⨾ z) (x ⨾ (y ⨾ z))
    A1 q q′ w w′ b b′ Y Y′ cY cY′ c cb r =
      proj₁ (rf z) q q′ _ _ _ _ _ _ (cR i (x ⨾ y) q w Y cY) (cR i y q′ _ _ (cR i x q′ w′ Y′ cY′))
        (smono (smono c (≤-refl (V0 x))) (≤-refl (V0 y)))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (cR i x q w Y cY) (cR i x q′ w′ Y′ cY′) (smono c (≤-refl (V0 x)))
           (proj₁ (rf x) q q′ w w′ b b′ Y Y′ cY cY′ c cb r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ cY cY′ c r r))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (cR i x q w Y cY) (cR i x q′ w′ Y′ cY′) (smono c (≤-refl (V0 x)))
           (proj₁ (rf x) q q′ w w′ _ _ Y Y′ cY cY′ c r r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ cY cY′ c r r))
    A1′ : OutLe i i (x ⨾ (y ⨾ z)) ((x ⨾ y) ⨾ z)
    A1′ q q′ w w′ b b′ Y Y′ cY cY′ c cb r =
      proj₁ (rf z) q q′ _ _ _ _ _ _ (cR i y q _ _ (cR i x q w Y cY)) (cR i (x ⨾ y) q′ w′ Y′ cY′)
        (smono (smono c (≤-refl (V0 x))) (≤-refl (V0 y)))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (cR i x q w Y cY) (cR i x q′ w′ Y′ cY′) (smono c (≤-refl (V0 x)))
           (proj₁ (rf x) q q′ w w′ b b′ Y Y′ cY cY′ c cb r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ cY cY′ c r r))
        (proj₁ (rf y) q q′ _ _ _ _ _ _ (cR i x q w Y cY) (cR i x q′ w′ Y′ cY′) (smono c (≤-refl (V0 x)))
           (proj₁ (rf x) q q′ w w′ _ _ Y Y′ cY cY′ c r r) (proj₁ (rf x) q q′ w w′ _ _ Y Y′ cY cY′ c r r))

module _ {i j : S₀} where
  lim-leP : HAᶜ i i → ∀ {V₁ V₂} (x : D azero V₁) (d : ℕ → D azero V₁) (z : D azero V₂) →
            (∀ k → Rl i j (x ⨾ pre d k) z) → Rl i j (x ⨾ nl d) z
  lim-leP ha x d z h =
    (λ q q′ w w′ b b′ Y Y′ cY cY′ c cb r →
      l≤ (λ k → ≤-trans (proj₁ (proj₂ (go q k (cR i x q w Y cY)))) (proj₁ (h k) q q′ w w′ b b′ Y Y′ cY cY′ c cb r))) ,
    l≤ (λ k → ≤-trans (⊞-mono (≤-refl (V0 x)) (preV′ d d (λ m → ≤-refl _) k)) (proj₂ (h k)))
    where
    go : ∀ q k {w₁ e Z} → CohY Z → (val (proj₁ (F.Rpt ac₀ d q (lW₀ i) (kW₀ i) (act i) w₁ Z k)) ≤ val (w₁ ⨾ nw q (pre d k))) ×
                          ((pt e (λ m → F.yc (Rn i (d m) q (proj₁ (F.Rpt ac₀ d q (lW₀ i) (kW₀ i) (act i) w₁ Z m))
                                                (proj₂ (F.Rpt ac₀ d q (lW₀ i) (kW₀ i) (act i) w₁ Z m))) (inj₁ (kW₀ i)) tt) k
                            ≤ Ob i e (pre d k) q w₁ Z) ×
                           ((vY₀ i (proj₂ (F.Rpt ac₀ d q (lW₀ i) (kW₀ i) (act i) w₁ Z k)) ≤ vY₀ i (Z F.⊕ Rn i (pre d k) q w₁ Z)) ×
                            CohY (proj₂ (F.Rpt ac₀ d q (lW₀ i) (kW₀ i) (act i) w₁ Z k))))
    go q zero g = ≤-refl _ , (≤-refl _ , (≤-refl _ , g))
    go q (suc k) {w₁} {Z = Z} g = let (gc , (gb , (gs , g1))) = go q k g in
      smono gc (≤-refl (V0 (d k))) ,
      (proj₁ (refl⊑ {i} {i} ha (d k)) q q _ _ _ _ _ _ g1 (cR i (pre d k) q w₁ Z g) gc gb gs ,
       (proj₁ (refl⊑ {i} {i} ha (d k)) q q _ _ _ _ _ _ g1 (cR i (pre d k) q w₁ Z g) gc gs gs ,
        cR i (d k) q _ _ g1))

  tr⊑ : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → Rl i i z z′ → Rl i j z′ z″ → Rl i j z z″
  tr⊑ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ cY cY″ c cb r → ≤-trans (h q q w w b b Y Y cY cY (≤-refl _) (≤-refl _) (≤-refl _)) (h′ q q″ w w″ b b″ Y Y″ cY cY″ c cb r)) ,
    ≤-trans a a′

  tr⊑ʳ : ∀ {V V₁} {z : D azero V₁} {z′ z″ : D azero V} → Rl i j z z′ → Rl j j z′ z″ → Rl i j z z″
  tr⊑ʳ (h , a) (h′ , a′) =
    (λ q q″ w w″ b b″ Y Y″ cY cY″ c cb r → ≤-trans (h q q″ w w″ b b″ Y Y″ cY cY″ c cb r) (h′ q″ q″ w″ w″ b″ b″ Y″ Y″ cY″ cY″ (≤-refl _) (≤-refl _) (≤-refl _))) ,
    ≤-trans a a′
```

## §3 规范形: 套 `Gen`

```agda
private
  module GG = Gen HAᶜ Rl (λ {i} {j} h → n1⊑ {i} {j} h) (λ {i} {j} z → infl {i} {j} z)
                 (λ {i} {j} → ⨾-mono {i} {j}) (λ {i} {j} → nl-mono {i} {j}) (λ {i} {j} → nw-l {i} {j}) (λ {i} {j} → nw-r {i} {j})
                 (λ {i} {j} → tr⊑ {i} {j}) (λ {i} {j} → tr⊑ʳ {i} {j})
                 (λ {i} h → unit-l {i} h) (λ {i} h → unit-r {i} h) (λ {i} h → assoc {i} h)
                 (λ {i} {j} → pre-le {i} {j}) (λ {i} {j} h → lim-leP {i} {j} h)

cong0 : ∀ {i j : S₀} → HAᶜ i i → HAᶜ j j → HAᶜ i j →
        ∀ {V V′} (z : D azero V) (z′ : D azero V′) → V0 z ≤ V0 z′ → Rl i j z z′
cong0 {i} {j} ha ha′ hx = GG.Two.cong0 {i} {j} ha ha′ hx
```

## §4 链

```agda
module _ {i j : S₀} (ha : HAᶜ i i) (ha′ : HAᶜ j j) (hx : HAᶜ i j) where
  CC : (k : S₀) → F.St (W₀ k) → ℕ → D azero (W₀ k) × (D azero (W₀ k) × F.St (W₀ k))
  CC k Y = F.Chn ac₀ (kW₀ k) (lW₀ k) tt (act k) Y

  segs : (k : S₀) → F.St (W₀ k) → ℕ → D azero (W₀ k)
  segs k Y n = F.yc (Rn k (proj₁ (proj₂ (CC k Y n))) C.self (proj₁ (CC k Y n)) (proj₂ (proj₂ (CC k Y n)))) (inj₁ (kW₀ k)) tt

  cohC : (k : S₀) (Y : F.St (W₀ k)) → CohY Y → ∀ n → CohY (proj₂ (proj₂ (CC k Y n)))
  cohC k Y cY zero = cY
  cohC k Y cY (suc n) = cR k (proj₁ (proj₂ (CC k Y n))) C.self (proj₁ (CC k Y n)) _ (cohC k Y cY n)

  chain : ∀ (Y : F.St (W₀ i)) (Y′ : F.St (W₀ j)) → CohY Y → CohY Y′ → ∀ b b′ → b ≤ b′ → vY₀ i Y ≤ vY₀ j Y′ →
          sum b (nl (segs i Y)) ≤ sum b′ (nl (segs j Y′))
  chain Y Y′ cY cY′ b b′ cb r = l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (go n)))))
    where
    c  = λ n → proj₁ (CC i Y n)
    c′ = λ n → proj₁ (CC j Y′ n)
    δ  = λ n → proj₁ (proj₂ (CC i Y n))
    δ′ = λ n → proj₁ (proj₂ (CC j Y′ n))
    Yn  = λ n → proj₂ (proj₂ (CC i Y n))
    Yn′ = λ n → proj₂ (proj₂ (CC j Y′ n))
    go : ∀ n → (val (c n) ≤ val (c′ n)) × ((V0 (δ n) ≤ V0 (δ′ n)) × ((vY₀ i (Yn n) ≤ vY₀ j (Yn′ n)) × (pt b (segs i Y) n ≤ pt b′ (segs j Y′) n)))
    go zero = z≤ , (toV0 (δ 0) (δ′ 0) r , (r , cb))
    go (suc n) =
      let (gc , (gd , (gs , gb))) = go n
          h = proj₁ (cong0 {i} {j} ha ha′ hx (δ n) (δ′ n) gd)
          g1 = cohC i Y cY n
          g2 = cohC j Y′ cY′ n
      in smono gc gd ,
         (toV0 _ _ (h C.self C.self (c n) (c′ n) azero azero (Yn n) (Yn′ n) g1 g2 gc z≤ gs) ,
          (h C.self C.self (c n) (c′ n) _ _ (Yn n) (Yn′ n) g1 g2 gc gs gs ,
           h C.self C.self (c n) (c′ n) _ _ (Yn n) (Yn′ n) g1 g2 gc gb gs))
```
