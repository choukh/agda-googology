# `nκ` 的值语义 (二): 语义的记号, 路径一致

> 不含记号. 入口 [KVal](KVal.lagda.md). 对象是 `SumOneClosed` 的折叠 ($S=\cdot\omega$) 在**目标第 0 层**上的输出.
>
> 跨世界比较时, 第 0 层的目标路径不能固定成一条: `nκ` 的格读 `inj₁ (z⊲ v)`, 格里的 `ni` 的链从 `inj₁ (κ₀ ll)` 起步, `cv` 把路径经 `cmpF` 换掉. 所以先证**路径一致**: 状态在一切到第 0 层的路径上值相同 (`CohY`), 则任何输入的输出也如此 (`coh₀`, `coh₁`, 对一切树, 不要关系), 换世界保持值 (`cv≤`, `≤cv`). 值语义的定理 (`KValSound`) 只在一条规范路径 `κ₀ ll` 上陈述, 别的路径由这里换过去.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KValSem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ss; ⊲-tr; z⊲; cmpF; Tg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; ⊞-mono)
open import OCF.Align.SumOneTree using (D; Dl; n0; n1; _⨾_; nl; ni; nκ; nw; sum; pt; sum-fst; cnt; drp)
import OCF.Align.SumOneClosed as F
open import OCF.Align.BrwMidZero using (toA; sum₀; sum-toA)
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValTree using (V0)
```

## §1 值与单调

```agda
val : ∀ {V} → D azero V → A
val t = sum azero t

smono : ∀ {V₁ V₂} {b b′ : A} {x : D azero V₁} {x′ : D azero V₂} → b ≤ b′ → V0 x ≤ V0 x′ → sum b x ≤ sum b′ x′
smono {b = b} {b′} {x} {x′} h hx = ≤-trans (proj₁ (sum-toA b x)) (≤-trans (⊞-mono h hx) (proj₂ (sum-toA b′ x′)))

toV0 : ∀ {V V′} (x : D azero V) (x′ : D azero V′) → val x ≤ val x′ → V0 x ≤ V0 x′
toV0 x x′ le = ≤-trans (proj₂ (sum₀ x)) (≤-trans le (proj₁ (sum₀ x′)))

-- 底 ≤, 值 ≤ ⇒ 和 ≤
svmono : ∀ {V₁ V₂} {b b′ : A} (x : D azero V₁) (x′ : D azero V₂) → b ≤ b′ → val x ≤ val x′ → sum b x ≤ sum b′ x′
svmono x x′ h hx = smono h (toV0 x x′ hx)

sbase : ∀ {V} {b b′ : A} (x : D azero V) → b ≤ b′ → sum b x ≤ sum b′ x
sbase x h = smono h (≤-refl (V0 x))

-- drp 不改和
drp≤ : ∀ {V V′} (x : D azero V) {b b′} → b ≤ b′ → sum b (drp {W′ = V′} x) ≤ sum b′ x
≤drp : ∀ {V V′} (x : D azero V) {b b′} → b ≤ b′ → sum b x ≤ sum b′ (drp {W′ = V′} x)
drp≤ n0 h = h
drp≤ n1 h = s≤ h
drp≤ (x ⨾ y) h = drp≤ y (drp≤ x h)
drp≤ {V′ = V′} (nl d) {b} {b′} h = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b (λ m → drp {W′ = V′} (d m)) n ≤ pt b′ d n
  go zero = h
  go (suc n) = drp≤ (d n) (go n)
drp≤ (ni () u) h
drp≤ (nκ () u) h
drp≤ (nw p x) h = drp≤ x h
≤drp n0 h = h
≤drp n1 h = s≤ h
≤drp (x ⨾ y) h = ≤drp y (≤drp x h)
≤drp {V′ = V′} (nl d) {b} {b′} h = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b d n ≤ pt b′ (λ m → drp {W′ = V′} (d m)) n
  go zero = h
  go (suc n) = ≤drp (d n) (go n)
≤drp (ni () u) h
≤drp (nκ () u) h
≤drp (nw p x) h = ≤drp x h

-- 极限的各项经 drp 落到两个不同世界: 和相同
nl-drp : ∀ {Wf : ℕ → A} {V₁ V₂} (X : ∀ n → D azero (Wf n)) c → sum c (nl (λ n → drp {W′ = V₁} (X n))) ≤ sum c (nl (λ n → drp {W′ = V₂} (X n)))
nl-drp {V₁ = V₁} {V₂} X c = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt c (λ m → drp {W′ = V₁} (X m)) n ≤ pt c (λ m → drp {W′ = V₂} (X m)) n
  go zero = ≤-refl c
  go (suc n) = ≤-trans (drp≤ (X n) (go n)) (≤drp (X n) (≤-refl _))
```

## §2 路径一致

`κ₀ ll`: 第 1 层的 `ni` 在世界 $W$ 里上升时读的路径 (`SumOneFold.kk`). 规范路径取它.

```agda
κ₀ : ∀ {W} → one ⊲ W → azero ⊲ W
κ₀ ll = ⊲-tr (C.suc C.self) ll

vYk : ∀ {W} → azero ⊲ W → F.St W → A
vYk k Y = val (F.yc (F.d Y) (inj₁ k) tt)

record CohY {W} (Y : F.St W) : Set where
  constructor cy
  field cyA : ∀ (τ τ′ : Tg azero W) → val (F.yc (F.d Y) τ tt) ≤ val (F.yc (F.d Y) τ′ tt)
open CohY public

record CohD {W} (Δ : F.Df W) : Set where
  constructor cd
  field cdA : ∀ (τ τ′ : Tg azero W) c → sum c (F.yc Δ τ tt) ≤ sum c (F.yc Δ τ′ tt)
open CohD public

CohA : ∀ {ly W} → F.Ig ly W → Set
CohA {ly} {W} A₀ = ∀ {V} (p : W ⊲ V) (lV : Lg V) (w : Dl ly V) (Y : F.St V) → CohY Y → CohD (A₀ p lV w Y)

cohA↾ : ∀ {ly W W′} {A₀ : F.Ig ly W} (p : W ⊲ W′) → CohA A₀ → CohA (F.Ig↾ p A₀)
cohA↾ p c p′ = c (⊲-tr p p′)

cohZ : ∀ {W} → CohD (F.zeroD {W})
cohZ = cd (λ τ τ′ c → ≤-refl c)

cohY0 : ∀ {W} → CohY (F.st (F.zeroD {W}) n0)
cohY0 = cy (λ τ τ′ → z≤)

coh⊕ : ∀ {W} {Y : F.St W} {Δ : F.Df W} → CohY Y → CohD Δ → CohY (Y F.⊕ Δ)
coh⊕ {Y = Y} {Δ} (cy cY) (cd cD) = cy (λ τ τ′ → ≤-trans (sbase (F.yc Δ τ tt) (cY τ τ′)) (cD τ τ′ _))

coh⨾ : ∀ {W} {a b : F.Df W} → CohD a → CohD b → CohD (a F.⨾ᴰ b)
coh⨾ {a = a} {b} (cd ca) (cd cb) = cd (λ τ τ′ c → ≤-trans (sbase (F.yc b τ tt) (ca τ τ′ c)) (cb τ τ′ _))

cohNl : ∀ {W} {G : ℕ → F.Df W} → (∀ n → CohD (G n)) → CohD (F.nlᴰ G)
cohNl {G = G} h = cd (λ τ τ′ c → l≤ (λ n → ≤l n (go τ τ′ c n)))
  where
  go : ∀ τ τ′ c n → pt c (λ m → F.yc (G m) τ tt) n ≤ pt c (λ m → F.yc (G m) τ′ tt) n
  go τ τ′ c zero = ≤-refl c
  go τ τ′ c (suc n) = ≤-trans (sbase (F.yc (G n) τ tt) (go τ τ′ c n)) (cdA (h n) τ τ′ _)
```

## §3 第 0 层输入的输出一致

```agda
coh₀ : ∀ {V W} (ac : F.AccY (cnt azero)) (z : D azero V) (q : V ⊲ W) (lW : Lg W) (kW : azero ⊲ W) (A₀ : F.Ig (cnt azero) W)
       (w : D azero W) (Y : F.St W) → CohA A₀ → CohY Y → CohD (F.Run ac z q lW kW A₀ w Y)
coh₀ ac n0 q lW kW A₀ w Y cA cY = cohZ
coh₀ ac n1 q lW kW A₀ w Y cA cY = cA C.self lW w Y cY
coh₀ ac (x ⨾ y) q lW kW A₀ w Y cA cY =
  coh⨾ (coh₀ ac x q lW kW A₀ w Y cA cY) (coh₀ ac y q lW kW A₀ _ _ cA (coh⊕ cY (coh₀ ac x q lW kW A₀ w Y cA cY)))
coh₀ ac (nl G) q lW kW A₀ w Y cA cY = cohNl (λ n → coh₀ ac (G n) q lW kW A₀ _ _ cA (cR n))
  where
  cR : ∀ n → CohY (proj₂ (F.Rpt ac G q lW kW A₀ w Y n))
  cR zero = cY
  cR (suc n) = coh⊕ (cR n) (coh₀ ac (G n) q lW kW A₀ _ _ cA (cR n))
coh₀ ac (ni () u) q lW kW A₀ w Y cA cY
coh₀ ac (nκ () u) q lW kW A₀ w Y cA cY
coh₀ ac (nw p x) q lW kW A₀ w Y cA cY = coh₀ ac x (⊲-tr p q) lW kW A₀ w Y cA cY
```

## §4 第 1 层输入的输出一致

`ni` 在目标第 0 层只能上升, 链与读出的路径无关; `nκ` 在目标第 0 层的输出字面不看路径 (`RKy` 的 `azero` 子句).

```agda
ac₁ : F.AccY (cnt one)
ac₁ = F.accCn one

coh₁ : ∀ {V W} (x : D one V) (q : V ⊲ W) (lW : Lg W) (ll : one ⊲ W) (A₀ : F.Ig (cnt one) W) (w : D one W) (Y : F.St W) →
       CohA A₀ → CohY Y → CohD (F.Run ac₁ x q lW ll A₀ w Y)
coh₁ n0 q lW ll A₀ w Y cA cY = cohZ
coh₁ n1 q lW ll A₀ w Y cA cY = cA C.self lW w Y cY
coh₁ (x ⨾ y) q lW ll A₀ w Y cA cY =
  coh⨾ (coh₁ x q lW ll A₀ w Y cA cY) (coh₁ y q lW ll A₀ _ _ cA (coh⊕ cY (coh₁ x q lW ll A₀ w Y cA cY)))
coh₁ (nl G) q lW ll A₀ w Y cA cY = cohNl (λ n → coh₁ (G n) q lW ll A₀ _ _ cA (cR n))
  where
  cR : ∀ n → CohY (proj₂ (F.Rpt ac₁ G q lW ll A₀ w Y n))
  cR zero = cY
  cR (suc n) = coh⊕ (cR n) (coh₁ (G n) q lW ll A₀ _ _ cA (cR n))
coh₁ (nw p x) q lW ll A₀ w Y cA cY = coh₁ x (⊲-tr p q) lW ll A₀ w Y cA cY
coh₁ (nκ zz u) q lW ll A₀ w Y cA cY = cd (λ τ τ′ c → nl-drp _ c)
coh₁ (ni (ss C.self) u) q lW ll A₀ w Y cA cY = cd (λ τ τ′ c → rs τ τ′ c (F.rkT kW τ lW) (F.rkT kW τ′ lW))
  where
  kW = κ₀ ll
  ac₀ = F.accCn azero
  A² = F.Ai ac₁ (ss C.self) u q kW ll A₀ w
  cA² : CohA A²
  cA² p lV z Y′ cY′ = coh₁ (u (⊲-tr q p) lV z) C.self lV (⊲-tr ll p) (F.Ig↾ p A₀) _ Y′ (cohA↾ p cA) cY′
  C′ = F.Chn ac₀ kW lW tt A² Y
  cC : ∀ n → CohY (proj₂ (proj₂ (C′ n)))
  cC zero = cY
  cC (suc n) = coh⊕ (cC n) (coh₀ ac₀ (proj₁ (proj₂ (C′ n))) C.self lW kW A² _ _ cA² (cC n))
  seg : (σ : Tg azero _) → ℕ → D azero (F.wm σ)
  seg σ n = F.yc (F.Run ac₀ (proj₁ (proj₂ (C′ n))) C.self lW kW A² (proj₁ (C′ n)) (proj₂ (proj₂ (C′ n)))) σ tt
  go : ∀ τ τ′ c n → pt c (seg τ) n ≤ pt c (seg τ′) n
  go τ τ′ c zero = ≤-refl c
  go τ τ′ c (suc n) = ≤-trans (sbase (seg τ n) (go τ τ′ c n))
                       (cdA (coh₀ ac₀ (proj₁ (proj₂ (C′ n))) C.self lW kW A² _ _ cA² (cC n)) τ τ′ _)
  rs : ∀ τ τ′ c (rk rk′ : F.Rk′ azero azero) →
       sum c (F.RKi ac₁ ac₀ (ss C.self) u q lW ll A₀ w Y τ tt rk) ≤ sum c (F.RKi ac₁ ac₀ (ss C.self) u q lW ll A₀ w Y τ′ tt rk′)
  rs τ τ′ c (F.keep ()) rk′
  rs τ τ′ c (F.rise _) (F.keep ())
  rs τ τ′ c (F.rise _) (F.rise _) = l≤ (λ n → ≤l n (go τ τ′ c n))
```

## §5 换世界

`cv` 把旧差 (某条路径上) 包一层 `nw`, 不改值.

```agda
module _ {W W′ : A} (Y : F.St W) (q : W ⊲ W′) (lW′ : Lg W′) where
  cv-l : ∀ (X : A) → (∀ τ → val (F.yc (F.d Y) τ tt) ≤ X) → ∀ τ → val (F.yc (F.d (F.cv q lW′ Y)) τ tt) ≤ X
  cv-l X h (inj₁ τ₁) with cmpF q τ₁ lW′
  ... | inj₁ t⊲W = h (inj₁ t⊲W)
  ... | inj₂ W⊲t = h (inj₂ W⊲t)
  cv-l X h (inj₂ τ₂) = h (inj₂ (⊲-tr q τ₂))

  cv-r : ∀ (X : A) → (∀ τ → X ≤ val (F.yc (F.d Y) τ tt)) → ∀ τ → X ≤ val (F.yc (F.d (F.cv q lW′ Y)) τ tt)
  cv-r X h (inj₁ τ₁) with cmpF q τ₁ lW′
  ... | inj₁ t⊲W = h (inj₁ t⊲W)
  ... | inj₂ W⊲t = h (inj₂ W⊲t)
  cv-r X h (inj₂ τ₂) = h (inj₂ (⊲-tr q τ₂))

  cohCv : CohY Y → CohY (F.cv q lW′ Y)
  cohCv cY = cy (λ τ τ′ → cv-l _ (λ σ → cv-r _ (λ σ′ → cyA cY σ σ′) τ′) τ)

  cv≤ : CohY Y → ∀ τ σ → val (F.yc (F.d (F.cv q lW′ Y)) τ tt) ≤ val (F.yc (F.d Y) σ tt)
  cv≤ cY τ σ = cv-l _ (λ σ′ → cyA cY σ′ σ) τ

  ≤cv : CohY Y → ∀ σ τ → val (F.yc (F.d Y) σ tt) ≤ val (F.yc (F.d (F.cv q lW′ Y)) τ tt)
  ≤cv cY σ τ = cv-r _ (λ σ′ → cyA cY σ σ′) τ
```
