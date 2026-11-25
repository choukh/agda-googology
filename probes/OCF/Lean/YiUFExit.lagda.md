# 完整候选折叠按对照表逐出口核: 形状档

> 判决: 编译定理 (形状档), 对一切层号、证据、槽位、孩子、目标路径, 不按站; 不读记号, 没有值的定理. 候选的保留判定仍只有三个出口 (`kp-exit`). 下标侧槽位、目标经指定孩子: 有 `Schema` 时要么目标在地板之下, 要么结果是 "保留在层号字面相同的槽位上, 或目标字面等于槽位层号而不保留" (`idx-case`, `Lin`); 塔各项是实例 (`idx-tw`), 审查 E 路 `drop₂` 那一格现在保留 (`keep₂`, `node₂`).
> 嵌入行: 满证据且 d ≥ 1 时不回退, 按 `route` 二分 (`row-full`); 替身内部是同一个折叠低一档, 证据仍满 (`seen-eq`, `full-row`), d = 0 时回退 (`row-zero`).
> 没有改的格 (仍在分叉出口): 孩子侧槽位 (`diag-slotᶜ`); 下标侧槽位而目标在地板之下 (`lo-cross₂`: 槽位层 `zero`, 目标 `tw 1`, 经孩子的路径不保留, 经下标层侧的路径保留 `lo-ink₂`). 入口: `idx-case`, `row-full`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUFExit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; mapK; node⁺)
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiRBSib using (rb-ind)
open import OCF.Lean.YiBSBase using (Schema; schema; floor; offsets; index-floor; ok-offsets; route; back; raiseO; downOk)
open import OCF.Lean.YiCMCross using (toKeep; keepS; IsJust; isJ)
open import OCF.Lean.YiCMExit using (Exit; kept; high; cross; psh-at; map-exit)
open import OCF.Lean.YiUFBase
open import OCF.Lean.YiUFFold
```

## 三个出口 (候选的保留判定)

`Exit` 用 `YiCMExit` 的原类型. `keepS` 的结果不在分叉出口, 而且 "不保留" 时目标字面等于槽位层号 (`Lin`, 比 `high` 强).

```agda
data Lin (a₀ : L) {j : L} {X : Set} {x₀ : X} : Keep j X x₀ → Set where
  keptᴸ : ∀ q cv e → at j q ≡ a₀ → Lin a₀ (just (q , cv , e))
  sameᴸ : j ≡ a₀ → Lin a₀ nothing

lin→exit : ∀ {a₀ j X} {x₀ : X} {m : Keep j X x₀} → Lin a₀ m → Exit a₀ m
lin→exit (keptᴸ q cv e eq) = kept q cv e eq
lin→exit {j = j} (sameᴸ eq) = high (subst (λ a → j ≤ a) eq self)

toKeep-lin : ∀ {j X a₀} {x₀ : X} (r : Pos⁼ j) (cv : Br⁼ j r → X) (e : cv (bz⁼ j r) ≡ x₀)
  → proj₁ (sl⁼ j r) ≡ a₀ → Lin a₀ (toKeep r cv e)
toKeep-lin (inj₁ _) cv e eq = sameᴸ eq
toKeep-lin (inj₂ q) cv e eq = keptᴸ q cv e eq

keepS-lin : ∀ {k h} (S : Schema k h) (t : Pos⁼ k) {j} (u : floor S ≤ j) → Lin (proj₁ (sl⁼ k t)) (keepS S t u)
keepS-lin S t u = toKeep-lin (psh (index-floor S ∙ u) t) _ _ (psh-at (index-floor S ∙ u) t)

mutual
  kp-exit : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → Exit (at ℓ p) (kp ℓ o r p w)
  kp-exit ℓ             o               r        p              self      = kept p _ _ refl
  kp-exit (nd s h)      (_ , oc)        (_ , rc) (inj₂ (c , t)) (inu vs)  = kp⁼-exit (h c) (oc c) (rc c) t (vs c)
  kp-exit (nd (sΩ k) h) ((_ , kh) , oc) (_ , rc) (inj₂ (c , t)) (ink v)   = kp⁼-exit (h c) (oc c) (rc c) t (v ∙ kh c)
  kp-exit (nd sS h)     (_ , oc)        (_ , rc) (inj₂ (c , t)) (inc _ v) = kp⁼-exit (h c) (oc c) (rc c) t v
  kp-exit (nd sL g)     (r , oc)        (_ , rc) (inj₂ (m , t)) (inc n v) =
    cW-ind (Exit (proj₁ (sl⁼ (g m) t))) (way g r m n)
      (λ u → map-exit (pshBr u t) (pshFirst u t) (psh-at u t) (kp⁼-exit (g n) (oc n) (rc n) (psh u t) v))
      (λ u → kp⁼-exit (g m) (oc m) (rc m) t (v ∙ u))
  kp-exit (nd (sΩ k) h) _               _        (inj₂ (c , t)) (inc c′ v) = cross c c′ (posW⁼ (h c) t) v
  kp-exit (nd (sΩ k) h) ((ok , _) , _)  ((rk , _) , _) (inj₁ t) (ink v)   = kp⁼-exit k ok rk t v
  kp-exit (nd (sΩ k) h) ((_ , kh) , oc) ((_ , m) , rc) (inj₁ t) (inc c v) =
    rb-ind (Exit (proj₁ (sl⁼ k t))) m
      (λ S → cW-ind (Exit (proj₁ (sl⁼ k t))) (route S _ c v)
        (λ _ → map-exit (pshBr (kh c) t) (pshFirst (kh c) t) (psh-at (kh c) t) (kp⁼-exit (h c) (oc c) (rc c) (psh (kh c) t) v))
        (λ u → lin→exit (keepS-lin S t u)))
      (map-exit (pshBr (kh c) t) (pshFirst (kh c) t) (psh-at (kh c) t) (kp⁼-exit (h c) (oc c) (rc c) (psh (kh c) t) v))
  kp-exit (nd (sΩ k) h) ((_ , kh) , oc) (_ , rc) (inj₁ t)       (inu vs)  =
    map-exit (pshBr (kh zero) t) (pshFirst (kh zero) t) (psh-at (kh zero) t)
      (kp⁼-exit (h zero) (oc zero) (rc zero) (psh (kh zero) t) (vs zero))

  kp⁼-exit : (a : L) (o : Ok a) (r : Rb a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) → Exit (proj₁ (sl⁼ a t)) (kp⁼ a o r t w)
  kp⁼-exit a o r (inj₁ _) w = high w
  kp⁼-exit a o r (inj₂ p) w = kp-exit a o r p w
```

## 下标侧槽位推进后分叉那一格 (`drop-idx`, `drop-tw`, `drop₂`)

对一切 `Schema`, 槽位 t, 孩子 c, 目标路径 v: `route` 给地板之下, 或者结果是 `keepS` (不分叉). `route` 是目标路径 v 的函数.

```agda
alt : ∀ {A B X : Set} (Q : X → Set) (W : A ⊎ B) {F : A → X} {G : B → X} → ((b : B) → Q (G b)) → A ⊎ Q (cW W F G)
alt Q (inj₁ a) hG = inj₁ a
alt Q (inj₂ b) hG = inj₂ (hG b)

idx-hi : ∀ k h (o : Ok (nd (sΩ k) h)) (rk : Rb k) (S : Schema k h) (rc : (c : Tr k) → Rb (h c)) (t : Pos⁼ k) c {j} (v : j ≤ h c)
  → (j ≤ floor S) ⊎ (Σ (floor S ≤ j) λ u → kp (nd (sΩ k) h) o ((rk , just S) , rc) (inj₁ t) (inc c v) ≡ keepS S t u)
idx-hi k h o rk S rc t c v = alt (λ m → Σ _ λ u → m ≡ keepS S t u) (route S _ c v) (λ u → u , refl)

idx-case : ∀ k h (o : Ok (nd (sΩ k) h)) (rk : Rb k) (S : Schema k h) (rc : (c : Tr k) → Rb (h c)) (t : Pos⁼ k) c {j} (v : j ≤ h c)
  → (j ≤ floor S) ⊎ Lin (proj₁ (sl⁼ k t)) (kp (nd (sΩ k) h) o ((rk , just S) , rc) (inj₁ t) (inc c v))
idx-case k h o rk S rc t c v = alt (Lin (proj₁ (sl⁼ k t))) (route S _ c v) (λ u → keepS-lin S t u)
```

顶槽位 (下标层自身): 目标在地板之上时保留, 除非目标字面就是下标层.

```agda
top-w : ∀ {k j} (w : k ≤ j) → IsJust (toKeep (psh w (inj₁ tt)) (pshBr w (inj₁ tt)) (pshFirst w (inj₁ tt))) ⊎ (k ≡ j)
top-w self                  = inj₂ refl
top-w (inc c v)             = inj₁ (isJ _)
top-w {j = nd s h} (inu vs) = inj₁ (isJ _)
top-w (ink v)               = inj₁ (isJ _)

top-keep : ∀ {k h} (S : Schema k h) {j} (u : floor S ≤ j) → IsJust (keepS S (inj₁ tt) u) ⊎ (k ≡ j)
top-keep S u = top-w (index-floor S ∙ u)

slot-keep : ∀ {k h} (S : Schema k h) (p : Pos k) {j} (u : floor S ≤ j) → IsJust (keepS S (inj₂ p) u)
slot-keep S p u = sk (index-floor S ∙ u)
  where
  sk : ∀ {k j} {p : Pos k} (w : k ≤ j) → IsJust (toKeep (psh w (inj₂ p)) (pshBr w (inj₂ p)) (pshFirst w (inj₂ p)))
  sk self                  = isJ _
  sk (inc c v)             = isJ _
  sk {j = nd s h} (inu vs) = isJ _
  sk (ink v)               = isJ _
```

塔各项 (一切 n, 一切孩子 c′, 一切目标路径), `drop-tw` 的对应.

```agda
idx-tw : ∀ n (t : Pos⁼ (tw n)) (c′ : Tr (tw n)) {j} (v : j ≤ tw n ⊕ ↑ (tw n) c′)
  → (j ≤ tw n) ⊎ Lin (proj₁ (sl⁼ (tw n) t)) (kp (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) (inj₁ t) (inc c′ v))
idx-tw n t c′ v = idx-case (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ok-tw (suc n)) (rb-tw n) _ _ t c′ v
```

审查 E 路 `drop₂` 的那一格 (塔第 2 项顶槽位, 目标是孩子 `Ωt (tw 1)` 的偏移顶结点的第 0 个孩子): 候选保留, 所以 `Ωt (tw 2)` 朝这个目标折出的是 Ω 结点, 对一切 d, 底, 起点.

```agda
c′₂ : Tr (tw 1)
c′₂ = proj₁ (Ωt (tw 1))

j₂ : L
j₂ = nd sS (λ _ → tw 1)

v₂ : j₂ ≤ tw 1 ⊕ ↑ (tw 1) c′₂
v₂ = inc zero self

keep₂ : IsJust (kp (tw 2) (Ok-tw 2) (rb-tw 2) (inj₁ (inj₁ tt)) (inc c′₂ v₂))
keep₂ = isJ _

data IsΩ {S : Sg} : T S → Set where
  isΩ : ∀ p g → IsΩ (Ω p g)

nodeΩ : ∀ {j X x₀} (m : Keep j X x₀) → IsJust m → (G : X → Tr⁺ j) (s : X → X) → IsΩ (proj₁ (node⁺ m G s))
nodeΩ .(just _) (isJ (q , cv , e)) G s = isΩ _ _

keep-node : ∀ d ℓ o r (B : Base ℓ) j (w : j ≤ ℓ) β p g → IsJust (kp ℓ o r p w) → IsΩ (proj₁ (ψ d ℓ o r B j w β (Ω p g)))
keep-node d ℓ o r B j w β p g e = nodeΩ (kp ℓ o r p w) e _ _

node₂ : ∀ d (B : Base (tw 2)) (β : Tr⁺ j₂)
  → IsΩ (proj₁ (ψ d (tw 2) (Ok-tw 2) (rb-tw 2) B j₂ (inc c′₂ v₂) β (proj₁ (Ωt (tw 2)))))
node₂ d B β = keep-node d (tw 2) (Ok-tw 2) (rb-tw 2) B j₂ (inc c′₂ v₂) β _ _ keep₂
```

## 没有改的格

孩子侧槽位 (R77): 与主线逐字同一行. 对角上槽位字面是目标的槽位仍给 `nothing`.

```agda
diag-slotᶜ : ∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) c (p′ : Pos (h c))
  → (kp (nd (sΩ k) h) o r (inj₂ (c , inj₂ p′)) (inc c self) ≡ nothing)
  × (Br (h c) p′ ≡ Br (nd (sΩ k) h) (inj₂ (c , inj₂ p′)))
  × (at (h c) p′ ≡ at (nd (sΩ k) h) (inj₂ (c , inj₂ p′)))
diag-slotᶜ k h o r c p′ = refl , refl , refl
```

下标侧槽位而目标在地板之下: `route` 给 `inj₁`, 行是原来的推进. 实例: 塔第 2 项, 槽位在下标层 `tw 1` 里 (层号 `zero`), 目标是 `tw 1` 自身, 经孩子 `Ωt (tw 1)` 的偏移到达: 不保留; 同一槽位同一目标层, 经下标层侧的路径: 保留.

```agda
p₂ : Pos (tw 2)
p₂ = inj₁ (inj₂ (inj₁ (inj₁ tt)))

p₂-at : at (tw 2) p₂ ≡ zero
p₂-at = refl

w₂ : tw 1 ≤ tw 1 ⊕ ↑ (tw 1) c′₂
w₂ = inc zero (inc tt self)

lo-cross₂ : kp (tw 2) (Ok-tw 2) (rb-tw 2) p₂ (inc c′₂ w₂) ≡ nothing
lo-cross₂ = refl

lo-ink₂ : IsJust (kp (tw 2) (Ok-tw 2) (rb-tw 2) p₂ (ink self))
lo-ink₂ = isJ _
```

无证据 (`rb-no`) 时候选的保留判定逐点等于主线的 `YiRWFold.kp`: 改动只在有 `Schema` 的结点上起作用.

```agda
mutual
  kp-no : (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → kp ℓ o (rb-no ℓ) p w ≡ RW.kp ℓ o p w
  kp-no ℓ             o               p              self      = refl
  kp-no (nd s h)      (_ , oc)        (inj₂ (c , t)) (inu vs)  = kp⁼-no (h c) (oc c) t (vs c)
  kp-no (nd (sΩ k) h) ((_ , kh) , oc) (inj₂ (c , t)) (ink v)   = kp⁼-no (h c) (oc c) t (v ∙ kh c)
  kp-no (nd sS h)     (_ , oc)        (inj₂ (c , t)) (inc _ v) = kp⁼-no (h c) (oc c) t v
  kp-no (nd sL g)     (r , oc)        (inj₂ (m , t)) (inc n v) =
    cW-ind₂ (λ Z Z′ → Z ≡ Z′) (way g r m n)
      (λ u → cong (mapK (pshBr u t) (pshFirst u t)) (kp⁼-no (g n) (oc n) (psh u t) v))
      (λ u → kp⁼-no (g m) (oc m) t (v ∙ u))
  kp-no (nd (sΩ k) h) _               (inj₂ _)       (inc _ _) = refl
  kp-no (nd (sΩ k) h) ((ok , _) , _)  (inj₁ t)       (ink v)   = kp⁼-no k ok t v
  kp-no (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inc c v) =
    cong (mapK (pshBr (kh c) t) (pshFirst (kh c) t)) (kp⁼-no (h c) (oc c) (psh (kh c) t) v)
  kp-no (nd (sΩ k) h) ((_ , kh) , oc) (inj₁ t)       (inu vs)  =
    cong (mapK (pshBr (kh zero) t) (pshFirst (kh zero) t)) (kp⁼-no (h zero) (oc zero) (psh (kh zero) t) (vs zero))

  kp⁼-no : (a : L) (o : Ok a) (t : Pos⁼ a) → ∀ {j} (w : j ≤ a) → kp⁼ a o (rb-no a) t w ≡ RW.kp⁼ a o t w
  kp⁼-no a o (inj₁ _) w = refl
  kp⁼-no a o (inj₂ p) w = kp-no a o p w
```

## 嵌入行的分叉出口 (`fallᶻ`, `fallᴮ` 的对应)

d = 0: 回退. d ≥ 1 且有 `Schema`: 按 `route` 二分, 不回退; 满证据时每个 Ω 形状结点都如此.

```agda
row-zero : ∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e
  → ψ zero (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e)
  ≡ ψ zero (nd (sΩ k) h) o r B j (inc c′ v) β x ⊞ ψ zero (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y
row-zero k h o r B j c′ v β x c y e = refl

alt₂ : ∀ {A B X : Set} (W : A ⊎ B) {F : A → X} {G : B → X}
  → (Σ A λ a → cW W F G ≡ F a) ⊎ (Σ B λ b → cW W F G ≡ G b)
alt₂ (inj₁ a) = inj₁ (a , refl)
alt₂ (inj₂ b) = inj₂ (b , refl)

row-alt : ∀ d k h (o : Ok (nd (sΩ k) h)) (rk : Rb k) (S : Schema k h) (rc : (c : Tr k) → Rb (h c)) (B : Base (nd (sΩ k) h))
  j c′ (v : j ≤ h c′) β x c y e
  → (Σ (j ≤ floor S) λ u → ψ (suc d) (nd (sΩ k) h) o ((rk , just S) , rc) B j (inc c′ v) β (up x c y e)
       ≡ ψ (suc d) (h c) (proj₂ o c) (rc c)
           (λ i u′ → ψ (suc d) (nd (sΩ k) h) o ((rk , just S) , rc) B i (inc c u′) (B i (inc c u′)) x)
           j (back S c u) (ψ (suc d) (nd (sΩ k) h) o ((rk , just S) , rc) B j (inc c′ v) β x) y)
  ⊎ (Σ (floor S ≤ j) λ u → ψ (suc d) (nd (sΩ k) h) o ((rk , just S) , rc) B j (inc c′ v) β (up x c y e)
       ≡ seen d S j (downOk (h c′) (proj₂ o c′) j v) (rb≤ (h c′) (rc c′) v) u
           (ψ (suc d) (nd (sΩ k) h) o ((rk , just S) , rc) B j (inc c′ v) β x) c
         ⊞ ψ (suc d) (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)
row-alt d k h o rk S rc B j c′ v β x c y e = alt₂ (route S j c′ v)

row-full : ∀ d k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (f : Full (nd (sΩ k) h) r) (B : Base (nd (sΩ k) h))
  j c′ (v : j ≤ h c′) β x c y e
  → (Σ (j ≤ floor (proj₁ (proj₂ (proj₁ f)))) λ u → ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e)
       ≡ ψ (suc d) (h c) (proj₂ o c) (proj₂ r c)
           (λ i u′ → ψ (suc d) (nd (sΩ k) h) o r B i (inc c u′) (B i (inc c u′)) x)
           j (back (proj₁ (proj₂ (proj₁ f))) c u) (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) y)
  ⊎ (Σ (floor (proj₁ (proj₂ (proj₁ f))) ≤ j) λ u → ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e)
       ≡ seen d (proj₁ (proj₂ (proj₁ f))) j (downOk (h c′) (proj₂ o c′) j v) (rb≤ (h c′) (proj₂ r c′) v) u
           (ψ (suc d) (nd (sΩ k) h) o r B j (inc c′ v) β x) c
         ⊞ ψ (suc d) (h c) (proj₂ o c) (proj₂ r c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)
row-full d k h o ((rk , .(just S)) , rc) ((fk , S , refl) , fc) B j c′ v β x c y e = row-alt d k h o rk S rc B j c′ v β x c y e
```

## 替身内部

`seen d` 逐字是第 d 个折叠在重建层号上朝 j 的折叠, 证据是 `rb-row`; 外层证据满时它也满 (`YiUFBase.full-row`, `full≤`), 所以替身内部的嵌入行在 d ≥ 1 时仍按 `row-full` 二分, 保留行仍按 `idx-case`.

```agda
seen-eq : ∀ d {k h} (S : Schema k h) j oj rj (u : floor S ≤ j) β c
  → seen d S j oj rj u β c
  ≡ ψ d (j ⊕ offsets S c) (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
      (rb-row S j oj rj u c) (B₀ _) j (lift j (offsets S c)) β (proj₁ (Ωt (j ⊕ offsets S c)))
seen-eq d S j oj rj u β c = refl

seen-full : ∀ {k h} (r : (c : Tr k) → Rb (h c)) → ((c : Tr k) → Full (h c) (r c)) → (S : Schema k h) → ∀ j c′ (v : j ≤ h c′) oj
  (u : floor S ≤ j) (c : Tr k) → Full (j ⊕ offsets S c) (rb-row S j oj (rb≤ (h c′) (r c′) v) u c)
seen-full {h = h} r f S j c′ v oj u c = full-row S j oj (rb≤ (h c′) (r c′) v) u (full≤ (h c′) (r c′) (f c′) v) c
```
