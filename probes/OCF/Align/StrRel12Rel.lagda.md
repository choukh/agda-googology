# 结构关系, 第十二轮 (二): 关系族, 坐标的互换, 第 0 层

> 不读记号, 不提折叠. 入口 [StrRel12](StrRel12.lagda.md). 关系族与 `StrRel11Le` 同形 (对层递归, 坐标关系沿左边节点的位置往下取更低层的 `Rel`), **只改一处**: 节点 `niᴸ` 与 `nκ` 的 `κᴸ` 只在 **`CP`** 分支对上比 (对齐 `AP` + 顶端可比 + 顶端 `Lg` 自洽), 不在一切 `APair` 分支对上比. 改的理由: 折叠沿分支路径走 (`Walk`, `Cut`, `IW`) 时, 位置上的前段只在顶端自洽时才满足 `AP` 的 `Lg` 等式, 位置的值可比由 `Al` 的 `aP` 给出 (见 [StrRel12Al](StrRel12Al.lagda.md) 文件头). 这一改动让关系**更宽** (前提少了), 所以 `StrRel11Le` 的关系的每个推导在这里都有对应 (判断, 未写嵌入).
>
> 本文还给出: 坐标关系与 `Rel k` 的互换 (`belowOut`, `belowIn`, 用 `out-inS`), 第 0 层的值可靠 (`vsum`), `drp` 的搬运 (`drpR`), 第 0 层的和产生自洽的 `Lg` (`cohSum`), 由第 0 层关系生成对齐 (`genAl`, `StrRel4Pr.genᴾ` 的主线版; 用 `al-adm` 代替 `sum-toA` 的一半).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel12Rel where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤; _⊞_; ⊞-mono; ⊞-asso; ⊞-assoʳ)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; StH; ss; sl; sL; Vs; Vc; D; D₀;
  outC; inC; outS; inS; n0; n1; _⨾_; nl; ni; nκ; nw; NZ; drp; sum; pt; sum-fst; Lg-sum; Lg-pt)
open import OCF.Align.KNestAdm using (Adm; adm-tr)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aL)
open import OCF.Align.StrRel4Gen using (lg-tr; cat; ext)
open import OCF.Align.StrRel12Al using (Coh; cohEq; AP; CP; stepA; adm-lo; al-adm)
```

## 1 关系族

```agda
LoT : H → Set₁
LoT L = ∀ {V V′ k c c′} (r : StH V k L) (r′ : StH V′ k L) → Lg c → Lg c′ → Vs L r c → Vs L r′ c′ → Set

data LeF (L : H) (Lo : LoT L) : ∀ {V V′} → Lg V → Lg V′ → D L V → D L V′ → Set where
  n0ᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x′ : D L V′} → LeF L Lo lV lV′ n0 x′
  n1ᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → LeF L Lo lV lV′ n1 n1
  ⨾ᴸ   : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D L V} {x′ y′ : D L V′} →
         LeF L Lo lV lV′ x x′ → LeF L Lo lV lV′ y y′ → LeF L Lo lV lV′ (x ⨾ y) (x′ ⨾ y′)
  nlᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d : ℕ → D L V} {d′ : ℕ → D L V′} →
         (∀ n → LeF L Lo lV lV′ (d n) (d′ n)) → LeF L Lo lV lV′ (nl d) (nl d′)
  prᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D L V} {x′ y′ : D L V′} →
         LeF L Lo lV lV′ x x′ → LeF L Lo lV lV′ x (x′ ⨾ y′)
  nwAᴸ : ∀ {V₀ V₀′ V V′} {lV₀ : Lg V₀} {lV₀′ : Lg V₀′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V} {p′ : V₀′ ⊲ V′}
           {x : D L V₀} {x′ : D L V₀′} →
         AP lV₀ lV₀′ p lV p′ lV′ → LeF L Lo lV₀ lV₀′ x x′ → LeF L Lo lV lV′ (nw p x) (nw p′ x′)
  niᴸ  : ∀ {V V′ k} {lV : Lg V} {lV′ : Lg V′} {r : StH V k L} {r′ : StH V′ k L}
           {u : ∀ {W′} → V ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} {u′ : ∀ {W′} → V′ ⊲ W′ → Lg W′ → Vs L r′ W′ → D L W′} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
            ∀ y y′ → Lo r r′ lc lc′ y y′ → LeF L Lo lc lc′ (u p lc y) (u′ p′ lc′ y′)) →
         LeF L Lo lV lV′ (ni r u) (ni r′ u′)
  κᴸ   : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {zz zz′ : NZ L}
           {u : ∀ {c} → V ⊲ c → Lg c → D L c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D L c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → CP lV lV′ p lc p′ lc′ →
            LeF L Lo lc lc′ (u p lc) (u′ p′ lc′)) →
         LeF L Lo lV lV′ (nκ zz u) (nκ zz′ u′)

Rel   : ∀ L {V V′} → Lg V → Lg V′ → D L V → D L V′ → Set
Below : ∀ L → LoT L
RelS  : ∀ L {V k c c′} → StH V k L → Lg c → Lg c′ → D k c → D k c′ → Set
RelAt : ∀ b {V k c c′} → k ⊲[ V ] b → Lg c → Lg c′ → D k c → D k c′ → Set

Rel L = LeF L (Below L)
Below L r r′ lc lc′ y y′ = RelS L r lc lc′ (outS r y) (outS r′ y′)
RelS (hs b) (ss P) = RelAt b P
RelS (hl f) (sl n P) = RelAt (f n) P
RelS (hΩ g) (sL e P) = RelAt (g _) P
RelAt b hself = Rel b
RelAt (hs b) (hsuc P) = RelAt b P
RelAt (hl f) (hlim n P) = RelAt (f n) P
RelAt (hΩ g) (hLim e P) = RelAt (g _) P
```

## 2 坐标关系与 `Rel k` 的互换

沿位置, 每一步定义性. 把树放进节点再取出 (`outS r (inS r z)`) 只在命题意义上等于 $z$ (`out-inS`, 对位置归纳, 每一步 `refl`).

```agda
atOut : ∀ b {V k c c′} (P : k ⊲[ V ] b) {lc : Lg c} {lc′ : Lg c′} {z : D k c} {z′ : D k c′} → RelAt b P lc lc′ z z′ → Rel k lc lc′ z z′
atOut b hself h = h
atOut (hs b) (hsuc P) h = atOut b P h
atOut (hl f) (hlim n P) h = atOut (f n) P h
atOut (hΩ g) (hLim e P) h = atOut (g _) P h

atIn : ∀ b {V k c c′} (P : k ⊲[ V ] b) {lc : Lg c} {lc′ : Lg c′} {z : D k c} {z′ : D k c′} → Rel k lc lc′ z z′ → RelAt b P lc lc′ z z′
atIn b hself h = h
atIn (hs b) (hsuc P) h = atIn b P h
atIn (hl f) (hlim n P) h = atIn (f n) P h
atIn (hΩ g) (hLim e P) h = atIn (g _) P h

sOut : ∀ L {V k c c′} (r : StH V k L) {lc : Lg c} {lc′ : Lg c′} {z : D k c} {z′ : D k c′} → RelS L r lc lc′ z z′ → Rel k lc lc′ z z′
sOut (hs b) (ss P) = atOut b P
sOut (hl f) (sl n P) = atOut (f n) P
sOut (hΩ g) (sL e P) = atOut (g _) P

sIn : ∀ L {V k c c′} (r : StH V k L) {lc : Lg c} {lc′ : Lg c′} {z : D k c} {z′ : D k c′} → Rel k lc lc′ z z′ → RelS L r lc lc′ z z′
sIn (hs b) (ss P) = atIn b P
sIn (hl f) (sl n P) = atIn (f n) P
sIn (hΩ g) (sL e P) = atIn (g _) P

out-inC : ∀ {b W a u} (P : a ⊲[ W ] b) (x : D a u) → outC P (inC P x) ≡ x
out-inC hself x = refl
out-inC (hsuc P) x = out-inC P x
out-inC (hlim n P) x = out-inC P x
out-inC (hLim e P) x = out-inC P x

out-inS : ∀ {L W k u} (R : StH W k L) (x : D k u) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x
out-inS (sL e P) x = out-inC P x

belowOut : ∀ L {V V′ k c c′} (r : StH V k L) (r′ : StH V′ k L) {lc : Lg c} {lc′ : Lg c′} {y : Vs L r c} {y′ : Vs L r′ c′} →
           Below L r r′ lc lc′ y y′ → Rel k lc lc′ (outS r y) (outS r′ y′)
belowOut L r r′ h = sOut L r h

belowIn : ∀ L {V V′ k c c′} (r : StH V k L) (r′ : StH V′ k L) {lc : Lg c} {lc′ : Lg c′} {z : D k c} {z′ : D k c′} →
          Rel k lc lc′ z z′ → Below L r r′ lc lc′ (inS r z) (inS r′ z′)
belowIn L {k = k} r r′ {lc} {lc′} {z} {z′} h = sIn L r (subst₂ (Rel k lc lc′) (sym (out-inS r z)) (sym (out-inS r′ z′)) h)
```

## 3 第 0 层: 值可靠, `drp`, 自洽, 和的分解

```agda
vsum : ∀ {V V′ b b′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → Rel hz lV lV′ x x′ → b ≤ b′ → sum b x ≤ sum b′ x′
vsum {b′ = b′} {x′ = x′} n0ᴸ h = ≤-trans h (⊲→≤ (sum-fst b′ x′))
vsum n1ᴸ h = s≤ h
vsum {b = b} {b′} (⨾ᴸ {x = x} {y} {x′} {y′} hx hy) h = vsum {b = sum b x} {sum b′ x′} {x = y} {y′} hy (vsum {x = x} {x′} hx h)
vsum {b = b} {b′} (nlᴸ {d = d} {d′} hd) h = l≤ (λ n → ≤l n (go n))
  where
  go : ∀ n → pt b d n ≤ pt b′ d′ n
  go zero = h
  go (suc n) = vsum {b = pt b d n} {pt b′ d′ n} {x = d n} {d′ n} (hd n) (go n)
vsum {b = b} {b′} (prᴸ {x = x} {x′ = x′} {y′} hx) h = ≤-trans (vsum {b = b} {b′} {x = x} {x′} hx h) (⊲→≤ (sum-fst (sum b′ x′) y′))
vsum {b = b} {b′} (nwAᴸ {x = x} {x′} hp hx) h = vsum {b = b} {b′} {x = x} {x′} hx h
vsum (niᴸ {r = ()} h)
vsum (κᴸ {zz = ()} h)

drpR : ∀ {V V′ U U′} {lV : Lg V} {lV′ : Lg V′} {lU : Lg U} {lU′ : Lg U′} {x : D₀ V} {x′ : D₀ V′} →
       Rel hz lV lV′ x x′ → Rel hz lU lU′ (drp {W′ = U} x) (drp {W′ = U′} x′)
drpR n0ᴸ = n0ᴸ
drpR n1ᴸ = n1ᴸ
drpR (⨾ᴸ hx hy) = ⨾ᴸ (drpR hx) (drpR hy)
drpR (nlᴸ hd) = nlᴸ (λ n → drpR (hd n))
drpR (prᴸ hx) = prᴸ (drpR hx)
drpR (nwAᴸ hp hx) = drpR hx
drpR (niᴸ {r = ()} h)
drpR (κᴸ {zz = ()} h)

lgsf : ∀ {V} b (x : D₀ V) (w : Lg b) → lg⊲ (sum-fst b x) (Lg-sum b x w) ≡ w
lgsf b n0 w = refl
lgsf b n1 w = refl
lgsf b (x ⨾ y) w =
  trans (lg-tr (sum-fst b x) (sum-fst (sum b x) y) (Lg-sum (sum b x) y (Lg-sum b x w)))
        (trans (cong (lg⊲ (sum-fst b x)) (lgsf (sum b x) y (Lg-sum b x w))) (lgsf b x w))
lgsf b (nl d) w = refl
lgsf b (ni () u) w
lgsf b (nκ () u) w
lgsf b (nw p x) w = lgsf b x w

cohSum : ∀ {V} b (x : D₀ V) (w : Lg b) → Coh w → Coh (Lg-sum b x w)
cohPt  : ∀ {V} b (d : ℕ → D₀ V) n (w : Lg b) → Coh w → Coh (Lg-pt b d n w)
cohSum b n0 w c = c
cohSum b n1 w c = c
cohSum b (x ⨾ y) w c = cohSum (sum b x) y (Lg-sum b x w) (cohSum b x w c)
cohSum b (nl d) w c = (λ n → lgsf (pt b d n) (d n) (Lg-pt b d n w)) , (λ n → cohPt b d n w c)
cohSum b (ni () u) w c
cohSum b (nκ () u) w c
cohSum b (nw p x) w c = cohSum b x w c
cohPt b d zero w c = c
cohPt b d (suc n) w c = cohSum (pt b d n) (d n) (Lg-pt b d n w) (cohPt b d n w c)

-- 和的分解: Σ_b x 与 b ⊞ Σ_0 x 互相 ≤
sumA : ∀ {V} b (x : D₀ V) → (sum b x ≤ b ⊞ sum azero x) × (b ⊞ sum azero x ≤ sum b x)
ptA  : ∀ {V} b (d : ℕ → D₀ V) n → (pt b d n ≤ b ⊞ pt azero d n) × (b ⊞ pt azero d n ≤ pt b d n)
sumA b n0 = ≤-refl b , ≤-refl b
sumA b n1 = ≤-refl _ , ≤-refl _
sumA b (x ⨾ y) =
  ≤-trans (proj₁ (sumA (sum b x) y))
    (≤-trans (⊞-mono (proj₁ (sumA b x)) (≤-refl _)) (≤-trans (⊞-assoʳ b _ _) (⊞-mono (≤-refl b) (proj₂ (sumA (sum azero x) y))))) ,
  ≤-trans (⊞-mono (≤-refl b) (proj₁ (sumA (sum azero x) y)))
    (≤-trans (⊞-asso b _ _) (≤-trans (⊞-mono (proj₂ (sumA b x)) (≤-refl _)) (proj₂ (sumA (sum b x) y))))
sumA b (nl d) = l≤ (λ n → ≤l n (proj₁ (ptA b d n))) , l≤ (λ n → ≤l n (proj₂ (ptA b d n)))
sumA b (ni () u)
sumA b (nκ () u)
sumA b (nw p x) = sumA b x
ptA b d zero = ≤-refl b , ≤-refl b
ptA b d (suc n) =
  ≤-trans (proj₁ (sumA (pt b d n) (d n)))
    (≤-trans (⊞-mono (proj₁ (ptA b d n)) (≤-refl _)) (≤-trans (⊞-assoʳ b _ _) (⊞-mono (≤-refl b) (proj₂ (sumA (pt azero d n) (d n)))))) ,
  ≤-trans (⊞-mono (≤-refl b) (proj₁ (sumA (pt azero d n) (d n))))
    (≤-trans (⊞-asso b _ _) (≤-trans (⊞-mono (proj₂ (ptA b d n)) (≤-refl _)) (proj₂ (sumA (pt b d n) (d n)))))

-- 一段极限的尾巴 (同 StrRel4Gen.Tail)
module Tail {V} (b : A) (d : ℕ → D₀ V) where
  tl : ℕ → D₀ V
  tl m = nl (λ j → d (j + m))

  ptsh : ∀ m j → pt (pt b d m) (λ i → d (i + m)) j ≡ pt b d (j + m)
  ptsh m zero = refl
  ptsh m (suc j) = cong (λ t → sum t (d (j + m))) (ptsh m j)

  pt-mono : ∀ i k → pt b d i ≤ pt b d (k + i)
  pt-mono i zero = ≤-refl _
  pt-mono i (suc k) = ≤-trans (pt-mono i k) (⊲→≤ (sum-fst (pt b d (k + i)) (d (k + i))))

  ≡→≤ : ∀ {a c} → a ≡ c → a ≤ c
  ≡→≤ {a} refl = ≤-refl a

  tup : ∀ m → alim (pt b d) ≤ sum (pt b d m) (tl m)
  tup m = l≤ (λ j → ≤l j (≤-trans (subst (λ k → pt b d j ≤ pt b d k) (+-comm m j) (pt-mono j m)) (≡→≤ (sym (ptsh m j)))))

  tdn : ∀ m → sum (pt b d m) (tl m) ≤ alim (pt b d)
  tdn m = l≤ (λ j → ≤l (j + m) (≡→≤ (ptsh m j)))
```

## 4 由第 0 层关系生成对齐 (`StrRel4Pr.genᴾ` 的主线版)

```agda
genAl : ∀ {L L′ V V′ b b′} {lV : Lg V} {lV′ : Lg V′} {x : D₀ V} {x′ : D₀ V′} → Rel hz lV lV′ x x′ →
        (w : Lg b) (w′ : Lg b′) → b ≤ b′ → Adm (sum b x) (sum b′ x′) L L′ →
        Al L L′ (sum-fst b x) (Lg-sum b x w) (sum-fst b′ x′) (Lg-sum b′ x′ w′)
genAl {b′ = b′} {x′ = x′} n0ᴸ w w′ h ad = aS (sum-fst b′ x′) (Lg-sum b′ x′ w′)
genAl {b = b} {b′} n1ᴸ w w′ h ad = aP (aS C.self w′) h (adm-tr (stepA b b′) ad)
genAl {b = b} {b′} (⨾ᴸ {x = x} {y} {x′} {y′} hx hy) w w′ h ad =
  cat (genAl hx w w′ h (adm-tr (al-adm Gy) ad)) Gy
      (sym (lgsf (sum b x) y (Lg-sum b x w))) (sym (lgsf (sum b′ x′) y′ (Lg-sum b′ x′ w′)))
  where Gy = genAl hy (Lg-sum b x w) (Lg-sum b′ x′ w′) (vsum {b = b} {b′} {x = x} {x′} hx h) ad
genAl {b = b} {b′} (nlᴸ {d = d} {d′} hd) w w′ h ad =
  aL (aS C.self w′) (λ m → genAl (hd (m + 0)) (Lg-pt b d (m + 0) w) (Lg-pt b′ d′ (m + 0) w′) (ptle (m + 0)) (seg (m + 0)))
  where
  module T = Tail b d
  module T′ = Tail b′ d′
  ptle : ∀ n → pt b d n ≤ pt b′ d′ n
  ptle zero = h
  ptle (suc n) = vsum {b = pt b d n} {pt b′ d′ n} {x = d n} {d′ n} (hd n) (ptle n)
  tadm : ∀ j → Adm (pt b d j) (pt b′ d′ j) (alim (pt b d)) (alim (pt b′ d′))
  tadm j = sum azero (T.tl j) ,
           ≤-trans (T.tup j) (proj₁ (sumA (pt b d j) (T.tl j))) ,
           ≤-trans (⊞-mono (≤-refl _) (vsum (nlᴸ (λ i → hd (i + j))) (z≤ {b = azero})))
             (≤-trans (proj₂ (sumA (pt b′ d′ j) (T′.tl j))) (T′.tdn j))
  seg : ∀ n → Adm (sum (pt b d n) (d n)) (sum (pt b′ d′ n) (d′ n)) _ _
  seg n = adm-tr (tadm (suc n)) ad
genAl {b′ = b′} (prᴸ {x′ = x′} {y′} hx) w w′ h ad =
  ext (sum-fst (sum b′ x′) y′) (Lg-sum (sum b′ x′) y′ (Lg-sum b′ x′ w′)) (sym (lgsf (sum b′ x′) y′ (Lg-sum b′ x′ w′)))
      (genAl hx w w′ h (adm-lo (⊲→≤ (sum-fst (sum b′ x′) y′)) ad))
genAl (nwAᴸ hp hx) w w′ h ad = genAl hx w w′ h ad
genAl (niᴸ {r = ()} h)
genAl (κᴸ {zz = ()} h)
```
