# 和形式, 高度取 $A$ (四): 每站严格增长

> 不含记号. 入口 [SumHt](SumHt.lagda.md). 序是布劳威尔树上的 `_≤_` ([TLRuleSpec](TLRuleSpec.lagda.md), 不读记号). 四条, 都对一切 $n,a$, 没有按站定制:
>
> - `S1`: `asuc (T n a) ≤ T n (suc a)`.
> - `S2`: `T n a ≤ T (suc n) 0`.
> - `S3`: `T n 0 ≤ Tω`.
> - `S4`: `asuc Tω ≤ T²`.
>
> 由此要求的四站一站高过一站 (`Ω+1<Ω+2`, `Ω+2<Ω·2`, `Ω·2<Ω·ω`, `Ω·ω<Ω²`). **这只说明站不塌缩: 后一站的折叠字面地含前一站的折叠, 再多出一段非零.** 多出多少 (例如 `T 2 0` 是否高过一切 `T 1 a` 的折叠的不动点) 这里没有定理.
>
> 证明只用三件事: (L1) 右结合的前缀与 `nl` 的部分和字面相同 (`Pfx`, `L1`); (L2) 一个分支为 $1$ 的节点在第 $(0,0)$ 个目标上的输出非零, 只要状态在各目标上非零 (`Inv`); (L4) 回灌第一格走的路非零.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumHtGrow where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; Strict)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumHtTree
open import OCF.Align.SumHtClosed
```

## §1 非零

`NZ₀ x`: 沿 `⨾`, `nl` 的第 0 项, `nw` 能走到一个 `n1`, 不经过节点.

```agda
data NZ₀ {Kd : A → A → A → Set} {V′ : ∀ {W h k} → Kd W h k → A → Set} {Z : Set} : ∀ {W} → D₊ Kd V′ Z W → Set where
  nz1 : ∀ {W} → NZ₀ (n1 {W = W})
  nzL : ∀ {W} {x y : D₊ Kd V′ Z W} → NZ₀ x → NZ₀ (x ⨾ y)
  nzR : ∀ {W} {x y : D₊ Kd V′ Z W} → NZ₀ y → NZ₀ (x ⨾ y)
  nzl : ∀ {W} {e : ℕ → D₊ Kd V′ Z W} → NZ₀ (e 0) → NZ₀ (nl e)
  nzw : ∀ {W₀ W} {p : W₀ ⊲ W} {x : D₊ Kd V′ Z W₀} → NZ₀ x → NZ₀ (nw p x)

sum≥ : ∀ {W} b (x : D₀ W) → b ≤ sum b x
sum≥ b x = ⊲→≤ (sum-fst b x)

nz≤ : ∀ {W} b {x : D₀ W} → NZ₀ x → asuc b ≤ sum b x
nz≤ b nz1 = ≤-refl _
nz≤ b {x ⨾ y} (nzL d) = ≤-trans (nz≤ b d) (sum≥ (sum b x) y)
nz≤ b {x ⨾ y} (nzR d) = ≤-trans (s≤ (sum≥ b x)) (nz≤ (sum b x) d)
nz≤ b (nzl d) = ≤l 1 (nz≤ b d)
nz≤ b (nzw {x = x′} d) = nz≤ b {x′} d

nz-drp : ∀ {W W′} {x : D₀ W} → NZ₀ x → NZ₀ (drp {W} {W′} x)
nz-drp nz1 = nz1
nz-drp (nzL d) = nzL (nz-drp d)
nz-drp (nzR d) = nzR (nz-drp d)
nz-drp (nzl d) = nzl (nz-drp d)
nz-drp (nzw {x = x′} d) = nz-drp {x = x′} d

-- 一格 Step 在每个目标上非零: Ωd 以 n1 开头
nz-Step : ∀ {W} (Y : St W) {q t m} (T : Tg W q t m) → NZ₀ (yc (Step Y) T)
nz-Step Y T = nzl (nzL (nzL nz1))

record Inv {W : A} (Y : St W) : Set where
  constructor iv
  field
    nzI : ∀ {q t m} (T : Tg W q t m) → NZ₀ (yc (d Y) T)
open Inv public

inv⊕ : ∀ {W} {Y : St W} (lW : Lg W) (Δ′ : Df W) → Inv Y → Inv (Y ⊕⟨ lW ⟩ Δ′)
inv⊕ lW Δ′ v = iv (λ T → nzL (nzI v T))

invcv : ∀ {W W′} (q : W ⊲ W′) {Y : St W} → Inv Y → Inv (cv q Y)
invcv q v = iv (λ T → nzI v (tg↑ q T))
```

## §2 不经过节点的路 (L3), 一个节点 (L2)

```agda
record NZA {ly : Ly} {W : A} (A₀ : Ig ly W) (lW : Lg W) {m : A} (T : Tg W azero azero m) : Set where
  constructor na
  field
    nzA : ∀ (w : Dl ly W) (Y : St W) → NZ₀ (yc (A₀ C.self lW w Y) T)
open NZA public

nz-Act : ∀ {ly W} (lW : Lg W) {m} (T : Tg W azero azero m) → NZA {ly} Act lW T
nz-Act lW T = na (λ w Y → nz-Step Y T)

L3 : ∀ {ly W₀ W} (ac : AccY ly) {x : Dl ly W₀} (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) {m} (T : Tg W azero azero m) →
     NZA A₀ lW T → NZ₀ x → ∀ w Y → NZ₀ (yc (Run ac x q₀ lW ll A₀ w Y) T)
L3 ac q₀ lW ll A₀ T h nz1 w Y = nzA h w Y
L3 ac q₀ lW ll A₀ T h (nzL nx) w Y = nzL (L3 ac q₀ lW ll A₀ T h nx w Y)
L3 ac q₀ lW ll A₀ T h (nzR ny) w Y = nzR (L3 ac q₀ lW ll A₀ T h ny _ _)
L3 ac q₀ lW ll A₀ T h (nzl nd) w Y = nzl (L3 ac q₀ lW ll A₀ T h nd w Y)
L3 ac q₀ lW ll A₀ T h (nzw {p = p} nx) w Y = L3 ac (⊲-tr p q₀) lW ll A₀ T h nx w Y

-- 分支为 1 的节点
c1 : ∀ {ly W₀ h k} (r : K ly W₀ h k) → ∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′
c1 r _ _ _ = n1

L2′ : ∀ {ly W₀ W h k m} (ac : AccY ly) (ac′ : AccY (lay h k)) (r : K ly W₀ h k) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : Dl ly W) (Y : St W)
      (T : Tg W azero azero m) → NZA A₀ lW T → Inv Y → (x : Rk h k azero azero m) → NZ₀ (RKi ac ac′ r (c1 r) q₀ lW ll A₀ w Y T x)
L2′ ac ac′ r q₀ lW ll A₀ w Y T hA v (keep (sm ()))
L2′ ac ac′ r q₀ lW ll A₀ w Y T hA v (keep (lo () e))
L2′ {ly} ac ac′ r q₀ lW ll A₀ w Y T hA v rise =
  nzl (L3 ac′ C.self lW (kk ly r q₀ ll) (Ai ac ac′ r (c1 r) q₀ (kk ly r q₀ ll) ll A₀ w) T (na (λ z Y′ → nzA hA _ Y′))
          (nzI v (tg C.self (proj₁ (kk ly r q₀ ll)) (proj₂ (kk ly r q₀ ll)) lW)) n0 Y)

L2 : ∀ {ly W₀ W h k m} (ac : AccY ly) (r : K ly W₀ h k) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : Dl ly W) (Y : St W)
     (T : Tg W azero azero m) → NZA A₀ lW T → Inv Y → NZ₀ (yc (Run ac (ni r (c1 r)) q₀ lW ll A₀ w Y) T)
L2 {ly} (acc f) r q₀ lW ll A₀ w Y T hA v =
  L2′ (acc f) (f r) r q₀ lW ll A₀ w Y T hA v
      (rkT (⊲-tr (proj₁ (kk ly r q₀ ll)) (wm T)) (⊲-tr (proj₂ (kk ly r q₀ ll)) (wm T)) (qm T) (tm T) (lm T))
```

## §3 前缀与部分和 (L1)

站都在顶层, 世界 $\omega$, 一格是 `Act`.

```agda
R : D̂ ω → D̂ ω → St ω → Df ω
R x w Y = Run accTop x C.self lω tt Act w Y

τ : Tg ω azero azero ω
τ = τ₀ lω

module P (F : ℕ → D̂ ω) (w : D̂ ω) (Y : St ω) where
  Rp : ℕ → D̂ ω × St ω
  Rp = Rpt accTop F C.self lω tt Act w Y

  dF : ℕ → D₀ ω
  dF j = yc (R (F j) (proj₁ (Rp j)) (proj₂ (Rp j))) τ

  ptF : A → ℕ → ℕ → A
  ptF b k zero = b
  ptF b k (suc n) = ptF (sum b (dF k)) (suc k) n

  L1 : ∀ n k tl b → sum b (yc (R (Pfx F k n tl) (proj₁ (Rp k)) (proj₂ (Rp k))) τ) ≡ sum (ptF b k n) (yc (R tl (proj₁ (Rp (k + n))) (proj₂ (Rp (k + n)))) τ)
  L1 zero k tl b = cong (λ j → sum b (yc (R tl (proj₁ (Rp j)) (proj₂ (Rp j))) τ)) (sym (+-identityʳ k))
  L1 (suc n) k tl b =
    trans (L1 n (suc k) tl (sum b (dF k)))
          (cong (λ j → sum (ptF (sum b (dF k)) (suc k) n) (yc (R tl (proj₁ (Rp j)) (proj₂ (Rp j))) τ)) (sym (+-suc k n)))

  L1b : ∀ n k b → ptF b k (suc n) ≡ sum (ptF b k n) (dF (k + n))
  L1b zero k b = cong (λ j → sum b (dF j)) (sym (+-identityʳ k))
  L1b (suc n) k b = trans (L1b n (suc k) (sum b (dF k))) (cong (λ j → sum (ptF (sum b (dF k)) (suc k) n) (dF j)) (sym (+-suc k n)))

  ptF≡pt : ∀ n b → ptF b 0 n ≡ pt b dF n
  ptF≡pt zero b = refl
  ptF≡pt (suc n) b = trans (L1b n 0 b) (cong (λ x → sum x (dF n)) (ptF≡pt n b))

  inv-Rp : Inv Y → ∀ j → Inv (proj₂ (Rp j))
  inv-Rp v zero = v
  inv-Rp v (suc j) = inv⊕ lω (R (F j) (proj₁ (Rp j)) (proj₂ (Rp j))) (inv-Rp v j)

≡≤ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
≡≤ refl q = q

≤≡ : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤≡ q refl = q
```

## §4 各站的形状

$T(X)=\mathrm{sum}\ b_0\ (\ldots)$, $b_0=1+\psi_0(1)$ 的那一段 (第一个 `n1` 的 `Step`). 之后是 `B` 的前缀.

```agda
w₁ : D̂ ω
w₁ = n0 ⨾ nw C.self n1

Y₁ : St ω
Y₁ = Y₀ ⊕⟨ lω ⟩ Step (Y₀ {ω})

b₀ : A
b₀ = sum (sum {ω} azero n1) (yc (Step (Y₀ {ω})) τ)

inv-Y₁ : Inv Y₁
inv-Y₁ = iv (λ T → nzR (nz-Step (Y₀ {ω}) T))

module PB = P B w₁ Y₁

WB : ℕ → D̂ ω × St ω
WB = PB.Rp

module PN (n : ℕ) = P (nd n) (proj₁ (WB n)) (proj₂ (WB n))

β : ℕ → A
β n = PB.ptF b₀ 0 n

-- T n a 是两层前缀
T≡ : ∀ n a → T n a ≡ PN.ptF n (β n) 0 a
T≡ n a = trans (PB.L1 n 0 (Pfx (nd n) 0 a n0) b₀) (PN.L1 n a 0 n0 (β n))

Tω≡ : Tω ≡ alim (pt b₀ PB.dF)
Tω≡ = refl
```

## §5 四条定理

```agda
inv-WB : ∀ n → Inv (proj₂ (WB n))
inv-WB = PB.inv-Rp inv-Y₁

nz-nd : ∀ n j → NZ₀ (PN.dF n j)
nz-nd n j = L2 accTop (nω n , nω j) C.self lω tt Act (proj₁ (PN.Rp n j)) (proj₂ (PN.Rp n j)) τ (nz-Act lω τ) (PN.inv-Rp n (inv-WB n) j)

S1 : ∀ n a → asuc (T n a) ≤ T n (suc a)
S1 n a =
  ≡≤ (cong asuc (T≡ n a))
     (≤≡ (nz≤ (PN.ptF n (β n) 0 a) (nz-nd n (0 + a))) (sym (trans (T≡ n (suc a)) (PN.L1b n a 0 (β n)))))

-- 高度后继的第一站: B n 的部分和
T0≡ : ∀ n → T (suc n) 0 ≡ sum (β n) (PB.dF n)
T0≡ n = trans (T≡ (suc n) 0) (PB.L1b n 0 b₀)

S2 : ∀ n a → T n a ≤ T (suc n) 0
S2 n a =
  ≡≤ (trans (T≡ n a) (PN.ptF≡pt n a (β n)))
     (≤≡ (⊲→≤ (⊲-tr (C.lim a C.self) (sum-fst (alim (pt (β n) (PN.dF n))) (yc (R (κB n) (proj₁ (WB n) ⨾ nw C.self (nl (nd n))) (proj₂ (WB n) ⊕⟨ lω ⟩ R (nl (nd n)) (proj₁ (WB n)) (proj₂ (WB n)))) τ)))) (sym (T0≡ n)))

S3 : ∀ n → T n 0 ≤ Tω
S3 n = ≡≤ (trans (T≡ n 0) (PB.ptF≡pt n b₀)) (⊲→≤ (C.lim n C.self))
```

**S4.** `T²` 在 `Tω` 之后接上高度的闭包 `κH`, 它在第 $(0,0)$ 个目标上是回灌的格子; 第一格走 $[\omega,\omega+z)$, $z$ 是到此为止的输出, 非零. 路的非零 (L4) 按 `sum-fst` 的形状归纳.

```agda
module W (V₁ : A) (lV : Lg V₁) (A₀ : Ig top V₁) (hA : NZA A₀ lV (τ₀ lV)) where
  u² : ∀ {c} → ω ⊲ c → Lg c → D̂ c
  u² {c} _ _ = ni (C.self , z⊲ c) (λ _ _ _ → n1)

  NZW : ∀ b {a} → a ⊲ b → ω ⊲ a → Lg b → Set
  NZW b P ap lb = ∀ (bV : b ⊲ V₁) co (Y : St V₁) → Inv Y → NZ₀ (yc (Walk accTop u² b P ap lb bV lV tt A₀ co Y) (τ₀ lV))

  W-suc : ∀ c {a} (P : a ⊲ c) ap lb → NZW (asuc c) (C.suc P) ap lb
  W-suc c P ap lb bV co Y v =
    nzR (L2 accTop (C.self , z⊲ c) (⊲-tr (C.suc C.self) bV) lV tt A₀ (co ⨾ Cut u² c P ap lb (⊲-tr (C.suc C.self) bV))
           (Y ⊕⟨ lV ⟩ Walk accTop u² c P ap lb (⊲-tr (C.suc C.self) bV) lV tt A₀ co Y) (τ₀ lV) hA
           (inv⊕ lV (Walk accTop u² c P ap lb (⊲-tr (C.suc C.self) bV) lV tt A₀ co Y) v))

  W-ext : ∀ {W₀′} b″ {a} (P : a ⊲ b″) ap lb″ (y : D₀ W₀′) → NZW b″ P ap lb″ → NZW (sum b″ y) (⊲-tr P (sum-fst b″ y)) ap (Lg-sum b″ y lb″)
  W-ext b″ P ap lb″ n0 h = h
  W-ext b″ P ap lb″ n1 h = W-suc b″ P ap lb″
  W-ext b″ P ap lb″ (y₁ ⨾ y₂) h =
    subst (λ π → NZW (sum (sum b″ y₁) y₂) π ap (Lg-sum (sum b″ y₁) y₂ (Lg-sum b″ y₁ lb″)))
          (sym (⊲-as P (sum-fst b″ y₁) (sum-fst (sum b″ y₁) y₂)))
          (W-ext (sum b″ y₁) (⊲-tr P (sum-fst b″ y₁)) ap (Lg-sum b″ y₁ lb″) y₂ (W-ext b″ P ap lb″ y₁ h))
  W-ext b″ P ap lb″ (nl e) h bV co Y v = nzL (h _ co Y v)
  W-ext b″ P ap lb″ (ni (sm ()) u) h
  W-ext b″ P ap lb″ (ni (lo () e) u) h
  W-ext b″ P ap lb″ (nκ (inj₁ ()) u) h
  W-ext b″ P ap lb″ (nκ (inj₂ ()) u) h
  W-ext b″ P ap lb″ (nw p y) h = W-ext b″ P ap lb″ y h

  L4 : ∀ {W₀′} (z′ : D₀ W₀′) → NZ₀ z′ → ∀ b′ {a} (Rr : a ⊲ b′) ap lb′ → NZW (sum b′ z′) (⊲-tr Rr (sum-fst b′ z′)) ap (Lg-sum b′ z′ lb′)
  L4 n1 nz1 b′ Rr ap lb′ = W-suc b′ Rr ap lb′
  L4 (x ⨾ y) (nzL nx) b′ Rr ap lb′ =
    subst (λ π → NZW (sum (sum b′ x) y) π ap (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)))
          (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y)))
          (W-ext (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) ap (Lg-sum b′ x lb′) y (L4 x nx b′ Rr ap lb′))
  L4 (x ⨾ y) (nzR ny) b′ Rr ap lb′ =
    subst (λ π → NZW (sum (sum b′ x) y) π ap (Lg-sum (sum b′ x) y (Lg-sum b′ x lb′)))
          (sym (⊲-as Rr (sum-fst b′ x) (sum-fst (sum b′ x) y)))
          (L4 y ny (sum b′ x) (⊲-tr Rr (sum-fst b′ x)) ap (Lg-sum b′ x lb′))
  L4 (nl e) (nzl ne) b′ Rr ap lb′ bV co Y v =
    nzR (nzl (subst (λ π → NZW (sum b′ (e 0)) π (⊲-tr ap Rr) (Lg-sum b′ (e 0) lb′)) (⊲-idl (sum-fst b′ (e 0)))
                    (L4 (e 0) ne b′ C.self (⊲-tr ap Rr) lb′) (⊲-tr (C.lim 1 C.self) bV) (co ⨾ Cut u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV))
                    (Y ⊕⟨ lV ⟩ Walk accTop u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV tt A₀ co Y)
                    (inv⊕ lV (Walk accTop u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV tt A₀ co Y) v)))
  L4 (nw p x) (nzw nx) b′ Rr ap lb′ = L4 x nx b′ Rr ap lb′

-- κH 之前的状态
w₂ : D̂ ω
w₂ = w₁ ⨾ nw C.self (nl B)

Y₂ : St ω
Y₂ = Y₁ ⊕⟨ lω ⟩ R (nl B) w₁ Y₁

inv-Y₂ : Inv Y₂
inv-Y₂ = inv⊕ lω (R (nl B) w₁ Y₁) inv-Y₁

nz-z₂ : NZ₀ (z Y₂)
nz-z₂ = nzL (nzR (nz-Step (Y₀ {ω}) τ))

nz-κH : NZ₀ (yc (R κH w₂ Y₂) τ)
nz-κH =
  nzl (nz-drp (W.L4 (sum ω (z Y₂)) (Lg-sum ω (z Y₂) lω) (Ig↾ (sum-fst ω (z Y₂)) Act) (nz-Act (Lg-sum ω (z Y₂) lω) (τ₀ (Lg-sum ω (z Y₂) lω)))
                    (z Y₂) nz-z₂ ω C.self C.self lω C.self (nw (sum-fst ω (z Y₂)) w₂) (cv (sum-fst ω (z Y₂)) Y₂) (invcv (sum-fst ω (z Y₂)) inv-Y₂)))

S4 : asuc Tω ≤ T²
S4 = nz≤ Tω nz-κH
```

## §6 要求的各站

```agda
Ω<Ω+1 : asuc (T 1 0) ≤ TΩ+1
Ω<Ω+1 = S1 1 0

Ω+1<Ω+2 : asuc TΩ+1 ≤ TΩ+2
Ω+1<Ω+2 = S1 1 1

Ω+2<Ω·2 : asuc TΩ+2 ≤ TΩ·2
Ω+2<Ω·2 = ≤-trans (S1 1 2) (S2 1 3)

Ω·2<Ω·ω : asuc TΩ·2 ≤ TΩ·ω
Ω·2<Ω·ω = ≤-trans (S1 2 0) (≤-trans (S2 2 1) (S3 3))

Ω·ω<Ω² : asuc TΩ·ω ≤ TΩ²
Ω·ω<Ω² = S4

-- 一般形: 每站严格低于下一个高度的第一站, 也低于 Tω
lt-up : ∀ n a → asuc (T n a) ≤ T (suc n) 0
lt-up n a = ≤-trans (S1 n a) (S2 n (suc a))

lt-ω : ∀ n a → asuc (T n a) ≤ Tω
lt-ω n a = ≤-trans (lt-up n a) (S3 (suc n))
```
