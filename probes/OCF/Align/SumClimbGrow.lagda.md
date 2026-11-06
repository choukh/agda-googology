# 和形式, 层取三位 (四): 严格增长, 与前一族的上确界

> 不含记号. 入口 [SumClimb](SumClimb.lagda.md). 序是布劳威尔树上的 `_≤_` ([TLRuleSpec](TLRuleSpec.lagda.md)). 证法同 [SumHtGrow](SumHtGrow.lagda.md) (L1 前缀与部分和, L2 节点非零, L4 回灌第一格非零), 只换三位的层.
>
> 两类定理:
>
> - **不塌缩** (同上一轮): `S1` (下标后继), `S2` (第二位后继), `S3`/`S4` (第一位后继), `S5`/`S6` (到 `Tω`, `T³`).
> - **高于前一族的上确界** (`SupN`, `SupR`, `Sup3`): 一个闭包站严格高于前一族**任意可数多个**站的上确界. 例如 `SupR r g`: 对任何 $g:\mathbb N\to\mathbb N^2$, $\sup_k T(r,g_k)<T(r+1,0,0)$. 证法: 前一族都在 `nl` 那一段的极限 (`TNω`, `TRω`, `Tω`) 之下, 闭包节点在其后的回灌输出非零. **分辨力到此为止:** 多出的仍是 "极限之上一段非零", 不是 "高于前一族的某个闭包点" (那要折叠对世界单调, 没有做).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumClimbGrow where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲; Strict)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.SumClimbTree
open import OCF.Align.SumClimbClosed
```

## §1 非零

```agda
data NZ₀ {Kd : A → A → A → A → Set} {V′ : ∀ {W g h k} → Kd W g h k → A → Set} {Z : Set} : ∀ {W} → D₊ Kd V′ Z W → Set where
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

nz-Step : ∀ {W} (Y : St W) {r q t m} (T′ : Tg W r q t m) → NZ₀ (yc (Step Y) T′)
nz-Step Y T′ = nzl (nzL (nzL nz1))

record Inv {W : A} (Y : St W) : Set where
  constructor iv
  field
    nzI : ∀ {r q t m} (T′ : Tg W r q t m) → NZ₀ (yc (d Y) T′)
open Inv public

record IZ {W : A} (Y : St W) : Set where
  constructor izz
  field
    nzZ : NZ₀ (z Y)
open IZ public

inv⊕ : ∀ {W} {Y : St W} (lW : Lg W) (Δ′ : Df W) → Inv Y → Inv (Y ⊕⟨ lW ⟩ Δ′)
inv⊕ lW Δ′ v = iv (λ T′ → nzL (nzI v T′))

iz⊕ : ∀ {W} {Y : St W} (lW : Lg W) (Δ′ : Df W) → IZ Y → IZ (Y ⊕⟨ lW ⟩ Δ′)
iz⊕ lW Δ′ v = izz (nzL (nzZ v))

invcv : ∀ {W W′} (q : W ⊲ W′) {Y : St W} → Inv Y → Inv (cv q Y)
invcv q v = iv (λ T′ → nzI v (tg↑ q T′))
```

## §2 不经过节点的路 (L3), 一个节点 (L2)

```agda
record NZA {ly : Ly} {W : A} (A₀ : Ig ly W) (lW : Lg W) {m : A} (T′ : Tg W azero azero azero m) : Set where
  constructor na
  field
    nzA : ∀ (w : Dl ly W) (Y : St W) → NZ₀ (yc (A₀ C.self lW w Y) T′)
open NZA public

nz-Act : ∀ {ly W} (lW : Lg W) {m} (T′ : Tg W azero azero azero m) → NZA {ly} Act lW T′
nz-Act lW T′ = na (λ w Y → nz-Step Y T′)

L3 : ∀ {ly W₀ W} (ac : AccY ly) {x : Dl ly W₀} (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) {m} (T′ : Tg W azero azero azero m) →
     NZA A₀ lW T′ → NZ₀ x → ∀ w Y → NZ₀ (yc (Run ac x q₀ lW ll A₀ w Y) T′)
L3 ac q₀ lW ll A₀ T′ h nz1 w Y = nzA h w Y
L3 ac q₀ lW ll A₀ T′ h (nzL nx) w Y = nzL (L3 ac q₀ lW ll A₀ T′ h nx w Y)
L3 ac q₀ lW ll A₀ T′ h (nzR ny) w Y = nzR (L3 ac q₀ lW ll A₀ T′ h ny _ _)
L3 ac q₀ lW ll A₀ T′ h (nzl nd′) w Y = nzl (L3 ac q₀ lW ll A₀ T′ h nd′ w Y)
L3 ac q₀ lW ll A₀ T′ h (nzw {p = p} nx) w Y = L3 ac (⊲-tr p q₀) lW ll A₀ T′ h nx w Y

L2′ : ∀ {ly W₀ W g h k m} (ac : AccY ly) (ac′ : AccY (lay g h k)) (x : K ly W₀ g h k) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : Dl ly W) (Y : St W)
      (T′ : Tg W azero azero azero m) → NZA A₀ lW T′ → Inv Y → (o : Rk g h k azero azero azero m) → NZ₀ (RKi ac ac′ x (c1 x) q₀ lW ll A₀ w Y T′ o)
L2′ ac ac′ x q₀ lW ll A₀ w Y T′ hA v (keep (sm ()))
L2′ ac ac′ x q₀ lW ll A₀ w Y T′ hA v (keep (lo () e))
L2′ ac ac′ x q₀ lW ll A₀ w Y T′ hA v (keep (lr () e₁ e₂))
L2′ {ly} ac ac′ x q₀ lW ll A₀ w Y T′ hA v rise =
  nzl (L3 ac′ C.self lW (kk ly x q₀ ll) (Ai ac ac′ x (c1 x) q₀ (kk ly x q₀ ll) ll A₀ w) T′ (na (λ z′ Y′ → nzA hA _ Y′))
          (nzI v (tg C.self (proj₁ (kk ly x q₀ ll)) (proj₁ (proj₂ (kk ly x q₀ ll))) (proj₂ (proj₂ (kk ly x q₀ ll))) lW)) n0 Y)

L2 : ∀ {ly W₀ W g h k m} (ac : AccY ly) (x : K ly W₀ g h k) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : Dl ly W) (Y : St W)
     (T′ : Tg W azero azero azero m) → NZA A₀ lW T′ → Inv Y → NZ₀ (yc (Run ac (ni x (c1 x)) q₀ lW ll A₀ w Y) T′)
L2 {ly} (acc f) x q₀ lW ll A₀ w Y T′ hA v =
  L2′ (acc f) (f x) x q₀ lW ll A₀ w Y T′ hA v
      (rkT (⊲-tr (proj₁ (kk ly x q₀ ll)) (wm T′)) (⊲-tr (proj₁ (proj₂ (kk ly x q₀ ll))) (wm T′)) (⊲-tr (proj₂ (proj₂ (kk ly x q₀ ll))) (wm T′))
           (rm T′) (qm T′) (tm T′) (lm T′))
```

## §3 前缀与部分和 (L1)

```agda
R : D̂ ω → D̂ ω → St ω → Df ω
R x w Y = Run accTop x C.self lω tt Act w Y

τ : Tg ω azero azero azero ω
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

  iz-Rp : IZ Y → ∀ j → IZ (proj₂ (Rp j))
  iz-Rp v zero = v
  iz-Rp v (suc j) = iz⊕ lω (R (F j) (proj₁ (Rp j)) (proj₂ (Rp j))) (iz-Rp v j)

≡≤ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
≡≤ refl q = q

≤≡ : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤≡ q refl = q
```

## §4 回灌的第一格 (L4)

对任何闭包 `κN … ρ` (节点的层由 `ρ` 给), 对任何状态: 只要状态在各目标上非零 (`Inv`) 且到此为止的第 $(0,0,0)$ 层输出非零 (`IZ`), 它在目标 $(0,0,0)$ 上的输出非零. 按 `sum-fst` 的形状归纳, 同 `SumHtGrow`.

```agda
module W (G′ H′ K′ : A → A) (ρ : ∀ {c} → ω ⊲ c → KT c (G′ c) (H′ c) (K′ c)) (V₁ : A) (lV : Lg V₁) (A₀ : Ig top V₁) (hA : NZA A₀ lV (τ₀ lV)) where
  u² : ∀ {c} → ω ⊲ c → Lg c → D̂ c
  u² p _ = ni (ρ p) (c1 (ρ p))

  NZW : ∀ b {a} → a ⊲ b → ω ⊲ a → Lg b → Set
  NZW b P ap lb = ∀ (bV : b ⊲ V₁) co (Y : St V₁) → Inv Y → NZ₀ (yc (Walk accTop u² b P ap lb bV lV tt A₀ co Y) (τ₀ lV))

  W-suc : ∀ c {a} (P : a ⊲ c) ap lb → NZW (asuc c) (C.suc P) ap lb
  W-suc c P ap lb bV co Y v =
    nzR (L2 accTop (ρ (⊲-tr ap P)) (⊲-tr (C.suc C.self) bV) lV tt A₀ (co ⨾ Cut u² c P ap lb (⊲-tr (C.suc C.self) bV))
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
  W-ext b″ P ap lb″ (ni (lr () e₁ e₂) u) h
  W-ext b″ P ap lb″ (nκ (inj₁ ()) u) h
  W-ext b″ P ap lb″ (nκ (inj₂ (inj₁ ())) u) h
  W-ext b″ P ap lb″ (nκ (inj₂ (inj₂ ())) u) h
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

-- 闭包在任何满足 Inv, IZ 的状态上非零
nz-κ : ∀ (G′ H′ K′ : A → A) (ρ : ∀ {c} → ω ⊲ c → KT c (G′ c) (H′ c) (K′ c)) (w : D̂ ω) (Y : St ω) → Inv Y → IZ Y → NZ₀ (yc (R (κN G′ H′ K′ ρ) w Y) τ)
nz-κ G′ H′ K′ ρ w Y v iz =
  nzl (nz-drp (W.L4 G′ H′ K′ ρ (sum ω (z Y)) (Lg-sum ω (z Y) lω) (Ig↾ (sum-fst ω (z Y)) Act) (nz-Act (Lg-sum ω (z Y) lω) (τ₀ (Lg-sum ω (z Y) lω)))
                    (z Y) (nzZ iz) ω C.self C.self lω C.self (nw (sum-fst ω (z Y)) w) (cv (sum-fst ω (z Y)) Y) (invcv (sum-fst ω (z Y)) v)))
```

## §5 各站的形状

三层前缀: `BR` 的前 $r$ 项, `B r` 的前 $n$ 项, `nd r n` 的前 $a$ 项.

```agda
w₁ : D̂ ω
w₁ = n0 ⨾ nw C.self n1

Y₁ : St ω
Y₁ = Y₀ ⊕⟨ lω ⟩ Step (Y₀ {ω})

b₀ : A
b₀ = sum (sum {ω} azero n1) (yc (Step (Y₀ {ω})) τ)

inv-Y₁ : Inv Y₁
inv-Y₁ = iv (λ T′ → nzR (nz-Step (Y₀ {ω}) T′))

iz-Y₁ : IZ Y₁
iz-Y₁ = izz (nzR (nz-Step (Y₀ {ω}) τ))

module PR = P BR w₁ Y₁

WR : ℕ → D̂ ω × St ω
WR = PR.Rp

module PB (r : ℕ) = P (B r) (proj₁ (WR r)) (proj₂ (WR r))

WB : ℕ → ℕ → D̂ ω × St ω
WB r = PB.Rp r

module PN (r n : ℕ) = P (nd r n) (proj₁ (WB r n)) (proj₂ (WB r n))

βR : ℕ → A
βR r = PR.ptF b₀ 0 r

βB : ℕ → ℕ → A
βB r n = PB.ptF r (βR r) 0 n

T≡ : ∀ r n a → T r n a ≡ PN.ptF r n (βB r n) 0 a
T≡ r n a =
  trans (PR.L1 r 0 (Pfx (B r) 0 n (Pfx (nd r n) 0 a n0)) b₀)
        (trans (PB.L1 r n 0 (Pfx (nd r n) 0 a n0) (βR r)) (PN.L1 r n a 0 n0 (βB r n)))

TNω≡ : ∀ r n → TNω r n ≡ alim (pt (βB r n) (PN.dF r n))
TNω≡ r n = trans (PR.L1 r 0 (Pfx (B r) 0 n (nl (nd r n))) b₀) (PB.L1 r n 0 (nl (nd r n)) (βR r))

TRω≡ : ∀ r → TRω r ≡ alim (pt (βR r) (PB.dF r))
TRω≡ r = PR.L1 r 0 (nl (B r)) b₀

inv-WR : ∀ r → Inv (proj₂ (WR r))
inv-WR = PR.inv-Rp inv-Y₁

iz-WR : ∀ r → IZ (proj₂ (WR r))
iz-WR = PR.iz-Rp iz-Y₁

inv-WB : ∀ r n → Inv (proj₂ (WB r n))
inv-WB r = PB.inv-Rp r (inv-WR r)

iz-WB : ∀ r n → IZ (proj₂ (WB r n))
iz-WB r = PB.iz-Rp r (iz-WR r)

nz-nd : ∀ r n j → NZ₀ (PN.dF r n j)
nz-nd r n j =
  L2 accTop (nω r , (nω n , nω j)) C.self lω tt Act (proj₁ (PN.Rp r n j)) (proj₂ (PN.Rp r n j)) τ (nz-Act lω τ) (PN.inv-Rp r n (inv-WB r n) j)
```

## §6 不塌缩

```agda
S1 : ∀ r n a → asuc (T r n a) ≤ T r n (suc a)
S1 r n a =
  ≡≤ (cong asuc (T≡ r n a))
     (≤≡ (nz≤ (PN.ptF r n (βB r n) 0 a) (nz-nd r n a)) (sym (trans (T≡ r n (suc a)) (PN.L1b r n a 0 (βB r n)))))

-- 第二位后继的第一站: B r n 的部分和
TN0≡ : ∀ r n → T r (suc n) 0 ≡ sum (βB r n) (PB.dF r n)
TN0≡ r n = trans (T≡ r (suc n) 0) (PB.L1b r n 0 (βR r))

-- κB 之前的坐标与状态
wκB : ℕ → ℕ → D̂ ω
wκB r n = proj₁ (WB r n) ⨾ nw C.self (nl (nd r n))

YκB : ℕ → ℕ → St ω
YκB r n = proj₂ (WB r n) ⊕⟨ lω ⟩ R (nl (nd r n)) (proj₁ (WB r n)) (proj₂ (WB r n))

T≤TNω : ∀ r n a → T r n a ≤ TNω r n
T≤TNω r n a = ≡≤ (trans (T≡ r n a) (PN.ptF≡pt r n a (βB r n))) (≤≡ (⊲→≤ (C.lim a C.self)) (sym (TNω≡ r n)))

TNω<N : ∀ r n → asuc (TNω r n) ≤ T r (suc n) 0
TNω<N r n =
  ≡≤ (cong asuc (TNω≡ r n))
     (≤≡ (nz≤ (alim (pt (βB r n) (PN.dF r n))) (nz-κ _ _ _ (ρB r n) (wκB r n) (YκB r n) (inv⊕ lω _ (inv-WB r n)) (iz⊕ lω _ (iz-WB r n))))
         (sym (TN0≡ r n)))

S2 : ∀ r n a → T r n a ≤ T r (suc n) 0
S2 r n a = ≤-trans (T≤TNω r n a) (≤-trans (≤-suc′ (TNω r n)) (TNω<N r n))
  where
  ≤-suc′ : ∀ x → x ≤ asuc x
  ≤-suc′ x = ⊲→≤ (C.suc C.self)

-- 第一位后继
TR0≡ : ∀ r → T (suc r) 0 0 ≡ sum (βR r) (PR.dF r)
TR0≡ r = trans (T≡ (suc r) 0 0) (PR.L1b r 0 b₀)

wκR : ℕ → D̂ ω
wκR r = proj₁ (WR r) ⨾ nw C.self (nl (B r))

YκR : ℕ → St ω
YκR r = proj₂ (WR r) ⊕⟨ lω ⟩ R (nl (B r)) (proj₁ (WR r)) (proj₂ (WR r))

S3 : ∀ r n → T r n 0 ≤ TRω r
S3 r n = ≡≤ (trans (T≡ r n 0) (PB.ptF≡pt r n (βR r))) (≤≡ (⊲→≤ (C.lim n C.self)) (sym (TRω≡ r)))

S4 : ∀ r → asuc (TRω r) ≤ T (suc r) 0 0
S4 r =
  ≡≤ (cong asuc (TRω≡ r))
     (≤≡ (nz≤ (alim (pt (βR r) (PB.dF r))) (nz-κ _ _ _ (ρR r) (wκR r) (YκR r) (inv⊕ lω _ (inv-WR r)) (iz⊕ lω _ (iz-WR r))))
         (sym (TR0≡ r)))

S5 : ∀ r → T r 0 0 ≤ Tω
S5 r = ≡≤ (trans (T≡ r 0 0) (PR.ptF≡pt r b₀)) (⊲→≤ (C.lim r C.self))

w³ : D̂ ω
w³ = w₁ ⨾ nw C.self (nl BR)

Y³ : St ω
Y³ = Y₁ ⊕⟨ lω ⟩ R (nl BR) w₁ Y₁

S6 : asuc Tω ≤ T³
S6 = nz≤ Tω (nz-κ _ _ _ ρ3 w³ Y³ (inv⊕ lω _ inv-Y₁) (iz⊕ lω _ iz-Y₁))
```

## §7 高于前一族的上确界

`T r n a ≤ T r (suc n) 0 ≤ TRω r`, 所以第一位相同的一切站都在 `TRω r` 之下; 第一位 $<r+1$ 的一切站都在 `T (suc r) 0 0` 之下, 从而在 `Tω` 之下.

```agda
T≤TRω : ∀ r n a → T r n a ≤ TRω r
T≤TRω r n a = ≤-trans (S2 r n a) (S3 r (suc n))

T≤Tω : ∀ r n a → T r n a ≤ Tω
T≤Tω r n a = ≤-trans (T≤TRω r n a) (≤-trans (⊲→≤ (C.suc C.self)) (≤-trans (S4 r) (S5 (suc r))))

-- Ω·(n+1) 这一级: 高于 Ω²·r+Ω·n+a (一切 a) 的任意可数族的上确界
SupN : ∀ r n (g : ℕ → ℕ) → asuc (alim (λ k → T r n (g k))) ≤ T r (suc n) 0
SupN r n g = ≤-trans (s≤ (l≤ (λ k → T≤TNω r n (g k)))) (TNω<N r n)

-- Ω²·(r+1): 高于 Ω²·r+Ω·n+a (一切 n, a) 的任意可数族的上确界
SupR : ∀ r (g : ℕ → ℕ × ℕ) → asuc (alim (λ k → T r (proj₁ (g k)) (proj₂ (g k)))) ≤ T (suc r) 0 0
SupR r g = ≤-trans (s≤ (l≤ (λ k → T≤TRω r (proj₁ (g k)) (proj₂ (g k))))) (S4 r)

-- Ω³: 高于一切 Ω²·r+Ω·n+a 的任意可数族的上确界
Sup3 : ∀ (g : ℕ → ℕ × (ℕ × ℕ)) → asuc (alim (λ k → T (proj₁ (g k)) (proj₁ (proj₂ (g k))) (proj₂ (proj₂ (g k))))) ≤ T³
Sup3 g = ≤-trans (s≤ (l≤ (λ k → T≤Tω (proj₁ (g k)) (proj₁ (proj₂ (g k))) (proj₂ (proj₂ (g k)))))) S6
```

## §8 要求的各站

```agda
Ω²<Ω²+1 : asuc (T 1 0 0) ≤ TΩ²+1
Ω²<Ω²+1 = S1 1 0 0

Ω²+1<Ω²·2 : asuc TΩ²+1 ≤ TΩ²·2
Ω²+1<Ω²·2 = ≤-trans (s≤ (T≤TRω 1 0 1)) (S4 1)

Ω²·2<Ω²·ω : asuc TΩ²·2 ≤ TΩ²·ω
Ω²·2<Ω²·ω = ≤-trans (S1 2 0 0) (T≤Tω 2 0 1)

Ω²·ω<Ω³ : asuc TΩ²·ω ≤ TΩ³
Ω²·ω<Ω³ = S6

-- 上一轮的 Ω² 站在这里是 T 1 0 0; Ω²·2 严格高于 Ω²+Ω·n+a 一族的上确界
Ω²·2>sup : ∀ (g : ℕ → ℕ × ℕ) → asuc (alim (λ k → T 1 (proj₁ (g k)) (proj₂ (g k)))) ≤ TΩ²·2
Ω²·2>sup = SupR 1
```
