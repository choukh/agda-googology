# 两种种类的折叠 (五): 增长

> 不含记号. 入口 [HtTowerF](HtTowerF.lagda.md). 由 [HtFeedGrow](HtFeedGrow.lagda.md) 改写到新折叠上, 对一切合法最高层 $\Lambda$ (以第 1 层为第一位置) 与一切节点族, 世界 $\omega_2=(\omega,\omega^H)$ ($\omega^H$ 是 `H₀` 里的 ℕ-极限). 站与四条引理同 `HtFeedGrow`:
>
>     Xn n = 1 ⨾ Σ_{z:k_0}1 ⨾ … ⨾ Σ_{z:k_{n-1}}1,  Xs = 1 ⨾ nl (j ↦ Σ_{z:k_j}1),  Xκ = 1 ⨾ (nl … ⨾ 旧种类的闭包)
>
> **`Sup`**: `asuc (sup_k T (Xn (σ k))) ≤ T Xκ`, 对一切 $\Lambda$, 节点族, $\sigma$; 回灌闭包是**旧种类**的 (`nκ`, 经 `KG`).
> **`Supμ`**: 同一句, 站换成 `Xμ = 1 ⨾ (nl … ⨾ nμ …)`: 回灌闭包是**新种类**的. 第一格沿读回路径 $[\omega^H,\mathrm{rd}(\omega^H,z_1))$ 走 (`Walk₁`), 对第 1 层输出 $z_1$ 的形状归纳 (`L4₁`).
>
> 实例: `μSup`, `μSupμ` ($\Lambda=\mathrm{h\Omega}\,\kappa_H\,g$, 最外是新种类, 第 $j$ 段过层 $g(j)$); 代入 $\Lambda=1\boxplus\Omega_2$: `Sup-Ω₂`, **`Supμ-Ω₂`**. `ΩSup` ($\Lambda=\mathrm{h\Omega}\,\kappa_A\,g$); 代入 $g(c)=1\boxplus\Omega_2\boxplus c$: `Sup-Ω₂+Ω`.
>
> 档: 同 `HtFeedGrow.Sup` (一个折叠实例之内, 闭包站高于前缀站的任意可数子族); 不说跨实例, 不说值.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerFGrow where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤) renaming (_≤_ to _≤ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFClosed using (ω⋅; module At; top⁺; Ω₂ᴴ; lΩ₂)
open import OCF.Align.HtTowerFRead using (D₁; rd; rd-fst; Lg-rd; rdp; Lg-rdp)
```

## §1 非零

```agda
data NZ₀ {Kd : Wd₂ → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wd₂ → Set} {Z₀ Z₁ : Set} : ∀ {W} → D₊ Kd V′ Z₀ Z₁ W → Set where
  nz1 : ∀ {W} → NZ₀ (n1 {W = W})
  nzL : ∀ {W} {x y : D₊ Kd V′ Z₀ Z₁ W} → NZ₀ x → NZ₀ (x ⨾ y)
  nzR : ∀ {W} {x y : D₊ Kd V′ Z₀ Z₁ W} → NZ₀ y → NZ₀ (x ⨾ y)
  nzl : ∀ {W} {e : ℕ → D₊ Kd V′ Z₀ Z₁ W} → NZ₀ (e 0) → NZ₀ (nl e)
  nzw : ∀ {W₀ W} {p : W₀ ≤ W} {x : D₊ Kd V′ Z₀ Z₁ W₀} → NZ₀ x → NZ₀ (nw p x)

sum≥ : ∀ {W} b (x : D₀ W) → b ≤ᴬ sum b x
sum≥ b x = ⊲→≤ (sum-fst b x)

nz≤ : ∀ {W} b {x : D₀ W} → NZ₀ x → asuc b ≤ᴬ sum b x
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

nz-Ωd : ∀ t {W} → NZ₀ (Ωd t {W})
nz-Ωd hz = nz1
nz-Ωd (hs b) = nzL nz1
nz-Ωd (hl f) = nzL nz1
nz-Ωd (hΩ (inj₁ tt) g) = nzL nz1
nz-Ωd (hΩ (inj₂ tt) g) = nzL nz1

⊲-idl : ∀ {a b} (q : a ⊲ b) → ⊲-tr C.self q ≡ q
⊲-idl C.self = refl
⊲-idl (C.suc q) = cong C.suc (⊲-idl q)
⊲-idl (C.lim n q) = cong (C.lim n) (⊲-idl q)

⊲-as : ∀ {a b c d} (p : a ⊲ b) (q : b ⊲ c) (r : c ⊲ d) → ⊲-tr p (⊲-tr q r) ≡ ⊲-tr (⊲-tr p q) r
⊲-as p q C.self = refl
⊲-as p q (C.suc r) = cong C.suc (⊲-as p q r)
⊲-as p q (C.lim n r) = cong (C.lim n) (⊲-as p q r)

⊲ᴮ-idl : ∀ {S w a b} (q : _⊲[_]_ {S} a w b) → ⊲ᴮ-tr hself q ≡ q
⊲ᴮ-idl hself = refl
⊲ᴮ-idl (hsuc q) = cong hsuc (⊲ᴮ-idl q)
⊲ᴮ-idl (hlim n q) = cong (hlim n) (⊲ᴮ-idl q)
⊲ᴮ-idl (hLim e q) = cong (hLim e) (⊲ᴮ-idl q)

⊲ᴮ-as : ∀ {S w a b c d} (p : _⊲[_]_ {S} a w b) (q : b ⊲[ w ] c) (r : c ⊲[ w ] d) → ⊲ᴮ-tr p (⊲ᴮ-tr q r) ≡ ⊲ᴮ-tr (⊲ᴮ-tr p q) r
⊲ᴮ-as p q hself = refl
⊲ᴮ-as p q (hsuc r) = cong hsuc (⊲ᴮ-as p q r)
⊲ᴮ-as p q (hlim n r) = cong (hlim n) (⊲ᴮ-as p q r)
⊲ᴮ-as p q (hLim e r) = cong (hLim e) (⊲ᴮ-as p q r)

≡≤ : ∀ {a b c} → a ≡ b → b ≤ᴬ c → a ≤ᴬ c
≡≤ refl q = q

≤≡ : ∀ {a b c} → a ≤ᴬ b → b ≡ c → a ≤ᴬ c
≤≡ q refl = q

natA : ℕ → A
natA zero = azero
natA (suc n) = asuc (natA n)

ω : A
ω = alim natA

lgN : ∀ n → Lg (natA n)
lgN zero = tt
lgN (suc n) = lgN n

lω : Lg ω
lω = (λ n → C.suc C.self) , lgN

nω : ∀ n → natA n ⊲ ω
nω n = C.lim n C.self

natH : ℕ → H₀
natH zero = hz
natH (suc n) = hs (natH n)

ωᴴ : H₀
ωᴴ = hl natH

lωᴴ : LgB ωᴴ
lωᴴ = (λ n → hsuc hself) , lg
  where
  lg : ∀ n → LgB (natH n)
  lg zero = tt
  lg (suc n) = lg n

Wω : Wd₂
Wω = ω , ωᴴ

lWω : LgW₂ Wω
lWω = lω , lωᴴ
```

## §2 对一切 $\Lambda$

```agda
module G (Λ : Ht) (lΛ : LgB Λ) (o : ∀ {w} → hs hz ⊲[ w ] Λ) where
  open At Λ lΛ o hiding (Tψ; Lg-Tψ; ΔΩ; ΨΩ)

  nz-Step : ∀ {W} (Y : St W) {t m} (T : Tg W t m) → NZ₀ (yc (Stp Y) T)
  nz-Step Y {t} T = nzl (nzL (nz-Ωd t))

  record Inv {W : Wd₂} (Y : St W) : Set where
    constructor iv
    field
      nzI : ∀ {t m} (T : Tg W t m) → NZ₀ (yc (d Y) T)
  open Inv public

  inv⊕ : ∀ {W} {Y : St W} (lW : LgW₂ W) (Δ′ : Df W) → Inv Y → Inv (Y ⊕⟨ lW ⟩ Δ′)
  inv⊕ lW Δ′ v = iv (λ T → nzL (nzI v T))

  invcv : ∀ {W W′} (q : W ≤ W′) {Y : St W} → Inv Y → Inv (cv q Y)
  invcv q v = iv (λ T → nzI v (tg↑ q T))

  record NZA {ly : Ht} {W : Wd₂} (A₀ : Ig ly W) (lW : LgW₂ W) {m : Wd₂} (T : Tg W hz m) : Set where
    constructor na
    field
      nzA : ∀ (w : D ly W) (Y : St W) → NZ₀ (yc (A₀ ≤rf lW w Y) T)
  open NZA public

  nz-Act : ∀ {ly W} (lW : LgW₂ W) {m} (T : Tg W hz m) → NZA {ly} Act lW T
  nz-Act lW T = na (λ w Y → nz-Step Y T)

  L3 : ∀ {ly W₀ W} (ac : AccY ly) {x : D ly W₀} (q₀ : W₀ ≤ W) (lW : LgW₂ W) (ll : LW ly W) (A₀ : Ig ly W) {m} (T : Tg W hz m) →
       NZA A₀ lW T → NZ₀ x → ∀ w Y → NZ₀ (yc (Run ac x q₀ lW ll A₀ w Y) T)
  L3 ac q₀ lW ll A₀ T h nz1 w Y = nzA h w Y
  L3 ac q₀ lW ll A₀ T h (nzL nx) w Y = nzL (L3 ac q₀ lW ll A₀ T h nx w Y)
  L3 ac q₀ lW ll A₀ T h (nzR ny) w Y = nzR (L3 ac q₀ lW ll A₀ T h ny _ _)
  L3 ac q₀ lW ll A₀ T h (nzl nd) w Y = nzl (L3 ac q₀ lW ll A₀ T h nd w Y)
  L3 ac q₀ lW ll A₀ T h (nzw {p = p} nx) w Y = L3 ac (≤tr p q₀) lW ll A₀ T h nx w Y

  c1 : ∀ {ly W₀ k} (r : StH W₀ k ly) → ∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′
  c1 r _ _ _ = n1

  L2′ : ∀ {ly W₀ W k m} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (q₀ : W₀ ≤ W) (lW : LgW₂ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
        (T : Tg W hz m) → NZA A₀ lW T → Inv Y → (x : Rk k hz m) → NZ₀ (RKi ac ac′ r (c1 r) q₀ lW ll A₀ w Y T x)
  L2′ ac ac′ r q₀ lW ll A₀ w Y T hA v (keep ())
  L2′ ac ac′ r q₀ lW ll A₀ w Y T hA v rise =
    nzl (L3 ac′ ≤rf lW (kk r q₀ ll) (Ai ac ac′ r (c1 r) q₀ (kk r q₀ ll) ll A₀ w) T (na (λ z Y′ → nzA hA _ Y′))
            (nzI v (tg ≤rf (kk r q₀ ll) lW)) n0 Y)

  L2 : ∀ {ly W₀ W k m} (ac : AccY ly) (r : StH W₀ k ly) (q₀ : W₀ ≤ W) (lW : LgW₂ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
       (T : Tg W hz m) → NZA A₀ lW T → Inv Y → NZ₀ (yc (Run ac (ni r (c1 r)) q₀ lW ll A₀ w Y) T)
  L2 (acc f) r q₀ lW ll A₀ w Y T hA v =
    L2′ (acc f) (f r) r q₀ lW ll A₀ w Y T hA v (rkT (⊲ᴮ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T))

  R : D Λ Wω → D Λ Wω → St Wω → Df Wω
  R x w Y = Run accᴸ x ≤rf lWω hself Act w Y

  τ : Tg Wω hz Wω
  τ = τ₀ lWω

  Pfx : (ℕ → D Λ Wω) → ℕ → ℕ → D Λ Wω → D Λ Wω
  Pfx F k zero tl = tl
  Pfx F k (suc n) tl = F k ⨾ Pfx F (suc k) n tl

  module P (F : ℕ → D Λ Wω) (w : D Λ Wω) (Y : St Wω) where
    Rp : ℕ → D Λ Wω × St Wω
    Rp = Rpt accᴸ F ≤rf lWω hself Act w Y

    dF : ℕ → D₀ Wω
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
    inv-Rp v (suc j) = inv⊕ lWω (R (F j) (proj₁ (Rp j)) (proj₂ (Rp j))) (inv-Rp v j)
```

回灌第一格非零 (L4): 旧种类闭包的第一格走 $[\omega,\omega+z)$. 走法是新折叠的 `KG.Walk`, 分支的折叠是 `Run`.

```agda
  module W (ρ : ∀ {c} → ω ⊲ c → Lg c → Σ Ht (λ k → StH (c , ωᴴ) k Λ)) (V₁ : Wd₂) (lV : LgW₂ V₁) (βV : ωᴴ ⊲[ proj₁ V₁ ] proj₂ V₁)
           (A₀ : Ig Λ V₁) (hA : NZA A₀ lV (τ₀ lV)) where
    u² : ∀ {c} → ω ⊲ c → Lg c → D Λ (c , ωᴴ)
    u² p lc = ni (proj₂ (ρ p lc)) (c1 (proj₂ (ρ p lc)))

    module KW = KG {Λ} {ω} {ωᴴ} u² (λ p lc q lV′ ll′ A′ co′ Y′ → Run accᴸ (u² p lc) q lV′ ll′ A′ co′ Y′)

    NZW : ∀ b {a} → a ⊲ b → ω ⊲ a → Lg b → Set
    NZW b P ap lb = ∀ (bV : b ⊲ proj₁ V₁) co (Y : St V₁) → Inv Y → NZ₀ (yc (KW.Walk b P ap lb bV βV lV hself A₀ co Y) (τ₀ lV))

    W-suc : ∀ c {a} (P : a ⊲ c) ap lb → NZW (asuc c) (C.suc P) ap lb
    W-suc c P ap lb bV co Y v =
      nzR (L2 accᴸ (proj₂ (ρ (⊲-tr ap P) lb)) (⊲-tr (C.suc C.self) bV , βV) lV hself A₀ (co ⨾ Cut₀ u² c P ap lb (⊲-tr (C.suc C.self) bV) βV)
             (Y ⊕⟨ lV ⟩ KW.Walk c P ap lb (⊲-tr (C.suc C.self) bV) βV lV hself A₀ co Y) (τ₀ lV) hA
             (inv⊕ lV (KW.Walk c P ap lb (⊲-tr (C.suc C.self) bV) βV lV hself A₀ co Y) v))

    W-ext : ∀ {W₀′} b″ {a} (P : a ⊲ b″) ap lb″ (y : D₀ W₀′) → NZW b″ P ap lb″ → NZW (sum b″ y) (⊲-tr P (sum-fst b″ y)) ap (Lg-sum b″ y lb″)
    W-ext b″ P ap lb″ n0 h = h
    W-ext b″ P ap lb″ n1 h = W-suc b″ P ap lb″
    W-ext b″ P ap lb″ (y₁ ⨾ y₂) h =
      subst (λ π → NZW (sum (sum b″ y₁) y₂) π ap (Lg-sum (sum b″ y₁) y₂ (Lg-sum b″ y₁ lb″)))
            (sym (⊲-as P (sum-fst b″ y₁) (sum-fst (sum b″ y₁) y₂)))
            (W-ext (sum b″ y₁) (⊲-tr P (sum-fst b″ y₁)) ap (Lg-sum b″ y₁ lb″) y₂ (W-ext b″ P ap lb″ y₁ h))
    W-ext b″ P ap lb″ (nl e) h bV co Y v = nzL (h _ co Y v)
    W-ext b″ P ap lb″ (ni () u) h
    W-ext b″ P ap lb″ (nκ () u) h
    W-ext b″ P ap lb″ (nμ () u) h
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
                      (L4 (e 0) ne b′ C.self (⊲-tr ap Rr) lb′) (⊲-tr (C.lim 1 C.self) bV)
                      (co ⨾ Cut₀ u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) βV)
                      (Y ⊕⟨ lV ⟩ KW.Walk b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) βV lV hself A₀ co Y)
                      (inv⊕ lV (KW.Walk b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) βV lV hself A₀ co Y) v)))
    L4 (nw p x) (nzw nx) b′ Rr ap lb′ = L4 x nx b′ Rr ap lb′
```

新种类的闭包第一格非零 (L4₁): 第一格沿读回的路径 $[\omega^H, \mathrm{rd}(\omega^H, z_1))$ 走 (`Walk₁`). 对 $z_1$ 的形状归纳, 同 `L4`; `ni`, `nκ` 读出的 $\Omega$-极限在坐标 $0$ 处就是底, 所以走进 `hLim` 的第一段就是归纳假设.

```agda
  module W₁ (ρμ : ∀ {W′} → Wω ≤ W′ → LgW₂ W′ → Σ Ht (λ k → StH W′ k Λ)) (zΛ : NZ Λ) (x : H₀) (lx : LgB x)
            (A₀ : Ig Λ (ω , x)) (hA : NZA A₀ (lω , lx) (τ₀ (lω , lx))) where
    uμ : Bu Λ Wω
    uμ q lW′ = ni (proj₂ (ρμ q lW′)) (c1 (proj₂ (ρμ q lW′)))

    lV : LgW₂ (ω , x)
    lV = lω , lx

    NZW₁ : ∀ b {a} → a ⊲[ ω ] b → ωᴴ ⊲[ ω ] a → LgB b → Set
    NZW₁ b P ap lb = ∀ (bV : b ⊲[ ω ] x) co (Y : St (ω , x)) → Inv Y →
                     NZ₀ (yc (Walk₁ accᴸ zΛ uμ b P ap lb bV C.self lV hself A₀ co Y) (τ₀ lV))

    W-suc₁ : ∀ b {a} (P : a ⊲[ ω ] b) ap lb → NZW₁ (hs b) (hsuc P) ap lb
    W-suc₁ b P ap lb bV co Y v =
      nzR (L2 accᴸ (proj₂ (ρμ (C.self , ⊲ᴮ-tr ap P) (lω , lb))) (C.self , ⊲ᴮ-tr (hsuc hself) bV) lV hself A₀
             (co ⨾ Cut₁ zΛ uμ b P ap lb (⊲ᴮ-tr (hsuc hself) bV) C.self lω)
             (Y ⊕⟨ lV ⟩ Walk₁ accᴸ zΛ uμ b P ap lb (⊲ᴮ-tr (hsuc hself) bV) C.self lV hself A₀ co Y) (τ₀ lV) hA
             (inv⊕ lV (Walk₁ accᴸ zΛ uμ b P ap lb (⊲ᴮ-tr (hsuc hself) bV) C.self lV hself A₀ co Y) v))

    W-ext₁ : ∀ {W′} (lW′ : LgW₂ W′) b {a} (P : a ⊲[ ω ] b) ap lb (y : D₁ W′) → NZW₁ b P ap lb →
             NZW₁ (rd lW′ b y) (⊲ᴮ-tr P (rd-fst lW′ b y)) ap (Lg-rd lW′ b y lb)
    W-ext₁ lW′ b P ap lb n0 h = h
    W-ext₁ lW′ b P ap lb n1 h = W-suc₁ b P ap lb
    W-ext₁ lW′ b P ap lb (y₁ ⨾ y₂) h =
      subst (λ π → NZW₁ (rd lW′ (rd lW′ b y₁) y₂) π ap (Lg-rd lW′ (rd lW′ b y₁) y₂ (Lg-rd lW′ b y₁ lb)))
            (sym (⊲ᴮ-as P (rd-fst lW′ b y₁) (rd-fst lW′ (rd lW′ b y₁) y₂)))
            (W-ext₁ lW′ (rd lW′ b y₁) (⊲ᴮ-tr P (rd-fst lW′ b y₁)) ap (Lg-rd lW′ b y₁ lb) y₂ (W-ext₁ lW′ b P ap lb y₁ h))
    W-ext₁ lW′ b P ap lb (nl e) h bV co Y v = nzL (h _ co Y v)
    W-ext₁ lW′ b P ap lb (ni (ss hself) u) h bV co Y v = nzL (h _ co Y v)
    W-ext₁ lW′ b P ap lb (nκ _ u) h bV co Y v = nzL (h _ co Y v)
    W-ext₁ lW′ b P ap lb (nμ () u) h
    W-ext₁ lW′ b P ap lb (nw p y) h = W-ext₁ (lgW≤ p lW′) b P ap lb y h

    L4₁ : ∀ {W′} (lW′ : LgW₂ W′) (z′ : D₁ W′) → NZ₀ z′ → ∀ b′ {a} (Rr : a ⊲[ ω ] b′) ap lb′ →
          NZW₁ (rd lW′ b′ z′) (⊲ᴮ-tr Rr (rd-fst lW′ b′ z′)) ap (Lg-rd lW′ b′ z′ lb′)
    L4₁ lW′ n1 nz1 b′ Rr ap lb′ = W-suc₁ b′ Rr ap lb′
    L4₁ lW′ (x₁ ⨾ y) (nzL nx) b′ Rr ap lb′ =
      subst (λ π → NZW₁ (rd lW′ (rd lW′ b′ x₁) y) π ap (Lg-rd lW′ (rd lW′ b′ x₁) y (Lg-rd lW′ b′ x₁ lb′)))
            (sym (⊲ᴮ-as Rr (rd-fst lW′ b′ x₁) (rd-fst lW′ (rd lW′ b′ x₁) y)))
            (W-ext₁ lW′ (rd lW′ b′ x₁) (⊲ᴮ-tr Rr (rd-fst lW′ b′ x₁)) ap (Lg-rd lW′ b′ x₁ lb′) y (L4₁ lW′ x₁ nx b′ Rr ap lb′))
    L4₁ lW′ (x₁ ⨾ y) (nzR ny) b′ Rr ap lb′ =
      subst (λ π → NZW₁ (rd lW′ (rd lW′ b′ x₁) y) π ap (Lg-rd lW′ (rd lW′ b′ x₁) y (Lg-rd lW′ b′ x₁ lb′)))
            (sym (⊲ᴮ-as Rr (rd-fst lW′ b′ x₁) (rd-fst lW′ (rd lW′ b′ x₁) y)))
            (L4₁ lW′ y ny (rd lW′ b′ x₁) (⊲ᴮ-tr Rr (rd-fst lW′ b′ x₁)) ap (Lg-rd lW′ b′ x₁ lb′))
    L4₁ lW′ (nl e) (nzl ne) b′ Rr ap lb′ bV co Y v =
      nzR (nzl (subst (λ π → NZW₁ (rd lW′ b′ (e 0)) π (⊲ᴮ-tr ap Rr) (Lg-rd lW′ b′ (e 0) lb′)) (⊲ᴮ-idl (rd-fst lW′ b′ (e 0)))
                      (L4₁ lW′ (e 0) ne b′ hself (⊲ᴮ-tr ap Rr) lb′) (⊲ᴮ-tr (hlim 1 hself) bV)
                      (co ⨾ Cut₁ zΛ uμ b′ Rr ap lb′ (⊲ᴮ-tr (hlim 0 hself) bV) C.self lω)
                      (Y ⊕⟨ lV ⟩ Walk₁ accᴸ zΛ uμ b′ Rr ap lb′ (⊲ᴮ-tr (hlim 0 hself) bV) C.self lV hself A₀ co Y)
                      (inv⊕ lV (Walk₁ accᴸ zΛ uμ b′ Rr ap lb′ (⊲ᴮ-tr (hlim 0 hself) bV) C.self lV hself A₀ co Y) v)))
    L4₁ lW′ (nw p x₁) (nzw nx) b′ Rr ap lb′ = L4₁ (lgW≤ p lW′) x₁ nx b′ Rr ap lb′
```

## §3 站与 `Sup`, 对一切 $\Lambda$ 与节点族

```agda
  module Sta (r : ℕ → Σ Ht (λ k → StH Wω k Λ)) (ρ : ∀ {c} → ω ⊲ c → Lg c → Σ Ht (λ k → StH (c , ωᴴ) k Λ)) (zΛ : NZ Λ) where
    nd : ℕ → D Λ Wω
    nd j = ni (proj₂ (r j)) (c1 (proj₂ (r j)))

    κ : D Λ Wω
    κ = nκ zΛ (λ {c} p lc → ni (proj₂ (ρ p lc)) (c1 (proj₂ (ρ p lc))))

    Xn : ℕ → D Λ Wω
    Xn n = n1 ⨾ Pfx nd 0 n n0

    Xs Xκ : D Λ Wω
    Xs = n1 ⨾ nl nd
    Xκ = n1 ⨾ (nl nd ⨾ κ)

    Tψ : D Λ Wω → A
    Tψ x = sum azero (n1 ⨾ yc (R x n0 (Y₀ {Wω})) τ)

    Lg-Tψ : ∀ x → Lg (Tψ x)
    Lg-Tψ x = Lg-sum azero (n1 ⨾ yc (R x n0 (Y₀ {Wω})) τ) tt

    w₁ : D Λ Wω
    w₁ = n0 ⨾ nw ≤rf n1

    Y₁ : St Wω
    Y₁ = Y₀ ⊕⟨ lWω ⟩ Stp (Y₀ {Wω})

    b₀ : A
    b₀ = sum (sum {Wω} azero n1) (yc (Stp (Y₀ {Wω})) τ)

    inv-Y₁ : Inv Y₁
    inv-Y₁ = iv (λ T → nzR (nz-Step (Y₀ {Wω}) T))

    module PB = P nd w₁ Y₁

    β : ℕ → A
    β n = PB.ptF b₀ 0 n

    Xn≡ : ∀ n → Tψ (Xn n) ≡ β n
    Xn≡ n = PB.L1 n 0 n0 b₀

    nz-nd : ∀ j → NZ₀ (PB.dF j)
    nz-nd j = L2 accᴸ (proj₂ (r j)) ≤rf lWω hself Act (proj₁ (PB.Rp j)) (proj₂ (PB.Rp j)) τ (nz-Act lWω τ) (PB.inv-Rp inv-Y₁ j)

    pre< : ∀ n → asuc (Tψ (Xn n)) ≤ᴬ Tψ (Xn (suc n))
    pre< n = ≡≤ (cong asuc (Xn≡ n)) (≤≡ (nz≤ (β n) (nz-nd (0 + n))) (sym (trans (Xn≡ (suc n)) (PB.L1b n 0 b₀))))

    pre≤s : ∀ n → Tψ (Xn n) ≤ᴬ Tψ Xs
    pre≤s n = ≡≤ (trans (Xn≡ n) (PB.ptF≡pt n b₀)) (⊲→≤ (C.lim n C.self))

    w₂ : D Λ Wω
    w₂ = w₁ ⨾ nw ≤rf (nl nd)

    Y₂ : St Wω
    Y₂ = Y₁ ⊕⟨ lWω ⟩ R (nl nd) w₁ Y₁

    inv-Y₂ : Inv Y₂
    inv-Y₂ = inv⊕ lWω (R (nl nd) w₁ Y₁) inv-Y₁

    nz-z₂ : NZ₀ (z Y₂)
    nz-z₂ = nzL (nzR (nz-Step (Y₀ {Wω}) τ))

    module WB = W ρ (sum ω (z Y₂) , ωᴴ) (Lg-sum ω (z Y₂) lω , lωᴴ) hself (Ig↾ (≤A (sum-fst ω (z Y₂))) Act)
                  (nz-Act (Lg-sum ω (z Y₂) lω , lωᴴ) (τ₀ (Lg-sum ω (z Y₂) lω , lωᴴ)))

    nz-κ : NZ₀ (yc (R κ w₂ Y₂) τ)
    nz-κ =
      nzl (nz-drp (WB.L4 (z Y₂) nz-z₂ ω C.self C.self lω C.self (nw (≤A (sum-fst ω (z Y₂))) w₂) (cv (≤A (sum-fst ω (z Y₂))) Y₂)
                    (invcv (≤A (sum-fst ω (z Y₂))) inv-Y₂)))

    s<κ : asuc (Tψ Xs) ≤ᴬ Tψ Xκ
    s<κ = nz≤ (Tψ Xs) nz-κ

    Sup : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ᴬ Tψ Xκ
    Sup σ = ≤-trans (s≤ (l≤ (λ k → pre≤s (σ k)))) s<κ
```

**新种类闭包的站** `Xμ = 1 ⨾ (nl nd ⨾ nμ …)`: 闭包的节点族 $\rho^\mu$ 对一切更大的世界. 回灌的第一格非零 (`nz-μ`, 用 `L4₁`, 起点是 $z_1$: 第 1 层到此为止的输出, 由第一步的 `Stp` 非零). **`Supμ`**: 新种类的闭包站严格高于前缀站的任意可数子族的上确界.

```agda
  module Stμ (r : ℕ → Σ Ht (λ k → StH Wω k Λ)) (ρ : ∀ {c} → ω ⊲ c → Lg c → Σ Ht (λ k → StH (c , ωᴴ) k Λ))
             (ρμ : ∀ {W′} → Wω ≤ W′ → LgW₂ W′ → Σ Ht (λ k → StH W′ k Λ)) (zΛ : NZ Λ) (z1 : NZ₁ Λ) where
    open Sta r ρ zΛ public

    μ : D Λ Wω
    μ = nμ z1 (λ q lW′ → ni (proj₂ (ρμ q lW′)) (c1 (proj₂ (ρμ q lW′))))

    Xμ : D Λ Wω
    Xμ = n1 ⨾ (nl nd ⨾ μ)

    nz-z₁₂ : NZ₀ (z₁ Y₂)
    nz-z₁₂ = nzL (nzR (nz-Step (Y₀ {Wω}) (τ₁ lWω)))

    x₀ : H₀
    x₀ = rd lWω ωᴴ (z₁ Y₂)

    lx₀ : LgB x₀
    lx₀ = Lg-rd lWω ωᴴ (z₁ Y₂) lωᴴ

    module WB₁ = W₁ ρμ (nz₁→nz Λ z1) x₀ lx₀ (Ig↾ (C.self , rd-fst lWω ωᴴ (z₁ Y₂)) Act) (nz-Act (lω , lx₀) (τ₀ (lω , lx₀)))

    nz-μ : NZ₀ (yc (R μ w₂ Y₂) τ)
    nz-μ =
      nzl (nz-drp (WB₁.L4₁ lWω (z₁ Y₂) nz-z₁₂ ωᴴ hself hself lωᴴ hself
                     (nw (C.self , rd-fst lWω ωᴴ (z₁ Y₂)) w₂) (cv (C.self , rd-fst lWω ωᴴ (z₁ Y₂)) Y₂)
                     (invcv (C.self , rd-fst lWω ωᴴ (z₁ Y₂)) inv-Y₂)))

    s<μ : asuc (Tψ Xs) ≤ᴬ Tψ Xμ
    s<μ = nz≤ (Tψ Xs) nz-μ

    Supμ : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ᴬ Tψ Xμ
    Supμ σ = ≤-trans (s≤ (l≤ (λ k → pre≤s (σ k)))) s<μ
```

## §4 最外是新种类 / 旧种类的 $\Omega$-极限

```agda
-- 最外是新种类: 第 j 段过层 g(j) (新种类坐标 j); 闭包的节点族取层 g(0)
module μSt (g : H₀ → Ht) (lg : LgB (hΩ κH g)) (o : ∀ {w} → hs hz ⊲[ w ] hΩ κH g) where
  open G (hΩ κH g) lg o public
  open Stμ (λ j → g (natH j) , sL {κ = κH} {c = natH j} (hlim j hself) hself)
           (λ {c} _ _ → g hz , sL {κ = κH} {c = hz} (z⊲ᴮ ωᴴ) hself)
           (λ {W′} _ _ → g (proj₂ W′) , sL {κ = κH} {c = proj₂ W′} hself hself) tt tt public

  -- 旧种类闭包的站
  μSup : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ᴬ Tψ Xκ
  μSup = Sup

  -- 新种类闭包的站: Xμ 读 ψ₀(Ω_{hΩ κH g}) 的形状 (判断)
  μSupμ : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ᴬ Tψ Xμ
  μSupμ = Supμ

-- 最外是旧种类: 第 j 段过层 g(j), 闭包在世界 c 上过层 g(c)
module ΩSt (g : A → Ht) (lg : LgB (hΩ κA g)) (o : ∀ {w} → hs hz ⊲[ w ] hΩ κA g) where
  open G (hΩ κA g) lg o public
  open Sta (λ j → g (natA j) , sL {κ = κA} (nω j) hself) (λ {c} _ _ → g c , sL {κ = κA} C.self hself) tt public

  ΩSup : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ᴬ Tψ Xκ
  ΩSup = Sup
```

## §5 实例: 层用到新种类

```agda
-- Λ = 1 ⊞ Ω₂ (第 j 段读 ψ₀(Ω_{1+j+1}), Xκ 读 ψ₀(Ω_{Ω₂}); 判断)
gΩ₂ : H₀ → Ht
gΩ₂ c = hs hz ⊞ up c

Sup-Ω₂ : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → μSt.Tψ gΩ₂ _ (⊞-fst (hs hz) Ω₂ᴴ) (μSt.Xn gΩ₂ _ (⊞-fst (hs hz) Ω₂ᴴ) (σ k))))
                         ≤ᴬ μSt.Tψ gΩ₂ (Lg-⊞ (hs hz) Ω₂ᴴ tt lΩ₂) (⊞-fst (hs hz) Ω₂ᴴ) (μSt.Xκ gΩ₂ (Lg-⊞ (hs hz) Ω₂ᴴ tt lΩ₂) (⊞-fst (hs hz) Ω₂ᴴ))
Sup-Ω₂ = μSt.μSup gΩ₂ (Lg-⊞ (hs hz) Ω₂ᴴ tt lΩ₂) (⊞-fst (hs hz) Ω₂ᴴ)

Supμ-Ω₂ : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → μSt.Tψ gΩ₂ _ (⊞-fst (hs hz) Ω₂ᴴ) (μSt.Xn gΩ₂ _ (⊞-fst (hs hz) Ω₂ᴴ) (σ k))))
                          ≤ᴬ μSt.Tψ gΩ₂ (Lg-⊞ (hs hz) Ω₂ᴴ tt lΩ₂) (⊞-fst (hs hz) Ω₂ᴴ) (μSt.Xμ gΩ₂ (Lg-⊞ (hs hz) Ω₂ᴴ tt lΩ₂) (⊞-fst (hs hz) Ω₂ᴴ))
Supμ-Ω₂ = μSt.μSupμ gΩ₂ (Lg-⊞ (hs hz) Ω₂ᴴ tt lΩ₂) (⊞-fst (hs hz) Ω₂ᴴ)

-- Λ = Ω₂ + Ω: 旧种类的 Ω-极限, 第 c 支是 1 ⊞ Ω₂ ⊞ c
embA : A → Ht
embA azero = hz
embA (asuc c) = hs (embA c)
embA (alim f) = hl (λ n → embA (f n))

embA-⊲ : ∀ {c c′} → c ⊲ c′ → ∀ {w} → embA c ⊲[ w ] embA c′
embA-⊲ C.self = hself
embA-⊲ (C.suc p) = hsuc (embA-⊲ p)
embA-⊲ (C.lim n p) = hlim n (embA-⊲ p)

Lg-embA : ∀ c → Lg c → LgB (embA c)
Lg-embA azero _ = tt
Lg-embA (asuc c) l = Lg-embA c l
Lg-embA (alim f) (st , l) = (λ n → embA-⊲ (st n)) , (λ n → Lg-embA (f n) (l n))

b⁺ : Ht
b⁺ = top⁺ Ω₂ᴴ

lb⁺ : LgB b⁺
lb⁺ = Lg-⊞ (hs hz) Ω₂ᴴ tt lΩ₂

gΩΩ : A → Ht
gΩΩ c = b⁺ ⊞ embA c

lgΩΩ : LgB (hΩ κA gΩΩ)
lgΩΩ = (λ lw e e′ p → ⊞-⊲ b⁺ (embA-⊲ p)) , (λ c lc → Lg-⊞ b⁺ (embA c) lb⁺ (Lg-embA c lc))

oΩΩ : ∀ {w} → hs hz ⊲[ w ] hΩ κA gΩΩ
oΩΩ {w} = hLim {κ = κA} {c = azero} (z⊲ (proj₁ w)) (⊞-fst (hs hz) Ω₂ᴴ)

Sup-Ω₂+Ω : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → ΩSt.Tψ gΩΩ lgΩΩ oΩΩ (ΩSt.Xn gΩΩ lgΩΩ oΩΩ (σ k)))) ≤ᴬ ΩSt.Tψ gΩΩ lgΩΩ oΩΩ (ΩSt.Xκ gΩΩ lgΩΩ oΩΩ)
Sup-Ω₂+Ω = ΩSt.ΩSup gΩΩ lgΩΩ oΩΩ
```
