# 高度是树 (五): 一条增长定理对一切高度

> 不含记号. 入口 [HtFeed](HtFeed.lagda.md). 序是布劳威尔树上的 `_≤_` ([TLRuleSpec](TLRuleSpec.lagda.md)). 由 [SumHtGrow](SumHtGrow.lagda.md) 改写, 但**不按站写**: 一切引理与定理都对任意合法的最高层 $\Lambda$ (折叠的模块参数) 与任意节点族成立.
>
> 站 (都是层 $\Lambda$ 在世界 $\omega$ 上的输入): 给一列节点种类 $r_j$ (层 $k_j$) 与世界上的节点种类 $\rho$ (层 $\rho_c$, $c\ge\omega$),
>
>     Xn n = 1 ⨾ Σ_{z:k_0}1 ⨾ … ⨾ Σ_{z:k_{n-1}}1        前 n 段
>     Xs   = 1 ⨾ nl (j ↦ Σ_{z:k_j}1)                       ℕ-部分和的极限
>     Xκ   = 1 ⨾ (nl (j ↦ Σ_{z:k_j}1) ⨾ Σ_{c≥ω} Σ_{z:ρ_c}1)  再接回灌闭包
>
> - `pre<`: `asuc (T (Xn n)) ≤ T (Xn (suc n))`.
> - `pre≤s`: `T (Xn n) ≤ T Xs`.
> - `s<κ`: `asuc (T Xs) ≤ T Xκ`: 回灌闭包在第 0 层的第一格非零.
> - **`Sup`**: 对任意 $\sigma:\mathbb N\to\mathbb N$, `asuc (sup_k T (Xn (σ k))) ≤ T Xκ`.
>
> 对 $\Omega$-极限的高度 $\Lambda=\mathrm{h\Omega}\,g$ 取 $k_j=g(j)$, $\rho_c=g(c)$ (`ΩSt`): 前 $n$ 段读 $\psi_0(\Omega_{g(n-1)+1})$, `Xκ` 读 $\psi_0(\Omega_\Lambda)$ (判断). **这一条对一切 $\Omega$-极限的高度成立, 不按高度或阶段写**; `SumHt` 的 `S4`, `SumClimb` 的 `SupN`, `SupR`, `Sup3` 是它在各自坐标里的同形物.
>
> **分辨力到此为止** (同 `SumClimbGrow`): 多出的是 "ℕ-部分和的极限之上一段非零", 不说 `Xκ` 高于前一族的闭包点. 那要折叠对世界单调.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtFeedGrow where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedClosed using (ω⋅; module At)
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ; emb; it; Hier; T; Tk; h-Ω·2; l-Ω·2; h-ΩΩk; l-ΩΩk)
```

## §1 非零

```agda
data NZ₀ {Kd : A → H → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} : ∀ {W} → D₊ Kd V′ Z W → Set where
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

nz-Ωd : ∀ t {W} → NZ₀ (Ωd t {W})
nz-Ωd hz = nz1
nz-Ωd (hs b) = nzL nz1
nz-Ωd (hl f) = nzL nz1
nz-Ωd (hΩ g) = nzL nz1

⊲-idl : ∀ {a b} (q : a ⊲ b) → ⊲-tr C.self q ≡ q
⊲-idl C.self = refl
⊲-idl (C.suc q) = cong C.suc (⊲-idl q)
⊲-idl (C.lim n q) = cong (C.lim n) (⊲-idl q)

⊲-as : ∀ {a b c d} (p : a ⊲ b) (q : b ⊲ c) (r : c ⊲ d) → ⊲-tr p (⊲-tr q r) ≡ ⊲-tr (⊲-tr p q) r
⊲-as p q C.self = refl
⊲-as p q (C.suc r) = cong C.suc (⊲-as p q r)
⊲-as p q (C.lim n r) = cong (C.lim n) (⊲-as p q r)

≡≤ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
≡≤ refl q = q

≤≡ : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
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
```

## §2 对一切 $\Lambda$: 不经过节点的路 (L3), 一个节点 (L2), 前缀 (L1), 回灌第一格 (L4)

```agda
module G (Λ : H) (lΛ : LgH Λ) where
  open At Λ lΛ hiding (Tψ; Lg-Tψ; ΔΩ; ΨΩ)

  nz-Step : ∀ {W} (Y : St W) {t m} (T : Tg W t m) → NZ₀ (yc (Step Y) T)
  nz-Step Y {t} T = nzl (nzL (nz-Ωd t))

  record Inv {W : A} (Y : St W) : Set where
    constructor iv
    field
      nzI : ∀ {t m} (T : Tg W t m) → NZ₀ (yc (d Y) T)
  open Inv public

  inv⊕ : ∀ {W} {Y : St W} (lW : Lg W) (Δ′ : Df W) → Inv Y → Inv (Y ⊕⟨ lW ⟩ Δ′)
  inv⊕ lW Δ′ v = iv (λ T → nzL (nzI v T))

  invcv : ∀ {W W′} (q : W ⊲ W′) {Y : St W} → Inv Y → Inv (cv q Y)
  invcv q v = iv (λ T → nzI v (tg↑ q T))

  record NZA {ly : H} {W : A} (A₀ : Ig ly W) (lW : Lg W) {m : A} (T : Tg W hz m) : Set where
    constructor na
    field
      nzA : ∀ (w : D ly W) (Y : St W) → NZ₀ (yc (A₀ C.self lW w Y) T)
  open NZA public

  nz-Act : ∀ {ly W} (lW : Lg W) {m} (T : Tg W hz m) → NZA {ly} Act lW T
  nz-Act lW T = na (λ w Y → nz-Step Y T)

  L3 : ∀ {ly W₀ W} (ac : AccY ly) {x : D ly W₀} (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) {m} (T : Tg W hz m) →
       NZA A₀ lW T → NZ₀ x → ∀ w Y → NZ₀ (yc (Run ac x q₀ lW ll A₀ w Y) T)
  L3 ac q₀ lW ll A₀ T h nz1 w Y = nzA h w Y
  L3 ac q₀ lW ll A₀ T h (nzL nx) w Y = nzL (L3 ac q₀ lW ll A₀ T h nx w Y)
  L3 ac q₀ lW ll A₀ T h (nzR ny) w Y = nzR (L3 ac q₀ lW ll A₀ T h ny _ _)
  L3 ac q₀ lW ll A₀ T h (nzl nd) w Y = nzl (L3 ac q₀ lW ll A₀ T h nd w Y)
  L3 ac q₀ lW ll A₀ T h (nzw {p = p} nx) w Y = L3 ac (⊲-tr p q₀) lW ll A₀ T h nx w Y

  -- 分支为 1 的节点
  c1 : ∀ {ly W₀ k} (r : StH W₀ k ly) → ∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′
  c1 r _ _ _ = n1

  L2′ : ∀ {ly W₀ W k m} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
        (T : Tg W hz m) → NZA A₀ lW T → Inv Y → (x : Rk k hz m) → NZ₀ (RKi ac ac′ r (c1 r) q₀ lW ll A₀ w Y T x)
  L2′ ac ac′ r q₀ lW ll A₀ w Y T hA v (keep ())
  L2′ ac ac′ r q₀ lW ll A₀ w Y T hA v rise =
    nzl (L3 ac′ C.self lW (kk r q₀ ll) (Ai ac ac′ r (c1 r) q₀ (kk r q₀ ll) ll A₀ w) T (na (λ z Y′ → nzA hA _ Y′))
            (nzI v (tg C.self (kk r q₀ ll) lW)) n0 Y)

  L2 : ∀ {ly W₀ W k m} (ac : AccY ly) (r : StH W₀ k ly) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W)
       (T : Tg W hz m) → NZA A₀ lW T → Inv Y → NZ₀ (yc (Run ac (ni r (c1 r)) q₀ lW ll A₀ w Y) T)
  L2 (acc f) r q₀ lW ll A₀ w Y T hA v =
    L2′ (acc f) (f r) r q₀ lW ll A₀ w Y T hA v (rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T))
```

**回灌给出层的坐标** (定义层的事实, 写成定理): `nκ` 在第 0 层的第 $n$ 格的世界 $v_n$ 是第一个世界接上到此为止的输出, $v_{n+1}=v_n+\Delta_n$, $\Delta_n$ 是第 $n$ 格的折叠输出; 第 $n$ 格走过 $[v_{n-1},v_n)$ 里每个 $c$ 上的分支 $u(c)$. 对 $\Omega$-极限的层, $u(c)$ 的节点在层 $g(c)$ 上 (`Ωd`, `ΩSt`): **用到的高度 $g(c)$ 由折叠的输出选出.**

```agda
  feed₀ : ∀ {ly W₀ W} (ac : AccY ly) (u : ∀ {c} → W₀ ⊲ c → Lg c → D ly c) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
          v (κc ac u q₀ lW ll A₀ w Y zero) ≡ sum W (z Y)
  feed₀ ac u q₀ lW ll A₀ w Y = refl

  feed : ∀ {ly W₀ W} (ac : AccY ly) (u : ∀ {c} → W₀ ⊲ c → Lg c → D ly c) (q₀ : W₀ ⊲ W) (lW : Lg W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) n →
         v (κc ac u q₀ lW ll A₀ w Y (suc n)) ≡
         sum (v (κc ac u q₀ lW ll A₀ w Y n)) (yc (κΔ ac u ll A₀ (κc ac u q₀ lW ll A₀ w Y n)) (τ₀ (lv (κc ac u q₀ lW ll A₀ w Y n))))
  feed ac u q₀ lW ll A₀ w Y n = refl
```

前缀与部分和. 输入都在层 $\Lambda$, 世界 $\omega$.

```agda
  R : D Λ ω → D Λ ω → St ω → Df ω
  R x w Y = Run accᴸ x C.self lω hself Act w Y

  τ : Tg ω hz ω
  τ = τ₀ lω

  Pfx : (ℕ → D Λ ω) → ℕ → ℕ → D Λ ω → D Λ ω
  Pfx F k zero tl = tl
  Pfx F k (suc n) tl = F k ⨾ Pfx F (suc k) n tl

  module P (F : ℕ → D Λ ω) (w : D Λ ω) (Y : St ω) where
    Rp : ℕ → D Λ ω × St ω
    Rp = Rpt accᴸ F C.self lω hself Act w Y

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
```

回灌第一格非零 (L4): 第一格走 $[\omega,\omega+z)$, $z$ 是到此为止的输出; 按 `sum-fst` 的形状归纳. 对世界上的任意节点族 $\rho$.

```agda
  module W (ρ : ∀ {c} → ω ⊲ c → Lg c → Σ H (λ k → StH c k Λ)) (V₁ : A) (lV : Lg V₁) (A₀ : Ig Λ V₁) (hA : NZA A₀ lV (τ₀ lV)) where
    u² : ∀ {c} → ω ⊲ c → Lg c → D Λ c
    u² p lc = ni (proj₂ (ρ p lc)) (c1 (proj₂ (ρ p lc)))

    NZW : ∀ b {a} → a ⊲ b → ω ⊲ a → Lg b → Set
    NZW b P ap lb = ∀ (bV : b ⊲ V₁) co (Y : St V₁) → Inv Y → NZ₀ (yc (Walk accᴸ u² b P ap lb bV lV hself A₀ co Y) (τ₀ lV))

    W-suc : ∀ c {a} (P : a ⊲ c) ap lb → NZW (asuc c) (C.suc P) ap lb
    W-suc c P ap lb bV co Y v =
      nzR (L2 accᴸ (proj₂ (ρ (⊲-tr ap P) lb)) (⊲-tr (C.suc C.self) bV) lV hself A₀ (co ⨾ Cut u² c P ap lb (⊲-tr (C.suc C.self) bV))
             (Y ⊕⟨ lV ⟩ Walk accᴸ u² c P ap lb (⊲-tr (C.suc C.self) bV) lV hself A₀ co Y) (τ₀ lV) hA
             (inv⊕ lV (Walk accᴸ u² c P ap lb (⊲-tr (C.suc C.self) bV) lV hself A₀ co Y) v))

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
                      (Y ⊕⟨ lV ⟩ Walk accᴸ u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV hself A₀ co Y)
                      (inv⊕ lV (Walk accᴸ u² b′ Rr ap lb′ (⊲-tr (C.lim 0 C.self) bV) lV hself A₀ co Y) v)))
    L4 (nw p x) (nzw nx) b′ Rr ap lb′ = L4 x nx b′ Rr ap lb′
```

## §3 站与四条定理, 对一切 $\Lambda$ 与一切节点族

```agda
  module Sta (r : ℕ → Σ H (λ k → StH ω k Λ)) (ρ : ∀ {c} → ω ⊲ c → Lg c → Σ H (λ k → StH c k Λ)) (zΛ : NZ Λ) where
    nd : ℕ → D Λ ω
    nd j = ni (proj₂ (r j)) (c1 (proj₂ (r j)))

    κ : D Λ ω
    κ = nκ zΛ (λ {c} p lc → ni (proj₂ (ρ p lc)) (c1 (proj₂ (ρ p lc))))

    Xn : ℕ → D Λ ω
    Xn n = n1 ⨾ Pfx nd 0 n n0

    Xs Xκ : D Λ ω
    Xs = n1 ⨾ nl nd
    Xκ = n1 ⨾ (nl nd ⨾ κ)

    Tψ : D Λ ω → A
    Tψ x = sum azero (n1 ⨾ yc (R x n0 (Y₀ {ω})) τ)

    Lg-Tψ : ∀ x → Lg (Tψ x)
    Lg-Tψ x = Lg-sum azero (n1 ⨾ yc (R x n0 (Y₀ {ω})) τ) tt

    w₁ : D Λ ω
    w₁ = n0 ⨾ nw C.self n1

    Y₁ : St ω
    Y₁ = Y₀ ⊕⟨ lω ⟩ Step (Y₀ {ω})

    b₀ : A
    b₀ = sum (sum {ω} azero n1) (yc (Step (Y₀ {ω})) τ)

    inv-Y₁ : Inv Y₁
    inv-Y₁ = iv (λ T → nzR (nz-Step (Y₀ {ω}) T))

    module PB = P nd w₁ Y₁

    β : ℕ → A
    β n = PB.ptF b₀ 0 n

    Xn≡ : ∀ n → Tψ (Xn n) ≡ β n
    Xn≡ n = PB.L1 n 0 n0 b₀

    Xs≡ : Tψ Xs ≡ alim (pt b₀ PB.dF)
    Xs≡ = refl

    nz-nd : ∀ j → NZ₀ (PB.dF j)
    nz-nd j = L2 accᴸ (proj₂ (r j)) C.self lω hself Act (proj₁ (PB.Rp j)) (proj₂ (PB.Rp j)) τ (nz-Act lω τ) (PB.inv-Rp inv-Y₁ j)

    pre< : ∀ n → asuc (Tψ (Xn n)) ≤ Tψ (Xn (suc n))
    pre< n = ≡≤ (cong asuc (Xn≡ n)) (≤≡ (nz≤ (β n) (nz-nd (0 + n))) (sym (trans (Xn≡ (suc n)) (PB.L1b n 0 b₀))))

    pre≤s : ∀ n → Tψ (Xn n) ≤ Tψ Xs
    pre≤s n = ≡≤ (trans (Xn≡ n) (PB.ptF≡pt n b₀)) (⊲→≤ (C.lim n C.self))

    w₂ : D Λ ω
    w₂ = w₁ ⨾ nw C.self (nl nd)

    Y₂ : St ω
    Y₂ = Y₁ ⊕⟨ lω ⟩ R (nl nd) w₁ Y₁

    inv-Y₂ : Inv Y₂
    inv-Y₂ = inv⊕ lω (R (nl nd) w₁ Y₁) inv-Y₁

    nz-z₂ : NZ₀ (z Y₂)
    nz-z₂ = nzL (nzR (nz-Step (Y₀ {ω}) τ))

    module WB = W ρ (sum ω (z Y₂)) (Lg-sum ω (z Y₂) lω) (Ig↾ (sum-fst ω (z Y₂)) Act) (nz-Act (Lg-sum ω (z Y₂) lω) (τ₀ (Lg-sum ω (z Y₂) lω)))

    nz-κ : NZ₀ (yc (R κ w₂ Y₂) τ)
    nz-κ =
      nzl (nz-drp (WB.L4 (z Y₂) nz-z₂ ω C.self C.self lω C.self (nw (sum-fst ω (z Y₂)) w₂) (cv (sum-fst ω (z Y₂)) Y₂) (invcv (sum-fst ω (z Y₂)) inv-Y₂)))

    s<κ : asuc (Tψ Xs) ≤ Tψ Xκ
    s<κ = nz≤ (Tψ Xs) nz-κ

    Sup : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ Tψ Xκ
    Sup σ = ≤-trans (s≤ (l≤ (λ k → pre≤s (σ k)))) s<κ
```

## §4 $\Omega$-极限的高度

$\Lambda=\mathrm{h\Omega}\,g$: 第 $j$ 段过层 $g(j)$, 回灌闭包在世界 $c$ 上过层 $g(c)$. **一条定义, 一条定理, 对一切 $g$.**

```agda
module ΩSt (g : A → H) (lg : LgH (hΩ g)) where
  open G (hΩ g) lg public
  open Sta (λ j → g (natA j) , sL (nω j) hself) (λ {c} _ _ → g c , sL C.self hself) tt public

  -- 前 n+1 段读 ψ₀(Ω_{g(n)+1}), Xκ 读 ψ₀(Ω_{hΩ g}) (判断)
  ΩSup : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ Tψ Xκ
  ΩSup = Sup

  Ω-pre< : ∀ n → asuc (Tψ (Xn n)) ≤ Tψ (Xn (suc n))
  Ω-pre< = pre<
```

## §5 实例: 同一条定理用在生成的高度上

不另证, 都是 `ΩSup` 代入. 读法是判断.

```agda
SupStmt : (g : A → H) → LgH (hΩ g) → Set
SupStmt g lg = ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → ΩSt.Tψ g lg (ΩSt.Xn g lg (σ k)))) ≤ ΩSt.Tψ g lg (ΩSt.Xκ g lg)

-- Ω: 前 n+1 段读 ψ₀(Ω_{n+1})
Sup-Ω : SupStmt emb Lg-Ωᴴ
Sup-Ω = ΩSt.ΩSup emb Lg-Ωᴴ

-- Ω·2: 前 n+1 段读 ψ₀(Ω_{Ω+n+2})
Sup-Ω·2 : SupStmt (it hs (hs Ωᴴ)) l-Ω·2
Sup-Ω·2 = ΩSt.ΩSup (it hs (hs Ωᴴ)) l-Ω·2

-- Ω^{Ω^{k+1}}: 第 j 支是变换 T_k 迭代 1+j 次作用于后继, 再作用于 0
Sup-ΩΩk : ∀ k → SupStmt (λ c → Hier (T (Tk k)) (T (Tk k) hs) c hz) (l-ΩΩk (suc k))
Sup-ΩΩk k = ΩSt.ΩSup (λ c → Hier (T (Tk k)) (T (Tk k) hs) c hz) (l-ΩΩk (suc k))
```
