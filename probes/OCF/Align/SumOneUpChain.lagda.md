# `SumOne.T₁` 的上界 (三): 上下文里第 0 层坐标的链

> **验收文件, 定理.** 第一个带上下文的回灌的第 0 格里, 走完第 0 层 (坐标是第 0 层的差, 没有节点) 的位置 `S¹` 的值是 $\psi_0(\Omega_\Omega+\Omega_1)$: `S¹-vlab : VLab (trA S¹) (γ′ᴱ 1)`. 一般引理 `runG`, `chain≈` 对一切状态成立 (只读状态的第 0 层).
> 不覆盖第 $\ge1$ 层的坐标 (它们含 `nκ`). 入口 [SumOneUp](SumOneUp.lagda.md). `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneUpChain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Align.Level hiding (below)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≈ᵛ-trans; ≅→≈ᵛ; +-mono; iter-≼; VLab)
open import OCF.Align.Stage2 using (ℓ₀; σ₁; ch; χ; χ1-label; γ′ᴱ)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleVar using (trA)
open import OCF.Align.CumReadCF using (z⊲)
open import OCF.Align.TLRuleVar using (≤→≼)
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; ≤-refl; ≤-trans)
open import OCF.Align.SumOneTree using (D; cnt; top; n0; n1; _⨾_; nl; nw; ni; nκ; sum; pt; drp)
open import OCF.Align.SumOneClosed using (one; T₁; St; Df; yc; d; _⊕_; zeroD; Step; Ig; Ig↾; AccY; accCn; accTop; Run; Rpt; Chn; Ai; A₁; v; lv; wv; co; Sv)
open import OCF.Align.SumOneAccept using (sum≥; sum-drp)
open import OCF.Align.SumOneUpStation using (M; sum≼+; +≼sum; shift≼; shift≽; Sω; Sω≈)
open import OCF.Align.SumOneUpCell using (Cκ; dκ; fb₁; Fb₁; Fb₁≤T₁)
```

## §1 参照侧的一步

`G Y` 是 $\psi^0(\Omega_{\ell_0}\oplus Y)$, $Y$ 在第 0 层. 它对 $Y$ 的值单调: $Y$ 在第 0 层时 $\psi^0$ 的递归只有零, 后继, $\mathbb N$-极限三行.

```agda
G : Ordᶜ zero → Ordᶜ zero
G Y = ψ⁰ (add (Ω ℓ₀) σ₁ Y)

G-base : ∀ Y → G zero ≼ G Y
G-base zero = ≼-refl _
G-base (suc Y) = ≼l 1 (G-base Y)
G-base (lim f) = ≼l 0 (G-base (f 0))
G-base (limᵢ () f)
G-base (up () x)

G-mono : ∀ {Y Y′ : Ordᶜ zero} → Y ≼ Y′ → G Y ≼ G Y′
G-mono {Y′ = Y′} z≼ = G-base Y′
G-mono (s≼s e) = l≼ (λ n → ≼l n (iter-≼ (G-mono e) n))
G-mono (≼l n e) = ≼l n (G-mono e)
G-mono (l≼ h) = l≼ (λ n → G-mono (h n))
G-mono (≼i {p = ()} x ex e)
G-mono (i≼ {p = ()} h)
G-mono (≼u {r = ()} e)
G-mono (u≼ {r = ()} e)

G-cong : ∀ {Y Y′ : Ordᶜ zero} → Y ≈ᵛ Y′ → G Y ≈ᵛ G Y′
G-cong (p , q) = G-mono p , G-mono q

ch≈ : ∀ n → ch (suc n) ≈ᵛ G (ch n)
ch≈ n = ≅→≈ᵛ (≅-sym (ψ⁰≅ψ {p = lim 0 zero} {σ = λ r → r} (add-≅ {σ = σ₁} {σ′ = σ₁} (Ω-refl ℓ₀) (≅-refl⁰ (ch n)))))
```

## §2 一次 `Step` 乘以 $\omega$

```agda
ωst≼ : ∀ {W} (e : D azero W) (b : A) (B : Ordᶜ zero) → trA b ≼ B → trA (sum azero e) ≼ B → ∀ k → trA (pt b (λ _ → e) k) ≼ M B (suc k)
ωst≼ e b B hb he zero = hb
ωst≼ e b B hb he (suc k) =
  ≼-trans (sum≼+ e {b = pt b (λ _ → e) k} {c = azero} {B = M B (suc k)} (ωst≼ e b B hb he k))
  (≼-trans (+-mono (≼-refl (M B (suc k))) he) (shift≼ B (suc k)))

ωst≽ : ∀ {W} (e : D azero W) (b : A) (B : Ordᶜ zero) → B ≼ trA b → B ≼ trA (sum azero e) → ∀ k → M B (suc k) ≼ trA (pt b (λ _ → e) k)
ωst≽ e b B hb he zero = hb
ωst≽ e b B hb he (suc k) =
  ≼-trans (shift≽ B (suc k))
  (≼-trans (+-mono (≼-refl (M B (suc k))) he)
           (+≼sum e {b = pt b (λ _ → e) k} {c = azero} {B = M B (suc k)} (ωst≽ e b B hb he k)))

ωst : ∀ {W} (e : D azero W) (b : A) (B : Ordᶜ zero) → trA b ≈ᵛ B → trA (sum azero e) ≈ᵛ B → trA (sum b (nl (λ _ → e))) ≈ᵛ lim (M B)
ωst e b B hb he = l≼ (λ k → ≼l (suc k) (ωst≼ e b B (proj₁ hb) (proj₁ he) k)) , l≼ lo
  where
  lo : ∀ n → M B n ≼ trA (sum b (nl (λ _ → e)))
  lo zero = z≼
  lo (suc k) = ≼l k (ωst≽ e b B (proj₂ hb) (proj₂ he) k)
```

## §3 第 0 层的输入, 动作是 `Step`

世界 `W` 固定. `tot Y`: 状态在第 0 层的总和. 不变量: `tot Y` 的值是 `G` 在指数 `a` 处的值; 走过 `x` 之后指数变成 `sum a x`. 指数就用 `A` 里的树记, 所以不需要指数律. 前提 `HA` 只说动作在当前世界就是 `Step`.

```agda
module Run₀ {W : A} (lW : Lg W) (kW : azero ⊲ W) (A² : Ig (cnt azero) W)
            (HA : ∀ (w : D azero W) (Y : St W) → A² C.self lW w Y ≡ Step Y) where

  y₀ : St W → D azero W
  y₀ Y = yc (d Y) (inj₁ kW) tt

  tot : St W → A
  tot Y = sum one (y₀ Y)

  outᴿ : ∀ {W₀} → AccY (cnt azero) → (ℕ → D azero W₀) → W₀ ⊲ W → D azero W → St W → ℕ → D azero W
  outᴿ acz F q₀ w Y n = yc (Run acz (F n) q₀ lW kW A² (proj₁ (Rpt acz F q₀ lW kW A² w Y n)) (proj₂ (Rpt acz F q₀ lW kW A² w Y n))) (inj₁ kW) tt

  tot-rpt : ∀ {W₀} (acz : AccY (cnt azero)) (F : ℕ → D azero W₀) (q₀ : W₀ ⊲ W) (w : D azero W) (Y : St W) n →
            tot (proj₂ (Rpt acz F q₀ lW kW A² w Y n)) ≡ pt (tot Y) (outᴿ acz F q₀ w Y) n
  tot-rpt acz F q₀ w Y zero = refl
  tot-rpt acz F q₀ w Y (suc n) = cong (λ b → sum b (outᴿ acz F q₀ w Y n)) (tot-rpt acz F q₀ w Y n)

  runG : ∀ {W₀} (acz : AccY (cnt azero)) (x : D azero W₀) (q₀ : W₀ ⊲ W) (w : D azero W) (Y : St W) (a : A) →
         trA (tot Y) ≈ᵛ G (trA a) → trA (tot (Y ⊕ Run acz x q₀ lW kW A² w Y)) ≈ᵛ G (trA (sum a x))
  rptG : ∀ {W₀} (acz : AccY (cnt azero)) (F : ℕ → D azero W₀) (q₀ : W₀ ⊲ W) (w : D azero W) (Y : St W) (a : A) →
         trA (tot Y) ≈ᵛ G (trA a) → ∀ n → trA (tot (proj₂ (Rpt acz F q₀ lW kW A² w Y n))) ≈ᵛ G (trA (pt a F n))

  runG acz n0 q₀ w Y a h = h
  runG acz n1 q₀ w Y a h =
    subst (λ Δ → trA (tot (Y ⊕ Δ)) ≈ᵛ G (suc (trA a))) (sym (HA w Y))
          (ωst ((n1 ⨾ n0) ⨾ y₀ Y) (tot Y) (G (trA a)) h h)
  runG acz (x ⨾ y) q₀ w Y a h =
    runG acz y q₀ (w ⨾ nw q₀ x) (Y ⊕ Run acz x q₀ lW kW A² w Y) (sum a x) (runG acz x q₀ w Y a h)
  runG acz (nl F) q₀ w Y a h =
    l≼ (λ n → ≼l n (subst (λ b → trA b ≼ G (trA (pt a F n))) (tot-rpt acz F q₀ w Y n) (proj₁ (rptG acz F q₀ w Y a h n)))) ,
    l≼ (λ n → ≼l n (subst (λ b → G (trA (pt a F n)) ≼ trA b) (tot-rpt acz F q₀ w Y n) (proj₂ (rptG acz F q₀ w Y a h n))))
  runG acz (nw p x) q₀ w Y a h = runG acz x (C.⊲-tr p q₀) w Y a h
  runG acz (ni () u) q₀ w Y a h
  runG acz (nκ () u) q₀ w Y a h

  rptG acz F q₀ w Y a h zero = h
  rptG acz F q₀ w Y a h (suc n) =
    runG acz (F n) q₀ (proj₁ (Rpt acz F q₀ lW kW A² w Y n)) (proj₂ (Rpt acz F q₀ lW kW A² w Y n)) (pt a F n) (rptG acz F q₀ w Y a h n)
```

## §4 链

链点 $\delta_0$ 是状态在第 0 层的差, $\delta_{n+1}$ 是走 $\delta_n$ 的输出. 指数从 $1$ 起, 以后每一步的指数就是上一步的总和: `T (n+1)` 的值是 `G` 在 `T n` 处的值. 所以与参照的链 `ch` 逐项同值, 没有错位.

```agda
  module Chain (acz : AccY (cnt azero)) (Y : St W) (h : trA (tot Y) ≈ᵛ G (suc zero)) where
    C′ : ℕ → D azero W × (D azero W × St W)
    C′ = Chn acz kW lW tt A² Y

    δ : ℕ → D azero W
    δ n = proj₁ (proj₂ (C′ n))

    T : ℕ → A
    T n = tot (proj₂ (proj₂ (C′ n)))

    chnG : ∀ n → trA (T (suc n)) ≈ᵛ G (trA (T n))
    chnG zero = runG acz (δ 0) C.self (proj₁ (C′ 0)) Y one h
    chnG (suc n) = runG acz (δ (suc n)) C.self (proj₁ (C′ (suc n))) (proj₂ (proj₂ (C′ (suc n)))) (T n) (chnG n)

    val : ∀ n → trA (T n) ≈ᵛ G (ch n)
    val zero = h
    val (suc n) = ≈ᵛ-trans (chnG n) (≈ᵛ-trans (G-cong (val n)) (G-cong (proj₂ (ch≈ n) , proj₁ (ch≈ n))))

    pt-T : ∀ n → pt (tot Y) (λ m → δ (suc m)) n ≡ T n
    pt-T zero = refl
    pt-T (suc n) = cong (λ b → sum b (δ (suc n))) (pt-T n)

    chain≈ : trA (sum (tot Y) (nl (λ m → δ (suc m)))) ≈ᵛ χ 1
    chain≈ =
      l≼ (λ n → ≼l n (subst (λ b → trA b ≼ G (ch n)) (sym (pt-T n)) (proj₁ (val n)))) ,
      l≼ (λ n → ≼l n (subst (λ b → G (ch n) ≼ trA b) (sym (pt-T n)) (proj₂ (val n))))
```

## §5 `T₁` 里的实例: 第 0 格的第 0 层

位置用路径 `Pa` 指: `cut x π` 是差 `x` 沿 `π` 取出的前缀 (`pL`: 左边的前缀; `pR`: 左边整个加右边的前缀; `pI`: `nl` 的第 0 项的前缀). 第 0 格先走第 0 层, 所以 `S¹` 的路径是三次 `pL`.

```agda
data Pa {W : A} : D azero W → Set where
  stop : ∀ {x} → Pa x
  pL : ∀ {x y} → Pa x → Pa (x ⨾ y)
  pR : ∀ {x y} → Pa y → Pa (x ⨾ y)
  pI : ∀ {d′} → Pa (d′ 0) → Pa (nl d′)

cut : ∀ {W} (x : D azero W) → Pa x → D azero W
cut x stop = x
cut (x ⨾ y) (pL π) = cut x π
cut (x ⨾ y) (pR π) = x ⨾ cut y π
cut (nl d′) (pI π) = cut (d′ 0) π

cut≤ : ∀ {W} b (x : D azero W) (π : Pa x) → sum b (cut x π) ≤ sum b x
cut≤ b x stop = ≤-refl _
cut≤ b (x ⨾ y) (pL π) = ≤-trans (cut≤ b x π) (sum≥ (sum b x) y)
cut≤ b (x ⨾ y) (pR π) = cut≤ (sum b x) y π
cut≤ b (nl d′) (pI π) = ≤l 1 (cut≤ b (d′ 0) π)

W¹ : A
W¹ = v (Cκ 0)

kW¹ : azero ⊲ W¹
kW¹ = z⊲ W¹

A¹ : Ig (cnt azero) W¹
A¹ = Ai {ly = top} {W₀ = azero} {k = azero} accTop C.self (λ _ _ _ → n1) kW¹ kW¹ tt (Ig↾ (wv (Cκ 0)) A₁) (co (Cκ 0) ⨾ n0)

HA¹ : ∀ (w : D azero W¹) (Y : St W¹) → A¹ C.self (lv (Cκ 0)) w Y ≡ Step Y
HA¹ w Y = refl

Y¹ : St W¹
Y¹ = Sv (Cκ 0) ⊕ zeroD

module R¹ = Run₀ (lv (Cκ 0)) kW¹ A¹ HA¹
module C¹ = R¹.Chain (accCn azero) Y¹ Sω≈

r₀ : D azero W¹
r₀ = nl (λ m → C¹.δ (suc m))

π¹ : Pa fb₁
π¹ = pI (pL (pL (pL stop)))

S¹ : A
S¹ = sum Sω (cut fb₁ π¹)

-- 检查器核对: 路径取出的就是链的输出 (前面一个零差)
S¹-shape : cut fb₁ π¹ ≡ n0 ⨾ drp r₀
S¹-shape = refl

S¹≈ : trA S¹ ≈ᵛ χ 1
S¹≈ = ≈ᵛ-trans (≅→≈ᵛ (sum-drp {W′ = one} r₀ (≅-refl⁰ (trA Sω)))) C¹.chain≈

S¹-vlab : VLab (trA S¹) (γ′ᴱ 1)
S¹-vlab = χ 1 , χ1-label , S¹≈

S¹≤T₁ : S¹ ≤ T₁
S¹≤T₁ = ≤-trans (cut≤ Sω fb₁ π¹) Fb₁≤T₁

low¹-T₁ : χ 1 ≼ trA T₁
low¹-T₁ = ≼-trans (proj₂ S¹≈) (≤→≼ S¹≤T₁)
```
