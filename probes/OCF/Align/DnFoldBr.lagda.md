# 有内容的下降 (五): 第 1 站的桥 (无世界的层 ⇄ 带有限外层世界的层)

> 不含记号. 入口 [DnFold](DnFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **部分的种类映射 `PE S T`**: 每个种类要么映到一个种类并带坐标的**反方向**映射, 要么丢掉. 由它得高度的映射 `mapP` (丢掉的结点只走底支). 不要求保合法: 桥的输出只喂给数据树的翻译, 数据树没有合法性, 下降的合法由读回的形状给出 (`DnFoldEv`).
>
> **第 1 站的桥** (外层世界 $a_N=(N,N)$, 有限): `F N b : PE (Lev b) (LvH a_N (μ′ b))`, `G N b` 反方向, 对层号 $b$ 结构递归, 与 `μ′` 同形. 保留的种类 (`Kd1` 的前四类) 的下标 $x$ 在 $a_N$ 里可入才留下: **判定是对 $x$ 的构造子递归** (`decA`, `decH`: $x$ 字面地是有限的 $k\le N$), 外层世界有限所以可判; 这是裸判定, 只因外层世界有限才不撞分离子 (`NegDnFoldAdm.keepS₁-sep` 要外层世界的 `A`-分量是 $\omega$). 带世界的层多出来的那一层后继 (每支的新种类) 在 `G` 里丢掉.
>
> **丢了什么.** (i) 种类下标不是有限 $\le N$ 的结点 (无穷的下标, 含 $\omega$ 与 $\Omega$-结构的下标); (ii) `Oth` 类的种类 (第 2 级以上的级); (iii) 带世界的层在每支多出的新种类. 第 1 站读回 `hs (Ωtop (Lev X₁))` 的**头** (新种类结点) 原样留下, 分支是 `F ∘ up ∘ G` (`DnFoldK.rd-kept`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldBr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; LgW₂; κA; κH)
open import OCF.Align.DnFoldIf using (LvH)
open import OCF.Align.DnFoldDc using (finA; finH₀; lg-finA; lg-finH₀)
open import OCF.Align.DnFoldMu
```

## §1 部分的种类映射

```agda
PE : KS → KS → Set
PE S T = (κ : K S) → (Σ (K T) (λ κ′ → E T κ′ → E S κ)) ⊎ ⊤

selP : ∀ {T : KS} {X : Set} → (Σ (K T) (λ κ′ → E T κ′ → X)) ⊎ ⊤ → (X → HB T) → HB T → HB T
selP (inj₁ (κ′ , cv)) r d = hΩ κ′ (λ z → r (cv z))
selP (inj₂ _) r d = d

mapP : ∀ {S T : KS} → PE S T → HB S → HB T
mapP P hz = hz
mapP P (hs x) = hs (mapP P x)
mapP P (hl f) = hl (λ n → mapP P (f n))
mapP {S} P (hΩ κ g) = selP (P κ) (λ x → mapP P (g x)) (mapP P (g (bot S κ)))

liftO : ∀ {T : KS} {X : Set} → (Σ (K T) (λ κ′ → E T κ′ → X)) ⊎ ⊤ → (Σ (K (step T)) (λ κ′ → E (step T) κ′ → X)) ⊎ ⊤
liftO (inj₁ (κ′ , cv)) = inj₁ (inj₁ κ′ , cv)
liftO (inj₂ t) = inj₂ t

stepPE : ∀ {S T : KS} → PE S T → (HB T → HB S) → PE (step S) (step T)
stepPE P back (inj₂ tt) = inj₁ (inj₂ tt , back)
stepPE P back (inj₁ κ) = liftO (P κ)
```

## §2 有限外层世界里的可入: 对下标的构造子递归

```agda
eqA : (x : A) (n : ℕ) → (x ≡ finA n) ⊎ ⊤
eqA azero zero = inj₁ refl
eqA (asuc x) (suc n) = sucA (eqA x n)
  where
  sucA : (x ≡ finA n) ⊎ ⊤ → (asuc x ≡ finA (suc n)) ⊎ ⊤
  sucA (inj₁ e) = inj₁ (cong asuc e)
  sucA (inj₂ t) = inj₂ t
eqA azero (suc n) = inj₂ tt
eqA (asuc x) zero = inj₂ tt
eqA (alim f) n = inj₂ tt

decA : (n : ℕ) (x : A) → (x ⊲ finA n) ⊎ ⊤
decA n x = pick n x (eqA x n)
  where
  pick : (n : ℕ) (x : A) → (x ≡ finA n) ⊎ ⊤ → (x ⊲ finA n) ⊎ ⊤
  pick n x (inj₁ e) = inj₁ (subst (λ z → z ⊲ finA n) (sym e) C.self)
  pick zero x (inj₂ _) = inj₂ tt
  pick (suc n) x (inj₂ _) = down (decA n x)
    where
    down : (x ⊲ finA n) ⊎ ⊤ → (x ⊲ finA (suc n)) ⊎ ⊤
    down (inj₁ p) = inj₁ (C.suc p)
    down (inj₂ t) = inj₂ t

eqH : (y : H₀) (n : ℕ) → (y ≡ finH₀ n) ⊎ ⊤
eqH hz zero = inj₁ refl
eqH (hs y) (suc n) = sucH (eqH y n)
  where
  sucH : (y ≡ finH₀ n) ⊎ ⊤ → (hs y ≡ finH₀ (suc n)) ⊎ ⊤
  sucH (inj₁ e) = inj₁ (cong hs e)
  sucH (inj₂ t) = inj₂ t
eqH hz (suc n) = inj₂ tt
eqH (hs y) zero = inj₂ tt
eqH (hl f) n = inj₂ tt
eqH (hΩ κ g) n = inj₂ tt

decH : (n : ℕ) (y : H₀) {w : A} → (y ⊲[ w ] finH₀ n) ⊎ ⊤
decH n y {w} = pick n y (eqH y n)
  where
  pick : (n : ℕ) (y : H₀) → (y ≡ finH₀ n) ⊎ ⊤ → (y ⊲[ w ] finH₀ n) ⊎ ⊤
  pick n y (inj₁ e) = inj₁ (subst (λ z → z ⊲[ w ] finH₀ n) (sym e) hself)
  pick zero y (inj₂ _) = inj₂ tt
  pick (suc n) y (inj₂ _) = down (decH n y {w})
    where
    down : (y ⊲[ w ] finH₀ n) ⊎ ⊤ → (y ⊲[ w ] finH₀ (suc n)) ⊎ ⊤
    down (inj₁ p) = inj₁ (hsuc p)
    down (inj₂ t) = inj₂ t
```

## §3 第 1 站的桥

```agda
module Br (N : ℕ) where
  aN : Wd₂
  aN = finA N , finH₀ N

  laN : LgW₂ aN
  laN = lg-finA N , lg-finH₀ N

  Lv : Ht → KS
  Lv = LvH aN

  -- 进 / 出 带世界的 Ω-层的第 x 支 (旧种类)
  inΩ : ∀ {κ′ : K S₁} {h : E S₁ κ′ → Ht} {X : Set} {x : E S₁ κ′} → (Bd S₁ κ′ x aN) ⊎ ⊤ →
        (Σ (K (Lv (h x))) (λ κ‴ → E (Lv (h x)) κ‴ → X)) ⊎ ⊤ →
        (Σ (K (Lv (hΩ κ′ h))) (λ κ⁗ → E (Lv (hΩ κ′ h)) κ⁗ → X)) ⊎ ⊤
  inΩ {x = x} (inj₁ e) (inj₁ (κ‴ , cv)) = inj₁ (((x , e) , inj₁ κ‴) , cv)
  inΩ (inj₁ e) (inj₂ t) = inj₂ t
  inΩ (inj₂ t) _ = inj₂ t

  outΩ : ∀ {I : Set} {F′ : I → KS} {X : Set} (x : I) → (Σ (K (F′ x)) (λ κ″ → E (F′ x) κ″ → X)) ⊎ ⊤ →
         (Σ (K (sup I F′)) (λ κ → E (sup I F′) κ → X)) ⊎ ⊤
  outΩ x (inj₁ (κ″ , cv)) = inj₁ ((x , κ″) , cv)
  outΩ x (inj₂ t) = inj₂ t

  FΩ : ∀ κ (k : Kd1 κ) (g : E K1 κ → HB K1) → ((x : E K1 κ) → PE (Lev (g x)) (Lv (μ′ (g x)))) →
       PE (Lev (hΩ κ g)) (Lv (μΩ κ k (λ x → μ′ (g x))))
  FΩ _ kA₁ g Fg (x , κ″) = inΩ {κA} {λ x → μ′ (g x)} (decA N x) (Fg x κ″)
  FΩ _ kA₂ g Fg (x , κ″) = inΩ {κA} {λ x → μ′ (g x)} (decA N x) (Fg x κ″)
  FΩ _ kA₃ g Fg (x , κ″) = inΩ {κA} {λ x → μ′ (g x)} (decA N x) (Fg x κ″)
  FΩ _ kH g Fg (y , κ″) = inΩ {κH} {λ y → μ′ (g y)} (decH N y) (Fg y κ″)
  FΩ _ (kO κ o) g Fg _ = inj₂ tt

  GΩ : ∀ κ (k : Kd1 κ) (g : E K1 κ → HB K1) → ((x : E K1 κ) → PE (Lv (μ′ (g x))) (Lev (g x))) →
       PE (Lv (μΩ κ k (λ x → μ′ (g x)))) (Lev (hΩ κ g))
  GΩ _ kA₁ g Gg ((x , e) , inj₁ κ‴) = outΩ {F′ = λ x → Lev (g x)} x (Gg x κ‴)
  GΩ _ kA₁ g Gg ((x , e) , inj₂ tt) = inj₂ tt
  GΩ _ kA₂ g Gg ((x , e) , inj₁ κ‴) = outΩ {F′ = λ x → Lev (g x)} x (Gg x κ‴)
  GΩ _ kA₂ g Gg ((x , e) , inj₂ tt) = inj₂ tt
  GΩ _ kA₃ g Gg ((x , e) , inj₁ κ‴) = outΩ {F′ = λ x → Lev (g x)} x (Gg x κ‴)
  GΩ _ kA₃ g Gg ((x , e) , inj₂ tt) = inj₂ tt
  GΩ _ kH g Gg ((y , e) , inj₁ κ‴) = outΩ {F′ = λ y → Lev (g y)} y (Gg y κ‴)
  GΩ _ kH g Gg ((y , e) , inj₂ tt) = inj₂ tt
  GΩ _ (kO {c} κ o) g Gg κ′ = outΩ {F′ = λ x → Lev (g x)} (bot K1 (inj₂ c , κ)) (Gg (bot K1 (inj₂ c , κ)) κ′)

  F : (b : HB K1) → PE (Lev b) (Lv (μ′ b))
  G : (b : HB K1) → PE (Lv (μ′ b)) (Lev b)
  F hz κ = inj₁ (inj₁ κ , λ x → x)
  F (hs b) = stepPE (F b) (mapP (G b))
  F (hl f) (n , κ) = outΩ′ (F (f n) κ)
    where
    outΩ′ : (Σ (K (Lv (μ′ (f n)))) (λ κ′ → E (Lv (μ′ (f n))) κ′ → E (Lev (f n)) κ)) ⊎ ⊤ →
            (Σ (K (Lv (μ′ (hl f)))) (λ κ′ → E (Lv (μ′ (hl f))) κ′ → E (Lev (f n)) κ)) ⊎ ⊤
    outΩ′ (inj₁ (κ′ , cv)) = inj₁ ((n , inj₁ κ′) , cv)
    outΩ′ (inj₂ t) = inj₂ t
  F (hΩ κ g) = FΩ κ (kd1 κ) g (λ x → F (g x))
  G hz (inj₁ κ) = inj₁ (κ , λ x → x)
  G hz (inj₂ tt) = inj₂ tt
  G (hs b) = stepPE (G b) (mapP (F b))
  G (hl f) (n , inj₁ κ′) = outΩ {F′ = λ n → Lev (f n)} n (G (f n) κ′)
  G (hl f) (n , inj₂ tt) = inj₂ tt
  G (hΩ κ g) = GΩ κ (kd1 κ) g (λ x → G (g x))
```
