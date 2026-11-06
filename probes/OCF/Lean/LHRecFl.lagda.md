# LHRec (三): 每个层号的地板, 合法 (分量下标是第 $k$ 层的值)

> 不含记号. 入口 [LHRec](LHRec.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [LHRecTy](LHRecTy.lagda.md), [LHRecLeg](LHRecLeg.lagda.md).
>
> **RecB 卡点 1 (分量下标换成第 $k$ 层的值).** RecB 的地板 `fl (suc n)` 是指标种类的结点, 分支 $y\mapsto\sum_{c<y}\iota_c(\text{第 }c\text{ 个分量的地板})$, $y$ 是可数树 (`gtX`). 这里对**一切层号** $x$ 写地板 `flL x : HB (Lv x)` (读 $\Omega_x$, 判断): `lΩ k g` 的地板是指标种类 ($\Omega_{k+1}$, 坐标是第 $k$ 层的值) 的结点, 分支 $y$ 是 θ 累加 (`LHRecLeg.New.θ`): 后继 $d+1$ 处加上 $\iota_d(\texttt{flL}\,(g\,d))$, ℕ-极限逐点, **坐标 $y$ 里的 $\Omega$-结点映成指标分量 `step (Lv k)` 的旧种类** (`inj₁ κ`, 坐标相同). $k=$ `lz` 时 $y$ 没有 $\Omega$-结点, 与 RecB 的 `gtX` 同形.
>
> **合法** `Lg-flL`: 对一切层号, 一步归纳 (RecB 接手清单 5 "地板合法没有证" 在这里对一切层号是定理). 用到: `up`, `ι` 在一切世界保第一位置与合法 (§1), θ 累加的单调与合法 (`LHRecLeg`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LHRecFl where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLeg using (Ctx; here; viaL; module New)
```

## §1 `up`, `ι` 保第一位置与合法

```agda
module _ {S : KS} where
  up-⊲ : ∀ {a b} {W : Wd (step S)} → a ⊲[ proj₁ W ] b → up a ⊲[ W ] up b
  up-⊲ hself = hself
  up-⊲ (hsuc p) = hsuc (up-⊲ p)
  up-⊲ (hlim n p) = hlim n (up-⊲ p)
  up-⊲ (hLim e p) = hLim e (up-⊲ p)

  Lg-up : ∀ a → LgB a → LgB (up {S} a)
  Lg-up hz l = tt
  Lg-up (hs a) l = Lg-up a l
  Lg-up (hl f) (st , l) = (λ n → up-⊲ (st n)) , (λ n → Lg-up (f n) (l n))
  Lg-up (hΩ κ g) (mo , l) = (λ lw e e′ p → up-⊲ (mo (proj₁ lw) e e′ p)) , (λ lw e → Lg-up (g _) (l (proj₁ lw) e))

module _ {I : Set} {F : I → KS} where
  ι-⊲ : ∀ {i a b} {W : Wd (sup I F)} → a ⊲[ W i ] b → ι {I} {F} i a ⊲[ W ] ι i b
  ι-⊲ hself = hself
  ι-⊲ (hsuc p) = hsuc (ι-⊲ p)
  ι-⊲ (hlim n p) = hlim n (ι-⊲ p)
  ι-⊲ (hLim e p) = hLim e (ι-⊲ p)

  Lg-ι : ∀ i a → LgB a → LgB (ι {I} {F} i a)
  Lg-ι i hz l = tt
  Lg-ι i (hs a) l = Lg-ι i a l
  Lg-ι i (hl f) (st , l) = (λ n → ι-⊲ (st n)) , (λ n → Lg-ι i (f n) (l n))
  Lg-ι i (hΩ κ g) (mo , l) = (λ lw e e′ p → ι-⊲ (mo (lw i) e e′ p)) , (λ lw e → Lg-ι i (g _) (l (lw i) e))
```

## §2 地板

```agda
-- θ 累加的被加项: 后继 d+1 处是第 d 个分量的地板
gcF : ∀ {U T : KS} → (HB U → HB T) → HB U → HB T
gcF φ (hs d) = φ d
gcF φ _ = hz

-- 指标种类 (Ω_{k+1})
ixK : ∀ {k g} → K (Lv (lΩ k g))
ixK = inj₁ tt , inj₂ tt

cxI : ∀ k g → Ctx (Lv (lΩ k g)) (step (Lv k))
cxI k g = viaL {F = FXL k g} here (inj₁ tt)

flL : ∀ x → HB (Lv x)
ΣF : (f : ℕ → LH) → ℕ → HB (Lv (ll f))
flL lz = hz
flL (ls x) = hΩ (inj₂ tt) up
flL (ll f) = hl (ΣF f)
flL (lΩ k g) = hΩ ixK (New.θ (cxI k g) (gcF (λ d → ι {IxL k} {FXL k g} (inj₂ d) (flL (g d)))))
ΣF f zero = ι 0 (flL (f 0))
ΣF f (suc n) = ΣF f n ⊞ ι (suc n) (flL (f (suc n)))
```

## §3 地板合法 (对一切层号)

```agda
Lg-flL : ∀ x → LgB (flL x)
Lg-ΣF : ∀ f n → LgB (ΣF f n)
Lg-flL lz = tt
Lg-flL (ls x) = (λ lw e e′ p → up-⊲ p) , (λ lw e → Lg-up _ (lgB⊲ e (proj₁ lw) (proj₂ lw)))
Lg-flL (ll f) = (λ n → ⊞-fst (ΣF f n) (ι (suc n) (flL (f (suc n))))) , Lg-ΣF f
Lg-flL (lΩ k g) =
  (λ lw e e′ p → New.θ-⊲ (cxI k g) φ p) ,
  (λ lw e → New.Lg-θ (cxI k g) φ lφ _ (lgB⊲ e (proj₁ (lw (inj₁ tt))) (proj₂ (lw (inj₁ tt)))))
  where
  φ : HB (Lv k) → HB (Lv (lΩ k g))
  φ = gcF (λ d → ι {IxL k} {FXL k g} (inj₂ d) (flL (g d)))
  lφ : ∀ d → LgB (φ d)
  lφ hz = tt
  lφ (hs d) = Lg-ι (inj₂ d) (flL (g d)) (Lg-flL (g d))
  lφ (hl f) = tt
  lφ (hΩ κ h) = tt
Lg-ΣF f zero = Lg-ι 0 (flL (f 0)) (Lg-flL (f 0))
Lg-ΣF f (suc n) = Lg-⊞ _ (ι (suc n) (flL (f (suc n)))) (Lg-ΣF f n) (Lg-ι (suc n) (flL (f (suc n))) (Lg-flL (f (suc n))))
```
