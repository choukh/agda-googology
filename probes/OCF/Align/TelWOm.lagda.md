# 望远镜世界 (二): 携带的位置上的 Ω, 固定望远镜装不下 x ↦ Ω_x

> 不含记号. 入口 [TelW](TelW.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> - **正面.** 位置 $p$ 携带在手时, $\Omega_{\mathrm{lv}\,p+1}$ 是一个合法的望远镜高度 (`Ωp`, `Lg-Ωp`): 坐标 $c$ 经 `up` 放进位置 $p$ 的那一层 (`ιT`), 证明与 `LFReTower.Lg-Ω̂` 的后继情形相同. 推入新层后旧的 `Ωp` 经 `wkH` 仍合法 (`TelWTy.Lg-wk`).
> - **反面 (`no-all-fin`, `no-fixed-Ω`).** 固定一个望远镜 `lvs`, 它装不下一切有限层号: 不存在 $n\mapsto p_n$ 使 `lv pₙ ≡ lsⁿ n` 对一切 $n$ 成立 (鸽笼). 所以**不存在** `HT lvs` 上的 $x\mapsto\Omega_x$, 只要它在有限高度的后继处的顶层种类是 "以参数的层号为层号的新种类" (这正是 `LFReTower.Ω̂ (hs h)` 的形状, 顶层种类 `νL (ofHB h)`, 定义相等).
>
> 结论 (定理 + 一句判断): 塔 $t_{n+1}=\Omega_{t_n}$ 与 $\Lambda$ 在任何**固定的**有限望远镜上都写不出; 判断: $\Lambda$ 之下要有一切有限层号的新种类 ($\Omega_\omega\lhd\Lambda$), 而 $\Omega_{\Omega_1}$ 的分支已经要以分支坐标为层号 (不可数多个). 所以 D1 的高度必须让**分支体推入新位置** (审查 §2 D1 写的 `g : (c : …) → H (c ∷ Γ)`), 新位置的界从哪里来, 见 [TelWNeg](TelWNeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TelWOm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (<-irrefl; n<1+n)
open import Data.Fin using (Fin; toℕ) renaming (zero to fz; suc to fs)
open import Data.Fin.Properties using (pigeonhole; toℕ-injective; suc-injective)
open import Data.List using (List; []; _∷_; length)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (LH; lz; ls; Lv; FL)
open import OCF.Align.TelWTy
```

## §1 位置 $p$ 上的 $\Omega$

`ιT p`: 位置 $p$ 那一层 (`FL (lv p)`) 的高度放进望远镜高度, 种类 $\kappa\mapsto(p,\kappa)$. 与 `HtTowerTy.ι` 同形, 世界取位置 $p$ 的条目.

```agda
module _ {lvs : List LH} (p : Pos lvs) where
  ιT : HB (FL (lv p)) → HT lvs
  ιT hz = hz
  ιT (hs x) = hs (ιT x)
  ιT (hl f) = hl (λ n → ιT (f n))
  ιT (hΩ κ g) = hΩ (p , κ) (λ c → ιT (g c))

  ιT-⊲ : ∀ {a b} {Γ : Tel lvs} → a ⊲[ bnd Γ p ] b → ιT a ⊲[ Γ ] ιT b
  ιT-⊲ hself = hself
  ιT-⊲ (hsuc q) = hsuc (ιT-⊲ q)
  ιT-⊲ (hlim n q) = hlim n (ιT-⊲ q)
  ιT-⊲ (hLim e q) = hLim e (ιT-⊲ q)

  Lg-ιT : ∀ a → LgB a → LgB (ιT a)
  Lg-ιT hz l = tt
  Lg-ιT (hs a) l = Lg-ιT a l
  Lg-ιT (hl f) (st , l) = (λ n → ιT-⊲ (st n)) , (λ n → Lg-ιT (f n) (l n))
  Lg-ιT (hΩ κ g) (mo , l) = (λ lΓ e e′ q → ιT-⊲ (mo (lg-at lΓ p) e e′ q)) , (λ c lc → Lg-ιT (g c) (l c lc))

  -- Ω_{lv p + 1}: 一切界之下的坐标
  Ωp : HT lvs
  Ωp = hΩ (νT p) (λ c → ιT (up c))

  Lg-Ωp : LgB Ωp
  Lg-Ωp = (λ lΓ e e′ q → ιT-⊲ (up-⊲ q)) , (λ c lc → Lg-ιT (up c) (Lg-up c lc))
```

## §2 固定望远镜装不下一切有限层号

```agda
lsⁿ : ℕ → LH
lsⁿ zero = lz
lsⁿ (suc n) = ls (lsⁿ n)

private
  pr : LH → LH
  pr (ls x) = x
  pr y = y

  isZ : LH → Set
  isZ lz = ⊤
  isZ _ = ⊥

lsⁿ-inj : ∀ n m → lsⁿ n ≡ lsⁿ m → n ≡ m
lsⁿ-inj zero zero e = refl
lsⁿ-inj zero (suc m) e = Data.Empty.⊥-elim (subst isZ e tt)
lsⁿ-inj (suc n) zero e = Data.Empty.⊥-elim (subst isZ (sym e) tt)
lsⁿ-inj (suc n) (suc m) e = cong suc (lsⁿ-inj n m (cong pr e))

toFin : ∀ {lvs} → Pos lvs → Fin (length lvs)
toFin z = fz
toFin (s p) = fs (toFin p)

toFin-inj : ∀ {lvs} {p q : Pos lvs} → toFin p ≡ toFin q → p ≡ q
toFin-inj {p = z} {q = z} e = refl
toFin-inj {p = z} {q = s q} ()
toFin-inj {p = s p} {q = z} ()
toFin-inj {p = s p} {q = s q} e = cong s (toFin-inj (suc-injective e))

no-all-fin : ∀ (lvs : List LH) → ¬ (∀ n → Σ (Pos lvs) (λ p → lv p ≡ lsⁿ n))
no-all-fin lvs h with pigeonhole (n<1+n (length lvs)) (λ i → toFin (proj₁ (h (toℕ i))))
... | i , j , i<j , e = <-irrefl (lsⁿ-inj (toℕ i) (toℕ j) lvq) i<j
  where
  pe : proj₁ (h (toℕ i)) ≡ proj₁ (h (toℕ j))
  pe = toFin-inj e
  lvq : lsⁿ (toℕ i) ≡ lsⁿ (toℕ j)
  lvq = trans (sym (proj₂ (h (toℕ i)))) (trans (cong lv pe) (proj₂ (h (toℕ j))))
```

**$x\mapsto\Omega_x$ 的后继形状.** `TopNew Ω′`: 对一切有限高度 $n$, `Ω′ (hs n)` 的顶层是一个新种类的 Ω-节点, 其层号是 $n$ 的层号 `lsⁿ n`. 固定望远镜上没有这样的 `Ω′`.

```agda
finT : ∀ {lvs} → ℕ → HT lvs
finT zero = hz
finT (suc n) = hs (finT n)

TopNew : ∀ {lvs} → (HT lvs → HT lvs) → Set
TopNew {lvs} Ω′ = ∀ n → Σ (Pos lvs) (λ p → Σ (HB (Lv (lv p)) → HT lvs) (λ g →
  (Ω′ (hs (finT n)) ≡ hΩ (νT p) g) × (lv p ≡ lsⁿ n)))

no-fixed-Ω : ∀ lvs (Ω′ : HT lvs → HT lvs) → ¬ TopNew Ω′
no-fixed-Ω lvs Ω′ t = no-all-fin lvs (λ n → proj₁ (t n) , proj₂ (proj₂ (proj₂ (t n))))
```

**正对照: 前提在积世界里可满足.** `LFReTower.Ω̂` 在 `SL` (种类是一切层号, 世界是层号上的积) 上满足同一形状: 顶层种类 `νL (ofHB (hs ⋯ hz))`, 其层号是 `lsⁿ n`. 所以 `no-fixed-Ω` 杀的是 "固定的有限望远镜", 不是这个形状本身.

```agda
open import OCF.Align.LFReTy using (SL; νL; ofHB)
open import OCF.Align.LFReTower using (Ω̂)

finS : ℕ → HB SL
finS zero = hz
finS (suc n) = hs (finS n)

ofHB-fin : ∀ n → ofHB (finS n) ≡ lsⁿ n
ofHB-fin zero = refl
ofHB-fin (suc n) = cong ls (ofHB-fin n)

TopNewSL : ∀ n → Σ (HB (Lv (ofHB (finS n))) → HB SL) (λ g →
  (Ω̂ (hs (finS n)) ≡ hΩ (νL (ofHB (finS n))) g) × (ofHB (finS n) ≡ lsⁿ n))
TopNewSL n = _ , refl , ofHB-fin n
```
