# `T⁺` 对输入单调, 否定一路 (二): 接口的律有模型, 而且对非最小坐标是盲的

> 不含记号. 入口 [NegTpMono](NegTpMono.lagda.md). 接口 [TpMonoIf](TpMonoIf.lagda.md).
>
> - **`rk-laws`, `rk-steps`** (定理): 一个不是 `T⁺` 的 `F` (结构秩 `rk`: 后继加一, ℕ-极限取后继的累加的极限, $\Omega$-极限取最小坐标的分支加一) 满足接口的全部律 `Laws` 与一步律 `Steps`. 所以接口的律合起来不矛盾, 单靠这些律推不出否定; 要否定 `Laws T⁺` 就得用 `T⁺` 的定义 (本路没有找到这样的否定, 见入口). 构造一路的 `TpMonoToy` 给了另一个模型 (ℕ-极限的写法不同); 本文自己写一个, 不导入构造一路的文件.
> - **`blind₂`, `blindᴬ₂`** (定理): 存在满足 `Laws` 与 `Steps` 的 `F`, 使 $F(2)\not\le F(\Omega_2^H)$, 也使 $F(e\,2)+1\not\le F(\Omega^A)$. 所以**单靠接口的律, 推不出 $\Omega$-极限高于它的非最小坐标的分支**, 连 "$T^+(2)\le$ `T-Ω₂`" 都推不出. 律在 $\Omega$-极限处只说到最小坐标 (接口有意如此: 一切世界的路径只走 `bot`). 这是接口的 "盲" 定理 (手册 §3.7): 接口给出的比较只有互模拟、最小坐标链与左加平移三种; `FamFold` 接手清单第 1 项期望的 "`Tᵀ`, `Tᵀ₂`, `Tlv n`, `T∞` 之间的比较" 里, 凡要用到 $\Omega$-极限的非最小坐标的, 都要在接口之外另加律 (判断; 哪些比较要用非最小坐标没有逐个查).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTpMonoBlind where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤-suc; ⊞-mono) renaming (_⊞_ to _+ᴬ_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂; κA; κH)
open import OCF.Align.HtTowerFClosed using (Ω₂ᴴ; lΩ₂)
open import OCF.Align.TpMonoIf
open import OCF.Align.DiagK3Zero using (≈z; ≈s; ≈l; ≈Ω)
open import OCF.Align.NegTpMonoWorld using (eᴬ; Ωᴬ; lΩᴬ)
```

## §1 `A` 上的累加

```agda
+fst : ∀ a b → a C.⊲ a +ᴬ b
+fst a azero = C.self
+fst a (asuc b) = C.suc (+fst a b)
+fst a (alim f) = C.lim 0 (+fst a (f 0))

+⊲ : ∀ a {x y} → x C.⊲ y → a +ᴬ x C.⊲ a +ᴬ y
+⊲ a C.self = C.self
+⊲ a (C.suc p) = C.suc (+⊲ a p)
+⊲ a (C.lim n p) = C.lim n (+⊲ a p)

Lg+ : ∀ a b → Lg a → Lg b → Lg (a +ᴬ b)
Lg+ a azero la lb = la
Lg+ a (asuc b) la lb = Lg+ a b la lb
Lg+ a (alim f) la (st , l) = (λ n → +⊲ a (st n)) , (λ n → Lg+ a (f n) la (l n))

≤+r : ∀ a b → b ≤ a +ᴬ b
≤+r a azero = z≤
≤+r a (asuc b) = s≤ (≤+r a b)
≤+r a (alim f) = l≤ (λ n → ≤l n (≤+r a (f n)))

-- s 0 = 1 + r 0, s (n+1) = s n + (1 + r (n+1))
sm : (ℕ → A) → ℕ → A
sm r zero = asuc (r zero)
sm r (suc n) = sm r n +ᴬ asuc (r (suc n))

Lg-sm : ∀ r → (∀ n → Lg (r n)) → ∀ n → Lg (sm r n)
Lg-sm r l zero = l zero
Lg-sm r l (suc n) = Lg+ (sm r n) (asuc (r (suc n))) (Lg-sm r l n) (l (suc n))

sm-hit : ∀ r n → asuc (r n) ≤ sm r n
sm-hit r zero = ≤-refl _
sm-hit r (suc n) = ≤+r (sm r n) (asuc (r (suc n)))

sm-mono : ∀ {r r′} → (∀ n → r n ≤ r′ n) → ∀ n → sm r n ≤ sm r′ n
sm-mono h zero = s≤ (h zero)
sm-mono h (suc n) = ⊞-mono (sm-mono h n) (s≤ (h (suc n)))
```

## §2 结构秩

```agda
rk : Ht → A
rk hz = azero
rk (hs h) = asuc (rk h)
rk (hl f) = alim (sm (λ n → rk (f n)))
rk (hΩ κ g) = asuc (rk (g (bot S₁ κ)))

Lg-rk : ∀ h → LgB h → Lg (rk h)
Lg-rk hz l = tt
Lg-rk (hs h) l = Lg-rk h l
Lg-rk (hl f) (st , l) = (λ n → +fst (sm (λ m → rk (f m)) n) _) , Lg-sm (λ n → rk (f n)) (λ n → Lg-rk (f n) (l n))
Lg-rk (hΩ (inj₁ tt) g) (mo , l) = Lg-rk (g azero) (l azero tt)
Lg-rk (hΩ (inj₂ tt) g) (mo , l) = Lg-rk (g hz) (l hz tt)

Fᵣ : Fn
Fᵣ h _ = rk h
```

## §3 `rk` 满足接口的律

最小世界 $w_0=(0,0)$ 里, $\Omega$-分支有界的坐标只有 `bot` (对路径的 `self`/`hself` 匹配即得).

```agda
w₀ : Wd₂
w₀ = azero , hz

rk≤ : ∀ {x y} → x ⊲[ w₀ ] y → rk x ≤ rk y
rk< : ∀ {x y} → x ⊲⁺[ w₀ ] y → asuc (rk x) ≤ rk y
rk≤ hself = ≤-refl _
rk≤ (hsuc p) = ≤-suc (rk≤ p)
rk≤ (hlim n p) = ≤-trans (≤-suc (≤-refl _)) (rk< (plim n p))
rk≤ (hLim {κ = κ} e p) = ≤-trans (≤-suc (≤-refl _)) (rk< (pLim {κ = κ} e p))
rk< (psuc p) = s≤ (rk≤ p)
rk< {y = hl f} (plim n p) = ≤l n (≤-trans (s≤ (rk≤ p)) (sm-hit (λ m → rk (f m)) n))
rk< (pLim {κ = inj₁ tt} C.self p) = s≤ (rk≤ p)
rk< (pLim {κ = inj₂ tt} hself p) = s≤ (rk≤ p)

rk-sim : ∀ {x y} → x ≈ y → rk x ≤ rk y
rk-sim ≈z = z≤
rk-sim (≈s p) = s≤ (rk-sim p)
rk-sim (≈l p) = l≤ (λ n → ≤l n (sm-mono (λ m → rk-sim (p m)) n))
rk-sim (≈Ω {κ = κ} p) = s≤ (rk-sim (p (bot S₁ κ)))

rk-shift : ∀ a b → rk b ≤ rk (a ⊞ b)
rk-shift a hz = z≤
rk-shift a (hs b) = s≤ (rk-shift a b)
rk-shift a (hl f) = l≤ (λ n → ≤l n (sm-mono (λ m → rk-shift a (f m)) n))
rk-shift a (hΩ κ g) = s≤ (rk-shift a (g (bot S₁ κ)))

rk-laws : Laws Fᵣ
rk-laws = record
  { sim   = λ a la b lb e → rk-sim e
  ; fst   = λ a la b lb p → rk≤ (p {w₀})
  ; fst<  = λ a la b lb p → rk< (p {w₀})
  ; shift = λ a la b lb → rk-shift a b }

rk-steps : Steps Fᵣ
rk-steps = record
  { irr  = λ a la la′ → ≤-refl _
  ; s-hs = λ a la → ≤-refl _
  ; s-hl = λ f lf n → ≤l n (sm-hit (λ m → rk (f m)) n)
  ; s-hΩ = λ κ g lg lc → ≤-refl _ }
```

## §4 盲

```agda
two : Ht
two = hs (hs hz)

-- F(2) ≰ F(Ω₂ᴴ): rk 2 = 2, rk Ω₂ᴴ = 1
blind₂ : Σ Fn (λ F → Laws F × Steps F × ¬ (F two tt ≤ F Ω₂ᴴ lΩ₂))
blind₂ = Fᵣ , rk-laws , rk-steps , λ { (s≤ ()) }

-- 旧种类: F(e 2) + 1 ≰ F(Ωᴬ)
blindᴬ₂ : Σ Fn (λ F → Laws F × Steps F × ¬ (asuc (F (eᴬ (asuc (asuc azero))) tt) ≤ F Ωᴬ lΩᴬ))
blindᴬ₂ = Fᵣ , rk-laws , rk-steps , λ { (s≤ ()) }
```
