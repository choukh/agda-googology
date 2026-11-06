# 高度来自折叠的输出 (三): 增长

> 不含记号. 入口 [HtOut](HtOut.lagda.md). 序是布劳威尔树上的 `_≤_` ([TLRuleSpec](TLRuleSpec.lagda.md)). 不另写折叠的引理: [HtFeedGrow](HtFeedGrow.lagda.md) 的 `Sta`, `ΩSt` 对一切合法最高层与一切节点族成立, 这里只给出回灌高度上的节点族.
>
> 1. **高度一步一步变大** (`fb-st`, `Λ-st`): $\Lambda_n+1$ 字面地是 $\Lambda_{n+1}$ 的第一位置.
> 2. **回灌保持 $\Omega$-形** (`Fb-Ω`): 最高层是 $\Omega$-极限时, 第 1 层输出的最外一段是折叠的回灌闭包 `nκ`, 读出来又是 $\Omega$-极限. 由检查器归约, 对一切 $g$. 于是 `Λs (n+1)` 都是 `hΩ gₙ` (`Λ-Ω`).
> 3. **`Sup-fb n`**: 在每个回灌高度 $\Lambda_{n+1}=\mathrm{h\Omega}\,g_n$ 上, `ΩSup` 成立: 闭包站严格高于经过 $g_n(j)$ 层的前缀站的任意可数子族的上确界.
> 4. **`Sup-ω`**: 在 $\Lambda_\omega=\mathrm{hl}\,\Lambda_s$ 上, 前缀站的第 $j$ 段过层 $\Lambda_j$; 闭包站严格高于前缀站的任意可数子族的上确界.
>
> 档: 与 `HtFeedGrow.Sup` 同档 (一个折叠实例之内); **不说** `T-fb (n+1)` 高于 `T-fb n` (跨实例, 见入口的第一个障碍).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtOutGrow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedGrow using (module G; module ΩSt; SupStmt)
open import OCF.Align.HtOutRead
open import OCF.Align.HtOutFeed
```

## §1 高度变大

```agda
Λ-st : ∀ n → hs (proj₁ (Λs n)) ⊲[ azero ] proj₁ (Λs (suc n))
Λ-st n = fb-fst (Λs n)
```

## §2 回灌保持 $\Omega$-形

```agda
ΩHL : Set
ΩHL = Σ (A → H) (λ g → LgH (hΩ g))

Fb-Ω : ∀ g (l : LgH (hΩ g)) → Σ ΩHL (λ y → Fb (hΩ g , l) ≡ (hΩ (proj₁ y) , proj₂ y))
Fb-Ω g l = (_ , _) , refl

Λ₁-form : Σ ΩHL (λ y → Λs 1 ≡ (hΩ (proj₁ y) , proj₂ y))
Λ₁-form = (_ , _) , refl

Λ-Ω : ∀ n → Σ ΩHL (λ y → Λs (suc n) ≡ (hΩ (proj₁ y) , proj₂ y))
Λ-Ω zero = Λ₁-form
Λ-Ω (suc n) with Λ-Ω n
... | (g , l) , e = proj₁ (Fb-Ω g l) , subst (λ x → Fb x ≡ (hΩ (proj₁ (proj₁ (Fb-Ω g l))) , proj₂ (proj₁ (Fb-Ω g l)))) (sym′ e) (proj₂ (Fb-Ω g l))
  where
  sym′ : ∀ {a b : HL} → a ≡ b → b ≡ a
  sym′ refl = refl
```

## §3 每个回灌高度上的 `Sup`

```agda
gₙ : ℕ → A → H
gₙ n = proj₁ (proj₁ (Λ-Ω n))

lₙ : ∀ n → LgH (hΩ (gₙ n))
lₙ n = proj₂ (proj₁ (Λ-Ω n))

Sup-fb : ∀ n → SupStmt (gₙ n) (lₙ n)
Sup-fb n = ΩSt.ΩSup (gₙ n) (lₙ n)
```

## §4 $\Lambda_\omega$ 上的 `Sup`

前缀站的第 $j$ 段过层 $\Lambda_j$ (`sl j`); 回灌闭包在世界 $c$ 上过层 $\Lambda_0$ (节点族可任取, `Sta` 对一切节点族成立).

```agda
module ωSt where
  open G Λω lΛω public
  open Sta (λ j → proj₁ (Λs j) , sl j hself) (λ {c} _ _ → proj₁ (Λs 0) , sl 0 hself) tt public

  Sup-ω : ∀ (σ : ℕ → ℕ) → asuc (alim (λ k → Tψ (Xn (σ k)))) ≤ Tψ Xκ
  Sup-ω = Sup

  pre<-ω : ∀ n → asuc (Tψ (Xn n)) ≤ Tψ (Xn (suc n))
  pre<-ω = pre<
```
