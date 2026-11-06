# `T⁺` 对输入单调 (一): 一步形式与 (b) 互推

> 不含记号. 接口 [TpMonoIf](TpMonoIf.lagda.md). 对任意 `F : Fn`:
>
> - **`steps→fst`, `steps→fst<`**: `Steps F` (合法性无关, 后继, ℕ-极限第 $n$ 项, $\Omega$-极限最小坐标, 后三步严格) 推出 (b) 的两条 `FstMono F`, `FstMono< F`. 证明取一切世界的路径在最小世界 $w_0=(0,0)$ 的那一条, 对它归纳; 最小世界里 $\Omega$-分支有界的坐标只有最小坐标 (`bd₀`), 所以 `hLim` 一步落在 `s-hΩ` 上.
> - **`fst→steps`**: 反过来 (b) 的两条推出 `Steps F`. 所以 (b) 恰好等价于四条一步律.
>
> 这是对结构参数 (路径) 的一步定理: 新用到的字段只有路径的三个构造子与最小世界里的界 (`Bd` 在 $(0,0)$ 处只容 `bot`). 不涉及 `T⁺` 的定义.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMonoStep where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; s≤; ≤-refl; ≤-trans; ≤-suc)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂)
open import OCF.Align.TpMonoIf
```

## §1 最小世界

```agda
w₀ : Wd₂
w₀ = azero , hz

lw₀ : LgW S₁ w₀
lw₀ = tt , tt

≤s : ∀ {x y} → asuc x ≤ y → x ≤ y
≤s h = ≤-trans (≤-suc (≤-refl _)) h
```

## §2 一步律推出 (b)

```agda
module FromSteps {F : Fn} (St : Steps F) where
  open Steps St

  fst₀ : ∀ {a b} → a ⊲[ w₀ ] b → ∀ la lb → F a la ≤ F b lb
  fst₀ hself la lb = irr _ la lb
  fst₀ (hsuc p) la lb = ≤-trans (fst₀ p la lb) (≤s (s-hs _ lb))
  fst₀ (hlim n p) la lb = ≤-trans (fst₀ p la (proj₂ lb n)) (≤s (s-hl _ lb n))
  fst₀ (hLim {κ = inj₁ tt} C.self p) la lb = ≤-trans (fst₀ p la (proj₂ lb azero tt)) (≤s (s-hΩ (inj₁ tt) _ lb tt))
  fst₀ (hLim {κ = inj₂ tt} hself p) la lb = ≤-trans (fst₀ p la (proj₂ lb hz tt)) (≤s (s-hΩ (inj₂ tt) _ lb tt))

  fst<₀ : ∀ {a b} → a ⊲⁺[ w₀ ] b → ∀ la lb → asuc (F a la) ≤ F b lb
  fst<₀ (psuc p) la lb = ≤-trans (s≤ (fst₀ p la lb)) (s-hs _ lb)
  fst<₀ (plim n p) la lb = ≤-trans (s≤ (fst₀ p la (proj₂ lb n))) (s-hl _ lb n)
  fst<₀ (pLim {κ = inj₁ tt} C.self p) la lb = ≤-trans (s≤ (fst₀ p la (proj₂ lb azero tt))) (s-hΩ (inj₁ tt) _ lb tt)
  fst<₀ (pLim {κ = inj₂ tt} hself p) la lb = ≤-trans (s≤ (fst₀ p la (proj₂ lb hz tt))) (s-hΩ (inj₂ tt) _ lb tt)

steps→fst : ∀ {F} → Steps F → FstMono F
steps→fst St a la b lb p = FromSteps.fst₀ St (p {w₀}) la lb

steps→fst< : ∀ {F} → Steps F → FstMono< F
steps→fst< St a la b lb p = FromSteps.fst<₀ St (p {w₀}) la lb
```

## §3 反过来

```agda
fst→steps : ∀ {F} → FstMono F → FstMono< F → Steps F
fst→steps fm fm< = record
  { irr  = λ a la la′ → fm a la a la′ hself
  ; s-hs = λ a la → fm< a la (hs a) la (psuc hself)
  ; s-hl = λ f lf n → fm< (f n) (proj₂ lf n) (hl f) lf (plim n hself)
  ; s-hΩ = λ κ g lg lc → fm< (g (bot S₁ κ)) (proj₂ lg (bot S₁ κ) lc) (hΩ κ g) lg (λ {w} → pLim (botBd S₁ κ w) hself)
  }

-- (b) 与一步律合成接口的律 (另两条照传)
laws : ∀ {F} → SimInv F → Steps F → ShiftMono F → Laws F
laws sm St sh = record { sim = sm ; fst = steps→fst St ; fst< = steps→fst< St ; shift = sh }
```
