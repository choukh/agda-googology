# 树侧判据 (二): `ghost` 的推广 (定义与定理)

> 不含记号. 结论写在 [TreeJudge2](TreeJudge2.lagda.md). 只导入 [TreeJudgeBase](TreeJudgeBase.lagda.md) 与 `OCF.Free.*`, stdlib.
>
> `ghost` ([TreeJudgeBase](TreeJudgeBase.lagda.md)) 的前提量词过**一切** $\tau$, 要界 $\ge\tau+1$. 对这里的树这个前提看来是假的: 分支 $b+1$ 上的地板是 `fk b`, 界是 $b+1$, 不是 $b+2$ ([GuardTightTree](GuardTightTree.lagda.md) 的 `pick`); 恒等读法在分支 $2$ 上的界正好是 $2$ (有限测试 `b-id`, [TreeJudge2Test](TreeJudge2Test.lagda.md)). **所以 `ghost` 实例化不到这棵树 (读定义加有限测试, 判断, 没有写成定理).** 但证明只用 $\tau=\mathrm{lv}(t_0)$, 而 $t_0$ 是极限时 $\tau$ 也是极限, `pr τ = τ`.
>
> - `Ghostᴸ`, `ghostᴸ`: 前提只要求 $\tau\cong\mathrm{lv}(t_0)$. `ghost→ᴸ`: 严格强于 `ghost`.
> - `Pinch`, `pinch`: 再推广一步, 不要求第一路径是字面的: 只要 $o\,\tau$ 的证书能推出一个闭包的证书, 界 $\ge\tau+1$, 头的层号 $\sqsubseteq\mathrm{lv}(t_0)$. `Ghostᴸ→Pinch`. [TreeJudge2Id](TreeJudge2Id.lagda.md) 实例化的是它, 因为 `f 0` 不能分情形, 走树的每一步是 `subst` 而不是 `FP` 的构造子.
>
> **这些都是 `Goodᴺ` 的必要条件的逆否, 对一切 `Z`, 无条件.** 它们不是合法性的充分条件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge2Base where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Free.Force using (Goodᴺ; gc; forceᴺ; forceᴺ-HS)
open import OCF.Align.TreeJudgeBase using (FP; fp-good; head-law; lv; lv-≅; ≅ᴵ→⊑; suc⊑self; Ghost; Ghost₁)
```

## §1 `ghostᴸ`: 只看链的第 0 点

```agda
-- 第 0 个链点的层号
Ghostᴸ : ∀ {c} (t₀ : Z) (o : (η : Ordᴵ) → c ⊑ᴵ η → Z) → Set
Ghostᴸ {c} t₀ o = ∀ (G₀ : Goodᴺ t₀) τ (e : c ⊑ᴵ τ) → τ ≅ᴵ lv G₀ → Ghost₁ t₀ τ (o τ e)

ghost→ᴸ : ∀ {c t₀} {o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → Ghost t₀ o → Ghostᴸ t₀ o
ghost→ᴸ gh G₀ τ e _ = gh τ e
```

## §2 `pinch`: 不要字面的第一路径

`Pinch₁ G₀ τ x`: $x$ 的证书推出一个闭包: 界 $c'\ge\tau+1$, 头律 $c'\sqsubseteq\mathrm{lv}(z)$, 而 $\mathrm{lv}(z)\sqsubseteq\mathrm{lv}(t_0)$. 这时 $\tau+1\sqsubseteq\tau$. 这里只写推出来的东西, 不写怎么走到.

```agda
Pinch₁ : ∀ {t₀} → Goodᴺ t₀ → Ordᴵ → Z → Set
Pinch₁ G₀ τ x = Goodᴺ x → Σ Ordᴵ λ c′ → (suc τ ⊑ᴵ c′) × Σ Z λ z → Σ (Goodᴺ z) λ Gz → (c′ ⊑ᴵ lv Gz) × (lv Gz ⊑ᴵ lv G₀)

Pinch : ∀ {c} (t₀ : Z) (o : (η : Ordᴵ) → c ⊑ᴵ η → Z) → Set
Pinch {c} t₀ o = ∀ (G₀ : Goodᴺ t₀) τ (e : c ⊑ᴵ τ) → τ ≅ᴵ lv G₀ → Pinch₁ G₀ τ (o τ e)

pinch : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → Pinch t₀ o → Goodᴺ (ĉᴸ c t₀ g o₀ o) → ⊥
pinch pn (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) with pn G₀ _ (dy 0) (toLevel-≅ (hy 0) (forceᴺ-HS _ G₀) (≅-sym l₀)) (Go 0)
... | c′ , gt , z , Gz , le , ub =
  suc⊑self (⊑ᴵ-trans gt (⊑ᴵ-trans le (⊑ᴵ-trans ub (≅ᴵ→⊑ (≅ᴵ-sym (toLevel-≅ (hy 0) (forceᴺ-HS _ G₀) (≅-sym l₀)))))))

Ghostᴸ→Pinch : ∀ {c t₀} {o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → Ghostᴸ t₀ o → Pinch t₀ o
Ghostᴸ→Pinch gh G₀ τ e τ≅ Gb =
  c′ , bdC , _ , proj₁ H , proj₂ H ,
  ⊑ᴵ-trans (≅ᴵ→⊑ (lv-≅ hdC (proj₁ H) (proj₁ Y))) (toLevel-⊑ (forceᴺ-HS _ (proj₁ Y)) (forceᴺ-HS _ G₀) (proj₂ Y))
  where
  open Ghost₁ (gh G₀ τ e τ≅)
  C = fp-good fpC Gb
  H = head-law (proj₁ C)
  Y = fp-good fpY G₀

ghostᴸ : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} → Ghostᴸ t₀ o → Goodᴺ (ĉᴸ c t₀ g o₀ o) → ⊥
ghostᴸ gh = pinch (Ghostᴸ→Pinch gh)
```
