# 只对可入层号给分量的否定 (四): 律的定义域, `RaiseA′` 要外层界合法

> 不含记号. 入口 [NegColimA](NegColimA.lagda.md). 对着接口 [ColimAIf](ColimAIf.lagda.md) ("接口定稿 2026-11-05 11:12 (编译通过)", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示; `FE₀` (`ColimWNeg.FE₀`, 只对 `ℕ → HB S₀` 的函数外延) 只作前提, 用到它的结论标 "条件".
>
> 接口的 `RaiseA′` 记录以 $X$, $w$ 为模块参数, 字段里**不带** $X$ 或 $w$ 的合法性. 它的 `atA`/`offA` 在 $X$ 之下的两个可入层号上判等; 接口 §判决第 5 条说构造用 `bdec`, 而 `bdec` 要 `LgW S w` 与 `LgB X`. 本篇说明这不是可省的细节:
>
> - **`SepD.raiseA′-sep`** (定理, 无条件): 外层界取 $X_\alpha = \lim(\mathrm{hs}\,(\mathrm{up}\,y_\alpha), \mathrm{hs}\,(\mathrm{up}\,\omega_0), \mathrm{hs}\,(\mathrm{up}\,\omega_0), \dots)$ ($y_\alpha$ 是 `ColimWNeg.yα`; $\alpha$ 某处为真时 $X_\alpha$ 不合法, `illegal`, 定理; 常值假时前两项定义相等, 合法), 两个层号 `up (yα α)`, `up ω₀` 都在 $X_\alpha$ 之下可入 (`hlim 0 hself`, `hlim 1 hself`). 若对一切 $\alpha$ 都有 `RaiseA′ (Xα α) wω`, 则对每个 $\alpha$: `up (yα α) ≢ up ω₀` 或 $\alpha$ 恒假. **`raiseA′→WLPO`** (条件: `FE₀`): WLPO.
> - 证明只用 `atA` (前提是相等), `offA` (前提是不等), 常值族增量 $1$ (族相干是 `refl`), 全 0 的世界. 这与 `ColimWNeg.raiseA-sep` 同形, 区别是这里每个被读的下标都**带证据**: 分离子来自外层界的合法性随 $\alpha$ 变而不能一致地提供 (某处为真时两个可入层号不在一条可比的链上), 不来自裸下标.
>
> **为什么是构造一路需要的律.** `atA`, `offA` 是接口原文; 它们对**一切** $X$, $w$ 以模块参数的形式出现. 结论: 构造一路给出的 `RaiseA′ X w` 必须以 `LgB X`, `LgW S w` 为前提 (`bdec` 的前提), 不能对任意外层界一致地给出. 折叠只在合法节点上回灌, 所以这一条不挡折叠 (判断).
>
> **前提实例.** `wω` 合法 (`ColimWNeg.Lg-wω`); 两个可入证据是闭项; 经典地 (高度相等可判定) 每个 `RaiseA′ (Xα α) wω` 都存在, 所以前提族经典可满足; `FE₀` 在 Agda 里证不出也否证不了, 条件定理的意思与 `ColimWNeg.raiseA→WLPO` 同档 (实现性模型里 `FE₀` 成立而 WLPO 不成立, 那里这一族不存在; 纸面, 元定理).
>
> **只否定什么.** 只否定: 对不合法的外层界 $X_\alpha$ 一族一致地满足 `atA`/`offA` (条件: `FE₀`; 无条件的是分离子). **不否定**: 带 `LgB X`, `LgW S w` 前提构造的 `RaiseA′` (那里 `bdec` 给判定, 不推出禁忌); 族增量的写法; 接口的任何别的律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegColimADom where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.ColimWIf using (AdmL; S₁; ω₀)
open import OCF.Align.ColimWNeg using (wω; WLPO; FE₀; yα; ne₁; yα≡; isz; isz-true; t≢f; fin⊲; up-fin; unhs)
open import OCF.Align.ColimWIf using (finH)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Align.ColimAIf
```

## §1 不合法的外层界, 两个可入层号

```agda
Gα : (ℕ → Bool) → ℕ → HB S₁
Gα α zero = hs (up (yα α))
Gα α (suc _) = hs (up ω₀)

Xα : (ℕ → Bool) → HB S₁
Xα α = hl (Gα α)

pa : ∀ α → AdmL (Xα α) wω (up (yα α))
pa α = hlim 0 hself

pb : ∀ α → AdmL (Xα α) wω (up ω₀)
pb α = hlim 1 hself
```

**某处为真时 $X_\alpha$ 不合法** (前提族里确有不合法的外层界; 常值假的 $\alpha$ 处 $X_\alpha$ 的前两项定义相等, 是合法的, 所以合法性随 $\alpha$ 变, 不能一致地提供).

```agda
unsuc : ∀ {T : KS} {a b : HB T} {w} → hs a ⊲[ w ] hs b → (a ≡ b) ⊎ (hs a ⊲[ w ] b)
unsuc hself = inj₁ refl
unsuc (hsuc p) = inj₂ p

inlim : ∀ {T : KS} {t : HB T} {f w} → hs t ⊲[ w ] hl f → Σ ℕ (λ n → hs t ⊲[ w ] f n)
inlim (hlim n p) = n , p

nlf : ∀ {T : KS} {f : ℕ → HB T} m → ¬ (hl f ≡ finH m)
nlf zero ()
nlf (suc m) ()

nfin : ∀ α {w} n → ¬ (hs (up (yα α)) ⊲[ w ] finH n)
nfin α n q with fin⊲ n q
... | zero , ()
... | suc m , e = nlf m (cong unhs e)

illegal : ∀ α k → α k ≡ true → ¬ LgB (Xα α)
illegal α k e (st , _) with unsuc (st {wω} 0)
... | inj₁ eq = ne₁ α k e eq
... | inj₂ p with inlim p
...   | n , q = nfin α n (subst (λ t → hs (up (yα α)) ⊲[ wω ] t) (up-fin n) q)
```

## §2 分离子

```agda
hs≢hz′ : ∀ {T : KS} {t : HB T} → hs t ≡ hz → ⊥
hs≢hz′ ()

module SepD (R : ∀ α → Adm.RaiseA′ (Xα α) wω) where
  open Adm.RaiseA′

  W₀ : ∀ α → GWA (Xα α) wω
  W₀ α = azero , λ y p → hz

  δ₁ : ∀ α → Adm.IncA (Xα α) wω
  δ₁ α y p = hs hz

  v : ∀ α → HB (LevA wω (up ω₀))
  v α = proj₂ (raiseA (R α) (W₀ α) (up (yα α)) (pa α) (δ₁ α)) (up ω₀) (pb α)

  look : ∀ α (b : Bool) → isz (v α) ≡ b → ¬ (up (yα α) ≡ up ω₀) ⊎ (∀ n → α n ≡ false)
  look α true e = inj₁ (λ eq → hs≢hz′ (trans (sym (atA (R α) (W₀ α) (up (yα α)) (pa α) (δ₁ α) (up ω₀) (pb α) eq)) (isz-true (v α) e)))
  look α false e = inj₂ (λ n → helper n (α n) refl)
    where
    helper : ∀ n b → α n ≡ b → α n ≡ false
    helper n false h = h
    helper n true h = ⊥-elim (t≢f (trans (sym (cong isz (offA (R α) (W₀ α) (up (yα α)) (pa α) (δ₁ α) (up ω₀) (pb α) (ne₁ α n h)))) e))

  raiseA′-sep : ∀ α → ¬ (up (yα α) ≡ up ω₀) ⊎ (∀ n → α n ≡ false)
  raiseA′-sep α = look α (isz (v α)) refl

raiseA′→WLPO : FE₀ → (∀ α → Adm.RaiseA′ (Xα α) wω) → WLPO
raiseA′→WLPO fe R α with SepD.raiseA′-sep R α
... | inj₁ ne = inj₂ (λ h → ne (cong up (yα≡ fe α h)))
... | inj₂ h = inj₁ h
```
