# 可入下标上的比较式更新 (一): 对角上给 `hself` 的比较

> 不含记号. 入口 [AdmW](AdmW.lagda.md), 接口 [AdmWIf](AdmWIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 更新律 "在 $(c_0,p_0)$ 处恰好接长" 要读出 `cmpB p₀ p₀` 的结果. `HtTowerTy.cmpB` 在 $\Omega$-结点处先比坐标 (`cmpK`), 再用界的合法性里的单调 `mo` 把一边搬过去; 对角上 `cmpK e e` 给出某个自反的 `Pr`, `mo` 对它给出某个 $g\,c\lhd g\,c$ 的证明, 不必字面是 `hself`, 证它是 `hself` 要那个类型的 UIP (诊断 §3.3 义务 2; `AdmWNegLaws` 文件头也记了这一处).
>
> 这里的办法: 在坐标是 `HB S₀` (外层是 `A`) 的情形重写一个比较 `cmpB₀`, 与 `cmpB` 逐条相同, 只在 $\Omega$-结点处多一条: **`cmpF` 返回字面的 `self` 时, 两个坐标在模式匹配里被合一, 直接比较两条子路径, 不调用 `mo`.** 合一的是两个不同的模式变量 (两个 `hLim` 的坐标), 所以不需要 K. 于是
>
> - **`cmpB₀-diag`**: 对一切路径 $p$, `cmpB₀ p p ≡ inj₁ hself` (对 $p$ 归纳; ℕ-极限处用 `dec-diag`, 即 `<ᴺ-dec n n ≡ injᶜ refl`; $\Omega$-结点处用 `cmpF-diag`, 即 `cmpF e e ≡ inj₁ self`).
> - `dec₀`: 由比较结果判定两个坐标相等 (`StallDxBdec.bdec` 的同形物), `dec₀-diag`: 对角上给 `inj₁ refl`.
> - 共用引理: `<ᴮ-tr` (严格子项传递).
>
> `cmpB₀` 是一个比较 (类型与 `cmpB` 相同), 不改任何已有定义.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWCmp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg; lg⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; wf; irr; toLt; lt→≢)
```

## §1 两个对角引理

```agda
dec-diag : ∀ n → <ᴺ-dec n n ≡ injᶜ refl
dec-diag zero = refl
dec-diag (suc n) rewrite dec-diag n = refl

cmpF-diag : ∀ {a L} (p : a ⊲ L) (w : Lg L) → cmpF p p w ≡ inj₁ C.self
cmpF-diag C.self w = refl
cmpF-diag (C.suc p) w = cmpF-diag p w
cmpF-diag (C.lim n p) (st , w) rewrite dec-diag n = cmpF-diag p (w n)
```

## §2 比较 `cmpB₀`

与 `cmpB` 逐条相同 (`S = S₀`, `cmpK S₀ = cmpF`, `lgBd S₀ = lg⊲`), $\Omega$-结点处多一条 `inj₁ C.self`.

```agda
cmpB₀ : ∀ {a b L w} → a ⊲[ w ] L → b ⊲[ w ] L → Lg w → LgB {S₀} L → (b ⊲[ w ] a) ⊎ (a ⊲[ w ] b)
cmpB₀ hself q lw l = inj₁ q
cmpB₀ p hself lw l = inj₂ p
cmpB₀ (hsuc p) (hsuc q) lw l = cmpB₀ p q lw l
cmpB₀ (hlim n p) (hlim m q) lw (st , l) with <ᴺ-dec n m
... | injᵃ n<m = cmpB₀ (⊲ᴮ-tr p (stepsᴮ st n<m)) q lw (l m)
... | injᵇ m<n = cmpB₀ p (⊲ᴮ-tr q (stepsᴮ st m<n)) lw (l n)
... | injᶜ refl = cmpB₀ p q lw (l n)
cmpB₀ (hLim e p) (hLim e′ q) lw (mo , l) with cmpF e e′ lw
... | inj₁ C.self = cmpB₀ p q lw (l _ (lg⊲ e lw))
... | inj₁ c′c = cmpB₀ p (⊲ᴮ-tr q (mo lw e′ e c′c)) lw (l _ (lg⊲ e lw))
... | inj₂ cc′ = cmpB₀ (⊲ᴮ-tr p (mo lw e e′ cc′)) q lw (l _ (lg⊲ e′ lw))
```

**对角.** 对 $p$ 归纳; 每一步把对角上的 `with` 结果改写成它的对角值.

```agda
cmpB₀-diag : ∀ {a L w} (p : a ⊲[ w ] L) (lw : Lg w) (l : LgB {S₀} L) → cmpB₀ p p lw l ≡ inj₁ hself
cmpB₀-diag hself lw l = refl
cmpB₀-diag (hsuc p) lw l = cmpB₀-diag p lw l
cmpB₀-diag (hlim n p) lw (st , l) rewrite dec-diag n = cmpB₀-diag p lw (l n)
cmpB₀-diag (hLim e p) lw (mo , l) rewrite cmpF-diag e lw = cmpB₀-diag p lw (l _ (lg⊲ e lw))
```

## §3 由比较结果判定相等

```agda
<ᴮ-tr : ∀ {S} {a b c : HB S} → a <ᴮ b → b <ᴮ c → a <ᴮ c
<ᴮ-tr p <s₀ = <s p
<ᴮ-tr p (<s q) = <s (<ᴮ-tr p q)
<ᴮ-tr p (<l₀ n) = <l n p
<ᴮ-tr p (<l n q) = <l n (<ᴮ-tr p q)
<ᴮ-tr p (<Ω₀ c) = <Ω c p
<ᴮ-tr p (<Ω c q) = <Ω c (<ᴮ-tr p q)

dec₀ : ∀ {S} {c₀ c : HB S} {w} → (c₀ ⊲[ w ] c) ⊎ (c ⊲[ w ] c₀) → (c₀ ≡ c) ⊎ ¬ (c₀ ≡ c)
dec₀ (inj₁ r) with toLt r
... | inj₁ e = inj₁ e
... | inj₂ s = inj₂ (lt→≢ s)
dec₀ (inj₂ r) with toLt r
... | inj₁ e = inj₁ (sym e)
... | inj₂ s = inj₂ (λ e → lt→≢ s (sym e))

dec₀-diag : ∀ {a L w} (p : a ⊲[ w ] L) (lw : Lg w) (l : LgB {S₀} L) → dec₀ (cmpB₀ p p lw l) ≡ inj₁ refl
dec₀-diag p lw l = cong dec₀ (cmpB₀-diag p lw l)
```
