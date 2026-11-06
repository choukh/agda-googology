# Cubical 验证实验 (四): 经 `funExt` 搬过的合法性证据还算不算得动

> **验证实验, 作者 2026-11-05 准许, 不进成品, 不改规则.** `--cubical --safe` 模块 (库文件另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`), 不开 K. 不改任何已有文件. 无公设, 无洞, 无停机或正性编译指示. 不含记号. 入口 [CubXFe](CubXFe.lagda.md).
>
> 问题 (作者): 函数外延会不会让 FGH 不可计算? 在我们的设计里合法性证明是计算数据: `LgB (hl f)` 的第一分量 (相邻项的第一位置) 被 `cmpB` 调用, 拼进它输出的第一位置证明. 若证据经过由 `funExt` 换来的 `≡` 做 `subst`, 计算会不会停在 `transp`/`hcomp` 上?
>
> 检验 (测试档: 具体闭项上的 `refl`, 不是一般定理): 两个字面不同而逐点相等的分支函数 $f_1\,n =$ `finH (n + 0)`, $f_2\,n =$ `finH n`; $e : f_1\equiv f_2$ 由 `CubXFe.fe` 给出. `LgB (hl f₁)` 的证据沿 $e$ 搬成 `LgB (hl f₂)` 的证据 `l₂`, 喂给 `cmpB`, 再用按构造子计数的 `sz` 读出一个自然数.

```agda
{-# OPTIONS --cubical --safe --lossy-unification #-}
module OCF.Align.CubXComp where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.ColimWIf using (finH)
open import OCF.Align.AdmWCoh using (UIPᴴ)
open import OCF.Align.CubXFe using (fe; uipᴴ)
```

## §1 闭项

```agda
f₁ f₂ : ℕ → HB S₀
f₁ n = finH (n + 0)
f₂ n = finH n

lgFin : ∀ k → LgB {S = S₀} (finH k)
lgFin zero = tt
lgFin (suc k) = lgFin k

l₁ : LgB (hl f₁)
l₁ = (λ n → hsuc hself) , (λ n → lgFin (n + 0))

e : f₁ ≡ f₂
e = fe (λ n → cong finH (+-identityʳ n))

l₂ : LgB (hl f₂)
l₂ = subst (λ f → LgB (hl f)) e l₁
```

`sz` 数第一位置证明的构造子; `out` 把 `cmpB` 的输出读成数 (右边加 100).

```agda
sz : ∀ {a b : HB S₀} {w} → a ⊲[ w ] b → ℕ
sz hself = 1
sz (hsuc p) = suc (sz p)
sz (hlim n p) = suc (sz p)
sz (hLim _ p) = suc (sz p)

out : ∀ {a b : HB S₀} {w} → (b ⊲[ w ] a) ⊎ (a ⊲[ w ] b) → ℕ
out (inj₁ p) = sz p
out (inj₂ p) = 100 + sz p

-- 对照: 不经搬运的证据
r₁ : ℕ
r₁ = out (cmpB {a = finH 1} {b = finH 3} {L = hl f₁} {w = azero} (hlim 1 hself) (hlim 3 hself) tt l₁)

-- 经 funExt 换来的 ≡ 搬运的证据
r₂ : ℕ
r₂ = out (cmpB {a = finH 1} {b = finH 3} {L = hl f₂} {w = azero} (hlim 1 hself) (hlim 3 hself) tt l₂)
```

## §2 `refl` 检验

```agda
t₁ : r₁ ≡ 103
t₁ = refl

t₂ : r₂ ≡ 103
t₂ = refl
```

## §3 沿 `uipᴴ` 产生的相等搬运

`uipᴴ` (= `AdmWUip.fe→uip fe`) 给出两条字面不同的相等证明 $E_1, E_2 :$ `hl f₁ ≡ hl f₂` 之间的相等 $u$. 沿 $u$ 搬一个依赖于证明的数据: `Fam r` 是 "数 $k$ 等于沿 $r$ 搬过的证据喂给 `cmpB` 的输出".

```agda
E₁ E₂ : hl f₁ ≡ hl f₂
E₁ = cong hl e
E₂ = cong hl (fe (λ n → sym (sym (cong finH (+-identityʳ n)))))

u : E₁ ≡ E₂
u = uipᴴ E₁ E₂

rd : hl f₁ ≡ hl f₂ → ℕ
rd r = out (cmpB {a = finH 1} {b = finH 3} {L = hl f₂} {w = azero} (hlim 1 hself) (hlim 3 hself) tt (subst LgB r l₁))

Fam : hl f₁ ≡ hl f₂ → Set
Fam r = Σ ℕ (λ k → k ≡ rd r)

t₃ : rd E₂ ≡ 103
t₃ = refl

v : Fam E₂
v = subst Fam u (103 , refl)

t₄ : proj₁ v ≡ 103
t₄ = refl

-- 常值族
t₅ : subst (λ _ → ℕ) u 7 ≡ 7
t₅ = refl
```

## §4 沿非常值的指标线搬第一位置证明

上面搬的是 `LgB (hl f)`: `LgB` 先按 `hl` 归约成 Σ, 每个分量的指标在具体的 $n$ 处归约成常值, 所以搬运推得动. 下面直接沿 $E_1 :$ `hl f₁ ≡ hl f₂` 搬一个第一位置证明 `hlim 3 hself : finH 3 ⊲ hl f₁`. 这里指标线是 `hl` 作用在函数之间的路径上, 构造子 `hlim` 的指标是 `hl f` (要 `hl` 的单射), 正是 `-W noUnsupportedIndexedMatch` 压下的那类匹配.

```agda
q₂ : finH 3 ⊲[ azero ] hl f₂
q₂ = subst (λ L → finH 3 ⊲[ azero ] L) E₁ (hlim 3 hself)

t₆ : sz q₂ ≡ 2
t₆ = refl
```

`t₆` 通过: 搬过的证明本身推得动 (`sz` 的匹配不需要 `hl` 的单射, 第二个指标是变量). 但把 `q₂` 喂给 `cmpB` 时 `refl` **失败** (测试档; 下面这条不进代码块, 只记录):

```text
t₇ : out (cmpB {a = finH 1} {b = finH 3} {L = hl f₂} {w = azero} (hlim 1 hself) q₂ tt l₂) ≡ 103
t₇ = refl
-- error: [UnequalTerms]
-- out (primHComp (λ i → isOneEmpty)
--       (Data.Sum.Base.transp_⊎_ (λ i → finH 3 ⊲[ azero ] finH 1) (λ i → finH 1 ⊲[ azero ] finH 3) i0
--         (cmpB (hlim 1 hself)
--               (OCF.Align.HtTowerTy.transpX-_⊲[_]_ (λ n → primComp (λ i → HB …) …) …)
--               (primTransp (λ i → LgW S₀ azero) … tt)
--               (primTransp (λ i → LgB (hl f₂)) … l₂))))
-- != 103 of type ℕ
```

卡住的项: `cmpB` 的第二个参数是 `transpX-_⊲[_]_ …` (立方 Agda 对带指标族沿非常值指标线搬运时生成的中性项), `cmpB` 的子句 `cmpB (hlim n p) (hlim m q)` 要两个证明的指标都是 `hl f` 同一个 `f`, 依赖构造子 `hl` 的单射; 立方 Agda 对这类子句不生成搬运情形 (`HtTowerTy` 在打开该警告时的原文: "This clause uses pattern-matching features that are not yet supported by Cubical Agda, the function to which it belongs will not compute when applied to transports. Reason: It relies on injectivity of the data constructor hl", `cmpB` 处共 6 条, 对 `hl`, `hs`, `hΩ`). 库选项 `-W noUnsupportedIndexedMatch` 只是不显示这条警告, 不改计算: 把 `HtTowerTy` 拷贝成 `--cubical` 模块重新检查 (scratch 里的 `TwHtTowerTyC`), 同一个 `t₇` 同样卡在 `TwHtTowerTyC.transpX-_⊲[_]_` 上; 原选项 (`--cubical-compatible`) 下打开警告, 同样是这 6 条.
