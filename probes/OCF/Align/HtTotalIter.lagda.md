# 折叠对一切高度有定义 (三): 回灌的 $\Omega$-迭代

> 不含记号. 入口 [HtTotal](HtTotal.lagda.md). `Fbᶜ : H → H` 是全函数且 `Good` ([HtTotalClamp](HtTotalClamp.lagda.md)), 所以 [HtFeedHt](HtFeedHt.lagda.md) 的 $\Omega$-迭代 `Ωit`, 沿坐标的变换族 `Tk`, ℕ-对角 `Tω` 都直接用在它上面, 合法性是那里一般定理的实例 (`Good-Ωit`, `Tgd`, `Good-Tω`). 这些定理对迭代的坐标只走路径, 不要坐标合法, 所以 [HtOutNeg](HtOutNeg.lagda.md) 的 `no-total` 不挡: 不合法坐标上的高度不合法也没关系, `Fbᶜ` 照样有定义.
>
> - `ΛΩ₀ = Ωit Fbᶜ 0`: 从 $0$ 出发, 第 $c$ 支是 $\mathrm{Fb}^{\mathsf c}{}^{\,c}(\mathrm{Fb}^{\mathsf c}\,0)$; 第 $0$ 支就是 `HtOutFeed` 的 `Λs 1` (`ΛΩ₀-0`, 由 `agree-fin`).
> - `ΛΩ = Ωit Fbᶜ Λω`: 从 `HtOutFeed` 的 ℕ-对角 $\Lambda_\omega$ (用真的 `Fb` 生成) 出发. `ω⊲Ω`: $\Lambda_\omega$ 字面是它的第一位置.
> - `Λ²ω`: $\Omega$-迭代再沿 ℕ 迭代取对角; `ΛT = Tω Fbᶜ Λω`: `HtFeedHt` 的整族变换用在回灌上.
> - 闭项 `T-Ω₀`, `T-Ω`, `T-Λ²ω`, `T-T`, `fgh`: 都是 `HtFeedClosed.TΛ` 在合法高度上的实例 (这些高度合法, 所以闭项用原来的折叠, 不经夹法).
> - 增长: `Sup-Ω₀`, `Sup-Ω`, `Sup-Tk k`: `HtFeedGrow.Sup` 那一档, 节点族是迭代的各支.
> - `no-agree-it`: [HtTotalNeg](HtTotalNeg.lagda.md) 的 `no-agree` 用在这里的迭代上: 若回灌在迭代的各坐标上用的比较器全有定义, 且在合法坐标上与 `rkT` 判得一样, 则 LPO. 所以迭代里的回灌**只能**是 `Fbᶜ` 这种与 `Fb` 不同的东西 (就比较器那一种做法而言).
>
> 读法都是判断, 见入口.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTotalIter where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Free.Level as FL
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; hself; hlim; ⊲ᴴ-tr; LgH)
open import OCF.Align.HtFeedHt using (Good; lf; fst; it; Ωit; Good-Ωit; Ωit-inf; Hier; T; Tk; Tgd; Tω; Good-Tω)
open import OCF.Align.HtFeedClosed using (TΛ; Lg-TΛ; ord)
open import OCF.Align.HtFeedGrow using (SupStmt; module ΩSt)
open import OCF.Align.HtOutRead using (it-cont)
open import OCF.Align.HtOutFeed using (Λs; Λω; lΛω; top⁺)
open import OCF.Align.HtTotalClamp using (Fbᶜ; Good-Fbᶜ; fbᶜ-fst; agree-fin)
open import OCF.Align.HtTotalNeg using (LPO; Cmp; rises; module Old; no-agree)
open import OCF.Align.HtOutFeed using (Lg-top⁺)
open import OCF.Align.HtOutRead using (cont-lg)
```

## §1 $\Omega$-迭代的高度

```agda
Ωᶜ : H → H
Ωᶜ = Ωit Fbᶜ

Good-Ωᶜ : Good Ωᶜ
Good-Ωᶜ = Good-Ωit Good-Fbᶜ

-- 从 0 出发
ΛΩ₀ : H
ΛΩ₀ = Ωᶜ hz

lΛΩ₀ : LgH ΛΩ₀
lΛΩ₀ = lf Good-Ωᶜ hz tt

-- 第 0 支就是 HtOutFeed 的 Λs 1
ΛΩ₀-0 : it Fbᶜ (Fbᶜ hz) azero ≡ proj₁ (Λs 1)
ΛΩ₀-0 = agree-fin 0 tt

-- 从 ℕ-对角 Λω 出发
ΛΩ : H
ΛΩ = Ωᶜ Λω

lΛΩ : LgH ΛΩ
lΛΩ = lf Good-Ωᶜ Λω lΛω

ω⊲Ω : Λω ⊲[ azero ] ΛΩ
ω⊲Ω = ⊲ᴴ-tr (fst Good-Fbᶜ Λω) (Ωit-inf Fbᶜ Λω)

-- Ω-迭代沿 ℕ 再迭代
Λ²s : ℕ → H
Λ²s zero = Λω
Λ²s (suc n) = Ωᶜ (Λ²s n)

lΛ²s : ∀ n → LgH (Λ²s n)
lΛ²s zero = lΛω
lΛ²s (suc n) = lf Good-Ωᶜ (Λ²s n) (lΛ²s n)

Λ²ω : H
Λ²ω = hl Λ²s

lΛ²ω : LgH Λ²ω
lΛ²ω = (λ n → fst Good-Ωᶜ (Λ²s n)) , lΛ²s

Ω⊲Λ²ω : ΛΩ ⊲[ azero ] Λ²ω
Ω⊲Λ²ω = hlim 1 hself

-- HtFeedHt 的整族变换用在回灌上
ΛT : H
ΛT = Tω Fbᶜ Λω

lΛT : LgH ΛT
lΛT = lf (Good-Tω Good-Fbᶜ) Λω lΛω

Ω⊲ΛT : ΛΩ ⊲[ azero ] ΛT
Ω⊲ΛT = hlim 0 hself
```

## §2 闭项

```agda
T-Ω₀ : A
T-Ω₀ = TΛ ΛΩ₀ lΛΩ₀

T-Ω : A
T-Ω = TΛ ΛΩ lΛΩ

T-Λ²ω : A
T-Λ²ω = TΛ Λ²ω lΛ²ω

T-T : A
T-T = TΛ ΛT lΛT

Lg-T-T : Lg T-T
Lg-T-T = Lg-TΛ ΛT lΛT

fgh : ℕ → ℕ
fgh = FL.FGH (ord T-T)
```

## §3 增长: `Sup` 那一档

`Ωit F x = hΩ (it F (F x))`, `T (Tk (k+1)) F x` 也是 $\Omega$-极限, 所以 `ΩSt.ΩSup` 直接适用.

```agda
Sup-Ω₀ : SupStmt (it Fbᶜ (Fbᶜ hz)) lΛΩ₀
Sup-Ω₀ = ΩSt.ΩSup (it Fbᶜ (Fbᶜ hz)) lΛΩ₀

Sup-Ω : SupStmt (it Fbᶜ (Fbᶜ Λω)) lΛΩ
Sup-Ω = ΩSt.ΩSup (it Fbᶜ (Fbᶜ Λω)) lΛΩ

Sup-Tk : ∀ k → SupStmt (λ c → Hier (T (Tk k)) (T (Tk k) Fbᶜ) c Λω) (lf (Tgd (Tk (suc k)) Good-Fbᶜ) Λω lΛω)
Sup-Tk k = ΩSt.ΩSup (λ c → Hier (T (Tk k)) (T (Tk k) Fbᶜ) c Λω) (lf (Tgd (Tk (suc k)) Good-Fbᶜ) Λω lΛω)
```

## §4 迭代里的回灌不能与 `Fb` 判得一样

迭代 `it Fbᶜ x` 连续 (`it-cont`), 后继处严格变大 (`fbᶜ-fst`), 正是 `no-agree` 的前提.

```agda
no-agree-it : ∀ x → (lx : LgH x) → (rk : Cmp (λ c → top⁺ (it Fbᶜ x c))) →
  (∀ {c} (lc : Lg c) {k t m} (p : k ⊲[ m ] top⁺ (it Fbᶜ x c)) (q : t ⊲[ m ] top⁺ (it Fbᶜ x c)) (lm : Lg m) →
     rises (rk c p q lm) ≡ Old.bitO (top⁺ (it Fbᶜ x c)) (Lg-top⁺ (it Fbᶜ x c) (cont-lg (it-cont Good-Fbᶜ x lx) c lc)) p q lm) → LPO
no-agree-it x lx = no-agree (it Fbᶜ x) (it-cont Good-Fbᶜ x lx) (λ c → fbᶜ-fst (it Fbᶜ x c))
```
