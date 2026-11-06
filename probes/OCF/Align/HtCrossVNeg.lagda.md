# 跨高度, 不用外延性 (四): 边界

> 不含记号. 入口 [HtCrossV](HtCrossV.lagda.md). 三条编译过的定理, 划出不用函数外延性的换实例能做到哪里.
>
> 1. **`eq0↔ext`**: 原路线的那一步 ("第 0 层相关 ⇒ 相等", `HtCrossSim.eq0` 的结论) **恰好等价于**第 0 层树的 ℕ-序列的外延性 (`SeqExt₀`). 所以原路线的这一步本身就是外延性的一个实例, 不是可以另行证明的引理. (外延性在 MLTT 里不可证, 这是元定理, 本文不形式化; 本文编译的是等价.)
> 2. **`no-val-world`**: P3 的提法 "状态的第 0 层只要值相等 (`≈`)" 在原关系里接不上: 两个值相等的第 0 层状态 ($1$ 与 $\lim(0,1,1,\dots)$) 回灌出的世界值相等, 但沿它们切出的上下文 (`Cut`, 与实例无关) 在 `Rl` 下不相关. 折叠的关系引理 (`Run-R` 一族) 要上下文相关, 所以 "`zR` 换成 `≈`" 不能只改 `StR` 一处.
> 3. **`no-κ`**: [HtCrossVSim](HtCrossVSim.lagda.md) 的关系不含 $\Omega$-极限的输入: `Ωd (hΩ g)` 与自己不相关. 所以本族的结果对 `Free` 之外的高度无话可说, 这是关系的形状决定的, 不是证明没写完.
>
> 各条说的只是上面写的: (1) 不是否定, 是等价: 不用外延性证 `eq0` 就是证 ℕ-序列的外延性 (后者在 MLTT 里不可证是元定理, 未形式化, 所以 "`eq0` 不可证" 是判断); (2) 否定 "值相等的世界 + 结构关系" 这一组合; (3) 否定 "无 `nκ` 的关系覆盖 $\Omega$-极限". **不否定**一般的跨实例值相等 (那要异质世界的关系, 见入口 "第一个障碍").

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossVNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtCrossVSim
```

## §1 第 0 层的相等就是外延性

```agda
SeqExt₀ : Set
SeqExt₀ = ∀ {W} {d₁ d₂ : ℕ → D₀ W} → (∀ n → d₁ n ≡ d₂ n) → d₁ ≡ d₂

Eq0 : Set
Eq0 = ∀ {W} {x y : D₀ W} → Rl hz x y → x ≡ y

private
  get : ∀ {W} → D₀ W → ℕ → D₀ W
  get (nl d) = d
  get _ = λ _ → n0

  eqA : SeqExt₀ → ∀ (a : AccY hz) {W} {x y : D hz W} → RelA a x y → x ≡ y
  eqA ext (acc g) s0 = refl
  eqA ext (acc g) s1 = refl
  eqA ext (acc g) (s⨾ p q) = cong₂ _⨾_ (eqA ext (acc g) p) (eqA ext (acc g) q)
  eqA ext (acc g) (sl h) = cong nl (ext (λ n → eqA ext (acc g) (h n)))
  eqA ext (acc g) (si {R = ()} h)
  eqA ext (acc g) (sw p) = cong (nw _) (eqA ext (acc g) p)

eq0→ext : Eq0 → SeqExt₀
eq0→ext e {d₁ = d₁} {d₂} h = cong get (e (sl (λ n → subst (Rl hz (d₁ n)) (h n) (refl0 accᴸ (d₁ n)))))

ext→eq0 : SeqExt₀ → Eq0
ext→eq0 ext = eqA ext accᴸ

eq0↔ext : (Eq0 → SeqExt₀) × (SeqExt₀ → Eq0)
eq0↔ext = eq0→ext , ext→eq0
```

## §2 值相等的回灌世界, 不相关的上下文

$z_1 = 1$, $z_2 = \lim(1, 0, 0, \dots)$, 都在世界 $0$. 回灌的世界 $v_i = \mathrm{sum}\,0\,z_i$: $v_1 = 1$, $v_2 = \lim(0, 1, 1, \dots)$, 值相等 (`v≈`). $v_1$ 是 $v_2$ 的第一位置 (第 1 项), 所以两段上下文可以放在同一个世界 $v_2$ 里比; 它们形状不同 (`nw` 对 `nl`).

```agda
d₂ : ℕ → D₀ azero
d₂ zero = n1
d₂ (suc n) = n0

z₁ z₂ : D₀ azero
z₁ = n1
z₂ = nl d₂

v₁ v₂ : A
v₁ = sum azero z₁
v₂ = sum azero z₂

private
  ptv : ∀ n → pt azero d₂ n ≤ v₁
  ptv zero = z≤
  ptv (suc zero) = ≤-refl v₁
  ptv (suc (suc n)) = ptv (suc n)

v≈ : (v₁ ≤ v₂) × (v₂ ≤ v₁)
v≈ = ≤l 1 (≤-refl v₁) , l≤ ptv

lv₁ : Lg v₁
lv₁ = Lg-sum azero z₁ tt

lv₂ : Lg v₂
lv₂ = Lg-sum azero z₂ tt

v₁⊲v₂ : v₁ ⊲ v₂
v₁⊲v₂ = C.lim 1 C.self

u₀ : ∀ {c} → azero ⊲ c → Lg c → D hz c
u₀ _ _ = n1

no-val-world : ¬ Rl hz (Cut u₀ v₁ (sum-fst azero z₁) C.self lv₁ v₁⊲v₂) (Cut u₀ v₂ (sum-fst azero z₂) C.self lv₂ C.self)
no-val-world (s⨾ _ ())
```

## §3 关系不含 $\Omega$-极限的输入

```agda
no-κ : ∀ (g : A → H) {W} → ¬ Rl (hΩ g) (Ωd (hΩ g) {W}) (Ωd (hΩ g) {W})
no-κ g (s⨾ _ ())
```
