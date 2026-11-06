# RaiseC (四): 高度 `HB S` 上的升界算子

> 不含记号. 入口 [RaiseC](RaiseC.lagda.md). 对着接口 [RaiseIf](RaiseIf.lagda.md) §2 (`RaiseB S`, 第一位置相对一个合法世界).
>
> 1. **`R-in→cmpᴮ`, `R-out-evodᴮ`, `no-alwaysᴮ` (定理, 对一切 `S`, 一切合法世界).** 与 `A` 上同形 (`RaiseCBase`): $v\lhd_w R\,a\,v$ 推出 $a, v$ 在 $w$ 里可比; 偶数列与奇数列的 ℕ-极限那一对, $R$ 的输出不含 $v$; "总把 $v$ 放进去" 撞 `HtTowerNeg.no-joinᴮ`. 合法世界的实例: `S₀` 的 $0$, `step` 加 $0$, 一切 `Lev x` 的最小世界 (`lg-dW`).
> 2. **`Rᴮᵇ` (构造, 对一切 `S`).** 带公共上界 $\Lambda$ 与一个合法世界 $w$ 的证据时, `cmpB` 取大. 在一切 $w'\ge w$ 里两条下界律成立 (不要前提 $a\lhd_{w'} v$), 合法, 仍在 $\Lambda$ 之下. 这是接口的 `RaiseB` 的有界版: 值依赖起始世界 $w$ 的证据.
> 3. **`decᴮ→RaiseB₀` (条件, 只对 `S₀`).** 若 `HB S₀` 上 "$a\lhd_c v$" 对一切世界 $c$ 可判定, 则 `RaiseB S₀` 有实例: $R\,a\,v = \Omega\text{-结点}\ (c\mapsto v$ 若 $a\lhd_c v$, 否则 $a)$. 这里用到 `S₀` 的世界就是坐标 (`A`), 所以 $\Omega$-结点可以按世界分支. 前提推出 LPO (**`decᴮ→LPO`**). 值的定理: 输出是 $\Omega$-结点 (`decᴮ-head`), 所以它在一切世界里都不是 $a$ 或 $v$ 的字面第一位置的那一层 (判断: 读法远大于 $\max(a,v)$; 接口不管大小).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RaiseCB where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Barrier using (LPO)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (evᴴ; odᴴ; Lg-ev; Lg-od; no-joinᴮ)
open import OCF.Align.RaiseIf using (RaiseB; Rᴮ; Rᴮ-lo; Rᴮ-hi; Rᴮ-lg)
```

## §1 与 `A` 上同形的三条

```agda
module _ {S : KS} where
  module _ (ρ : RaiseB S) where
    R-in→cmpᴮ : ∀ {a v w} → LgW S w → LgB a → LgB v → v ⊲[ w ] Rᴮ ρ a v → (v ⊲[ w ] a) ⊎ (a ⊲[ w ] v)
    R-in→cmpᴮ lw la lv p = cmpB (Rᴮ-lo ρ lw la lv) p lw (Rᴮ-lg ρ la lv)

    R-out-evodᴮ : ∀ {w} → LgW S w → ¬ (hl odᴴ ⊲[ w ] Rᴮ ρ (hl evᴴ) (hl odᴴ))
    R-out-evodᴮ lw p = no-joinᴮ lw (Rᴮ ρ (hl evᴴ) (hl odᴴ) , Rᴮ-lg ρ Lg-ev Lg-od , Rᴮ-lo ρ lw Lg-ev Lg-od , p)

  no-alwaysᴮ : ∀ {w} → LgW S w → ∀ (F : HB S → HB S → HB S) →
    (∀ {a v} → LgB a → LgB v → a ⊲[ w ] F a v) → (∀ {a v} → LgB a → LgB v → LgB (F a v)) →
    ¬ (∀ {a v} → LgB a → LgB v → v ⊲[ w ] F a v)
  no-alwaysᴮ lw F lo gd al = no-joinᴮ lw (F (hl evᴴ) (hl odᴴ) , gd Lg-ev Lg-od , lo Lg-ev Lg-od , al Lg-ev Lg-od)
```

**合法世界的实例** (上面的前提 `LgW S w` 可满足): 每一级 `Lev x` 取最小的世界.

```agda
dW : ∀ {S} (x : HB S) → Wd (Lev x)
dW hz = azero
dW (hs x) = dW x , hz
dW (hl f) = λ n → dW (f n)
dW (hΩ κ g) = λ c → dW (g c)

lg-dW : ∀ {S} (x : HB S) → LgW (Lev x) (dW x)
lg-dW hz = tt
lg-dW (hs x) = lg-dW x , tt
lg-dW (hl f) = λ n → lg-dW (f n)
lg-dW (hΩ κ g) = λ c → lg-dW (g c)

lgW-S₀ : LgW S₀ azero
lgW-S₀ = tt

lgW-step : ∀ {S w} → LgW S w → LgW (step S) (w , hz)
lgW-step lw = lw , tt
```

## §2 有界版 (构造, 对一切 `S`)

```agda
module _ {S : KS} where
  pickᴮ : ∀ {a v : HB S} {w} → (v ⊲[ w ] a) ⊎ (a ⊲[ w ] v) → HB S
  pickᴮ {a} (inj₁ _) = a
  pickᴮ {v = v} (inj₂ _) = v

  module _ {a v Λ : HB S} {w : Wd S} (p : a ⊲[ w ] Λ) (q : v ⊲[ w ] Λ) (lw : LgW S w) (lΛ : LgB Λ) where
    Rᴮᵇ : HB S
    Rᴮᵇ = pickᴮ (cmpB p q lw lΛ)

    Rᴮᵇ-Λ : Rᴮᵇ ⊲[ w ] Λ
    Rᴮᵇ-Λ with cmpB p q lw lΛ
    ... | inj₁ _ = p
    ... | inj₂ _ = q

    Rᴮᵇ-lg : LgB Rᴮᵇ
    Rᴮᵇ-lg = lgB⊲ Rᴮᵇ-Λ lw lΛ

    Rᴮᵇ-lo : ∀ {w′} → _≤w_ S w w′ → a ⊲[ w′ ] Rᴮᵇ
    Rᴮᵇ-lo le with cmpB p q lw lΛ
    ... | inj₁ _ = hself
    ... | inj₂ av = ⊲ᴮ↑ le av

    -- 不要前提 a ⊲ v
    Rᴮᵇ-hi : ∀ {w′} → _≤w_ S w w′ → v ⊲[ w′ ] Rᴮᵇ
    Rᴮᵇ-hi le with cmpB p q lw lΛ
    ... | inj₁ va = ⊲ᴮ↑ le va
    ... | inj₂ _ = hself

    Rᴮᵇ-least : ∀ {c} → a ⊲[ w ] c → v ⊲[ w ] c → Rᴮᵇ ⊲[ w ] c
    Rᴮᵇ-least ac vc with cmpB p q lw lΛ
    ... | inj₁ _ = ac
    ... | inj₂ _ = vc
```

## §3 `S₀` 上的经典实例 (条件)

`S₀` 的世界是 `A`, 正好是 `S₀` 的唯一种类的坐标. 所以可以写一个按世界分支的 $\Omega$-结点.

```agda
module DecB (d : ∀ (a v : HB S₀) (c : A) → Dec (a ⊲[ c ] v)) where
  pk : ∀ {a v : HB S₀} {c} → Dec (a ⊲[ c ] v) → HB S₀
  pk {v = v} (yes _) = v
  pk {a} (no _) = a

  h : HB S₀ → HB S₀ → A → HB S₀
  h a v c = pk (d a v c)

  Rd : HB S₀ → HB S₀ → HB S₀
  Rd a v = hΩ tt (h a v)

  h0 : ∀ a v {w} → a ⊲[ w ] h a v azero
  h0 a v {w} with d a v azero
  ... | yes p = ⊲ᴮ↑ (z⊲ w) p
  ... | no _ = hself

  hw : ∀ a v w → a ⊲[ w ] v → v ⊲[ w ] h a v w
  hw a v w p with d a v w
  ... | yes _ = hself
  ... | no n = ⊥-elim (n p)

  h-mono : ∀ a v {w c c′} → c ⊲ w → c′ ⊲ w → c ⊲ c′ → h a v c ⊲[ w ] h a v c′
  h-mono a v {w} {c} {c′} cw c′w cc′ with d a v c | d a v c′
  ... | yes _ | yes _ = hself
  ... | no _ | no _ = hself
  ... | no _ | yes p = ⊲ᴮ↑ c′w p
  ... | yes p | no n = ⊥-elim (n (⊲ᴮ↑ cc′ p))

  h-lg : ∀ a v → LgB a → LgB v → ∀ c → LgB (h a v c)
  h-lg a v la lv c with d a v c
  ... | yes _ = lv
  ... | no _ = la

  decᴮ→RaiseB₀ : RaiseB S₀
  decᴮ→RaiseB₀ = record
    { Rᴮ = Rd
    ; Rᴮ-lo = λ {a} {v} {w} lw la lv → hLim {c = azero} (z⊲ w) (h0 a v)
    ; Rᴮ-hi = λ {a} {v} {w} lw la lv p → hLim {c = w} C.self (hw a v w p)
    ; Rᴮ-lg = λ {a} {v} la lv → (λ {w} {c} {c′} lw cw c′w cc′ → h-mono a v cw c′w cc′) , (λ c _ → h-lg a v la lv c) }

  decᴮ-head : ∀ a v → Rd a v ≡ hΩ tt (h a v)
  decᴮ-head a v = refl
```

**前提推出 LPO** (与 `CumUpClean.dec⊲→LPO` 同形).

```agda
bitᴴ : Bool → HB S₀
bitᴴ true = hs hz
bitᴴ false = hz

no-1⊲0 : ∀ {w} → ¬ (hs {S₀} hz ⊲[ w ] hz)
no-1⊲0 ()

decᴮ→LPO : (∀ (a v : HB S₀) (c : A) → Dec (a ⊲[ c ] v)) → LPO
decᴮ→LPO d α with d (hs hz) (hl (λ n → bitᴴ (α n))) azero
... | yes (hlim n p) = inj₁ (n , aux (α n) p)
  where
  aux : ∀ b → hs hz ⊲[ azero ] bitᴴ b → b ≡ true
  aux true _ = refl
  aux false q = ⊥-elim (no-1⊲0 q)
... | no q = inj₂ (λ k → aux′ k (α k) refl)
  where
  aux′ : ∀ k b → α k ≡ b → α k ≡ false
  aux′ k false e = e
  aux′ k true e = ⊥-elim (q (hlim k (sub e)))
    where
    sub : α k ≡ true → hs hz ⊲[ azero ] bitᴴ (α k)
    sub e′ rewrite e′ = hself
```
