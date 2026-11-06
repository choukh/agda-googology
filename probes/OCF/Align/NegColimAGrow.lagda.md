# 只对可入层号给分量的否定 (三): 外层世界变大时, 世界要判定 "旧时是否可入"

> 不含记号. 入口 [NegColimA](NegColimA.lagda.md). 对着接口 [ColimAIf](ColimAIf.lagda.md) ("接口定稿 2026-11-05 11:12 (编译通过)", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 接口判决里写: 外层世界 $w$ 变大时 "种类要沿 `Bd↑` 搬 (本篇不处理, 判断: 只是搬运, 不判定任何东西)". 种类确实只是搬运 (`Bd↑` 是协变的). **世界不是**: `GWA X w` 是可入证据上的函数, 对证据**逆变**. 新世界 `GWA X w′` 要对每个新证据 $p'$ 给值, 而新证据可能属于旧时就可入的层号 (要保留旧值), 也可能属于新可入的层号.
>
> 1. **`need`** (定理, 一般形, 对任何证据族与分量族): 若延拓 `ext` 满足 (a) 旧证据弱化后读旧值 (或更大, 关系 $R$ 只要在 $0$ 处反射), (b) 旧时不可入的层号从 $0$ 开始, (c) 保相干, 则对每个带新证据的层号, "旧时可入" 有弱判定: $\neg\mathrm{Adm}\,y \uplus \neg\neg\mathrm{Adm}\,y$. 这是 `ColimWNeg.raiseA-sep` 的形状换到了外层世界的变大上: 延拓的值本身把旧可入与新可入分开.
> 2. **但在接口的最小实例上它是可判定的** (`odec`, 定理): $X = x_0$, 外层世界 $(a, b) \le (a, b')$ ($b \lhd_{[a]} b'$, $a$ 与 $b'$ 合法), 任一层号 $y$ 带新证据, 则 "$y$ 在 $(a,b)$ 下可入" 可判定. 证明只用 `cmpB` 两次, `toLt`, 子项良基: 先比新证据的坐标 $c$ 与旧界 $b$; 若 $c$ 在 $b$ 之上, 再比 $\mathrm{hs}\,y$ 与 $\mathrm{up}\,b$; 若 $\mathrm{up}\,b$ 严格在 $\mathrm{hs}\,y$ 之下, 则任何旧证据都会给出 $\mathrm{up}\,b <\mathrm{up}\,b$.
> 3. **所以 (1) 的前提在那里可满足** (`ext₀`, 定理): 分量族取常值 `HB S₀` 时, 由 `odec` 造出满足 (a)(b)(c) 的延拓. 真正的分量族 `HB (LevA w y)` 随 $w$ 变, 还要一个搬运 `HB (LevA w y) → HB (LevA w′ y)` (接口说的 "只是搬运"), 本篇没有写 (判断: 对种类递归, 不判定任何东西).
>
> **为什么是构造一路需要的律.** 回灌把输出写回外层 (诊断 §3.1 的 "读界, 升一个槽"), 外层世界的界 $b$ 随之长高; 当前节点的世界 `GWA X w` 要随 $w$ 换成 `GWA X w′`. (a) 是世界序 `_≤GA_` 的跨 $w$ 版本 (旧界不丢); (b) 是自然的初值 (新可入的层号的界从 $0$ 起), 去掉 (b) 本篇不判断; (c) 是 [NegColimACross](NegColimACross.lagda.md) 说的认同所需的不变量.
>
> **只否定什么.** **不否定任何东西**: 诊断的嫌疑 (ii) "外层界长高后世界要对新证据给值, 重新出现分离子" 在形状上成立 (`need` 要一个判定), 但在 $x_0$ 上 $b$ 长高时那个判定是构造的 (`odec`), 推不出禁忌. 判断: 外层世界的 `A` 分量 $a$ 也长高时同样可判定 (再用一次 `cmpF` 比坐标与旧的 $a$), 一般的合法 $X$ 也一样 (对 $X$ 的路径归纳), 都没有写. 不合法的新世界 $w'$ 上它是否可判定, 没有查.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegColimAGrow where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; wf; irr; toLt)
open _<ᴮ_
open import OCF.Align.ColimWIf using (AdmL; S₁; x₀)
```

## §1 一般形: 延拓要判定旧可入

```agda
module Need {L : Set} (Adm Adm′ : L → Set) (wk : ∀ {y} → Adm y → Adm′ y)
            (C C′ : L → Set) (tr : ∀ {y} → C y → C′ y)
            (z : ∀ {y} → C′ y) (isZ : ∀ {y} (c : C′ y) → (c ≡ z) ⊎ ¬ (c ≡ z))
            (R : ∀ {y} → C′ y → C′ y → Set) (Rz : ∀ {y} {c : C′ y} → R c z → c ≡ z)
            (one : ∀ {y} → C y) (one≢ : ∀ {y} → ¬ (tr (one {y}) ≡ z)) where
  World World′ : Set
  World = (y : L) → Adm y → C y
  World′ = (y : L) → Adm′ y → C′ y

  Coh : World → Set
  Coh W = ∀ y (p p′ : Adm y) → W y p ≡ W y p′

  Coh′ : World′ → Set
  Coh′ W = ∀ y (p p′ : Adm′ y) → W y p ≡ W y p′

  record Ext : Set where
    field
      ext   : World → World′
      old   : ∀ W → Coh W → ∀ y (p : Adm y) → R (tr (W y p)) (ext W y (wk p))
      fresh : ∀ W y (p′ : Adm′ y) → ¬ Adm y → ext W y p′ ≡ z
      coh   : ∀ W → Coh W → Coh′ (ext W)
  open Ext public

  W₁ : World
  W₁ y p = one

  coh₁ : Coh W₁
  coh₁ y p p′ = refl

  need : Ext → ∀ y (p′ : Adm′ y) → ¬ Adm y ⊎ ¬ ¬ Adm y
  need E y p′ with isZ (ext E W₁ y p′)
  ... | inj₁ eq = inj₁ (λ p → one≢ (Rz (subst (R (tr one)) (trans (coh E W₁ coh₁ y (wk p) p′) eq) (old E W₁ coh₁ y p))))
  ... | inj₂ ne = inj₂ (λ np → ne (fresh E W₁ y p′ np))
```

## §2 接口的最小实例: 旧界 $b$ 长到 $b'$ 时, 旧可入可判定

```agda
module _ {S : KS} where
  lt⊲ : ∀ {a b c : HB S} {w} → a <ᴮ b → b ⊲[ w ] c → a <ᴮ c
  lt⊲ q hself = q
  lt⊲ q (hsuc p) = <s (lt⊲ q p)
  lt⊲ q (hlim n p) = <l n (lt⊲ q p)
  lt⊲ q (hLim {c = c} e p) = <Ω c (lt⊲ q p)

module Grow {a : A} {b b′ : HB S₀} (q : b ⊲[ a ] b′) (la : Lg a) (lb′ : LgB b′) where
  -- up c 里的路径只经旧种类的结点, 不看世界的第二分量
  upW : ∀ {β β′ : HB S₀} (c : HB S₀) {t : HB S₁} → t ⊲[ (a , β) ] up c → t ⊲[ (a , β′) ] up c
  upW hz hself = hself
  upW (hs c) hself = hself
  upW (hs c) (hsuc p) = hsuc (upW c p)
  upW (hl f) hself = hself
  upW (hl f) (hlim n p) = hlim n (upW (f n) p)
  upW (hΩ κ g) hself = hself
  upW (hΩ κ g) (hLim {c = d} e p) = hLim e (upW (g d) p)

  Old New : HB S₁ → Set
  Old y = AdmL x₀ (a , b) y
  New y = AdmL x₀ (a , b′) y

  wkA : ∀ {y} → Old y → New y
  wkA p = ⊲ᴮ↑ (C.self , q) p

  -- 第二次比较: hs y 与 up b, 都在 up c 之下
  second : ∀ {y} → (up b ⊲[ (a , b′) ] hs y) ⊎ (hs y ⊲[ (a , b′) ] up b) → Old y ⊎ ¬ Old y
  second (inj₂ s) = inj₁ (hLim {c = b} hself (upW b s))
  second {y} (inj₁ t) with toLt t
  ... | inj₁ eq = inj₁ (hLim {c = b} hself (subst (λ z → z ⊲[ (a , b) ] up b) eq hself))
  ... | inj₂ lt = inj₂ λ { (hLim e″ q″) → irr (wf _) (lt⊲ lt (⊲ᴮ-tr q″ (up-⊲ {β = b} e″))) }

  odec : ∀ {y} → New y → Old y ⊎ ¬ Old y
  odec {y} (hLim {c = c} e′ q′) with cmpB e′ q la lb′
  ... | inj₂ cb = inj₁ (hLim {c = c} cb (upW c q′))
  ... | inj₁ bc = second (cmpB q′ (up-⊲ bc) (la , lb′) (Lg-up c (lgB⊲ e′ la lb′)))
```

## §3 §1 的前提在这里可满足 (分量族取常值)

```agda
  isZ₀ : (c : HB S₀) → (c ≡ hz) ⊎ ¬ (c ≡ hz)
  isZ₀ hz = inj₁ refl
  isZ₀ (hs _) = inj₂ (λ ())
  isZ₀ (hl _) = inj₂ (λ ())
  isZ₀ (hΩ _ _) = inj₂ (λ ())

  module N = Need Old New wkA (λ _ → HB S₀) (λ _ → HB S₀) (λ c → c) hz isZ₀ _≡_ (λ e → e) (hs hz) (λ ())

  sel : ∀ {y} → (Old y → HB S₀) → Old y ⊎ ¬ Old y → HB S₀
  sel f (inj₁ p) = f p
  sel f (inj₂ _) = hz

  sel-old : ∀ W → N.Coh W → ∀ y (p : Old y) (d : Old y ⊎ ¬ Old y) → W y p ≡ sel (W y) d
  sel-old W cW y p (inj₁ p″) = cW y p p″
  sel-old W cW y p (inj₂ np) = ⊥-elim (np p)

  sel-fresh : ∀ {y} (f : Old y → HB S₀) → ¬ Old y → (d : Old y ⊎ ¬ Old y) → sel f d ≡ hz
  sel-fresh f np (inj₁ p) = ⊥-elim (np p)
  sel-fresh f np (inj₂ _) = refl

  sel-coh : ∀ W → N.Coh W → ∀ y (d d′ : Old y ⊎ ¬ Old y) → sel (W y) d ≡ sel (W y) d′
  sel-coh W cW y (inj₁ p) (inj₁ p′) = cW y p p′
  sel-coh W cW y (inj₁ p) (inj₂ np) = ⊥-elim (np p)
  sel-coh W cW y (inj₂ np) (inj₁ p) = ⊥-elim (np p)
  sel-coh W cW y (inj₂ _) (inj₂ _) = refl

  ext₀ : N.Ext
  ext₀ = record
    { ext = λ W y p′ → sel (W y) (odec p′)
    ; old = λ W cW y p → sel-old W cW y p (odec (wkA p))
    ; fresh = λ W y p′ np → sel-fresh (W y) np (odec p′)
    ; coh = λ W cW y p′ p″ → sel-coh W cW y (odec p′) (odec p″) }

  -- §1 的结论在这里成立 (弱于 odec; 只说明前提不空)
  need₀ : ∀ y (p′ : New y) → ¬ Old y ⊎ ¬ ¬ Old y
  need₀ = N.need ext₀
```
