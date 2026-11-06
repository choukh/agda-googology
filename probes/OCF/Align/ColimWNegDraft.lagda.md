# `Lev` 取并的否定 (草稿): 沿塔的映射认同, 律写在裸下标上

> 不含记号. 入口 [ColimWNeg](ColimWNeg.lagda.md). 本篇在接口 [ColimWIf](ColimWIf.lagda.md) 定稿之前写成, 不导入它. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> **对象.** 诊断 §4 第 4 条 (iii) 说 `Lev` 在极限处 "取和而不取并". 真正的余极限沿塔的映射认同拷贝: 坐标 $c_0$ 处的拷贝进坐标 $c$ 处的拷贝, 当且仅当 $c_0$ 是 $c$ 的第一位置. 若世界仍按拷贝存界, 回灌升高 $c_0$ 处的一个种类时, 必须在一切 "与 $c_0$ 认同" 的拷贝处变、在其余拷贝处不变. 把这两条写成对**裸下标**的律 (`Sel.UpdR`: `atR` 在 $R\,i_0\,i$ 处, `offR` 在 $
eg R\,i_0\,i$ 处), 就得到 $R$ 的弱判定 (`updR→wdec`).
>
> - **`wdec⊲→WLPO`** (无条件, 不用外延): 坐标是 `A`, $R$ 是 `A` 的第一位置时, 弱判定 "$1 \lhd a$" 对一切 $a$ 就是 WLPO. 见证是合法的 $a_lpha = \lim_n (lpha$ 前 $n$ 项有真 $? 1 : 0)$. **`HTab.wdecH→WLPO`**: 同样的事对任一种类结构的高度, 任一世界. 比 `DiagKLev.upd→wdec` 强: 那里认同关系是相等, 到 WLPO 要外延; 这里认同关系是第一位置, 它本身就是 "存在一项", 不要外延.
> - **反模型 `AdmModel.model`**: 下标限制在一个合法界 $a$ 之下 (带证据 $c \lhd a$), 同样两条律可满足, 因为同一合法界之下第一位置可判定 (`adm-dec⊲`, 由 `cmpF` 与子项良基).
>
> **与定稿接口的差别.** 接口不沿映射认同, 而按字面层号认同 (`ColimWIf §3`: 比余极限粗, 不需要路径数据), 律 `Glob` 每条只含一个种类, 没有 $R$ 这样的二元认同关系. 所以本篇的定理**不否定接口的任何一条律**; 它说明的是: 若改成沿映射认同且把更新律写在裸下标上, 墙是无条件的 WLPO, 而按字面层号认同把墙推到了更新的世界 `GW` 上 (入口 §3, 那里要外延才到 WLPO).
>
> **只否定什么.** 只否定 `Sel.UpdR` 在裸下标上对 $R = \lhd$ 成立. 不否定可入下标上的同一形状 (反模型), 不否定接口.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimWNegDraft where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; cmpF; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy

WLPO : Set
WLPO = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (∀ n → α n ≡ false)

-- 一般形: 认同关系 R 写在裸下标上, 更新在 R 处改, 在 ¬R 处不改 ⇒ R 的弱判定
module Sel (I : Set) (R : I → I → Set) (W : Set) (rd : I → W → Bool) (w₀ : W)
           (r₀ : ∀ i → rd i w₀ ≡ true) where
  record UpdR : Set where
    field
      raise : I → W → W
      atR   : ∀ i₀ i → R i₀ i → rd i (raise i₀ w₀) ≡ false
      offR  : ∀ i₀ i → ¬ R i₀ i → rd i (raise i₀ w₀) ≡ rd i w₀
  open UpdR public

  t≢f : true ≡ false → ⊥
  t≢f ()

  module _ (U : UpdR) where
    look : ∀ i₀ i (r : Bool) → rd i (raise U i₀ w₀) ≡ r → ¬ R i₀ i ⊎ ¬ ¬ R i₀ i
    look i₀ i true e = inj₁ (λ q → t≢f (trans (sym e) (atR U i₀ i q)))
    look i₀ i false e = inj₂ (λ nq → t≢f (trans (sym (r₀ i)) (trans (sym (offR U i₀ i nq)) e)))

    updR→wdec : ∀ i₀ i → ¬ R i₀ i ⊎ ¬ ¬ R i₀ i
    updR→wdec i₀ i = look i₀ i (rd i (raise U i₀ w₀)) refl

-- 禁忌实例: A 里 1 ⊲ aα 的弱判定就是 WLPO
or : (ℕ → Bool) → ℕ → Bool
or α zero = α zero
or α (suc n) = or α n ∨ α (suc n)

pick : Bool → A
pick true = asuc azero
pick false = azero

fα : (ℕ → Bool) → ℕ → A
fα α n = pick (or α n)

aα : (ℕ → Bool) → A
aα α = alim (fα α)

step-or : ∀ α n → pick (or α n) ⊲ pick (or α (suc n))
step-or α n with or α n
... | true = C.self
... | false = C.z⊲ _

lg-pick : ∀ b → Lg (pick b)
lg-pick true = tt
lg-pick false = tt

Lg-aα : ∀ α → Lg (aα α)
Lg-aα α = step-or α , (λ n → lg-pick (or α n))

one : A
one = asuc azero

one⋪z : ¬ (one ⊲ azero)
one⋪z ()

-- or α n ≡ true 给出某个 α k ≡ true
or-wit : ∀ α n → or α n ≡ true → Σ ℕ (λ k → α k ≡ true)
or-wit α zero e = zero , e
or-wit α (suc n) e with or α n in eq
... | true = or-wit α n eq
... | false = suc n , e

or-in : ∀ α k → α k ≡ true → or α k ≡ true
or-in α zero e = e
or-in α (suc k) e with or α k
... | true = refl
... | false = e

pick-one : ∀ b → one ⊲ pick b → b ≡ true
pick-one true _ = refl
pick-one false ()

one⊲→∃ : ∀ α → one ⊲ aα α → Σ ℕ (λ k → α k ≡ true)
one⊲→∃ α (C.lim n p) = or-wit α n (pick-one (or α n) p)

∃→one⊲ : ∀ α k → α k ≡ true → one ⊲ aα α
∃→one⊲ α k e = C.lim k (subst (λ b → one ⊲ pick b) (sym (or-in α k e)) C.self)

f≢t : false ≡ true → ⊥
f≢t ()

wdec⊲→WLPO : (∀ a → ¬ (one ⊲ a) ⊎ ¬ ¬ (one ⊲ a)) → WLPO
wdec⊲→WLPO d α with d (aα α)
... | inj₁ n = inj₁ (λ k → helper k (α k) refl)
  where
  helper : ∀ k b → α k ≡ b → α k ≡ false
  helper k true e = ⊥-elim (n (∃→one⊲ α k e))
  helper k false e = e
... | inj₂ nn = inj₂ (λ allf → nn (λ p → let (k , e) = one⊲→∃ α p in f≢t (trans (sym (allf k)) e)))
```

## 可入时: 同一合法界之下 ⊲ 可判定 (A)

```agda
infix 4 _<ᴬ_
data _<ᴬ_ : A → A → Set where
  <s₀ : ∀ {b} → b <ᴬ asuc b
  <s  : ∀ {a b} → a <ᴬ b → a <ᴬ asuc b
  <l₀ : ∀ {f} n → f n <ᴬ alim f
  <l  : ∀ {a f} n → a <ᴬ f n → a <ᴬ alim f

data AccA (x : A) : Set where
  acc : (∀ {y} → y <ᴬ x → AccA y) → AccA x

downA : ∀ {x y} → AccA x → y <ᴬ x → AccA y
downA (acc r) p = r p

wfA : ∀ x → AccA x
wfA azero = acc (λ ())
wfA (asuc x) = acc (λ { <s₀ → wfA x ; (<s p) → downA (wfA x) p })
wfA (alim f) = acc (λ { (<l₀ n) → wfA (f n) ; (<l n p) → downA (wfA (f n)) p })

irrA : ∀ {x} → AccA x → ¬ (x <ᴬ x)
irrA (acc r) p = irrA (r p) p

toLtA : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (a <ᴬ b)
toLtA C.self = inj₁ refl
toLtA (C.suc p) with toLtA p
... | inj₁ refl = inj₂ <s₀
... | inj₂ q = inj₂ (<s q)
toLtA (C.lim n p) with toLtA p
... | inj₁ refl = inj₂ (<l₀ n)
... | inj₂ q = inj₂ (<l n q)

<⊲-tr : ∀ {a b c} → a <ᴬ b → b ⊲ c → a <ᴬ c
<⊲-tr q C.self = q
<⊲-tr q (C.suc p) = <s (<⊲-tr q p)
<⊲-tr q (C.lim n p) = <l n (<⊲-tr q p)

-- c <ᴬ c₀ 时 c₀ 不是 c 的第一位置
lt→⋪ : ∀ {c c₀} → c <ᴬ c₀ → ¬ (c₀ ⊲ c)
lt→⋪ {c} q p = irrA (wfA c) (<⊲-tr q p)

adm-dec⊲ : ∀ {c₀ c a} → c₀ ⊲ a → c ⊲ a → Lg a → (c₀ ⊲ c) ⊎ ¬ (c₀ ⊲ c)
adm-dec⊲ p₀ p la with cmpF p₀ p la
... | inj₂ r = inj₁ r
... | inj₁ r with toLtA r
...   | inj₁ refl = inj₁ C.self
...   | inj₂ q = inj₂ (lt→⋪ q)
```

反模型: 下标限制在合法界 $a$ 之下 (带证据), 同样的两条律可满足.

```agda
module AdmModel (a : A) (la : Lg a) where
  I : Set
  I = Σ A (λ c → c ⊲ a)

  R : I → I → Set
  R (c₀ , _) (c , _) = c₀ ⊲ c

  W : Set
  W = I → Bool

  rd : I → W → Bool
  rd i w = w i

  w₀ : W
  w₀ _ = true

  sel : ∀ {c₀ c : A} → (c₀ ⊲ c) ⊎ ¬ (c₀ ⊲ c) → Bool → Bool
  sel (inj₁ _) b = false
  sel (inj₂ _) b = b

  raiseA : I → W → W
  raiseA (c₀ , p₀) w (c , p) = sel (adm-dec⊲ p₀ p la) (w (c , p))

  atA : ∀ i₀ i → R i₀ i → rd i (raiseA i₀ w₀) ≡ false
  atA (c₀ , p₀) (c , p) q with adm-dec⊲ p₀ p la
  ... | inj₁ _ = refl
  ... | inj₂ nq = ⊥-elim (nq q)

  offA : ∀ i₀ i → ¬ R i₀ i → rd i (raiseA i₀ w₀) ≡ rd i w₀
  offA (c₀ , p₀) (c , p) nq with adm-dec⊲ p₀ p la
  ... | inj₁ q = ⊥-elim (nq q)
  ... | inj₂ _ = refl

  model : Sel.UpdR I R W rd w₀ (λ _ → refl)
  model = record { raise = raiseA ; atR = atA ; offR = offA }
```

## 高度上的禁忌实例: 任一种类结构, 任一世界

```agda
module HTab {T : KS} (w : Wd T) where
  pickH : Bool → HB T
  pickH true = hs hz
  pickH false = hz

  hα : (ℕ → Bool) → HB T
  hα α = hl (λ n → pickH (or α n))

  stepH : ∀ α n {u} → pickH (or α n) ⊲[ u ] pickH (or α (suc n))
  stepH α n with or α n
  ... | true = hself
  ... | false = z⊲ᴮ _

  Lg-hα : ∀ α → LgB (hα α)
  Lg-hα α = (λ n → stepH α n) , (λ n → lgp (or α n))
    where
    lgp : ∀ b → LgB (pickH b)
    lgp true = tt
    lgp false = tt

  oneH : HB T
  oneH = hs hz

  pickH-one : ∀ b → oneH ⊲[ w ] pickH b → b ≡ true
  pickH-one true _ = refl
  pickH-one false ()

  oneH→∃ : ∀ α → oneH ⊲[ w ] hα α → Σ ℕ (λ k → α k ≡ true)
  oneH→∃ α (hlim n p) = or-wit α n (pickH-one (or α n) p)

  ∃→oneH : ∀ α k → α k ≡ true → oneH ⊲[ w ] hα α
  ∃→oneH α k e = hlim k (subst (λ b → oneH ⊲[ w ] pickH b) (sym (or-in α k e)) hself)

  wdecH→WLPO : (∀ y → ¬ (oneH ⊲[ w ] y) ⊎ ¬ ¬ (oneH ⊲[ w ] y)) → WLPO
  wdecH→WLPO d α with d (hα α)
  ... | inj₁ n = inj₁ (λ k → helper k (α k) refl)
    where
    helper : ∀ k b → α k ≡ b → α k ≡ false
    helper k true e = ⊥-elim (n (∃→oneH α k e))
    helper k false e = e
  ... | inj₂ nn = inj₂ (λ allf → nn (λ p → let (k , e) = oneH→∃ α p in f≢t (trans (sym (allf k)) e)))
```
