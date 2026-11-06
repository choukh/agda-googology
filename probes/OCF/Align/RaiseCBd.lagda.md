# RaiseC (二): 带公共上界的升界算子 (构造), 与判定子项给出的 `RaiseA` (条件)

> 不含记号. 入口 [RaiseC](RaiseC.lagda.md).
>
> 1. **`Rᵇ` (构造, 无条件).** 律的定义域带字面公共上界 (手册 §3.1): $a\lhd\Lambda$, $v\lhd\Lambda$, $\Lambda$ 合法. 这时 `cmpF` 判定 $v\lhd a$ 或 $a\lhd v$, 取大的那一个. 三条律都成立, 而且 `R-hi` 不要前提 $a\lhd v$ (**`Rᵇ-hi`**). 值的定理: $R^b\in\{a,v\}$ (`Rᵇ-cases`), 是 $a,v$ 的字面最小公共上界 (`Rᵇ-least`), 仍在 $\Lambda$ 之下 (`Rᵇ-Λ`), 对 $v$ 单调 (`Rᵇ-mono`), 与上界的证据无关 (`Rᵇ-irr`, 用 `⊲-antisym`).
> 2. **`dec→Raise` (条件).** 若子项关系可判定, `RaiseA` 有实例: $R\,a\,v = v$ (若 $a\lhd v$) 否则 $a$. 前提**在 Agda 里不可得**: `CumUpClean.dec⊲→LPO` 证它推出 LPO. 所以这条只说明: 经典地 `RaiseA` 有实例, 否定一路不能证 `¬ RaiseA` 本身 (那会与 "排中律与 MLTT 相容" 冲突, 判断, 元层), 只能证 `RaiseA → 某个非构造原则`.
> 3. **`R⊵Rᵇ` (定理).** 对任一 `RaiseA` 与有界的输入, $R^b(a,v)\lhd R\,a\,v$: `Rᵇ` 是接口在有界输入上允许的最小值.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RaiseCBd where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Barrier using (LPO)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumUpClean using (dec⊲→LPO)
open import OCF.Align.RaiseIf using (RaiseA; R; R-lo)
open import OCF.Align.RaiseCBase using (⊲-antisym; R-cmp→in)
```

## §1 有界的升界算子

`pick` 只看 `cmpF` 的答案是哪一边, 不看证明本身; 值是 $a$ 或 $v$.

```agda
pick : ∀ {a v : A} → (v ⊲ a) ⊎ (a ⊲ v) → A
pick {a} (inj₁ _) = a
pick {v = v} (inj₂ _) = v

Rᵇ : ∀ {a v Λ} → a ⊲ Λ → v ⊲ Λ → Lg Λ → A
Rᵇ p q l = pick (cmpF p q l)

module _ {a v Λ : A} (p : a ⊲ Λ) (q : v ⊲ Λ) (l : Lg Λ) where
  -- 值: a 或 v, 带比较的方向
  Rᵇ-cases : (Rᵇ p q l ≡ a × v ⊲ a) ⊎ (Rᵇ p q l ≡ v × a ⊲ v)
  Rᵇ-cases with cmpF p q l
  ... | inj₁ va = inj₁ (refl , va)
  ... | inj₂ av = inj₂ (refl , av)

  Rᵇ-lo : a ⊲ Rᵇ p q l
  Rᵇ-lo with cmpF p q l
  ... | inj₁ _ = C.self
  ... | inj₂ av = av

  -- R-hi 不要前提 a ⊲ v
  Rᵇ-hi : v ⊲ Rᵇ p q l
  Rᵇ-hi with cmpF p q l
  ... | inj₁ va = va
  ... | inj₂ _ = C.self

  Rᵇ-Λ : Rᵇ p q l ⊲ Λ
  Rᵇ-Λ with cmpF p q l
  ... | inj₁ _ = p
  ... | inj₂ _ = q

  Rᵇ-lg : Lg (Rᵇ p q l)
  Rᵇ-lg = lg⊲ Rᵇ-Λ l

  -- 字面最小公共上界
  Rᵇ-least : ∀ {c} → a ⊲ c → v ⊲ c → Rᵇ p q l ⊲ c
  Rᵇ-least ac vc with cmpF p q l
  ... | inj₁ _ = ac
  ... | inj₂ _ = vc
```

**与证据无关.** 两组证据给出的值都是 $a$ 或 $v$; 若方向不同, 则 $a\lhd v$ 且 $v\lhd a$, 由反对称 $a\equiv v$.

```agda
Rᵇ-irr : ∀ {a v Λ Λ′} (p : a ⊲ Λ) (q : v ⊲ Λ) (l : Lg Λ) (p′ : a ⊲ Λ′) (q′ : v ⊲ Λ′) (l′ : Lg Λ′) →
         Rᵇ p q l ≡ Rᵇ p′ q′ l′
Rᵇ-irr p q l p′ q′ l′ with cmpF p q l | cmpF p′ q′ l′
... | inj₁ _ | inj₁ _ = refl
... | inj₂ _ | inj₂ _ = refl
... | inj₁ va | inj₂ av = ⊲-antisym av va
... | inj₂ av | inj₁ va = ⊲-antisym va av
```

**对 $v$ 单调.** $v\lhd v'$, 都在 $\Lambda$ 之下: $R^b(a,v)\lhd R^b(a,v')$ (用最小性).

```agda
Rᵇ-mono : ∀ {a v v′ Λ} (p : a ⊲ Λ) (q : v ⊲ Λ) (q′ : v′ ⊲ Λ) (l : Lg Λ) → v ⊲ v′ → Rᵇ p q l ⊲ Rᵇ p q′ l
Rᵇ-mono p q q′ l vv′ = Rᵇ-least p q l (Rᵇ-lo p q′ l) (⊲-tr vv′ (Rᵇ-hi p q′ l))

-- 对 a 也单调
Rᵇ-monoa : ∀ {a a′ v Λ} (p : a ⊲ Λ) (p′ : a′ ⊲ Λ) (q : v ⊲ Λ) (l : Lg Λ) → a ⊲ a′ → Rᵇ p q l ⊲ Rᵇ p′ q l
Rᵇ-monoa p p′ q l aa′ = Rᵇ-least p q l (⊲-tr aa′ (Rᵇ-lo p′ q l)) (Rᵇ-hi p′ q l)

-- 再升一次不动
Rᵇ-idem : ∀ {a v Λ} (p : a ⊲ Λ) (q : v ⊲ Λ) (l : Lg Λ) → Rᵇ (Rᵇ-Λ p q l) q l ≡ Rᵇ p q l
Rᵇ-idem p q l with cmpF (Rᵇ-Λ p q l) q l | Rᵇ-hi p q l
... | inj₁ _ | _ = refl
... | inj₂ c⊲v | v⊲c = sym (⊲-antisym c⊲v v⊲c)
```

## §2 判定子项给出 `RaiseA` (条件; 前提推出 LPO)

```agda
module _ (d : ∀ a v → Dec (a ⊲ v)) where
  Rd : A → A → A
  Rd a v with d a v
  ... | yes _ = v
  ... | no _ = a

  Rd-lo : ∀ a v → a ⊲ Rd a v
  Rd-lo a v with d a v
  ... | yes av = av
  ... | no _ = C.self

  Rd-hi : ∀ a v → a ⊲ v → v ⊲ Rd a v
  Rd-hi a v av with d a v
  ... | yes _ = C.self
  ... | no n = ⊥-elim (n av)

  Rd-lg : ∀ a v → Lg a → Lg v → Lg (Rd a v)
  Rd-lg a v la lv with d a v
  ... | yes _ = lv
  ... | no _ = la

  dec→Raise : RaiseA
  dec→Raise = record
    { R = Rd
    ; R-lo = λ {a} {v} _ _ → Rd-lo a v
    ; R-hi = λ {a} {v} _ _ → Rd-hi a v
    ; R-lg = λ {a} {v} → Rd-lg a v }

  -- 前提本身推出 LPO (CumUpClean)
  dec→LPO : LPO
  dec→LPO = dec⊲→LPO d
```

`dec→Raise` 的 `R-lo` 与 `R-lg` 不用合法前提; 有界版 `Rᵇ` 的 `cmpF` 要上界合法. 两者的值都在 $\{a, v\}$ 里 (判断: 这就是经典的 "取大"; `RaiseA` 的接口没有要求它, 只要求两个下界).

## §3 任一 `RaiseA` 在有界的输入上不低于 `Rᵇ`

有公共上界时 $a, v$ 可比, 所以任一 `RaiseA` 的输出同时含 $a$ 与 $v$ (`R-cmp→in`); 由最小性, `Rᵇ` 是它的字面第一位置. 所以 `Rᵇ` 是接口在有界输入上允许的最小值.

```agda
R⊵Rᵇ : ∀ (ρ : RaiseA) {a v Λ} (p : a ⊲ Λ) (q : v ⊲ Λ) (l : Lg Λ) → Rᵇ p q l ⊲ R ρ a v
R⊵Rᵇ ρ p q l = Rᵇ-least p q l (R-lo ρ la lv) (R-cmp→in ρ la lv (cmpF p q l))
  where
  la = lg⊲ p l
  lv = lg⊲ q l
```
