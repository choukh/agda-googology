# 值支配 `Tp` 的 Ω 结点: 归结到分支类型之间的满射

> 判决: 编译定理, 无前提. 层号对 (a, a′) 若满足 `PS` (a 的每个槽位在 a′ 里有一个槽位, 其分支树类型满射到 a 的分支树类型), 则 a 的每棵树被 a′ 的某棵树按值支配 (`TpS`); 不用 `Ok`, 也不用值序. 槽位层号有语法路径 (`PP`) 时满射取恒等 (`PP→PS`).
> 所以 `YiRVOmega.Reg` 归结为对一切合法、值有序的层号对给出 `PS` (`regPS`). 例: `sc zero` 与 `nd sL (λ _ → zero)` 双向有 `PP`; 合法同值对 `sc (sc zero)`, `sc (nd sL (λ _ → zero))` 没有同层号槽位 (`¬PE₂`), 它的满射在 `YiQNCollapse` (条件: 函数外延).
> 不否定 `Tp` 或 `Reg`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQNReg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst-sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (Ok; _≤_; self; inc; inu; ink; _∙_; posW⁼)
import OCF.Lean.YiVWVal as W
open W using (V; val; _≼_)
open import OCF.Lean.YiRVLevel using (_≼ᴸ_; z≼; n≼; sc)
open import OCF.Lean.YiRVOmega using (_⊙_; ≼s; F≼cum; ⊹-mono₂; Reg; Tp; tpR)
```

## 分支类型与槽位层号的树类型互换

`Br ℓ p` 逐层就是 `Tr (at ℓ p)`, `fromBr` 是恒等的逐层拼接; `toBr` 是反向, 两个方向互逆 (逐层 `refl`).

```agda
mutual
  toBr : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Tr (at ℓ p)
  toBr (nd s h)      (inj₂ (c , t)) z = toBr⁼ (h c) t z
  toBr (nd (sΩ k) h) (inj₁ t)       z = toBr⁼ k t z

  toBr⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Tr (proj₁ (sl⁼ a t))
  toBr⁼ a (inj₁ _) z = z
  toBr⁼ a (inj₂ p) z = toBr a p z

mutual
  ft : (ℓ : L) (p : Pos ℓ) (z : Br ℓ p) → fromBr ℓ p (toBr ℓ p z) ≡ z
  ft (nd s h)      (inj₂ (c , t)) z = ft⁼ (h c) t z
  ft (nd (sΩ k) h) (inj₁ t)       z = ft⁼ k t z

  ft⁼ : (a : L) (t : Pos⁼ a) (z : Br⁼ a t) → proj₂ (sl⁼ a t) (toBr⁼ a t z) ≡ z
  ft⁼ a (inj₁ _) z = refl
  ft⁼ a (inj₂ p) z = ft a p z

mutual
  tf : (ℓ : L) (p : Pos ℓ) (u : Tr (at ℓ p)) → toBr ℓ p (fromBr ℓ p u) ≡ u
  tf (nd s h)      (inj₂ (c , t)) u = tf⁼ (h c) t u
  tf (nd (sΩ k) h) (inj₁ t)       u = tf⁼ k t u

  tf⁼ : (a : L) (t : Pos⁼ a) (u : Tr (proj₁ (sl⁼ a t))) → toBr⁼ a t (proj₂ (sl⁼ a t) u) ≡ u
  tf⁼ a (inj₁ _) u = refl
  tf⁼ a (inj₂ p) u = tf a p u
```

## 满射条件 `PS` 推出值支配

```agda
Surj : Set → Set → Set
Surj B A = Σ (B → A) λ ρ → (z : A) → Σ B λ u → ρ u ≡ z

PS : L → L → Set
PS a a′ = (p : Pos a) → Σ (Pos a′) λ p′ → Surj (Tr (at a′ p′)) (Tr (at a p))

RegAt : L → L → Set
RegAt a a′ = (p : Pos a) (φ : Br a p → Tr a′) → Σ (Tr a′) λ x′ → (z : Br a p) → val a′ (φ z) ≼ val a′ x′

regS : ∀ {a a′} → PS a a′ → RegAt a a′
regS {a} {a′} ps p φ =
  Ω p′ (λ w → φ (fromBr a p (ρ (toBr a′ p′ w)))) , bound
  where
  p′ = proj₁ (ps p)
  ρ  = proj₁ (proj₂ (ps p))
  sj = proj₂ (proj₂ (ps p))
  bound : (z : Br a p) → val a′ (φ z) ≼ val a′ (Ω p′ (λ w → φ (fromBr a p (ρ (toBr a′ p′ w)))))
  bound z =
    let u = proj₁ (sj (toBr a p z))
        eq = trans (cong (λ t → fromBr a p (ρ t)) (tf a′ p′ u))
                   (trans (cong (fromBr a p) (proj₂ (sj (toBr a p z)))) (ft a p z))
    in W.≼Ω (fromBr a′ p′ u) (subst (λ t → val a′ (φ z) ≼ val a′ (φ t)) (sym eq) (W.≼-refl _))

PS-ch : ∀ {s h a′} (c : Ch s) → PS (nd s h) a′ → PS (h c) a′
PS-ch c ps p = ps (inj₂ (c , inj₂ p))

TpS : ∀ {a a′} → PS a a′ → (x : Tr a) → Σ (Tr a′) λ x′ → val a x ≼ val a′ x′
TpS ps zero    = zero , W.z≼
TpS ps (suc x) = suc (proj₁ (TpS ps x)) , W.s≼s (proj₂ (TpS ps x))
TpS {a} {a′} ps (lim f m) =
  let P = λ n → proj₁ (TpS ps (f n)) in
  lim (cum (λ n → suc (P n))) (λ n → +-mono (cum (λ i → suc (P i)) n) (z◃ (P (suc n)) ◃s)) ,
  W.l≼ (λ n → W.≼l n (proj₂ (TpS ps (f n)) ⊙ ≼s _ ⊙ F≼cum a′ (λ i → suc (P i)) n))
TpS ps (Ω p g) =
  let r = regS ps p (λ z → proj₁ (TpS ps (g z))) in
  proj₁ r , W.Ω≼ (λ z → proj₂ (TpS ps (g z)) ⊙ proj₂ r z)
TpS {nd s h} {a′} ps (up x c y e) =
  let X = TpS ps x
      Y = TpS (PS-ch c ps) y in
  proj₁ X + proj₁ Y ,
  (⊹-mono₂ (proj₂ X) (W.emb-≼ (nd s h) c (val (h c) y) ⊙ proj₂ Y) ⊙ proj₂ (W.val-+ (proj₁ X) (proj₁ Y)))
```

接口: 对一切合法、值有序的层号对给出 `PS`, 就有 `Reg`, 从而有 `Tp` (`YiRVOmega.tpR`).

```agda
regPS : (∀ {a a′} → Ok a → Ok a′ → a ≼ᴸ a′ → PS a a′) → Reg
regPS ps oa oa′ d = regS (ps oa oa′ d)

tpPS : (∀ {a a′} → Ok a → Ok a′ → a ≼ᴸ a′ → PS a a′) → Tp
tpPS ps = tpR (regPS ps)
```

## 同层号槽位与路径

槽位层号相等时满射取恒等 (`eqSurj`). 有语法路径 `b ≤ at a′ p″` 时, 沿路径往下走能在 a′ 里找到层号恰为 b 的槽位 (`reach`, `deep`).

```agda
eqSurj : ∀ {A B : L} → A ≡ B → Surj (Tr A) (Tr B)
eqSurj e = subst Tr e , λ z → subst Tr (sym e) z , subst-subst-sym e

PE : L → L → Set
PE a a′ = (p : Pos a) → Σ (Pos a′) λ p′ → at a′ p′ ≡ at a p

PE→PS : ∀ {a a′} → PE a a′ → PS a a′
PE→PS pe p = proj₁ (pe p) , eqSurj (proj₂ (pe p))

reach : ∀ {b ℓ} → b ≤ ℓ → Σ (Pos⁼ ℓ) λ t → proj₁ (sl⁼ ℓ t) ≡ b
reach self = inj₁ tt , refl
reach (inc c v) = inj₂ (inj₂ (c , proj₁ (reach v))) , proj₂ (reach v)
reach {ℓ = nd s h} (inu vs) = inj₂ (inj₂ (c₀ s , proj₁ (reach (vs (c₀ s))))) , proj₂ (reach (vs (c₀ s)))
reach (ink v) = inj₂ (inj₁ (proj₁ (reach v))) , proj₂ (reach v)

deep : ∀ {b} (ℓ : L) (p : Pos ℓ) → b ≤ at ℓ p → Σ (Pos ℓ) λ p′ → at ℓ p′ ≡ b
deep (nd s h)      (inj₂ (c , t)) v = inj₂ (c , proj₁ (reach (v ∙ posW⁼ (h c) t))) , proj₂ (reach (v ∙ posW⁼ (h c) t))
deep (nd (sΩ k) h) (inj₁ t)       v = inj₁ (proj₁ (reach (v ∙ posW⁼ k t))) , proj₂ (reach (v ∙ posW⁼ k t))

PP : L → L → Set
PP a a′ = (p : Pos a) → Σ (Pos a′) λ p′ → at a p ≤ at a′ p′

PP→PE : ∀ {a a′} → PP a a′ → PE a a′
PP→PE {a′ = a′} pp p = deep a′ (proj₁ (pp p)) (proj₂ (pp p))

PP→PS : ∀ {a a′} → PP a a′ → PS a a′
PP→PS pp = PE→PS (PP→PE pp)
```

## 例

`w₁ = nd sL (λ _ → zero)` 与 `sc zero` 同值异形, 两个方向都有同层号槽位, 所以值支配无前提成立.

```agda
w₁ : L
w₁ = nd sL (λ _ → zero)

pe₁ : PE (sc zero) w₁
pe₁ (inj₁ ())
pe₁ (inj₂ (tt , inj₁ tt)) = inj₂ (zero , inj₁ tt) , refl
pe₁ (inj₂ (tt , inj₂ ()))

pe₁′ : PE w₁ (sc zero)
pe₁′ (inj₁ ())
pe₁′ (inj₂ (n , inj₁ tt)) = inj₂ (tt , inj₁ tt) , refl
pe₁′ (inj₂ (n , inj₂ ()))

tp₁ : (x : Tr (sc zero)) → Σ (Tr w₁) λ x′ → val (sc zero) x ≼ val w₁ x′
tp₁ = TpS (PE→PS pe₁)

tp₁′ : (x : Tr w₁) → Σ (Tr (sc zero)) λ x′ → val w₁ x ≼ val (sc zero) x′
tp₁′ = TpS (PE→PS pe₁′)
```

上一层: `sc (sc zero)` 与 `sc w₁` 都合法且同值, 但前者的槽位层号 `sc zero` 不是后者任何槽位的层号, 同层号的办法到此为止.

```agda
ok₂ : Ok (sc (sc zero))
ok₂ = tt , λ _ → tt , λ _ → tt

ok₂′ : Ok (sc w₁)
ok₂′ = tt , λ _ → (λ n → self) , λ _ → tt

le₂ : sc (sc zero) ≼ᴸ sc w₁
le₂ = n≼ (λ _ → tt , n≼ (λ _ → zero , z≼))

le₂′ : sc w₁ ≼ᴸ sc (sc zero)
le₂′ = n≼ (λ _ → tt , n≼ (λ _ → tt , z≼))

¬PE₂ : PE (sc (sc zero)) (sc w₁) → ⊥
¬PE₂ pe with pe (inj₂ (tt , inj₁ tt))
... | inj₁ () , _
... | inj₂ (tt , inj₁ tt) , ()
... | inj₂ (tt , inj₂ (inj₁ ())) , _
... | inj₂ (tt , inj₂ (inj₂ (n , inj₁ tt))) , ()
... | inj₂ (tt , inj₂ (inj₂ (n , inj₂ ()))) , _
```
