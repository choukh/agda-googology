# 遗传封闭关系的参数搬运
> 验收文件（读记号）。`mapᴴ` 对槽位分支关系逆向、孩子关系与余尾读法正向搬运。
> 证明按 `YiHCRel.Mᴴ` 的七个构造子归纳；`mΩ` 的分支证据必须逆向输入。
> 本文件不声称整个有限关系族具有单向包含；有限实例见 `YiFMFin`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFMMap where
open import OCF.Lean.YiRWBlock using (Sg; P; B; C; D)
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc)
import OCF.Align.EboLeanDef as E

mapᴴ : ∀ {S : Sg}
  {Low₀ Low₁ : (p : P S) → E.T → B S p → Set}
  {Ch₀ Ch₁ : (c : C S) → E.T → D S c → Set}
  {Nu₀ Nu₁ : P S → E.T → Set}
  → (∀ p {η c} → Low₁ p η c → Low₀ p η c)
  → (∀ c {s y} → Ch₀ c s y → Ch₁ c s y)
  → (∀ p {ν} → Nu₀ p ν → Nu₁ p ν)
  → ∀ {t x} → Mᴴ S Low₀ Ch₀ Nu₀ t x → Mᴴ S Low₁ Ch₁ Nu₁ t x
mapᴴ low ch nu mz = mz
mapᴴ low ch nu (m1 e r) = m1 e (mapᴴ low ch nu r)
mapᴴ low ch nu (mL e h) = mL e (λ n → mapᴴ low ch nu (h n))
mapᴴ low ch nu (mΩ {p = p} e q h) =
  mΩ e (nu p q) (λ η c l → mapᴴ low ch nu (h η c (low p l)))
mapᴴ low ch nu (mU {c = c} m d) = mU (mapᴴ low ch nu m) (ch c d)
mapᴴ low ch nu (mw m d) = mw (mapᴴ low ch nu m) d
mapᴴ low ch nu (mc le m) = mc le (mapᴴ low ch nu m)
```
