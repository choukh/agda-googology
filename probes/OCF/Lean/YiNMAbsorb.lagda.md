# 吸收引理的反例: 被吸收的上下文改变走链一支的值

> 判决: 编译定理, 条件 (排中律作模块参数), 验收侧. 树 `T* = ε₀ + Ω₁` (左项是 ψ₀(Ω₁) 的折叠输出 `E`, 右项是 `Ωt one`) 与 `Ωt one` 严格值相同 (`absorbed`), 朝第 0 层折 `T*` 的输出却严格高于折 `Ωt one` 的输出 (`absorb-fails`).
> 推论 `B-false`: 若 `T*` 名为 Ω₁, 则 `YiNMName.BRow` 在 `T*` 上不成立 (底族的前提已证, `ctx₀`). "`T*` 名为 Ω₁" 只有纸面依据 (结点一行只要求夹逼, 嵌入一行不限制左项), 所以读作命名关系太宽, 不读作路线被否定.
> 不否定带附加条件的吸收引理 (上下文 K 的 ψ_u(K) 是标准形); 这里的上下文 ε₀ 不满足它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNMAbsorb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Induction.WellFounded using (Acc; acc)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRVLevel
open import OCF.Lean.YiNMSharp
open import OCF.Lean.YiNMTerm
open import OCF.Lean.YiNMName
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanTrian as ET
open EB using (NF)

one : L
one = sc zero

o₁ : Ok one
o₁ = tt , λ _ → tt

module Absorb (lem : LEM) where
  open Sharp lem
  open Term lem
  open Name lem
```

## 第 0 层的折叠不降严格值

第 0 层的树只有零, 后继, ℕ 极限三种; 折叠把后继变成 ·ω, 所以输出的严格值不低于输入 (底任意).

```agda
  ge0 : (B : Base♯) (β : Tr⁺ zero) (x : Tr zero) → ↑ zero x ≼ᴸ ↑ zero (proj₁ (ψ♯ zero tt B zero tt β x))
  ge0 B β zero          = z≼
  ge0 B β (suc x)       = n≼ (λ _ → zero , ge0 B β x)
  ge0 B β (lim f a)     = n≼ (λ n → n , ge0 B β (f n))
  ge0 B β (Ω () g)
  ge0 B β (up x () y e)
```

## 两棵树

`E⁺` 是 ψ₀(Ω₁) (朝第 0 层折 `Ωt one`, 默认底). `E′` 把它嵌进 `one` 层, `T*` 是树加法 `E′ + Ωt one`, 即结点 c ↦ ε₀ + (c + 1). `out` 是朝第 0 层折 `T*`.

```agda
  E⁺ : Tr⁺ zero
  E⁺ = ψ♯ one o₁ B♯ zero tt (Ωt zero) (proj₁ (Ωt one))

  E′ : Tr one
  E′ = up zero tt (proj₁ E⁺) (proj₂ E⁺)

  T* : Tr one
  T* = E′ + proj₁ (Ωt one)

  out : Tr⁺ zero
  out = ψ♯ one o₁ B♯ zero tt (Ωt zero) T*
```

上下文被吸收: 两棵树的严格值相同 (分支 c 对上分支 `E + c`).

```agda
  absorbed : ↑ one T* ≈ᴸ ↑ one (proj₁ (Ωt one))
  absorbed =
    n≼ (λ c → (proj₁ E⁺ + c) , n≼ (λ _ → tt ,
      ≼ᴸ-trans (proj₁ (⊕-assoc zero (↑ zero (proj₁ E⁺)) (↑ zero c)))
               (⊕-monoʳ zero (proj₂ (↑-+ zero (proj₁ E⁺) c))))) ,
    n≼ (λ c → c , ⊕-monoˡ {zero} {zero ⊕ ↑ zero (proj₁ E⁺)} z≼ (↑ zero (suc c)))
```

折叠的值不同: `out` 走链, 链的第 0 项是 (朝第 0 层折 ε₀)·ω, 它已经严格高于 ε₀.

```agda
  absorb-fails : ↑ zero (proj₁ E⁺) ≺ᴸ ↑ zero (proj₁ out)
  absorb-fails = zero , up≼ zero (ge0 _ (Ωt zero) (proj₁ E⁺))

  ¬same : ↑ zero (proj₁ out) ≼ᴸ ↑ zero (proj₁ E⁺) → ⊥
  ¬same d = ≺-irrefl (↑ zero (proj₁ E⁺)) (≺≼ (↑ zero (proj₁ out)) (↑ zero (proj₁ E⁺)) absorb-fails d)
```

## 对 B 的后果

记号: Ω₁ = ψ₁(0), ψ₀(Ω₁). 项模型里 ψ₀(Ω₁) 的严格值就是 `E⁺` 的 (`model-E`, 定义展开). B 在 `T*` 上取默认底, 目标第 0 层, 上下文 0, 底族的域取 `D₀` (只有第 0 层, 这次折叠只在那里问底族); 这时底族的前提是定理 (`ctx₀`: 值为零的层号只能名为 0, 用非空项的层号非零 `lev-nz`). 结论的 (V) 说 `out` 与 `E⁺` 同值, 与 `¬same` 矛盾. 剩下的前提只有 "`T*` 名为 Ω₁".

```agda
  Ω₁ᵗ ψ₀Ω₁ : E.T
  Ω₁ᵗ  = E.ψ (E.𝟏 ∷ []) [] ∷ []
  ψ₀Ω₁ = E.ψ [] Ω₁ᵗ ∷ []

  model-E : sv ⟦ ψ₀Ω₁ ⟧ ≡ ↑ zero (proj₁ E⁺)
  model-E = refl

  nf𝟏 : NF (E.𝟏 ∷ [])
  nf𝟏 = EB.nf-ψ EB.n[] EB.n[] EB.GB[]

  nfψ₀Ω₁ : NF ψ₀Ω₁
  nfψ₀Ω₁ = EB.nf-ψ EB.n[] (EB.nf-Ω nf𝟏) gb
    where
    gb : EB.GB [] Ω₁ᵗ Ω₁ᵗ
    gb (EB.gp (EB.gh _))                   = E.[]<
    gb (EB.gp (EB.gw _ (EB.gp (EB.gh _)))) = E.[]<
    gb (EB.gp (EB.gw _ (EB.gp (EB.gw _ ()))))
    gb (EB.gp (EB.gw _ (EB.gp (EB.gc _ ()))))
    gb (EB.gp (EB.gw _ (EB.gtl ())))
    gb (EB.gp (EB.gc _ ()))
    gb (EB.gtl ())

  named-𝟏 : (ac : Acc _≺ᴸ_ zero) → Nmd zero tt ac (suc zero) (E.𝟏 ∷ [])
  named-𝟏 ac = nf𝟏 , ≈ᴸ-refl (sc zero) , refl , EB.n[] , ≈ᴸ-refl zero , refl

  sv-nz : ∀ x xs → zero ≺ᴸ sv ⟦ x ∷ xs ⟧
  sv-nz (E.ψ u a) xs = go (Dk (lv ⟦ xs ⟧) (lv ⟦ E.ψ u a ⟧ᴾ))
    where
    m₁ m₂ : M
    m₁ = ⟦ E.ψ u a ⟧ᴾ
    m₂ = ⟦ xs ⟧
    nz : lv m₁ ⊢ zero ◃ tr m₁
    nz = proj₂ (ψ♯ (lv ⟦ a ⟧) (ok ⟦ a ⟧) B♯ (rd ⟦ u ⟧) (rdOk ⟦ u ⟧) (Ωt (rd ⟦ u ⟧)) (tr ⟦ a ⟧))
    go : (d : (lv m₂ ≼ᴸ lv m₁) ⊎ (lv m₁ ≺ᴸ lv m₂)) → zero ≺ᴸ sv (comb′ m₁ m₂ d)
    go (inj₁ le) =
      ≺≼ {a = zero} (↑ (lv m₁) (tr m₁)) (↑ (lv m₁) (tr m₁ + t₂)) (↑-strict (lv m₁) nz)
         (≼ᴸ-trans (≼⊕ˡ (↑ (lv m₁) (tr m₁)) (↑ (lv m₁) t₂)) (proj₂ (↑-+ (lv m₁) (tr m₁) t₂)))
      where
      t₂ : Tr (lv m₁)
      t₂ = τ (lv m₂) (lv m₁) (ok m₂) (ok m₁) (wfL (lv m₂)) le (tr m₂)
    go (inj₂ lt) =
      ≺≼ {a = zero} (↑ (lv m₂) t₁) (↑ (lv m₂) (t₁ + tr m₂))
         (↑-strict (lv m₂) (τm (lv m₁) (lv m₂) (ok m₁) (ok m₂) (wfL (lv m₁)) (≺→≼ (lv m₂) lt) nz))
         (≼ᴸ-trans (≼⊕ˡ (↑ (lv m₂) t₁) (↑ (lv m₂) (tr m₂))) (proj₂ (↑-+ (lv m₂) t₁ (tr m₂))))
      where
      t₁ : Tr (lv m₂)
      t₁ = τ (lv m₁) (lv m₂) (ok m₁) (ok m₂) (wfL (lv m₁)) (≺→≼ (lv m₂) lt) (tr m₁)

  lev-nz : ∀ x xs → zero ≺ᴸ lev (x ∷ xs)
  lev-nz x xs = ≺≼ {a = zero} (sv ⟦ x ∷ xs ⟧) (lev (x ∷ xs)) (sv-nz x xs) (≼⊕ʳ (lv ⟦ x ∷ xs ⟧) (sv ⟦ x ∷ xs ⟧))

  D₀ : L → Set
  D₀ i = i ≡ zero

  ctx₀ : CtxN D₀ B♯ [] []
  ctx₀ i oi aci []       refl lvn le = named-𝟏 aci
  ctx₀ i oi aci (x ∷ xs) refl ((_ , d) , _) le = ⊥-elim (≺≼ {a = zero} (lev (x ∷ xs)) zero (lev-nz x xs) d)

  B-false : Nmd one o₁ (wfL one) T* Ω₁ᵗ → BRow D₀ one o₁ T* → ⊥
  B-false nT b =
    ¬same (proj₁ (proj₁ (proj₂
      (b (wfL one) B♯ zero tt (wfL zero) (Ωt zero) Ω₁ᵗ [] [] tt nT (≈ᴸ-refl zero , tt) ctx₀ (named-𝟏 (wfL zero)) nfψ₀Ω₁))))
```

## 修正的方向: 夹逼换成 Buchholz 的 ◁

记号侧的 `Trian z b a` (b ◁_z a: b < a, 且 b 的 G 集被区间 (b, a] 里每一项的 G 集, 0 与 z 的 G 集支配) 是基本列封闭性证明用的关系. 被吸收的左项 ε₀ = ψ₀(Ω₁) 对 Ω₁ 不满足它 (`¬◁`): G₀(ε₀) 里有 Ω₁, 而 G₀(Ω₁) 只有 0. 所以把命名关系里的 "低于 a" 换成 ◁, 这个反例就不在域内.

```agda
  ¬◁ : ET.Trian [] ψ₀Ω₁ Ω₁ᵗ → ⊥
  ¬◁ t = bad (ET.tb t [] Ω₁ᵗ (E.hd< (E.lv< E.[]<)) (inj₂ refl) (EB.gp (EB.gh (inj₂ refl))))
    where
    no : ∀ {y} → EB.InG [] y Ω₁ᵗ → Ω₁ᵗ EB.≤ᵀ y → ⊥
    no (EB.gp (EB.gh _)) (inj₁ ())
    no (EB.gp (EB.gh _)) (inj₂ ())
    no (EB.gp (EB.gw _ (EB.gp (EB.gh _)))) (inj₁ ())
    no (EB.gp (EB.gw _ (EB.gp (EB.gh _)))) (inj₂ ())
    no (EB.gp (EB.gw _ (EB.gp (EB.gw _ ())))) l
    no (EB.gp (EB.gw _ (EB.gp (EB.gc _ ())))) l
    no (EB.gp (EB.gw _ (EB.gtl ()))) l
    no (EB.gp (EB.gc _ ())) l
    no (EB.gtl ()) l
    bad : ET.Dom [] [] Ω₁ᵗ Ω₁ᵗ → ⊥
    bad (inj₁ (y , i , l))        = no i l
    bad (inj₂ (inj₁ ()))
    bad (inj₂ (inj₂ (y , () , l)))
```
