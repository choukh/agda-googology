# 安全种类排除部分合法原始坐标

对定稿 `FrozenOmegaIf.SafeTw` 的实际首个 Ω 层做检查。
只否定 erase 意义下的结构无损全嵌入，不声称排除值相等的换根编码。
本例与旧 `NegThirdIf.no-wash` 同源，但这里直接针对新类型给出
合法闭坐标及无原像证明，不再声称一般的洗法壁垒是新发现。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenOmegaNegEmbed where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.NegRecBPre using (Ωˢ; Lg-Ωˢ)

U = step S⊥
w : Wd U
w = tt , hz
m : HB U
m = Ωˢ
legal-world : LgW U w
legal-world = tt , tt
legal-level : LgB m
legal-level = Lg-Ωˢ

κ : K (Tw U m)
κ = hs hz , inj₂ tt

no-position : Pos U w m κ → ⊥
no-position (() , p)

coordinate : HB (Tw U m)
coordinate = hΩ κ (λ _ → hz)

legal-coordinate : LgB coordinate
legal-coordinate = (λ lw b b′ p → hself) , (λ lw b → tt)

RootPosition : HB (Tw U m) → Set
RootPosition (hΩ k g) = Pos U w m k
RootPosition _ = ⊤

root-safe : (a : HB (SafeTw U w m)) → RootPosition (erase a)
root-safe hz = tt
root-safe (hs a) = tt
root-safe (hl f) = tt
root-safe (hΩ (k , p) g) = p

no-preimage : (a : HB (SafeTw U w m)) → erase a ≡ coordinate → ⊥
no-preimage a eq = no-position (subst RootPosition eq (root-safe a))

no-legal-section :
  (embed : (c : HB (Tw U m)) → LgB c → HB (SafeTw U w m)) →
  (∀ c (lc : LgB c) → erase (embed c lc) ≡ c) → ⊥
no-legal-section embed exact = no-preimage
  (embed coordinate legal-coordinate) (exact coordinate legal-coordinate)
```

可满足前提：层 `m` 是实际的 `Ωˢ`，合法；世界 `w` 合法；被排除的
坐标 `coordinate` 也合法，而非故意用不合法树。失败发生在其根种类
通过 Ω 分量 1，而固定外层界为 0。故只证明安全化不是所有合法原始
坐标的结构重编码。尚未证明任何值损失，也未否定更大世界或只在实际
回灌坐标上成立的嵌入。
翻译账：未改树、折叠或合法性；新增验收性质与否定。

## 原地板分支 up c 也无安全原像

这把上述坐标放到后继层地板的实际分支形状中，而非仅讨论恒等嵌入。

```agda
RootPosition⁺ : HB (Tw U (hs m)) → Set
RootPosition⁺ (hΩ k g) = Pos U w (hs m) k
RootPosition⁺ _ = ⊤

root-safe⁺ : (a : HB (SafeTw U w (hs m))) → RootPosition⁺ (erase a)
root-safe⁺ hz = tt
root-safe⁺ (hs a) = tt
root-safe⁺ (hl f) = tt
root-safe⁺ (hΩ (k , p) g) = p

no-floor-branch : (a : HB (SafeTw U w (hs m))) → erase a ≡ up coordinate → ⊥
no-floor-branch a eq = no-position (subst RootPosition⁺ eq (root-safe⁺ a))

no-full-floor :
  (floor-branch : (c : HB (Tw U m)) → LgB c → HB (SafeTw U w (hs m))) →
  (∀ c (lc : LgB c) → erase (floor-branch c lc) ≡ up c) → ⊥
no-full-floor g exact = no-floor-branch
  (g coordinate legal-coordinate) (exact coordinate legal-coordinate)
```

根的不可入证据在 `up` 后定义地不变；这里没有否定改变基本列但保持值
的地板，也没有否定把当前世界扩大后的地板。

## 任意固定界：原地板仍不能在全部合法坐标上原样表示

此推广不是从零界特例推断：对每个固定界 B，重新选取 B+1 分量，
用已有可数树良基性排除 B+1 为 B 的第一位置。

```agda
open import OCF.Lean.NegFold1Sup using (¬hs⊲)

module Fixed (B : Cd) (lB : LgB B) where
  wB : Wd U
  wB = tt , B
  lwB : LgW U wB
  lwB = tt , lB

  κB : K (Tw U m)
  κB = hs B , inj₂ tt
  absent : Pos U wB m κB → ⊥
  absent (p , _) = ¬hs⊲ B p

  cB : HB (Tw U m)
  cB = hΩ κB (λ _ → hz)
  lcB : LgB cB
  lcB = (λ lw p q r → hself) , (λ lw p → tt)

  RP : HB (Tw U (hs m)) → Set
  RP (hΩ k g) = Pos U wB (hs m) k
  RP _ = ⊤
  safe : (a : HB (SafeTw U wB (hs m))) → RP (erase a)
  safe hz = tt
  safe (hs a) = tt
  safe (hl f) = tt
  safe (hΩ (k , p) g) = p

  no-branch : (a : HB (SafeTw U wB (hs m))) → erase a ≡ up cB → ⊥
  no-branch a eq = absent (subst RP eq (safe a))

  no-fixed-floor :
    (g : (c : HB (Tw U m)) → LgB c → HB (SafeTw U wB (hs m))) →
    (∀ c (lc : LgB c) → erase (g c lc) ≡ up c) → ⊥
  no-fixed-floor g exact = no-branch (g cB lcB) (exact cB lcB)
```

合法界 B 任意，世界合法证书为 `lwB`；被排除的合法坐标为 `cB`。
结论仍只针对同一个固定世界里对全部合法原始坐标的结构等式，
不否定世界随分支增长、不否定受限回灌族、不否定按值改写。
