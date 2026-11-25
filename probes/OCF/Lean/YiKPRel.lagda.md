# 验收一侧: 塔第 1 项那一层 (`tw 1`) 上的关系, 折到第 0 层的保持 (对孩子族的接口)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 前提是接口 `Kid` (孩子层 `h₁ c` 上的关系 `Kd` 与它折到第 0 层的保持 `foldᶜ`); 实例在 [YiKPInst](YiKPInst.lagda.md).
> `M¹` 是 `YiHCRel.Mᴴ` 在 `Sig (tw 1)` 上的实例: 下标层槽位的分支关系是 `M⁰`, 孩子关系是 `Kd`, 孩子层里的槽位不许出现. `Fold.LF¹`: 折叠 (`YiRBSib.ψ`, 目标第 0 层, 路径是一致路径或经下标层) 把 `M¹ a x` 送到 `M⁰ (ψ₀(t₀ + a))`, 量化域是满足 `Sp` 的推导 (嵌入结点的左项推导是 `mz`). `leaf¹`: 带 `LeafC` 时 Ω 树对着 Ω_Ω.
> 不给出什么: 折到第 j ≥ 1 层 (路径必经指定孩子) 没有做; 左项非零的嵌入与孩子层槽位上的结点不在量化域内; 不涉及上界.
> 来源: `LF¹` 的 `mz`, `m1`, `mL`, `mw`, `mc` 各行与回灌链照 `YiHCLim.Lim.Fold.LFω`, `LFΩ-lim`, `chain` 搬来 (目标取第 0 层); 嵌入一行与 `nodeZ` 新写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKPRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (ψ-⊵)
open import OCF.Lean.YiRBCrit using (h₁)
open import OCF.Lean.YiKVRel using (_⊴_; ++[])
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc; M⁰; pos⁰; module G⁰)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; natT; ΩTower)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
```

## 接口

`tw 1 = nd (sΩ zero) h₁`. 孩子 c 上要的只是朝第 0 层的一条律: 路径在 `Pc c` 里 (含一致路径 `z≤` 与经下标层进孩子的 `self ∙ kh c`), 底满足 `GBc c` (对底逐点放大封闭), 起点对着 ψ₀(t₀). 前缀 t₀ 是接口的参数.

```agda
ℓ¹ : L
ℓ¹ = tw 1

ΩΩ : E.T
ΩΩ = E.Ωt (ΩTower 1)

record Kid (o : Ok ℓ¹) (r : Rb ℓ¹) (t₀ : E.T) : Set₁ where
  field
    Kd    : (c : Tr zero) → E.T → Tr (h₁ c) → Set
    GBc   : (c : Tr zero) → Base (h₁ c) → Set
    Pc    : (c : Tr zero) → zero ≤ h₁ c → Set
    pz    : ∀ c → Pc c (z≤ (h₁ c))
    pk    : ∀ c → Pc c (self ∙ proj₂ (proj₁ o) c)
    gb⊴   : ∀ c {B B′ : Base (h₁ c)} → GBc c B → (∀ i u → proj₁ (B i u) ⊴ proj₁ (B′ i u)) → GBc c B′
    foldᶜ : ∀ c (v : zero ≤ h₁ c) → Pc c v → (B : Base (h₁ c)) → GBc c B
          → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
          → ∀ {s y} → Kd c s y → M⁰ (ψᴺ 0 (t₀ ++ s)) (proj₁ (ψ (h₁ c) (proj₂ o c) (proj₂ r c) B zero v β y))
```

## 关系与量化域

`Nu¹`: 下标层槽位上参照项的余尾是 Ω₁ (`cΩ []`); 孩子层里的槽位取空, 所以推导里没有这种结点. `Sp m`: m 的每个嵌入结点 `mU m′ ch` 的左项推导 m′ 是 `mz` (左项的树任意, 参照取空).

```agda
module Top (o : Ok ℓ¹) (r : Rb ℓ¹) (t₀ : E.T) (K : Kid o r t₀) where
  open Kid K public

  Low¹ : (p : Pos ℓ¹) → E.T → Br ℓ¹ p → Set
  Low¹ (inj₁ (inj₁ tt)) = M⁰
  Low¹ (inj₁ (inj₂ ()))
  Low¹ (inj₂ _)         = λ _ _ → ⊥

  Nu¹ : Pos ℓ¹ → E.T → Set
  Nu¹ (inj₁ (inj₁ tt)) ν = ν ≡ []
  Nu¹ (inj₁ (inj₂ ()))
  Nu¹ (inj₂ _)         ν = ⊥

  M¹ : E.T → Tr ℓ¹ → Set
  M¹ = Mᴴ (Sig ℓ¹) Low¹ Kd Nu¹

  IsZ : ∀ {a x} → M¹ a x → Set
  IsZ mz = ⊤
  IsZ _  = ⊥

  isz : ∀ {a x} (m : M¹ a x) → IsZ m → a ≡ []
  isz mz         _ = refl
  isz (m1 _ _)   ()
  isz (mL _ _)   ()
  isz (mΩ _ _ _) ()
  isz (mU _ _)   ()
  isz (mw _ _)   ()
  isz (mc _ _)   ()

  Sp : ∀ {a x} → M¹ a x → Set
  Sp mz         = ⊤
  Sp (m1 _ m)   = Sp m
  Sp (mL _ h)   = ∀ n → Sp (h n)
  Sp (mΩ _ _ h) = ∀ η c l → Sp (h η c l)
  Sp (mU m _)   = IsZ m
  Sp (mw m _)   = Sp m
  Sp (mc _ m)   = Sp m
```

## 底的条件, 路径

底只在两处被读: 下标层槽位的回灌 (分量 `B zero (ink self)`), 与传给孩子 c 的底 (分量 `B i (inc c u)`).

```agda
  record GB¹ (B : Base ℓ¹) : Set where
    constructor mkGB¹
    field
      bK : M⁰ (ψᴺ 0 t₀) (proj₁ (B zero (ink self)))
      bC : ∀ c → GBc c (λ i u → B i (inc c u))
  open GB¹ public

  data Pw : zero ≤ ℓ¹ → Set where
    wu : Pw (inu (λ c → z≤ (h₁ c)))
    wi : Pw (ink self)

  nodeZ : ∀ {X : Set} {x₀ : X} (K′ : Keep zero X x₀) (Q : Tr⁺ zero → Set) (G : X → Tr⁺ zero) (s : X → X)
        → Q (limc⁺ (λ n → G (iter s x₀ n))) → Q (node⁺ K′ G s)
  nodeZ nothing         Q G s q = q
  nodeZ (just (() , _)) Q G s q
```

## 折到第 0 层

对推导归纳. 下标层槽位的结点朝第 0 层不保留 (`nodeZ`: 第 0 层没有槽位), 取回灌链; 链点满足分支关系 `M⁰` 由对较小推导的归纳假设给出 (`chain`). 嵌入结点落到孩子 c 的折叠, 用 `foldᶜ`; 孩子的底是左项 x 的折叠, 逐点不低于 B 的分量 (`gbx`).

```agda
  module Fold (B : Base ℓ¹) (gb : GB¹ B) where
    F : zero ≤ ℓ¹ → Tr⁺ zero → Tr ℓ¹ → Tr⁺ zero
    F w β x = ψ ℓ¹ o r B zero w β x

    feed : (Tr zero → Tr ℓ¹) → Tr zero → Tr zero
    feed g z = proj₁ (F (ink self) (B zero (ink self)) (g z))

    Fz : ∀ w (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β) → ∀ x → M⁰ (ψᴺ 0 t₀) (proj₁ (F w β x))
    Fz w β hβ x = G⁰.m-zl (λ y → proj₁ (F w β y)) (mono ℓ¹ o r B zero w β) hβ x

    gbx : ∀ x c → GBc c (λ i u → ψ ℓ¹ o r B i (inc c u) (B i (inc c u)) x)
    gbx x c = gb⊴ c (bC gb c) (λ i u → ψ-⊵ ℓ¹ o r B i (inc c u) (B i (inc c u)) x)

    LFU : ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
        → ∀ {s₁} (x : Tr ℓ¹) (c : Tr zero) (y : Tr (h₁ c)) (ey : h₁ c ⊢ zero ◃ y) → Kd c s₁ y
        → M⁰ (ψᴺ 0 (t₀ ++ s₁)) (proj₁ (F w β (up x c y ey)))
    LFU wu β hβ x c y ey ch =
      foldᶜ c (z≤ (h₁ c)) (pz c) _ (gbx x c) (F (inu (λ c → z≤ (h₁ c))) β x) (Fz _ β hβ x) ch
    LFU wi β hβ x c y ey ch =
      foldᶜ c (self ∙ proj₂ (proj₁ o) c) (pk c) _ (gbx x c) (F (ink self) β x) (Fz _ β hβ x) ch

    mutual
      LF¹ : ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
          → ∀ {a x} (m : M¹ a x) → Sp m → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (F w β x))
      LF¹ {w} pw β hβ (mz {x = x}) sp =
        ++[] (λ z → M⁰ (ψᴺ 0 z) (proj₁ (F w β x))) t₀ (Fz w β hβ x)
      LF¹ {w} pw β hβ (m1 {t = a} {x = x} e h) sp =
        G⁰.m-next (F w β x) (cofψ1 (natT 0) (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 (natT 0) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ (natT 0) z)) (pred++ t₀ a e)))
          (LF¹ pw β hβ h sp)
      LF¹ {w} pw β hβ (mL {t = a} {x = x} e h) sp =
        mL (cofψω (natT 0) (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → M⁰ z (proj₁ (F w β x)))
            (sym (trans (fsnψω (natT 0) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ 0) (fsn++ t₀ a k e))))
            (LF¹ pw β hβ (h k) (sp k)))
      LF¹ {w} pw β hβ (mΩ {t = a} {p = inj₁ (inj₁ tt)} {g = g} e refl h) sp =
        nodeZ (kp ℓ¹ o (inj₁ (inj₁ tt)) w) (λ Z → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ Z)) (λ z → F w β (g z)) (feed g)
          (mL (cofG (natT 0) (t₀ ++ a) refl (cof++Ω t₀ a e))
            (λ k → subst (λ z → M⁰ z (proj₁ (limc⁺ (λ k′ → F w β (g (iter (feed g) zero k′))))))
              (sym (trans (fsnG (natT 0) (t₀ ++ a) k refl (cof++Ω t₀ a e)) (cong (ψᴺ 0) (fsT++ t₀ a (γT (t₀ ++ a) [] k) e))))
              (G⁰.m-cum (λ k′ → F w β (g (iter (feed g) zero k′))) (suc k)
                (LF¹ pw β hβ (h (γT (t₀ ++ a) [] k) (iter (feed g) zero (suc k)) (chain e h sp k))
                     (sp (γT (t₀ ++ a) [] k) (iter (feed g) zero (suc k)) (chain e h sp k))))))
      LF¹ pw β hβ (mΩ {p = inj₁ (inj₂ ())} _ _ _) sp
      LF¹ pw β hβ (mΩ {p = inj₂ _} _ () _) sp
      LF¹ {w} pw β hβ (mU {s = s₁} {x = x} {c = c} {y = y} {e = ey} m ch) sp =
        subst (λ z → M⁰ (ψᴺ 0 (t₀ ++ (z ++ s₁))) (proj₁ (F w β (up x c y ey)))) (sym (isz m sp))
          (LFU pw β hβ x c y ey ch)
      LF¹ {w} pw β hβ (mw m d) sp = mw (LF¹ pw β hβ m sp) (mono ℓ¹ o r B zero w β d)
      LF¹ pw β hβ (mc le m) sp = mc (app≤ 0 t₀ le) (LF¹ pw β hβ m sp)

      chain : ∀ {a} {g : Tr zero → Tr ℓ¹} → cof a ≡ cΩ []
            → (h : ∀ η c → M⁰ η c → M¹ (fsT a η) (g c)) → (∀ η c l → Sp (h η c l))
            → ∀ k → M⁰ (γT (t₀ ++ a) [] k) (iter (feed g) zero (suc k))
      chain {g = g} e h sp zero = pos⁰ _ (proj₂ (F (ink self) (B zero (ink self)) (g zero)))
      chain {a} {g} e h sp (suc k) =
        subst (λ z → M⁰ (ψᴺ 0 z) (feed g (iter (feed g) zero (suc k)))) (sym (fsT++ t₀ a (γT (t₀ ++ a) [] k) e))
          (LF¹ wi (B zero (ink self)) (bK gb) (h (γT (t₀ ++ a) [] k) (iter (feed g) zero (suc k)) (chain e h sp k))
               (sp (γT (t₀ ++ a) [] k) (iter (feed g) zero (suc k)) (chain e h sp k)))
```

## Ω 树

`LeafC`: 第 0 层的树 c 对着 η 时, 孩子层 `h₁ c` 的 Ω 树在孩子关系里对着 Ω_η. 有它, `tw 1` 的 Ω 树对着 Ω_Ω, 推导在量化域 `Sp` 内.

```agda
  LeafC : Set
  LeafC = ∀ {η c} → M⁰ η c → Kd c (E.Ωt η) (proj₁ (Ωt (h₁ c)))

  leaf¹ : LeafC → M¹ ΩΩ (proj₁ (Ωt ℓ¹))
  leaf¹ lf = mΩ {ν = []} refl refl (λ η c l → mU mz (lf l))

  leafSp : (lf : LeafC) → Sp (leaf¹ lf)
  leafSp lf η c l = tt
```
