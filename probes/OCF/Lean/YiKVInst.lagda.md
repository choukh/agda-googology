# 候选 A: 两条前提在小的点上的实例 (验收)

> 验收文件 (读记号). 编译定理, 无前提: `YiKVValue` 的 A1 在 (η, c) = (0, 0), (1, 1), (2, 2) 处成立 (`A1-at`): 孩子 two 的第 1 层底的第 c 支 `g₁ c` 不低于 ψ₁(Ω_c), 其中第 two 支不低于 ψ₁(Ω₂) (`a1-2`); A0 在 (0, 0), (1, 1) 处对一切路径, 在 (2, 2) 处对一致路径成立 (`A0-at`); 由后者, 新块上层号 2 的 Ω 树的折叠不低于 ψ₀(Ω₂) (`bho-lowerᴷ`, 值定理).
> 工具: `φ` 以第 2 层为锚, 源是第 1 层的树时对 ψ₁ 的保持 (`ΦF`, 对任意源底与起点). 两条前提的极限情形 (η 余尾 ω) 对任意树一步得出 (`a1-lim`, `a0-lim`). 不给出 A0, A1 的一般情形 (零, 后继, 松弛三种情形); 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKVInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel
open import OCF.Lean.YiKVCheck using (o¹; h₁; c1; c2; g₁; A0f)
open import OCF.Lean.YiKVValue using (module At)
open import OCF.Lean.YiCertFold using (Base; B₀)
import OCF.Align.EboLeanDef as E
open E using (HC; γT; natT; 𝟏; cof; cω; fsn; fsn0; cofψ0) renaming (ψ to ψᵉ)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cofψΩ; fsTψΩ)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_)
```

## φ 在第 1 层源树上对 ψ₁ 的保持

锚是第 2 层 (地板到锚的路径是 `inu` 两步), 目标第 1 层, 源是第 1 层的树, 证书 `ab (λ _ → here)`. 地板上的槽位推进锚层后保留 (规则 5Ω); 孩子 (第 0 层的树 y) 嵌进锚层后上折, 前面多一 (`s+`).

```agda
kk₂ : zero ≤ two
kk₂ = inu (λ _ → inu (λ _ → self))

module Φm (o2 : Ok two) (Ba : Base two) (Bm1 : Base one) (β : Tr⁺ one) (hβ : M¹ Ω₁ᵗ (proj₁ β)) where
  Φ⁺ : Tr one → Tr⁺ one
  Φ⁺ x = φ two o2 Ba kk₂ one (inc tt self) one (proj₂ o2 tt) (ab (λ _ → here)) Bm1 β x

  Φ : Tr one → Tr one
  Φ x = proj₁ (Φ⁺ x)

  Φmono : ∀ {x y} → one ⊢ x ◃ y → one ⊢ Φ x ◃ Φ y
  Φmono = φm two o2 Ba kk₂ one (inc tt self) one (proj₂ o2 tt) (ab (λ _ → here)) Bm1 β

  ΦF : ∀ {a x} → M¹ a x → M¹ (ψ₁ᵗ a) (Φ x)
  ΦF (mz {x = x}) = G¹.m-zl Φ Φmono hβ x
  ΦF (m1 {t = a} {x = x} e r) = G¹.m-next (Φ⁺ x) (cofψ1 u₁ a e) (λ n → fsnψ1 u₁ a n e) (ΦF r)
  ΦF (mL {t = a} {x = x} e h) =
    mL (cofψω u₁ a e) (λ n → subst (λ z → M¹ z (Φ x)) (sym (fsnψω u₁ a n e)) (ΦF (h n)))
  ΦF (mΩ {t = a} {p = inj₂ (tt , inj₁ tt)} {g = g} e refl h) =
    mΩ (cofψΩ u₁ a e) refl (λ η c l → subst (λ z → M¹ z (Φ (g c))) (sym (fsTψΩ u₁ a η e)) (ΦF (h η c l)))
  ΦF (mΩ {p = inj₁ ()} _ _ _)
  ΦF (mΩ {p = inj₂ (tt , inj₂ ())} _ _ _)
  ΦF (mU {x = x} m ch) = Pu (Φ⁺ x) (ΦF m) (G⁰.m-right (suc zero) ch)
  ΦF (mw m d) = mw (ΦF m) (Φmono d)
```

## A1 的三个点

孩子 two 的支 (c = c′ = two): Ω₂ 树在源层不保留, 链是源层第 1 层的自身折叠 (起点 Ω₁ 树), 各项再经 `φ`; 记号 ψ₁(Ω₂) 的 γ-链 γ₀ = Ω₁, γₙ₊₁ = ψ₁(γₙ). 孩子 one 的支: Ω₁ 树的槽位在地板上, 推进锚层后保留, 就是 `ΦF` 作用在 Ω₁ 树上. 孩子 0 的支是 Ω₁ 树上两次 `next`.

```agda
o2 : Ok two
o2 = proj₂ o¹ c2

Bx : Base two
Bx i u = ψ (tw 1) o¹ (B₀ (tw 1)) i (inc c2 u) (B₀ (tw 1) i (inc c2 u)) zero

Bx1 : Base one
Bx1 i u = ψ two o2 Bx i (inc tt u) (Bx i (inc tt u)) zero

open PFm [] (proj₂ o2 tt) Bx1 (Ωt one) Mβ₀
open Φm o2 Bx Bx1 (Ωt one) Mβ₀

zz : ℕ → Tr one
zz = iter (λ c → proj₁ (next⁺ (F⁺ c))) zero

Ω₂ᵗ : E.T
Ω₂ᵗ = E.Ωt (natT 2)

g₁2-form : proj₁ (g₁ c2) ≡ proj₁ (limc⁺ (λ k → next⁺ (Φ⁺ (zz k))))
g₁2-form = refl

sγ′ : ∀ n → M¹ (γT Ω₂ᵗ u₁ n) (zz (suc n))
sγ′ zero    = mw Mβ₀ (◃l zero)
sγ′ (suc n) = mw (PF (sγ′ n)) (◃l zero)

a1-2 : M¹ (ψ₁ᵗ Ω₂ᵗ) (proj₁ (g₁ c2))
a1-2 = mL refl (λ n → G¹.m-cum (λ k → next⁺ (Φ⁺ (zz k))) (suc n) (mw (ΦF (sγ′ n)) (◃l zero)))

g₁1-form : proj₁ (g₁ c1) ≡ Φm.Φ o2 Bx (λ i u → Ωt i) (Ωt one) Mβ₀ (proj₁ (Ωt one))
g₁1-form = refl

a1-1 : M¹ (ψ₁ᵗ Ω₁ᵗ) (proj₁ (g₁ c1))
a1-1 = Φm.ΦF o2 Bx (λ i u → Ωt i) (Ωt one) Mβ₀ Mβ₀

a1-0 : M¹ (ψ₁ᵗ (E.Ωt [])) (proj₁ (g₁ zero))
a1-0 = G¹.m-next (next⁺ (Ωt one)) refl (λ n → fsnψ1 u₁ (𝟏 ∷ []) n refl) (mw Mβ₀ (◃l zero))

A1-at : (M⁰ [] zero × M¹ (ψ₁ᵗ (E.Ωt [])) (proj₁ (g₁ zero)))
      × (M⁰ (natT 1) c1 × M¹ (ψ₁ᵗ (E.Ωt (natT 1))) (proj₁ (g₁ c1)))
      × (M⁰ (natT 2) c2 × M¹ (ψ₁ᵗ (E.Ωt (natT 2))) (proj₁ (g₁ c2)))
A1-at = (mz , a1-0) , (m1 refl mz , a1-1) , (m1 refl (m1 refl mz) , a1-2)
```

## A0 的三个点, ψ₀(Ω₂) 的值下界

第 0 层: 标准折叠是 Ω₀ 树上一次 `next`. 第 1 层: `QHm` 取前缀为空. 第 2 层: `At` 取前缀为空, 四条下界都是平凡的.

```agda
a0-0 : (w : zero ≤ h₁ zero) → M⁰ (ψ₀ᵗ (E.Ωt [])) (proj₁ (A0f zero w))
a0-0 w = G⁰.m-next (Ωt zero) refl (λ n → fsnψ1 u₀ (𝟏 ∷ []) n refl) (m1 refl mz)

a0-1 : (w : zero ≤ h₁ c1) → M⁰ (ψ₀ᵗ (E.Ωt (natT 1))) (proj₁ (A0f c1 w))
a0-1 w = QHm.QH [] (proj₂ o¹ c1) (B₀ one) (m1 refl mz) w (Ωt zero) (m1 refl mz) Mβ₀

a0-2 : M⁰ (ψ₀ᵗ (E.Ωt (natT 2))) (proj₁ (A0f c2 (z≤ two)))
a0-2 = At.lowerM [] (proj₂ o¹ c2) (B₀ two) (Ωt zero) Mβ₀ Mβ₀ (m1 refl mz) (m1 refl mz)

A0-at : (M⁰ [] zero × ((w : zero ≤ h₁ zero) → M⁰ (ψ₀ᵗ (E.Ωt [])) (proj₁ (A0f zero w))))
      × (M⁰ (natT 1) c1 × ((w : zero ≤ h₁ c1) → M⁰ (ψ₀ᵗ (E.Ωt (natT 1))) (proj₁ (A0f c1 w))))
      × (M⁰ (natT 2) c2 × M⁰ (ψ₀ᵗ (E.Ωt (natT 2))) (proj₁ (A0f c2 (z≤ two))))
A0-at = (mz , a0-0) , (m1 refl mz , a0-1) , (m1 refl (m1 refl mz) , a0-2)

bho-lowerᴷ : (h : HC (ψ₀ᵗ (E.Ωt (natT 2)))) → Rt h ≼ readRW (proj₁ (A0f c2 (z≤ two)))
bho-lowerᴷ = lower⁰ a0-2
```

## 两条前提的极限情形

对 `M⁰ η c` 归纳时, η 的余尾为 ω 的情形由归纳假设一步得出 (规则 5ω: ψ_u(Ω_η)[n] = ψ_u(Ω_{η[n]})), 对任意树成立. 余下的是零, 后继 (`m1`) 与沿 ◃ 的松弛 (`mw`) 三种情形.

```agda
Ωω : ∀ η → cof η ≡ cω → cof (E.Ωt η) ≡ cω
Ωω []       ()
Ωω (w ∷ ws) e = cong (cofψ0 (w ∷ ws)) e

fsnΩω : ∀ η n → cof η ≡ cω → fsn (E.Ωt η) n ≡ E.Ωt (fsn η n)
fsnΩω []       n ()
fsnΩω (w ∷ ws) n e = cong (λ c → fsn0 (w ∷ ws) c n) e

a1-lim : ∀ η (x : Tr one) → cof η ≡ cω → (∀ n → M¹ (ψ₁ᵗ (E.Ωt (fsn η n))) x) → M¹ (ψ₁ᵗ (E.Ωt η)) x
a1-lim η x e ih = mL (cofψω u₁ (E.Ωt η) (Ωω η e))
  (λ n → subst (λ z → M¹ z x) (sym (trans (fsnψω u₁ (E.Ωt η) n (Ωω η e)) (cong ψ₁ᵗ (fsnΩω η n e)))) (ih n))

a0-lim : ∀ η (x : Tr zero) → cof η ≡ cω → (∀ n → M⁰ (ψ₀ᵗ (E.Ωt (fsn η n))) x) → M⁰ (ψ₀ᵗ (E.Ωt η)) x
a0-lim η x e ih = mL (cofψω u₀ (E.Ωt η) (Ωω η e))
  (λ n → subst (λ z → M⁰ z x) (sym (trans (fsnψω u₀ (E.Ωt η) n (Ωω η e)) (cong ψ₀ᵗ (fsnΩω η n e)))) (ih n))
```
