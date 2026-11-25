# 合流的关系族: 颈槽位取精确读回, 其余第 0 层槽位取下界

> 验收文件 (读记号)。编译定理, 无前提: 关系族 `Rᵐ` (槽位标签 `YiELOmega.Lblᵒ`; Ω 形状层号下标层槽位即 "颈槽位" 的分支前提取 `Ex⁰`, 其余槽位同 `YiGLExact.Rˣ`) 上 Leaf `topᵐ` 对一切带 `Lblᵒ` 的层号成立 (含 `YiBVSmall.layer`, `top-layerᵐ`); 不含 Ω 形状的层号上 `Rᵐ` 与 `Rˣ` 互相给出 (`toˣ`, `ofˣ`)。
> 与 `YiELOmega.Rᵉ`: 第 0 层与颈槽位的前提相同 (`zero-sameᵐ`, `neck-sameᵐ`), 孩子路径上的第 0 层槽位不同 (`one-diffᵐ`); 层号 `one` 上 `Rᵐ` 嵌入 `Rᵉ` (`ᵐ→ᵉ-one`)。为什么不处处取 `Ex⁰`: 见 [YiMGNeck](YiMGNeck.lagda.md) 的 `no-chainᵉ-one`。
> 来源: `topᵐ` 逐行搬自 `YiELOmega.topᵉ`, 映射照 `YiXPExact.to`/`of`。不否定什么; 不改树、折叠、合法性。LowKeep 在 [YiMGFrame](YiMGFrame.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMGRel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiKVInst using (Ωω; fsnΩω)
open import OCF.Lean.YiNLRaise using (ΩΩ; fsΩΩ)
open import OCF.Lean.YiFMMap using (mapᴴ)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.EBO using () renaming (pred-suc to suc-pred)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiGLFrame using (Lbl)
open import OCF.Lean.YiGLExact using (Rˣ; Lowˣ; Low⁼ˣ)
open import OCF.Lean.YiELLim using (limAt)
open import OCF.Lean.YiELZero using (Ex⁰; ex→M⁰; Ω₁)
open import OCF.Lean.YiELOmega using (Lblᵒ; lbl-layer; Rᵉ; Lowᵉ) renaming (emb to embᵒ)
open import OCF.Lean.YiXPFrame using (NoΩ; noΩ-ch)
```

## 关系族

与 `YiGLExact.Rˣ` 的差别: 槽位标签用 `Lblᵒ`; Ω 形状层号经下标层侧的槽位走 `Neckᵐ`, 下标层是第 0 层时取 `Ex⁰`。孩子路径上的槽位 (含第 0 层) 仍是 `Rᵐ` 本身。

```agda
mutual
  Rᵐ : (ℓ : L) → E.T → Tr ℓ → Set
  Rᵐ zero = H.M⁰
  Rᵐ (nd s h) = H.Mᴴ (Sig (nd s h)) (Lowᵐ (nd s h)) (λ c → Rᵐ (h c)) (λ p → Lblᵒ (at (nd s h) p))

  Lowᵐ : (ℓ : L) (p : Pos ℓ) → E.T → Br ℓ p → Set
  Lowᵐ (nd s h) (inj₂ (c , t)) = Low⁼ᵐ (h c) t
  Lowᵐ (nd (sΩ k) h) (inj₁ t) = Neckᵐ k t

  Low⁼ᵐ : (a : L) (t : Pos⁼ a) → E.T → Br⁼ a t → Set
  Low⁼ᵐ a (inj₁ _) = Rᵐ a
  Low⁼ᵐ a (inj₂ p) = Lowᵐ a p

  Neckᵐ : (k : L) (t : Pos⁼ k) → E.T → Br⁼ k t → Set
  Neckᵐ zero (inj₁ _) = Ex⁰
  Neckᵐ zero (inj₂ ())
  Neckᵐ (nd s h) t = Low⁼ᵐ (nd s h) t

wkᵐ : ∀ ℓ {t x y} → Rᵐ ℓ t x → ℓ ⊢ x ◃ y → Rᵐ ℓ t y
wkᵐ zero = H.mw
wkᵐ (nd s h) = H.mw

module Gᵐ (s : Sh) (h : Ch s → L) =
  H.Gen {Sig (nd s h)} {Lowᵐ (nd s h)} {λ c → Rᵐ (h c)} {λ p → Lblᵒ (at (nd s h) p)}

zero-sameᵐ : (Rᵐ zero ≡ Rᵉ zero) × (Rᵐ zero ≡ Rˣ zero)
zero-sameᵐ = refl , refl

neck-sameᵐ : ∀ h → Lowᵐ (nd (sΩ zero) h) (inj₁ (inj₁ tt)) ≡ Lowᵉ (nd (sΩ zero) h) (inj₁ (inj₁ tt))
neck-sameᵐ h = refl

one-diffᵐ : (Lowᵐ K.one K.q1 ≡ H.M⁰) × (Lowᵉ K.one K.q1 ≡ Ex⁰)
one-diffᵐ = refl , refl

ᵐ→ᵉ-one : ∀ {t x} → Rᵐ K.one t x → Rᵉ K.one t x
ᵐ→ᵉ-one = mapᴴ low (λ c m → m) (λ p q → q)
  where
  low : ∀ p {η c} → Lowᵉ K.one p η c → Lowᵐ K.one p η c
  low (inj₁ ())
  low (inj₂ (tt , inj₁ tt)) {c = c} x = ex→M⁰ c x
  low (inj₂ (tt , inj₂ ()))
```

## Leaf

逐行同 `topᵉ`; 后继形状的顶槽位前提已经是 `Rᵐ (h tt)`, 不用换型。

```agda
topᵐ : ∀ a {ν} → Lblᵒ a ν → Rᵐ a (E.Ωt ν) (proj₁ (O.Ωt a))
topᵐ zero refl = H.m1 refl H.mz
topᵐ (nd sS h) {ν} (e , q) =
  subst (λ t → Rᵐ (nd sS h) (E.Ωt t) (proj₁ (O.Ωt (nd sS h)))) (suc-pred ν e)
    (H.mΩ (cof-regular (E.pred ν)) q
      (λ η c r → subst (λ t → Rᵐ (nd sS h) t (up zero tt (suc c) (O.z◃ c ◃s)))
        (sym (fs-regular (E.pred ν) η)) (H.mU H.mz (wkᵐ (h tt) r ◃s))))
topᵐ (nd sL g) {ν} (e , nf , f) = H.mL (Ωω ν e)
  (λ n → subst (λ t → Rᵐ (nd sL g) t (proj₁ (O.Ωt (nd sL g)))) (sym (fsnΩω ν n e))
    (H.mc (Ωt-mono (proj₁ (proj₂ (proj₂ (f n)))))
      (Gᵐ.m-cum sL g (λ m → O.upz {s = sL} {h = g} m (O.Ωt (g m))) n
        (H.mU H.mz (topᵐ (g n) (proj₁ (proj₂ (f n))))))))
topᵐ (nd (sΩ zero) h) {ν} (e , nf , cf , f) = H.mΩ (ΩΩ ν e) refl
  (λ η c x → subst (λ t → Rᵐ (nd (sΩ zero) h) t (proj₁ (O.upz c (O.Ωt (h c)))))
    (sym (fsΩΩ ν η e))
    (H.mc (Ωt-mono (proj₁ (proj₂ (proj₂ (f c η x)))))
      (H.mU H.mz (topᵐ (h c) (proj₁ (proj₂ (f c η x)))))))
topᵐ (nd (sΩ (nd s k)) h) ()

top-layerᵐ : Rᵐ S.layer (E.Ωt Ω₁) (proj₁ (O.Ωt S.layer))
top-layerᵐ = topᵐ S.layer lbl-layer
```

## 不含 Ω 形状的层号

槽位层号与孩子都不含 Ω 形状; 这里 `Lblᵒ` 与 `Lbl` 互相给出 (`LimAt` 由 `limAt` 补); 颈槽位不出现, 所以 `Rᵐ` 与 `Rˣ` 互相给出。最小实例的孩子层号不含 Ω 形状 (`noΩ-child`)。

```agda
mutual
  noΩ-at : ∀ ℓ → NoΩ ℓ → (p : Pos ℓ) → NoΩ (at ℓ p)
  noΩ-at (nd sS h) nω (inj₁ ())
  noΩ-at (nd sL g) nω (inj₁ ())
  noΩ-at (nd s h) nω (inj₂ (c , t)) = noΩ-at⁼ (h c) (noΩ-ch s h nω c) t
  noΩ-at (nd (sΩ k) h) () (inj₁ t)

  noΩ-at⁼ : ∀ a → NoΩ a → (t : Pos⁼ a) → NoΩ (proj₁ (sl⁼ a t))
  noΩ-at⁼ a nω (inj₁ _) = nω
  noΩ-at⁼ a nω (inj₂ p) = noΩ-at a nω p

noΩ-⊕ : ∀ a b → NoΩ a → NoΩ b → NoΩ (a ⊕ b)
noΩ-⊕ a zero na nb = na
noΩ-⊕ a (nd sS h) na nb = noΩ-⊕ a (h tt) na nb
noΩ-⊕ a (nd sL g) na nb = λ n → noΩ-⊕ a (g n) na (nb n)
noΩ-⊕ a (nd (sΩ k) h) na ()

noΩ-↑ : ∀ d → NoΩ (↑ zero d)
noΩ-↑ zero = tt
noΩ-↑ (suc d) = noΩ-↑ d
noΩ-↑ (lim f a) = λ n → noΩ-↑ (f n)
noΩ-↑ (Ω () _)
noΩ-↑ (up _ () _ _)

noΩ-child : ∀ d → NoΩ (S.child d)
noΩ-child d = noΩ-⊕ K.two (↑ zero (suc d)) tt (noΩ-↑ (suc d))

unemb : ∀ a → NoΩ a → ∀ {ν} → Lblᵒ a ν → Lbl a ν
unemb zero _ q = q
unemb (nd sS h) nω (e , q) = e , unemb (h tt) nω q
unemb (nd sL g) nω {ν} (e , nf , f) = e , nf , limAt ν e , λ n →
  proj₁ (f n) , unemb (g n) (nω n) (proj₁ (proj₂ (f n))) , proj₂ (proj₂ (f n))
unemb (nd (sΩ k) h) () q

mutual
  toˣ : ∀ ℓ → NoΩ ℓ → ∀ {t x} → Rᵐ ℓ t x → Rˣ ℓ t x
  toˣ zero _ m = m
  toˣ (nd s h) nω m = mapᴴ (lowOfᵐ (nd s h) nω) (λ c → toˣ (h c) (noΩ-ch s h nω c))
    (λ p → unemb (at (nd s h) p) (noΩ-at (nd s h) nω p)) m

  ofˣ : ∀ ℓ → NoΩ ℓ → ∀ {t x} → Rˣ ℓ t x → Rᵐ ℓ t x
  ofˣ zero _ m = m
  ofˣ (nd s h) nω m = mapᴴ (lowToᵐ (nd s h) nω) (λ c → ofˣ (h c) (noΩ-ch s h nω c))
    (λ p → embᵒ (at (nd s h) p)) m

  lowOfᵐ : ∀ ℓ → NoΩ ℓ → ∀ p {η c} → Lowˣ ℓ p η c → Lowᵐ ℓ p η c
  lowOfᵐ (nd s h) nω (inj₂ (c , t)) = lowOf⁼ᵐ (h c) (noΩ-ch s h nω c) t
  lowOfᵐ (nd (sΩ k) h) () (inj₁ t)

  lowOf⁼ᵐ : ∀ a → NoΩ a → ∀ t {η c} → Low⁼ˣ a t η c → Low⁼ᵐ a t η c
  lowOf⁼ᵐ a nω (inj₁ _) = ofˣ a nω
  lowOf⁼ᵐ a nω (inj₂ p) = lowOfᵐ a nω p

  lowToᵐ : ∀ ℓ → NoΩ ℓ → ∀ p {η c} → Lowᵐ ℓ p η c → Lowˣ ℓ p η c
  lowToᵐ (nd s h) nω (inj₂ (c , t)) = lowTo⁼ᵐ (h c) (noΩ-ch s h nω c) t
  lowToᵐ (nd (sΩ k) h) () (inj₁ t)

  lowTo⁼ᵐ : ∀ a → NoΩ a → ∀ t {η c} → Low⁼ᵐ a t η c → Low⁼ˣ a t η c
  lowTo⁼ᵐ a nω (inj₁ _) = toˣ a nω
  lowTo⁼ᵐ a nω (inj₂ p) = lowToᵐ a nω p
```
