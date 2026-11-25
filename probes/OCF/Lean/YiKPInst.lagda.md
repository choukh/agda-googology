# 验收一侧: `tw 1` 上孩子族接口的两个实例, 归约到读回层号上的一条陈述 `Lift₁`

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理. 实例一 `Fin.Kidᶠ` (无前提): 孩子取自然数 `nat n`, 关系是封闭族 `YiHCFam.M n`, 律来自 `YiHCFold.LF`, `Qu`; `Fin.lf¹` 是 [YiKPRel](YiKPRel.lagda.md) 的 `LF¹` 在它上面的形式, `no-leafᶠ`: 这个实例下 `LeafC` 为假 (孩子域太窄, 不是数学障碍).
> 实例二 `Sem.Kidˢ`: 孩子关系取 "朝第 0 层的折叠对着 ψ₀(s)" 本身, 律是恒等; `LeafC` 展开成 `Lift₁`. `k1ˢ : Lift₁ → M⁰ (EBOψ 2) (ψ₀ʳ … (Ωt (tw 1)))` (条件定理; `Lift₁` 只在 (natT n, nat n) 上验证: `lift-fin`).
> 不给出什么: `Lift₁` 对一般的 (η, c) 没有证也没有否定; 值的陈述停在 `M⁰`, 没有过出口 `exitᴴ`; 无条件的只有第 0 行 `row0` (重证, 弱于已有的 `YiKSRead.k1`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKPInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (Pt; can; pu; pt; tu; OKB)
open import OCF.Lean.YiRBCrit using (h₁; blk)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r)
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (mz; m1; mU; M⁰; module G⁰)
import OCF.Align.EboLeanDef as E
open E using (natT; EBOψ)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiCLFam using (nat; fn)
open import OCF.Lean.YiCLLow using (s0)
open import OCF.Lean.YiHCFam using (M; m⊴N; ΩJ)
open import OCF.Lean.YiHCFold using (Qu; LF; GB; mkGB; gΩ; gM; sΩ-LF)
open import OCF.Lean.YiSMFold using (twˢ)
open import OCF.Lean.YiKPRel
```

## 路径

孩子 `nat n` 的层号是 `fn n`. 接口要的两条路径 (一致路径, 经下标层进孩子) 在 `fn n` 上都是 `zpt n`, 即 `YiRBFam.Pt` 的 `pu` 链.

```agda
o¹ : Ok ℓ¹
o¹ = Ok-tw 1

zq : ∀ n → Pt n 0
zq zero    = can s0
zq (suc n) = pu (zq n)

zpt : ∀ n → zero ≤ fn n
zpt n = pt (zq n)

pz-eq : ∀ n → z≤ (fn n) ≡ zpt n
pz-eq zero    = refl
pz-eq (suc n) = cong (λ p → inu (λ _ → p)) (pz-eq n)

pk-eq : ∀ n → self ∙ proj₂ (proj₁ o¹) (nat n) ≡ zpt n
pk-eq zero    = refl
pk-eq (suc n) = cong (λ p → inu (λ _ → p)) (pk-eq n)
```

## 实例一: 孩子取自然数

`Kdᶠ c s y`: c 是某个 `nat n`, 且 `M n s y`. 底的条件在 `nat (suc n)` 上是 `YiHCFold.GB`.

```agda
module Fin (r : Rb ℓ¹) (t₀ : E.T) where

  Kdᶠ : (c : Tr zero) → E.T → Tr (h₁ c) → Set
  Kdᶠ c s y = Σ ℕ λ n → Σ (c ≡ nat n) λ e → M n s (subst (λ c → Tr (h₁ c)) e y)

  GBf : ∀ n → Base (fn n) → Set
  GBf zero    B = ⊤
  GBf (suc n) B = GB n B t₀

  GBcᶠ : (c : Tr zero) → Base (h₁ c) → Set
  GBcᶠ c B = ∀ n (e : c ≡ nat n) → GBf n (subst (λ c → Base (h₁ c)) e B)

  Pcᶠ : (c : Tr zero) → zero ≤ h₁ c → Set
  Pcᶠ c v = ∀ n (e : c ≡ nat n) → subst (λ c → zero ≤ h₁ c) e v ≡ zpt n

  pzᶠ : ∀ c → Pcᶠ c (z≤ (h₁ c))
  pzᶠ _ n refl = pz-eq n

  pkᶠ : ∀ c → Pcᶠ c (self ∙ proj₂ (proj₁ o¹) c)
  pkᶠ _ n refl = pk-eq n

  gbf-mono : ∀ n {B B′ : Base (fn n)} → GBf n B → (∀ i u → proj₁ (B i u) ⊴ proj₁ (B′ i u)) → GBf n B′
  gbf-mono zero    g le = tt
  gbf-mono (suc n) g le = mkGB (λ si → ⊴-trans (gΩ g si) (le _ _)) (λ {i} si → m⊴N i (gM g si) (le _ _))

  gb⊴ᶠ : ∀ c {B B′ : Base (h₁ c)} → GBcᶠ c B → (∀ i u → proj₁ (B i u) ⊴ proj₁ (B′ i u)) → GBcᶠ c B′
  gb⊴ᶠ _ g le n refl = gbf-mono n (g n refl) le

  foldN : ∀ n (v : zero ≤ fn n) → v ≡ zpt n → (B : Base (fn n)) → GBf n B
        → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
        → ∀ {s y} → M n s y → M⁰ (ψᴺ 0 (t₀ ++ s)) (proj₁ (ψ (fn n) (proj₂ o¹ (nat n)) (proj₂ r (nat n)) B zero v β y))
  foldN zero    _ refl B g β hβ m = Qu (proj₂ o¹ (nat 0)) (proj₂ r (nat 0)) B self β hβ m
  foldN (suc n) _ refl B g β hβ m = LF (proj₂ o¹ (nat (suc n))) (proj₂ r (nat (suc n))) (tu (zq n)) t₀ B g β hβ m

  foldᶠ : ∀ c (v : zero ≤ h₁ c) → Pcᶠ c v → (B : Base (h₁ c)) → GBcᶠ c B
        → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
        → ∀ {s y} → Kdᶠ c s y → M⁰ (ψᴺ 0 (t₀ ++ s)) (proj₁ (ψ (h₁ c) (proj₂ o¹ c) (proj₂ r c) B zero v β y))
  foldᶠ _ v pc B g β hβ (n , refl , m) = foldN n v (pc n refl) B (g n refl) β hβ m

  Kidᶠ : Kid o¹ r t₀
  Kidᶠ = record { Kd = Kdᶠ ; GBc = GBcᶠ ; Pc = Pcᶠ ; pz = pzᶠ ; pk = pkᶠ ; gb⊴ = gb⊴ᶠ ; foldᶜ = foldᶠ }

  open Top o¹ r t₀ Kidᶠ public
```

保持 (无前提): 对一切满足 `Sp` 的推导.

```agda
  lf¹ : (B : Base ℓ¹) → GB¹ B → ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
      → ∀ {a x} (m : M¹ a x) → Sp m → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (ψ ℓ¹ o¹ r B zero w β x))
  lf¹ B gb = Fold.LF¹ B gb
```

量化域里的树: Ω 树的第 `nat n` 支对着 Ω_n. 整棵 Ω 树不在: `LeafC` 要孩子取一切对着某个 η 的 c, 而 `Kdᶠ` 只认自然数.

```agda
  leaf-fin : ∀ n → Kdᶠ (nat n) (Ωᴺ n) (proj₁ (Ωt (fn n)))
  leaf-fin n = n , refl , ΩJ n (Ωt (fn n)) ⊴r

  blk-fin : ∀ n → M¹ (Ωᴺ n) (blk (nat n))
  blk-fin n = mU mz (leaf-fin n)

  ωt : Tr zero
  ωt = proj₁ (next⁺ (Ωt zero))

  ¬nat : ∀ n → ωt ≡ nat n → ⊥
  ¬nat zero    ()
  ¬nat (suc n) ()

  no-leafᶠ : LeafC → ⊥
  no-leafᶠ lf with lf {η = []} {c = ωt} mz
  ... | n , e , _ = ¬nat n e
```

## 标准底, 第 0 行

标准底满足 `GB¹` (前缀取空). 塔第 1 项 (兄弟孩子折叠的 `twʳ 1`) 的回灌链第 0 项是第 `nat 0` 支, 所以 ψ₀(Ω₀) 对着它.

```agda
module Std (r : Rb ℓ¹) where
  open Fin r []

  gb₀c : ∀ n → GBf n (B₀ (fn n))
  gb₀c zero    = tt
  gb₀c (suc n) = mkGB (λ si → ⊴r) (λ {i} si → ΩJ i (Ωt (fn i)) ⊴r)

  gb₀ᶠ′ : ∀ c → GBcᶠ c (B₀ (h₁ c))
  gb₀ᶠ′ _ n refl = gb₀c n

  gb₀ᶠ : GB¹ (B₀ ℓ¹)
  gb₀ᶠ = mkGB¹ (m1 refl mz) gb₀ᶠ′

  val-fin : ∀ n → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (blk (nat n))))
  val-fin n = lf¹ (B₀ ℓ¹) gb₀ᶠ wu (Ωt zero) (m1 refl mz) (blk-fin n) tt

  row0 : M⁰ (ψᴺ 0 (Ωᴺ 0)) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (proj₁ (Ωt ℓ¹))))
  row0 = G⁰.m-cum
    (λ k → ψ₀ʳ ℓ¹ o¹ r (blk (iter (λ z → proj₁ (ψ ℓ¹ o¹ r (B₀ ℓ¹) zero (ink self) (Ωt zero) (blk z))) zero k)))
    0 (val-fin 0)
```

## 实例二: 孩子关系取折叠的保持本身

`Kdˢ c s y`: 孩子层 `h₁ c` 上, 对接口的两条路径, 一切各分量在 Ω 树之上的底 (`OKB`), 一切对着 ψ₀(0) 的起点, y 朝第 0 层的折叠对着 ψ₀(s). 接口的律是恒等, 所以 `LF¹` 的全部内容落到 `LeafC` 上, 它在这里展开成 `Lift₁`.

```agda
module Sem (r : Rb ℓ¹) where

  Pcˢ : (c : Tr zero) → zero ≤ h₁ c → Set
  Pcˢ c v = (v ≡ z≤ (h₁ c)) ⊎ (v ≡ self ∙ proj₂ (proj₁ o¹) c)

  Kdˢ : (c : Tr zero) → E.T → Tr (h₁ c) → Set
  Kdˢ c s y = (v : zero ≤ h₁ c) → Pcˢ c v → (B : Base (h₁ c)) → OKB B → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
            → M⁰ (ψᴺ 0 s) (proj₁ (ψ (h₁ c) (proj₂ o¹ c) (proj₂ r c) B zero v β y))

  Kidˢ : Kid o¹ r []
  Kidˢ = record { Kd = Kdˢ ; GBc = λ c B → OKB B ; Pc = Pcˢ ; pz = λ c → inj₁ refl ; pk = λ c → inj₂ refl
                ; gb⊴ = λ c ok le i u → ⊴-trans (ok i u) (le i u)
                ; foldᶜ = λ c v pc B g β hβ k → k v pc B g β hβ }

  open Top o¹ r [] Kidˢ

  Lift₁ : Set
  Lift₁ = ∀ {η c} → M⁰ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₁ c)))

  _ : Lift₁ ≡ LeafC
  _ = refl

  gb₀ˢ : GB¹ (B₀ ℓ¹)
  gb₀ˢ = mkGB¹ (m1 refl mz) (λ c i u → ⊴r)

  k1ˢ : Lift₁ → M⁰ (EBOψ 2) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (proj₁ (Ωt ℓ¹))))
  k1ˢ lf = Fold.LF¹ (B₀ ℓ¹) gb₀ˢ wu (Ωt zero) (m1 refl mz) (leaf¹ lf) (leafSp lf)
```

`Lift₁` 的前提在 (natT n, nat n) 上可满足: 由 `Qu` 与 `sΩ-LF`.

```agda
  liftN : ∀ n (B : Base (fn n)) → OKB B → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
        → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ (fn n) (proj₂ o¹ (nat n)) (proj₂ r (nat n)) B zero (zpt n) β (proj₁ (Ωt (fn n)))))
  liftN zero    B ok β hβ = Qu (proj₂ o¹ (nat 0)) (proj₂ r (nat 0)) B self β hβ (m1 refl mz)
  liftN (suc n) B ok β hβ = sΩ-LF (proj₂ o¹ (nat (suc n))) (proj₂ r (nat (suc n))) (tu (zq n)) B β ok hβ

  lift-fin : ∀ n → Kdˢ (nat n) (E.Ωt (natT n)) (proj₁ (Ωt (h₁ (nat n))))
  lift-fin n _ (inj₁ refl) B ok β hβ =
    subst (λ v → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ (fn n) (proj₂ o¹ (nat n)) (proj₂ r (nat n)) B zero v β (proj₁ (Ωt (fn n))))))
      (sym (pz-eq n)) (liftN n B ok β hβ)
  lift-fin n _ (inj₂ refl) B ok β hβ =
    subst (λ v → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ (fn n) (proj₂ o¹ (nat n)) (proj₂ r (nat n)) B zero v β (proj₁ (Ωt (fn n))))))
      (sym (pk-eq n)) (liftN n B ok β hβ)
```

## 塔第 1 项

证据取 `rb-tw 1` 时折叠的值就是主线候选的闭项 `YiSMFold.twˢ 1` (与 `YiRWFold.twᶜ 1` 同值: `YiSMValue.same-twˢ`).

```agda
k1-tw : Sem.Lift₁ (rb-tw 1) → M⁰ (EBOψ 2) (twˢ 1)
k1-tw = Sem.k1ˢ (rb-tw 1)

row0-tw : M⁰ (ψᴺ 0 (Ωᴺ 0)) (twˢ 1)
row0-tw = Std.row0 (rb-tw 1)
```
