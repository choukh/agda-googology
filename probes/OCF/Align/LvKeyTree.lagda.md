# 键即节点的数据树 (定义)

> 底座 [LvKeyBase](LvKeyBase.lagda.md). 不含记号. 结论写在 [LvKey](LvKey.lagda.md). 由 [UniformLvTree](UniformLvTree.lagda.md) 改写; 没有高度标签. 全部定义在 `Over c` 里: $c$ 是这次折叠的顶层层号, 地板项的键是 $c$ 里的位置.
>
> **世界的接口 (给证书一路).** 世界 `w = wd ℓ₀ Ε`: $\ell_0$ 是可数层的旧世界 (目标 $i<\ell_0$), `Ε` 是节点的表. 三条规则:
>
> 1. 查: `at Ε y ℓ` 是关系, 尊重 `≈` (`at-resp`), 在 `≈` 下唯一 (`at-uq`), 界非零 (`at-pos`).
> 2. 证据: `tk P K` 的证据是 $P$ 自己可容许 (`AdmC`), 且 $K$ 落在节点的界之下 (`BelS`).
> 3. 更新: `cloK` 的新表是 `Ε ▸ lcl κ , X`. 进界的是 `S.φ`, 恰是地板里键 $\approx\kappa$ 的项及它们的前缀分支; 别的项不进界, 也不动 (`S.lft`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; <→◃; Simᴵ; <ᴵ-dec; _◃₁_; ◃₁→◃; self; <ᴵ-trans)
import OCF.Align.Level as Lv
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; outˢ; toZ; Ωˢ; _+ˢ_; tr⁻ˢ)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; bound; Bd; Fc; evF; iF; FB; liftEv; Top)
open import OCF.Align.LvKeyBase
```

## §1 世界与证据

```agda
record Wd : Set where
  constructor wd
  field
    ℓ₀ : Ordᴵ
    Ε  : Ents
open Wd public

Wok : Wd → Set
Wok w = (zero <ᴵ ℓ₀ w) × OkE (Ε w)

BelS : Ents → LI → Ordᴵ → Set
BelS E y K = Σ Ordᴵ λ ℓ → at E y ℓ × Simᴵ (suc K) ℓ

S→B : ∀ {E y K} → BelS E y K → Bel E y K
S→B (ℓ , a , s) = ℓ , a , s zero

B→S : ∀ {E y K} → Bel E y K → BelS E y K
B→S (ℓ , a , q) = ℓ , a , (λ { zero → q ; (suc r) → <ᴵ-trans r q })

Cf : LI → Set
Cf c = WF c × (c ≈ c)
```

## §2 带键的地板

```agda
module Over (c : LI) where
  infixl 5 _∪_
  data Fᵗ : Set where
    tz  : Fᵗ
    t₀  : Ordᴵ → Fᵗ
    tb  : Ordᴵ → Fᵗ
    tk  : ∀ {g} → Cp (lcl g) c → Ordᴵ → Fᵗ
    _∪_ : Fᵗ → Fᵗ → Fᵗ

  Evt : Wd → Fᵗ → Set
  Evt w tz       = ⊤
  Evt w (t₀ K)   = Simᴵ (suc K) (ℓ₀ w)
  Evt w (tb K)   = Simᴵ K (ℓ₀ w)
  Evt w (tk {g} p K) = AdmC (Ε w) p × BelS (Ε w) (lcl g) K
  Evt w (a ∪ b)  = Evt w a × Evt w b

  Fl₀ : Fᵗ
  Fl₀ = tz ∪ t₀ zero

  prj₀ : Fᵗ → Flr
  prj₀ tz       = fz
  prj₀ (t₀ K)   = fk K
  prj₀ (tb K)   = fb K
  prj₀ (tk p K) = fz
  prj₀ (a ∪ b)  = prj₀ a ⊔ prj₀ b

  toPrj₀ : ∀ {w} (π : Fᵗ) → Evt w π → Ev (ℓ₀ w) (prj₀ π)
  toPrj₀ tz e = tt
  toPrj₀ (t₀ K) e = e
  toPrj₀ (tb K) e = e
  toPrj₀ (tk p K) e = tt
  toPrj₀ (a ∪ b) e = toPrj₀ a (proj₁ e) , toPrj₀ b (proj₂ e)

  ofPrj₀ : ∀ {w x} (π : Fᵗ) → Ev x (prj₀ π) → Evt w π → Evt (wd x (Ε w)) π
  ofPrj₀ tz _ e = tt
  ofPrj₀ (t₀ K) a e = a
  ofPrj₀ (tb K) a e = a
  ofPrj₀ (tk p K) a e = e
  ofPrj₀ (a ∪ b) x e = ofPrj₀ a (proj₁ x) (proj₁ e) , ofPrj₀ b (proj₂ x) (proj₂ e)
```

## §3 进界的项: 在证据之上挑选

`S G`: 挑出的地板 `φ`, 它在键的界 $\ell$ 上的证据 (`wit`; 没有挑出任何项时任何 $\ell$ 都行), 以及给定新界 $X$ 时目标 $G$ 在新表里的证据 (`lft`). `pick` 用 `kdec` 回答 "这个节点是不是 $\kappa$". `walk` 沿位置走一遍: 位置的前缀分支也是证据, 表一更新它们也要搬. 这一处是这个设计里**唯一**判定键的地方, 判定读的是 `Evt` 里的字面证据.

```agda
  module Sel (wf : WF c) (sf : c ≈ c) {κ} (P : Cp (lcl κ) c) (w : Wd) (ok : Wok w) (ap : AdmC (Ε w) P) where
    E = Ε w
    E′ : Ordᴵ → Ents
    E′ X = E ▸ lcl κ , X

    kself : lcl κ ≈ lcl κ
    kself = selfAt sf P

    record S (G : Ents → Set) : Set where
      field
        φ   : Flr
        wit : (∀ ℓ → Ev ℓ φ) ⊎ (Σ Ordᴵ λ ℓ → at E (lcl κ) ℓ × Ev ℓ φ)
        lft : ∀ X → Ev X φ → G (E′ X)
    open S public

    triv : ∀ {G} → (∀ X → G (E′ X)) → S G
    triv f = record { φ = fz ; wit = inj₁ (λ _ → tt) ; lft = λ X _ → f X }

    mapS : ∀ {A B} → (∀ F → A F → B F) → S A → S B
    mapS f s = record { φ = φ s ; wit = wit s ; lft = λ X x → f _ (lft s X x) }

    _⋈_ : ∀ {A B} → S A → S B → S (λ F → A F × B F)
    s ⋈ s′ = record { φ = φ s ⊔ φ s′ ; wit = mg (wit s) (wit s′) ; lft = λ X x → lft s X (proj₁ x) , lft s′ X (proj₂ x) }
      where
      mg : ∀ {a b} → ((∀ ℓ → Ev ℓ a) ⊎ (Σ Ordᴵ λ ℓ → at E (lcl κ) ℓ × Ev ℓ a)) → ((∀ ℓ → Ev ℓ b) ⊎ (Σ Ordᴵ λ ℓ → at E (lcl κ) ℓ × Ev ℓ b)) →
           (∀ ℓ → Ev ℓ (a ⊔ b)) ⊎ (Σ Ordᴵ λ ℓ → at E (lcl κ) ℓ × Ev ℓ (a ⊔ b))
      mg (inj₁ f) (inj₁ h) = inj₁ (λ ℓ → f ℓ , h ℓ)
      mg (inj₁ f) (inj₂ (ℓ , a , y)) = inj₂ (ℓ , a , f ℓ , y)
      mg (inj₂ (ℓ , a , x)) (inj₁ h) = inj₂ (ℓ , a , x , h ℓ)
      mg (inj₂ (ℓ , a , x)) (inj₂ (ℓ′ , a′ , y)) with at-uq {E} kself a a′
      ... | refl = inj₂ (ℓ , a , x , y)

    pick : ∀ {g} (Q : Cp (lcl g) c) → AdmC E Q → ∀ K → BelS E (lcl g) K → S (λ F → BelS F (lcl g) K)
    pick {g} Q aq K (ℓ , a , s) with kdec wf sf Q P E (proj₂ ok) aq ap
    ... | inj₁ e = record { φ = fk K ; wit = inj₂ (ℓ , at-resp {E} e a , s) ; lft = λ X x → X , inj₁ (e , refl) , x }
    ... | inj₂ n = record { φ = fz ; wit = inj₁ (λ _ → tt) ; lft = λ X _ → ℓ , inj₂ (n , a) , s }

    walk : ∀ {a x} (Q : Cp a c) → AdmC E Q → (r : Cp x a) → AdmC E r → S (λ F → AdmC F r)
    walk Q aq self _ = triv (λ _ → tt)
    walk Q aq (suc r) ad = walk (Q ⊙ suc self) (adm⊙ {E} Q aq tt) r ad
    walk Q aq (lim n r) ad = walk (Q ⊙ lim n self) (adm⊙ {E} Q aq tt) r ad
    walk Q aq (fst r) ad = walk (Q ⊙ fst self) (adm⊙ {E} Q aq tt) r ad
    walk Q aq (bra η r) (u , ad) =
      mapS (λ F x → S→B {F} (proj₁ x) , proj₂ x)
           (pick Q aq η (B→S {E} u) ⋈ walk (Q ⊙ bra η self) (adm⊙ {E} Q aq (u , tt)) r ad)

    selF : ∀ π → Evt w π → S (λ F → Evt (wd (ℓ₀ w) F) π)
    selF tz e = triv (λ _ → tt)
    selF (t₀ K) e = triv (λ _ → e)
    selF (tb K) e = triv (λ _ → e)
    selF (tk p K) (ad , b) = walk self tt p ad ⋈ pick p ad K b
    selF (a ∪ b) (x , y) = selF a x ⋈ selF b y

    L₀ : ∀ {a} → ((∀ ℓ → Ev ℓ a) ⊎ (Σ Ordᴵ λ ℓ → at E (lcl κ) ℓ × Ev ℓ a)) → Σ Ordᴵ λ ℓ → (zero <ᴵ ℓ) × Ev ℓ a
    L₀ (inj₁ f) = suc zero , zero , f (suc zero)
    L₀ (inj₂ (ℓ , a , x)) = ℓ , at-pos {E} (proj₂ ok) a , x

    -- 闭包的界: 只看挑出的项, 目标是 0
    Bnd : ∀ π (ev : Evt w π) → Top zero (proj₁ (L₀ (wit (selF π ev)))) (φ (selF π ev) ⊔ fk zero)
    Bnd π ev = bound (φ (selF π ev) ⊔ fk zero) (proj₂ (proj₂ (L₀ (wit (selF π ev)))) , (λ { zero → proj₁ (proj₂ (L₀ (wit (selF π ev)))) ; (suc ()) })) (proj₁ (proj₂ (L₀ (wit (selF π ev)))))
```

## §4 求值的积木

```agda
  Runᵗ : Fᵗ → Set
  Runᵗ π = ∀ {i w} → Wok w → Evt w π → i <ᴵ ℓ₀ w → Ordˢ i

  wkᵗ : ∀ {π ρ} → (∀ {w} → Evt w ρ → Evt w π) → Runᵗ π → Runᵗ ρ
  wkᵗ le R ok e p = R ok (le e) p

  limᵗ : ∀ {π} → (ℕ → Runᵗ π) → Runᵗ π
  limᵗ F ok e p = Ord₊ˢ.lim (λ m → F m ok e p)

  sucᵗ : ∀ {π} → Runᵗ π → Runᵗ π
  sucᵗ R ok e p = Ord₊ˢ.lim (iter (R ok e p +ˢ_) Ord₊ˢ.zero)

  limᵢᵗ : ∀ {π j} → (∀ {w} → Evt w π → j <ᴵ ℓ₀ w) → (Ordˢ j → Runᵗ π) → Runᵗ π
  limᵢᵗ {j = j} ac h ok ev p with <ᴵ-dec (ac ev) p
  ... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → h (tr⁻ˢ e (outˢ (<→◃ r) y)) ok ev p)
  ... | injᵇ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ok ev (ac ev)) (Ωˢ j) m) ok ev p)
  ... | injᶜ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ok ev (ac ev)) (Ωˢ j) m) ok ev p)

  ŝᵗ : ∀ {π} (c₀ : Ordᴵ) → Runᵗ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Runᵗ π) → Runᵗ π
  ŝᵗ c₀ t g ok e p = Ord₊ˢ.ŝ c₀ (t ok e p) (λ η d → g η d ok e p)

  ĉᵗ : ∀ {π} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → Runᵗ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Runᵗ π) → Runᵗ π
  ĉᵗ c₀ t₀′ g o₀ o ok e p = Ord₊ˢ.ĉᴸ c₀ t₀′ g (o₀ ok e p) (λ η d → o η d ok e p)
```

**可数层的闭包.** 与 [UniformLvTree](UniformLvTree.lagda.md) 的 `cloᵗ zero` 同形. 表不动.

```agda
  cl₀ : ∀ {π} → Runᵗ π → ((η : Ordᴵ) → Runᵗ (π ∪ t₀ η)) → Runᵗ π
  cl₀ {π} t g {i} {w} ok ev p =
    Ord₊ˢ.ŝ (Bd B) (t ok ev p)
      (λ η e → g η {w = wd (Mlev (Fc B) (suc η) (FB B e)) (Ε w)} (lim 0 (proj₂ (evF B) zero) , proj₂ ok)
                   (ofPrj₀ π (liftEv (prj₀ π) (λ q → lim 0 q) (proj₁ (evF B))) ev , (λ q → lim 1 q))
                   (lim 0 (iF B)))
    where
    B = bound (prj₀ π ⊔ fk zero) (toPrj₀ π ev , (λ { zero → proj₁ ok ; (suc ()) })) p
```

**节点的闭包.** 位置 $P$ 自带可容许的证据 (地板推出). 界只看 `selF` 挑出的项; 目标留在 $\ell_0$ 里, 界的起点取 $0$, 与 `cloᵗ (suc h)` 同形. 新表在 $\kappa$ 处是 $X$, 别处不变. 这里**没有**标签, 也没有对表的全称查询.

```agda
  cloK : WF c → c ≈ c → ∀ {π g} (P : Cp (lcl g) c) → (∀ {w} → Evt w π → AdmC (Ε w) P) → Runᵗ π → ((η : Ordᴵ) → Runᵗ (π ∪ tk P η)) → Runᵗ π
  cloK wf sf {π} {g} P pa t h {i} {w} ok ev p =
    Ord₊ˢ.ŝ (Bd B) (t ok ev p)
      (λ η e → h η {w = W η e} (proj₁ ok , (proj₂ ok , lim 0 (proj₂ (evF B) zero)))
                   (Lft η e , (pa (Lft η e) , (X η e , inj₁ (kself , refl) , (λ q → lim 1 q))))
                   p)
    where
    open Sel wf sf P w ok (pa ev)
    Sl : S (λ F → Evt (wd (ℓ₀ w) F) π)
    Sl = selF π ev
    B = Bnd π ev
    X : ∀ η → Bd B ⊑ᴵ η → Ordᴵ
    X η e = Mlev (Fc B) (suc η) (FB B e)
    W : ∀ η → Bd B ⊑ᴵ η → Wd
    W η e = wd (ℓ₀ w) (E′ (X η e))
    Lft : ∀ η e → Evt (W η e) π
    Lft η e = lft Sl (X η e) (liftEv (φ Sl) (λ q → lim 0 q) (proj₁ (evF B)))
```

## §5 数据树

与 [UniformLvTree](UniformLvTree.lagda.md) §3 同形. `oc₀` 是可数层的闭包, `ocl P pa t h` 是节点 $P$ 的闭包.

```agda
  module _ (L : LI) (U : ∀ {k} → k <ᴸ L → Fᵗ → Set) where
    data O₊ : Fᵗ → Set where
      o0   : ∀ {π} → O₊ π
      os   : ∀ {π} → O₊ π → O₊ π
      ol   : ∀ {π} → (ℕ → O₊ π) → O₊ π
      oi   : ∀ {π j} → (∀ {w} → Evt w π → j <ᴵ ℓ₀ w) → (Ordˢ j → O₊ π) → O₊ π
      oŝ   : ∀ {π} (c₀ : Ordᴵ) → O₊ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ π) → O₊ π
      oĉ   : ∀ {π} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → O₊ π → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ π) → O₊ π
      oc₀  : ∀ {π} → O₊ π → ((η : Ordᴵ) → O₊ (π ∪ t₀ η)) → O₊ π
      ocl  : ∀ {π g} (P : Cp (lcl g) c) → (∀ {w} → Evt w π → AdmC (Ε w) P) → O₊ π → ((η : Ordᴵ) → O₊ (π ∪ tk P η)) → O₊ π
      owk  : ∀ {π ρ} → (∀ {w} → Evt w ρ → Evt w π) → O₊ π → O₊ ρ
      oΩ   : ∀ {π k} → (∀ {w} → Evt w π → Evt w Fl₀) → (r : k <ᴸ L) → (∀ {w} → Evt w π → Adm (Ε w) r) → (∀ ξ → U r ξ → O₊ (ξ ∪ π)) → O₊ π
      oev  : ∀ {π} → (∀ {w} → Wok w → Evt w π → O₊ π) → O₊ π

  O  : LI → Fᵗ → Set
  Us : ∀ L {k} → k <ᴸ L → Fᵗ → Set
  O L π = O₊ L (Us L) π
  Us (suc a) zero      ξ = O a ξ
  Us (suc b) (suc r)   ξ = Us b r ξ
  Us (lim f) (lim n r) ξ = Us (f n) r ξ
  Us (lcl g) (fst r)   ξ = Us (g one) r ξ
  Us (lcl g) (bra η r) ξ = Us (g η) r ξ

  outU : ∀ {L k} (r : k <ᴸ L) {ξ} → Us L r ξ → O k ξ
  outU zero      x = x
  outU (suc r)   x = outU r x
  outU (lim n r) x = outU r x
  outU (fst r)   x = outU r x
  outU (bra η r) x = outU r x

  intoU : ∀ {L k} (r : k <ᴸ L) {ξ} → O k ξ → Us L r ξ
  intoU zero      x = x
  intoU (suc r)   x = intoU r x
  intoU (lim n r) x = intoU r x
  intoU (fst r)   x = intoU r x
  intoU (bra η r) x = intoU r x

  asl : ∀ {a b d w} → Evt w (a ∪ (b ∪ d)) → Evt w ((a ∪ b) ∪ d)
  asl (u , (v , t)) = (u , v) , t
  asr : ∀ {a b d w} → Evt w ((a ∪ b) ∪ d) → Evt w (a ∪ (b ∪ d))
  asr ((u , v) , t) = u , (v , t)
  swp : ∀ {a b d w} → Evt w (b ∪ (a ∪ d)) → Evt w (a ∪ (b ∪ d))
  swp (u , (v , t)) = v , (u , t)
  sw₃ : ∀ {a b d w} → Evt w ((a ∪ d) ∪ b) → Evt w ((a ∪ b) ∪ d)
  sw₃ ((u , v) , t) = (u , t) , v
```

## §6 加法, 嵌入, 搬运

```agda
  infixl 6 _⊕_
  _⊕_ : ∀ {k φ ψ} → O k φ → O k ψ → O k (φ ∪ ψ)
  W ⊕ o0       = owk proj₁ W
  W ⊕ os a     = os (W ⊕ a)
  W ⊕ ol F     = ol (λ n → W ⊕ F n)
  W ⊕ oi ac f  = oi (λ e → ac (proj₂ e)) (λ x → W ⊕ f x)
  W ⊕ oŝ c₀ t g = oŝ c₀ (W ⊕ t) (λ η e → W ⊕ g η e)
  W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
  W ⊕ oc₀ t g = oc₀ (W ⊕ t) (λ η → owk asr (W ⊕ g η))
  W ⊕ ocl P pa t g = ocl P (λ e → pa (proj₂ e)) (W ⊕ t) (λ η → owk asr (W ⊕ g η))
  W ⊕ owk le t = owk (λ e → proj₁ e , le (proj₂ e)) (W ⊕ t)
  W ⊕ oΩ fe r ac h = oΩ (λ e → fe (proj₂ e)) r (λ e → ac (proj₂ e)) (λ ξ z → owk swp (W ⊕ h ξ z))
  W ⊕ oev f = oev (λ ok e → W ⊕ f ok (proj₂ e))

  data Dn : LI → LI → Set where
    ds : ∀ {k} → Dn k (suc k)
    dl : ∀ {f} n → Dn (f n) (lim f)
    df : ∀ {g} → Dn (g one) (lcl g)
    db : ∀ {g} η → Cp (lcl g) c → Dn (g η) (lcl g)

  dnF : ∀ {a b} → Dn a b → Fᵗ
  dnF ds       = tz
  dnF (dl n)   = tz
  dnF df       = tz
  dnF (db η P) = tk P η

  pl : ∀ {a b} → Dn a b → ∀ {k} → k <ᴸ a → k <ᴸ b
  pl ds       r = suc r
  pl (dl n)   r = lim n r
  pl df       r = fst r
  pl (db η _) r = bra η r

  cvU : ∀ {a b} (d : Dn a b) {k} (r : k <ᴸ a) {ξ} → Us b (pl d r) ξ → Us a r ξ
  cvU ds       r x = x
  cvU (dl n)   r x = x
  cvU df       r x = x
  cvU (db η _) r x = x

  admD : ∀ {a b} (d : Dn a b) {k} (r : k <ᴸ a) {w} → Evt w (dnF d) → Adm (Ε w) r → Adm (Ε w) (pl d r)
  admD ds       r e a = a
  admD (dl n)   r e a = a
  admD df       r e a = a
  admD (db η _) r {w} (_ , b) a = S→B {Ε w} b , a

  ι : ∀ {a b} (d : Dn a b) {π} → O a π → O b (π ∪ dnF d)
  ι d o0 = o0
  ι d (os a) = os (ι d a)
  ι d (ol F) = ol (λ n → ι d (F n))
  ι d (oi ac f) = oi (λ e → ac (proj₁ e)) (λ x → ι d (f x))
  ι d (oŝ c₀ t g) = oŝ c₀ (ι d t) (λ η e → ι d (g η e))
  ι d (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι d o₀) (λ η e → ι d (o η e))
  ι d (oc₀ t g) = oc₀ (ι d t) (λ η → owk sw₃ (ι d (g η)))
  ι d (ocl P pa t g) = ocl P (λ e → pa (proj₁ e)) (ι d t) (λ η → owk sw₃ (ι d (g η)))
  ι d (owk le t) = owk (λ e → le (proj₁ e) , proj₂ e) (ι d t)
  ι d (oΩ fe r ac h) = oΩ (λ e → fe (proj₁ e)) (pl d r) (λ e → admD d r (proj₂ e) (ac (proj₁ e))) (λ ξ z → owk asl (ι d (h ξ (cvU d r z))))
  ι d (oev f) = oev (λ ok e → ι d (f ok (proj₁ e)))

  record RestrO {k a : LI} (r : k <ᴸ a) (b : LI) : Set where
    constructor restrO
    field
      {repO} : LI
      eqO    : k ≈ repO
      ltO    : repO <ᴸ b
      trfO   : ∀ E → Adm E r → Adm E ltO
      backO  : ∀ {ξ} → O repO ξ → O k ξ
  open RestrO public

  trO   : ∀ {a b π} → a ≈ b → O a π → O b π
  tr⁻O  : ∀ {a b π} → a ≈ b → O b π → O a π
  resO  : ∀ {k a b} (r : k <ᴸ a) → a ≈ b → RestrO r b
  res⁻O : ∀ {k a b} (r : k <ᴸ b) → a ≈ b → RestrO r a

  trO e o0 = o0
  trO e (os a) = os (trO e a)
  trO e (ol F) = ol (λ n → trO e (F n))
  trO e (oi ac f) = oi ac (λ x → trO e (f x))
  trO e (oŝ c₀ t g) = oŝ c₀ (trO e t) (λ η d → trO e (g η d))
  trO e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (trO e o₀) (λ η d → trO e (o η d))
  trO e (oc₀ t g) = oc₀ (trO e t) (λ η → trO e (g η))
  trO e (ocl P pa t g) = ocl P pa (trO e t) (λ η → trO e (g η))
  trO e (owk le t) = owk le (trO e t)
  trO e (oΩ fe q ac h) = oΩ fe (ltO (resO q e)) (λ v → trfO (resO q e) _ (ac v)) (λ ξ z → trO e (h ξ (intoU q (backO (resO q e) (outU (ltO (resO q e)) z)))))
  trO e (oev f) = oev (λ ok d → trO e (f ok d))

  tr⁻O e o0 = o0
  tr⁻O e (os a) = os (tr⁻O e a)
  tr⁻O e (ol F) = ol (λ n → tr⁻O e (F n))
  tr⁻O e (oi ac f) = oi ac (λ x → tr⁻O e (f x))
  tr⁻O e (oŝ c₀ t g) = oŝ c₀ (tr⁻O e t) (λ η d → tr⁻O e (g η d))
  tr⁻O e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (tr⁻O e o₀) (λ η d → tr⁻O e (o η d))
  tr⁻O e (oc₀ t g) = oc₀ (tr⁻O e t) (λ η → tr⁻O e (g η))
  tr⁻O e (ocl P pa t g) = ocl P pa (tr⁻O e t) (λ η → tr⁻O e (g η))
  tr⁻O e (owk le t) = owk le (tr⁻O e t)
  tr⁻O e (oΩ fe q ac h) = oΩ fe (ltO (res⁻O q e)) (λ v → trfO (res⁻O q e) _ (ac v)) (λ ξ z → tr⁻O e (h ξ (intoU q (backO (res⁻O q e) (outU (ltO (res⁻O q e)) z)))))
  tr⁻O e (oev f) = oev (λ ok d → tr⁻O e (f ok d))

  resO zero      (s≈ e) = restrO e zero (λ _ _ → tt) (tr⁻O e)
  resO (suc r)   (s≈ e) with resO r e
  ... | restrO d l t b = restrO d (suc l) t b
  resO (lim n r) (l≈ h) with resO r (h n)
  ... | restrO d l t b = restrO d (lim n l) t b
  resO (fst r)   (o≈ h) with resO r (h one one (Lv.≅ᴵ-refl one))
  ... | restrO d l t b = restrO d (fst l) t b
  resO (bra η r) (o≈ h) with resO r (h η η (Lv.≅ᴵ-refl η))
  ... | restrO d l t b = restrO d (bra η l) (λ E u → Bel-resp {E} (o≈ h) (proj₁ u) , t E (proj₂ u)) b

  res⁻O zero      (s≈ e) = restrO (≈-sym e) zero (λ _ _ → tt) (trO e)
  res⁻O (suc r)   (s≈ e) with res⁻O r e
  ... | restrO d l t b = restrO d (suc l) t b
  res⁻O (lim n r) (l≈ h) with res⁻O r (h n)
  ... | restrO d l t b = restrO d (lim n l) t b
  res⁻O (fst r)   (o≈ h) with res⁻O r (h one one (Lv.≅ᴵ-refl one))
  ... | restrO d l t b = restrO d (fst l) t b
  res⁻O (bra η r) (o≈ h) with res⁻O r (h η η (Lv.≅ᴵ-refl η))
  ... | restrO d l t b = restrO d (bra η l) (λ E u → Bel-resp {E} (≈-sym (o≈ h)) (proj₁ u) , t E (proj₂ u)) b
```

## §7 尾巴与 $\Omega$

`Ω̇ᵖ k P`: $\Omega_k$, $k$ 在 $c$ 的位置 $P$. **键就从这里来**: `lcl` 处闭包的键就是当前位置; 分支 $\eta$ 下面的位置是 `P ⊙ bra η self`, 第一支是 `P ⊙ fst self`. 没有编号要选.

```agda
  floᵗ : Ordᴵ → Fᵗ
  floᵗ zero      = tz
  floᵗ (suc k)   = t₀ k
  floᵗ (lim f s) = tb (lim f s)

  cvᵗ : ∀ k {w} → Evt w (floᵗ k) → Simᴵ k (ℓ₀ w)
  cvᵗ zero      _ ()
  cvᵗ (suc k)   e = e
  cvᵗ (lim f s) e = e

  toᵗ : ∀ k {w} → Simᴵ k (ℓ₀ w) → Evt w (floᵗ k)
  toᵗ zero      σ = tt
  toᵗ (suc k)   σ = σ
  toᵗ (lim f s) σ = σ

  tl : ∀ {t k} (π : Fᵗ) → (∀ {w} → Evt w π → Simᴵ k (ℓ₀ w)) → Ordˢ k → O t π
  tl π cv Ord₊ˢ.zero = o0
  tl π cv (Ord₊ˢ.suc a) = os (tl π cv a)
  tl π cv (Ord₊ˢ.lim f) = ol (λ n → tl π cv (f n))
  tl π cv (Ord₊ˢ.limᵢ q f) = oi (λ e → cv e q) (λ x → tl π cv (f (intoˢ (<→◃ q) x)))
  tl {k = suc k′} π cv (Ord₊ˢ.up zero x) = owk (λ {w} v → toᵗ k′ {w} (λ q → cv v (suc q))) (tl (floᵗ k′) (λ {w} → cvᵗ k′ {w}) x)
  tl {k = lim f s} π cv (Ord₊ˢ.up (self n) x) = owk (λ {w} v → toᵗ (f n) {w} (λ q → cv v (lim n q))) (tl (floᵗ (f n)) (λ {w} → cvᵗ (f n) {w}) x)
  tl {k = zero} π cv (Ord₊ˢ.ŝ c₀ t₀′ g) = oĉ c₀ (toZ t₀′) (λ η e → toZ (g η e)) (tl π cv t₀′) (λ η e → tl π cv (g η e))
  tl {k = suc _} π cv (Ord₊ˢ.ŝ c₀ t₀′ g) = oŝ c₀ (tl π cv t₀′) (λ η e → tl π cv (g η e))
  tl {k = lim _ _} π cv (Ord₊ˢ.ŝ c₀ t₀′ g) = oŝ c₀ (tl π cv t₀′) (λ η e → tl π cv (g η e))
  tl π cv (Ord₊ˢ.ĉᴸ c₀ t₀′ g o₀ o) = oĉ c₀ t₀′ g (tl π cv o₀) (λ η e → tl π cv (o η e))

  idF : ∀ {w} → Evt w Fl₀ → Evt w Fl₀
  idF e = e

  pt : ∀ {π w} → Evt w π → Evt w (π ∪ tz)
  pt e = e , tt

  Ω̇₀ : O base Fl₀
  Ω̇₀ = oc₀ (tl Fl₀ (λ e q → proj₂ e q) (Ωˢ (suc zero))) (λ η → tl (Fl₀ ∪ t₀ η) (λ e q → proj₂ e (suc q)) (Ωˢ η))

  Ω̇ᵖ : ∀ k {π} (P : Cp k c) → (∀ {w} → Evt w π → Evt w Fl₀) → (∀ {w} → Evt w π → AdmC (Ε w) P) → O k π
  Ω̇ᵖ zero P fl ac = os o0
  Ω̇ᵖ base P fl ac = owk fl Ω̇₀
  Ω̇ᵖ (suc k) P fl ac = oΩ fl zero (λ _ → tt) (λ ξ z → owk (λ e → proj₁ e , tt) (ι ds z))
  Ω̇ᵖ (lim f) P fl ac = ol (λ n → owk pt (ι (dl n) (Ω̇ᵖ (f n) (P ⊙ lim n self) fl (λ {w} e → adm⊙ {Ε w} P (ac e) tt))))
  Ω̇ᵖ (lcl g) {π} P fl ac =
    ocl P ac (owk pt (ι df (Ω̇ᵖ (g one) (P ⊙ fst self) fl (λ {w} e → adm⊙ {Ε w} P (ac e) tt))))
      (λ η → owk (λ e → e , proj₂ e)
               (ι (db η P) (Ω̇ᵖ (g η) {π ∪ tk P η} (P ⊙ bra η self) (λ e → fl (proj₁ e))
                  (λ {w} e → adm⊙ {Ε w} P (ac (proj₁ e)) (S→B {Ε w} (proj₂ (proj₂ e)) , tt)))))
```

## §8 折叠

与 [UniformLvTree](UniformLvTree.lagda.md) §8 同形. 目标 $q$ 的 $\Omega$ 由位置 `toCp q` 给键.

```agda
  repᵒ : ∀ {k π} → O k π → ℕ → O k π
  repᵒ x zero          = o0
  repᵒ x (suc zero)    = x
  repᵒ x (suc (suc m)) = owk (λ e → e , e) (repᵒ x (suc m) ⊕ x)

  module Fold (cf : Cf c) where
    chainᵒ : ∀ {k π} (r : k <ᴸ c) → (∀ {w} → Evt w π → Evt w Fl₀) → (∀ {w} → Evt w π → Adm (Ε w) r) → (O k π → O k π) → ℕ → O k π
    chainᵒ {k} r fe ac f zero    = Ω̇ᵖ k (toCp r) fe (λ {w} e → admTo {Ε w} r (ac e))
    chainᵒ r fe ac f (suc n) = f (chainᵒ r fe ac f n)

    ψᵒ : ∀ {t χ} (q : t <ᴸ c) → (∀ {w} → Evt w χ → Evt w Fl₀) → (∀ {w} → Evt w χ → Adm (Ε w) q) → ∀ {π} → O c π → O t (χ ∪ π)
    ψΩ : ∀ {t χ k π} (q : t <ᴸ c) (fl : ∀ {w} → Evt w χ → Evt w Fl₀) (aq : ∀ {w} → Evt w χ → Adm (Ε w) q)
         (fe : ∀ {w} → Evt w π → Evt w Fl₀) (r : k <ᴸ c) (ac : ∀ {w} → Evt w π → Adm (Ε w) r) (h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)) →
         Tri r q → O t (χ ∪ π)
    chR : ∀ {χ k π} (fl : ∀ {w} → Evt w χ → Evt w Fl₀) (fe : ∀ {w} → Evt w π → Evt w Fl₀) (r : k <ᴸ c) (ac : ∀ {w} → Evt w π → Adm (Ε w) r) (h : ∀ ξ → Us c r ξ → O c (ξ ∪ π)) → ℕ → O k (χ ∪ π)

    ψᵒ {t} q fl aq o0 = Ω̇ᵖ t (toCp q) (λ e → fl (proj₁ e)) (λ {w} e → admTo {Ε w} q (aq (proj₁ e)))
    ψᵒ q fl aq (os a) = ol (repᵒ (ψᵒ q fl aq a))
    ψᵒ q fl aq (ol F) = ol (λ n → ψᵒ q fl aq (F n))
    ψᵒ q fl aq (oi ac f) = oi (λ e → ac (proj₂ e)) (λ x → ψᵒ q fl aq (f x))
    ψᵒ q fl aq (oŝ c₀ x g) = oŝ c₀ (ψᵒ q fl aq x) (λ η e → ψᵒ q fl aq (g η e))
    ψᵒ q fl aq (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψᵒ q fl aq o₀) (λ η e → ψᵒ q fl aq (o η e))
    ψᵒ q fl aq (oc₀ x g) = oc₀ (ψᵒ q fl aq x) (λ η → owk asr (ψᵒ q fl aq (g η)))
    ψᵒ q fl aq (ocl P pa x g) = ocl P (λ e → pa (proj₂ e)) (ψᵒ q fl aq x) (λ η → owk asr (ψᵒ q fl aq (g η)))
    ψᵒ q fl aq (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ q fl aq x)
    ψᵒ q fl aq (oev f) = oev (λ ok e → ψᵒ q fl aq (f ok (proj₂ e)))
    ψᵒ q fl aq (oΩ fe r ac h) =
      oev (λ {w} ok e → ψΩ q fl aq fe r ac h (<-dec (proj₁ cf) (proj₂ cf) r q (Ε w) (proj₂ ok) (ac (proj₂ e)) (aq (proj₁ e))))

    ψΩ q fl aq fe r ac h (tlt (viaᴸ d s u)) =
      oΩ (λ e → fl (proj₁ e)) s (λ {w} e → u (Ε w) (ac (proj₂ e))) (λ ξ y → owk swp (ψᵒ q fl aq (h ξ (intoU r (tr⁻O d (outU s y))))))
    ψΩ {χ = χ} {π = π} q fl aq fe r ac h (tgt _) = ol (λ n → owk (λ e → proj₁ e , (e , proj₂ e)) (ψᵒ q fl aq (h (χ ∪ π) (intoU r (chR fl fe r ac h n)))))
    ψΩ {χ = χ} {π = π} q fl aq fe r ac h (teq _) = ol (λ n → owk (λ e → proj₁ e , (e , proj₂ e)) (ψᵒ q fl aq (h (χ ∪ π) (intoU r (chR fl fe r ac h n)))))

    chR {χ} {k} {π} fl fe r ac h = chainᵒ r (λ e → fl (proj₁ e)) (λ e → ac (proj₂ e)) (λ z → owk (λ e → proj₂ e , (e , proj₂ e)) (ψᵒ r fe ac (h (χ ∪ π) (intoU r z))))

    ψ̄ : ∀ {π} → O c π → Runᵗ π
    ψ̄ o0 ok e p = Ωˢ _
    ψ̄ (os a) = sucᵗ (ψ̄ a)
    ψ̄ (ol F) = limᵗ (λ n → ψ̄ (F n))
    ψ̄ (oi ac f) = limᵢᵗ ac (λ x → ψ̄ (f x))
    ψ̄ (oŝ c₀ t g) = ŝᵗ c₀ (ψ̄ t) (λ η e → ψ̄ (g η e))
    ψ̄ (oĉ c₀ z zg o₀ o) = ĉᵗ c₀ z zg (ψ̄ o₀) (λ η e → ψ̄ (o η e))
    ψ̄ (oc₀ t g) = cl₀ (ψ̄ t) (λ η → ψ̄ (g η))
    ψ̄ (ocl P pa t g) = cloK (proj₁ cf) (proj₂ cf) P pa (ψ̄ t) (λ η → ψ̄ (g η))
    ψ̄ (owk le x) = wkᵗ le (ψ̄ x)
    ψ̄ {π} (oΩ fe r ac h) =
      limᵗ (λ n → wkᵗ (λ v → v , v)
             (ψ̄ (h π (intoU r (chainᵒ r fe ac (λ z → owk (λ v → v , (v , v)) (ψᵒ r fe ac (h π (intoU r z)))) n)))))
    ψ̄ (oev f) ok ev p = ψ̄ (f ok ev) ok ev p
```

## §9 封闭的计值

```agda
-- $\psi_0(\Omega_L)$: 任何带证书的层号. 一个定义, 没有标签, 没有对阶段的归纳.
T : (L : LI) → Cf L → Over.Runᵗ L (Over.Fl₀ L)
T L cf = Over.Fold.ψ̄ L cf (Over.Ω̇ᵖ L L Cp.self (λ e → e) (λ _ → tt))

w₀ : Wd
w₀ = wd (suc zero) (∅ (suc zero))

ok₀ : Wok w₀
ok₀ = zero , zero

T₀ : (L : LI) → Cf L → Ordˢ zero
T₀ L cf = T L cf ok₀ (tt , (λ q → q)) zero
```
