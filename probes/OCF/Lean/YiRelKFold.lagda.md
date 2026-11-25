# 前缀 Ω_{ℓ₀} 下对 k 一般的折叠引理

验收文件. 编译定理 (模块 `FoldK ℓ₀ Tg`, 条件于接口 `Pf K Φ`): `Fold`: 输入层 K 上 `Rel K X η`、目标层 t (Tg t), 推出 ψ_q(Ω_{ℓ₀} ⊕_σ X) 在第 t 层不高于 `Φ t η`; 一条定理对一切 K, t, 一切 Sim σ 与 `q ≅ᴵ ℓk t`. 是 [YiStepFold2](YiStepFold2.lagda.md) 的 `Fold22`, `Fold21`, `fold2²` 及其部件的一般形.
接口 `Pf` 收树一侧的事实 (前缀的单调与后继, 每个结点在每个目标层上保留或折叠, 对角线 `Z`), 不陈述它们对一般 k 成立; k = 2 的实例在 [YiRelKTwo](YiRelKTwo.lagda.md). 另有 `TRC-all` (关系对层间搬运封闭). 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRelKFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiLeanValRel using (TRC; module Back)
open import OCF.Align.YiLvVal2 using (s≅⁻; l≅⁻)
import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using () renaming (iter to iterᴸ)
open import OCF.Lean.YiRelK
```

## 1 关系对层间搬运封闭

照主线 [YiLeanValRel](YiLeanValRel.lagda.md) §4, 多 `dg` 与 `≅⊴` 两种情形.

```agda
TR0 : TRC R0
TR0 = record { tr⁻ᴿ = go⁻ ; trᴿ = go }
  where
  go⁻ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → R0 y η → R0 (L.tr⁻ e y) η
  go⁻ L.z≅ {y} q = ≼-trans (≅→≼ (L.tr⁻-≅ L.z≅ (L.≅-refl⁰ y))) q
  go : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → R0 y η → R0 (L.tr e y) η
  go L.z≅ {y} q = ≼-trans (≅→≼ (L.tr-≅ L.z≅ (L.≅-refl⁰ y))) q

bself⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {y} → y L.≅ y →
  L.Restr.back (L.res⁻ q e) y L.≅ L.Restr.back (L.res⁻ q e) y
bself⁻ q e s = L.≅-trans (L.back⁻-≅ q e s) (L.≅-sym (L.back⁻-≅ q e s))

bself : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {y} → y L.≅ y →
  L.Restr.back (L.res q e) y L.≅ L.Restr.back (L.res q e) y
bself q e s = L.≅-trans (L.back-≅ q e s) (L.≅-sym (L.back-≅ q e s))

module TRG (m : ℕ) (KT : TRC (Rel m)) (ST : ∀ r → TRC (Hyp (suc m) r)) where
  TR⁻ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → Rel (suc m) y η → Rel (suc m) (L.tr⁻ e y) η
  TR⁺ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → Rel (suc m) y η → Rel (suc m) (L.tr e y) η

  TR⁻ e z⊴ = z⊴
  TR⁻ e (s⊴s p) = s⊴s (TR⁻ e p)
  TR⁻ e (⊴s p) = ⊴s (TR⁻ e p)
  TR⁻ e (⊴l n p) = ⊴l n (TR⁻ e p)
  TR⁻ e (l⊴ h) = l⊴ (λ n → TR⁻ e (h n))
  TR⁻ e (⊴b p) = ⊴b (TR⁻ e p)
  TR⁻ e (nd {r = s} {g = g} {p = q} {f = f} e₀ h) =
    nd (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) e₀) (λ y a r t →
      subst (λ w → Rel (suc m) (L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w)))) (g a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a (Back.back⁻ᴿ (ST s) q e r) (bself⁻ q e t))))
  TR⁻ e (nt {p = q} {f = f} e₀ h) =
    nt (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) e₀) (λ y a r t →
      subst (λ w → Rel (suc m) (L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w)))) (G.em tt a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a (Back.back⁻ᴿ KT q e r) (bself⁻ q e t))))
  TR⁻ e (em q) = em (TRC.tr⁻ᴿ KT e q)
  TR⁻ (L.s≅ e) (u⊴ {r = L.zero} p) = u⊴ (TR⁻ e p)
  TR⁻ (L.l≅ h) (u⊴ {r = L.self n} p) = u⊴ (TR⁻ (h n) p)
  TR⁻ e (dg z h) = dg z (λ n a c → TR⁻ e (h n a c))
  TR⁻ e (≅⊴ d p) = ≅⊴ (L.≅-tr⁻ e (L.tr⁻-≅ e d)) (TR⁻ e p)

  TR⁺ e z⊴ = z⊴
  TR⁺ e (s⊴s p) = s⊴s (TR⁺ e p)
  TR⁺ e (⊴s p) = ⊴s (TR⁺ e p)
  TR⁺ e (⊴l n p) = ⊴l n (TR⁺ e p)
  TR⁺ e (l⊴ h) = l⊴ (λ n → TR⁺ e (h n))
  TR⁺ e (⊴b p) = ⊴b (TR⁺ e p)
  TR⁺ e (nd {r = s} {g = g} {p = q} {f = f} e₀ h) =
    nd (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) e₀) (λ y a r t →
      subst (λ w → Rel (suc m) (L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w)))) (g a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a (Back.backᴿ (ST s) q e r) (bself q e t))))
  TR⁺ e (nt {p = q} {f = f} e₀ h) =
    nt (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) e₀) (λ y a r t →
      subst (λ w → Rel (suc m) (L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w)))) (G.em tt a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a (Back.backᴿ KT q e r) (bself q e t))))
  TR⁺ e (em q) = em (TRC.trᴿ KT e q)
  TR⁺ (L.s≅ e) (u⊴ {r = L.zero} p) = u⊴ (TR⁺ e p)
  TR⁺ (L.l≅ h) (u⊴ {r = L.self n} p) = u⊴ (TR⁺ (h n) p)
  TR⁺ e (dg z h) = dg z (λ n a c → TR⁺ e (h n a c))
  TR⁺ e (≅⊴ d p) = ≅⊴ (L.≅-tr e (L.tr-≅ e d)) (TR⁺ e p)

  trc : TRC (Rel (suc m))
  trc = record { tr⁻ᴿ = TR⁻ ; trᴿ = TR⁺ }

TRC-all : ∀ k → TRC (Rel k)
TRC-H : ∀ k r → TRC (Hyp k r)
TRC-all zero = TR0
TRC-all (suc m) = TRG.trc m (TRC-all m) (TRC-H (suc m))
TRC-H (suc m) (inj₁ _) = TRC-all m
TRC-H (suc m) (inj₂ r) = TRC-H m r
```

## 2 对一切目标层 (含第 0 层) 的规则

```agda
Rel-≅ : ∀ t {ℓ} {x y : L.Ordᶜ ℓ} {η} → x L.≅ y → Rel t y η → Rel t x η
Rel-≅ zero {L.zero} e q = ≼-trans (≅→≼ e) q
Rel-≅ (suc m) e q = ≅⊴ e q

Rel-ll : ∀ t {ℓ} {F : ℕ → L.Ordᶜ ℓ} {η} → (∀ n → Rel t (F n) η) → Rel t (L.lim F) η
Rel-ll zero {L.zero} h = l≼ h
Rel-ll zero {L.suc _} h = ⊥-elim (h 0)
Rel-ll zero {L.lim _ _} h = ⊥-elim (h 0)
Rel-ll (suc m) h = l⊴ h

Rel-+ˡt : ∀ t θ {ℓ} {x : L.Ordᶜ ℓ} {η} → Rel t x η → Rel t x (plus (Lk t) θ η)
Rel-+ˡt zero θ {L.zero} {η = η} q = NA.plus≽ θ η q
Rel-+ˡt (suc m) θ q = Rel-+ˡ m θ q

Rel-ωt : ∀ t {i} → i ≅ᴵ ℓk t → {A : L.Ordᶜ i} {β : Raw (Lk t)} → A L.≅ A → Rel t A β →
  Rel t (L.lim (iterᴸ (A L.+_) L.zero)) (succ (Lk t) β)
Rel-ωt zero L.z≅ {β = β} s q = l≼ λ where
  zero → z≼
  (suc n) → ≼l n (NA.read-copies β q n)
Rel-ωt (suc m) _ s q = Rel-ω m s q

Ω⊴top′ : ∀ j {i} → i ≅ᴵ ℓk j → Rel j (L.Ω i) G.top
Ω⊴top′ zero L.z≅ = s≼s z≼
Ω⊴top′ (suc m) (L.s≅ e) = nt e (λ y a q t → u⊴ (em q))

z< : ∀ m → L.zero <ᴵ ℓk (suc m)
z< zero = L.zero
z< (suc m) = L.suc (z< m)

zero≺ : ∀ m → ℓk 0 ≺ᴵ ℓk (suc m)
zero≺ m = L.via L.z≅ (z< m)
```

## 3 `≅` 的反演

```agda
upˡ⁻ : ∀ {k ℓ ℓ′} {r : k L.◃₁ ℓ} {x : L.U k (L.◃₁→◃ r)} {b : L.Ordᶜ ℓ′} → L.up r x L.≅ b →
  L.out (L.◃₁→◃ r) x L.≅ b
upˡ⁻ {r = L.zero} (L.upˡ e) = e
upˡ⁻ {r = L.self n} (L.upˡ e) = e
upˡ⁻ {r = L.zero} (L.upʳ {r = L.zero} e) = L.upʳ {r = L.zero} (upˡ⁻ e)
upˡ⁻ {r = L.zero} (L.upʳ {r = L.self n} e) = L.upʳ {r = L.self n} (upˡ⁻ e)
upˡ⁻ {r = L.self m} (L.upʳ {r = L.zero} e) = L.upʳ {r = L.zero} (upˡ⁻ e)
upˡ⁻ {r = L.self m} (L.upʳ {r = L.self n} e) = L.upʳ {r = L.self n} (upˡ⁻ e)

upʳ⁻ : ∀ {k ℓ ℓ′} {r : k L.◃₁ ℓ} {y : L.U k (L.◃₁→◃ r)} {a : L.Ordᶜ ℓ′} → a L.≅ L.up r y →
  a L.≅ L.out (L.◃₁→◃ r) y
upʳ⁻ = λ e → L.≅-sym (upˡ⁻ (L.≅-sym e))

u≅⁻ : ∀ {k ℓ} {r : k L.◃₁ ℓ} {y : L.U k (L.◃₁→◃ r)} → L.up r y L.≅ L.up r y →
  L.out (L.◃₁→◃ r) y L.≅ L.out (L.◃₁→◃ r) y
u≅⁻ e = upʳ⁻ (upˡ⁻ e)

lᵢself : ∀ {i ℓ} {p : i <ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} → L.limᵢ p f L.≅ L.limᵢ p f →
  ∀ y → y L.≅ y → f (L.into (L.<→◃ p) y) L.≅ f (L.into (L.<→◃ p) y)
lᵢself {p = p} (L.lᵢ≅ e h) y s = h y y (L.≅→R (L.<→◃ p) s)
```

## 4 结点的路径

`Path K j`: 从第 K 层的根往下走到一个第 j 层的位置 (每步添 `inj₂`); `bld π` 是那里造结点的办法. 层号 j′ 的结点 `bld π (inj₁ tt) g` 的分支定义域定义性地是 `Raw (Lk j′)`, 所以接口只对这种结点陈述.

```agda
data Path (K : ℕ) : ℕ → Set where
  here : Path K K
  there : ∀ {j} → Path K (suc j) → Path K j

bld : ∀ {K j} → Path K j → Bld (Lk K) (Lk j)
bld here = G.lc
bld (there π) r = bld π (inj₂ r)
```

## 5 接口与折叠引理

`Pf K Φ`: `Φ t` 是第 K 层的树经前缀与第 t 层的折叠之后的像. 字段: 对角线 `Z` (对 `≅ᴵ ℓk t` 的一切参照层号与证明), 单调 `mΦ`, 后继 `sΦ`, 结点保留 `kΦ` (层号在目标之下) 与折叠 `fΦ` (链在结点自己的层上, 用 `Φ j`), 层号 0 槽位上对角规则的保留 `dkΦ` 与折叠 `dfΦ`, `top` 的形状 `tp`, 孩子层 `dn` (`Φ` 与 `em` 复合).

```agda
module FoldK (ℓ₀ : L.Ordᴵ) (Tg : ℕ → Set) where

  TopF : (K : ℕ) → (∀ t → Raw (Lk K) → Raw (Lk t)) → Set
  TopF zero Φ = ∀ t → Tg t → Cp (Lk t) (succ (Lk t) (Φ t G.zero)) (Φ t G.top)
  TopF (suc K) Φ = ∀ t → Φ t G.top ≡ Φ t (G.lc (inj₁ tt) (λ a → G.em tt a))

  record PfL (K : ℕ) (Φ : ∀ t → Raw (Lk K) → Raw (Lk t)) (D : Set) : Set where
    field
      Z : ∀ t → Tg t → ∀ {i} (q : i <ᴵ ℓ₀) → i ≅ᴵ ℓk t → ∀ η →
        Rel t (L.ψ q (λ r → r) (L.Ω ℓ₀)) (Φ t η)
      mΦ : ∀ t → Tg t → ∀ {a b} → Cp (Lk K) a b → Cp (Lk t) (Φ t a) (Φ t b)
      sΦ : ∀ t → Tg t → ∀ η → Cp (Lk t) (succ (Lk t) (Φ t η)) (Φ t (G.suc η))
      tgN : ∀ {j} → Path K (suc j) → Tg j
      kΦ : ∀ t → Tg t → ∀ {j} (π : Path K (suc j)) → ℓk j ≺ᴵ ℓk t →
        ∀ {i ℓ} {p : i <ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} {g : Raw (Lk j) → Raw (Lk K)} → i ≅ᴵ ℓk j →
        (∀ (y : L.Ordᶜ i) a → Rel j y a → y L.≅ y → Rel t (f (L.into (L.<→◃ p) y)) (Φ t (g a))) →
        Rel t (L.limᵢ p f) (Φ t (bld π (inj₁ tt) g))
      fΦ : ∀ t → Tg t → ∀ {j} (π : Path K (suc j)) → ¬ (ℓk j ≺ᴵ ℓk t) →
        ∀ {g : Raw (Lk j) → Raw (Lk K)} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
        (∀ n → Rel t (F n) (Φ t (g (chain (Lk j) (λ a → Φ j (g a)) n)))) →
        Rel t (L.lim F) (Φ t (bld π (inj₁ tt) g))
      dkΦ : ∀ m → Tg (suc m) → ∀ {r} (z : Z0 K r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
        (∀ n a → Cp zero thr a → Rel (suc m) (F n) (Φ (suc m) (g (toA z a)))) →
        Rel (suc m) (L.lim F) (Φ (suc m) (G.lc r g))
      dfΦ : ∀ {r} (z : Z0 K r) {g} {ℓ} {F : ℕ → L.Ordᶜ ℓ} →
        (∀ n a → Cp zero thr a → Rel zero (F n) (Φ zero (g (toA z a)))) →
        Rel zero (L.lim F) (Φ zero (G.lc r g))
      tp : TopF K Φ
      dn : D
  open PfL public

  Pf : (K : ℕ) → (∀ t → Raw (Lk K) → Raw (Lk t)) → Set
  Pf zero Φ = PfL zero Φ ⊤
  Pf (suc K) Φ = PfL (suc K) Φ (Pf K (λ t a → Φ t (G.em tt a)))

  ρ : ∀ {i} (q : i <ᴵ ℓ₀) {ℓ} (σ : L.Simᴵ ℓ ℓ₀) → L.Ordᶜ ℓ → L.Ordᶜ i
  ρ q σ X = L.ψ q (λ r → r) (L.add (L.Ω ℓ₀) σ X)

  ρ≅ : ∀ {i} (q : i <ᴵ ℓ₀) {ℓ} (σ : L.Simᴵ ℓ ℓ₀) {X Y : L.Ordᶜ ℓ} → X L.≅ Y → ρ q σ X L.≅ ρ q σ Y
  ρ≅ q σ e = L.ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (L.≅ᴵ-refl _)
    (L.add-≅ {σ = σ} {σ′ = σ} (L.Ω-refl ℓ₀) e)
```

结点: 参照一侧按 `<ᴵ-dec` 分三种; 穿透时用 `kΦ`, 分支先 `tr⁻` 搬回 (`TRC-all`); 另两种用 `fΦ`, 两条链同步 (参照从 `Ω i₀` 起每步 `ψ_{p′}`, 树从 `top` 起每步加 `Φ j`). 递归的结果以参数 `rec` 传入.

```agda
  module NodeR {K Φ D} (P : PfL K Φ D) {j} (π : Path K (suc j)) t (tg : Tg t) {i} (q : i <ᴵ ℓ₀)
    (ei : i ≅ᴵ ℓk t) {i₀} (p′ : i₀ <ᴵ ℓ₀) (f′ : L.U i₀ (L.<→◃ p′) → L.Ordᶜ ℓ₀)
    {g : Raw (Lk j) → Raw (Lk K)} (e₀ : i₀ ≅ᴵ ℓk j)
    (sf : ∀ (y : L.Ordᶜ i₀) → y L.≅ y → f′ (L.into (L.<→◃ p′) y) L.≅ f′ (L.into (L.<→◃ p′) y))
    (rec : ∀ t′ → Tg t′ → ∀ {i′} (q′ : i′ <ᴵ ℓ₀) → i′ ≅ᴵ ℓk t′ → ∀ (y : L.Ordᶜ i₀) a → Rel j y a → y L.≅ y →
      Rel t′ (L.ψ q′ (λ r → r) (f′ (L.into (L.<→◃ p′) y))) (Φ t′ (g a))) where

    c : ℕ → L.Ordᶜ i₀
    c = iterᴸ (λ x → L.ψ p′ (λ r → r) (f′ (L.into (L.<→◃ p′) x))) (L.Ω i₀)

    δ : ℕ → Raw (Lk j)
    δ = chain (Lk j) (λ a → Φ j (g a))

    sc : ∀ n → c n L.≅ c n
    sc zero = L.Ω-refl i₀
    sc (suc n) = L.ψ-≅ {p = p′} {σ = λ r → r} {p′ = p′} {σ′ = λ r → r} (L.≅ᴵ-refl _) (sf (c n) (sc n))

    sync : ∀ n → Rel j (c n) (δ n)
    sync zero = Ω⊴top′ j e₀
    sync (suc n) = Rel-+ˡt j (δ n) (rec j (tgN P π) p′ e₀ (c n) (δ n) (sync n) (sc n))

    lt : ∀ {i′} → i₀ ≅ᴵ i′ → i′ <ᴵ i → ℓk j ≺ᴵ ℓk t
    lt e r = L.≺ᴵ-respʳ (L.≺ᴵ-respˡ (L.≅ᴵ-sym e₀) (L.via e r)) ei

    nb : i ≺ᴵ i₀ → ¬ (ℓk j ≺ᴵ ℓk t)
    nb s u = L.≺ᴵ-irrefl (L.≺ᴵ-trans (L.≺ᴵ-respˡ e₀ (L.≺ᴵ-respʳ u (L.≅ᴵ-sym ei))) s)

    nc : i₀ ≅ᴵ i → ¬ (ℓk j ≺ᴵ ℓk t)
    nc d u = L.≺ᴵ-irrefl (L.≺ᴵ-respˡ e₀ (L.≺ᴵ-respʳ u (L.≅ᴵ-sym (L.≅ᴵ-trans d ei))))

    fol : ∀ n → Rel t (L.ψ q (λ r → r) (f′ (L.into (L.<→◃ p′) (c n)))) (Φ t (g (δ n)))
    fol n = rec t tg q ei (c n) (δ n) (sync n) (sc n)

    result : Rel t (L.ψ q (λ r → r) (L.limᵢ p′ f′)) (Φ t (bld π (inj₁ tt) g))
    result with L.<ᴵ-dec p′ q
    ... | injᵃ (L.via e r) = kΦ P t tg π (lt e r) (L.≅ᴵ-trans (L.≅ᴵ-sym e) e₀) (λ y a hy sy →
      subst (λ w → Rel t (L.ψ q (λ r → r) (f′ (L.into (L.<→◃ p′) (L.tr⁻ e w)))) (Φ t (g a)))
        (sym (L.out-into (L.<→◃ r) y))
        (rec t tg q ei (L.tr⁻ e y) a (TRC.tr⁻ᴿ (TRC-all j) e hy) (L.≅-tr⁻ e (L.tr⁻-≅ e sy))))
    ... | injᵇ s = fΦ P t tg π (nb s) fol
    ... | injᶜ d = fΦ P t tg π (nc d) fol

  nodeF : ∀ {K Φ D} (P : PfL K Φ D) {J} (π : Path K J) (r : Pre (Lk J)) t → Tg t → ∀ {i} (q : i <ᴵ ℓ₀) →
    i ≅ᴵ ℓk t → ∀ {i₀} (p′ : i₀ <ᴵ ℓ₀) (f′ : L.U i₀ (L.<→◃ p′) → L.Ordᶜ ℓ₀) {g} → i₀ ≅ᴵ lvI J r →
    (∀ (y : L.Ordᶜ i₀) → y L.≅ y → f′ (L.into (L.<→◃ p′) y) L.≅ f′ (L.into (L.<→◃ p′) y)) →
    (∀ t′ → Tg t′ → ∀ {i′} (q′ : i′ <ᴵ ℓ₀) → i′ ≅ᴵ ℓk t′ → ∀ (y : L.Ordᶜ i₀) a → Hyp J r y a → y L.≅ y →
      Rel t′ (L.ψ q′ (λ r → r) (f′ (L.into (L.<→◃ p′) y))) (Φ t′ (g a))) →
    Rel t (L.ψ q (λ r → r) (L.limᵢ p′ f′)) (Φ t (bld π r g))
  nodeF P {suc J} π (inj₁ _) t tg q ei p′ f′ e₀ sf rec = NodeR.result P π t tg q ei p′ f′ e₀ sf rec
  nodeF P {suc J} π (inj₂ r) = nodeF P (there π) r
```

折叠引理. 第 0 层的输入按值归纳; 其余各层按关系归纳, 嵌入时换到 `dn`.

```agda
  FoldZ : ∀ {Φ} (P : Pf zero Φ) t → Tg t → ∀ {i} (q : i <ᴵ ℓ₀) → i ≅ᴵ ℓk t → (σ : L.Simᴵ L.zero ℓ₀) →
    ∀ {X b : L.Ordᶜ L.zero} → X ≼ b → ∀ a → b ≡ NA.read a → Rel t (ρ q σ X) (Φ t a)
  FoldZ P t tg q ei σ z≼ a e = Z P t tg q ei a
  FoldZ P t tg q ei σ {L.suc X} (s≼s d) (G.suc a) refl =
    Rel-cp t (Rel-ωt t ei (ρ≅ q σ (L.≅-refl⁰ X)) (FoldZ P t tg q ei σ d a refl)) (sΦ P t tg a)
  FoldZ P t tg q ei σ {L.suc X} (s≼s d) G.top refl =
    Rel-cp t (Rel-ωt t ei (ρ≅ q σ (L.≅-refl⁰ X)) (FoldZ P t tg q ei σ d G.zero refl)) (tp P t tg)
  FoldZ P t tg q ei σ (≼l n d) (G.lim f) refl =
    Rel-cp t (FoldZ P t tg q ei σ d (f n) refl) (mΦ P t tg (inj₂ (n , inj₁ refl)))
  FoldZ P t tg q ei σ (l≼ h) a e = Rel-ll t (λ n → FoldZ P t tg q ei σ (h n) a e)
  FoldZ P t tg q ei σ (≼i {p = ()} x ex d) a e
  FoldZ P t tg q ei σ (i≼ {p = ()} h) a e
  FoldZ P t tg q ei σ (≼u {r = ()} d) a e
  FoldZ P t tg q ei σ (u≼ {r = ()} d) a e

  Fold : ∀ K {Φ} (P : Pf K Φ) t → Tg t → ∀ {i} (q : i <ᴵ ℓ₀) → i ≅ᴵ ℓk t →
    ∀ {ℓ} (σ : L.Simᴵ ℓ ℓ₀) {X : L.Ordᶜ ℓ} {η} → Rel K X η → X L.≅ X → Rel t (ρ q σ X) (Φ t η)
  FoldS : ∀ K {Φ} (P : Pf (suc K) Φ) t → Tg t → ∀ {i} (q : i <ᴵ ℓ₀) → i ≅ᴵ ℓk t →
    ∀ {ℓ} (σ : L.Simᴵ ℓ ℓ₀) {X : L.Ordᶜ ℓ} {η} → Rel (suc K) X η → X L.≅ X → Rel t (ρ q σ X) (Φ t η)

  Fold zero P t tg q ei {L.zero} σ {η = η} d s = FoldZ P t tg q ei σ d η refl
  Fold (suc K) P = FoldS K P

  FoldS K P t tg q ei σ {η = η} z⊴ s = Z P t tg q ei η
  FoldS K P t tg q ei σ {η = G.suc η} (s⊴s d) s =
    Rel-cp t (Rel-ωt t ei (ρ≅ q σ (s≅⁻ s)) (FoldS K P t tg q ei σ d (s≅⁻ s))) (sΦ P t tg η)
  FoldS K P t tg q ei σ (⊴s d) s = Rel-cp t (FoldS K P t tg q ei σ d s) (mΦ P t tg (inj₂ (inj₁ refl)))
  FoldS K P t tg q ei σ (⊴l n d) s = Rel-cp t (FoldS K P t tg q ei σ d s) (mΦ P t tg (inj₂ (n , inj₁ refl)))
  FoldS K P t tg q ei σ (l⊴ h) s = Rel-ll t (λ n → FoldS K P t tg q ei σ (h n) (l≅⁻ s n))
  FoldS K P t tg q ei σ (⊴b d) s = Rel-cp t (FoldS K P t tg q ei σ d s) (mΦ P t tg (inj₂ (inj₁ refl)))
  FoldS K {Φ} P t tg q ei σ (nd {r = r} {g = g} {p = p} {f = f} e₀ h) s =
    nodeF P here r t tg q ei (σ p) (λ w → L.add (L.Ω ℓ₀) σ (f (L.coe (L.<→◃ (σ p)) (L.<→◃ p) w))) e₀
      (λ y sy → subst (λ w → L.add (L.Ω ℓ₀) σ (f (L.into (L.<→◃ p) w)) L.≅ L.add (L.Ω ℓ₀) σ (f (L.into (L.<→◃ p) w)))
        (sym (L.out-into (L.<→◃ (σ p)) y)) (L.add-≅ {σ = σ} {σ′ = σ} (L.Ω-refl ℓ₀) (lᵢself s y sy)))
      (λ t′ tg′ q′ ei′ y a hy sy →
        subst (λ w → Rel t′ (ρ q′ σ (f (L.into (L.<→◃ p) w))) (Φ t′ (g a)))
          (sym (L.out-into (L.<→◃ (σ p)) y)) (FoldS K P t′ tg′ q′ ei′ σ (h y a hy sy) (lᵢself s y sy)))
  FoldS K {Φ} P t tg q ei σ (nt {p = p} {f = f} e₀ h) s =
    subst (λ w → Rel t (ρ q σ (L.limᵢ p f)) w) (sym (tp P t))
      (nodeF P here (inj₁ tt) t tg q ei (σ p) (λ w → L.add (L.Ω ℓ₀) σ (f (L.coe (L.<→◃ (σ p)) (L.<→◃ p) w)))
        {g = λ a → G.em tt a} e₀
        (λ y sy → subst (λ w → L.add (L.Ω ℓ₀) σ (f (L.into (L.<→◃ p) w)) L.≅ L.add (L.Ω ℓ₀) σ (f (L.into (L.<→◃ p) w)))
          (sym (L.out-into (L.<→◃ (σ p)) y)) (L.add-≅ {σ = σ} {σ′ = σ} (L.Ω-refl ℓ₀) (lᵢself s y sy)))
        (λ t′ tg′ q′ ei′ y a hy sy →
          subst (λ w → Rel t′ (ρ q′ σ (f (L.into (L.<→◃ p) w))) (Φ t′ (G.em tt a)))
            (sym (L.out-into (L.<→◃ (σ p)) y)) (FoldS K P t′ tg′ q′ ei′ σ (h y a hy sy) (lᵢself s y sy))))
  FoldS K P t tg q ei σ (em d) s = Fold K (dn P) t tg q ei σ d s
  FoldS K P t tg q ei σ (u⊴ {r = L.zero} d) s = FoldS K P t tg q ei (λ c → σ (L.suc c)) d (u≅⁻ s)
  FoldS K P t tg q ei σ (u⊴ {r = L.self n} d) s = FoldS K P t tg q ei (λ c → σ (L.lim n c)) d (u≅⁻ s)
  FoldS K P zero tg q ei σ (dg z h) s = dfΦ P z (λ n a c → FoldS K P zero tg q ei σ (h n a c) (l≅⁻ s n))
  FoldS K P (suc m) tg q ei σ (dg z h) s =
    dkΦ P m tg z (λ n a c → FoldS K P (suc m) tg q ei σ (h n a c) (l≅⁻ s n))
  FoldS K P t tg q ei σ (≅⊴ e d) s = Rel-≅ t (ρ≅ q σ e) (FoldS K P t tg q ei σ d (L.≅-trans (L.≅-sym e) e))
```
