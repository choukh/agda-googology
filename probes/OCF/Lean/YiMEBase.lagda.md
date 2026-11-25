# 值接口的记号直连实例 (一): 关系与出口

> 验收文件 (读记号). 判决: 编译定理, 无前提. 合法块 (`YiLegBlock`) 各层的树与记号项之间的下界关系 `Mᴰ` (按层号的签名取参数: 槽位的低层关系, 孩子层的关系, 槽位允许的记号下标); 第 0 层的实例 `M⁰` 满足 `YiAbsSim.Sim` 的全部前提 (`r1⁰`, `rω⁰`, `strict⁰`, `weak⁰`), 所以 `lower⁰ : M⁰ t x → (h : HC t) → Rt h ≼ read x`.
> `Sim` 的实填取 ψ 为恒等, 源层就是第 0 层的树: 记号的规则 4 把 ψ₀(b+1) 的基本列写成和, 和不是单棵源树的折叠. 折叠保持因此不在 `Sim` 的前提里, 而在 "闭项与记号项有 `M⁰`" 的证明里 (见 `YiMEAnchor`).
> 不给出什么: 高层的 `Mᴰ` 实例与折叠保持不在这里; 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMEBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
import OCF.Align.EboLeanDef as E
open E using (HC; cof; c0; c1; cω; cΩ; pred; fsn; fsT; 𝟏)
open import OCF.Align.EboLeanTree using (tree)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ⊑→≼)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiAbsSimInst using (lower′)
```

## 第 0 层的读回与第一位置序的自反闭包

```agda
T₀ : Set
T₀ = O.Ordᶜ O.zero

read : Tr zero → T₀
read zero          = O.zero
read (suc x)       = O.suc (read x)
read (lim f _)     = O.lim (λ n → read (f n))
read (Ω () _)
read (up _ () _ _)

◃⊑ : {x y : Tr zero} → zero ⊢ x ◃ y → read x O.⊑ read y
◃⊑ ◃s       h = O.≺s h
◃⊑ (◃l n)   h = O.≺l n h
◃⊑ (◃w {p = ()})
◃⊑ (◃u _ () _ _)
◃⊑ (◃c _ () _)
◃⊑ (◃t d e) h = ◃⊑ e (◃⊑ d h)

infix 4 _⊴_
data _⊴_ {S : Sg} (t : T S) : T S → Set where
  ⊴r : t ⊴ t
  ⊴◃ : ∀ {t′} → Lt S t t′ → t ⊴ t′

module _ {S : Sg} where
  ⊴-◃ : {a b c : T S} → a ⊴ b → Lt S b c → Lt S a c
  ⊴-◃ ⊴r     e = e
  ⊴-◃ (⊴◃ d) e = ◃t d e

  ◃-⊴ : {a b c : T S} → Lt S a b → b ⊴ c → Lt S a c
  ◃-⊴ d ⊴r     = d
  ◃-⊴ d (⊴◃ e) = ◃t d e

  ⊴-trans : {a b c : T S} → a ⊴ b → b ⊴ c → a ⊴ c
  ⊴-trans d ⊴r     = d
  ⊴-trans d (⊴◃ e) = ⊴◃ (⊴-◃ d e)

  +⊴ : (b y : T S) → b ⊴ b + y
  +⊴ b zero         = ⊴r
  +⊴ b (suc y)      = ⊴◃ (⊴-◃ (+⊴ b y) ◃s)
  +⊴ b (lim f a)    = ⊴◃ (⊴-◃ (+⊴ b (f zero)) (◃l zero))
  +⊴ b (Ω p g)      = ⊴◃ (⊴-◃ (+⊴ b (g (b₀ S p))) ◃w)
  +⊴ b (up y c w e) = ⊴◃ (⊴-◃ (+⊴ b y) (◃u (b + y) c w e))

⊴→≼ : {c c′ : Tr zero} → c ⊴ c′ → read c ≼ read c′
⊴→≼ {c} ⊴r     = ≼-refl (read c)
⊴→≼ {c} (⊴◃ d) = ⊑→≼ (read c) (◃⊑ d)
```

## 关系

`Mᴰ S Low Chd Nu t x`: 记号项 t 不高于树 x 的一个证据. 记号一侧只经 `cof`, `pred`, `fsn`, `fsT` 看 (不读项的构造), 和除外 (`mU`: 记号的和对着 `up`).
`mL` 是不严格的: t 的基本列逐项不高于同一棵 x. `mΩ` 的分支对一切被低层关系 `Low` 模拟的输入; `Nu p ν` 记槽位 p 允许的共尾下标 ν.

```agda
data Mᴰ (S : Sg) (Low : (p : P S) → E.T → B S p → Set) (Chd : (c : C S) → E.T → D S c → Set)
        (Nu : P S → E.T → Set) : E.T → T S → Set where
  mz : ∀ {x} → Mᴰ S Low Chd Nu [] x
  m1 : ∀ {t x} → cof t ≡ c1 → Mᴰ S Low Chd Nu (pred t) x → Mᴰ S Low Chd Nu t (suc x)
  mL : ∀ {t x} → cof t ≡ cω → (∀ n → Mᴰ S Low Chd Nu (fsn t n) x) → Mᴰ S Low Chd Nu t x
  mΩ : ∀ {t ν p g} → cof t ≡ cΩ ν → Nu p ν
     → (∀ η c → Low p η c → Mᴰ S Low Chd Nu (fsT t η) (g c)) → Mᴰ S Low Chd Nu t (Ω p g)
  mU : ∀ {t s x c y e} → Mᴰ S Low Chd Nu t x → Chd c s y → Mᴰ S Low Chd Nu (t ++ s) (up x c y e)
  mw : ∀ {t x x′} → Mᴰ S Low Chd Nu t x → Lt S x x′ → Mᴰ S Low Chd Nu t x′
```

## 对一切层成立的引理

和的首项不动: 余尾, 前驱, 基本列都落在后面的非空部分上 (`m1∷`, `mL∷`, `mΩ∷`). 由此加法与 `next` (规则 4 的 ψ(b)·n).

```agda
module Gen {S : Sg} {Low : (p : P S) → E.T → B S p → Set} {Chd : (c : C S) → E.T → D S c → Set}
           {Nu : P S → E.T → Set} where
  private
    M : E.T → T S → Set
    M = Mᴰ S Low Chd Nu

  m⊴ : ∀ {t x x′} → M t x → x ⊴ x′ → M t x′
  m⊴ m ⊴r     = m
  m⊴ m (⊴◃ d) = mw m d

  m1∷ : ∀ p s {x} → cof s ≡ c1 → M (p ∷ pred s) x → M (p ∷ s) (suc x)
  m1∷ p []      () r
  m1∷ p (_ ∷ _) e  r = m1 e r

  mL∷ : ∀ p s {x} → cof s ≡ cω → (∀ n → M (p ∷ fsn s n) x) → M (p ∷ s) x
  mL∷ p []      () h
  mL∷ p (_ ∷ _) e  h = mL e h

  mΩ∷ : ∀ p s {ν q g} → cof s ≡ cΩ ν → Nu q ν
      → (∀ η c → Low q η c → M (p ∷ fsT s η) (g c)) → M (p ∷ s) (Ω q g)
  mΩ∷ p []      () nu h
  mΩ∷ p (_ ∷ _) e  nu h = mΩ e nu h

  m-add : ∀ {p b s y} → M (p ∷ []) b → M s y → M (p ∷ s) (b + y)
  m-add {b = b} mb (mz {x = y})          = m⊴ mb (+⊴ b y)
  m-add {p = p} mb (m1 {t = s} e r)      = m1∷ p s e (m-add mb r)
  m-add {p = p} mb (mL {t = s} e h)      = mL∷ p s e (λ n → m-add mb (h n))
  m-add {p = p} mb (mΩ {t = s} e nu h)   = mΩ∷ p s e nu (λ η c l → m-add mb (h η c l))
  m-add mb (mU m ch)                     = mU (m-add mb m) ch
  m-add {b = b} mb (mw m d)              = mw (m-add mb m) (+-mono b d)

  m-rep : ∀ {p b} → M (p ∷ []) b → ∀ n → M (replicate (suc n) p) (iter (b +_) b n)
  m-rep mb zero    = mb
  m-rep mb (suc n) = m-add mb (m-rep mb n)

  m-next : ∀ {t p b} (nz : Lt S zero b) → cof t ≡ cω → (∀ n → fsn t n ≡ replicate n p)
         → M (p ∷ []) b → M t (next b nz)
  m-next {t} {p} {b} nz e q mb = mL e (λ n → subst (λ s → M s (next b nz)) (sym (q n)) (go n))
    where
    go : ∀ n → M (replicate n p) (next b nz)
    go zero    = mz
    go (suc n) = mw (m-rep mb n) (◃l n)

  m-right : ∀ {t y} (a : T S) → M t y → M t (a + y)
  m-right a mz             = mz
  m-right a (m1 e r)       = m1 e (m-right a r)
  m-right a (mL e h)       = mL e (λ n → m-right a (h n))
  m-right a (mΩ e nu h)    = mΩ e nu (λ η c l → m-right a (h η c l))
  m-right a (mU m ch)      = mU (m-right a m) ch
  m-right a (mw m d)       = mw (m-right a m) (+-mono a d)

  m-cum : ∀ {t} (G : ℕ → T S) (nz : ∀ n → Lt S zero (G n)) (n : ℕ) → M t (G n) → M t (limc G nz)
  m-cum {t} G nz n m = mw (go n m) (◃l n)
    where
    go : ∀ n → M t (G n) → M t (cum G n)
    go zero    m = m
    go (suc n) m = m-right (cum G n) m

  m-zl : {S′ : Sg} (Φ : T S′ → T S) → (∀ {x y} → Lt S′ x y → Lt S (Φ x) (Φ y))
       → ∀ {t} → M t (Φ zero) → (y : T S′) → M t (Φ y)
  m-zl Φ mono m y with zl y
  ... | inj₁ refl = m
  ... | inj₂ d    = mw m (mono d)
```

## 第 0 层的实例与 `Sim` 的前提

第 0 层没有槽位与孩子. 余尾 1 处走到 `pred` 且树严格下降一步 (`r1⁰`), 余尾 ω 处逐项走到 `fsn` 且树不升 (`rω⁰`): 都是对推导的反演.

```agda
M⁰ : E.T → Tr zero → Set
M⁰ = Mᴰ (Sig zero) (λ ()) (λ ()) (λ ())

private
  c0≢c1 : c0 ≡ c1 → ⊥
  c0≢c1 ()
  c0≢cω : c0 ≡ cω → ⊥
  c0≢cω ()
  ω≢1 : ∀ {c} → c ≡ cω → c ≡ c1 → ⊥
  ω≢1 refl ()

r1⁰ : ∀ {t x} → M⁰ t x → cof t ≡ c1 → Σ (Tr zero) λ x′ → M⁰ (pred t) x′ × ⊤ × (suc x′ ⊴ x)
r1⁰ mz        w = ⊥-elim (c0≢c1 w)
r1⁰ (m1 {x = x} _ r) w = x , r , tt , ⊴r
r1⁰ (mL e _)  w = ⊥-elim (ω≢1 e w)
r1⁰ (mΩ {p = ()} _ _ _) w
r1⁰ (mU {c = ()} _ _) w
r1⁰ (mw m d)  w with r1⁰ m w
... | x′ , r , _ , le = x′ , r , tt , ⊴◃ (⊴-◃ le d)

rω⁰ : ∀ {t x} → M⁰ t x → cof t ≡ cω → ∀ n → Σ (Tr zero) λ x′ → M⁰ (fsn t n) x′ × ⊤ × (x′ ⊴ x)
rω⁰ mz        w n = ⊥-elim (c0≢cω w)
rω⁰ (m1 e _)  w n = ⊥-elim (ω≢1 w e)
rω⁰ (mL {x = x} _ h) w n = x , h n , tt , ⊴r
rω⁰ (mΩ {p = ()} _ _ _) w n
rω⁰ (mU {c = ()} _ _) w n
rω⁰ (mw m d)  w n with rω⁰ m w n
... | x′ , r , _ , le = x′ , r , tt , ⊴◃ (⊴-◃ le d)

strict⁰ : ∀ {x y : Tr zero} → ⊤ → suc x ⊴ y → O.suc (read x) ≼ read y
strict⁰ _ le = ⊴→≼ le

weak⁰ : ∀ {x y : Tr zero} → ⊤ → x ⊴ y → read x ≼ read y
weak⁰ _ le = ⊴→≼ le

Rt : ∀ {t} → HC t → T₀
Rt h = toL (tree h)

lower⁰ : ∀ {t x} → M⁰ t x → (h : HC t) → Rt h ≼ read x
lower⁰ m h = lower′ read (λ x → x) (λ _ → ⊤) (λ x y → suc x ⊴ y) (λ x y → x ⊴ y)
  strict⁰ weak⁰ M⁰ (λ m _ w → r1⁰ m w) (λ m _ w n → rω⁰ m w n) m tt h
```

第 0 层的 1: 非零的树都在 1 之上.

```agda
pos⁰ : (y : Tr zero) → zero ⊢ zero ◃ y → M⁰ (𝟏 ∷ []) y
pos⁰ zero      d = ⊥-elim (¬◃z d)
pos⁰ (suc y)   d = m1 refl mz
pos⁰ (lim f a) d with zl (f 1)
... | inj₁ e  = ⊥-elim (¬◃z (subst (λ v → zero ⊢ f 0 ◃ v) (sym e) (a 0)))
... | inj₂ d′ = mw (pos⁰ (f 1) d′) (◃l 1)
pos⁰ (Ω () _)      d
pos⁰ (up _ () _ _) d
```
