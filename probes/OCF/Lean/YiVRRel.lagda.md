# 值关系: 遗传的值前序与规范域 (树侧)

> 判决: 工具, 树侧 (只导入精简块的块, 运算, 路径). 关系 `Le ℓ x y`: 零, 后继, ℕ 极限按值前序的规则; Ω 结点按 "相关的分支给相关的树"; 嵌入只比同一个孩子. 规范域 `Can ℓ x = Le ℓ x x`.
> 编译定理, 无前提: 加法, `next⁺`, 部分和极限, `ι`, `emb`, 上折 `Up` 保持关系 (`+≼`, `next≼`, `limc≼`, `ι≼`, `emb≼`, `Up≼`); 第 0 层的树都在规范域 (`refl₀`); 不含 Ω 形状的层号的 Ω 树在规范域 (`Ωt≼`).
> 编译否定: 塔第 1 项的 Ω 树不在规范域 (`β-not`), 因为关系不比较不同孩子; 读作 "关系太窄", 不是数学障碍. 折叠的保持在 `YiVRFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVRRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
```

## 一层之内的关系

参数 `RB` 是分支上的关系, `RD` 是孩子树上的关系. 右边变大的四条 (`≼s`, `≼l`, `≼w`, `≼u`) 都沿第一位置序: Ω 结点只取第一分支, 因为折叠只对第一分支不降 (`nodeLe`). `w≼w` 是函数式的: 相关的分支给相关的树, 所以 `Le x x` 说的是 x 的各个分支函数遗传地单调.

```agda
data LeS (S : Sg) (RB : (p : P S) → B S p → B S p → Set) (RD : (c : C S) → D S c → D S c → Set)
     : T S → T S → Set where
  z≼  : ∀ {b} → LeS S RB RD zero b
  s≼s : ∀ {a b} → LeS S RB RD a b → LeS S RB RD (suc a) (suc b)
  ≼s  : ∀ {a b} → LeS S RB RD a b → LeS S RB RD a (suc b)
  ≼l  : ∀ {a f r} (n : ℕ) → LeS S RB RD a (f n) → LeS S RB RD a (lim f r)
  l≼  : ∀ {f r b} → ((n : ℕ) → LeS S RB RD (f n) b) → LeS S RB RD (lim f r) b
  ≼w  : ∀ {a p g} → LeS S RB RD a (g (b₀ S p)) → LeS S RB RD a (Ω p g)
  w≼w : ∀ {p g g′} → ((z z′ : B S p) → RB p z z′ → LeS S RB RD (g z) (g′ z′)) → LeS S RB RD (Ω p g) (Ω p g′)
  ≼u  : ∀ {a x c y e} → LeS S RB RD a x → LeS S RB RD a (up x c y e)
  u≼u : ∀ {x x′ c y y′ e e′} → LeS S RB RD x x′ → RD c y y′ → LeS S RB RD (up x c y e) (up x′ c y′ e′)

module _ {S : Sg} {RB : (p : P S) → B S p → B S p → Set} {RD : (c : C S) → D S c → D S c → Set} where
  private
    _≼_ : T S → T S → Set
    _≼_ = LeS S RB RD

  ≼+ : ∀ {a b} → a ≼ b → (c : T S) → a ≼ (b + c)
  ≼+ d zero         = d
  ≼+ d (suc c)      = ≼s (≼+ d c)
  ≼+ d (lim f r)    = ≼l 0 (≼+ d (f 0))
  ≼+ d (Ω p g)      = ≼w (≼+ d (g (b₀ S p)))
  ≼+ d (up y c w e) = ≼u (≼+ d y)

  +≼ : ∀ {a a′ c c′} → a ≼ a′ → c ≼ c′ → (a + c) ≼ (a′ + c′)
  +≼ {c′ = c′} da z≼ = ≼+ da c′
  +≼ da (s≼s d)   = s≼s (+≼ da d)
  +≼ da (≼s d)    = ≼s (+≼ da d)
  +≼ da (≼l n d)  = ≼l n (+≼ da d)
  +≼ da (l≼ h)    = l≼ (λ n → +≼ da (h n))
  +≼ da (≼w d)    = ≼w (+≼ da d)
  +≼ da (w≼w h)   = w≼w (λ z z′ r → +≼ da (h z z′ r))
  +≼ da (≼u d)    = ≼u (+≼ da d)
  +≼ da (u≼u d r) = u≼u (+≼ da d) r

  iter≼ : ∀ {b b′} → b ≼ b′ → (n : ℕ) → iter (b +_) b n ≼ iter (b′ +_) b′ n
  iter≼ d zero    = d
  iter≼ d (suc n) = +≼ d (iter≼ d n)

  next≼ : (b b′ : T⁺ {S}) → proj₁ b ≼ proj₁ b′ → proj₁ (next⁺ b) ≼ proj₁ (next⁺ b′)
  next≼ b b′ d = l≼ (λ n → ≼l n (iter≼ d n))

  cum≼ : (F F′ : ℕ → T S) → ((n : ℕ) → F n ≼ F′ n) → (n : ℕ) → cum F n ≼ cum F′ n
  cum≼ F F′ h zero    = h zero
  cum≼ F F′ h (suc n) = +≼ (cum≼ F F′ h n) (h (suc n))

  limc≼ : (F F′ : ℕ → T⁺ {S}) → ((n : ℕ) → proj₁ (F n) ≼ proj₁ (F′ n)) → proj₁ (limc⁺ F) ≼ proj₁ (limc⁺ F′)
  limc≼ F F′ h = l≼ (λ n → ≼l n (cum≼ _ _ h n))
```

## 各层的关系

分支上的关系与孩子树上的关系按层号递归, 落到低层的同一个关系.

```agda
mutual
  LB : (ℓ : L) (p : Pos ℓ) → Br ℓ p → Br ℓ p → Set
  LB (nd s h)      (inj₂ (c , t)) = LB⁼ (h c) t
  LB (nd (sΩ k) h) (inj₁ t)       = LB⁼ k t

  LB⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t → Br⁼ a t → Set
  LB⁼ a (inj₁ _) = LeS (Sig a) (LB a) (LC a)
  LB⁼ a (inj₂ p) = LB a p

  LC : (ℓ : L) (c : CH ℓ) → ChT ℓ c → ChT ℓ c → Set
  LC (nd s h) c = LeS (Sig (h c)) (LB (h c)) (LC (h c))

Le : (ℓ : L) → Tr ℓ → Tr ℓ → Set
Le ℓ = LeS (Sig ℓ) (LB ℓ) (LC ℓ)

Can : (ℓ : L) → Tr ℓ → Set
Can ℓ x = Le ℓ x x

refl₀ : (x : Tr zero) → Can zero x
refl₀ zero      = z≼
refl₀ (suc x)   = s≼s (refl₀ x)
refl₀ (lim f a) = l≼ (λ n → ≼l n (refl₀ (f n)))
```

## 嵌入, 换型

```agda
ι≼ : (j : L) {a b : Tr zero} → Le zero a b → Le j (ι j a) (ι j b)
ι≼ j z≼       = z≼
ι≼ j (s≼s d)  = s≼s (ι≼ j d)
ι≼ j (≼s d)   = ≼s (ι≼ j d)
ι≼ j (≼l n d) = ≼l n (ι≼ j d)
ι≼ j (l≼ h)   = l≼ (λ n → ι≼ j (h n))

upz≼ : ∀ {s h} (c : Ch s) {y y′ : Tr⁺ (h c)} → Le (h c) (proj₁ y) (proj₁ y′)
     → Le (nd s h) (proj₁ (upz {s} {h} c y)) (proj₁ (upz {s} {h} c y′))
upz≼ c d = u≼u z≼ d

emb≼ : (ℓ : L) (o : Ok ℓ) {k : L} (v : k ≤ ℓ) {y y′ : Tr⁺ k} → Le k (proj₁ y) (proj₁ y′)
     → Le ℓ (proj₁ (emb ℓ o v y)) (proj₁ (emb ℓ o v y′))
emb≼ ℓ             o self      d = d
emb≼ (nd s h)      o (inc c v) d = u≼u z≼ (emb≼ (h c) (proj₂ o c) v d)
emb≼ (nd s h)      o (inu vs)  d = u≼u z≼ (emb≼ (h (c₀ s)) (proj₂ o (c₀ s)) (vs (c₀ s)) d)
emb≼ (nd (sΩ k) h) o (ink v)   d = u≼u z≼ (emb≼ (h zero) (proj₂ o zero) (v ∙ proj₂ (proj₁ o) zero) d)

mutual
  fromBr≼ : (ℓ : L) (p : Pos ℓ) {a b : Tr (at ℓ p)} → Le (at ℓ p) a b → LB ℓ p (fromBr ℓ p a) (fromBr ℓ p b)
  fromBr≼ (nd s h)      (inj₂ (c , t)) d = fromBr⁼≼ (h c) t d
  fromBr≼ (nd (sΩ k) h) (inj₁ t)       d = fromBr⁼≼ k t d

  fromBr⁼≼ : (a : L) (t : Pos⁼ a) {x y : Tr (proj₁ (sl⁼ a t))} → Le (proj₁ (sl⁼ a t)) x y
           → LB⁼ a t (proj₂ (sl⁼ a t) x) (proj₂ (sl⁼ a t) y)
  fromBr⁼≼ a (inj₁ _) d = d
  fromBr⁼≼ a (inj₂ p) d = fromBr≼ a p d

mvLB : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) {z z′ : Br ℓ (mv d p)} → LB ℓ (mv d p) z z′ → LB j p (mvBr d p z) (mvBr d p z′)
mvLB stop       p r = r
mvLB (down d c) p r = mvLB d (inj₂ (c , inj₂ p)) r

pshLB : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) {z z′ : Br⁼ a (psh v t)} → LB⁼ a (psh v t) z z′ → LB⁼ k t (pshBr v t z) (pshBr v t z′)
pshLB self                  t r = r
pshLB (inc c v)             t r = pshLB v t r
pshLB {a = nd s h} (inu vs) t r = pshLB (vs (c₀ s)) t r
pshLB (ink v)               t r = pshLB v t r
```

## 上折保持关系

`≼Up`: 上折不低于它的底. `Up≼`: 底相关, 被折的树相关, 则输出相关; 对推导递归, 嵌入一行落到孩子层的推导.

```agda
≼Up : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr⁺ ℓ) (y : Tr j) {a : Tr ℓ} → Le ℓ a (proj₁ b) → Le ℓ a (proj₁ (Up j d b y))
≼Up j d b zero      e = e
≼Up j d b (suc y)   e = ≼l 0 (≼Up j d b y e)
≼Up j d b (lim f r) e = ≼l 0 (≼Up j d b (f 0) e)
≼Up {ℓ} j d b (Ω p g) {a} e =
  ≼w (subst (λ t → Le ℓ a (proj₁ (Up j d b (g t)))) (sym (mvFirst d p)) (≼Up j d b (g (fromBr j p zero)) e))
≼Up (nd s h) d b (up y c y′ _) e = ≼Up (h c) (down d c) (Up (nd s h) d b y) y′ (≼Up (nd s h) d b y e)

Up≼ : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b b′ : Tr⁺ ℓ) → Le ℓ (proj₁ b) (proj₁ b′) → {y y′ : Tr j} → Le j y y′
    → Le ℓ (proj₁ (Up j d b y)) (proj₁ (Up j d b′ y′))
Up≼ j d b b′ e {y′ = y′} z≼ = ≼Up j d b′ y′ e
Up≼ j d b b′ e (s≼s q)  = next≼ _ _ (Up≼ j d b b′ e q)
Up≼ j d b b′ e (≼s q)   = ≼l 0 (Up≼ j d b b′ e q)
Up≼ j d b b′ e (≼l n q) = ≼l n (Up≼ j d b b′ e q)
Up≼ j d b b′ e (l≼ h)   = l≼ (λ n → Up≼ j d b b′ e (h n))
Up≼ {ℓ} j d b b′ e {y = y} (≼w {p = p} {g = g} q) =
  ≼w (subst (λ t → Le ℓ (proj₁ (Up j d b y)) (proj₁ (Up j d b′ (g t)))) (sym (mvFirst d p)) (Up≼ j d b b′ e q))
Up≼ j d b b′ e (w≼w {p = p} h) = w≼w (λ z z′ r → Up≼ j d b b′ e (h _ _ (mvLB d p r)))
Up≼ (nd s h) d b b′ e (≼u {x = x} {c = c} {y = y₁} q) =
  ≼Up (h c) (down d c) (Up (nd s h) d b′ x) y₁ (Up≼ (nd s h) d b b′ e q)
Up≼ (nd s h) d b b′ e (u≼u {c = c} q r) = Up≼ (h c) (down d c) _ _ (Up≼ (nd s h) d b b′ e q) r
```

## 规范域里的 Ω 树

`NoΩ ℓ`: 层号里没有 Ω 形状 (有限层号, 它们的 ℕ 极限, 第 0 层的树读出的层号). 这些层号的 Ω 树在规范域; 沿路径往下仍没有 Ω 形状.

```agda
NoΩ : L → Set
NoΩ zero          = ⊤
NoΩ (nd sS h)     = NoΩ (h tt)
NoΩ (nd sL g)     = (n : ℕ) → NoΩ (g n)
NoΩ (nd (sΩ k) h) = ⊥

Ωt≼ : (ℓ : L) → NoΩ ℓ → Can ℓ (proj₁ (Ωt ℓ))
Ωt≼ zero          _ = s≼s z≼
Ωt≼ (nd sS h)     _ = w≼w (λ z z′ r → u≼u z≼ (s≼s r))
Ωt≼ (nd sL g)     ν = limc≼ (λ n → upz {sL} {g} n (Ωt (g n))) (λ n → upz {sL} {g} n (Ωt (g n)))
                            (λ n → upz≼ {sL} {g} n (Ωt≼ (g n) (ν n)))

NoΩ≤ : ∀ {i ℓ} → i ≤ ℓ → NoΩ ℓ → NoΩ i
NoΩ≤ self                     ν = ν
NoΩ≤ {ℓ = nd sS h} (inc c v)  ν = NoΩ≤ v ν
NoΩ≤ {ℓ = nd sL g} (inc n v)  ν = NoΩ≤ v (ν n)
NoΩ≤ {ℓ = nd sS h} (inu vs)   ν = NoΩ≤ (vs tt) ν
NoΩ≤ {ℓ = nd sL g} (inu vs)   ν = NoΩ≤ (vs zero) (ν zero)

NoΩ↑ : (c : Tr zero) → NoΩ (zero ⊕ ↑ zero c)
NoΩ↑ zero      = tt
NoΩ↑ (suc c)   = NoΩ↑ c
NoΩ↑ (lim f a) = λ n → NoΩ↑ (f n)
```

后继形状的层号的 Ω 树对一切孩子层都在规范域 (上面第二行没有用 `NoΩ`).

```agda
ΩtS≼ : (h : ⊤ → L) → Can (nd sS h) (proj₁ (Ωt (nd sS h)))
ΩtS≼ h = w≼w (λ z z′ r → u≼u z≼ (s≼s r))
```

## 否定: 塔第 1 项的 Ω 树不在规范域

`Ωt (tw 1)` 的分支 c 是孩子 c 里的嵌入; 相关的两个分支 `zero`, `suc zero` 给出两个不同孩子的嵌入, 关系里没有比较它们的规则.

```agda
β-not : Can (tw 1) (proj₁ (Ωt (tw 1))) → ⊥
β-not (≼w (≼u ()))
β-not (w≼w h) with h zero (suc zero) z≼
... | ≼u ()
```
