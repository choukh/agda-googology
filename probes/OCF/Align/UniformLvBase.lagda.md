# 层号的文法之外: 分支在 `Ordᴵ` 上的层号, 相对比较 (底座)

> 底座, 不含记号. 结论写在 [UniformLv](UniformLv.lagda.md). 由 [InaccFloorBase](InaccFloorBase.lagda.md) 的 `Rel` 改写: 分支从原始树换到 `Ordᴵ` (证据才有来源), 路径改成带下标的关系 (与 `<ᴵ` 同形), 比较的输出多一项**跨环境的可容许性转移**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformLvBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑;
   ≅ᴵ-refl; ≅ᴵ-sym; ≅ᴵ-trans; <ᴵ-trans; <ᴵ-dec; ⊑ᴵ-trans; ⊑ᴵ-refl; Sim→⊑ᴵ)
open import OCF.Align.InaccFloorBase using (≺→⊑ᴵ; ≅→⊑ᴵ)
```

## §1 层号与路径

`LI`: `zero` ($\Omega_0$), `base` ($\Omega$, 节点在可数层, 由 `oi` 与 `oclo` 表示, 没有路径), `suc`, `lim`, `lcl g`: $\sup_{\eta<\Omega}g\,\eta$, 分支在 `Ordᴵ` 上. 第一支 `fst` 是 $\eta=1$ 处, 它不要 $1<\ell$, 所以不抬高地板.

路径 `a <ᴸ c` 与 `<ᴵ` 同形, $a$ 就是 `at`.

```agda
data LI : Set where
  zero : LI
  base : LI
  suc  : LI → LI
  lim  : (ℕ → LI) → LI
  lcl  : ℕ → (Ordᴵ → LI) → LI

one : Ordᴵ
one = suc zero

infix 4 _<ᴸ_
data _<ᴸ_ : LI → LI → Set where
  zero : ∀ {a} → a <ᴸ suc a
  suc  : ∀ {a b} → a <ᴸ b → a <ᴸ suc b
  lim  : ∀ {a f} n → a <ᴸ f n → a <ᴸ lim f
  fst  : ∀ {a h g} → a <ᴸ g one → a <ᴸ lcl h g
  bra  : ∀ {a h g} η → a <ᴸ g η → a <ᴸ lcl h g

Wd : Set
Wd = ℕ → Ordᴵ

Adm : Wd → ∀ {a c} → a <ᴸ c → Set
Adm ℓ zero      = ⊤
Adm ℓ (suc r)   = Adm ℓ r
Adm ℓ (lim n r) = Adm ℓ r
Adm ℓ (fst r)   = Adm ℓ r
Adm ℓ (bra {h = h} η r) = (η <ᴵ ℓ h) × Adm ℓ r
```

## §2 结构相等: 一个部分等价

`o≈` 是关系式的: $\eta\cong\eta'$ 处相关. 所以 `≈` 没有自反性 (`lcl` 的分支要尊重 $\cong^\mathsf I$), `L ≈ L` 是层号合法性的一部分 (`WF`).

```agda
infix 4 _≈_
data _≈_ : LI → LI → Set where
  z≈ : zero ≈ zero
  b≈ : base ≈ base
  s≈ : ∀ {a b} → a ≈ b → suc a ≈ suc b
  l≈ : ∀ {f g} → (∀ n → f n ≈ g n) → lim f ≈ lim g
  o≈ : ∀ {h h′ g g′} → h ≡ h′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ g′ η′) → lcl h g ≈ lcl h′ g′

≈-sym : ∀ {a b} → a ≈ b → b ≈ a
≈-sym z≈     = z≈
≈-sym b≈     = b≈
≈-sym (s≈ e) = s≈ (≈-sym e)
≈-sym (l≈ h) = l≈ (λ n → ≈-sym (h n))
≈-sym (o≈ r h) = o≈ (sym r) (λ η η′ d → ≈-sym (h η′ η (≅ᴵ-sym d)))

≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
≈-trans z≈     z≈      = z≈
≈-trans b≈     b≈      = b≈
≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
≈-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans (h n) (h′ n))
≈-trans (o≈ r h) (o≈ r′ h′) = o≈ (trans r r′) (λ η η′ d → ≈-trans (h η η (≅ᴵ-refl η)) (h′ η η′ d))

≈-reflˡ : ∀ {a b} → a ≈ b → a ≈ a
≈-reflˡ e = ≈-trans e (≈-sym e)

≈-reflʳ : ∀ {a b} → a ≈ b → b ≈ b
≈-reflʳ e = ≈-trans (≈-sym e) e
```

## §3 路径的搬运

`a ≺ b`: $a$ 模 `≈` 是 $b$ 的字面前驱, 带路径. `a ⊑ b`: $a$ 的路径都能搬到 $b$, 可容许性对**一切环境**保持. 这一点比 [InaccFloorBase](InaccFloorBase.lagda.md) 的 `⊑ᴬ` 强: 那里 $\ell$ 是固定的; 这里输出的路径要当树节点, 节点的证据要对后面的一切 $\ell$ 成立, 所以转移不能只在比较时的 $\ell$ 上.

```agda
record _≺⟨_⟩_ (a : LI) (A : Wd → Set) (b : LI) : Set where
  constructor viaᴸ
  field
    {rep} : LI
    eqv   : a ≈ rep
    pth   : rep <ᴸ b
    trf   : ∀ ℓ → A ℓ → Adm ℓ pth
open _≺⟨_⟩_ public

infix 4 _⊑_
_⊑_ : LI → LI → Set
a ⊑ b = ∀ {k} (r : k <ᴸ a) → k ≺⟨ (λ ℓ → Adm ℓ r) ⟩ b

≈-move : ∀ {a b} → a ≈ b → a ⊑ b
≈-move (s≈ e) zero = viaᴸ e zero (λ _ _ → tt)
≈-move (s≈ e) (suc r) with ≈-move e r
... | viaᴸ d p t = viaᴸ d (suc p) t
≈-move (l≈ h) (lim n r) with ≈-move (h n) r
... | viaᴸ d p t = viaᴸ d (lim n p) t
≈-move (o≈ _ h) (fst r) with ≈-move (h one one (≅ᴵ-refl one)) r
... | viaᴸ d p t = viaᴸ d (fst p) t
≈-move (o≈ e h) (bra η r) with ≈-move (h η η (≅ᴵ-refl η)) r
... | viaᴸ d p t = viaᴸ d (bra η p) (λ ℓ u → subst (λ x → η <ᴵ ℓ x) e (proj₁ u) , t ℓ (proj₂ u))
```

## §4 三歧: 有证据就是定理

`Tri c p q`: $p$ 的层号与 $q$ 的层号的比较, 输出的路径带转移. `WF`: 单调不看 $\ell$: $\eta\sqsubseteq^\mathsf I\eta'$ 推出 $g\,\eta\sqsubseteq g\,\eta'$. $\ell$ 只用来比较两个分支 (`<ᴵ-dec`).

```agda
data Tri {a b c c′ : LI} (p : a <ᴸ c) (q : b <ᴸ c′) : Set where
  tlt : a ≺⟨ (λ ℓ → Adm ℓ p) ⟩ b → Tri p q
  tgt : b ≺⟨ (λ ℓ → Adm ℓ q) ⟩ a → Tri p q
  teq : a ≈ b → Tri p q

WF : LI → Set
WF zero    = ⊤
WF base    = ⊤
WF (suc k) = WF k
WF (lim f) = (∀ n → f n ⊑ f (suc n)) × (∀ n → WF (f n))
WF (lcl h g) = (∀ {η η′} → η ⊑ᴵ η′ → g η ⊑ g η′) × (∀ {η} → one ⊑ᴵ η → g one ⊑ g η) × (∀ {η} → η ≅ᴵ zero → g η ⊑ g one) × (∀ η → WF (g η))

stepsᴸ : ∀ {f : ℕ → LI} → (∀ n → f n ⊑ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ f m
stepsᴸ s zero r = s _ r
stepsᴸ {f} s (suc {n} {m} q) r with stepsᴸ s q r
... | viaᴸ d p t with s _ p
...   | viaᴸ d′ p′ t′ = viaᴸ (≈-trans d d′) p′ (λ ℓ u → t′ ℓ (t ℓ u))
```

**搬运下的三歧.** `shL`: 把左边的路径换成搬运之后的. `gt` 那一支要把输出的路径搬回左边的层号 (`≈-move`), 所以 `≈` 只作用在路径的形状上, 分支值不变.

```agda
shL : ∀ {a a′ b c₁ c₂ c₃} {p : a <ᴸ c₁} {p′ : a′ <ᴸ c₂} {q : b <ᴸ c₃} → a ≈ a′ → (∀ ℓ → Adm ℓ p → Adm ℓ p′) → Tri p′ q → Tri p q
shL e t (tlt (viaᴸ d s u)) = tlt (viaᴸ (≈-trans e d) s (λ ℓ x → u ℓ (t ℓ x)))
shL e t (tgt (viaᴸ d s u)) with ≈-move (≈-sym e) s
... | viaᴸ d′ s′ u′ = tgt (viaᴸ (≈-trans d d′) s′ (λ ℓ x → u′ ℓ (u ℓ x)))
shL e t (teq d) = teq (≈-trans e d)

shR : ∀ {a b b′ c₁ c₂ c₃} {p : a <ᴸ c₁} {q : b <ᴸ c₂} {q′ : b′ <ᴸ c₃} → b ≈ b′ → (∀ ℓ → Adm ℓ q → Adm ℓ q′) → Tri p q′ → Tri p q
shR e t (tgt (viaᴸ d s u)) = tgt (viaᴸ (≈-trans e d) s (λ ℓ x → u ℓ (t ℓ x)))
shR e t (tlt (viaᴸ d s u)) with ≈-move (≈-sym e) s
... | viaᴸ d′ s′ u′ = tlt (viaᴸ (≈-trans d d′) s′ (λ ℓ x → u′ ℓ (u ℓ x)))
shR e t (teq d) = teq (≈-trans d (≈-sym e))
```

`rdx`: 只换路径的外壳, 层号不变. `Adm` 对外壳是定义相等的.

```agda
rdx : ∀ {a b c₁ c₂ c₃ c₄} {p : a <ᴸ c₁} {p′ : a <ᴸ c₂} {q : b <ᴸ c₃} {q′ : b <ᴸ c₄} → (∀ ℓ → Adm ℓ p → Adm ℓ p′) → (∀ ℓ → Adm ℓ q → Adm ℓ q′) → Tri p′ q′ → Tri p q
rdx f g (tlt (viaᴸ d s u)) = tlt (viaᴸ d s (λ ℓ x → u ℓ (f ℓ x)))
rdx f g (tgt (viaᴸ d s u)) = tgt (viaᴸ d s (λ ℓ x → u ℓ (g ℓ x)))
rdx f g (teq d) = teq d
```

**定理.** 对 $c$ 结构递归; `lcl` 处用环境 $\ell$ 比较两个分支. 第一支与 $\eta$ 比较时用 `zero <ᴵ ℓ` 判定 $\eta\cong0$ 还是 $1\sqsubseteq\eta$, 所以不要 $1<\ell$. 输出的路径的转移对一切环境成立.

```agda
<-dec : ∀ {c} → WF c → c ≈ c → ∀ {a b} (p : a <ᴸ c) (q : b <ᴸ c) (ℓ : Wd) → (∀ h → zero <ᴵ ℓ h) → Adm ℓ p → Adm ℓ q → Tri p q
<-dec {suc k} w (s≈ e) zero zero ℓ z _ _ = teq e
<-dec {suc k} w (s≈ e) zero (suc q) ℓ z _ _ with ≈-move e q
... | viaᴸ d s t = tgt (viaᴸ d s t)
<-dec {suc k} w (s≈ e) (suc p) zero ℓ z _ _ with ≈-move e p
... | viaᴸ d s t = tlt (viaᴸ d s t)
<-dec {suc k} w (s≈ e) (suc p) (suc q) ℓ z ap aq = rdx {p′ = p} {q′ = q} (λ _ x → x) (λ _ x → x) (<-dec w e p q ℓ z ap aq)
<-dec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) ℓ z ap aq with <ᴺ-dec n m
... | injᵃ n<m with stepsᴸ st n<m p
...   | viaᴸ d p′ t = shL d (λ ℓ′ x → t ℓ′ x) (rdx (λ _ x → x) (λ _ x → x) (<-dec (w m) (e m) p′ q ℓ z (t ℓ ap) aq))
<-dec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) ℓ z ap aq | injᵇ m<n with stepsᴸ st m<n q
...   | viaᴸ d q′ t = shR d (λ ℓ′ x → t ℓ′ x) (rdx (λ _ x → x) (λ _ x → x) (<-dec (w n) (e n) p q′ ℓ z ap (t ℓ aq)))
<-dec {lim f} (st , w) (l≈ e) (lim n p) (lim _ q) ℓ z ap aq | injᶜ refl = rdx {p′ = p} {q′ = q} (λ _ x → x) (λ _ x → x) (<-dec (w n) (e n) p q ℓ z ap aq)
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (fst p) (fst q) ℓ z ap aq = rdx {p′ = p} {q′ = q} (λ _ x → x) (λ _ x → x) (<-dec (w one) (e one one (≅ᴵ-refl one)) p q ℓ z ap aq)
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (fst p) (bra y q) ℓ z ap (ly , aq) with <ᴵ-dec (z h) ly
... | injᵃ (via d s) with up₁ (s⊑ d s) p
...   | viaᴸ d′ p′ t = shL d′ (λ ℓ′ x → t ℓ′ x) (rdx (λ _ x → x) (λ _ x → proj₂ x) (<-dec (w y) (e y y (≅ᴵ-refl y)) p′ q ℓ z (t ℓ ap) aq))
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (fst p) (bra y q) ℓ z ap (ly , aq) | injᵇ (via d ())
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (fst p) (bra y q) ℓ z ap (ly , aq) | injᶜ d with dn₀ (≅ᴵ-sym d) q
...   | viaᴸ d′ q′ t = shR d′ (λ ℓ′ x → t ℓ′ (proj₂ x)) (rdx (λ _ x → x) (λ _ x → x) (<-dec (w one) (e one one (≅ᴵ-refl one)) p q′ ℓ z ap (t ℓ aq)))
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (bra x p) (fst q) ℓ z (lx , ap) aq with <ᴵ-dec (z h) lx
... | injᵃ (via d s) with up₁ (s⊑ d s) q
...   | viaᴸ d′ q′ t = shR d′ (λ ℓ′ u → t ℓ′ u) (rdx (λ _ u → proj₂ u) (λ _ u → u) (<-dec (w x) (e x x (≅ᴵ-refl x)) p q′ ℓ z ap (t ℓ aq)))
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (bra x p) (fst q) ℓ z (lx , ap) aq | injᵇ (via d ())
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (bra x p) (fst q) ℓ z (lx , ap) aq | injᶜ d with dn₀ (≅ᴵ-sym d) p
...   | viaᴸ d′ p′ t = shL d′ (λ ℓ′ u → t ℓ′ (proj₂ u)) (rdx (λ _ u → u) (λ _ u → u) (<-dec (w one) (e one one (≅ᴵ-refl one)) p′ q ℓ z (t ℓ ap) aq))
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (bra x p) (bra y q) ℓ z (lx , ap) (ly , aq) with <ᴵ-dec lx ly
... | injᵃ r with dir (≺→⊑ᴵ r) p
...   | viaᴸ d′ p′ t = shL d′ (λ ℓ′ u → t ℓ′ (proj₂ u)) (rdx (λ _ u → u) (λ _ u → proj₂ u) (<-dec (w y) (e y y (≅ᴵ-refl y)) p′ q ℓ z (t ℓ ap) aq))
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (bra x p) (bra y q) ℓ z (lx , ap) (ly , aq) | injᵇ r with dir (≺→⊑ᴵ r) q
...   | viaᴸ d′ q′ t = shR d′ (λ ℓ′ u → t ℓ′ (proj₂ u)) (rdx (λ _ u → proj₂ u) (λ _ u → u) (<-dec (w x) (e x x (≅ᴵ-refl x)) p q′ ℓ z ap (t ℓ aq)))
<-dec {lcl h g} (dir , up₁ , dn₀ , w) (o≈ _ e) (bra x p) (bra y q) ℓ z (lx , ap) (ly , aq) | injᶜ d with dir (≅→⊑ᴵ d) p
...   | viaᴸ d′ p′ t = shL d′ (λ ℓ′ u → t ℓ′ (proj₂ u)) (rdx (λ _ u → u) (λ _ u → proj₂ u) (<-dec (w y) (e y y (≅ᴵ-refl y)) p′ q ℓ z (t ℓ ap) aq))
```

## §5 不看语法的层号函数

`_⊞_`: $L\mapsto L+a$, `times`: $L\mapsto L\cdot\Omega$, `_⊕_`: 层号的加法. 都是 `LI` 上的普通函数. 证据只用到 `Ordᴵ` 的步进. 与 [InaccFloorBase](InaccFloorBase.lagda.md) §2 同形, 但不要世界 $\ell$: 分支的单调对一切 $\eta$ 成立.

```agda
infixl 6 _⊞_
_⊞_ : LI → Ordᴵ → LI
L ⊞ zero    = L
L ⊞ suc a   = suc (L ⊞ a)
L ⊞ lim f s = lim (λ n → L ⊞ f n)

-- 塔的高度: 地板按高度分开 (§6 与 UniformLvTree). `suc` 与 `lim` 不改高度; `lim` 取第 1 项, 这里只是选一个数
ht : LI → ℕ
ht zero      = 0
ht base      = 1
ht (suc k)   = ht k
ht (lim f)   = ht (f 1)
ht (lcl h g) = suc h

times : LI → LI
times L = lcl (ht L) (L ⊞_)

≈⊞ : ∀ {L L′ a b} → L ≈ L′ → a ≅ᴵ b → (L ⊞ a) ≈ (L′ ⊞ b)
≈⊞ e z≅     = e
≈⊞ e (s≅ d) = s≈ (≈⊞ e d)
≈⊞ e (l≅ h) = l≈ (λ n → ≈⊞ e (h n))

≈ht : ∀ {L L′} → L ≈ L′ → ht L ≡ ht L′
≈ht z≈     = refl
≈ht b≈     = refl
≈ht {suc a} {suc b} (s≈ e) = ≈ht {a} {b} e
≈ht {lim f} {lim g} (l≈ h) = ≈ht {f 1} {g 1} (h 1)
≈ht (o≈ r h) = cong suc r

≈times : ∀ {L} → L ≈ L → times L ≈ times L
≈times e = o≈ refl (λ η η′ d → ≈⊞ e d)

module Mono (L : LI) (self : L ≈ L) where
  inL : ∀ a → L ⊑ (L ⊞ a)
  inL zero      r = ≈-move self r
  inL (suc a)   r with inL a r
  ... | viaᴸ d p t = viaᴸ d (suc p) t
  inL (lim f s) r with inL (f 0) r
  ... | viaᴸ d p t = viaᴸ d (lim 0 p) t

  lit⊞ : ∀ {a b} → a <ᴵ b → (L ⊞ a) <ᴸ (L ⊞ b)
  lit⊞ zero      = zero
  lit⊞ (suc q)   = suc (lit⊞ q)
  lit⊞ (lim n q) = lim n (lit⊞ q)

  adm⊞ : ∀ {a b} (q : a <ᴵ b) ℓ → Adm ℓ (lit⊞ q)
  adm⊞ zero      ℓ = tt
  adm⊞ (suc q)   ℓ = adm⊞ q ℓ
  adm⊞ (lim n q) ℓ = adm⊞ q ℓ

  up⊞ : ∀ {a b} → a <ᴵ b → (L ⊞ a) ⊑ (L ⊞ b)
  up⊞ zero      r = viaᴸ (eqv (≈-move (≈⊞ self (≅ᴵ-refl _)) r)) (suc (pth (≈-move (≈⊞ self (≅ᴵ-refl _)) r))) (trf (≈-move (≈⊞ self (≅ᴵ-refl _)) r))
  up⊞ (suc q)   r with up⊞ q r
  ... | viaᴸ d p t = viaᴸ d (suc p) t
  up⊞ (lim n q) r with up⊞ q r
  ... | viaᴸ d p t = viaᴸ d (lim n p) t

  mono⊞ : ∀ {a b} → a ⊑ᴵ b → (L ⊞ a) ⊑ (L ⊞ b)
  mono⊞ {b = b} z⊑ r = inL b r
  mono⊞ (s⊑ e q) zero = viaᴸ (≈⊞ self e) (lit⊞ q) (λ ℓ _ → adm⊞ q ℓ)
  mono⊞ (s⊑ e q) (suc r) with ≈-move (≈⊞ self e) r
  ... | viaᴸ d p t with up⊞ q p
  ...   | viaᴸ d′ p′ t′ = viaᴸ (≈-trans d d′) p′ (λ ℓ u → t′ ℓ (t ℓ u))
  mono⊞ (l⊑ h) (lim n r) = mono⊞ (h n) r

  res⊞ : ∀ {a b} → a ≅ᴵ b → (L ⊞ a) ⊑ (L ⊞ b)
  res⊞ e = ≈-move (≈⊞ self e)

  WF-⊞ : WF L → ∀ a → WF (L ⊞ a)
  WF-⊞ w zero      = w
  WF-⊞ w (suc a)   = WF-⊞ w a
  WF-⊞ w (lim f s) = (λ n → mono⊞ (s n)) , (λ n → WF-⊞ w (f n))

  WF-times : WF L → WF (times L)
  WF-times w = mono⊞ , mono⊞ , (λ e → ⊑-of e) , WF-⊞ w
    where
    ⊑-of : ∀ {η} → η ≅ᴵ zero → (L ⊞ η) ⊑ (L ⊞ one)
    ⊑-of e = mono⊞ (⊑ᴵ-trans (≅→⊑ᴵ e) z⊑)

  step-times : L ⊑ times L
  step-times r with ≈-move self r
  ... | viaᴸ d p t = viaᴸ d (fst (suc p)) t

self⊞ : ∀ {L} → L ≈ L → ∀ a → (L ⊞ a) ≈ (L ⊞ a)
self⊞ e zero      = e
self⊞ e (suc a)   = s≈ (self⊞ e a)
self⊞ e (lim f s) = l≈ (λ n → self⊞ e (f n))

Ω·_ : ℕ → LI
Ω· zero        = zero
Ω· suc zero    = base
Ω· suc (suc m) = times (Ω· suc m)

Ω·ω : LI
Ω·ω = lim Ω·_

selfΩ : ∀ m → (Ω· m) ≈ (Ω· m)
selfΩ zero          = z≈
selfΩ (suc zero)    = b≈
selfΩ (suc (suc m)) = ≈times (selfΩ (suc m))

WFΩ : ∀ m → WF (Ω· m)
WFΩ zero          = tt
WFΩ (suc zero)    = tt
WFΩ (suc (suc m)) = Mono.WF-times _ (selfΩ (suc m)) (WFΩ (suc m))

stepΩ : ∀ m → (Ω· m) ⊑ (Ω· suc m)
stepΩ zero          ()
stepΩ (suc zero)    ()
stepΩ (suc (suc m)) = Mono.step-times _ (selfΩ (suc (suc m)))

WFΩ·ω : WF Ω·ω
WFΩ·ω = stepΩ , WFΩ

selfΩ·ω : Ω·ω ≈ Ω·ω
selfΩ·ω = l≈ selfΩ
```

## §6 层号的加法 (只有定义)

`_⊕ᴸ_`, `rp`: [InaccFloorIter](InaccFloorIter.lagda.md) 同名函数的 `LI` 版, 给 [UniformLvTheta](UniformLvTheta.lagda.md) 用. `⊕ᴸ` 不改 `lcl` 的高度, 所以 `base ⊕ᴸ times base` 的外层与内层高度相同 (见 [UniformLv](UniformLv.lagda.md)). **这里没有证书**: `⊑` 只看路径, 看不见原子 `base` (`base⊑zero` 是真的, 而 $\Omega\le0$ 是假的), 所以 `InaccFloorIter` 的 `P̂⊑` 不能照搬; 要加一个 "含 $\Omega$" 的标记. 没有写.

```agda
infixl 6 _⊕ᴸ_
_⊕ᴸ_ : LI → LI → LI
M ⊕ᴸ zero    = M
M ⊕ᴸ base    = times M
M ⊕ᴸ suc x   = suc (M ⊕ᴸ x)
M ⊕ᴸ lim h   = lim (λ n → M ⊕ᴸ h n)
M ⊕ᴸ lcl h g = lcl h (λ η → M ⊕ᴸ g η)

rp : LI → ℕ → LI
rp M zero    = zero
rp M (suc n) = M ⊕ᴸ rp M n

base⊑zero : base ⊑ zero
base⊑zero ()
```
