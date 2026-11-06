# SameV (四): `leg` 的部分和给出配对

> 不含记号. 入口 [SameV](SameV.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 实例 `I₁`. 只导入 stdlib, `OCF.Lean.CRw*`, `OCF.Lean.ValCRel`, `OCF.Lean.ValCBase`, [SameVRel](SameVRel.lagda.md).
>
> **问题.** 由 $a\le b$ (第 0 层的值关系) 要造 $1\boxplus\mathrm{leg}\,a$ 与 $1\boxplus\mathrm{leg}\,b$ 的层的配对. `l≤l σ h` 的各项 `h n` 彼此无关, 对 $a,b$ 本身的 ℕ-极限, 这样的推导给不出单值的配对. 但 **`leg` 把 ℕ-极限换成部分和**: 第 $n{+}1$ 项的层都在第 $n$ 项之后 (左边在 $\Sigma_n$ 之后, 右边在 $\Sigma_{\sigma(n+1)-1}$ 之后), 各项的层互不相干. 所以 `h n` 无关也不影响单值. 这是累加第一次在值的证明里起正面作用.
>
> **前缀 `Pf`.** 一项的层写成 `ap π y`, $y$ 是这一项里的尾. `pb P`: $P\boxplus y$; `pc π S`: `ap π (S ⊞ y)`. 用数据而不用 $\boxplus$ 的结合律: 结合律对 ℕ-极限要函数外延, 这里 `ap-s`, `ap-l` 不要.
>
> **配对 `Pr p π₁ π₂`** (对推导 $p$ 递归): `s≤s` 添一对 (左边的尾的顶, 右边的尾的顶); `≤s` 不变; `≤l n` 右边进第 $n$ 项; `l≤l` 是各项的并, 第 $n$ 项放在左边第 $n$ 项之后、右边第 $\sigma n$ 项之后. **只配 $\Omega$ 的层** (后继位置的前驱), 尾的 0 端不配.
>
> **律.** `dom`, `cod`: 配上的层夹在这一段的上下界之间. `fun`, `smP`: 单值, 保后继位置; 不同项之间由上下界与没有真回路得出. `matchOf`: 记录 `Match`, 再加一对 $(0,0)$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SameVLeg where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤′_; ≤′-refl; ≤′-step; _<′_)
open import Data.Nat.Properties using (<⇒<′; <-cmp; <-trans; m≤n⇒m<n∨m≡n)
import Data.Nat as N
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)
open import OCF.Lean.CRwBase hiding (Pr)
open import OCF.Lean.CRw using (I₁; leg; Σ₀; W₀; Lg-leg)
open import OCF.Lean.CRwFold I₁
open import OCF.Lean.ValCRel I₁
open import OCF.Lean.ValCBase I₁ hiding (ap)
open import OCF.Lean.SameVRel I₁
```

## §1 前缀

```agda
data Pf : Set where
  pb : Cd → Pf
  pc : Pf → Cd → Pf

ap : Pf → Cd → Cd
ap (pb P) y = P ⊞ y
ap (pc π S) y = ap π (S ⊞ y)

ap-s : ∀ π y → ap π (hs y) ≡ hs (ap π y)
ap-s (pb P) y = refl
ap-s (pc π S) y = ap-s π (S ⊞ y)

ap-l : ∀ π f → ap π (hl f) ≡ hl (λ n → ap π (f n))
ap-l (pb P) f = refl
ap-l (pc π S) f = ap-l π (λ n → S ⊞ f n)

ap⊲ : ∀ π {x y} → x ⊲ y → ap π x ⊲ ap π y
ap⊲ (pb P) q = ⊞-⊲ P q
ap⊲ (pc π S) q = ap⊲ π (⊞-⊲ S q)

pre : Pf → (ℕ → Cd) → ℕ → Pf
pre π G zero = π
pre π G (suc k) = pc π (Σ₀ G k)

pre-top : ∀ π G n → ap (pre π G n) (G n) ≡ ap π (Σ₀ G n)
pre-top π G zero = refl
pre-top π G (suc k) = refl

Σ₀⊲ : ∀ G {n m} → n ≤′ m → Σ₀ G n ⊲ Σ₀ G m
Σ₀⊲ G ≤′-refl = hself
Σ₀⊲ G {n} {suc m} (≤′-step q) = ⊲ᴮ-tr (Σ₀⊲ G q) (⊞-fst (Σ₀ G m) (G (suc m)))

-- 下一段的下界在前一段之上
pre-lo : ∀ π G n → ap π hz ⊲ ap (pre π G n) hz
pre-lo π G zero = hself
pre-lo π G (suc k) = ap⊲ π (z⊲ᴮ (Σ₀ G k))

mon : ∀ π G {n m} → suc n ≤′ m → ap π (Σ₀ G n) ⊲ ap (pre π G m) hz
mon π G ≤′-refl = hself
mon π G (≤′-step q) = ap⊲ π (Σ₀⊲ G (lw′ q))
  where
  lw′ : ∀ {i j} → suc i ≤′ j → i ≤′ j
  lw′ ≤′-refl = ≤′-step ≤′-refl
  lw′ (≤′-step p) = ≤′-step (lw′ p)

⊲-s : ∀ π {x y} → x ⊲ ap π y → x ⊲ ap π (hs y)
⊲-s π {x} {y} q = subst (x ⊲_) (sym (ap-s π y)) (hsuc q)

⊲-lim : ∀ π G n {x} → x ⊲ ap (pre π G n) (G n) → x ⊲ ap π (hl (Σ₀ G))
⊲-lim π G n {x} q = subst (x ⊲_) (sym (ap-l π (Σ₀ G))) (hlim n (subst (x ⊲_) (pre-top π G n) q))

Fs : (ℕ → Cd) → ℕ → Cd
Fs f n = leg (f n)

-- leg (hl f) 的第 n 个部分和不超过 hl 的位置: 同 ⊲-lim, 形状写成 leg (hl f)
⊲-L : ∀ π f n {x} → x ⊲ ap (pre π (Fs f) n) (leg (f n)) → x ⊲ ap π (leg (hl f))
⊲-L π f n q = ⊲-lim π (Fs f) n q

inc-lt : ∀ {σ} → Inc σ → ∀ {a b} → a < b → σ a < σ b
inc-lt {σ} i {a} {suc b} (N.s≤s p) with m≤n⇒m<n∨m≡n p
... | inj₁ a<b = <-trans (inc-lt i a<b) (i b)
... | inj₂ refl = i a
```

## §2 配对, 上下界

```agda
Pr : ∀ {a b} → LeAt hz a b → Pf → Pf → Cd → Cd → Set
Pr Rel.z≤ π₁ π₂ u v = ⊥
Pr (Rel.s≤s {a = a} {b = b} p) π₁ π₂ u v = ((u ≡ ap π₁ (leg a)) × (v ≡ ap π₂ (leg b))) ⊎ Pr p π₁ π₂ u v
Pr (Rel.≤s p) π₁ π₂ u v = Pr p π₁ π₂ u v
Pr (Rel.≤l {g = g} n p) π₁ π₂ u v = Pr p π₁ (pre π₂ (Fs g) n) u v
Pr (Rel.l≤l {f = f} {g = g} σ i h) π₁ π₂ u v = Σ ℕ (λ n → Pr (h n) (pre π₁ (Fs f) n) (pre π₂ (Fs g) (σ n)) u v)
Pr (Rel.≤Ω {κ = ()} _ _ _ _) π₁ π₂ u v
Pr (Rel.Ω≤Ω {κ = ()} _ _) π₁ π₂ u v

dom : ∀ {a b} (p : LeAt hz a b) π₁ π₂ {u v} → Pr p π₁ π₂ u v → (hs u ⊲ ap π₁ (leg a)) × (ap π₁ hz ⊲ u)
dom Rel.z≤ π₁ π₂ ()
dom (Rel.s≤s {a = a} p) π₁ π₂ (inj₁ (refl , _)) = subst (hs (ap π₁ (leg a)) ⊲_) (sym (ap-s π₁ (leg a))) hself , ap⊲ π₁ (z⊲ᴮ (leg a))
dom (Rel.s≤s p) π₁ π₂ (inj₂ r) = ⊲-s π₁ (proj₁ (dom p π₁ π₂ r)) , proj₂ (dom p π₁ π₂ r)
dom (Rel.≤s p) π₁ π₂ r = dom p π₁ π₂ r
dom (Rel.≤l n p) π₁ π₂ r = dom p π₁ _ r
dom (Rel.l≤l {f = f} {g = g} σ i h) π₁ π₂ (n , r) =
  ⊲-L π₁ f n (proj₁ (dom (h n) _ _ r)) , ⊲ᴮ-tr (pre-lo π₁ (Fs f) n) (proj₂ (dom (h n) _ _ r))
dom (Rel.≤Ω {κ = ()} _ _ _ _)
dom (Rel.Ω≤Ω {κ = ()} _ _)

cod : ∀ {a b} (p : LeAt hz a b) π₁ π₂ {u v} → Pr p π₁ π₂ u v → (hs v ⊲ ap π₂ (leg b)) × (ap π₂ hz ⊲ v)
cod Rel.z≤ π₁ π₂ ()
cod (Rel.s≤s {b = b} p) π₁ π₂ (inj₁ (_ , refl)) = subst (hs (ap π₂ (leg b)) ⊲_) (sym (ap-s π₂ (leg b))) hself , ap⊲ π₂ (z⊲ᴮ (leg b))
cod (Rel.s≤s p) π₁ π₂ (inj₂ r) = ⊲-s π₂ (proj₁ (cod p π₁ π₂ r)) , proj₂ (cod p π₁ π₂ r)
cod (Rel.≤s p) π₁ π₂ r = ⊲-s π₂ (proj₁ (cod p π₁ π₂ r)) , proj₂ (cod p π₁ π₂ r)
cod (Rel.≤l {g = g} n p) π₁ π₂ r =
  ⊲-L π₂ g n (proj₁ (cod p π₁ _ r)) , ⊲ᴮ-tr (pre-lo π₂ (Fs g) n) (proj₂ (cod p π₁ _ r))
cod (Rel.l≤l {f = f} {g = g} σ i h) π₁ π₂ (n , r) =
  ⊲-L π₂ g (σ n) (proj₁ (cod (h n) _ _ r)) , ⊲ᴮ-tr (pre-lo π₂ (Fs g) (σ n)) (proj₂ (cod (h n) _ _ r))
cod (Rel.≤Ω {κ = ()} _ _ _ _)
cod (Rel.Ω≤Ω {κ = ()} _ _)
```

## §3 单值, 保后继位置

相邻两段: 前一段的顶在后一段的下界之下 (`gap`).

```agda
gap : ∀ π G {n m} → n < m → ∀ {x y} → x ⊲ ap (pre π G n) (G n) → ap (pre π G m) hz ⊲ y → x ⊲ y
gap π G {n} {m} n<m {x} p q = ⊲ᴮ-tr (subst (x ⊲_) (pre-top π G n) p) (⊲ᴮ-tr (mon π G (<⇒<′ n<m)) q)

fun : ∀ {a b} (p : LeAt hz a b) π₁ π₂ {u v v′} → Pr p π₁ π₂ u v → Pr p π₁ π₂ u v′ → v ≡ v′
fun Rel.z≤ π₁ π₂ () _
fun (Rel.s≤s p) π₁ π₂ (inj₁ (_ , e)) (inj₁ (_ , e′)) = trans e (sym e′)
fun (Rel.s≤s p) π₁ π₂ (inj₁ (refl , _)) (inj₂ r) = ⊥-elim (nos (proj₁ (dom p π₁ π₂ r)))
fun (Rel.s≤s p) π₁ π₂ (inj₂ r) (inj₁ (refl , _)) = ⊥-elim (nos (proj₁ (dom p π₁ π₂ r)))
fun (Rel.s≤s p) π₁ π₂ (inj₂ r) (inj₂ r′) = fun p π₁ π₂ r r′
fun (Rel.≤s p) π₁ π₂ r r′ = fun p π₁ π₂ r r′
fun (Rel.≤l n p) π₁ π₂ r r′ = fun p π₁ _ r r′
fun (Rel.l≤l {f = f} σ i h) π₁ π₂ (n , r) (n′ , r′) with <-cmp n n′
... | tri< n<n′ _ _ = ⊥-elim (nos (gap π₁ (Fs f) n<n′ (proj₁ (dom (h n) _ _ r)) (proj₂ (dom (h n′) _ _ r′))))
... | tri≈ _ refl _ = fun (h n) _ _ r r′
... | tri> _ _ n′<n = ⊥-elim (nos (gap π₁ (Fs f) n′<n (proj₁ (dom (h n′) _ _ r′)) (proj₂ (dom (h n) _ _ r))))
fun (Rel.≤Ω {κ = ()} _ _ _ _)
fun (Rel.Ω≤Ω {κ = ()} _ _)

smP : ∀ {a b} (p : LeAt hz a b) π₁ π₂ {j j′ u u′} → Pr p π₁ π₂ j j′ → Pr p π₁ π₂ u u′ → hs j ⊲ u → hs j′ ⊲ u′
smP Rel.z≤ π₁ π₂ () _
smP (Rel.s≤s p) π₁ π₂ (inj₁ (refl , _)) (inj₁ (e , _)) q = ⊥-elim (nos (subst (_ ⊲_) e q))
smP (Rel.s≤s p) π₁ π₂ (inj₁ (refl , _)) (inj₂ r) q = ⊥-elim (nos′ q (⊏⊑ (proj₁ (dom p π₁ π₂ r))))
smP (Rel.s≤s p) π₁ π₂ (inj₂ r) (inj₁ (_ , refl)) q = proj₁ (cod p π₁ π₂ r)
smP (Rel.s≤s p) π₁ π₂ (inj₂ r) (inj₂ r′) q = smP p π₁ π₂ r r′ q
smP (Rel.≤s p) π₁ π₂ r r′ q = smP p π₁ π₂ r r′ q
smP (Rel.≤l n p) π₁ π₂ r r′ q = smP p π₁ _ r r′ q
smP (Rel.l≤l {f = f} {g = g} σ i h) π₁ π₂ (n , r) (n′ , r′) q with <-cmp n n′
... | tri< n<n′ _ _ = gap π₂ (Fs g) (inc-lt i n<n′) (proj₁ (cod (h n) _ _ r)) (proj₂ (cod (h n′) _ _ r′))
... | tri≈ _ refl _ = smP (h n) _ _ r r′ q
... | tri> _ _ n′<n = ⊥-elim (nos′ q (⊏⊑ (gap π₁ (Fs f) n′<n (proj₁ (dom (h n′) _ _ r′)) (proj₂ (dom (h n) _ _ r)))))
smP (Rel.≤Ω {κ = ()} _ _ _ _)
smP (Rel.Ω≤Ω {κ = ()} _ _)
```

## §4 配对的记录

世界 $1\boxplus\mathrm{leg}\,a$. 配对 = $(0,0)$ 加上 `Pr`. `lgC`: 世界合法 (`pp` 要它: 合法树上真第一位置的层是后继位置).

```agda
π₀ : Pf
π₀ = pb W₀

C : Cd → Cd
C a = ap π₀ (leg a)

lgC : ∀ a → LgB (C a)
lgC a = Lg-⊞ W₀ (leg a) tt (Lg-leg a)

s⊲s : ∀ {u t} → hs u ⊲ hs t → u ⊲ t
s⊲s hself = hself
s⊲s (hsuc q) = ⊏⊑ q

module M {a b} (p : LeAt hz a b) where
  _≈_ : Cd → Cd → Set
  u ≈ v = ((u ≡ hz) × (v ≡ hz)) ⊎ Pr p π₀ π₀ u v

  noz : ∀ {x : Cd} → hs x ⊲ hz → ⊥
  noz ()

  domP = λ {u} {v} (r : Pr p π₀ π₀ u v) → dom p π₀ π₀ r
  codP = λ {u} {v} (r : Pr p π₀ π₀ u v) → cod p π₀ π₀ r

  ppP : ∀ {t t′ u u′} → Pr p π₀ π₀ t t′ → Pr p π₀ π₀ u u′ → Pp t u → Pp t′ u′
  ppP {t} {t′} {u} {u′} r r′ pq with cmpB (proj₁ (dom p π₀ π₀ r)) (proj₁ (dom p π₀ π₀ r′)) tt (lgC a)
  ... | inj₁ c = ⊥-elim (noPP pq (s⊲s c))
  ... | inj₂ hself = ⊥-elim (noPP pq hself)
  ... | inj₂ (hsuc c) = s⊲→Pp (smP p π₀ π₀ r r′ c)

  noPz : ∀ {t} → Pp t hz → ⊥
  noPz ()

  match : Match
  match = record { _~_ = _≈_ ; ~fun = f ; ~s = s ; ~pp = pq }
    where
    f : ∀ {u v v′} → u ≈ v → u ≈ v′ → v ≡ v′
    f (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
    f (inj₁ (refl , _)) (inj₂ r) = ⊥-elim (noz (proj₂ (dom p π₀ π₀ r)))
    f (inj₂ r) (inj₁ (refl , _)) = ⊥-elim (noz (proj₂ (dom p π₀ π₀ r)))
    f (inj₂ r) (inj₂ r′) = fun p π₀ π₀ r r′
    s : ∀ {j j′ u u′} → j ≈ j′ → u ≈ u′ → hs j ⊲ u → hs j′ ⊲ u′
    s _ (inj₁ (refl , _)) q = ⊥-elim (noz q)
    s (inj₁ (_ , refl)) (inj₂ r′) q = proj₂ (cod p π₀ π₀ r′)
    s (inj₂ r) (inj₂ r′) q = smP p π₀ π₀ r r′ q
    pq : ∀ {t t′ u u′} → t ≈ t′ → u ≈ u′ → Pp t u → Pp t′ u′
    pq _ (inj₁ (refl , _)) c = ⊥-elim (noPz c)
    pq (inj₁ (_ , refl)) (inj₂ r′) c = s⊲→Pp (proj₂ (cod p π₀ π₀ r′))
    pq (inj₂ r) (inj₂ r′) c = ppP r r′ c

  z≈ : hz ≈ hz
  z≈ = inj₁ (refl , refl)
```

## 结论 (按档)

- **[定理, 不用 UIP, 不用函数外延]** 前缀 `Pf`, `ap`, `ap-s`, `ap-l`, `ap⊲`, `pre`, `pre-top`, `pre-lo`, `mon`, `gap`; **`Pr`** (由 `LeAt hz a b` 的**任意**推导给出的配对), `dom`, `cod`, **`fun`**, **`smP`**; **`M.match`**: `Match` 的实例.
