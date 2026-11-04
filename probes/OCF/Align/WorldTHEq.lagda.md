# 带高度的世界: 结构等价与折叠的同余

> 不含记号. 结论写在 [WorldTH](WorldTH.lagda.md). `x ≈ y`: 对项递归的部分等价, 与 [CumReadCFEq](CumReadCFEq.lagda.md) 同形, 多三件:
>
> - **下标只模结构等价 (`≈ᴬ`).** 第 0 层闭包的链点读自输出, 同一个项算两次, 输出只差逐点等价, 没有函数外延就不字面相等. 所以层, 世界都模 `≈ᴬ`.
> - **`os`, `oi`, `od`, `oc` 要层和世界等价.** 输出闭包的世界 $\max(u,t,a)$ 读这两样.
> - `mx≈`: $\max$ 的值模 `≈ᴬ` 与证据无关. `ψQ`: 目标模 `≈ᴬ` 相同, 折叠保 `≈`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHEq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲; Rk; keep; rise; cmpN; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next; _⊞_; cumA; cs)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.WorldTHW
```

## §1 下标的结构等价

```agda
infix 4 _≈ᴬ_ _⊏_
data _≈ᴬ_ : A → A → Set where
  z≈ : azero ≈ᴬ azero
  s≈ : ∀ {a b} → a ≈ᴬ b → asuc a ≈ᴬ asuc b
  l≈ : ∀ {f g} → (∀ n → f n ≈ᴬ g n) → alim f ≈ᴬ alim g

≈ᴬ-refl : ∀ a → a ≈ᴬ a
≈ᴬ-refl azero = z≈
≈ᴬ-refl (asuc a) = s≈ (≈ᴬ-refl a)
≈ᴬ-refl (alim f) = l≈ (λ n → ≈ᴬ-refl (f n))

≈ᴬ-sym : ∀ {a b} → a ≈ᴬ b → b ≈ᴬ a
≈ᴬ-sym z≈ = z≈
≈ᴬ-sym (s≈ e) = s≈ (≈ᴬ-sym e)
≈ᴬ-sym (l≈ h) = l≈ (λ n → ≈ᴬ-sym (h n))

≈ᴬ-trans : ∀ {a b c} → a ≈ᴬ b → b ≈ᴬ c → a ≈ᴬ c
≈ᴬ-trans z≈ z≈ = z≈
≈ᴬ-trans (s≈ e) (s≈ d) = s≈ (≈ᴬ-trans e d)
≈ᴬ-trans (l≈ h) (l≈ k) = l≈ (λ n → ≈ᴬ-trans (h n) (k n))

-- 真的第一位置
data _⊏_ : A → A → Set where
  sf : ∀ {a b} → a ⊲ b → a ⊏ asuc b
  lf : ∀ {a f} n → a ⊲ f n → a ⊏ alim f

⊏→⊲ : ∀ {a b} → a ⊏ b → a ⊲ b
⊏→⊲ (sf p) = C.suc p
⊏→⊲ (lf n p) = C.lim n p

≪→⊏ : ∀ {a b} → a ≪ b → a ⊏ b
≪→⊏ C.zero = sf C.self
≪→⊏ (C.suc r) = sf (⊏→⊲ (≪→⊏ r))
≪→⊏ (C.lim n r) = lf n (⊏→⊲ (≪→⊏ r))

⊏⊲ : ∀ {a b c} → a ⊏ b → b ⊲ c → a ⊏ c
⊏⊲ r C.self = r
⊏⊲ r (C.suc q) = sf (⊏→⊲ (⊏⊲ r q))
⊏⊲ r (C.lim n q) = lf n (⊏→⊲ (⊏⊲ r q))

⊲or : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (a ⊏ b)
⊲or C.self = inj₁ refl
⊲or (C.suc p) = inj₂ (sf p)
⊲or (C.lim n p) = inj₂ (lf n p)

⊲-mv : ∀ {a b b′} → a ⊲ b → b ≈ᴬ b′ → Σ A (λ a′ → (a′ ⊲ b′) × (a ≈ᴬ a′))
⊲-mv {b′ = b′} C.self e = b′ , C.self , e
⊲-mv (C.suc p) (s≈ e) with ⊲-mv p e
... | a′ , q , d = a′ , C.suc q , d
⊲-mv (C.lim n p) (l≈ h) with ⊲-mv p (h n)
... | a′ , q , d = a′ , C.lim n q , d

⊏-mv : ∀ {a b b′} → a ⊏ b → b ≈ᴬ b′ → Σ A (λ a′ → (a′ ⊏ b′) × (a ≈ᴬ a′))
⊏-mv (sf p) (s≈ e) with ⊲-mv p e
... | a′ , q , d = a′ , sf q , d
⊏-mv (lf n p) (l≈ h) with ⊲-mv p (h n)
... | a′ , q , d = a′ , lf n q , d

data Acc⊏ (a : A) : Set where
  acc : (∀ {b} → b ⊏ a → Acc⊏ b) → Acc⊏ a

acc⊲ : ∀ a {b} → b ⊲ a → Acc⊏ b
acc⊏ : ∀ a {b} → b ⊏ a → Acc⊏ b
acc⊲ a C.self = acc (acc⊏ a)
acc⊲ (asuc a) (C.suc p) = acc⊲ a p
acc⊲ (alim f) (C.lim n p) = acc⊲ (f n) p
acc⊏ (asuc a) (sf p) = acc⊲ a p
acc⊏ (alim f) (lf n p) = acc⊲ (f n) p

irr′ : ∀ {a b} → Acc⊏ a → b ⊏ a → b ≈ᴬ a → ⊥
irr′ (acc h) r e with ⊏-mv r (≈ᴬ-sym e)
... | b₂ , r₂ , d = irr′ (h r) r₂ (≈ᴬ-sym d)

irr : ∀ {a b} → b ⊏ a → b ≈ᴬ a → ⊥
irr {a} = irr′ (acc (acc⊏ a))

-- k ⊏ t, t ≈ t′, t′ ⊲ k′, k′ ≈ k 相撞
clash⊏ : ∀ {k t k′ t′} → k ⊏ t → t′ ⊲ k′ → k ≈ᴬ k′ → t ≈ᴬ t′ → ⊥
clash⊏ s q ek et with ⊲-mv q (≈ᴬ-sym ek)
... | t″ , q″ , d with ⊏-mv s (≈ᴬ-trans et d)
...   | k₂ , r₂ , d₂ = irr (⊏⊲ r₂ q″) (≈ᴬ-sym d₂)

clash : ∀ {k t k′ t′} → k ≪ t → t′ ⊲ k′ → k ≈ᴬ k′ → t ≈ᴬ t′ → ⊥
clash s = clash⊏ (≪→⊏ s)

-- 反对称, 模 ≈ᴬ
anti : ∀ {a b a′ b′} → a ⊲ b → b′ ⊲ a′ → a ≈ᴬ a′ → b ≈ᴬ b′ → a ≈ᴬ b
anti {a} p q ea eb with ⊲or p
... | inj₁ refl = ≈ᴬ-refl a
... | inj₂ r = ⊥-elim (clash⊏ r q ea eb)

⊲≪ : ∀ {k a b} → k ≪ a → a ⊲ b → k ⊲ b
⊲≪ r q = ⊲-tr (≪⊲ r) q
```

## §1′ 高度的等价

```agda
infix 4 _≈ᴴ_
data _≈ᴴ_ : Hg → Hg → Set where
  ht≈ : ∀ {a b} → a ≈ᴬ b → ht a ≈ᴴ ht b
  tφ≈ : ∀ {f g} → (∀ a b → a ≈ᴬ b → f a ≈ᴴ g b) → tφ f ≈ᴴ tφ g

≈ᴴ-refl′ : ∀ {a b} → a ≈ᴬ b → ht a ≈ᴴ ht b
≈ᴴ-refl′ = ht≈

top≈ : top ≈ᴴ top
top≈ = tφ≈ (λ a b e → ht≈ e)

≈ᴴ-sym : ∀ {p q} → p ≈ᴴ q → q ≈ᴴ p
≈ᴴ-sym (ht≈ e) = ht≈ (≈ᴬ-sym e)
≈ᴴ-sym (tφ≈ h) = tφ≈ (λ a b e → ≈ᴴ-sym (h b a (≈ᴬ-sym e)))

<⊏ : ∀ {a b} → ht a <ᴴ ht b → a ⊏ b
<⊏ here = sf C.self
<⊏ (st j) = sf (⊏→⊲ (<⊏ j))
<⊏ (lh n) = lf n C.self
<⊏ (ll n j) = lf n (⊏→⊲ (<⊏ j))

-- 两边比较高度的结果对齐
data AlH {p q p′ q′ m m′} : HC p q m → HC p′ q′ m′ → Set where
  al-l : ∀ {i b i′ b′} → AlH (hlt i b) (hlt i′ b′)
  al-g : ∀ {i i′} → AlH (hgt i) (hgt i′)
  al-e : ∀ {e e′} → AlH (heq e) (heq e′)

le-g : ∀ {a a′ b′} → a ≈ᴬ a′ → a ≈ᴬ b′ → ht b′ <ᴴ ht a′ → ⊥
le-g ea eb l = irr (<⊏ l) (≈ᴬ-trans (≈ᴬ-sym eb) ea)

le-l : ∀ {a a′ b′} → a ≈ᴬ a′ → a ≈ᴬ b′ → ht a′ <ᴴ ht b′ → ⊥
le-l ea eb l = irr (<⊏ l) (≈ᴬ-trans (≈ᴬ-sym ea) eb)

rg : ∀ {a b c} → ht b <ᴴ ht a → a ≈ᴬ c → b ≈ᴬ c → ⊥
rg l ea eb = irr (<⊏ l) (≈ᴬ-trans eb (≈ᴬ-sym ea))

rl : ∀ {a b c} → ht a <ᴴ ht b → a ≈ᴬ c → b ≈ᴬ c → ⊥
rl l ea eb = irr (<⊏ l) (≈ᴬ-trans ea (≈ᴬ-sym eb))

alF : ∀ {a b a′ b′ m m′} (ea : a ≈ᴬ a′) (eb : b ≈ᴬ b′) (pm : a ⊲ m) (qm : b ⊲ m) (w : Lg m) (pm′ : a′ ⊲ m′) (qm′ : b′ ⊲ m′) (w′ : Lg m′) →
      AlH (hcmp (ht a) (ht b) pm qm w) (hcmp (ht a′) (ht b′) pm′ qm′ w′)
alF {a} {b} {a′} {b′} ea eb pm qm w pm′ qm′ w′ with cmpF pm qm w | cmpF pm′ qm′ w′
... | inj₁ x | inj₁ y with lt⊲ x | lt⊲ y
...   | inj₁ refl | inj₁ refl = al-e
...   | inj₁ refl | inj₂ l′ = ⊥-elim (le-g ea eb l′)
...   | inj₂ l | inj₁ refl = ⊥-elim (rg l ea eb)
...   | inj₂ l | inj₂ l′ = al-g
alF {a} {b} {a′} {b′} ea eb pm qm w pm′ qm′ w′ | inj₂ x | inj₂ y with lt⊲ x | lt⊲ y
...   | inj₁ refl | inj₁ refl = al-e
...   | inj₁ refl | inj₂ l′ = ⊥-elim (le-l ea eb l′)
...   | inj₂ l | inj₁ refl = ⊥-elim (rl l ea eb)
...   | inj₂ l | inj₂ l′ = al-l
alF {a} {b} {a′} {b′} ea eb pm qm w pm′ qm′ w′ | inj₁ x | inj₂ y with lt⊲ x | lt⊲ y
...   | inj₁ refl | inj₁ refl = al-e
...   | inj₁ refl | inj₂ l′ = ⊥-elim (le-l ea eb l′)
...   | inj₂ l | inj₁ refl = ⊥-elim (rg l ea eb)
...   | inj₂ l | inj₂ l′ = ⊥-elim (clash⊏ (<⊏ l) (⊏→⊲ (<⊏ l′)) eb ea)
alF {a} {b} {a′} {b′} ea eb pm qm w pm′ qm′ w′ | inj₂ x | inj₁ y with lt⊲ x | lt⊲ y
...   | inj₁ refl | inj₁ refl = al-e
...   | inj₁ refl | inj₂ l′ = ⊥-elim (le-g ea eb l′)
...   | inj₂ l | inj₁ refl = ⊥-elim (rl l ea eb)
...   | inj₂ l | inj₂ l′ = ⊥-elim (clash⊏ (<⊏ l) (⊏→⊲ (<⊏ l′)) ea eb)

hc≈ : ∀ {p q p′ q′ m m′} (ep : p ≈ᴴ p′) (eq : q ≈ᴴ q′) (pm : HO p m) (qm : HO q m) (w : Lg m) (pm′ : HO p′ m′) (qm′ : HO q′ m′) (w′ : Lg m′) →
      AlH (hcmp p q pm qm w) (hcmp p′ q′ pm′ qm′ w′)
hc≈ (ht≈ ea) (ht≈ eb) pm qm w pm′ qm′ w′ = alF ea eb pm qm w pm′ qm′ w′
hc≈ (ht≈ ea) (tφ≈ h) pm refl w pm′ refl w′ = al-l
hc≈ (tφ≈ h) (ht≈ eb) refl qm w refl qm′ w′ = al-g
hc≈ (tφ≈ h) (tφ≈ k) refl refl w refl refl w′ = al-e
```

## §2 $\max$ 的值

```agda
data Mis (m u : A) (q : Hg) (t : A) (p : Hg) (a : A) : Set where
  iu : m ≡ u → Mis m u q t p a
  it : m ≡ t → Mis m u q t p a
  ia : m ≡ a → Mis m u q t p a
  iq : m ≡ hA q → Mis m u q t p a
  ip : m ≡ hA p → Mis m u q t p a

mx-is : ∀ {u q t p a v} (gu : Gw u) (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v) → Mis (Mx.m (mx gu gv uv tv av)) u q t p a
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) with cmpF uv tv (lgw gv)
... | inj₁ _ with cmpF uv av (lgw gv)
...   | inj₁ _ with cmpF uv (hw qv) (lgw gv)
...     | inj₁ _ with cmpF uv (hw pv) (lgw gv)
...       | inj₁ _ = iu refl
...       | inj₂ _ = ip refl
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) | inj₁ _ | inj₁ _ | inj₂ _ with cmpF (hw qv) (hw pv) (lgw gv)
...       | inj₁ _ = iq refl
...       | inj₂ _ = ip refl
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) | inj₁ _ | inj₂ _ with cmpF av (hw qv) (lgw gv)
...     | inj₁ _ with cmpF av (hw pv) (lgw gv)
...       | inj₁ _ = ia refl
...       | inj₂ _ = ip refl
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) | inj₁ _ | inj₂ _ | inj₂ _ with cmpF (hw qv) (hw pv) (lgw gv)
...       | inj₁ _ = iq refl
...       | inj₂ _ = ip refl
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) | inj₂ _ with cmpF tv av (lgw gv)
...   | inj₁ _ with cmpF tv (hw qv) (lgw gv)
...     | inj₁ _ with cmpF tv (hw pv) (lgw gv)
...       | inj₁ _ = it refl
...       | inj₂ _ = ip refl
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) | inj₂ _ | inj₁ _ | inj₂ _ with cmpF (hw qv) (hw pv) (lgw gv)
...       | inj₁ _ = iq refl
...       | inj₂ _ = ip refl
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) | inj₂ _ | inj₂ _ with cmpF av (hw qv) (lgw gv)
...     | inj₁ _ with cmpF av (hw pv) (lgw gv)
...       | inj₁ _ = ia refl
...       | inj₂ _ = ip refl
mx-is {u} {q} {t} {p} {a} gu gv uv (tv , qv) (av , pv) | inj₂ _ | inj₂ _ | inj₂ _ with cmpF (hw qv) (hw pv) (lgw gv)
...       | inj₁ _ = iq refl
...       | inj₂ _ = ip refl

isOf : ∀ {u q t p a v} (gu : Gw u) (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v) {M : Mx u q t p a v} → mx gu gv uv tv av ≡ M → Mis (Mx.m M) u q t p a
isOf gu gv uv tv av refl = mx-is gu gv uv tv av

hA≈ : ∀ {p q} → p ≈ᴴ q → hA p ≈ᴬ hA q
hA≈ (ht≈ e) = e
hA≈ (tφ≈ h) = z≈

-- m 被对面的上界控制
ctrl : ∀ {m u q t p a m′ u′ q′ t′ p′ a′} → Mis m u q t p a → u′ ⊲ m′ → LB q′ t′ m′ → LB p′ a′ m′ → u ≈ᴬ u′ → (q ≈ᴴ q′) × (t ≈ᴬ t′) → (p ≈ᴴ p′) × (a ≈ᴬ a′) →
       Σ A (λ x′ → (x′ ⊲ m′) × (m ≈ᴬ x′))
ctrl {u′ = u′} (iu refl) p₁ p₂ p₃ e₁ e₂ e₃ = u′ , p₁ , e₁
ctrl {t′ = t′} (it refl) p₁ p₂ p₃ e₁ e₂ e₃ = t′ , proj₁ p₂ , proj₂ e₂
ctrl {a′ = a′} (ia refl) p₁ p₂ p₃ e₁ e₂ e₃ = a′ , proj₁ p₃ , proj₂ e₃
ctrl {q′ = q′} (iq refl) p₁ p₂ p₃ e₁ e₂ e₃ = hA q′ , hw (proj₂ p₂) , hA≈ (proj₁ e₂)
ctrl {p′ = p′} (ip refl) p₁ p₂ p₃ e₁ e₂ e₃ = hA p′ , hw (proj₂ p₃) , hA≈ (proj₁ e₃)

m≈ : ∀ {m u q t p a m′ u′ q′ t′ p′ a′} → Mis m u q t p a → Mis m′ u′ q′ t′ p′ a′ → u ⊲ m → LB q t m → LB p a m → u′ ⊲ m′ → LB q′ t′ m′ → LB p′ a′ m′ →
     u ≈ᴬ u′ → (q ≈ᴴ q′) × (t ≈ᴬ t′) → (p ≈ᴴ p′) × (a ≈ᴬ a′) → m ≈ᴬ m′
m≈ is is′ p₁ p₂ p₃ p₁′ p₂′ p₃′ e₁ e₂ e₃ with ctrl is p₁′ p₂′ p₃′ e₁ e₂ e₃ | ctrl is′ p₁ p₂ p₃ (≈ᴬ-sym e₁) (≈ᴴ-sym (proj₁ e₂) , ≈ᴬ-sym (proj₂ e₂)) (≈ᴴ-sym (proj₁ e₃) , ≈ᴬ-sym (proj₂ e₃))
... | x′ , xp , xe | y , yp , ye = ≈ᴬ-sym (≈ᴬ-trans ye (anti yp xp (≈ᴬ-sym ye) xe))
```

## §3 `≈`

```agda
infix 4 _≈_
_≈_ : ∀ {p a u p′ a′ u′} → 𝓞 p a u → 𝓞 p′ a′ u′ → Set
ELl : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) → Low p j k u → 𝓞 p′ a′ u′ → Set
ELr : ∀ {p a u p′ h k u′} → 𝓞 p a u → (j : h <ᴴ p′) → Low p′ j k u′ → Set
EqW : ∀ {p h k u p′ h′ k′ u′} (j : h <ᴴ p) (j′ : h′ <ᴴ p′) → Low p j k u → Low p′ j′ k′ u′ → Set
EqV : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) → Vs p a R u → Vs p′ a′ R′ u′ → Set
EVC : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) → Vc p a P u → Vs p′ a′ R′ u′ → Set
ELO : ∀ {p b u p′ a′ b′ u′} → 𝓞 p b u → (R′ : Strict b′ a′) → Vs p′ a′ R′ u′ → Set
EOC : ∀ {p b u p′ a′ b′ u′} → 𝓞 p b u → (P : b′ ⊲ a′) → Vc p′ a′ P u′ → Set

oe es x ≈ y = x ≈ y
oe (el n) x ≈ y = x ≈ y
oL j k e x ≈ y = ELl j x y
ow p g x ≈ y = x ≈ y
_≈_ X@o0 (oe es y) = X ≈ y
_≈_ X@o0 (oe (el n) y) = X ≈ y
_≈_ X@o0 (oL j k₂ e y) = ELr X j y
_≈_ X@o0 (ow p g y) = X ≈ y
_≈_ X@(os x) (oe es y) = X ≈ y
_≈_ X@(os x) (oe (el n) y) = X ≈ y
_≈_ X@(os x) (oL j k₂ e y) = ELr X j y
_≈_ X@(os x) (ow p g y) = X ≈ y
_≈_ X@(ol F) (oe es y) = X ≈ y
_≈_ X@(ol F) (oe (el n) y) = X ≈ y
_≈_ X@(ol F) (oL j k₂ e y) = ELr X j y
_≈_ X@(ol F) (ow p g y) = X ≈ y
_≈_ X@(oi r h) (oe es y) = X ≈ y
_≈_ X@(oi r h) (oe (el n) y) = X ≈ y
_≈_ X@(oi r h) (oL j k₂ e y) = ELr X j y
_≈_ X@(oi r h) (ow p g y) = X ≈ y
_≈_ X@(od i k r h) (oe es y) = X ≈ y
_≈_ X@(od i k r h) (oe (el n) y) = X ≈ y
_≈_ X@(od i k r h) (oL j k₂ e y) = ELr X j y
_≈_ X@(od i k r h) (ow p g y) = X ≈ y
_≈_ X@(oc x h) (oe es y) = X ≈ y
_≈_ X@(oc x h) (oe (el n) y) = X ≈ y
_≈_ X@(oc x h) (oL j k₂ e y) = ELr X j y
_≈_ X@(oc x h) (ow p g y) = X ≈ y
o0 ≈ o0 = ⊤
_≈_ {p} {a} {u} {p′} {a′} {u′} (os x) (os y) = (p ≈ᴴ p′) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (x ≈ y)
ol F ≈ ol G = ∀ n → F n ≈ G n
_≈_ {p} {a} {u} {p′} {a′} {u′} (oi {k = k} r h) (oi {k = k′} r′ h′) =
  (p ≈ᴴ p′) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (k ≈ᴬ k′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqV (≪S r) (≪S r′) y y′ → h q g y ≈ h′ q′ g′ y′)
_≈_ {p} {a} {u} {p′} {a′} {u′} (od {h = h₀} j k r h) (od {h = h₁} j′ k′ r′ h′) =
  (p ≈ᴴ p′) × (h₀ ≈ᴴ h₁) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (k ≈ᴬ k′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqW j j′ y y′ → h q g y ≈ h′ q′ g′ y′)
_≈_ {p} {a} {u} {p′} {a′} {u′} (oc x h) (oc x′ h′) =
  (p ≈ᴴ p′) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (x ≈ x′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → h q g ≈ h′ q′ g′)
_ ≈ _ = ⊥

ELl here x y = x ≈ y
ELl (lh n₉) x y = x ≈ y
ELl (tp a₉) x y = x ≈ y
ELl (st j) x y = ELl j x y
ELl (ll n₉ j) x y = ELl j x y
ELl (tq a₉ j) x y = ELl j x y
ELr X here y = X ≈ y
ELr X (lh n₉) y = X ≈ y
ELr X (tp a₉) y = X ≈ y
ELr X (st j) y = ELr X j y
ELr X (ll n₉ j) y = ELr X j y
ELr X (tq a₉ j) y = ELr X j y
EqW here j′ x y = ELr x j′ y
EqW (lh n₉) j′ x y = ELr x j′ y
EqW (tp a₉) j′ x y = ELr x j′ y
EqW (st j) j′ x y = EqW j j′ x y
EqW (ll n₉ j) j′ x y = EqW j j′ x y
EqW (tq a₉ j) j′ x y = EqW j j′ x y
EqV (ss P) R′ y y′ = EVC P R′ y y′
EqV (sl n P) R′ y y′ = EVC P R′ y y′
EVC C.self R′ y y′ = ELO y R′ y′
EVC (C.suc P) R′ y y′ = EVC P R′ y y′
EVC (C.lim n P) R′ y y′ = EVC P R′ y y′
ELO x (ss P) y′ = EOC x P y′
ELO x (sl n P) y′ = EOC x P y′
EOC x C.self y′ = x ≈ y′
EOC x (C.suc P) y′ = EOC x P y′
EOC x (C.lim n P) y′ = EOC x P y′
```

## §4 换视角

```agda
Ll→ : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} → ELl j x y → outL j x ≈ y
Ll→ here x e = e
Ll→ (lh n₉) x e = e
Ll→ (tp a₉) x e = e
Ll→ (st j) x e = Ll→ j x e
Ll→ (ll n₉ j) x e = Ll→ j x e
Ll→ (tq a₉ j) x e = Ll→ j x e

→Ll : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} → outL j x ≈ y → ELl j x y
→Ll here x e = e
→Ll (lh n₉) x e = e
→Ll (tp a₉) x e = e
→Ll (st j) x e = →Ll j x e
→Ll (ll n₉ j) x e = →Ll j x e
→Ll (tq a₉ j) x e = →Ll j x e

Lr→ : ∀ {p a u p′ h k u′} (X : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) → ELr X j y → X ≈ outL j y
Lr→ X here y e = e
Lr→ X (lh n₉) y e = e
Lr→ X (tp a₉) y e = e
Lr→ X (st j) y e = Lr→ X j y e
Lr→ X (ll n₉ j) y e = Lr→ X j y e
Lr→ X (tq a₉ j) y e = Lr→ X j y e

→Lr : ∀ {p a u p′ h k u′} (X : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) → X ≈ outL j y → ELr X j y
→Lr X here y e = e
→Lr X (lh n₉) y e = e
→Lr X (tp a₉) y e = e
→Lr X (st j) y e = →Lr X j y e
→Lr X (ll n₉ j) y e = →Lr X j y e
→Lr X (tq a₉ j) y e = →Lr X j y e

W→ : ∀ {p h k u p′ h′ k′ u′} (j : h <ᴴ p) (j′ : h′ <ᴴ p′) (x : Low p j k u) (y : Low p′ j′ k′ u′) → EqW j j′ x y → outL j x ≈ outL j′ y
W→ here j′ x y e = Lr→ x j′ y e
W→ (lh n₉) j′ x y e = Lr→ x j′ y e
W→ (tp a₉) j′ x y e = Lr→ x j′ y e
W→ (st j) j′ x y e = W→ j j′ x y e
W→ (ll n₉ j) j′ x y e = W→ j j′ x y e
W→ (tq a₉ j) j′ x y e = W→ j j′ x y e

→W : ∀ {p h k u p′ h′ k′ u′} (j : h <ᴴ p) (j′ : h′ <ᴴ p′) (x : Low p j k u) (y : Low p′ j′ k′ u′) → outL j x ≈ outL j′ y → EqW j j′ x y
→W here j′ x y e = →Lr x j′ y e
→W (lh n₉) j′ x y e = →Lr x j′ y e
→W (tp a₉) j′ x y e = →Lr x j′ y e
→W (st j) j′ x y e = →W j j′ x y e
→W (ll n₉ j) j′ x y e = →W j j′ x y e
→W (tq a₉ j) j′ x y e = →W j j′ x y e

V→ : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) (y : Vs p a R u) (y′ : Vs p′ a′ R′ u′) → EqV R R′ y y′ → outS R y ≈ outS R′ y′
VC→ : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) (y : Vc p a P u) (y′ : Vs p′ a′ R′ u′) → EVC P R′ y y′ → outC P y ≈ outS R′ y′
LO→ : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (R′ : Strict b′ a′) (y′ : Vs p′ a′ R′ u′) → ELO x R′ y′ → x ≈ outS R′ y′
OC→ : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (P : b′ ⊲ a′) (y′ : Vc p′ a′ P u′) → EOC x P y′ → x ≈ outC P y′
V→ (ss P) R′ y y′ e = VC→ P R′ y y′ e
V→ (sl n P) R′ y y′ e = VC→ P R′ y y′ e
VC→ C.self R′ y y′ e = LO→ y R′ y′ e
VC→ (C.suc P) R′ y y′ e = VC→ P R′ y y′ e
VC→ (C.lim n P) R′ y y′ e = VC→ P R′ y y′ e
LO→ x (ss P) y′ e = OC→ x P y′ e
LO→ x (sl n P) y′ e = OC→ x P y′ e
OC→ x C.self y′ e = e
OC→ x (C.suc P) y′ e = OC→ x P y′ e
OC→ x (C.lim n P) y′ e = OC→ x P y′ e

→V : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) (y : Vs p a R u) (y′ : Vs p′ a′ R′ u′) → outS R y ≈ outS R′ y′ → EqV R R′ y y′
→VC : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) (y : Vc p a P u) (y′ : Vs p′ a′ R′ u′) → outC P y ≈ outS R′ y′ → EVC P R′ y y′
→LO : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (R′ : Strict b′ a′) (y′ : Vs p′ a′ R′ u′) → x ≈ outS R′ y′ → ELO x R′ y′
→OC : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (P : b′ ⊲ a′) (y′ : Vc p′ a′ P u′) → x ≈ outC P y′ → EOC x P y′
→V (ss P) R′ y y′ e = →VC P R′ y y′ e
→V (sl n P) R′ y y′ e = →VC P R′ y y′ e
→VC C.self R′ y y′ e = →LO y R′ y′ e
→VC (C.suc P) R′ y y′ e = →VC P R′ y y′ e
→VC (C.lim n P) R′ y y′ e = →VC P R′ y y′ e
→LO x (ss P) y′ e = →OC x P y′ e
→LO x (sl n P) y′ e = →OC x P y′ e
→OC x C.self y′ e = e
→OC x (C.suc P) y′ e = →OC x P y′ e
→OC x (C.lim n P) y′ e = →OC x P y′ e
```

## §5 右边的包装透明

```agda
≈ow : ∀ {p a u p′} (x : 𝓞 p a u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → x ≈ y → x ≈ (ow p₀ g₀′ y)
≈owS : ∀ {p h k u p′} (j : h <ᴴ p) (x : Low p j k u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → ELl j x y → ELl j x (ow p₀ g₀′ y)
≈ow o0 p₀ g₀′ y d = d
≈ow (os x₁) p₀ g₀′ y d = d
≈ow (ol F) p₀ g₀′ y d = d
≈ow (oi r h) p₀ g₀′ y d = d
≈ow (od i k r h) p₀ g₀′ y d = d
≈ow (oc x₁ h) p₀ g₀′ y d = d
≈ow (oe es x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈ow (oe (el m) x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈ow (oL j₁ k₁ e₁ x) p₀ g₀′ y d = ≈owS j₁ x p₀ g₀′ y d
≈ow (ow q₁ g₁ x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS here x p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS (lh n₉) x p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS (tp a₉) x p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS (st j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d
≈owS (ll n₉ j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d
≈owS (tq a₉ j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d

≈ow⁻ : ∀ {p a u p′} (x : 𝓞 p a u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → x ≈ (ow p₀ g₀′ y) → x ≈ y
≈ow⁻S : ∀ {p h k u p′} (j : h <ᴴ p) (x : Low p j k u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → ELl j x (ow p₀ g₀′ y) → ELl j x y
≈ow⁻ o0 p₀ g₀′ y d = d
≈ow⁻ (os x₁) p₀ g₀′ y d = d
≈ow⁻ (ol F) p₀ g₀′ y d = d
≈ow⁻ (oi r h) p₀ g₀′ y d = d
≈ow⁻ (od i k r h) p₀ g₀′ y d = d
≈ow⁻ (oc x₁ h) p₀ g₀′ y d = d
≈ow⁻ (oe es x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻ (oe (el m) x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻ (oL j₁ k₁ e₁ x) p₀ g₀′ y d = ≈ow⁻S j₁ x p₀ g₀′ y d
≈ow⁻ (ow q₁ g₁ x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S here x p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S (lh n₉) x p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S (tp a₉) x p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S (st j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d
≈ow⁻S (ll n₉ j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d
≈ow⁻S (tq a₉ j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d


≈oe : ∀ {p a u p′ c b u₀} {R : Strict b c} (x : 𝓞 p a u) (stp : Stp R) (y : Vs p′ c R u₀) → x ≈ outS R y → x ≈ oe stp y
≈oeS : ∀ {p h k u p′ c b u₀} {R : Strict b c} (j : h <ᴴ p) (x : Low p j k u) (stp : Stp R) (y : Vs p′ c R u₀) → ELl j x (outS R y) → ELl j x (oe stp y)
≈oe⁻ : ∀ {p a u p′ c b u₀} {R : Strict b c} (x : 𝓞 p a u) (stp : Stp R) (y : Vs p′ c R u₀) → x ≈ oe stp y → x ≈ outS R y
≈oe⁻S : ∀ {p h k u p′ c b u₀} {R : Strict b c} (j : h <ᴴ p) (x : Low p j k u) (stp : Stp R) (y : Vs p′ c R u₀) → ELl j x (oe stp y) → ELl j x (outS R y)
≈oe o0 es y d = d
≈oe (os x) es y d = d
≈oe (ol F) es y d = d
≈oe (oi r h) es y d = d
≈oe (od i k r h) es y d = d
≈oe (oc x h) es y d = d
≈oe o0 (el n) y d = d
≈oe (os x) (el n) y d = d
≈oe (ol F) (el n) y d = d
≈oe (oi r h) (el n) y d = d
≈oe (od i k r h) (el n) y d = d
≈oe (oc x h) (el n) y d = d
≈oe (oe es x) stp y d = ≈oe x stp y d
≈oe (oe (el m) x) stp y d = ≈oe x stp y d
≈oe (oL j₁ k₁ e₁ x) stp y d = ≈oeS j₁ x stp y d
≈oe (ow q₁ g₁ x) stp y d = ≈oe x stp y d
≈oeS here x stp y d = ≈oe x stp y d
≈oeS (lh n₉) x stp y d = ≈oe x stp y d
≈oeS (tp a₉) x stp y d = ≈oe x stp y d
≈oeS (st j) x stp y d = ≈oeS j x stp y d
≈oeS (ll n₉ j) x stp y d = ≈oeS j x stp y d
≈oeS (tq a₉ j) x stp y d = ≈oeS j x stp y d
≈oe⁻ o0 es y d = d
≈oe⁻ (os x) es y d = d
≈oe⁻ (ol F) es y d = d
≈oe⁻ (oi r h) es y d = d
≈oe⁻ (od i k r h) es y d = d
≈oe⁻ (oc x h) es y d = d
≈oe⁻ o0 (el n) y d = d
≈oe⁻ (os x) (el n) y d = d
≈oe⁻ (ol F) (el n) y d = d
≈oe⁻ (oi r h) (el n) y d = d
≈oe⁻ (od i k r h) (el n) y d = d
≈oe⁻ (oc x h) (el n) y d = d
≈oe⁻ (oe es x) stp y d = ≈oe⁻ x stp y d
≈oe⁻ (oe (el m) x) stp y d = ≈oe⁻ x stp y d
≈oe⁻ (oL j₁ k₁ e₁ x) stp y d = ≈oe⁻S j₁ x stp y d
≈oe⁻ (ow q₁ g₁ x) stp y d = ≈oe⁻ x stp y d
≈oe⁻S here x stp y d = ≈oe⁻ x stp y d
≈oe⁻S (lh n₉) x stp y d = ≈oe⁻ x stp y d
≈oe⁻S (tp a₉) x stp y d = ≈oe⁻ x stp y d
≈oe⁻S (st j) x stp y d = ≈oe⁻S j x stp y d
≈oe⁻S (ll n₉ j) x stp y d = ≈oe⁻S j x stp y d
≈oe⁻S (tq a₉ j) x stp y d = ≈oe⁻S j x stp y d

≈oL : ∀ {p a u p′ a′ h k u₀} (x : 𝓞 p a u) (j : h <ᴴ p′) (e : (k ⊲ u₀) × Hb p′ h u₀) (y : Low p′ j k u₀) → x ≈ outL j y → _≈_ {a′ = a′} x (oL j k e y)
≈oLS : ∀ {p h₁ k₁ u p′ a′ h k u₀} (j₁ : h₁ <ᴴ p) (x : Low p j₁ k₁ u) (j : h <ᴴ p′) (e : (k ⊲ u₀) × Hb p′ h u₀) (y : Low p′ j k u₀) → ELl j₁ x (outL j y) → ELl {a′ = a′} j₁ x (oL j k e y)
≈oL o0 j e y d = →Lr o0 j y d
≈oL X@(os x) j e y d = →Lr X j y d
≈oL X@(ol F) j e y d = →Lr X j y d
≈oL X@(oi r h) j e y d = →Lr X j y d
≈oL X@(od i k r h) j e y d = →Lr X j y d
≈oL X@(oc x h) j e y d = →Lr X j y d
≈oL (oe es x) j e y d = ≈oL x j e y d
≈oL (oe (el m) x) j e y d = ≈oL x j e y d
≈oL (oL j₁ k₁ e₁ x) j e y d = ≈oLS j₁ x j e y d
≈oL (ow q₁ g₁ x) j e y d = ≈oL x j e y d
≈oLS here x j e y d = ≈oL x j e y d
≈oLS (lh n₉) x j e y d = ≈oL x j e y d
≈oLS (tp a₉) x j e y d = ≈oL x j e y d
≈oLS (st j₁) x j e y d = ≈oLS j₁ x j e y d
≈oLS (ll n₉ j₁) x j e y d = ≈oLS j₁ x j e y d
≈oLS (tq a₉ j₁) x j e y d = ≈oLS j₁ x j e y d

≈oL⁻ : ∀ {p a u p′ a′ h k u₀} (x : 𝓞 p a u) (j : h <ᴴ p′) (e : (k ⊲ u₀) × Hb p′ h u₀) (y : Low p′ j k u₀) → _≈_ {a′ = a′} x (oL j k e y) → x ≈ outL j y
≈oL⁻S : ∀ {p h₁ k₁ u p′ a′ h k u₀} (j₁ : h₁ <ᴴ p) (x : Low p j₁ k₁ u) (j : h <ᴴ p′) (e : (k ⊲ u₀) × Hb p′ h u₀) (y : Low p′ j k u₀) → ELl {a′ = a′} j₁ x (oL j k e y) → ELl j₁ x (outL j y)
≈oL⁻ o0 j e y d = Lr→ o0 j y d
≈oL⁻ X@(os x) j e y d = Lr→ X j y d
≈oL⁻ X@(ol F) j e y d = Lr→ X j y d
≈oL⁻ X@(oi r h) j e y d = Lr→ X j y d
≈oL⁻ X@(od i k r h) j e y d = Lr→ X j y d
≈oL⁻ X@(oc x h) j e y d = Lr→ X j y d
≈oL⁻ (oe es x) j e y d = ≈oL⁻ x j e y d
≈oL⁻ (oe (el m) x) j e y d = ≈oL⁻ x j e y d
≈oL⁻ (oL j₁ k₁ e₁ x) j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻ (ow q₁ g₁ x) j e y d = ≈oL⁻ x j e y d
≈oL⁻S here x j e y d = ≈oL⁻ x j e y d
≈oL⁻S (lh n₉) x j e y d = ≈oL⁻ x j e y d
≈oL⁻S (tp a₉) x j e y d = ≈oL⁻ x j e y d
≈oL⁻S (st j₁) x j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻S (ll n₉ j₁) x j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻S (tq a₉ j₁) x j e y d = ≈oL⁻S j₁ x j e y d

-- 用 O k 的值陈述分支
nI : ∀ {p a u p′ a′ u′ k k′} {r : k ≪ a} {r′ : k′ ≪ a′} {f : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} {f′ : ∀ {v} → u′ ⊲ v → Gw v → Vs p′ a′ (≪S r′) v → 𝓞 p′ a′ v} →
     (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqV (≪S r) (≪S r′) y y′ → f q g y ≈ f′ q′ g′ y′) →
     ∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → (z : 𝓞 p k v) (z′ : 𝓞 p′ k′ v′) → z ≈ z′ → f q g (inS (≪S r) z) ≈ f′ q′ g′ (inS (≪S r′) z′)
nI {r = r} {r′} N q q′ g g′ vv z z′ d = N q q′ g g′ vv _ _ (→V (≪S r) (≪S r′) _ _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r′) z′)) d))

nD : ∀ {p a u p′ a′ u′ h₀ h₁ k k′} {j : h₀ <ᴴ p} {j′ : h₁ <ᴴ p′} {f : ∀ {v} → u ⊲ v → Gw v → Low p j k v → 𝓞 p a v} {f′ : ∀ {v} → u′ ⊲ v → Gw v → Low p′ j′ k′ v → 𝓞 p′ a′ v} →
     (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqW j j′ y y′ → f q g y ≈ f′ q′ g′ y′) →
     ∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → (z : 𝓞 h₀ k v) (z′ : 𝓞 h₁ k′ v′) → z ≈ z′ → f q g (inL j z) ≈ f′ q′ g′ (inL j′ z′)
nD {j = j} {j′} N q q′ g g′ vv z z′ d = N q q′ g g′ vv _ _ (→W j j′ _ _ (subst₂ _≈_ (sym (out-inL j z)) (sym (out-inL j′ z′)) d))
```

## §6 $\Omega$, 加法, $y\cdot n$

```agda
≈ᴴ-trans : ∀ {p q r} → p ≈ᴴ q → q ≈ᴴ r → p ≈ᴴ r
≈ᴴ-trans (ht≈ e) (ht≈ d) = ht≈ (≈ᴬ-trans e d)
≈ᴴ-trans (tφ≈ h) (tφ≈ k) = tφ≈ (λ a b e → ≈ᴴ-trans (h a a (≈ᴬ-refl a)) (k a b e))

hrefl : ∀ {p} → HT p → p ≈ᴴ p
hrefl {ht a} _ = ht≈ (≈ᴬ-refl a)
hrefl {tφ _} refl = top≈

hirr : ∀ {p q} → HT q → p <ᴴ q → p ≈ᴴ q → ⊥
hirr {ht a} {ht b} _ l (ht≈ e) = irr (<⊏ l) e
hirr {tφ x} {ht b} _ l e = no-tφ l
hirr {q = tφ f} refl (tp a) ()
hirr {p = ht c} {q = tφ f} refl (tq a j) ()
hirr {p = tφ x} {q = tφ f} refl (tq a j) e = no-tφ j

Ω≈ : ∀ {p p′ a b} → p ≈ᴴ p′ → a ≈ᴬ b → Ω̇ p a ≈ Ω̇ p′ b
Ω≈ ep (s≈ {a} {b} e) = ep , s≈ e , s≈ z≈ , e , (λ q q′ g g′ vv y y′ d → ≈oe {R = ss C.self} y es y′ (V→ (ss C.self) (ss C.self) y y′ d))
Ω≈ {p} {p′} ep (l≈ {f} {g} h) = λ n → ≈oe {p} {f n} {one} {p′} {alim g} {g n} {one} {sl n C.self} (Ω̇ p (f n)) (el n) (Ω̇ p′ (g n)) (Ω≈ ep (h n))
Ω≈ (ht≈ z≈) z≈ = ht≈ z≈ , z≈ , s≈ z≈ , tt
Ω≈ (ht≈ (s≈ {a = p} {b = p′} e)) z≈ = ht≈ (s≈ e) , z≈ , (s≈ z≈) , (≈oL {a′ = azero} {k = one} {u₀ = one} (Ω̇ (ht p) one) here (C.self , tt) (Ω̇ (ht p′) one) (Ω≈ (ht≈ e) (≈ᴬ-refl one))) ,
  (λ {v} {v′} q q′ g g′ vv → ≈oL {a′ = azero} {k = v′} {u₀ = v′} (ow (pos g) g₀ (Ω̇ (ht p) v)) here (C.self , tt) (ow (pos g′) g₀ (Ω̇ (ht p′) v′))
     (≈ow (Ω̇ (ht p) v) (pos g′) g₀ (Ω̇ (ht p′) v′) (Ω≈ (ht≈ e) vv)))
Ω≈ (ht≈ (l≈ {f} {g} h)) z≈ = λ n → ≈oL {a′ = azero} {k = azero} {u₀ = one} (Ω̇ (ht (f n)) azero) (lh n) (z⊲ one , tt) (Ω̇ (ht (g n)) azero) (Ω≈ (ht≈ (h n)) z≈)
Ω≈ {tφ f} {tφ g} (tφ≈ k) z≈ = tφ≈ k , z≈ , (s≈ z≈) , (≈oL {a′ = azero} {k = azero} {u₀ = one} (Ω̇ (f azero) azero) (tp azero) (z⊲ one , hb₀ g) (Ω̇ (g azero) azero) (Ω≈ (k azero azero z≈) z≈)) ,
  (λ {v} {v′} q q′ g₁ g₁′ vv → ≈oL {a′ = azero} {k = azero} {u₀ = v′} (ow (pos g₁) g₀ (Ω̇ (f v) azero)) (tp v′) (z⊲ v′ , hbv g v′) (ow (pos g₁′) g₀ (Ω̇ (g v′) azero))
     (≈ow (Ω̇ (f v) azero) (pos g₁′) g₀ (Ω̇ (g v′) azero) (Ω≈ (k v v′ vv) z≈)))

≈-Ωat : ∀ {p p′ a b v v′} (g : Gw v) (g′ : Gw v′) → p ≈ᴴ p′ → a ≈ᴬ b → Ω̇at p a g ≈ Ω̇at p′ b g′
≈-Ωat {p} {p′} {a} {b} g g′ ep e = ≈ow (Ω̇ p a) (pos g′) g₀ (Ω̇ p′ b) (Ω≈ ep e)

bw≈ : ∀ {p p′ p₁ b a p₂ b′ a′} → p ≈ᴴ p′ → HT p → HT p′ → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) → p₁ ≈ᴴ p₂ → b ≈ᴬ b′ → bw R ≈ᴬ bw R′
bw≈ ep hp hp′ (sa P) (sa P′) eh e = z≈
bw≈ ep hp hp′ (lw i) (lw i′) eh e = e
bw≈ ep hp hp′ (sa P) (lw i′) eh e = ⊥-elim (hirr hp′ i′ (≈ᴴ-trans (≈ᴴ-sym eh) ep))
bw≈ ep hp hp′ (lw i) (sa P′) eh e = ⊥-elim (hirr hp i (≈ᴴ-trans eh (≈ᴴ-sym ep)))

bB≈ : ∀ {p p′ p₁ b a p₂ b′ a′} → p ≈ᴴ p′ → HT p → HT p′ → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) → p₁ ≈ᴴ p₂ → bB R ≈ᴬ bB R′
bB≈ ep hp hp′ (sa P) (sa P′) eh = z≈
bB≈ (ht≈ _) hp hp′ (lw i) (lw i′) eh = z≈
bB≈ (tφ≈ _) hp hp′ (lw i) (lw i′) eh = hA≈ eh
bB≈ ep hp hp′ (sa P) (lw i′) eh = ⊥-elim (hirr hp′ i′ (≈ᴴ-trans (≈ᴴ-sym eh) ep))
bB≈ ep hp hp′ (lw i) (sa P′) eh = ⊥-elim (hirr hp i (≈ᴴ-trans eh (≈ᴴ-sym ep)))

-- 左边 W 对齐, 输出世界规范
module AddE {p p′ a a′ u₀ u₀′} {W : 𝓞 p a u₀} {W′ : 𝓞 p′ a′ u₀′} (ep : p ≈ᴴ p′) (ea : a ≈ᴬ a′) (eu : u₀ ≈ᴬ u₀′) (E : W ≈ W′) (gu : Gw u₀) (gu′ : Gw u₀′) where
  add⁰≈ : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → Mis m u₀ (ht azero) w (ht (bB R)) (bw R) →
          ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : BW R′ m′) → Mis m′ u₀′ (ht azero) w′ (ht (bB R′)) (bw R′) →
          x ≈ y → add⁰ W gu R x gx m gm um tm am ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′

  add≈ : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : BW R v)
         v′ (gv′ : Gw v′) (uv′ : u₀′ ⊲ v′) (xv′ : w′ ⊲ v′) (bv′ : BW R′ v′) →
         x ≈ y → add W gu R x gx v gv uv xv bv ≈ add W′ gu′ R′ y gy v′ gv′ uv′ xv′ bv′
  add≈ R R′ x y gx gy v gv uv xv bv v′ gv′ uv′ xv′ bv′ d =
    ≈ow (add⁰ W gu R x gx (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ bv)) (Mx.mv M′) (Mx.gm M′) (add⁰ W′ gu′ R′ y gy (Mx.m M′) (Mx.gm M′) (Mx.um M′) (proj₁ (Mx.tm M′)) (Mx.am M′ , proj₂ bv′))
      (add⁰≈ R R′ x y gx gy (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ bv) (mx-is gu gv uv (lbu xv) (proj₁ bv)) (Mx.m M′) (Mx.gm M′) (Mx.um M′) (proj₁ (Mx.tm M′)) (Mx.am M′ , proj₂ bv′) (mx-is gu′ gv′ uv′ (lbu xv′) (proj₁ bv′)) d)
    where
    M = mx gu gv uv (lbu xv) (proj₁ bv)
    M′ = mx gu′ gv′ uv′ (lbu xv′) (proj₁ bv′)

  addl : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m)
         m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : BW R′ m′) → Mis m′ u₀′ (ht azero) w′ (ht (bB R′)) (bw R′) →
         x ≈ y → add W gu R x gx m gm um tm am ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addl R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d =
    add⁰≈ R R′ x y gx gy (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ am) (mx-is gu gm um (lbu tm) (proj₁ am)) m′ gm′ um′ tm′ am′ is′ d
    where
    M = mx gu gm um (lbu tm) (proj₁ am)

  addr : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → Mis m u₀ (ht azero) w (ht (bB R)) (bw R) →
         ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : BW R′ m′) →
         x ≈ y → add⁰ W gu R x gx m gm um tm am ≈ add W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addr R R′ x y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d =
    ≈ow (add⁰ W gu R x gx m gm um tm am) (Mx.mv M) (Mx.gm M) (add⁰ W′ gu′ R′ y gy (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ am′))
      (add⁰≈ R R′ x y gx gy m gm um tm am is (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ am′) (mx-is gu′ gm′ um′ (lbu tm′) (proj₁ am′)) d)
    where
    M = mx gu′ gm′ um′ (lbu tm′) (proj₁ am′)

  addLl : ∀ {p₁ h k w p₂ b′ w′} (t : h <ᴴ p) (j : h <ᴴ p₁) (x : Low p₁ j k w) (R′ : Rel p₂ b′ p′ a′) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : BW {b = k} {a = a} (lw t) m)
          m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : BW R′ m′) → Mis m′ u₀′ (ht azero) w′ (ht (bB R′)) (bw R′) →
          ELl j x y → addL W gu t j x gx m gm um tm km ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addLl t here x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (lh n₉) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (tp a₉) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (st j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (ll n₉ j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (tq a₉ j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d

  addLr : ∀ {p₁ b w p₂ h k w′} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (t : h <ᴴ p′) (j : h <ᴴ p₂) (y : Low p₂ j k w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → Mis m u₀ (ht azero) w (ht (bB R)) (bw R) →
          ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (km′ : BW {b = k} {a = a′} (lw t) m′) →
          ELr x j y → add⁰ W gu R x gx m gm um tm am ≈ addL W′ gu′ t j y gy m′ gm′ um′ tm′ km′
  addLr R x t here y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (lh n₉) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (tp a₉) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (st j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (ll n₉ j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (tq a₉ j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d

  add⁰≈ (sa P) R′ (oe es x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (sa (⊲-tr (C.suc C.self) P)) R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oe es x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (lw i) R′ x y gx gy m gm um tm (bw↓ i (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (sa P) R′ (oe (el n) x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (sa (⊲-tr (C.lim n C.self) P)) R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oe (el n) x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (lw i) R′ x y gx gy m gm um tm (bw↓ i (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (sa P) R′ (oL j k e x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLl j j x R′ y gx gy m gm um tm (bwEe j e tm (proj₂ am)) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oL j k e x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLl (<tr j i) j x R′ y gx gy m gm um tm (bwTr j i e tm am) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ R R′ (ow p′ g′ x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl R R′ x y g′ gy m gm um (⊲-tr p′ tm) am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ R (sa P) X@o0 (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@o0 (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@o0 (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@o0 (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@o0 (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwEe j e tm′ (proj₂ am′)) d
  add⁰≈ R (lw i) X@o0 (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwTr j i e tm′ am′) d
  add⁰≈ R R′ X@o0 (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(os x) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(os x) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(os x) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(os x) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(os x) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwEe j e tm′ (proj₂ am′)) d
  add⁰≈ R (lw i) X@(os x) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwTr j i e tm′ am′) d
  add⁰≈ R R′ X@(os x) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(ol F) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(ol F) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(ol F) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(ol F) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(ol F) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwEe j e tm′ (proj₂ am′)) d
  add⁰≈ R (lw i) X@(ol F) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwTr j i e tm′ am′) d
  add⁰≈ R R′ X@(ol F) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(oi r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oi r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(oi r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oi r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(oi r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwEe j e tm′ (proj₂ am′)) d
  add⁰≈ R (lw i) X@(oi r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwTr j i e tm′ am′) d
  add⁰≈ R R′ X@(oi r f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwEe j e tm′ (proj₂ am′)) d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwTr j i e tm′ am′) d
  add⁰≈ R R′ X@(od j₃ k₃ r f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(oc x f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oc x f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(oc x f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oc x f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(oc x f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwEe j e tm′ (proj₂ am′)) d
  add⁰≈ R (lw i) X@(oc x f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (bwTr j i e tm′ am′) d
  add⁰≈ R R′ X@(oc x f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R R′ o0 o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = ≈ow W um′ gu′ W′ E
  add⁰≈ R R′ (os x) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , d) =
    ep , ea , m≈ is is′ um (lbu tm) (proj₁ am) um′ (lbu tm′) (proj₁ am′) eu (ht≈ z≈ , ex) (ht≈ (bB≈ ep (proj₂ am) (proj₂ am′) R R′ eh) , bw≈ ep (proj₂ am) (proj₂ am′) R R′ eh ez) , add≈ R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ d
  add⁰≈ R R′ (ol F) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = λ n → add≈ R R′ (F n) (G n) gx gy m gm um tm am m′ gm′ um′ tm′ am′ (d n)
  add⁰≈ (sa P) (sa P′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , ek , N) =
    ep , ea , m≈ is is′ um (lbu tm) (proj₁ am) um′ (lbu tm′) (proj₁ am′) eu (ht≈ z≈ , ex) (ht≈ z≈ , z≈) , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (sa P) (sa P′) _ _ g g′ v g (⊲-tr um q) C.self (lb0 v , proj₂ am) v′ g′ (⊲-tr um′ q′) C.self (lb0 v′ , proj₂ am′)
        (nI {r = r} {r′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (V→ (≪S (≪∘ r P)) (≪S (≪∘ r′ P′)) y y′ d′)))
  add⁰≈ (lw i) (lw i′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , ek , N) =
    ep , eh , ea , m≈ is is′ um (lbu tm) (proj₁ am) um′ (lbu tm′) (proj₁ am′) eu (ht≈ z≈ , ex) (ht≈ (bB≈ ep (proj₂ am) (proj₂ am′) (lw i) (lw i′) eh) , ez) , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (lw i) (lw i′) _ _ g g′ v g (⊲-tr um q) C.self (bw↑ _ am q) v′ g′ (⊲-tr um′ q′) C.self (bw↑ _ am′ q′)
        (nI {r = r} {r′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ i i′ y y′ d′)))
  add⁰≈ (sa P) (lw i′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , _) = ⊥-elim (hirr (proj₂ am′) i′ (≈ᴴ-trans (≈ᴴ-sym eh) ep))
  add⁰≈ (lw i) (sa P′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , _) = ⊥-elim (hirr (proj₂ am) i (≈ᴴ-trans eh (≈ᴴ-sym ep)))
  add⁰≈ (sa P) (sa P′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , eh , ez , ex , ek , N) =
    ep , eh , ea , m≈ is is′ um (lbu tm) (proj₁ am) um′ (lbu tm′) (proj₁ am′) eu (ht≈ z≈ , ex) (ht≈ z≈ , z≈) , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (sa P) (sa P′) _ _ g g′ v g (⊲-tr um q) C.self (lb0 v , proj₂ am) v′ g′ (⊲-tr um′ q′) C.self (lb0 v′ , proj₂ am′)
        (nD {j = j} {j′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ j j′ y y′ d′)))
  add⁰≈ (lw i) (lw i′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , eh , ez , ex , ek , N) =
    ep , eh , ea , m≈ is is′ um (lbu tm) (proj₁ am) um′ (lbu tm′) (proj₁ am′) eu (ht≈ z≈ , ex) (ht≈ (bB≈ ep (proj₂ am) (proj₂ am′) (lw i) (lw i′) eh₀) , ez) , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (lw i) (lw i′) _ _ g g′ v g (⊲-tr um q) C.self (bw↑ _ am q) v′ g′ (⊲-tr um′ q′) C.self (bw↑ _ am′ q′)
        (nD {j = j} {j′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ (<tr j i) (<tr j′ i′) y y′ d′)))
  add⁰≈ (sa P) (lw i′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , _) = ⊥-elim (hirr (proj₂ am′) i′ (≈ᴴ-trans (≈ᴴ-sym eh) ep))
  add⁰≈ (lw i) (sa P′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , _) = ⊥-elim (hirr (proj₂ am) i (≈ᴴ-trans eh (≈ᴴ-sym ep)))
  add⁰≈ R R′ (oc x f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , d , N) =
    ep , ea , m≈ is is′ um (lbu tm) (proj₁ am) um′ (lbu tm′) (proj₁ am′) eu (ht≈ z≈ , ex) (ht≈ (bB≈ ep (proj₂ am) (proj₂ am′) R R′ eh) , bw≈ ep (proj₂ am) (proj₂ am′) R R′ eh ez) , add≈ R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ d ,
    (λ {v} {v′} q q′ g g′ vv →
      add≈ R R′ (f (⊲-tr tm q) g) (f′ (⊲-tr tm′ q′) g′) g g′ v g (⊲-tr um q) C.self (bw↑ _ am q) v′ g′ (⊲-tr um′ q′) C.self (bw↑ _ am′ q′) (N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv))
  add⁰≈ R R′ o0 (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()

rep≈ : ∀ {q q′ t t′ u u′} {y : 𝓞 q t u} {y′ : 𝓞 q′ t′ u′} (H : HT q) (H′ : HT q′) → q ≈ᴴ q′ → t ≈ᴬ t′ → u ≈ᴬ u′ → y ≈ y′ → (g : Gw u) (g′ : Gw u′) → ∀ n → rep H y g n ≈ rep H′ y′ g′ n
rep≈ H H′ eq et eu e g g′ zero = tt
rep≈ H H′ eq et eu e g g′ (suc zero) = e
rep≈ {u = u} {u′} {y = y} {y′} H H′ eq et eu e g g′ (suc (suc m)) =
  AddE.add≈ eq et eu (rep≈ H H′ eq et eu e g g′ (suc m)) g g′ (sa C.self) (sa C.self) y y′ g g′ u g C.self C.self (lb0 u , H) u′ g′ C.self C.self (lb0 u′ , H′) e
```
