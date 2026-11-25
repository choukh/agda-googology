# D7 编译检验：结构严格步进与基础闭包

只在平行 YiLglCore 的类型上检验。Properˢ 是原 YiLevelBase.Proper 的同形定义，
Legalˢ 只把平行 Legal 的 lim 步进加强为 Properˢ，其余条件相同。
这不是修改旧 Legal，也不导入旧 Reg 或继续 ψ／γ；末尾 R₂ 仅作作者允许的 Ω₁ 小样本检验。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglStrict where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.YiLglCore using (LF; Raw; Pre; Low; GdL; Kid; KidR; Lgl; LglK; Gd; Dn; DnK)
import OCF.Align.YiLglCore as F
open F using (module G)
open import OCF.Align.YiLglVal using (CP)
import OCF.Align.YiLglVal as V

data Properˢ : LF → LF → Set where
  under-suc : ∀ {a b} → CP a b → Properˢ a (F.suc b)
  under-lim : ∀ {a f} n → CP a (f n) → Properˢ a (F.lim f)
  under-first : ∀ {a k c t g} → CP a t → Properˢ a (F.lc k c t g)

weak : ∀ {a b} → Properˢ a b → CP a b
weak (under-suc p) = V.suc p
weak (under-lim n p) = V.lim n p
weak (under-first p) = V.fst p

Ω-proper : ∀ {a b} → Properˢ a b → Properˢ (V.Ω̂ a) (V.Ω̂ b)
Ω-proper (under-suc p) = under-first (V.Ω̂-CP p)
Ω-proper (under-lim n p) = under-lim n (V.Ω̂-CP p)
Ω-proper (under-first p) = under-first (V.Ω̂-CP p)

firstN : ∀ y r c t g {a} → CP a t → Properˢ a (V.upN y r c t g)
firstN (F.suc k) (inj₁ _) c t g p = under-first p
firstN (F.suc k) (inj₂ r) c t g p = firstN k r c t g p
firstN (F.lim f) (n , r) c t g p = firstN (f n) r c t g p
firstN (F.lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g p = under-first p
firstN (F.lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g p = firstN k r c t g p
firstN (F.lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g p = firstN t₀ r c t g p
firstN (F.lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g p = firstN (g₀ η e) r c t g p

dn-proper : ∀ y {a} b → Dn y a b → Properˢ (V.up y a) (V.up y b)
dnk-proper : ∀ y i i′ {a b} → DnK y i i′ a b → Properˢ (V.upK y i a) (V.upK y i′ b)
dn-proper y (G.suc b) p = under-suc (V.cp→CP y p)
dn-proper y (G.lim f) (n , p) = under-lim n (V.cp→CP y p)
dn-proper y (G.lc r c t g) p = firstN y r c _ _ (V.cp→CP y p)
dn-proper y {a = G.em i′ _} (G.em i T) p = dnk-proper y i′ i p
dn-proper (F.suc k) {G.em _ _} G.top p = under-first (V.cp→CP k p)
dn-proper (F.lc k c t g) {G.em (inj₂ (inj₁ _)) _} G.top p = under-first (V.cp→CP t p)
dnk-proper (F.suc k) _ _ {b = b} p = dn-proper k b p
dnk-proper (F.lim f) n .n {b = b} (refl , p) = dn-proper (f n) b p
dnk-proper (F.lc k c t g) (inj₁ _) (inj₁ _) {b = b} p = dn-proper k b p
dnk-proper (F.lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} p = dn-proper t b p
dnk-proper (F.lc k c t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b} (refl , p) = dn-proper (g η e) b p

Legalˢ : LF → Set
Legalˢ F.zero = ⊤
Legalˢ (F.suc x) = Legalˢ x
Legalˢ (F.lim f) = (∀ n → Properˢ (f n) (f (suc n))) × (∀ n → Legalˢ (f n))
Legalˢ (F.lc k c t g) =
  Legalˢ k × (∀ η e → CP t (g η e)) ×
  (∀ η e η′ e′ → Gd k η η′ → CP (g η e) (g η′ e′)) ×
  (∀ η e e′ → g η e ≡ g η e′) × Legalˢ t × (∀ η e → Legalˢ (g η e))

forget : ∀ x → Legalˢ x → V.Legal x
forget F.zero w = tt
forget (F.suc x) w = forget x w
forget (F.lim f) (st , w) = (λ n → weak (st n)) , (λ n → forget (f n) (w n))
forget (F.lc k c t g) (lk , first , mono , irr , lt , lg) =
  forget k lk , first , mono , irr , forget t lt , (λ η e → forget (g η e) (lg η e))

legalN : ∀ y r c t g → Legalˢ y →
  (∀ η e → CP t (g η e)) →
  (∀ η e η′ e′ → GdL y r η η′ → CP (g η e) (g η′ e′)) →
  (∀ η e e′ → g η e ≡ g η e′) →
  Legalˢ t → (∀ η e → Legalˢ (g η e)) → Legalˢ (V.upN y r c t g)
legalN (F.suc k) (inj₁ _) c t g L a b i u v = L , a , b , i , u , v
legalN (F.suc k) (inj₂ r) c t g L a b i u v = legalN k r c t g L a b i u v
legalN (F.lim f) (n , r) c t g L a b i u v = legalN (f n) r c t g (proj₂ L n) a b i u v
legalN (F.lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g L a b i u v = proj₁ L , a , b , i , u , v
legalN (F.lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g L a b i u v = legalN k r c t g (proj₁ L) a b i u v
legalN (F.lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g (_ , _ , _ , _ , lt , _) a b i u v = legalN t₀ r c t g lt a b i u v
legalN (F.lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g (_ , _ , _ , _ , _ , lg) a b i u v = legalN (g₀ η e) r c t g (lg η e) a b i u v

Ω-legalˢ : ∀ x → Legalˢ x → Legalˢ (V.Ω̂ x)
read-legalˢ : ∀ y → Legalˢ y → ∀ T → Lgl y T → Legalˢ (V.up y T)
readK-legalˢ : ∀ y → Legalˢ y → ∀ i T → LglK y i T → Legalˢ (V.upK y i T)
Ω-legalˢ F.zero w = tt
Ω-legalˢ (F.suc k) w = w , (λ η e → V.cO-CP k (proj₁ e)) ,
  (λ η e η′ e′ d → V.cp→CP k (proj₁ d)) , (λ η e e′ → refl) ,
  Ω-legalˢ k w , (λ η e → read-legalˢ k w η (proj₂ e))
Ω-legalˢ (F.lim f) (st , w) = (λ n → Ω-proper (st n)) , (λ n → Ω-legalˢ (f n) (w n))
Ω-legalˢ (F.lc k c t g) (lk , first , mono , irr , lt , lg) = lk ,
  (λ η e → V.Ω̂-CP (first η e)) ,
  (λ η e η′ e′ d → V.Ω̂-CP (mono η e η′ e′ d)) ,
  (λ η e e′ → cong V.Ω̂ (irr η e e′)) , Ω-legalˢ t lt , (λ η e → Ω-legalˢ (g η e) (lg η e))
read-legalˢ y L G.zero w = tt
read-legalˢ y L (G.suc a) w = read-legalˢ y L a w
read-legalˢ y L (G.lim f) (st , w) = (λ n → dn-proper y (f (suc n)) (st n)) , (λ n → read-legalˢ y L (f n) (w n))
read-legalˢ y L (G.lc r c t g) (first , mono , irr , lt , lg) =
  legalN y r c (V.up y t) (λ η e → V.up y (g η e)) L
    (λ η e → V.cp→CP y (first η e))
    (λ η e η′ e′ d → V.cp→CP y (mono η e η′ e′ d))
    (λ η e e′ → cong (V.up y) (irr η e e′))
    (read-legalˢ y L t lt) (λ η e → read-legalˢ y L (g η e) (lg η e))
read-legalˢ y L (G.em i T) w = readK-legalˢ y L i T w
read-legalˢ y L G.top w = Ω-legalˢ y L
readK-legalˢ (F.suc k) L _ T w = read-legalˢ k L T w
readK-legalˢ (F.lim f) L n T w = read-legalˢ (f n) (proj₂ L n) T w
readK-legalˢ (F.lc k c t g) L (inj₁ _) T w = read-legalˢ k (proj₁ L) T w
readK-legalˢ (F.lc k c t g) (_ , _ , _ , _ , lt , _) (inj₂ (inj₁ _)) T w = read-legalˢ t lt T w
readK-legalˢ (F.lc k c t g) (_ , _ , _ , _ , _ , lg) (inj₂ (inj₂ (η , e))) T w = read-legalˢ (g η e) (lg η e) T w

tw-proper : ∀ n → Properˢ (V.tw n) (V.tw (suc n))
tw-proper zero = under-suc V.self
tw-proper (suc n) = Ω-proper (tw-proper n)

tower-legalˢ : ∀ n → Legalˢ (V.tw n)
tower-legalˢ zero = tt
tower-legalˢ (suc n) = Ω-legalˢ (V.tw n) (tower-legalˢ n)

Λ-legalˢ : Legalˢ V.Λ
Λ-legalˢ = tw-proper , tower-legalˢ

lower-equality : ∀ k → Gd k (V.cO k) (V.cO k)
lower-equality k = inj₁ refl , V.Lgl-cO k

no-Dn-one-self : Dn F.zero (G.suc G.zero) (G.suc G.zero) → ⊥
no-Dn-one-self (inj₁ ())
no-Dn-one-self (inj₂ ())

no-old-coordinate : Lgl F.zero (G.lim (λ _ → G.suc G.zero)) → ⊥
no-old-coordinate (step , terms) = no-Dn-one-self (step zero)
```

上面是对一切层的结构步进与基础合法性闭包，不是几个塔样本的枚举。
它没有把原来已存在的弱极限任意变成严格极限，也没有提供值上的严格性或比较器。
下界本身仍由 lower-equality 可入；只排除极限内停顿。

## Ω₁ 的 R₂ 小样本

R₂ 是第十一轮 Reg₂ 的同形公式，但只作用在本篇平行 LF 上；
不能把此类型的证据用于旧 LF。此处只检验 Ω̂1，不推广或修订 Reg。

```agda
data Edge : LF → LF → Set where
  e-suc : ∀ {x} → Edge x (F.suc x)
  e-lim : ∀ {f} n → Edge (f n) (F.lim f)
  e-first : ∀ {k c t g} → Edge t (F.lc k c t g)
  e-branch : ∀ {k c t g} η e → Edge (g η e) (F.lc k c t g)

data Below : LF → LF → Set where
  one : ∀ {a b} → Edge a b → Below a b
  more : ∀ {a b c} → Below a b → Edge b c → Below a c

R₂ : LF → Set
R₂ F.zero = ⊤
R₂ (F.suc x) = R₂ x
R₂ (F.lim f) = (∀ n → Properˢ (f n) (f (suc n))) × (∀ n → R₂ (f n))
R₂ (F.lc k c t g) = Below (F.suc k) (F.lc k c t g) × R₂ k × R₂ t × (∀ η e → R₂ (g η e))

read0-R₂ : ∀ η → Lgl F.zero η → R₂ (V.up F.zero η)
read0-R₂ G.zero lawful = tt
read0-R₂ (G.suc η) lawful = read0-R₂ η lawful
read0-R₂ (G.lim f) (step , lawful) =
  (λ n → dn-proper F.zero (f (suc n)) (step n)) , (λ n → read0-R₂ (f n) (lawful n))
read0-R₂ (G.lc () c t g) lawful
read0-R₂ (G.em () T) lawful
read0-R₂ G.top lawful = tt

omega1-R₂ : R₂ (V.Ω̂ (F.suc F.zero))
omega1-R₂ = one e-first , tt , tt , (λ η e → read0-R₂ η (proj₂ e))
```
