# 没有闭包的世界: 结构等价与折叠的同余

> 不含记号. 结论写在 [CumRead](CumRead.lagda.md). `x ≈ y`: 两棵数据树同形, 层可以不同, 懒嵌入透明, 节点的层 $k$ 字面相同, 分支把等价的输入送到等价的输出. **这是对项递归的函数, 不是数据类型,** 所以分支的同余是它自己的一部分, 不用另外的假设. 它只是部分等价: `x ≈ x` 说 $x$ 尊重等价. `ψQ`: 折叠保 `≈`, 不问目标的证据是哪一个. 没有函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadCFEq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; subst₂)
open import OCF.Align.CumReadCF
```

## §1 `≈`

```agda
infix 4 _≈_
_≈_ : ∀ {a b} → O a → O b → Set
EqL : ∀ {L b a} (R : Strict a L) → Vs L R → O b → Set
EqLC : ∀ {L b a} (P : a ⊲ L) → Vc L P → O b → Set
EqR : ∀ {L b a} → O a → (R : Strict b L) → Vs L R → Set
EqRC : ∀ {L b a} → O a → (P : b ⊲ L) → Vc L P → Set
EqV : ∀ {a b k k′} (R : Strict k a) (R′ : Strict k′ b) → Vs a R → Vs b R′ → Set
EqVC : ∀ {a b k k′} (P : k ⊲ a) (R′ : Strict k′ b) → Vc a P → Vs b R′ → Set
EqLO : ∀ {b k k′} (x : O k) (R′ : Strict k′ b) → Vs b R′ → Set
EqLOC : ∀ {b k k′} (x : O k) (P : k′ ⊲ b) → Vc b P → Set

oe R x ≈ y = EqL R x y
_≈_ {a} o0 (oe R y) = EqR {a = a} o0 R y
os x ≈ oe R y = EqR (os x) R y
ol F ≈ oe R y = EqR (ol F) R y
oi r h ≈ oe R y = EqR (oi r h) R y
o0 ≈ o0 = ⊤
os x ≈ os y = x ≈ y
ol F ≈ ol G = ∀ n → F n ≈ G n
_≈_ (oi {k = k} r h) (oi {k = k′} r′ h′) = (k ≡ k′) × (∀ y y′ → EqV (≪S r) (≪S r′) y y′ → h y ≈ h′ y′)
_ ≈ _ = ⊥

EqL (ss P) x y = EqLC P x y
EqL (sl n P) x y = EqLC P x y
EqLC self x y = x ≈ y
EqLC (suc P) x y = EqLC P x y
EqLC (lim n P) x y = EqLC P x y

EqR x (ss P) y = EqRC x P y
EqR x (sl n P) y = EqRC x P y
EqRC x self y = x ≈ y
EqRC x (suc P) y = EqRC x P y
EqRC x (lim n P) y = EqRC x P y

EqV (ss P) R′ y y′ = EqVC P R′ y y′
EqV (sl n P) R′ y y′ = EqVC P R′ y y′
EqVC self R′ y y′ = EqLO y R′ y′
EqVC (suc P) R′ y y′ = EqVC P R′ y y′
EqVC (lim n P) R′ y y′ = EqVC P R′ y y′
EqLO x (ss P) y′ = EqLOC x P y′
EqLO x (sl n P) y′ = EqLOC x P y′
EqLOC x self y′ = x ≈ y′
EqLOC x (suc P) y′ = EqLOC x P y′
EqLOC x (lim n P) y′ = EqLOC x P y′
```

## §2 `outS` 的视角

`≈` 对 `Vs` 的值的陈述, 都可以换成对 `outS` 的值的陈述.

```agda
L→ : ∀ {L b a} (R : Strict a L) (x : Vs L R) {y : O b} → EqL R x y → outS R x ≈ y
LC→ : ∀ {L b a} (P : a ⊲ L) (x : Vc L P) {y : O b} → EqLC P x y → outC P x ≈ y
L→ (ss P) x e = LC→ P x e
L→ (sl n P) x e = LC→ P x e
LC→ self x e = e
LC→ (suc P) x e = LC→ P x e
LC→ (lim n P) x e = LC→ P x e

→L : ∀ {L b a} (R : Strict a L) (x : Vs L R) {y : O b} → outS R x ≈ y → EqL R x y
→LC : ∀ {L b a} (P : a ⊲ L) (x : Vc L P) {y : O b} → outC P x ≈ y → EqLC P x y
→L (ss P) x e = →LC P x e
→L (sl n P) x e = →LC P x e
→LC self x e = e
→LC (suc P) x e = →LC P x e
→LC (lim n P) x e = →LC P x e

R→ : ∀ {L b a} (x : O a) (R : Strict b L) (y : Vs L R) → EqR x R y → x ≈ outS R y
RC→ : ∀ {L b a} (x : O a) (P : b ⊲ L) (y : Vc L P) → EqRC x P y → x ≈ outC P y
R→ x (ss P) y e = RC→ x P y e
R→ x (sl n P) y e = RC→ x P y e
RC→ x self y e = e
RC→ x (suc P) y e = RC→ x P y e
RC→ x (lim n P) y e = RC→ x P y e

→R : ∀ {L b a} (x : O a) (R : Strict b L) (y : Vs L R) → x ≈ outS R y → EqR x R y
→RC : ∀ {L b a} (x : O a) (P : b ⊲ L) (y : Vc L P) → x ≈ outC P y → EqRC x P y
→R x (ss P) y e = →RC x P y e
→R x (sl n P) y e = →RC x P y e
→RC x self y e = e
→RC x (suc P) y e = →RC x P y e
→RC x (lim n P) y e = →RC x P y e

-- 右边是懒嵌入
≈oe : ∀ {a L b} (x : O a) (R : Strict b L) (y : Vs L R) → x ≈ outS R y → x ≈ oe R y
≈oeS : ∀ {a₀ a L b} (R₀ : Strict a a₀) (x : Vs a₀ R₀) (R : Strict b L) (y : Vs L R) → outS R₀ x ≈ outS R y → EqL R₀ x (oe R y)
≈oeC : ∀ {a₀ a L b} (R₀ : a ⊲ a₀) (x : Vc a₀ R₀) (R : Strict b L) (y : Vs L R) → outC R₀ x ≈ outS R y → EqLC R₀ x (oe R y)
≈oe {a} o0 R y e = →R {a = a} o0 R y e
≈oe (os x) R y e = →R (os x) R y e
≈oe (ol F) R y e = →R (ol F) R y e
≈oe (oi r h) R y e = →R (oi r h) R y e
≈oe (oe R₀ x) R y e = ≈oeS R₀ x R y (L→ R₀ x e)
≈oeS (ss P) x R y e = ≈oeC P x R y e
≈oeS (sl n P) x R y e = ≈oeC P x R y e
≈oeC self x R y e = ≈oe x R y e
≈oeC (suc P) x R y e = ≈oeC P x R y e
≈oeC (lim n P) x R y e = ≈oeC P x R y e

oe≈ : ∀ {a L b} (x : O a) (R : Strict b L) (y : Vs L R) → x ≈ oe R y → x ≈ outS R y
oe≈S : ∀ {a₀ a L b} (R₀ : Strict a a₀) (x : Vs a₀ R₀) (R : Strict b L) (y : Vs L R) → EqL R₀ x (oe R y) → EqL R₀ x (outS R y)
oe≈C : ∀ {a₀ a L b} (R₀ : a ⊲ a₀) (x : Vc a₀ R₀) (R : Strict b L) (y : Vs L R) → EqLC R₀ x (oe R y) → EqLC R₀ x (outS R y)
oe≈ {a} o0 R y e = R→ {a = a} o0 R y e
oe≈ (os x) R y e = R→ (os x) R y e
oe≈ (ol F) R y e = R→ (ol F) R y e
oe≈ (oi r h) R y e = R→ (oi r h) R y e
oe≈ (oe R₀ x) R y e = oe≈S R₀ x R y e
oe≈S (ss P) x R y e = oe≈C P x R y e
oe≈S (sl n P) x R y e = oe≈C P x R y e
oe≈C self x R y e = oe≈ x R y e
oe≈C (suc P) x R y e = oe≈C P x R y e
oe≈C (lim n P) x R y e = oe≈C P x R y e

V→ : ∀ {a b k k′} (R : Strict k a) (R′ : Strict k′ b) (y : Vs a R) (y′ : Vs b R′) → EqV R R′ y y′ → outS R y ≈ outS R′ y′
VC→ : ∀ {a b k k′} (P : k ⊲ a) (R′ : Strict k′ b) (y : Vc a P) (y′ : Vs b R′) → EqVC P R′ y y′ → outC P y ≈ outS R′ y′
LO→ : ∀ {b k k′} (x : O k) (R′ : Strict k′ b) (y′ : Vs b R′) → EqLO x R′ y′ → x ≈ outS R′ y′
LOC→ : ∀ {b k k′} (x : O k) (P : k′ ⊲ b) (y′ : Vc b P) → EqLOC x P y′ → x ≈ outC P y′
V→ (ss P) R′ y y′ e = VC→ P R′ y y′ e
V→ (sl n P) R′ y y′ e = VC→ P R′ y y′ e
VC→ self R′ y y′ e = LO→ y R′ y′ e
VC→ (suc P) R′ y y′ e = VC→ P R′ y y′ e
VC→ (lim n P) R′ y y′ e = VC→ P R′ y y′ e
LO→ x (ss P) y′ e = LOC→ x P y′ e
LO→ x (sl n P) y′ e = LOC→ x P y′ e
LOC→ x self y′ e = e
LOC→ x (suc P) y′ e = LOC→ x P y′ e
LOC→ x (lim n P) y′ e = LOC→ x P y′ e

→V : ∀ {a b k k′} (R : Strict k a) (R′ : Strict k′ b) (y : Vs a R) (y′ : Vs b R′) → outS R y ≈ outS R′ y′ → EqV R R′ y y′
→VC : ∀ {a b k k′} (P : k ⊲ a) (R′ : Strict k′ b) (y : Vc a P) (y′ : Vs b R′) → outC P y ≈ outS R′ y′ → EqVC P R′ y y′
→LO : ∀ {b k k′} (x : O k) (R′ : Strict k′ b) (y′ : Vs b R′) → x ≈ outS R′ y′ → EqLO x R′ y′
→LOC : ∀ {b k k′} (x : O k) (P : k′ ⊲ b) (y′ : Vc b P) → x ≈ outC P y′ → EqLOC x P y′
→V (ss P) R′ y y′ e = →VC P R′ y y′ e
→V (sl n P) R′ y y′ e = →VC P R′ y y′ e
→VC self R′ y y′ e = →LO y R′ y′ e
→VC (suc P) R′ y y′ e = →VC P R′ y y′ e
→VC (lim n P) R′ y y′ e = →VC P R′ y y′ e
→LO x (ss P) y′ e = →LOC x P y′ e
→LO x (sl n P) y′ e = →LOC x P y′ e
→LOC x self y′ e = e
→LOC x (suc P) y′ e = →LOC x P y′ e
→LOC x (lim n P) y′ e = →LOC x P y′ e

-- 用 O k 的值陈述分支
node≈ : ∀ {a b k k′} {r : k ≪ a} {r′ : k′ ≪ b} {h : Vs a (≪S r) → O a} {h′ : Vs b (≪S r′) → O b} →
        oi r h ≈ oi r′ h′ → ∀ (z : O k) (z′ : O k′) → z ≈ z′ → h (inS (≪S r) z) ≈ h′ (inS (≪S r′) z′)
node≈ {r = r} {r′} {h} {h′} (_ , p) z z′ e = p _ _ (→V (≪S r) (≪S r′) _ _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r′) z′)) e))

≈node : ∀ {a b k k′} {r : k ≪ a} {r′ : k′ ≪ b} {h : Vs a (≪S r) → O a} {h′ : Vs b (≪S r′) → O b} → k ≡ k′ →
        (∀ y y′ → outS (≪S r) y ≈ outS (≪S r′) y′ → h y ≈ h′ y′) → oi r h ≈ oi r′ h′
≈node {r = r} {r′} q p = q , (λ y y′ e → p y y′ (V→ (≪S r) (≪S r′) y y′ e))
```

## §3 $\Omega$, 加法, $y\cdot n$ 同余

```agda
Ω≈ : ∀ L → Ω̇ L ≈ Ω̇ L
Ω≈ azero = tt
Ω≈ (asuc a) = ≈node refl (λ y y′ e → ≈oe {a = asuc a} {L = asuc a} {b = a} (oe (ss self) y) (ss self) y′ e)
Ω≈ (alim f) = λ n → ≈oe {a = alim f} {L = alim f} {b = f n} (oe (sl n self) (Ω̇ (f n))) (sl n self) (Ω̇ (f n)) (Ω≈ (f n))

addSe : ∀ {L b a} (W : O L) (Q : b ⊲ L) (R : Strict a b) (x : Vs b R) → addS W Q R x ≡ add W (⊲-tr (S→⊲ R) Q) (outS R x)
addCe : ∀ {L b a} (W : O L) (Q : b ⊲ L) (P : a ⊲ b) (x : Vc b P) → addC W Q P x ≡ add W (⊲-tr P Q) (outC P x)
tr-assoc : ∀ {a b c d} (p : a ⊲ b) (q : b ⊲ c) (u : c ⊲ d) → ⊲-tr (⊲-tr p q) u ≡ ⊲-tr p (⊲-tr q u)
tr-assoc p q self = refl
tr-assoc p q (suc u) = cong suc (tr-assoc p q u)
tr-assoc p q (lim n u) = cong (lim n) (tr-assoc p q u)
⊲-idˡ : ∀ {a b} (Q : a ⊲ b) → ⊲-tr self Q ≡ Q
⊲-idˡ self = refl
⊲-idˡ (suc Q) = cong suc (⊲-idˡ Q)
⊲-idˡ (lim n Q) = cong (lim n) (⊲-idˡ Q)
addSe W Q (ss P) x rewrite addCe W (⊲-tr (suc self) Q) P x | tr-assoc P (suc self) Q = refl
addSe W Q (sl n P) x rewrite addCe W (⊲-tr (lim n self) Q) P x | tr-assoc P (lim n self) Q = refl
addCe W Q self x rewrite ⊲-idˡ Q = refl
addCe W Q (suc P) x rewrite addCe W (⊲-tr (suc self) Q) P x | tr-assoc P (suc self) Q = refl
addCe W Q (lim n P) x rewrite addCe W (⊲-tr (lim n self) Q) P x | tr-assoc P (lim n self) Q = refl

add≈ : ∀ {L L′ a b} {W : O L} {W′ : O L′} (P : a ⊲ L) (Q : b ⊲ L′) → W ≈ W′ → (x : O a) (y : O b) → x ≈ y → add W P x ≈ add W′ Q y
add≈S : ∀ {L L′ a₀ a b} {W : O L} {W′ : O L′} (P : a₀ ⊲ L) (Q : b ⊲ L′) → W ≈ W′ → (R : Strict a a₀) (x : Vs a₀ R) (y : O b) → EqL R x y → addS W P R x ≈ add W′ Q y
add≈C : ∀ {L L′ a₀ a b} {W : O L} {W′ : O L′} (P : a₀ ⊲ L) (Q : b ⊲ L′) → W ≈ W′ → (R : a ⊲ a₀) (x : Vc a₀ R) (y : O b) → EqLC R x y → addC W P R x ≈ add W′ Q y
add≈rS : ∀ {L L′ a b₀ b} {W : O L} {W′ : O L′} (P : a ⊲ L) (Q : b₀ ⊲ L′) → W ≈ W′ → (x : O a) (R : Strict b b₀) (y : Vs b₀ R) → EqR x R y → add W P x ≈ addS W′ Q R y
add≈rC : ∀ {L L′ a b₀ b} {W : O L} {W′ : O L′} (P : a ⊲ L) (Q : b₀ ⊲ L′) → W ≈ W′ → (x : O a) (R : b ⊲ b₀) (y : Vc b₀ R) → EqRC x R y → add W P x ≈ addC W′ Q R y

add≈ P Q e (oe R x) y h = add≈S P Q e R x y h
add≈ {a = a} P Q e o0 (oe R y) h = add≈rS {a = a} P Q e o0 R y h
add≈ P Q e (os x) (oe R y) h = add≈rS P Q e (os x) R y h
add≈ P Q e (ol F) (oe R y) h = add≈rS P Q e (ol F) R y h
add≈ P Q e (oi r f) (oe R y) h = add≈rS P Q e (oi r f) R y h
add≈ P Q e o0 o0 h = e
add≈ P Q e (os x) (os y) h = add≈ P Q e x y h
add≈ P Q e (ol F) (ol G) h = λ n → add≈ P Q e (F n) (G n) (h n)
add≈ {a = a} {b = b} P Q e (oi r f) (oi r′ f′) h =
  ≈node (proj₁ h) (λ y y′ d → add≈ P Q e (f _) (f′ _) (node≈ {r = r} {r′} {f} {f′} h _ _ d))

add≈S P Q e (ss R) x y h = add≈C (⊲-tr (suc self) P) Q e R x y h
add≈S P Q e (sl n R) x y h = add≈C (⊲-tr (lim n self) P) Q e R x y h
add≈C P Q e self x y h = add≈ P Q e x y h
add≈C P Q e (suc R) x y h = add≈C (⊲-tr (suc self) P) Q e R x y h
add≈C P Q e (lim n R) x y h = add≈C (⊲-tr (lim n self) P) Q e R x y h

add≈rS P Q e x (ss R) y h = add≈rC P (⊲-tr (suc self) Q) e x R y h
add≈rS P Q e x (sl n R) y h = add≈rC P (⊲-tr (lim n self) Q) e x R y h
add≈rC P Q e x self y h = add≈ P Q e x y h
add≈rC P Q e x (suc R) y h = add≈rC P (⊲-tr (suc self) Q) e x R y h
add≈rC P Q e x (lim n R) y h = add≈rC P (⊲-tr (lim n self) Q) e x R y h

rep≈ : ∀ {s t} {y : O s} {y′ : O t} → y ≈ y′ → ∀ n → rep y n ≈ rep y′ n
rep≈ e zero = tt
rep≈ e (suc zero) = e
rep≈ {y = y} {y′} e (suc (suc m)) = add≈ self self (rep≈ e (suc m)) y y′ e
```

## §4 比较不看证据

`Rk` 的两个答案互斥: $k\ll t$ 与 $t\lhd k$ 合起来是 $k\ll k$.

```agda
data Acc≪ (a : A) : Set where
  acc : (∀ {b} → b ≪ a → Acc≪ b) → Acc≪ a

acc≪ : ∀ a {b} → b ≪ a → Acc≪ b
acc≪ (asuc a) zero = acc (acc≪ a)
acc≪ (asuc a) (suc r) = acc≪ a r
acc≪ (alim f) (lim n r) = acc≪ (f n) r

≪-irr′ : ∀ {a} → Acc≪ a → a ≪ a → ⊥
≪-irr′ (acc h) p = ≪-irr′ (h p) p

≪-irr : ∀ {a} → a ≪ a → ⊥
≪-irr {a} p = ≪-irr′ (acc (acc≪ a)) p

no-keep-rise : ∀ {k t} → k ≪ t → t ⊲ k → ⊥
no-keep-rise s q = ≪-irr (≪∘ s q)
```

## §5 折叠保 `≈`

对两边的项同时递归, 懒嵌入走到底, 项是结构子项. 节点上: 两边的回答要么都保留, 要么都上升 (`no-keep-rise`), 上升时两条链逐项等价.

```agda
ψSe : ∀ {L a} t (R : Strict a L) (T : Tg t a) (w : Lg a) (x : Vs L R) → ψS t R T w x ≡ ψ t T w (outS R x)
ψCe : ∀ {b a} t (P : a ⊲ b) (T : Tg t a) (w : Lg a) (x : Vc b P) → ψC t P T w x ≡ ψ t T w (outC P x)
ψSe t (ss P) T w x = ψCe t P T w x
ψSe t (sl n P) T w x = ψCe t P T w x
ψCe t self T w x = refl
ψCe t (suc P) T w x = ψCe t P T w x
ψCe t (lim n P) T w x = ψCe t P T w x

ψQ : ∀ {t a b} (x : O a) (y : O b) (T : Tg t a) (w : Lg a) (T′ : Tg t b) (w′ : Lg b) → x ≈ y → ψ t T w x ≈ ψ t T′ w′ y
ψQS : ∀ {t L a b} (R : Strict a L) (x : Vs L R) (y : O b) (T : Tg t a) (w : Lg a) (T′ : Tg t b) (w′ : Lg b) → EqL R x y → ψS t R T w x ≈ ψ t T′ w′ y
ψQC : ∀ {t L a b} (R : a ⊲ L) (x : Vc L R) (y : O b) (T : Tg t a) (w : Lg a) (T′ : Tg t b) (w′ : Lg b) → EqLC R x y → ψC t R T w x ≈ ψ t T′ w′ y
ψQrS : ∀ {t L a b} (x : O a) (R : Strict b L) (y : Vs L R) (T : Tg t a) (w : Lg a) (T′ : Tg t b) (w′ : Lg b) → EqR x R y → ψ t T w x ≈ ψS t R T′ w′ y
ψQrC : ∀ {t L a b} (x : O a) (R : b ⊲ L) (y : Vc L R) (T : Tg t a) (w : Lg a) (T′ : Tg t b) (w′ : Lg b) → EqRC x R y → ψ t T w x ≈ ψC t R T′ w′ y

ψQ (oe R x) y T w T′ w′ e = ψQS R x y (tgS R T w) (lgS R w) T′ w′ e
ψQ {a = a} o0 (oe R y) T w T′ w′ e = ψQrS {a = a} o0 R y T w (tgS R T′ w′) (lgS R w′) e
ψQ (os x) (oe R y) T w T′ w′ e = ψQrS (os x) R y T w (tgS R T′ w′) (lgS R w′) e
ψQ (ol F) (oe R y) T w T′ w′ e = ψQrS (ol F) R y T w (tgS R T′ w′) (lgS R w′) e
ψQ (oi r f) (oe R y) T w T′ w′ e = ψQrS (oi r f) R y T w (tgS R T′ w′) (lgS R w′) e
ψQ {t} o0 o0 T w T′ w′ e = Ω≈ t
ψQ (os x) (os y) T w T′ w′ e = λ n → rep≈ (ψQ x y T w T′ w′ e) n
ψQ (ol F) (ol G) T w T′ w′ e = λ n → ψQ (F n) (G n) T w T′ w′ (e n)
ψQ {t} {a} {b} (oi {k = k} r f) (oi r′ f′) T w T′ w′ e with node≈ {r = r} {r′} {f} {f′} e | proj₁ e
... | N | refl with rkT r T w | rkT r′ T′ w′
... | keep s | keep s′ = ≈node refl (λ y y′ d → ψQ (f _) (f′ _) T w T′ w′ (N _ _ d))
... | keep s | rise q = ⊥-elim (no-keep-rise s q)
... | rise q | keep s = ⊥-elim (no-keep-rise s q)
... | rise q | rise q′ = λ n → ψQ (f _) (f′ _) T w T′ w′ (N _ _ (ch n))
  where
  F₁ : O k → O k
  F₁ z = ψ k (inj₁ (≪⊲ r)) w (f (inS (≪S r) z))
  F₂ : O k → O k
  F₂ z = ψ k (inj₁ (≪⊲ r′)) w′ (f′ (inS (≪S r′) z))
  ch : ∀ n → chainᵒ F₁ n ≈ chainᵒ F₂ n
  ch zero = Ω≈ k
  ch (suc n) = ψQ (f _) (f′ _) (inj₁ (≪⊲ r)) w (inj₁ (≪⊲ r′)) w′ (N _ _ (ch n))

ψQS (ss R) x y T w T′ w′ e = ψQC R x y T w T′ w′ e
ψQS (sl n R) x y T w T′ w′ e = ψQC R x y T w T′ w′ e
ψQC self x y T w T′ w′ e = ψQ x y T w T′ w′ e
ψQC (suc R) x y T w T′ w′ e = ψQC R x y T w T′ w′ e
ψQC (lim n R) x y T w T′ w′ e = ψQC R x y T w T′ w′ e

ψQrS x (ss R) y T w T′ w′ e = ψQrC x R y T w T′ w′ e
ψQrS x (sl n R) y T w T′ w′ e = ψQrC x R y T w T′ w′ e
ψQrC x self y T w T′ w′ e = ψQ x y T w T′ w′ e
ψQrC x (suc R) y T w T′ w′ e = ψQrC x R y T w T′ w′ e
ψQrC x (lim n R) y T w T′ w′ e = ψQrC x R y T w T′ w′ e
```
