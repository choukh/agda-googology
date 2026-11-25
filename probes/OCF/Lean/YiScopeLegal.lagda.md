# 作用域块的第一位置与合法性; 加法与 `top` 的合法性

非验收文件, 成品候选. 判决: 定义 (第 3 层的一部分) 与编译定理, 无前提. 第一位置 `Dn` 对新构造子: `into c t` 之下是 "送进孩子后在 `t` 之下" 或同一孩子里的严格之下; `up` 之下是 "包回外层后在外层那棵树之下" 或同一个 `up` 里的严格之下.
编译定理: 加法的三条 (`plus-weak`, `plus-dn`, `plus-lgl`), `succ-lgl`, `top-lgl` (一切层号的 `top` 合法). **折叠的合法性没有做到** (作用域里的 `sucS` 与洞, 见回报); 不否定它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiScopeLegal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.YiScopeCore
```

## 1 第一位置与合法性

`Cp` 是相等或严格. 结点的第一位置经过分支下标层的 `top` 那一支. 合法: ℕ 极限逐项是第一位置; 结点在合法的下标上分支合法并对下标单调;
`into` 与 `up` 看里面那棵树.

```agda
Dn : ∀ {K s} → Tr ⊥ K s → Tr ⊥ K s → Set

Cp : ∀ {K s} → Tr ⊥ K s → Tr ⊥ K s → Set
Cp z w = (z ≡ w) ⊎ Dn z w

Dn z G.zero = ⊥
Dn z (G.suc a) = Cp z a
Dn z (G.lim f) = Σ ℕ λ n → Cp z (f n)
Dn {K} {s} z (G.nd r h) = Cp z (h (tpD K s r))
Dn z (G.into c t) = Cp (G.up c refl z) t ⊎ (Σ _ λ t′ → (z ≡ G.into c t′) × Dn t′ t)
Dn z (G.up c refl w) = Cp (G.into c z) w ⊎ (Σ _ λ y′ → (z ≡ G.up c refl y′) × Dn y′ w)
Dn z (G.hole ())

Legal : ∀ K s → Tr ⊥ K s → Set
LegalD : ∀ K s → Root K s → Dom K s → Set
LeD : ∀ K s → Root K s → Dom K s → Dom K s → Set

Legal K s G.zero = ⊤
Legal K s (G.suc a) = Legal K s a
Legal K s (G.lim f) = (∀ n → Cp (f n) (f (suc n))) × (∀ n → Legal K s (f n))
Legal K s (G.nd r h) = (∀ η → LegalD K s r η → Legal K s (h η)) ×
  (∀ η η′ → LegalD K s r η → LeD K s r η η′ → LegalD K s r η′ → Cp (h η) (h η′))
Legal K s (G.into c t) = Legal K (sub K s c) t
Legal K s (G.up {s = s₀} c e y) = Legal K s₀ y
Legal K s (G.hole ())

LegalD zero (inj₁ _) ()
LegalD zero (inj₂ ())
LegalD (sup S g) (down c p) r = LegalD (g c) p r
LegalD (sup one g) root r = Legal (g tt) root
LegalD (sup nat g) root ()
LegalD (sup (raw k) g) root r = Legal k root

LeD zero (inj₁ _) ()
LeD zero (inj₂ ())
LeD (sup S g) (down c p) r = LeD (g c) p r
LeD (sup one g) root r = Cp
LeD (sup nat g) root ()
LeD (sup (raw k) g) root r = Cp
```

## 2 加法

`lift-sub`: 送进更深一层就是多一个 `up`. `lift-P`: 对 `up` 不变的谓词沿 `lift` 传下去 (对层号与路径归纳, 中间的树带洞, 所以谓词要一般).

```agda
up-cp : ∀ {K s} (c : Kid K s) {y w : Tr ⊥ K s} → Cp y w → Cp (G.up {s′ = sub K s c} c refl y) (G.up c refl w)
up-cp c (inj₁ refl) = inj₁ refl
up-cp c {y} (inj₂ p) = inj₂ (inj₂ (y , refl , p))

into-cp : ∀ {K s} (c : Kid K s) {t′ t : Tr ⊥ K (sub K s c)} → Cp t′ t → Cp (G.into c t′) (G.into c t)
into-cp c (inj₁ refl) = inj₁ refl
into-cp c {t′} (inj₂ p) = inj₂ (inj₂ (t′ , refl , p))

lift-sub : ∀ {Y} K s d (x : Tr Y K root) → lift K (sub K s d) x ≡ G.up d refl (lift K s x)
lift-sub zero s ()
lift-sub (sup S g) root d x = refl
lift-sub (sup S g) (down c p) d x =
  cong (un S g c (λ v → v) (sub (g c) p d)) (lift-sub (g c) p d (G.hole x))

lift-P : ∀ {Y} K (Q : ∀ s → Tr Y K s → Set) →
  (∀ s d y → Q s y → Q (sub K s d) (G.up d refl y)) → ∀ s x → Q root x → Q s (lift K s x)
lift-P K Q u root x q = q
lift-P zero Q u (inj₂ ())
lift-P (sup S g) Q u (down c p) x q =
  lift-P (g c) (λ p′ t → Q (down c p′) (un S g c (λ v → v) p′ t))
    (λ s d y → u (down c s) d (un S g c (λ v → v) s y)) p (G.hole x) (u root c x q)

lift-lgl : ∀ K s x → Legal K root x → Legal K s (lift K s x)
lift-lgl K = lift-P K (Legal K) (λ s d y q → q)

-- 在左加数 (送进作用域后) 之下的, 也在和之下.
plus-weak : ∀ {K s} (x : Raw K) (t : Tr ⊥ K s) {z} → Cp z (lift K s x) → Cp z (plus x t)
plus-weak x G.zero q = q
plus-weak x (G.suc a) q = inj₂ (plus-weak x a q)
plus-weak x (G.lim f) q = inj₂ (0 , plus-weak x (f 0) q)
plus-weak x (G.nd r h) q = inj₂ (plus-weak x (h _) q)
plus-weak {K} {s} x (G.into d t) {z} q = inj₂ (inj₁ (plus-weak x t
  (subst (Cp (G.up d refl z)) (sym (lift-sub K s d x)) (up-cp d q))))
plus-weak {K} x (G.up {s = s₀} d refl y) {z} q with subst (Cp z) (lift-sub K s₀ d x) q
... | inj₁ e = subst (λ z′ → Cp z′ (G.up d refl (plus x y))) (sym e) (up-cp d (plus-weak x y (inj₁ refl)))
... | inj₂ (inj₁ q′) = inj₂ (inj₁ (plus-weak x y q′))
... | inj₂ (inj₂ (y′ , e , q′)) =
  subst (λ z′ → Cp z′ (G.up d refl (plus x y))) (sym e) (up-cp d (plus-weak x y (inj₂ q′)))
plus-weak x (G.hole ())

plus-dn : ∀ {K s} (x : Raw K) (a b : Tr ⊥ K s) → Dn a b → Dn (plus x a) (plus x b)
plus-cp : ∀ {K s} (x : Raw K) (a b : Tr ⊥ K s) → Cp a b → Cp (plus x a) (plus x b)

plus-cp x a b (inj₁ refl) = inj₁ refl
plus-cp x a b (inj₂ p) = inj₂ (plus-dn x a b p)

plus-dn x a (G.suc b) p = plus-cp x a b p
plus-dn x a (G.lim f) (n , p) = n , plus-cp x a (f n) p
plus-dn x a (G.nd r h) p = plus-cp x a (h _) p
plus-dn x a (G.into c t) (inj₁ q) = inj₁ (plus-cp x (G.up c refl a) t q)
plus-dn x a (G.into c t) (inj₂ (t′ , e , q)) = inj₂ (plus x t′ , cong (plus x) e , plus-dn x t′ t q)
plus-dn x a (G.up c refl w) (inj₁ q) = inj₁ (plus-cp x (G.into c a) w q)
plus-dn x a (G.up c refl w) (inj₂ (y′ , e , q)) = inj₂ (plus x y′ , cong (plus x) e , plus-dn x y′ w q)
plus-dn x a (G.hole ())

plus-lgl : ∀ {K s} (x : Raw K) (t : Tr ⊥ K s) → Legal K root x → Legal K s t → Legal K s (plus x t)
plus-lgl {K} {s} x G.zero lx lt = lift-lgl K s x lx
plus-lgl x (G.suc a) lx lt = plus-lgl x a lx lt
plus-lgl x (G.lim f) lx (st , lf) = (λ n → plus-cp x _ _ (st n)) , (λ n → plus-lgl x (f n) lx (lf n))
plus-lgl x (G.nd r h) lx (lg , mo) =
  (λ η l → plus-lgl x (h η) lx (lg η l)) , (λ η η′ l e l′ → plus-cp x _ _ (mo η η′ l e l′))
plus-lgl x (G.into c t) lx lt = plus-lgl x t lx lt
plus-lgl x (G.up c e y) lx lt = plus-lgl x y lx lt
plus-lgl x (G.hole ())

acc-ind : ∀ {V : Set} (P : V → Set) (s : ℕ → V → V) → (∀ n y → P y → P (s n y)) → ∀ x → P x → ∀ n → P (acc s x n)
acc-ind P s h x px zero = px
acc-ind P s h x px (suc n) = h n _ (acc-ind P s h x px n)

succ-lgl : ∀ K (y : Raw K) → Legal K root y → Legal K root (sucS K root y)
succ-lgl K y ly = (λ n → plus-weak _ y (inj₁ refl)) ,
  acc-ind (Legal K root) _ (λ _ z lz → plus-lgl z y lz ly) y ly
```

## 3 闭树接到孩子作用域下; `top`

```agda
un-dn : ∀ S g c p (a b : Tr ⊥ (g c) p) → Dn a b → Dn (un S g c ⊥-elim p a) (un S g c ⊥-elim p b)
un-cp : ∀ S g c p (a b : Tr ⊥ (g c) p) → Cp a b → Cp (un S g c ⊥-elim p a) (un S g c ⊥-elim p b)

un-cp S g c p a b (inj₁ refl) = inj₁ refl
un-cp S g c p a b (inj₂ q) = inj₂ (un-dn S g c p a b q)

un-dn S g c p a (G.suc b) q = un-cp S g c p a b q
un-dn S g c p a (G.lim f) (n , q) = n , un-cp S g c p a (f n) q
un-dn S g c p a (G.nd r h) q = un-cp S g c p a (h _) q
un-dn S g c p a (G.into d t) (inj₁ q) = inj₁ (un-cp S g c (sub (g c) p d) (G.up d refl a) t q)
un-dn S g c p a (G.into d t) (inj₂ (t′ , e , q)) =
  inj₂ (_ , cong (un S g c ⊥-elim p) e , un-dn S g c (sub (g c) p d) t′ t q)
un-dn S g c p a (G.up {s = s₀} d refl w) (inj₁ q) = inj₁ (un-cp S g c s₀ (G.into d a) w q)
un-dn S g c p a (G.up {s = s₀} d refl w) (inj₂ (y′ , e , q)) =
  inj₂ (_ , cong (un S g c ⊥-elim p) e , un-dn S g c s₀ y′ w q)
un-dn S g c p a (G.hole ())

un-lgl : ∀ S g c p (t : Tr ⊥ (g c) p) → Legal (g c) p t → Legal (sup S g) (down c p) (un S g c ⊥-elim p t)
un-lgl S g c p G.zero l = tt
un-lgl S g c p (G.suc a) l = un-lgl S g c p a l
un-lgl S g c p (G.lim f) (st , lf) = (λ n → un-cp S g c p _ _ (st n)) , (λ n → un-lgl S g c p (f n) (lf n))
un-lgl S g c p (G.nd r h) (lg , mo) =
  (λ η l → un-lgl S g c p (h η) (lg η l)) , (λ η η′ l e l′ → un-cp S g c p _ _ (mo η η′ l e l′))
un-lgl S g c p (G.into d t) l = un-lgl S g c (sub (g c) p d) t l
un-lgl S g c p (G.up {s = s₀} d refl y) l = un-lgl S g c s₀ y l
un-lgl S g c p (G.hole ())

Kf-dn : ∀ {K} k {p} (T : Raw k → Raw K → Raw K) x (a b : Tr ⊥ k p) → Dn a b → Cp (Kf k T x a) (Kf k T x b)
Kf-cp : ∀ {K} k {p} (T : Raw k → Raw K → Raw K) x (a b : Tr ⊥ k p) → Cp a b → Cp (Kf k T x a) (Kf k T x b)

Kf-cp k T x a b (inj₁ refl) = inj₁ refl
Kf-cp k T x a b (inj₂ q) = Kf-dn k T x a b q

Kf-dn k T x a (G.suc b) q = inj₂ (0 , Kf-cp k T x a b q)
Kf-dn k T x a (G.lim f) (n , q) = inj₂ (n , Kf-cp k T x a (f n) q)
Kf-dn k T x a (G.nd r h) q = inj₂ (Kf-cp k T x a (h _) q)
Kf-dn k T x a (G.into c t) (inj₁ q) = Kf-cp k T x (G.up c refl a) t q
Kf-dn k T x a (G.into c t) (inj₂ (t′ , e , q)) =
  subst (λ a′ → Cp (Kf k T x a′) (Kf k T x t)) (sym e) (Kf-dn k T x t′ t q)
Kf-dn k T x a (G.up c refl w) (inj₁ q) = Kf-cp k T x (G.into c a) w q
Kf-dn k T x a (G.up c refl w) (inj₂ (y′ , e , q)) =
  subst (λ a′ → Cp (Kf k T x a′) (Kf k T x w)) (sym e) (Kf-dn k T x y′ w q)
Kf-dn k T x a (G.hole ())

top-lgl : ∀ K x → Legal K root x → Legal K root (top K x)
ct-lgl : ∀ S g c z → Legal (sup S g) root z → Legal (sup S g) root (ct S g c z)
tpD-lgl : ∀ K p r → LegalD K p r (tpD K p r)
Kf-lgl : ∀ {K} k {p} (T : Raw k → Raw K → Raw K) → (∀ η z → Legal K root z → Legal K root (T η z)) →
  (∀ η z → Cp z (T η z)) → ∀ x → Legal K root x → (t : Tr ⊥ k p) → Legal k p t → Legal K root (Kf k T x t)

top-lgl zero x lx = lx
top-lgl (sup one g) x lx =
  (λ η l → plus-lgl x (G.into tt (un one g tt ⊥-elim root η)) lx (un-lgl one g tt root η l)) ,
  (λ η η′ l e l′ → plus-cp x _ _ (into-cp tt (un-cp one g tt root η η′ e)))
top-lgl (sup nat g) x lx =
  (λ n → plus-weak _ (G.into (suc n) (un nat g (suc n) ⊥-elim root (top (g (suc n)) G.zero))) (inj₁ refl)) ,
  acc-ind (Legal (sup nat g) root) _ (λ m z lz → ct-lgl nat g (suc m) z lz) _ (ct-lgl nat g 0 x lx)
top-lgl (sup (raw k) g) x lx =
  (λ η l → Kf-lgl k (ct (raw k) g) (ct-lgl (raw k) g)
    (λ η′ z → plus-weak z (G.into η′ (un (raw k) g η′ ⊥-elim root (top (g η′) G.zero))) (inj₁ refl)) x lx η l) ,
  (λ η η′ l e l′ → Kf-cp k (ct (raw k) g) x η η′ e)

ct-lgl S g c z lz = plus-lgl z (G.into c (un S g c ⊥-elim root (top (g c) G.zero))) lz
  (un-lgl S g c root (top (g c) G.zero) (top-lgl (g c) G.zero tt))

tpD-lgl zero (inj₁ _) ()
tpD-lgl zero (inj₂ ())
tpD-lgl (sup S g) (down c p) r = tpD-lgl (g c) p r
tpD-lgl (sup one g) root r = top-lgl (g tt) G.zero tt
tpD-lgl (sup nat g) root ()
tpD-lgl (sup (raw k) g) root r = top-lgl k G.zero tt

Kf-lgl k T tl tw x lx G.zero l = tl _ x lx
Kf-lgl {K} k T tl tw x lx (G.suc a) l = (λ n → tw _ _) ,
  acc-ind (Legal K root) _ (λ _ z lz → tl _ z lz) _ (Kf-lgl k T tl tw x lx a l)
Kf-lgl k T tl tw x lx (G.lim f) (st , lf) =
  (λ n → Kf-cp k T x _ _ (st n)) , (λ n → Kf-lgl k T tl tw x lx (f n) (lf n))
Kf-lgl k {p} T tl tw x lx (G.nd r h) (lg , mo) = Kf-lgl k T tl tw x lx (h _) (lg _ (tpD-lgl k p r))
Kf-lgl k T tl tw x lx (G.into c t) l = Kf-lgl k T tl tw x lx t l
Kf-lgl k T tl tw x lx (G.up c e y) l = Kf-lgl k T tl tw x lx y l
Kf-lgl k T tl tw x lx (G.hole ())

-- 一切层号的 top 合法; 塔的各项与 Λ 的 top 是合法的闭树 (折叠之前).
top-legal : ∀ K → Legal K root (top K G.zero)
top-legal K = top-lgl K G.zero tt

top-tw-legal : ∀ n → Legal (tw n) root (top (tw n) G.zero)
top-tw-legal n = top-legal (tw n)

top-Λ-legal : Legal Λ root (top Λ G.zero)
top-Λ-legal = top-legal Λ
```
