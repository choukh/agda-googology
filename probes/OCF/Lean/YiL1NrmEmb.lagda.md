# 规范化 `nrmk` 不降层号: 前驱的保序嵌入

验收文件. 编译定理 `nrmkE`: 对一切合法的第 0 层树 ξ, ξ 读成的层号到 `nrmk ξ` 读成的层号有前驱的保序嵌入 (`PEmb`). 极限处 `nrmk` 取部分和, 第 n 块的前驱先判定是否已在第 n-1 块出现 (`dec`, 沿第一位置的结构递归), 未出现的平移到部分和之上 (`J`).
`fix1`: 树形如 `top + Z` 且 Z 不含零 (`ZF`) 时嵌入把 1 映到 1; 第 0 层的折叠值不含零 (`ZF-fold`). 用处: [YiL1Base](YiL1Base.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiL1NrmEmb where

open import Data.Nat.Base using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤-total; ≤⇒≤′; z≤′n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextValFin using (HS-readⁿ; cp⊑ⁿ)
import OCF.Lean.YiDlFold as W
open import OCF.Lean.YiShpOmega using (cpT)
open import OCF.Lean.YiPEStep using (_⊕_; ⊕-≺; ⊕-≅; ⊑⊕; toLevel-+; HS-≅)
open import OCF.Align.BTBOFullEmb using (PEmb)
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-suc; PEmb-limʳ; PEmb-limˡ)
import OCF.Align.Level as L
```

## 1 层号与第一位置

```agda
ℓv : (a : R) → Lgl zero a → L.Ordᴵ
ℓv a l = L.toLevel (NA.read a) (HS-readⁿ a l)

ℓv-⊑ : ∀ a b (la : Lgl zero a) (lb : Lgl zero b) → Cp zero a b → ℓv a la L.⊑ᴵ ℓv b lb
ℓv-⊑ a b la lb c = L.toLevel-⊑ (HS-readⁿ a la) (HS-readⁿ b lb) (cp⊑ⁿ a b c)

ℓv-≅ : ∀ a (l l′ : Lgl zero a) → ℓv a l L.≅ᴵ ℓv a l′
ℓv-≅ a l l′ = L.toLevel-≅ (HS-readⁿ a l) (HS-readⁿ a l′) (L.≅-refl⁰ (NA.read a))

≺⊑ : ∀ {c b a} → c L.≺ᴵ b → b L.⊑ᴵ a → c L.≺ᴵ a
≺⊑ (L.via e q) k = L.≺ᴵ-respˡ e (L.sim k q)

chainCp : ∀ (f : ℕ → R) → (∀ n → Cp zero (f n) (f (suc n))) → ∀ {i j} → i ≤′ j → Cp zero (f i) (f j)
chainCp f st ≤′-refl = inj₁ refl
chainCp f st (≤′-step p) = cpT zero (chainCp f st p) (st _)

Dec′ : Set → Set
Dec′ A = A ⊎ ¬ A

dec : ∀ a (la : Lgl zero a) b (lb : Lgl zero b) → Cp zero a b → ∀ {c} → c L.<ᴵ ℓv b lb → Dec′ (c L.≺ᴵ ℓv a la)
dec a la G.zero lb p ()
dec a la (G.suc b) lb (inj₁ refl) q = inj₁ (L.<-≅ q (ℓv-≅ (G.suc b) lb la))
dec a la (G.suc b) lb (inj₂ p) L.zero = inj₂ (λ r → L.≺ᴵ-irrefl (≺⊑ r (ℓv-⊑ a b la lb p)))
dec a la (G.suc b) lb (inj₂ p) (L.suc q) = dec a la b lb p q
dec a la (G.lim g) lb (inj₁ refl) q = inj₁ (L.<-≅ q (ℓv-≅ (G.lim g) lb la))
dec a la (G.lim g) (st , lg) (inj₂ (k , p)) (L.lim j q) with ≤-total j k
... | inj₁ j≤k with L.sim (ℓv-⊑ (g j) (g k) (lg j) (lg k) (chainCp g st (≤⇒≤′ j≤k))) q
...   | L.via e q′ with dec a la (g k) (lg k) p q′
...     | inj₁ y = inj₁ (L.≺ᴵ-respˡ e y)
...     | inj₂ ny = inj₂ (λ y → ny (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) y))
dec a la (G.lim g) (st , lg) (inj₂ (k , p)) (L.lim j q) | inj₂ k≤j =
  dec a la (g j) (lg j) (cpT zero p (chainCp g st (≤⇒≤′ k≤j))) q
dec a la (G.lc () h) lb p q
dec a la (G.em () d) lb p q
dec a la G.top lb (inj₁ refl) q = inj₁ (L.<-≅ q (ℓv-≅ G.top lb la))
dec a la G.top lb (inj₂ ()) q
```

## 2 嵌入

极限处的构造放在模块 `LimE` 里 (参数是各分量的嵌入 `ι`), 以便下一节谈它的像.

```agda
module LimE (f : ℕ → R) (st : ∀ n → Cp zero (f n) (f (suc n))) (lf : ∀ n → Lgl zero (f n))
  (ι : ∀ n → PEmb (ℓv (f n) (lf n)) (ℓv (WL.nrmk zero (f n)) (WL.nrmk-lgl zero (f n)))) where
  g : ℕ → R
  g n = WL.nrmk zero (f n)
  lg : ∀ n → Lgl zero (g n)
  lg n = WL.nrmk-lgl zero (f n)
  F : ℕ → L.Ordᴵ
  F n = ℓv (f n) (lf n)
  lps : ∀ n → Lgl zero (psum zero g n)
  lps = proj₂ (psum-lgl zero g lg)
  Gs : ℕ → L.Ordᴵ
  Gs n = ℓv (psum zero g n) (lps n)

  eG : ∀ n → (Gs n ⊕ ℓv (g (suc n)) (lg (suc n))) L.≅ᴵ Gs (suc n)
  eG n = L.≅ᴵ-trans
    (L.≅ᴵ-sym (toLevel-+ (NA.read (psum zero g n)) (NA.read (g (suc n)))
      (HS-readⁿ (psum zero g n) (lps n)) (HS-readⁿ (g (suc n)) (lg (suc n))) h))
    (L.toLevel-≅ h (HS-readⁿ (psum zero g (suc n)) (lps (suc n))) (L.≅-sym (NA.read-plus (psum zero g n) (g (suc n)))))
    where
    h : L.HS (NA.read (psum zero g n) L.+ NA.read (g (suc n)))
    h = HS-≅ (HS-readⁿ (psum zero g (suc n)) (lps (suc n))) (NA.read-plus (psum zero g n) (g (suc n)))

  G⊑ : ∀ n → Gs n L.⊑ᴵ Gs (suc n)
  G⊑ n = ℓv-⊑ (psum zero g n) (psum zero g (suc n)) (lps n) (lps (suc n)) (plus-weak zero (psum zero g n) (g (suc n)))

  cls : ∀ n {c} (r : c L.≺ᴵ F (suc n)) → Dec′ (c L.≺ᴵ F n)
  cls n (L.via e q) with dec (f n) (lf n) (f (suc n)) (lf (suc n)) (st n) q
  ... | inj₁ y = inj₁ (L.≺ᴵ-respˡ e y)
  ... | inj₂ ny = inj₂ (λ y → ny (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) y))

  J : ∀ n → PEmb (F n) (Gs n)
  mJ : ∀ n {c} (r : c L.≺ᴵ F (suc n)) → Dec′ (c L.≺ᴵ F n) → L.Ordᴵ
  bJ : ∀ n {c} (r : c L.≺ᴵ F (suc n)) (x : Dec′ (c L.≺ᴵ F n)) → mJ n r x L.≺ᴵ Gs (suc n)
  mnJ : ∀ n {c d} (r : c L.≺ᴵ F (suc n)) (s : d L.≺ᴵ F (suc n)) (x : Dec′ (c L.≺ᴵ F n)) (y : Dec′ (d L.≺ᴵ F n)) →
    c L.≺ᴵ d → mJ n r x L.≺ᴵ mJ n s y
  chJ : ∀ n {c d} (r : c L.≺ᴵ F (suc n)) (s : d L.≺ᴵ F (suc n)) (x : Dec′ (c L.≺ᴵ F n)) (y : Dec′ (d L.≺ᴵ F n)) →
    c L.≅ᴵ d → mJ n r x L.≅ᴵ mJ n s y

  J zero = ι 0
  J (suc n) = record
    { map = λ r → mJ n r (cls n r)
    ; bnd = λ r → bJ n r (cls n r)
    ; mono = λ r s lt → mnJ n r s (cls n r) (cls n s) lt
    ; coh = λ r s e → chJ n r s (cls n r) (cls n s) e }

  mJ n r (inj₁ y) = PEmb.map (J n) y
  mJ n r (inj₂ _) = Gs n ⊕ PEmb.map (ι (suc n)) r

  bJ n r (inj₁ y) = ≺⊑ (PEmb.bnd (J n) y) (G⊑ n)
  bJ n r (inj₂ _) = L.≺ᴵ-respʳ (⊕-≺ (Gs n) (PEmb.bnd (ι (suc n)) r)) (eG n)

  mnJ n r s (inj₁ a) (inj₁ b) lt = PEmb.mono (J n) a b lt
  mnJ n r s (inj₁ a) (inj₂ b) lt = ≺⊑ (PEmb.bnd (J n) a) (⊑⊕ (Gs n) _)
  mnJ n r s (inj₂ a) (inj₁ b) lt = ⊥-elim (a (L.≺ᴵ-trans lt b))
  mnJ n r s (inj₂ a) (inj₂ b) lt = ⊕-≺ (Gs n) (PEmb.mono (ι (suc n)) r s lt)

  chJ n r s (inj₁ a) (inj₁ b) e = PEmb.coh (J n) a b e
  chJ n r s (inj₁ a) (inj₂ b) e = ⊥-elim (b (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) a))
  chJ n r s (inj₂ a) (inj₁ b) e = ⊥-elim (a (L.≺ᴵ-respˡ e b))
  chJ n r s (inj₂ a) (inj₂ b) e = ⊕-≅ (Gs n) (PEmb.coh (ι (suc n)) r s e)

  up1 : ∀ n {c} (r : c L.≺ᴵ F n) (t : c L.≺ᴵ F (suc n)) → PEmb.map (J n) r L.≅ᴵ PEmb.map (J (suc n)) t
  up1 n r t with cls n t
  ... | inj₁ y = PEmb.coh (J n) r y (L.≅ᴵ-refl _)
  ... | inj₂ ny = ⊥-elim (ny r)

  cohJ : ∀ {n m} → n ≤′ m → ∀ {c} (r : c L.≺ᴵ F n) (t : c L.≺ᴵ F m) → PEmb.map (J n) r L.≅ᴵ PEmb.map (J m) t
  cohJ {n} ≤′-refl r t = PEmb.coh (J n) r t (L.≅ᴵ-refl _)
  cohJ {n} {suc m} (≤′-step p) r t = L.≅ᴵ-trans (cohJ p r r′) (up1 m r′ t)
    where
    r′ = ≺⊑ r (ℓv-⊑ (f n) (f m) (lf n) (lf m) (chainCp f st p))

  cohL : ∀ n m {c} (r : c L.≺ᴵ F n) (t : c L.≺ᴵ F m) → PEmb.map (J n) r L.≅ᴵ PEmb.map (J m) t
  cohL n m r t with ≤-total n m
  ... | inj₁ n≤m = cohJ (≤⇒≤′ n≤m) r t
  ... | inj₂ m≤n = L.≅ᴵ-sym (cohJ (≤⇒≤′ m≤n) t r)

  E : PEmb (ℓv (G.lim f) (st , lf)) (ℓv (WL.nrmk zero (G.lim f)) (WL.nrmk-lgl zero (G.lim f)))
  E = PEmb-limˡ (λ n → PEmb-limʳ n (J n)) cohL

nrmkE : ∀ ξ (l : Lgl zero ξ) → PEmb (ℓv ξ l) (ℓv (WL.nrmk zero ξ) (WL.nrmk-lgl zero ξ))
nrmkE G.zero l = PEmb-⊑ L.z⊑
nrmkE (G.suc a) l = PEmb-suc (nrmkE a l)
nrmkE (G.lc () h) l
nrmkE (G.em () a) l
nrmkE G.top l = PEmb-⊑ L.⊑ᴵ-refl
nrmkE (G.lim f) (st , lf) = LimE.E f st lf (λ n → nrmkE (f n) (lf n))
```

## 3 `top + Z` (Z 不含零) 上嵌入固定 1

```agda
ZF : R → Set
ZF G.zero = ⊥
ZF (G.suc a) = ZF a
ZF (G.lim f) = ∀ n → ZF (f n)
ZF (G.lc () g)
ZF (G.em () a)
ZF G.top = ⊤

one≺pt : ∀ W (l : Lgl zero (plus zero G.top W)) → ZF W → L.suc L.zero L.≺ᴵ ℓv (plus zero G.top W) l
one≺pt G.zero l ()
one≺pt (G.suc W) l z = L.≺-suc (one≺pt W l z)
one≺pt (G.lim h) (st , lh) z = L.≺-lim 0 (one≺pt (h 0) (lh 0) (z 0))
one≺pt (G.lc () g) l z
one≺pt (G.em () a) l z
one≺pt G.top l z = L.via (L.s≅ L.z≅) L.zero

fix1 : ∀ W (l : Lgl zero (plus zero G.top W)) → ZF W → ∀ (r : L.suc L.zero L.≺ᴵ ℓv (plus zero G.top W) l) →
  PEmb.map (nrmkE (plus zero G.top W) l) r L.≅ᴵ L.suc L.zero
fix1 G.zero l () r
fix1 (G.suc W) l z (L.via e L.zero) = ⊥-elim (L.≺ᴵ-irrefl (L.≺ᴵ-respˡ (L.≅ᴵ-sym e) (one≺pt W l z)))
fix1 (G.suc W) l z (L.via e (L.suc q)) = fix1 W l z (L.via e q)
fix1 (G.lim h) (st , lh) z (L.via e (L.lim n q)) = L.≅ᴵ-trans
  (L.≅ᴵ-sym (LimE.cohJ (λ i → plus zero G.top (h i)) st lh (λ i → nrmkE (plus zero G.top (h i)) (lh i))
    z≤′n (one≺pt (h 0) (lh 0) (z 0)) (L.via e q)))
  (fix1 (h 0) (lh 0) (z 0) (one≺pt (h 0) (lh 0) (z 0)))
fix1 (G.lc () g) l z r
fix1 (G.em () a) l z r
fix1 G.top l z (L.via e L.zero) = L.≅ᴵ-refl _
fix1 G.top l z (L.via () (L.suc L.zero))
```

## 4 第 0 层的折叠值不含零

```agda
ZF-plus : ∀ x y → ZF x → ZF y → ZF (plus zero x y)
ZF-plus x G.zero zx ()
ZF-plus x (G.suc y) zx zy = ZF-plus x y zx zy
ZF-plus x (G.lim f) zx zy = λ n → ZF-plus x (f n) zx (zy n)
ZF-plus x (G.lc () g) zx zy
ZF-plus x (G.em () a) zx zy
ZF-plus x G.top zx zy = zx

ZF-psum : ∀ h → (∀ n → ZF (h n)) → ∀ n → ZF (psum zero h n)
ZF-psum h zh zero = zh 0
ZF-psum h zh (suc n) = ZF-plus (psum zero h n) (h (suc n)) (ZF-psum h zh n) (zh (suc n))

ZF-succ : ∀ y → ZF y → ZF (succ zero y)
ZF-succ y zy zero = zy
ZF-succ y zy (suc n) = ZF-plus y _ zy (ZF-succ y zy n)

ZF-Ψn : ∀ j (w : Way zero j) gm gk → (∀ η → ZF (gm η)) → ZF (Ψn zero j w gm gk)
ZF-Ψn .(lev zero p) (keep p refl) gm gk h with p
... | ()
ZF-Ψn j fold gm gk h = λ n → h (chain j gk n)

ZF-ΨN : ∀ k r (w : Way zero (lev k r)) gm gk → (∀ η → ZF (gm η)) → ZF (ΨN zero k r w gm gk)
ZF-ΨN (suc k) (inj₁ _) = ZF-Ψn k
ZF-ΨN (suc k) (inj₂ r) = ZF-ΨN k r
ZF-ΨN (lim f) (n , r) = ZF-ΨN (f n) r
ZF-ΨN (lc j g) (η , _ , r) = ZF-ΨN (g η) r

ZF-ΩT : ∀ j (w : Way zero j) K o → (∀ n → ZF (o n)) → ZF (ΩT zero j w K o)
ZF-ΩT .(lev zero p) (keep p refl) K o h with p
... | ()
ZF-ΩT j fold K o h = h

ZF-fold : ∀ {k} (V : WL.Lw k) (x : Ext zero k) ξ → ZF (W.Ψ zero V x ξ)
ZF-fold V x G.zero = tt
ZF-fold V x (G.suc a) = ZF-succ (W.Ψ zero V x a) (ZF-fold V x a)
ZF-fold V x (G.lim f) = λ n → ZF-fold V x (f n)
ZF-fold {k} V x (G.lc r g) = ZF-ΨN k r (x r) _ _ (λ η → ZF-fold V x (g η))
ZF-fold WL.w0 x (G.em () a)
ZF-fold (WL.ws V) x (G.em _ a) = ZF-fold V (λ r → x (inj₂ r)) a
ZF-fold (WL.wl V st) x (G.em n a) = ZF-fold (V n) (λ r → x (n , r)) a
ZF-fold (WL.wΩ V w) x (G.em (η , l) a) = ZF-fold (V η l) (λ r → x (η , l , r)) a
ZF-fold WL.w0 x G.top = ZF-succ G.top tt
ZF-fold {suc k} (WL.ws V) x G.top = ZF-Ψn k (x (inj₁ tt)) _ _ (λ η → ZF-fold V (λ r → x (inj₂ r)) η)
ZF-fold (WL.wl V st) x G.top = λ n → ZF-psum _ (λ i → ZF-fold (V i) (λ r → x (i , r)) G.top) n
ZF-fold (WL.wΩ {k} {g} V w) x G.top = ZF-ΩT k (WL.rootW zero k g w x) _ _
  (ZF-psum _ (λ n → ZF-fold (V (WL.Pk.co (W.ptsΩ k g V n)) (WL.Pk.lw (W.ptsΩ k g V n)))
    (λ r → x (WL.Pk.co (W.ptsΩ k g V n) , WL.Pk.lw (W.ptsΩ k g V n) , r)) G.top))
```
