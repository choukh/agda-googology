# 带标注的加法: Ω 结点层号上标注随加法、后继、部分和、`Kfk` 走

非验收文件. 编译定理, 无前提. 标注用 [YiCtxAnn](YiCtxAnn.lagda.md) 的 `Mk`, `Pv`, `CpA`, `LglA`; 在 Ω 结点层号 `lc j h` 上, `x + top` 是 `suc x` (加法不打开结构), 所以标注可以逐个构造子随加法走 (`plusM`, `plusP`), 第二个加数不含嵌入 (`NE`) 时保第一位置与合法 (`plusA-weak`, `plusA-cp`, `plusA-lgl`); 后继, 部分和, `Kfk` 同理.
`fgL`, `fgC`: 去掉外层标注 (换成 `noM`) 保持带标注的合法与第一位置. `cv`: 位置上的分支域与位置的层号之间的拷贝 (产出端的根要用).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiProdArith where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; succ; psum)
open import OCF.Lean.YiLamFold using (Kfk; tp-lg)
open import OCF.Lean.YiCtxFold using (SB)
open import OCF.Lean.YiCtxAnn using
  ( Mk; noM; sucM; limM; lcM; Pv; noP; sucP; limP; lcP; mS; mL; mE; mB; pS; pL; pM; pB; CpA; DnA; LglA )
```

## 1 不含嵌入; 去掉外层标注

```agda
NE : ∀ {k} → Raw k → Set
NE G.zero = ⊤
NE (G.suc a) = NE a
NE (G.lim f) = ∀ n → NE (f n)
NE (G.lc r g) = ∀ ζ → NE (g ζ)
NE (G.em i a) = ⊥
NE G.top = ⊤

module _ {k : LF} where
  fgC : ∀ (S S′ : Pre k → Set) {a μa πa} t μ π → CpA S (a , μa , πa) t μ π → CpA S′ (a , noM , πa) t noM π
  fgD : ∀ (S S′ : Pre k → Set) {a μa πa} t μ π → DnA S (a , μa , πa) t μ π → DnA S′ (a , noM , πa) t noM π
  fgC S S′ t μ π (inj₁ refl) = inj₁ refl
  fgC S S′ t μ π (inj₂ p) = inj₂ (fgD S S′ t μ π p)
  fgD S S′ (G.suc d) μ π p = fgC S S′ d _ _ p
  fgD S S′ (G.lim f) μ π (n , p) = n , fgC S S′ (f n) _ _ p
  fgD S S′ (G.lc r g) μ π p = fgC S S′ _ _ _ p
  fgD S S′ {G.em i x} (G.em j d) μ π p = p
  fgD S S′ {G.zero} (G.em j d) μ π ()
  fgD S S′ {G.suc _} (G.em j d) μ π ()
  fgD S S′ {G.lim _} (G.em j d) μ π ()
  fgD S S′ {G.lc _ _} (G.em j d) μ π ()
  fgD S S′ {G.top} (G.em j d) μ π ()

  fgL : ∀ (S S′ : Pre k → Set) t μ π → LglA S t μ π → LglA S′ t noM π
  fgL S S′ G.zero μ π l = tt
  fgL S S′ (G.suc a) μ π l = fgL S S′ a _ _ l
  fgL S S′ (G.lim f) μ π (st , lf) = (λ n → fgC S S′ _ _ _ (st n)) , (λ n → fgL S S′ _ _ _ (lf n))
  fgL S S′ (G.lc r g) μ π (lg , mo , li) =
    (λ ζ l → fgL S S′ _ _ _ (lg ζ l)) , (λ ζ ζ′ l e l′ → fgC S S′ _ _ _ (mo ζ ζ′ l e l′)) , li
  fgL S S′ (G.em i a) μ π l = l
  fgL S S′ G.top μ π l = tt
```

## 2 Ω 结点层号上的加法

```agda
module _ {j : LF} {h : Raw j → LF} where
  private
    M : LF
    M = lc j h

  plusM : ∀ {S x} → Mk S x → (a : Raw M) → Mk S a → Mk S (plus M x a)
  plusM μx G.zero μa = μx
  plusM μx (G.suc a) μa = sucM (plusM μx a (mS μa))
  plusM μx (G.lim f) μa = limM (λ n → plusM μx (f n) (mL μa n))
  plusM μx (G.lc r g) μa = lcM (mE μa) (λ ζ → plusM μx (g ζ) (mB μa ζ))
  plusM μx (G.em i a) μa = noM
  plusM μx G.top μa = sucM μx

  plusP : ∀ {x} → Pv x → (a : Raw M) → Pv a → Pv (plus M x a)
  plusP πx G.zero πa = πx
  plusP πx (G.suc a) πa = sucP (plusP πx a (pS πa))
  plusP πx (G.lim f) πa = limP (λ n → plusP πx (f n) (pL πa n))
  plusP πx (G.lc r g) πa = lcP (λ ζ → plusM noM (g ζ) (pM πa ζ)) (λ ζ → plusP πx (g ζ) (pB πa ζ))
  plusP πx (G.em i a) πa = noP
  plusP πx G.top πa = sucP πx

  NE-plus : ∀ {x} (a : Raw M) → NE x → NE a → NE (plus M x a)
  NE-plus G.zero nx na = nx
  NE-plus (G.suc a) nx na = NE-plus a nx na
  NE-plus (G.lim f) nx na = λ n → NE-plus (f n) nx (na n)
  NE-plus (G.lc r g) nx na = λ ζ → NE-plus (g ζ) nx (na ζ)
  NE-plus (G.em i a) nx ()
  NE-plus G.top nx na = nx

  plusA-weak : ∀ {S x} μx πx (a : Raw M) μa πa → NE a →
    CpA S (x , μx , πx) (plus M x a) (plusM μx a μa) (plusP πx a πa)
  plusA-weak μx πx G.zero μa πa ne = inj₁ refl
  plusA-weak μx πx (G.suc a) μa πa ne = inj₂ (plusA-weak μx πx a (mS μa) (pS πa) ne)
  plusA-weak μx πx (G.lim f) μa πa ne = inj₂ (0 , plusA-weak μx πx (f 0) (mL μa 0) (pL πa 0) (ne 0))
  plusA-weak μx πx (G.lc r g) μa πa ne = inj₂ (plusA-weak μx πx (g _) (mB μa _) (pB πa _) (ne _))
  plusA-weak μx πx (G.em i a) μa πa ()
  plusA-weak μx πx G.top μa πa ne = inj₂ (inj₁ refl)

  plusA-cp : ∀ {S x} μx πx {a μa πa} (b : Raw M) μb πb → NE b → CpA S (a , μa , πa) b μb πb →
    CpA S (plus M x a , plusM μx a μa , plusP πx a πa) (plus M x b) (plusM μx b μb) (plusP πx b πb)
  plusA-dn : ∀ {S x} μx πx {a μa πa} (b : Raw M) μb πb → NE b → DnA S (a , μa , πa) b μb πb →
    DnA S (plus M x a , plusM μx a μa , plusP πx a πa) (plus M x b) (plusM μx b μb) (plusP πx b πb)
  plusA-cp μx πx b μb πb ne (inj₁ refl) = inj₁ refl
  plusA-cp μx πx b μb πb ne (inj₂ p) = inj₂ (plusA-dn μx πx b μb πb ne p)
  plusA-dn μx πx (G.suc d) μb πb ne p = plusA-cp μx πx d _ _ ne p
  plusA-dn μx πx (G.lim f) μb πb ne (n , p) = n , plusA-cp μx πx (f n) _ _ (ne n) p
  plusA-dn μx πx (G.lc r g) μb πb ne p = plusA-cp μx πx _ _ _ (ne _) p
  plusA-dn μx πx (G.em i d) μb πb () p
  plusA-dn μx πx G.zero μb πb ne ()
  plusA-dn μx πx G.top μb πb ne ()

  plusA-lgl : ∀ {S x} μx πx (a : Raw M) μa πa → NE a → LglA S x μx πx → LglA S a μa πa →
    LglA S (plus M x a) (plusM μx a μa) (plusP πx a πa)
  plusA-lgl μx πx G.zero μa πa ne lx la = lx
  plusA-lgl μx πx (G.suc a) μa πa ne lx la = plusA-lgl μx πx a _ _ ne lx la
  plusA-lgl μx πx (G.lim f) μa πa ne lx (st , lf) =
    (λ n → plusA-cp μx πx (f (suc n)) _ _ (ne (suc n)) (st n)) , (λ n → plusA-lgl μx πx (f n) _ _ (ne n) lx (lf n))
  plusA-lgl {S} {x} μx πx (G.lc r g) μa πa ne lx (lg , mo , li) =
    (λ ζ l → plusA-lgl μx πx (g ζ) _ _ (ne ζ) lx (lg ζ l)) ,
    (λ ζ ζ′ l e l′ → plusA-cp μx πx (g ζ′) _ _ (ne ζ′) (mo ζ ζ′ l e l′)) ,
    (λ ζ l → plusA-lgl noM πx (g ζ) _ _ (ne ζ) (fgL S (SB M r) x μx πx lx) (li ζ l))
  plusA-lgl μx πx (G.em i a) μa πa () lx la
  plusA-lgl μx πx G.top μa πa ne lx la = lx
```

## 3 右侧累加 (部分和, `Kfk`) 与后继

`accM b μb μx n`: `x` 依次右加 `b 0, …, b (n-1)` 的标注.

```agda
  accM : ∀ {S} (b : ℕ → Raw M) → (∀ n → Mk S (b n)) → ∀ {x} → Mk S x → ∀ n → Mk S (acc (λ n z → plus M z (b n)) x n)
  accM b μb μx zero = μx
  accM b μb μx (suc n) = plusM (accM b μb μx n) (b n) (μb n)

  accP : ∀ (b : ℕ → Raw M) → (∀ n → Pv (b n)) → ∀ {x} → Pv x → ∀ n → Pv (acc (λ n z → plus M z (b n)) x n)
  accP b πb πx zero = πx
  accP b πb πx (suc n) = plusP (accP b πb πx n) (b n) (πb n)

  NE-acc : ∀ (b : ℕ → Raw M) {x} → (∀ n → NE (b n)) → NE x → ∀ n → NE (acc (λ n z → plus M z (b n)) x n)
  NE-acc b nb nx zero = nx
  NE-acc b nb nx (suc n) = NE-plus (b n) (NE-acc b nb nx n) (nb n)

  accA-lgl : ∀ {S} (b : ℕ → Raw M) μb πb {x} μx πx → (∀ n → NE (b n)) → (∀ n → LglA S (b n) (μb n) (πb n)) →
    LglA S x μx πx → LglA S (G.lim (acc (λ n z → plus M z (b n)) x)) (limM (accM b μb μx)) (limP (accP b πb πx))
  accA-lgl b μb πb μx πx nb lb lx = (λ n → plusA-weak _ _ (b n) (μb n) (πb n) (nb n)) , go
    where
    go : ∀ n → LglA _ (acc (λ n z → plus M z (b n)) _ n) (accM b μb μx n) (accP b πb πx n)
    go zero = lx
    go (suc n) = plusA-lgl _ _ (b n) _ _ (nb n) (go n) (lb n)

  psumM : ∀ {S} {g : ℕ → Raw M} → (∀ n → Mk S (g n)) → Mk S (G.lim (psum M g))
  psumM {g = g} μg = limM (accM (λ n → g (suc n)) (λ n → μg (suc n)) (μg zero))

  psumP : ∀ {g : ℕ → Raw M} → (∀ n → Pv (g n)) → Pv (G.lim (psum M g))
  psumP {g} πg = limP (accP (λ n → g (suc n)) (λ n → πg (suc n)) (πg zero))

  NE-psum : ∀ (g : ℕ → Raw M) → (∀ n → NE (g n)) → NE (G.lim (psum M g))
  NE-psum g ng = NE-acc (λ n → g (suc n)) (λ n → ng (suc n)) (ng zero)

  psumA-lgl : ∀ {S} (g : ℕ → Raw M) μg πg → (∀ n → NE (g n)) → (∀ n → LglA S (g n) (μg n) (πg n)) →
    LglA S (G.lim (psum M g)) (psumM μg) (psumP πg)
  psumA-lgl g μg πg ng lg = accA-lgl (λ n → g (suc n)) _ _ _ _ (λ n → ng (suc n)) (λ n → lg (suc n)) (lg zero)
```

后继 `succ M y` 是 `y` 的左加累加.

```agda
  sacM : ∀ {S y} → Mk S y → ∀ n → Mk S (acc (λ _ z → plus M y z) y n)
  sacM μ zero = μ
  sacM {y = y} μ (suc n) = plusM μ (acc (λ _ z → plus M y z) y n) (sacM μ n)

  sacP : ∀ {y} → Pv y → ∀ n → Pv (acc (λ _ z → plus M y z) y n)
  sacP π zero = π
  sacP {y} π (suc n) = plusP π (acc (λ _ z → plus M y z) y n) (sacP π n)

  succM : ∀ {S y} → Mk S y → Mk S (succ M y)
  succM μ = limM (sacM μ)

  succP : ∀ {y} → Pv y → Pv (succ M y)
  succP π = limP (sacP π)

  NE-sac : ∀ {y} → NE y → ∀ n → NE (acc (λ _ z → plus M y z) y n)
  NE-sac ny zero = ny
  NE-sac {y} ny (suc n) = NE-plus (acc (λ _ z → plus M y z) y n) ny (NE-sac ny n)

  NE-succ : ∀ {y} → NE y → NE (succ M y)
  NE-succ = NE-sac

  succA-lgl : ∀ {S y} μ π → NE y → LglA S y μ π → LglA S (succ M y) (succM μ) (succP π)
  succA-lgl {S} {y} μ π ny ly = st , go
    where
    st : ∀ n → CpA S (acc (λ _ z → plus M y z) y n , sacM μ n , sacP π n)
      (acc (λ _ z → plus M y z) y (suc n)) (sacM μ (suc n)) (sacP π (suc n))
    st zero = plusA-weak μ π y μ π ny
    st (suc n) = plusA-cp μ π (acc (λ _ z → plus M y z) y (suc n)) _ _ (NE-sac ny (suc n)) (st n)
    go : ∀ n → LglA S (acc (λ _ z → plus M y z) y n) (sacM μ n) (sacP π n)
    go zero = ly
    go (suc n) = plusA-lgl μ π (acc (λ _ z → plus M y z) y n) _ _ (NE-sac ny n) ly (go n)
```

## 4 `Kfk` 的标注

```agda
  KfkM : ∀ {S} i {T : Raw i → Raw M} → (∀ η → Mk S (T η)) → ∀ ξ → Mk S (Kfk i T ξ)
  KfkM i μT G.zero = μT G.zero
  KfkM i {T} μT (G.suc a) = limM (accM (λ _ → T (G.suc a)) (λ _ → μT (G.suc a)) (KfkM i μT a))
  KfkM i μT (G.lim f) = limM (λ n → KfkM i μT (f n))
  KfkM i μT (G.lc r g) = sucM (KfkM i μT (g (Lay.tp (Lo i r))))
  KfkM zero μT (G.em () a)
  KfkM (suc i) μT (G.em _ a) = KfkM i (λ b → μT (G.em tt b)) a
  KfkM (lim f) μT (G.em n a) = KfkM (f n) (λ b → μT (G.em n b)) a
  KfkM (lc k g) μT (G.em (η , l) a) = KfkM (g η) (λ b → μT (G.em (η , l) b)) a
  KfkM i μT G.top = μT G.top

  KfkP : ∀ i {T : Raw i → Raw M} → (∀ η → Pv (T η)) → ∀ ξ → Pv (Kfk i T ξ)
  KfkP i πT G.zero = πT G.zero
  KfkP i {T} πT (G.suc a) = limP (accP (λ _ → T (G.suc a)) (λ _ → πT (G.suc a)) (KfkP i πT a))
  KfkP i πT (G.lim f) = limP (λ n → KfkP i πT (f n))
  KfkP i πT (G.lc r g) = sucP (KfkP i πT (g (Lay.tp (Lo i r))))
  KfkP zero πT (G.em () a)
  KfkP (suc i) πT (G.em _ a) = KfkP i (λ b → πT (G.em tt b)) a
  KfkP (lim f) πT (G.em n a) = KfkP (f n) (λ b → πT (G.em n b)) a
  KfkP (lc k g) πT (G.em (η , l) a) = KfkP (g η) (λ b → πT (G.em (η , l) b)) a
  KfkP i πT G.top = πT G.top

  NE-Kfk : ∀ i {T : Raw i → Raw M} → (∀ η → NE (T η)) → ∀ ξ → NE (Kfk i T ξ)
  NE-Kfk i nT G.zero = nT G.zero
  NE-Kfk i {T} nT (G.suc a) = NE-acc (λ _ → T (G.suc a)) (λ _ → nT (G.suc a)) (NE-Kfk i nT a)
  NE-Kfk i nT (G.lim f) = λ n → NE-Kfk i nT (f n)
  NE-Kfk i nT (G.lc r g) = NE-Kfk i nT (g (Lay.tp (Lo i r)))
  NE-Kfk zero nT (G.em () a)
  NE-Kfk (suc i) nT (G.em _ a) = NE-Kfk i (λ b → nT (G.em tt b)) a
  NE-Kfk (lim f) nT (G.em n a) = NE-Kfk (f n) (λ b → nT (G.em n b)) a
  NE-Kfk (lc k g) nT (G.em (η , l) a) = NE-Kfk (g η) (λ b → nT (G.em (η , l) b)) a
  NE-Kfk i nT G.top = nT G.top

  KfkA-cp : ∀ {S} i {T : Raw i → Raw M} μT πT {a b} → Cp i a b →
    CpA S (Kfk i T a , KfkM i μT a , KfkP i πT a) (Kfk i T b) (KfkM i μT b) (KfkP i πT b)
  KfkA-dn : ∀ {S} i {T : Raw i → Raw M} μT πT {a} b → Dn i a b →
    DnA S (Kfk i T a , KfkM i μT a , KfkP i πT a) (Kfk i T b) (KfkM i μT b) (KfkP i πT b)
  KfkA-cp i μT πT (inj₁ refl) = inj₁ refl
  KfkA-cp i μT πT (inj₂ p) = inj₂ (KfkA-dn i μT πT _ p)
  KfkA-dn i μT πT (G.suc b) p = 0 , KfkA-cp i μT πT p
  KfkA-dn i μT πT (G.lim f) (n , p) = n , KfkA-cp i μT πT p
  KfkA-dn i μT πT (G.lc r g) p = KfkA-cp i μT πT p
  KfkA-dn (suc i) μT πT {G.em _ a} (G.em _ d) (refl , p) = KfkA-dn i _ _ d p
  KfkA-dn (lim f) μT πT {G.em n a} (G.em _ d) (refl , p) = KfkA-dn (f n) _ _ d p
  KfkA-dn (lc k g) μT πT {G.em (η , l) a} (G.em _ d) (refl , p) = KfkA-dn (g η) _ _ d p

  KfkA-lgl : ∀ {S} i {T : Raw i → Raw M} μT πT → (∀ η → NE (T η)) → (∀ η → LglA S (T η) (μT η) (πT η)) →
    ∀ ξ → Lgl i ξ → LglA S (Kfk i T ξ) (KfkM i μT ξ) (KfkP i πT ξ)
  KfkA-lgl i μT πT nT lT G.zero l = lT G.zero
  KfkA-lgl i {T} μT πT nT lT (G.suc a) l =
    accA-lgl (λ _ → T (G.suc a)) _ _ _ _ (λ _ → nT (G.suc a)) (λ _ → lT (G.suc a)) (KfkA-lgl i μT πT nT lT a l)
  KfkA-lgl i μT πT nT lT (G.lim f) (st , lf) =
    (λ n → KfkA-cp i μT πT (st n)) , (λ n → KfkA-lgl i μT πT nT lT (f n) (lf n))
  KfkA-lgl i μT πT nT lT (G.lc r g) (lg , mo) = KfkA-lgl i μT πT nT lT _ (lg _ (tp-lg i r))
  KfkA-lgl zero μT πT nT lT (G.em () a) l
  KfkA-lgl (suc i) μT πT nT lT (G.em _ a) l = KfkA-lgl i _ _ (λ b → nT _) (λ b → lT _) a l
  KfkA-lgl (lim f) μT πT nT lT (G.em n a) l = KfkA-lgl (f n) _ _ (λ b → nT _) (λ b → lT _) a l
  KfkA-lgl (lc k g) μT πT nT lT (G.em (η , lη) a) l = KfkA-lgl (g η) _ _ (λ b → nT _) (λ b → lT _) a l
  KfkA-lgl i μT πT nT lT G.top l = lT G.top
```

## 5 位置的分支域与层号

```agda
cv : ∀ k (r : Pre k) → Lay.A (Lo k r) → Raw (lev k r)
cv (suc k) (inj₁ _) a = a
cv (suc k) (inj₂ r) a = cv k r a
cv (lim f) (n , r) a = cv (f n) r a
cv (lc k g) (η , _ , r) a = cv (g η) r a

cv-tp : ∀ k r → cv k r (Lay.tp (Lo k r)) ≡ G.top
cv-tp (suc k) (inj₁ _) = refl
cv-tp (suc k) (inj₂ r) = cv-tp k r
cv-tp (lim f) (n , r) = cv-tp (f n) r
cv-tp (lc k g) (η , _ , r) = cv-tp (g η) r

cv-lg : ∀ k r a → Lay.lg (Lo k r) a → Lgl (lev k r) (cv k r a)
cv-lg (suc k) (inj₁ _) a l = l
cv-lg (suc k) (inj₂ r) = cv-lg k r
cv-lg (lim f) (n , r) = cv-lg (f n) r
cv-lg (lc k g) (η , _ , r) = cv-lg (g η) r

cv-le : ∀ k r {a b} → Le (Lo k r) a b → Cp (lev k r) (cv k r a) (cv k r b)
cv-le (suc k) (inj₁ _) e = e
cv-le (suc k) (inj₂ r) = cv-le k r
cv-le (lim f) (n , r) = cv-le (f n) r
cv-le (lc k g) (η , _ , r) = cv-le (g η) r
```
