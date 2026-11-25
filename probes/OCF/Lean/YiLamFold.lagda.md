# 一致的折叠: Ω 结点层号任意, 塔的一切项与 Λ 的闭项

非验收文件, 设计候选 (第八次独立审查的临时试验 `R8Fin`, 主审 2026-11-12 移入, 代码未改). 在 [YiNextBase](YiNextBase.lagda.md) 的部件上: 公共上界 `Lw` 的 `wΩ` 对任意 `lc k g` 成立, 带可缺的根见证 `Wit` (`tw 2` 上就是 `p₀`); 保留结点的分支族是一般层上的结构累加 `Kfk`, 坐标先归一 `nrmk`; 链的观察取部分和; 派发 `dfin` 只在目标层字面是有限数时按头构造子保留. 编译定理: `TΛ-legal : Lgl zero TΛ` (读法 ψ₀(Λ)), `Tw-legal`, `T⁺ʷ-legal`, 都无前提; `TΛ-form` 是 `refl`. 没有值定理. 有限测试在 [YiLamTest](YiLamTest.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamFold where
open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst; subst₂)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using
  ( plus-lgl; plus-weak; add-cp; dnLc; lev; Way; keep; fold; Ext; Shift; R; ⌜_⌝
  ; iter; nodeAt; chain; Ψn; ΨN; succ; psum; self; succ-lgl; psum-lgl; ΨN-dn; ΨN-lgl
  ; Ψn-lgl; Br; acc-ind; ΩT; ΩT-lgl )
import OCF.Lean.YiNextTower as T

cps : ∀ {a b} → T.CP a b → Shift a b
cps T.self q = q , refl
cps (T.suc p) q = inj₂ (proj₁ (cps p q)) , proj₂ (cps p q)
cps (T.lim n p) q = (n , proj₁ (cps p q)) , proj₂ (cps p q)
cps (T.fst p) q = (G.top , tt , proj₁ (cps p q)) , proj₂ (cps p q)

------------------------------------------------------------------------
-- 一般层上的结构累加与归一 (U12 的判断: "归一只会处理 ℕ 极限")

tp-lg : ∀ j r → Lay.lg (Lo j r) (Lay.tp (Lo j r))
tp-lg (suc k) (inj₁ _) = tt
tp-lg (suc k) (inj₂ r) = tp-lg k r
tp-lg (lim f) (n , r) = tp-lg (f n) r
tp-lg (lc k g) (η , _ , r) = tp-lg (g η) r

Kfk : ∀ j {M} → (Raw j → Raw M) → Raw j → Raw M
Kfk j T G.zero = T G.zero
Kfk j {M} T (G.suc a) = G.lim (acc (λ _ z → plus M z (T (G.suc a))) (Kfk j T a))
Kfk j T (G.lim f) = G.lim (λ n → Kfk j T (f n))
Kfk j T (G.lc r g) = G.suc (Kfk j T (g (Lay.tp (Lo j r))))
Kfk zero T (G.em () a)
Kfk (suc j) T (G.em _ a) = Kfk j (λ b → T (G.em tt b)) a
Kfk (lim f) T (G.em n a) = Kfk (f n) (λ b → T (G.em n b)) a
Kfk (lc k g) T (G.em (η , l) a) = Kfk (g η) (λ b → T (G.em (η , l) b)) a
Kfk j T G.top = T G.top

Kfk-cp : ∀ j {M} T {a b} → Cp j a b → Cp M (Kfk j {M} T a) (Kfk j T b)
Kfk-dn : ∀ j {M} T {a} b → Dn j a b → Dn M (Kfk j {M} T a) (Kfk j T b)
Kfk-cp j T (inj₁ refl) = inj₁ refl
Kfk-cp j T (inj₂ p) = inj₂ (Kfk-dn j T _ p)
Kfk-dn j T (G.suc b) p = 0 , Kfk-cp j T p
Kfk-dn j T (G.lim f) (n , p) = n , Kfk-cp j T p
Kfk-dn j T (G.lc r g) p = Kfk-cp j T p
Kfk-dn (suc j) T {G.em _ a} (G.em _ d) (refl , p) = Kfk-dn j _ d p
Kfk-dn (lim f) T {G.em n a} (G.em _ d) (refl , p) = Kfk-dn (f n) _ d p
Kfk-dn (lc k g) T {G.em (η , l) a} (G.em _ d) (refl , p) = Kfk-dn (g η) _ d p

Kfk-lgl : ∀ j {M} T → (∀ η → Lgl M (T η)) → ∀ η → Lgl j η → Lgl M (Kfk j {M} T η)
Kfk-lgl j T h G.zero l = h G.zero
Kfk-lgl j {M} T h (G.suc a) l = (λ n → plus-weak M _ _) ,
  acc-ind (Lgl M) _ (λ _ z lz → plus-lgl M z _ lz (h _)) _ (Kfk-lgl j T h a l)
Kfk-lgl j T h (G.lim f) (st , lf) = (λ n → Kfk-cp j T (st n)) , (λ n → Kfk-lgl j T h (f n) (lf n))
Kfk-lgl j T h (G.lc r g) (lg , mo) = Kfk-lgl j T h (g (Lay.tp (Lo j r))) (lg _ (tp-lg j r))
Kfk-lgl (suc j) T h (G.em _ a) l = Kfk-lgl j _ (λ b → h _) a l
Kfk-lgl (lim f) T h (G.em n a) l = Kfk-lgl (f n) _ (λ b → h _) a l
Kfk-lgl (lc k g) T h (G.em (η , lη) a) l = Kfk-lgl (g η) _ (λ b → h _) a l
Kfk-lgl j T h G.top l = h G.top

Kfk-br : ∀ j {M} T → (∀ η → Lgl M (T η)) → Br (layer j) M (Kfk j {M} T)
Kfk-br j T h = Kfk-lgl j T h , λ η η′ l e l′ → Kfk-cp j T e

KfN : ∀ k r {M} → (Lay.A (Lo k r) → Raw M) → Lay.A (Lo k r) → Raw M
KfN (suc k) (inj₁ _) = Kfk k
KfN (suc k) (inj₂ r) = KfN k r
KfN (lim f) (n , r) = KfN (f n) r
KfN (lc k g) (η , _ , r) = KfN (g η) r

KfN-br : ∀ k r {M} T → (∀ η → Lgl M (T η)) → Br (Lo k r) M (KfN k r {M} T)
KfN-br (suc k) (inj₁ _) = Kfk-br k
KfN-br (suc k) (inj₂ r) = KfN-br k r
KfN-br (lim f) (n , r) = KfN-br (f n) r
KfN-br (lc k g) (η , _ , r) = KfN-br (g η) r

nrmk : ∀ k → Raw k → Raw k
nrmk k G.zero = G.zero
nrmk k (G.suc a) = G.suc (nrmk k a)
nrmk k (G.lim f) = G.lim (psum k (λ n → nrmk k (f n)))
nrmk k (G.lc r g) = G.lc r (KfN k r (λ η → nrmk k (g η)))
nrmk zero (G.em () a)
nrmk (suc k) (G.em i a) = G.em i (nrmk k a)
nrmk (lim f) (G.em n a) = G.em n (nrmk (f n) a)
nrmk (lc j g) (G.em (η , l) a) = G.em (η , l) (nrmk (g η) a)
nrmk k G.top = G.top

nrmk-lgl : ∀ k η → Lgl k (nrmk k η)
nrmk-lgl k G.zero = tt
nrmk-lgl k (G.suc a) = nrmk-lgl k a
nrmk-lgl k (G.lim f) = psum-lgl k _ (λ n → nrmk-lgl k (f n))
nrmk-lgl k (G.lc r g) = KfN-br k r _ (λ η → nrmk-lgl k (g η))
nrmk-lgl (suc k) (G.em i a) = nrmk-lgl k a
nrmk-lgl (lim f) (G.em n a) = nrmk-lgl (f n) a
nrmk-lgl (lc j g) (G.em (η , l) a) = nrmk-lgl (g η) a
nrmk-lgl k G.top = tt

------------------------------------------------------------------------
-- 有限目标层上的派发: 层号与有限数的字面相等可判定 (只看头构造子), 槽位在有限数的位置里.

fin : ℕ → LF
fin zero = zero
fin (suc n) = suc (fin n)

eqFin : ∀ n (L : LF) → Maybe (fin n ≡ L)
eqFin zero zero = just refl
eqFin (suc n) (suc L) with eqFin n L
... | just e = just (cong suc e)
... | nothing = nothing
eqFin _ _ = nothing

slotFin : ∀ n (L : LF) → Maybe (Σ (Pre (fin n)) λ s → lev (fin n) s ≡ L)
slotFin zero L = nothing
slotFin (suc n) L with eqFin n L
... | just e = just (inj₁ tt , e)
... | nothing with slotFin n L
...   | just (s , e) = just (inj₂ s , e)
...   | nothing = nothing

finOf : ∀ (k : LF) → Maybe (Σ ℕ λ n → fin n ≡ k)
finOf zero = just (zero , refl)
finOf (suc k) with finOf k
... | just (n , e) = just (suc n , cong suc e)
... | nothing = nothing
finOf _ = nothing

dfin₀ : ∀ n K → Ext (fin n) K
dfin₀ n K r with slotFin n (lev K r)
... | just (s , e) = keep s e
... | nothing = fold

dfin : ∀ k K → Ext k K
dfin k K r with finOf k
... | just (n , e) = subst (λ t → Way t (lev K r)) e (dfin₀ n K r)
... | nothing = fold

------------------------------------------------------------------------
-- 公共上界: Ω 结点层号任意; 根见证可缺

data Wit (k : LF) (g : Raw k → LF) : Set where
  none : Wit k g
  at : (ρ : Pre (g G.top)) → lev (g G.top) ρ ≡ k → Wit k g

data Lw : LF → Set where
  w0 : Lw zero
  ws : ∀ {k} → Lw k → Lw (suc k)
  wl : ∀ {f} → (∀ n → Lw (f n)) → (∀ n → Shift (f n) (f (suc n))) → Lw (lim f)
  wΩ : ∀ {k g} → (∀ η → Lgl k η → Lw (g η)) → Wit k g → Lw (lc k g)

shiftw : ∀ {f : ℕ → LF} → (∀ n → Shift (f n) (f (suc n))) → ∀ {n m} → n ≤′ m → Shift (f n) (f m)
shiftw st ≤′-refl q = q , refl
shiftw st (≤′-step p) q =
  proj₁ (st _ (proj₁ (shiftw st p q))) , trans (proj₂ (st _ _)) (proj₂ (shiftw st p q))

cmpw : ∀ {k} → Lw k → (q r : Pre k) → Way (lev k q) (lev k r)
cmpw w0 () r
cmpw (ws V) (inj₁ _) (inj₂ r) = keep r refl
cmpw (ws V) (inj₂ q) (inj₂ r) = cmpw V q r
cmpw (ws V) q r = fold
cmpw (wl V st) (n , q) (m , r) =
  subst₂ Way (proj₂ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r))
    (cmpw (V (n ⊔ m)) (proj₁ (shiftw st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₁ (shiftw st (≤⇒≤′ (m≤n⊔m n m)) r)))
-- Ω 结点层号上: 不比较两支的坐标, 只在目标层是字面的有限数时按层号的头构造子保留.
cmpw {lc k g} (wΩ V w) q r = dfin (lev (lc k g) q) (lc k g) r



record Pk (k : LF) : Set where
  constructor pk
  field
    co : Raw k
    lw : Lgl k co
open Pk

-- 根的派发: 有见证时取外部派发在 (top, tt, ρ) 上的值, 否则折叠.
rootW : ∀ m k (g : Raw k → LF) → Wit k g → Ext m (lc k g) → Way m k
rootW m k g none x = fold
rootW m k g (at ρ e) x = subst (Way m) e (x (G.top , tt , ρ))

Ψ : ∀ m {k} → Lw k → Ext m k → Raw k → Raw m
Ψ-lgl : ∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
Ψ-cp : ∀ m {k} (V : Lw k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
Ψ-dn : ∀ m {k} (V : Lw k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Ψ m V x ξ) (Ψ m V x ξ′)
ptsΩ : ∀ k (g : Raw k → LF) → (∀ η → Lgl k η → Lw (g η)) → ℕ → Pk k

Ψ m V x G.zero = G.top
Ψ m V x (G.suc a) = succ m (Ψ m V x a)
Ψ m V x (G.lim f) = G.lim (λ n → Ψ m V x (f n))
Ψ m {k} V x (G.lc r g) =
  ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmpw V r) (g η))
Ψ m (ws V) x (G.em _ a) = Ψ m V (λ r → x (inj₂ r)) a
Ψ m (wl V st) x (G.em n a) = Ψ m (V n) (λ r → x (n , r)) a
Ψ m (wΩ V w) x (G.em (η , l) a) = Ψ m (V η l) (λ r → x (η , l , r)) a
Ψ m w0 x G.top = succ m G.top
Ψ m {suc k} (ws V) x G.top =
  Ψn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
Ψ m (wl V st) x G.top = G.lim (psum m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top))
Ψ m (wΩ {k} {g} V w) x G.top =
  ΩT m k (rootW m k g w x)
    (Kfk k (λ η → Ψ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top))
    (psum m (λ n → Ψ m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (λ r → x (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) G.top))

ptsΩ k g V zero = pk G.top tt
ptsΩ k g V (suc n) =
  pk (plus k (co (ptsΩ k g V n)) (Ψ k (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (dfin k (g (co (ptsΩ k g V n)))) G.top))
     (plus-lgl k _ _ (lw (ptsΩ k g V n)) (Ψ-lgl k (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (dfin k (g (co (ptsΩ k g V n)))) G.top tt))

Ψ-cp m V x (inj₁ refl) = inj₁ refl
Ψ-cp m V x (inj₂ p) = inj₂ (Ψ-dn m V x _ p)

Ψ-dn m V x (G.suc d) p = 0 , Ψ-cp m V x p
Ψ-dn m V x (G.lim f) (n , p) = n , Ψ-cp m V x p
Ψ-dn m {k} V x (G.lc r g) p = ΨN-dn m k r (x r) _ _ (Ψ-cp m V x p)
Ψ-dn m (ws V) x {G.em _ a} (G.em _ d) (refl , p) = Ψ-dn m V _ d p
Ψ-dn m (wl V st) x {G.em n a} (G.em _ d) (refl , p) = Ψ-dn m (V n) _ d p
Ψ-dn m (wΩ V w) x {G.em (η , l) a} (G.em _ d) (refl , p) = Ψ-dn m (V η l) _ d p

Ψ-lgl m V x G.zero l = tt
Ψ-lgl m V x (G.suc a) l = succ-lgl m _ (Ψ-lgl m V x a l)
Ψ-lgl m V x (G.lim f) (st , lf) = (λ n → Ψ-cp m V x (st n)) , (λ n → Ψ-lgl m V x (f n) (lf n))
Ψ-lgl m {k} V x (G.lc r g) (lg , mo) = ΨN-lgl m k r (x r) _ _
  ((λ η l → Ψ-lgl m V x (g η) (lg η l)) , (λ η η′ l e l′ → Ψ-cp m V x (mo η η′ l e l′)))
  (λ η l → Ψ-lgl (lev k r) V (cmpw V r) (g η) (lg η l))
Ψ-lgl m (ws V) x (G.em _ a) l = Ψ-lgl m V _ a l
Ψ-lgl m (wl V st) x (G.em n a) l = Ψ-lgl m (V n) _ a l
Ψ-lgl m (wΩ V w) x (G.em (η , lη) a) l = Ψ-lgl m (V η lη) _ a l
Ψ-lgl m w0 x G.top l = succ-lgl m G.top tt
Ψ-lgl m {suc k} (ws V) x G.top l = Ψn-lgl m k (x (inj₁ tt)) _ _
  ((λ η l → Ψ-lgl m V _ η l) , (λ η η′ l e l′ → Ψ-cp m V _ e)) (λ η l → Ψ-lgl k V (self k) η l)
Ψ-lgl m (wl V st) x G.top l = psum-lgl m _ (λ n → Ψ-lgl m (V n) _ G.top tt)
Ψ-lgl m (wΩ {k} {g} V w) x G.top l = ΩT-lgl m k (rootW m k g w x) _ _
  (Kfk-br k _ (λ η → Ψ-lgl m (V (nrmk k η) (nrmk-lgl k η)) _ G.top tt))
  (psum-lgl m _ (λ n → Ψ-lgl m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) _ G.top tt))

------------------------------------------------------------------------
-- 见证的构造: 自表示 (只对零与后继), 沿 Ω̂ 的位置搬运 (要自表示的那一处可缺)

selfU : ∀ k → Maybe (Σ (Raw k) λ σ → Lgl k σ × up k σ ≡ k)
selfU zero = just (G.zero , tt , refl)
selfU (suc k) with selfU k
... | just (σ , l , e) = just (G.suc (G.em tt σ) , l , cong suc e)
... | nothing = nothing
selfU (lim f) = nothing
selfU (lc k g) = nothing

sxU : ∀ x (q : Pre x) → Maybe (Σ (Pre (upT x)) λ q′ → lev (upT x) q′ ≡ lev x q)
sxU (suc k) (inj₁ _) with selfU k
... | just (σ , l , e) = just ((G.suc σ , l , inj₁ tt) , e)
... | nothing = nothing
sxU (suc k) (inj₂ r) with sxU k r
... | just (q′ , e) = just ((G.top , tt , q′) , e)
... | nothing = nothing
sxU (lim f) (n , r) with sxU (f n) r
... | just (q′ , e) = just ((n , q′) , e)
... | nothing = nothing
sxU (lc k g) (η , l , r) with sxU (g η) r
... | just (q′ , e) = just ((η , l , q′) , e)
... | nothing = nothing

-- 后继层号 suc k 的 Ω̂ 的根见证: top 支 (读回 upT k) 里层号 k 的位置.
witU : ∀ k → Wit k (up k)
witU zero = at (inj₁ tt) refl
witU (suc j) with selfU j
... | just (σ , l , e) = at (G.suc (G.suc σ) , l , inj₁ tt) (cong suc e)
... | nothing = none
witU (lim f) = none
witU (lc k g) = none

witT : ∀ k (g : Raw k → LF) → Wit k g → Wit k (λ η → upT (g η))
witT k g none = none
witT k g (at ρ e) with sxU (g G.top) ρ
... | just (ρ′ , e′) = at ρ′ (trans e′ e)
... | nothing = none

lwN : ∀ y r (h : Lay.A (Lo y r) → LF) → (∀ η → Lay.lg (Lo y r) η → Lw (h η)) → Lw (upN y r h)
lwN (suc k) (inj₁ _) h W = wΩ W none
lwN (suc k) (inj₂ r) h W = lwN k r h W
lwN (lim f) (n , r) h W = lwN (f n) r h W
lwN (lc k g) (η , _ , r) h W = lwN (g η) r h W

Lw-Ω̂ : ∀ x → T.Legal x → Lw x → Lw (upT x)
lgl→Lw : ∀ y → T.Legal y → Lw y → ∀ a → Lgl y a → Lw (up y a)

Lw-Ω̂ zero L W = ws w0
Lw-Ω̂ (suc k) L (ws W) = wΩ (λ η l → lgl→Lw k L W η l) (witU k)
Lw-Ω̂ (lim f) (st , L) (wl W s) = wl (λ n → Lw-Ω̂ (f n) (L n) (W n)) (λ n → cps (T.Ω̂-CP (st n)))
Lw-Ω̂ (lc k g) (Lk , lg , mo) (wΩ W w) = wΩ (λ η l → Lw-Ω̂ (g η) (lg η l) (W η l)) (witT k g w)

lgl→Lw y L W G.zero l = w0
lgl→Lw y L W (G.suc a) l = ws (lgl→Lw y L W a l)
lgl→Lw y L W (G.lim f) (st , lf) = wl (λ n → lgl→Lw y L W (f n) (lf n)) (λ n → cps (T.cp→CP y (st n)))
lgl→Lw y L W (G.lc r h) (lg , mo) = lwN y r (λ η → up y (h η)) (λ η l → lgl→Lw y L W (h η) (lg η l))
lgl→Lw (suc k) L (ws W) (G.em _ a) l = lgl→Lw k L W a l
lgl→Lw (lim f) (st , L) (wl W s) (G.em n a) l = lgl→Lw (f n) (L n) (W n) a l
lgl→Lw (lc k g) (Lk , lg , mo) (wΩ W w) (G.em (η , lη) a) l = lgl→Lw (g η) (lg η lη) (W η lη) a l
lgl→Lw y L W G.top l = Lw-Ω̂ y L W

Lw-tw : ∀ n → Lw (tw n)
Lw-tw zero = w0
Lw-tw (suc n) = Lw-Ω̂ (tw n) (T.Legal-tw n) (Lw-tw n)

VΛ : Lw Λ
VΛ = wl Lw-tw (λ n → cps (T.tw-step n))

TΛ : R
TΛ = Ψ zero VΛ (λ _ → fold) G.top

TΛ-legal : Lgl zero TΛ
TΛ-legal = Ψ-lgl zero VΛ (λ _ → fold) G.top tt

-- 塔的各项与下一站 (Ω_{Ω+1} 的读法) 在同一套折叠里, 都合法无前提.
Tw : ℕ → R
Tw n = Ψ zero (Lw-tw n) (λ _ → fold) G.top

Tw-legal : ∀ n → Lgl zero (Tw n)
Tw-legal n = Ψ-lgl zero (Lw-tw n) (λ _ → fold) G.top tt

T⁺ʷ : R
T⁺ʷ = Ψ zero (ws (Lw-tw 2)) (λ _ → fold) G.top

T⁺ʷ-legal : Lgl zero T⁺ʷ
T⁺ʷ-legal = Ψ-lgl zero (ws (Lw-tw 2)) (λ _ → fold) G.top tt

TΛ-form : TΛ ≡ G.lim (psum zero Tw)
TΛ-form = refl
```
