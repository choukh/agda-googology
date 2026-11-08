# 原第一层 Int 的统一关系保持

沿同一 A 路径作 Cut₀/IW₀ 归纳；历史后缀分别携带，不使用函数外延。
本文件继承旧 IntM 的双递归机制，不复制其跨 A 不同路径的比较系统。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCtxBuild where
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (D₁)
open import OCF.Align.EventReturnCoordIf
open import OCF.Align.EventReturnCtxIf

module Cuts {a H H′}
  (v : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H))
  (v′ : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H′))
  (h : ∀ {c} (p : a ⊲ c) lc → R₁ c H H′ (v p lc) (v′ p lc)) where
  cut : ∀ b {c} (p : c ⊲ b) (ab : a ⊲ c) (lb : Lg b)
    {w J J′} (bw : b ⊲ w) (s : Suf H J) (s′ : Suf H′ J′) →
    R₁ w J J′ (Cut₀ v b p ab lb bw s) (Cut₀ v′ b p ab lb bw s′)
  cut b C.self ab lb bw s s′ = rz
  cut (asuc b) (C.suc p) ab lb bw s s′ =
    ra (cut b p ab lb (⊲-tr (C.suc C.self) bw) s s′)
       (rw (⊲-tr (C.suc C.self) bw) s s′ (h (⊲-tr ab p) lb))
  cut (alim f) (C.lim n p) ab (st , ls) bw s s′ =
    ra (cut (f n) p ab (ls n) (⊲-tr (C.lim n C.self) bw) s s′)
       (rl (λ m → cut (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m))
          (ls (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bw) s s′))

Z₀ : Set
Z₀ = ∀ κ → ZE κ hz → ZE κ (hs hz)
M₀ : Wε → Set
M₀ W = ∀ {V j} → W ≤ V → StH V j hz → StH V j (hs hz)

inner : ∀ {U U′ a H H′} (ac ac′ : AccY hz) {x : D₀ U} {y : D₀ U′} → E₀ x y →
  (q : U ≤ (a , H)) (q′ : U′ ≤ (a , H′)) (la : Lg a)
  (ze ze′ : Z₀) (mk : M₀ (a , H)) (mk′ : M₀ (a , H′))
  {u : ∀ {V} → (a , H) ≤ V → LgWε V → D₀ V → D₁ V}
  {v : ∀ {V} → (a , H′) ≤ V → LgWε V → D₀ V → D₁ V} →
  (∀ {z z′} → E₀ z z′ → R₁ a H H′ (u ≤rf (la , tt) z) (v ≤rf (la , tt) z′)) →
  ∀ {w w′} → E₀ w w′ →
  R₁ a H H′ (Int ac x q (la , tt) tt ze mk u w) (Int ac′ y q′ (la , tt) tt ze′ mk′ v w′)
inner ac ac′ ez q q′ la ze ze′ mk mk′ hu hw = rz
inner ac ac′ eo q q′ la ze ze′ mk mk′ hu hw = hu hw
inner ac ac′ (ea p r) q q′ la ze ze′ mk mk′ hu hw =
  ra (inner ac ac′ p q q′ la ze ze′ mk mk′ hu hw)
     (inner ac ac′ r q q′ la ze ze′ mk mk′ hu (ea hw (ewL q (ewR q′ p))))
inner ac ac′ (el {f = f} {g = g} p) q q′ la ze ze′ mk mk′ hu hw =
  rl (λ n → inner ac ac′ (p n) q q′ la ze ze′ mk mk′ hu (ea hw (pre n)))
  where
  pre : ∀ n → E₀ (Pre q f n) (Pre q′ g n)
  pre zero = ez
  pre (suc n) = ea (pre n) (ewL q (ewR q′ (p n)))
inner ac ac′ (ewL p h) q q′ la ze ze′ mk mk′ hu hw = inner ac ac′ h (≤tr p q) q′ la ze ze′ mk mk′ hu hw
inner ac ac′ (ewR p h) q q′ la ze ze′ mk mk′ hu hw = inner ac ac′ h q (≤tr p q′) la ze ze′ mk mk′ hu hw

mk-one : ∀ {W V} (mk : Mk₁ W) (p : W ≤ V) → mk p (ss hself) ≡ ss hself
mk-one mk p with mk p (ss hself)
... | ss hself = refl
```

```agda
module Walk {a b H H′ J J′} (ac ac′ : AccY (hs hz))
  (v : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H))
  (v′ : ∀ {c} → a ⊲ c → Lg c → D₁ (c , H′))
  (h : ∀ {c} (p : a ⊲ c) lc → R₁ c H H′ (v p lc) (v′ p lc))
  (s : Suf H J) (s′ : Suf H′ J′) (lb : Lg b)
  (mk : Mk₁ (b , J)) (mk′ : Mk₁ (b , J′))
  (u : ∀ {V} → (b , J) ≤ V → LgWε V → D₁ V → D₁ V)
  (u′ : ∀ {V} → (b , J′) ≤ V → LgWε V → D₁ V → D₁ V)
  (ih : ∀ {c} (p : a ⊲ c) lc (q : c ⊲ b) {w w′} → R₁ b J J′ w w′ →
    R₁ b J J′ (Int ac (v p lc) (q , s) (lb , tt) tt (λ _ z → z) mk u w)
                (Int ac′ (v′ p lc) (q , s′) (lb , tt) tt (λ _ z → z) mk′ u′ w′)) where
  walk : ∀ d {c} (p : c ⊲ d) (ap : a ⊲ c) (ld : Lg d) (db : d ⊲ b) {w w′} → R₁ b J J′ w w′ →
    R₁ b J J′ (IW₀ ac v d p ap ld db s (lb , tt) tt (λ _ z → z) mk u w)
                (IW₀ ac′ v′ d p ap ld db s′ (lb , tt) tt (λ _ z → z) mk′ u′ w′)
  walk d C.self ap ld db hw = rz
  walk (asuc d) (C.suc p) ap ld db hw =
    ra (walk d p ap ld (⊲-tr (C.suc C.self) db) hw)
       (ih (⊲-tr ap p) ld (⊲-tr (C.suc C.self) db)
         (ra hw (Cuts.cut v v′ h d p ap ld (⊲-tr (C.suc C.self) db) s s′)))
  walk (alim f) (C.lim n p) ap (st , ls) db hw =
    ra (walk (f n) p ap (ls n) (⊲-tr (C.lim n C.self) db) hw)
       (rl (λ m → walk (f (suc (m + n))) (st (m + n)) (⊲-tr ap (tailP f st p m))
          (ls (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) db)
          (ra hw (Cuts.cut v v′ h (f (m + n)) (tailP f st p m) ap (ls (m + n))
                    (⊲-tr (C.lim (m + n) C.self) db) s s′))))

preserve : ∀ {a b H H′ J J′} (ac ac′ : AccY (hs hz))
  {x : D₁ (a , H)} {y : D₁ (a , H′)} → R₁ a H H′ x y →
  (p : a ⊲ b) (s : Suf H J) (s′ : Suf H′ J′) (lb : Lg b)
  (mk : Mk₁ (b , J)) (mk′ : Mk₁ (b , J′))
  {u : ∀ {V} → (b , J) ≤ V → LgWε V → D₁ V → D₁ V}
  {v : ∀ {V} → (b , J′) ≤ V → LgWε V → D₁ V → D₁ V} → UH u v →
  ∀ {w w′} → R₁ b J J′ w w′ →
  R₁ b J J′ (Int ac x (p , s) (lb , tt) tt (λ _ z → z) mk u w)
              (Int ac′ y (p , s′) (lb , tt) tt (λ _ z → z) mk′ v w′)
preserve ac ac′ rz p s s′ lb mk mk′ hu hw = rz
preserve ac ac′ ro p s s′ lb mk mk′ hu hw = hu C.self here here lb hw
preserve ac ac′ (ra hx hy) p s s′ lb mk mk′ hu hw =
  ra (preserve ac ac′ hx p s s′ lb mk mk′ hu hw)
     (preserve ac ac′ hy p s s′ lb mk mk′ hu (ra hw (rw p s s′ hx)))
preserve ac ac′ (rl {f = f} {g = g} h) p s s′ lb mk mk′ hu hw =
  rl (λ n → preserve ac ac′ (h n) p s s′ lb mk mk′ hu (ra hw (pre n)))
  where
  pre : ∀ n → R₁ _ _ _ (Pre (p , s) f n) (Pre (p , s′) g n)
  pre zero = rz
  pre (suc n) = ra (pre n) (rw p s s′ (h n))
preserve ac ac′ (rw q t t′ h) p s s′ lb mk mk′ hu hw =
  preserve ac ac′ h (⊲-tr q p) (suf-tr t s) (suf-tr t′ s′) lb mk mk′ hu hw
preserve (acc g) (acc g′) (ri h) p s s′ lb mk mk′ hu hw
  rewrite mk-one mk ≤rf | mk-one mk′ ≤rf =
  ri (λ q t t′ lc hc →
    preserve (acc g) (acc g′) (h (⊲-tr p q) (suf-tr s t) (suf-tr s′ t′) lc hc)
      C.self here here lc (λ q′ → mk (≤tr (q , t) q′)) (λ q′ → mk′ (≤tr (q , t′) q′))
      (λ q′ t₂ t₂′ ld r → hu (⊲-tr q q′) (suf-tr t t₂) (suf-tr t′ t₂′) ld r)
      (ra (rw q t t′ hw)
          (inner (g (ss hself)) (g′ (ss hself)) hc ≤rf ≤rf lc _ _ _ _
            (λ he → h (⊲-tr (⊲-tr p q) C.self) (suf-tr (suf-tr s t) here) (suf-tr (suf-tr s′ t′) here) lc he) ez)))
preserve ac ac′ (rk {u = v} {v = v′} h) p s s′ lb mk mk′ {u} {v = u′} hu hw =
  ra (Walk.walk ac ac′ v v′ h s s′ lb mk mk′ u u′
        (λ q lc qb hr → preserve ac ac′ (h q lc) qb s s′ lb mk mk′ hu hr)
        _ p C.self lb C.self hw)
     (rk (λ q lc →
       preserve ac ac′ (h (⊲-tr p q) lc) C.self s s′ lc
         (λ q′ → mk (≤tr (q , here) q′)) (λ q′ → mk′ (≤tr (q , here) q′))
         (λ q′ t t′ ld r → hu (⊲-tr q q′) (suf-tr here t) (suf-tr here t′) ld r)
         (ra (rw q here here hw) (Cuts.cut v v′ h _ (⊲-tr p q) C.self lc C.self s s′))))

actual : Internal
actual = record { preserve = preserve }
```
