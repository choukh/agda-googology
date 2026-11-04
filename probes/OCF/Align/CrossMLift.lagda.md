# 跨段 (六): 树上的上移算子

> 入口 [CrossM](CrossM.lagda.md). **判决: HOLDS (定义编译过, 无条件).** `CrossMUpTree` 的 `up-sim` 只说两边同值; 这里是树上的算子: 对一切 `e : M ⊂ M′`,
>
> - `↑ᴾ p k : A.Q p k φ χ → B.Q (u p) k φ (E χ)`
> - `↓ᴾ p k : B.Q (u p) k φ χ′ → A.Q p k φ (χ′ ∘ u)`
>
> $u=$ `up e`, $E\chi$ 把地板族延拓到 $M'$ (新高度上平凡). 对高度用 `Rec`, 对层号用路径, 对树结构, 三重递归; 两个算子互相调用, 因为节点的输入是反变的. 这是把 "节点绑定高度" 放进数据树时要用的算子: 折叠穿过这个节点时, 输出在高世界, 要拿回低世界. 只有定义; 还没有证明它和折叠交换.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdPos
open import OCF.Align.CrossMUp
module OCF.Align.CrossMLift {M M′ : Code} (e : M ⊂ M′) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import OCF.Free.Level using (Ordᴵ; _◃_; _◃₁_; zero; suc; self; lim; <→◃; ◃₁→◃)
open import OCF.Free.Floor using (Flr; fz; _⊔_; Ev)
open import OCF.Align.LadderOrdBase
import OCF.Align.LadderOrdTree

module A = OCF.Align.LadderOrdTree (HB M)
module B = OCF.Align.LadderOrdTree (HB M′)

H H′ : Set
H = Pos (cs M)
H′ = Pos (cs M′)

u : H → H′
u = up e

ε : ∀ {p q : H} → p <ᴾ q → u p <ᴾ u q
ε = up-mono e
```

## §1 地板族的延拓与限制

```agda
extT : Flr → (H → Flr) → ∀ i′ {n′} → Tri _<ᴾ_ i′ n′ → (n′ ≡ u end) → Flr
extT d χ i′ (tlt r) refl = χ (proj₁ (up-down e r))
extT d χ i′ (teq _) _ = χ end
extT d χ i′ (tgt _) _ = d

E : A.Fv → B.Fv
E χ i′ = extT fz χ i′ (<ᴾ-tri i′ (u end)) refl

res : B.Fv → A.Fv
res χ′ i = χ′ (u i)

ext-β : ∀ (χ : A.Fv) i → E χ (u i) ≡ χ i
ext-β χ i with <ᴾ-tri (u i) (u end)
... | tlt r = cong χ (sym (up-inj e (proj₁ (proj₂ (up-down e {y = u i} r)))))
... | teq d = cong χ (sym (up-inj e d))
... | tgt r = ⊥-elim (up-refl e {p = end} {q = i} r)

-- 三歧对齐
data Al : ∀ i n → Tri _<ᴾ_ i n → Tri _<ᴾ_ (u i) (u n) → Set where
  all : ∀ {i n} (l : i <ᴾ n) {l′} → Al i n (tlt l) (tlt l′)
  ale : ∀ {i} {d : u i ≡ u i} → Al i i (teq refl) (teq d)
  alg : ∀ {i n} (l : n <ᴾ i) {l′} → Al i n (tgt l) (tgt l′)

al : ∀ i n → Al i n (<ᴾ-tri i n) (<ᴾ-tri (u i) (u n))
al i n with <ᴾ-tri i n | <ᴾ-tri (u i) (u n)
... | tlt l | tlt l′ = all l
... | tlt l | teq d = ⊥-elim (no-self d (ε {i} {n} l))
... | tlt l | tgt l′ = ⊥-elim (irrᴾ {p = u i} (<ᴾ-trans (u i) (u n) (u i) (ε {i} {n} l) l′))
... | teq refl | teq d = ale
... | teq refl | tlt l′ = ⊥-elim (irrᴾ {p = u i} l′)
... | teq refl | tgt l′ = ⊥-elim (irrᴾ {p = u i} l′)
... | tgt l | tgt l′ = alg l
... | tgt l | teq d = ⊥-elim (no-self (sym d) (ε {n} {i} l))
... | tgt l | tlt l′ = ⊥-elim (irrᴾ {p = u n} (<ᴾ-trans (u n) (u i) (u n) (ε {n} {i} l) l′))

upd-res : ∀ (χ′ : B.Fv) n x i → B.upd χ′ (u n) x (u i) ≡ A.upd (res χ′) n x i
upd-res χ′ n x i = go (<ᴾ-tri i n) (<ᴾ-tri (u i) (u n)) (al i n)
  where
  go : ∀ {i n} (t : Tri _<ᴾ_ i n) (t′ : Tri _<ᴾ_ (u i) (u n)) → Al i n t t′ → B.updT χ′ x (u i) t′ ≡ A.updT (res χ′) x i t
  go _ _ (all l) = refl
  go _ _ ale = refl
  go _ _ (alg l) = refl

lo-res : ∀ (χ′ : B.Fv) n i → B.lo (u n) χ′ (u i) ≡ A.lo n (res χ′) i
lo-res χ′ n i = go (<ᴾ-tri i n) (<ᴾ-tri (u i) (u n)) (al i n)
  where
  go : ∀ {i n} (t : Tri _<ᴾ_ i n) (t′ : Tri _<ᴾ_ (u i) (u n)) → Al i n t t′ → B.loT χ′ (u i) t′ ≡ A.loT (res χ′) i t
  go _ _ (all l) = refl
  go _ _ ale = refl
  go _ _ (alg l) = refl

-- 一个新高度不是像
no-self′ : ∀ {i′ i} → i′ ≡ up e i → up e end <ᴾ i′ → ⊥
no-self′ {i = i} refl r = up-refl e {p = end} {q = i} r

via : ∀ {ℓ a b} → a ≡ b → Ev ℓ a → Ev ℓ b
via refl x = x

via⁻ : ∀ {ℓ a b} → a ≡ b → Ev ℓ b → Ev ℓ a
via⁻ refl x = x

-- 只看像的 Sub
SubU : ∀ {p} {a′ b′ : B.Fv} → (∀ i → i <ᴾ p → ∀ {ℓ} → Ev ℓ (a′ (u i)) → Ev ℓ (b′ (u i))) → B.Sub (u p) a′ b′
SubU {p} f i′ r x with up-down e {y = i′} {q = p} r
... | i , refl , l = f i l x

res-E : ∀ (χ : A.Fv) i → res (E χ) i ≡ χ i
res-E = ext-β

lo-at : ∀ {a b : A.Fv} n i → a i ≡ b i → A.lo n a i ≡ A.lo n b i
lo-at {a} {b} n i h with <ᴾ-tri i n
... | tlt _ = h
... | teq _ = refl
... | tgt _ = refl

-- ↑ 用到的三个转换
c↑-upd : ∀ {p} (χ : A.Fv) n x → B.Sub (u p) (B.upd (E χ) (u n) x) (E (A.upd χ n x))
c↑-upd {p} χ n x = SubU {p} λ i l y →
  via⁻ (ext-β (A.upd χ n x) i) (via (trans (upd-res (E χ) n x i) (A.upd-at n i (res-E χ i))) y)

c↑-lo : ∀ {p} (ζ′ : B.Fv) n (χ : A.Fv) → B.Sub (u p) (B.lo (u n) ζ′ B.∪ E χ) (E (A.lo n (res ζ′) A.∪ χ))
c↑-lo {p} ζ′ n χ = SubU {p} λ i l y →
  via⁻ (ext-β (A.lo n (res ζ′) A.∪ χ) i) (via (lo-res ζ′ n i) (proj₁ y) , via (ext-β χ i) (proj₂ y))

c↑-wk : ∀ {p} {a b : A.Fv} → A.Sub p a b → B.Sub (u p) (E a) (E b)
c↑-wk {p} {a} {b} s = SubU {p} λ i l y → via⁻ (ext-β b i) (s i l (via (ext-β a i) y))

-- ↓ 用到的三个转换
c↓-upd : ∀ {p} (χ′ : B.Fv) n x → A.Sub p (A.upd (res χ′) n x) (res (B.upd χ′ (u n) x))
c↓-upd χ′ n x i l y = via⁻ (upd-res χ′ n x i) y

c↓-lo : ∀ {p} (ζ : A.Fv) n (χ′ : B.Fv) → A.Sub p (A.lo n ζ A.∪ res χ′) (res (B.lo (u n) (E ζ) B.∪ χ′))
c↓-lo ζ n χ′ i l y = via⁻ (trans (lo-res (E ζ) n i) (lo-at n i (res-E ζ i))) (proj₁ y) , proj₂ y
```

## §2 算子

```agda
LiftAt : H → Set
LiftAt p = ∀ k → (∀ {φ χ} → A.Q p k φ χ → B.Q (u p) k φ (E χ)) × (∀ {φ χ′} → B.Q (u p) k φ χ′ → A.Q p k φ (res χ′))

module At (p : H) (I : ∀ {n} → n <ᴾ p → LiftAt n) where
  ↑Q : ∀ α {φ χ} → A.Q p α φ χ → B.Q (u p) α φ (E χ)
  ↓Q : ∀ α {φ χ′} → B.Q (u p) α φ χ′ → A.Q p α φ (res χ′)
  ↑U : ∀ α {k} (r : k ◃ α) {φ χ} → A.Q p k φ χ → B.Q (u p) k φ (E χ)
  ↓U : ∀ α {k} (r : k ◃ α) {φ χ′} → B.Q (u p) k φ χ′ → A.Q p k φ (res χ′)

  ↑U (suc k) zero x = ↑Q k x
  ↑U (suc c) (suc r) x = ↑U c r x
  ↑U (lim f s) (self n) x = ↑Q (f n) x
  ↑U (lim f s) (lim n r) x = ↑U (f n) r x
  ↓U (suc k) zero x = ↓Q k x
  ↓U (suc c) (suc r) x = ↓U c r x
  ↓U (lim f s) (self n) x = ↓Q (f n) x
  ↓U (lim f s) (lim n r) x = ↓U (f n) r x

  ↑Q α A.q0 = B.q0
  ↑Q α (A.qs a) = B.qs (↑Q α a)
  ↑Q α (A.ql F) = B.ql (λ i → ↑Q α (F i))
  ↑Q α (A.qi ac f) = B.qi ac (λ x → ↑Q α (f x))
  ↑Q α (A.qŝ c₀ t g) = B.qŝ c₀ (↑Q α t) (λ η d → ↑Q α (g η d))
  ↑Q α (A.qĉ c₀ z zg o₀ o) = B.qĉ c₀ z zg (↑Q α o₀) (λ η d → ↑Q α (o η d))
  ↑Q α (A.qclo t g) = B.qclo (↑Q α t) (λ η → ↑Q α (g η))
  ↑Q α {χ = χ} (A.qcl {n = n} q ψ s t g) =
    B.qcl (ε {n} {p} q) ψ (λ y → s (via (ext-β χ n) y)) (↑Q α t) (λ η → B.qwk (λ y → y) (c↑-upd {p} χ n _) (↑Q α (g η)))
  ↑Q α (A.qwk le lc t) = B.qwk le (c↑-wk {p} lc) (↑Q α t)
  ↑Q α {χ = χ} (A.qΩ↓ {n = n} {k = k} q fe ac h) =
    B.qΩ↓ (ε {n} {p} q) fe (λ y → ac (via (ext-β χ n) y))
      (λ ξ ζ′ z′ → B.qwk (λ y → y) (c↑-lo {p} ζ′ n χ) (↑Q α (h ξ (res ζ′) (A.intoV q (proj₂ (I q k) (B.outV (ε {n} {p} q) z′))))))
  ↑Q α {χ = χ} (A.qΩ fe r h) =
    B.qΩ fe r (λ ξ ζ′ z′ → B.qwk (λ y → y) (c↑-lo {p} ζ′ p χ) (↑Q α (h ξ (res ζ′) (A.intoU (<→◃ r) (↓U α (<→◃ r) (B.outU (<→◃ r) z′))))))
  ↑Q α (A.omk r z x) = B.omk r (B.intoU (◃₁→◃ r) (↑U α (◃₁→◃ r) (A.outU (◃₁→◃ r) z))) (↑Q α x)

  ↓Q α B.q0 = A.q0
  ↓Q α (B.qs a) = A.qs (↓Q α a)
  ↓Q α (B.ql F) = A.ql (λ i → ↓Q α (F i))
  ↓Q α (B.qi ac f) = A.qi ac (λ x → ↓Q α (f x))
  ↓Q α (B.qŝ c₀ t g) = A.qŝ c₀ (↓Q α t) (λ η d → ↓Q α (g η d))
  ↓Q α (B.qĉ c₀ z zg o₀ o) = A.qĉ c₀ z zg (↓Q α o₀) (λ η d → ↓Q α (o η d))
  ↓Q α (B.qclo t g) = A.qclo (↓Q α t) (λ η → ↓Q α (g η))
  ↓Q α {χ′ = χ′} (B.qcl {n = n′} q′ ψ s t g) with up-down e {y = n′} {q = p} q′
  ... | n , refl , l = A.qcl l ψ s (↓Q α t) (λ η → A.qwk (λ y → y) (c↓-upd {p} χ′ n _) (↓Q α (g η)))
  ↓Q α (B.qwk le lc t) = A.qwk le (λ i l y → lc (u i) (ε {i} {p} l) y) (↓Q α t)
  ↓Q α {χ′ = χ′} (B.qΩ↓ {n = n′} {k = k} q′ fe ac h) with up-down e {y = n′} {q = p} q′
  ... | n , refl , l = A.qΩ↓ l fe ac
      (λ ξ ζ z → A.qwk (λ y → y) (c↓-lo {p} ζ n χ′) (↓Q α (h ξ (E ζ) (B.intoV q′ (proj₁ (I l k) (A.outV l z))))))
  ↓Q α {χ′ = χ′} (B.qΩ fe r h) =
    A.qΩ fe r (λ ξ ζ z → A.qwk (λ y → y) (c↓-lo {p} ζ p χ′) (↓Q α (h ξ (E ζ) (B.intoU (<→◃ r) (↑U α (<→◃ r) (A.outU (<→◃ r) z))))))
  ↓Q α (B.omk r z x) = A.omk r (A.intoU (◃₁→◃ r) (↓U α (◃₁→◃ r) (B.outU (◃₁→◃ r) z))) (↓Q α x)

FL : ∀ p → (∀ {n} → n <ᴾ p → LiftAt n) → LiftAt p
FL p I k = At.↑Q p I k , At.↓Q p I k

Lift : ∀ p → LiftAt p
Lift p = FL p (A.Rec LiftAt FL p)

↑ᴾ : ∀ p k {φ χ} → A.Q p k φ χ → B.Q (u p) k φ (E χ)
↑ᴾ p k = proj₁ (Lift p k)

↓ᴾ : ∀ p k {φ χ′} → B.Q (u p) k φ χ′ → A.Q p k φ (res χ′)
↓ᴾ p k = proj₂ (Lift p k)
```
