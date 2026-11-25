# YiOmFold 第 B 站的第二种行：归一坐标上的保留行

**判决 (编译定理)：保留模式下 `top` 的一行 `topᴺ`，没有前提，合法，分支里是分支槽位上的保留结点：第 `suc a` 支的头是层号 `read0 (nrm a)` 的结点 (`norm-keep`)，
`a` 不含极限时就是层号 `read0 a` (`norm-keep-fin`)。与本该有的行差两处：槽位取在归一坐标 `suc (nrm a)` 的那一支 (它的守卫由树算出)；各支沿坐标的路径累加 (`Gκ`)。**
它的输出不在 `Dom⁰` 里 (`norm-not-dom`)，所以闭项 [YiOmFoldTop](YiOmFoldTop.lagda.md) 没有用它；没有值定理。前提的类型在 [YiOmFoldGap](YiOmFoldGap.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmFoldNorm where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested; cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; read0)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (Plain; lev; Kept)
open import OCF.Align.YiLvFoldAdd using (Pos)
open import OCF.Align.YiLvNegCum using (psum; psum-legal; weak)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold
open import OCF.Align.YiOmFoldGap using (Branches; RowLegal; row; row-legal; row-nested)
```

## 1 归一坐标：守卫由树算出

`nrm` 是 `YiLvNegCum.cum` 把第 0 层的 `top` 送到零：极限换成部分和，所以不要证书就合法。
`Sp X`：`X` 的每个极限的第 1 项是后继。归一的输出都是这样的，于是 `1 ⊲ suc (nrm a)` 有闭的路径，`suc (nrm a)` 是 `tw 3` 的带相关守卫的坐标。

```agda
nrm : R → R
nrm G.zero = G.zero
nrm (G.suc a) = G.suc (nrm a)
nrm (G.lim f) = G.lim (psum (λ n → nrm (f n)))
nrm G.top = G.zero

nrm-legal : ∀ a → Lgl zero (nrm a)
nrm-legal G.zero = tt
nrm-legal (G.suc a) = nrm-legal a
nrm-legal (G.lim f) =
  (λ n → weak (psum (λ k → nrm (f k)) n) (G.suc (nrm (f (suc n))))) ,
  psum-legal (λ k → nrm (f k)) (λ k → nrm-legal (f k))
nrm-legal G.top = tt

data Sp : R → Set where
  sz : Sp G.zero
  ss : ∀ {X} → Sp X → Sp (G.suc X)
  sl : ∀ {h Z} → h 1 ≡ G.suc Z → Sp Z → Sp (G.lim h)

sp-add : ∀ {x y} → Sp x → Sp y → Sp (x +ʳ y)
sp-add sx sz = sx
sp-add sx (ss sy) = ss (sp-add sx sy)
sp-add {x} sx (sl eq sy) = sl (cong (x +ʳ_) eq) (sp-add sx sy)

sp-nrm : ∀ a → Sp (nrm a)
sp-nrm G.zero = sz
sp-nrm (G.suc a) = ss (sp-nrm a)
sp-nrm (G.lim f) = sl refl (sp-add (sp-nrm (f 0)) (sp-nrm (f 1)))
sp-nrm G.top = sz

one≤suc : ∀ {X} → Sp X → Cp zero one (G.suc X)
one≤suc sz = inj₁ refl
one≤suc (ss s) = inj₂ (one≤suc s)
one≤suc (sl eq s) = inj₂ (inj₂ (1 , subst (Cp zero one) (sym eq) (one≤suc s)))

γ : ∀ a → Gd zero raw1 (G.suc (nrm a))
γ a = one≤suc (sp-nrm a) , nrm-legal a , raw0-Nested (G.suc (nrm a))

LimFree : R → Set
LimFree G.zero = ⊤
LimFree (G.suc a) = LimFree a
LimFree (G.lim f) = ⊥
LimFree G.top = ⊥

nrm-id : ∀ a → LimFree a → nrm a ≡ a
nrm-id G.zero h = refl
nrm-id (G.suc a) h = cong G.suc (nrm-id a h)
```

## 2 一支里的保留折叠

`keepAll k ν`：把 `Raw k` 的树折进 `tw 2`，目标是 `tw 2` 自己，一律保留，`ν` 是 "在 `k` 的位置 `r` 对应的槽位上造结点"。行照 `YiRawFold.Ψ` 在 `mix` 之下保留时的行：
零给 `top`，后继给 ω 倍，`top` 在后继层号上展开成根槽位的结点，在极限层号上取各支的部分和。没有链，所以不读 `Legal k`。

```agda
Nod : LF → Set
Nod k = (r : Pre k) (c : Low k r) → RΩ → ((ζ : Low k r) → .(GdL k r c ζ) → RΩ) → RΩ

nS : ∀ {k} → Nod (suc k) → Nod k
nS ν r = ν (inj₂ r)

nL : ∀ {f} → Nod (lim f) → ∀ n → Nod (f n)
nL ν n r = ν (n , r)

record NodLaw {k} (ν : Nod k) : Set where
  field
    dnN : ∀ {a} r c t g → Cp K₂ω a t → Dn K₂ω a (ν r c t g)
    lgN : ∀ r c t g →
      (∀ ζ (e : GdL k r c ζ) → Cp K₂ω t (g ζ e)) →
      (∀ ζ (e : GdL k r c ζ) ζ′ (e′ : GdL k r c ζ′) → GdL k r ζ ζ′ → Cp K₂ω (g ζ e) (g ζ′ e′)) →
      Lgl K₂ω t → (∀ ζ (e : GdL k r c ζ) → Lgl K₂ω (g ζ e)) → Lgl K₂ω (ν r c t g)
    nsN : ∀ r c t g → LglLow k r c → NestedLow k r c → Nested K₂ω t →
      (∀ ζ (e : GdL k r c ζ) → Nested K₂ω (g ζ e)) → Nested K₂ω (ν r c t g)
    psN : ∀ r c t g → Pos K₂ω (ν r c t g)
open NodLaw

lawS : ∀ {k} {ν : Nod (suc k)} → NodLaw ν → NodLaw (nS ν)
lawS H = record
  { dnN = λ r → dnN H (inj₂ r); lgN = λ r → lgN H (inj₂ r); nsN = λ r → nsN H (inj₂ r)
  ; psN = λ r → psN H (inj₂ r) }

lawL : ∀ {f} {ν : Nod (lim f)} → NodLaw ν → ∀ n → NodLaw (nL ν n)
lawL H n = record
  { dnN = λ r → dnN H (n , r); lgN = λ r → lgN H (n , r); nsN = λ r → nsN H (n , r)
  ; psN = λ r → psN H (n , r) }

psumΩ : (ℕ → RΩ) → ℕ → RΩ
psumΩ g zero = g zero
psumΩ g (suc n) = plusΩ (psumΩ g n) (g (suc n))

psumΩ-legal : ∀ g → (∀ n → Lgl K₂ω (g n)) → ∀ n → Lgl K₂ω (psumΩ g n)
psumΩ-legal g lg zero = lg zero
psumΩ-legal g lg (suc n) = plus-lgl (psumΩ g n) (g (suc n)) (psumΩ-legal g lg n) (lg (suc n))

psumΩ-nested : ∀ g → (∀ n → Nested K₂ω (g n)) → ∀ n → Nested K₂ω (psumΩ g n)
psumΩ-nested g ng zero = ng zero
psumΩ-nested g ng (suc n) =
  plus-ns (psumΩ g n) (g (suc n)) (psumΩ-nested g ng n) (ng (suc n))

keepAll : ∀ k → Nod k → Raw k → RΩ
keepAll k ν G.zero = G.top
keepAll k ν (G.suc a) = successorΩ (keepAll k ν a)
keepAll k ν (G.lim f) = G.lim (λ n → keepAll k ν (f n))
keepAll k ν (G.lc r c t g) = ν r c (keepAll k ν t) (λ ζ e → keepAll k ν (g ζ e))
keepAll (suc k) ν (G.em _ a) = keepAll k (nS ν) a
keepAll (lim f) ν (G.em n a) = keepAll (f n) (nL ν n) a
keepAll (lc k c w b t g) ν (G.em i a) = G.top
keepAll zero ν G.top = successorΩ G.top
keepAll (suc k) ν G.top =
  ν (inj₁ tt) (cO k) (keepAll k (nS ν) (cO k)) (λ ζ e → keepAll k (nS ν) ζ)
keepAll (lim f) ν G.top = G.lim (psumΩ (λ n → keepAll (f n) (nL ν n) G.top))
keepAll (lc k c w b t g) ν G.top = G.top

KA-cp : ∀ k → Plain k → (ν : Nod k) → NodLaw ν → ∀ {a b} →
  Cp k a b → Cp K₂ω (keepAll k ν a) (keepAll k ν b)
KA-dn : ∀ k → Plain k → (ν : Nod k) → NodLaw ν → ∀ {a} b →
  Dn k a b → Dn K₂ω (keepAll k ν a) (keepAll k ν b)
KA-top : ∀ k → Plain k → (ν : Nod k) → NodLaw ν → ∀ {a} →
  Cp k a G.top → Cp K₂ω (keepAll k ν a) (keepAll k ν (cO k))

KA-cp k pl ν H (inj₁ refl) = inj₁ refl
KA-cp k pl ν H {b = b} (inj₂ p) = inj₂ (KA-dn k pl ν H b p)

KA-dn k pl ν H (G.suc b) p = zero , KA-cp k pl ν H p
KA-dn k pl ν H (G.lim f) (n , p) = n , KA-cp k pl ν H p
KA-dn k pl ν H (G.lc r c t g) p = dnN H r c _ _ (KA-cp k pl ν H p)
KA-dn (suc k) pl ν H {G.em _ a} (G.em _ T) p = KA-dn k pl (nS ν) (lawS H) T p
KA-dn (lim f) pl ν H {G.em n a} (G.em .n T) (refl , p) =
  KA-dn (f n) (pl n) (nL ν n) (lawL H n) T p
KA-dn (suc k) pl ν H {G.em _ a} G.top p =
  dnN H (inj₁ tt) (cO k) _ _ (KA-top k pl (nS ν) (lawS H) p)

KA-top zero pl ν H (inj₁ refl) = inj₁ refl
KA-top (suc k) pl ν H p = KA-cp (suc k) pl ν H p
KA-top (lim f) pl ν H p = KA-cp (lim f) pl ν H p

KA-pos : ∀ k → Plain k → (ν : Nod k) → NodLaw ν → ∀ ξ → Pos K₂ω (keepAll k ν ξ)
KA-pos k pl ν H G.zero = tt
KA-pos k pl ν H (G.suc a) = tt
KA-pos k pl ν H (G.lim f) = tt
KA-pos k pl ν H (G.lc r c t g) = psN H r c _ _
KA-pos (suc k) pl ν H (G.em _ a) = KA-pos k pl (nS ν) (lawS H) a
KA-pos (lim f) pl ν H (G.em n a) = KA-pos (f n) (pl n) (nL ν n) (lawL H n) a
KA-pos zero pl ν H G.top = tt
KA-pos (suc k) pl ν H G.top = psN H (inj₁ tt) (cO k) _ _
KA-pos (lim f) pl ν H G.top = tt

KA-legal : ∀ k → Plain k → (ν : Nod k) → NodLaw ν → ∀ ξ → Lgl k ξ → Lgl K₂ω (keepAll k ν ξ)
KA-legal k pl ν H G.zero l = tt
KA-legal k pl ν H (G.suc a) l =
  copiesΩ-step (keepAll k ν a) , copiesΩ-legal (keepAll k ν a) (KA-legal k pl ν H a l)
KA-legal k pl ν H (G.lim f) (st , lf) =
  (λ n → KA-cp k pl ν H (st n)) , (λ n → KA-legal k pl ν H (f n) (lf n))
KA-legal k pl ν H (G.lc r c t g) (tg , dir , irr , lt , lg) =
  lgN H r c _ _
    (λ ζ e → KA-cp k pl ν H (tg ζ e))
    (λ ζ e ζ′ e′ q → KA-cp k pl ν H (dir ζ e ζ′ e′ q))
    (KA-legal k pl ν H t lt)
    (λ ζ e → KA-legal k pl ν H (g ζ e) (lg ζ e))
KA-legal (suc k) pl ν H (G.em _ a) l = KA-legal k pl (nS ν) (lawS H) a l
KA-legal (lim f) pl ν H (G.em n a) l = KA-legal (f n) (pl n) (nL ν n) (lawL H n) a l
KA-legal zero pl ν H G.top l = copiesΩ-step G.top , copiesΩ-legal G.top tt
KA-legal (suc k) pl ν H G.top l =
  lgN H (inj₁ tt) (cO k) _ _
    (λ ζ e → KA-cp k pl (nS ν) (lawS H) (proj₁ e))
    (λ ζ e ζ′ e′ q → KA-cp k pl (nS ν) (lawS H) (proj₁ q))
    (KA-legal k pl (nS ν) (lawS H) (cO k) (cO-Lgl k))
    (λ ζ e → KA-legal k pl (nS ν) (lawS H) ζ (proj₁ (proj₂ e)))
KA-legal (lim f) pl ν H G.top l =
  (λ n → plus-weak (psumΩ (λ m → keepAll (f m) (nL ν m) G.top) n)
    (keepAll (f (suc n)) (nL ν (suc n)) G.top)) ,
  psumΩ-legal (λ n → keepAll (f n) (nL ν n) G.top)
    (λ n → KA-legal (f n) (pl n) (nL ν n) (lawL H n) G.top tt)

KA-nested : ∀ k → Plain k → (ν : Nod k) → NodLaw ν → ∀ ξ → Nested k ξ →
  Nested K₂ω (keepAll k ν ξ)
KA-nested k pl ν H G.zero nb = tt
KA-nested k pl ν H (G.suc a) nb =
  copiesΩ-nested (keepAll k ν a) (KA-nested k pl ν H a nb)
KA-nested k pl ν H (G.lim f) nb = λ n → KA-nested k pl ν H (f n) (nb n)
KA-nested k pl ν H (G.lc r c t g) (l , nl , nt , ng) =
  nsN H r c _ _ l nl (KA-nested k pl ν H t nt) (λ ζ e → KA-nested k pl ν H (g ζ e) (ng ζ e))
KA-nested (suc k) pl ν H (G.em _ a) nb = KA-nested k pl (nS ν) (lawS H) a nb
KA-nested (lim f) pl ν H (G.em n a) nb = KA-nested (f n) (pl n) (nL ν n) (lawL H n) a nb
KA-nested zero pl ν H G.top nb = copiesΩ-nested G.top tt
KA-nested (suc k) pl ν H G.top nb =
  nsN H (inj₁ tt) (cO k) _ _ (cO-Lgl k) (cO-Nested k)
    (KA-nested k pl (nS ν) (lawS H) (cO k) (cO-Nested k))
    (λ ζ e → KA-nested k pl (nS ν) (lawS H) ζ (proj₂ (proj₂ e)))
KA-nested (lim f) pl ν H G.top nb =
  psumΩ-nested (λ n → keepAll (f n) (nL ν n) G.top)
    (λ n → KA-nested (f n) (pl n) (nL ν n) (lawL H n) G.top tt)
```

## 3 第 `η` 支的槽位，与归一坐标那一支的 `top`

```agda
νᴮ : ∀ η → Gd zero raw1 η → Nod (read0 η)
νᴮ η e r = G.lc (br η e r)

lawᴮ : ∀ η (e : Gd zero raw1 η) → NodLaw (νᴮ η e)
lawᴮ η e = record
  { dnN = λ r c t g p → p
  ; lgN = λ r c t g tg dir lt lg → tg , dir , (λ ζ e₁ e₂ → refl) , lt , lg
  ; nsN = λ r c t g l nl nt ng → l , nl , nt , ng
  ; psN = λ r c t g → tt }

-- 坐标 suc (nrm a) 那一支的 top 的保留折叠: 根槽位上层号 read0 (nrm a) 的结点.
KT : R → RΩ
KT a = keepAll (suc (read0 (nrm a))) (νᴮ (G.suc (nrm a)) (γ a)) G.top

KT-legal : ∀ a → Lgl K₂ω (KT a)
KT-legal a = KA-legal (suc (read0 (nrm a))) (rplain (nrm a))
  (νᴮ (G.suc (nrm a)) (γ a)) (lawᴮ (G.suc (nrm a)) (γ a)) G.top tt

KT-nested : ∀ a → Nested K₂ω (KT a)
KT-nested a = KA-nested (suc (read0 (nrm a))) (rplain (nrm a))
  (νᴮ (G.suc (nrm a)) (γ a)) (lawᴮ (G.suc (nrm a)) (γ a)) G.top tt

KT-kept : ∀ a → Kept K₂ω (read0 (nrm a)) (KT a)
KT-kept a = br (G.suc (nrm a)) (γ a) (inj₁ tt) , refl , cO (read0 (nrm a)) , _ , _ , refl
```

## 4 分支族与行

各支的保留结点落在各自的槽位上，相互不是第一位置 (`YiOmFoldGap.moved-undirected`)。所以分支族对坐标递归，沿路径累加：
`Gκ (suc a) = Gκ a + KT a`，极限逐项；它不看守卫，对坐标的第一位置单调。这与极限层号上 `top` 取部分和 (`YiRawFoldBase.psum`) 是同一个办法。

```agda
Gκ : R → RΩ
Gκ G.zero = t₀
Gκ (G.suc a) = plusΩ (Gκ a) (KT a)
Gκ (G.lim f) = G.lim (λ n → Gκ (f n))
Gκ G.top = t₀

Gκ-first : ∀ η → Cp K₂ω t₀ (Gκ η)
Gκ-first G.zero = inj₁ refl
Gκ-first (G.suc a) = Cp-tr K₂ω (Gκ-first a) (plus-weak (Gκ a) (KT a))
Gκ-first (G.lim f) = inj₂ (zero , Gκ-first (f zero))
Gκ-first G.top = inj₁ refl

Gκ-cp : ∀ {η} η′ → Cp zero η η′ → Cp K₂ω (Gκ η) (Gκ η′)
Gκ-cp η′ (inj₁ refl) = inj₁ refl
Gκ-cp (G.suc b) (inj₂ p) = Cp-tr K₂ω (Gκ-cp b p) (plus-weak (Gκ b) (KT b))
Gκ-cp (G.lim f) (inj₂ (n , p)) = inj₂ (n , Gκ-cp (f n) p)

Gκ-legal : ∀ η → Lgl zero η → Lgl K₂ω (Gκ η)
Gκ-legal G.zero l = F₁-legal G.top tt
Gκ-legal (G.suc a) l = plus-lgl (Gκ a) (KT a) (Gκ-legal a l) (KT-legal a)
Gκ-legal (G.lim f) (st , lf) =
  (λ n → Gκ-cp (f (suc n)) (st n)) , (λ n → Gκ-legal (f n) (lf n))
Gκ-legal G.top l = F₁-legal G.top tt

Gκ-nested : ∀ η → Nested K₂ω (Gκ η)
Gκ-nested G.zero = F₁-nested G.top tt
Gκ-nested (G.suc a) = plus-ns (Gκ a) (KT a) (Gκ-nested a) (KT-nested a)
Gκ-nested (G.lim f) = λ n → Gκ-nested (f n)
Gκ-nested G.top = F₁-nested G.top tt

βᴺ : Branches
βᴺ η e = Gκ η

βᴺ-legal : RowLegal βᴺ
βᴺ-legal = record
  { first = λ η e → Gκ-first η
  ; directed = λ η e η′ e′ q → Gκ-cp η′ (proj₁ q)
  ; lawful = λ η e → Gκ-legal η (proj₁ (proj₂ e))
  ; nested = λ η e → Gκ-nested η }

topᴺ : RΩ
topᴺ = row βᴺ

topᴺ-legal : Lgl K₂ω topᴺ
topᴺ-legal = row-legal βᴺ βᴺ-legal

topᴺ-nested : Nested K₂ω topᴺ
topᴺ-nested = row-nested βᴺ βᴺ-legal

topᴺ-kept : Kept K₂ω zero topᴺ
topᴺ-kept = root₂ , refl , raw1 , _ , _ , refl
```

## 5 归一坐标上的保留律

`YiOmFoldGap.KeepLaw` 要第 `suc a` 支是层号 `read0 a` 的保留结点。这里得到层号 `read0 (nrm a)`，槽位在坐标 `suc (nrm a)` 的那一支的根上；`a` 不含极限时 `nrm a ≡ a`。
这一行的结点在分支槽位上，出了 `Φ⁰` 的定义域：再折它要 `YiOmFoldGap.BranchRow` 的 `own`，而它的各支里有 `top` 与别的支上的结点。

```agda
norm-keep : ∀ a (e : Gd zero raw1 (G.suc a)) → Kept K₂ω (read0 (nrm a)) (βᴺ (G.suc a) e)
norm-keep a e =
  br (G.suc (nrm a)) (γ a) (inj₁ tt) , refl , cO (read0 (nrm a)) , _ , _ , refl

norm-keep-fin : ∀ a → LimFree a → (e : Gd zero raw1 (G.suc a)) →
  Kept K₂ω (read0 a) (βᴺ (G.suc a) e)
norm-keep-fin a h e =
  subst (λ z → Kept K₂ω (read0 z) (Gκ (G.suc a))) (nrm-id a h) (norm-keep a e)

norm-not-dom : ∀ a → Dom⁰ (Gκ (G.suc a)) → ⊥
norm-not-dom a ()

norm-not-tr : ∀ a → Tr (Gκ (G.suc a)) → ⊥
norm-not-tr a ()
```

用这一行推进链的第一步：`top + topᴺ` 合法，是 `Ω₁⁺` 的带守卫坐标 (下界 `top` 的守卫)；它不在 `Dom⁰` 里，链的起点坐标 1 上的那一支就是分支槽位上的结点。

```agda
point₁ᴺ : RΩ
point₁ᴺ = plusΩ G.top topᴺ

point₁ᴺ-guard : Gd K₂ω G.top point₁ᴺ
point₁ᴺ-guard =
  plus-weak G.top topᴺ , plus-lgl G.top topᴺ tt topᴺ-legal , plus-ns G.top topᴺ tt topᴺ-nested

point₁ᴺ-not-dom : Dom⁰ point₁ᴺ → ⊥
point₁ᴺ-not-dom (dt , dg) with dg one (inj₁ refl , tt , tt)
... | ()
```
