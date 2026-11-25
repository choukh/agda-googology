# 不同步引理: 否定一路 (对 `YiASIface` 的陈述)

> 验收文件 (读记号, 读具体块); 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. 最小实例被否定: `¬async₀ᶜ`, `¬async₀`, `¬pair₀` (第 3 层 Ω 树与 Ω₁ 没有 `M` 关系; 它折到第 2 层的输出含第 0 层槽位的结点当且仅当底值或底含, `out₀`).
> `LowKeepAsyncᶠ` 没有被否定, 按槽位层细分的 "槽位不保留" 在它上面不可得: 有关系的不同步对, 输出总含余尾下标那一层槽位的结点 (`async-kept`, 经 `keepHas`); 且这样的对只能经放宽得到 (`async→weak`).
> 工具: `Has m n x` (x 沿第一位置序与孩子含槽位层 m 的结点), 反演 `invˢ` (`YiAbsGNeg.Inv.inv` 的细分: 结点一条只对 `Nu` 允许的槽位). 不否定 `LowKeepᶠ`, 不证 `LowKeepAsyncᶠ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiASNeg where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; 1+n≰n; ≤-reflexive)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ∷-injectiveʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiAbsLeg using (Bsᴸ; Btᴸ)
import OCF.Align.EboLeanDef as E
open E using (cof; c0; c1; cω; cΩ; natT)
open import OCF.Lean.YiMEBase using (Mᴰ; mz; m1; mL; mΩ; mU; mw; M⁰; _⊴_; ⊴r; ⊴◃; pos⁰)
open import OCF.Lean.YiANFam using (fin; slot; M; Lw; Nw; mwN; ψᴺ; Ωᴺ; cofΩ; cofK; cmp-pen; Mβ; FD; fd0; fds; dn; mvS)
open import OCF.Lean.YiMWPre using (cof++Ω)
open import OCF.Lean.YiAbsGFin using (slLᶠ)
open import OCF.Lean.YiAbsGFinInv using (cof++ne)
open import OCF.Lean.YiASIface
```

## 含槽位层 m 的结点

`Has m n x`: 第 n 层的树 x 之下 (沿第一位置序: 后继的前驱, ℕ 极限的项, 结点的第一分支, 嵌入的左项) 或孩子里, 有槽位层为 m 的结点. 它沿第一位置序向上保持.

```agda
Has : (m n : ℕ) → Tr (fin n) → Set
Has m zero    x            = ⊥
Has m (suc n) zero         = ⊥
Has m (suc n) (suc x)      = Has m (suc n) x
Has m (suc n) (lim f a)    = Σ ℕ λ k → Has m (suc n) (f k)
Has m (suc n) (Ω p g)      = (slot n p ≡ m) ⊎ Has m (suc n) (g (br0 (fin (suc n)) p))
Has m (suc n) (up x _ y _) = Has m (suc n) x ⊎ Has m n y

has◃ : ∀ m n {x x′} → Has m n x → fin n ⊢ x ◃ x′ → Has m n x′
has◃ m (suc n) h        ◃s           = h
has◃ m (suc n) h        (◃l k)       = k , h
has◃ m (suc n) h        ◃w           = inj₂ h
has◃ m (suc n) h        (◃u x c y e) = inj₁ h
has◃ m (suc n) (inj₁ h) (◃c x c r)   = inj₁ h
has◃ m (suc n) (inj₂ h) (◃c x c r)   = inj₂ (has◃ m n h r)
has◃ m (suc n) h        (◃t d e)     = has◃ m (suc n) (has◃ m (suc n) h d) e

has⊴ : ∀ m n {x x′} → Has m n x → x ⊴ x′ → Has m n x′
has⊴ m n h ⊴r     = h
has⊴ m n h (⊴◃ d) = has◃ m n h d
```

任何对 "槽位层 m 的结点", 放宽, "孩子含" 封闭的谓词都含 `Has` (所以细分之后没有更小的可用谓词).

```agda
module Least (m j : ℕ) (H : Tr (fin (suc j)) → Set)
    (hΩ : (p : Pos (fin (suc j))) (g : Br (fin (suc j)) p → Tr (fin (suc j))) → slot j p ≡ m → H (Ω p g))
    (hw : ∀ {x x′} → H x → fin (suc j) ⊢ x ◃ x′ → H x′)
    (hc : ∀ {x y e} → Has m j y → H (up x tt y e)) where

  has→H : (o : Tr (fin (suc j))) → Has m (suc j) o → H o
  has→H (suc o)      h        = hw (has→H o h) ◃s
  has→H (lim f a)    (k , h)  = hw (has→H (f k) h) (◃l k)
  has→H (Ω p g)      (inj₁ e) = hΩ p g e
  has→H (Ω p g)      (inj₂ h) = hw (has→H (g (br0 (fin (suc j)) p)) h) ◃w
  has→H (up x _ y e) (inj₁ h) = hw (has→H x h) (◃u x tt y e)
  has→H (up x _ y e) (inj₂ h) = hc h
```

## 反演

余尾为 Ω_{m+1} 的记号项只能对着含槽位层 m 的结点的树. 与 `YiAbsGFinInv.invᶠ` 的差别: 结点一条用到 `Nw` (槽位允许的余尾下标).

```agda
private
  no0 : ∀ {κ} → c0 ≡ cΩ κ → ⊥
  no0 ()
  no1 : ∀ {c κ} → c ≡ c1 → c ≡ cΩ κ → ⊥
  no1 refl ()
  noω : ∀ {c κ} → c ≡ cω → c ≡ cΩ κ → ⊥
  noω refl ()

cΩ-inj : ∀ {a b} → cΩ a ≡ cΩ b → a ≡ b
cΩ-inj refl = refl

natT-inj : ∀ a b → natT a ≡ natT b → a ≡ b
natT-inj zero    zero    e = refl
natT-inj zero    (suc b) ()
natT-inj (suc a) zero    ()
natT-inj (suc a) (suc b) e = cong suc (natT-inj a b (∷-injectiveʳ e))

inv⁰ : ∀ {κ s o} → M⁰ s o → cof s ≡ cΩ κ → ⊥
inv⁰ mz                 w = no0 w
inv⁰ (m1 e r)           w = no1 e w
inv⁰ (mL e h)           w = noω e w
inv⁰ (mΩ {p = ()} _ _ _)
inv⁰ (mU {c = ()} _ _)
inv⁰ (mw r d)           w = inv⁰ r w

invU : ∀ m n t s {x : Tr (fin (suc n))} {y : Tr (fin n)}
     → (cof t ≡ cΩ (natT m) → Has m (suc n) x) → (cof s ≡ cΩ (natT m) → Has m n y)
     → cof (t ++ s) ≡ cΩ (natT m) → Has m (suc n) x ⊎ Has m n y
invU m n t []       q q′ w = inj₁ (q (subst (λ u → cof u ≡ cΩ (natT m)) (++-identityʳ t) w))
invU m n t (a ∷ as) q q′ w = inj₂ (q′ (trans (sym (cof++ne t a as)) w))

module Step (m n : ℕ) (rec : ∀ {s o} → M n s o → cof s ≡ cΩ (natT m) → Has m n o) where
  step : ∀ {s o} → Mᴰ (Sig (fin (suc n))) (Lw n) (λ _ → M n) (Nw n) s o → cof s ≡ cΩ (natT m) → Has m (suc n) o
  step mz                    w = ⊥-elim (no0 w)
  step (m1 e r)              w = ⊥-elim (no1 e w)
  step (mL e h)              w = ⊥-elim (noω e w)
  step (mΩ {p = p} e nu h)   w = inj₁ (natT-inj (slot n p) m (trans (sym nu) (cΩ-inj (trans (sym e) w))))
  step (mU {t = t} {s = s} {x = x} {y = y} r ch) w = invU m n t s {x = x} {y = y} (step r) (rec ch) w
  step (mw r d)              w = has◃ m (suc n) (step r w) d

invˢ : ∀ m n {s o} → M n s o → cof s ≡ cΩ (natT m) → Has m n o
invˢ m zero    r w = ⊥-elim (inv⁰ r w)
invˢ m (suc n) r w = Step.step m n (invˢ m n) r w
```

## 上界: 运算与折到自身不新造结点

和, `next`, 部分和, 上折, 折到自身: 输出含槽位层 m 的结点, 则某个输入含.

```agda
has+ : ∀ m n (x y : Tr (fin (suc n))) → Has m (suc n) (x + y) → Has m (suc n) x ⊎ Has m (suc n) y
has+ m n x zero         h        = inj₁ h
has+ m n x (suc y)      h        = has+ m n x y h
has+ m n x (lim f a)    (k , h)  with has+ m n x (f k) h
... | inj₁ u = inj₁ u
... | inj₂ u = inj₂ (k , u)
has+ m n x (Ω p g)      (inj₁ e) = inj₂ (inj₁ e)
has+ m n x (Ω p g)      (inj₂ h) with has+ m n x (g (br0 (fin (suc n)) p)) h
... | inj₁ u = inj₁ u
... | inj₂ u = inj₂ (inj₂ u)
has+ m n x (up y c w e) (inj₁ h) with has+ m n x y h
... | inj₁ u = inj₁ u
... | inj₂ u = inj₂ (inj₁ u)
has+ m n x (up y c w e) (inj₂ h) = inj₂ (inj₂ h)

has-iter : ∀ m n (b : Tr (fin (suc n))) k → Has m (suc n) (iter (b +_) b k) → Has m (suc n) b
has-iter m n b zero    h = h
has-iter m n b (suc k) h with has+ m n b (iter (b +_) b k) h
... | inj₁ u = u
... | inj₂ u = has-iter m n b k u

has-next : ∀ m n (b : Tr (fin (suc n))) → (Σ ℕ λ k → Has m (suc n) (iter (b +_) b k)) → Has m (suc n) b
has-next m n b (k , h) = has-iter m n b k h

has-cum : ∀ m n (F : ℕ → Tr (fin (suc n))) k → Has m (suc n) (cum F k) → Σ ℕ λ i → Has m (suc n) (F i)
has-cum m n F zero    h = zero , h
has-cum m n F (suc k) h with has+ m n (cum F k) (F (suc k)) h
... | inj₁ u = has-cum m n F k u
... | inj₂ u = suc k , u

hasUp : ∀ m {N} n (d : FD (suc N) n) (b : Tr (fin (suc N))) (nb : fin (suc N) ⊢ zero ◃ b) (y : Tr (fin n))
      → Has m (suc N) (Up (fin n) (dn d) b nb y) → Has m (suc N) b ⊎ Has m n y
hasUp m zero d b nb zero      h = inj₁ h
hasUp m zero d b nb (suc y)   h = hasUp m zero d b nb y (has-next m _ (Up zero (dn d) b nb y) h)
hasUp m zero d b nb (lim f a) (k , h) = hasUp m zero d b nb (f k) h
hasUp m zero d b nb (Ω () _)
hasUp m zero d b nb (up _ () _ _)
hasUp m (suc n) d b nb zero      h = inj₁ h
hasUp m (suc n) d b nb (suc y)   h = hasUp m (suc n) d b nb y (has-next m _ (Up (fin (suc n)) (dn d) b nb y) h)
hasUp m (suc n) d b nb (lim f a) (k , h) with hasUp m (suc n) d b nb (f k) h
... | inj₁ u = inj₁ u
... | inj₂ u = inj₂ (k , u)
hasUp m {N} (suc n) d b nb (Ω p g) (inj₁ e) = inj₂ (inj₁ (trans (sym (mvS d p)) e))
hasUp m {N} (suc n) d b nb (Ω p g) (inj₂ h)
  with hasUp m (suc n) d b nb (g (br0 (fin (suc n)) p))
         (subst (λ t → Has m (suc N) (Up (fin (suc n)) (dn d) b nb (g t))) (mvFirst (dn d) p) h)
... | inj₁ u = inj₁ u
... | inj₂ u = inj₂ (inj₂ u)
hasUp m (suc n) d b nb (up y _ y′ e) h
  with hasUp m n (fds d) (Up (fin (suc n)) (dn d) b nb y) (Up-nz (fin (suc n)) (dn d) b nb y) y′ h
... | inj₂ u = inj₂ (inj₂ u)
... | inj₁ u with hasUp m (suc n) d b nb y u
...   | inj₁ v = inj₁ v
...   | inj₂ v = inj₂ (inj₁ v)

hasSelf : ∀ m n (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (B : Base (fin (suc n)))
          (β : Tr (fin (suc n))) (nβ : fin (suc n) ⊢ zero ◃ β) (z : Tr (fin (suc n)))
        → Has m (suc n) (ψs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ z) → Has m (suc n) β ⊎ Has m (suc n) z
hasSelf m n ε ρ B β nβ zero      h = inj₁ h
hasSelf m n ε ρ B β nβ (suc z)   h =
  hasSelf m n ε ρ B β nβ z (has-next m n (ψs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ z) h)
hasSelf m n ε ρ B β nβ (lim f a) (k , h) with hasSelf m n ε ρ B β nβ (f k) h
... | inj₁ u = inj₁ u
... | inj₂ u = inj₂ (k , u)
hasSelf m n ε ρ B β nβ (Ω p g)   (inj₁ e) = inj₂ (inj₁ e)
hasSelf m n ε ρ B β nβ (Ω p g)   (inj₂ h) with hasSelf m n ε ρ B β nβ (g (br0 (fin (suc n)) p)) h
... | inj₁ u = inj₁ u
... | inj₂ u = inj₂ (inj₂ u)
hasSelf m n ε ρ B β nβ (up x _ y e) h
  with hasUp m n (fds fd0) (ψs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ x)
         (nzs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ x) y h
... | inj₂ u = inj₂ (inj₂ u)
... | inj₁ u with hasSelf m n ε ρ B β nβ x u
...   | inj₁ v = inj₁ v
...   | inj₂ v = inj₂ (inj₁ v)
```

## 第 n+2 层 Ω 树折到第 n+1 层的输出

输出是回灌链的部分和极限 (对角). 它含槽位层 m 的结点, 则底值 β 或底在目标层的分量含.

```agda
module Out (m n : ℕ) (ε : Ev (fin (suc (suc n)))) (ρ : Rt (fin (suc (suc n)))) (B : Base (fin (suc (suc n))))
           (β : Tr (fin (suc n))) (nβ : fin (suc n) ⊢ zero ◃ β) where
  private
    j = fin (suc n)
    ℓ = fin (suc (suc n))
    b₂ : Tr j
    b₂ = bs B j (ins self)
    n₂ : j ⊢ zero ◃ b₂
    n₂ = ns B j (ins self)
    g : Tr j → Tr ℓ
    g z = up zero tt (suc z) (z◃s z)
    Φ : Tr j → Tr j
    Φ z = ψs ℓ ε ρ B j (ins self) b₂ n₂ (g z)
    Z : ℕ → Tr j
    Z = iter Φ zero
    F : ℕ → Tr j
    F k = ψs ℓ ε ρ B j (ins self) β nβ (g (Z k))
    B′ : Base j
    B′ = dS j ε ρ B zero

    hasZ : ∀ k → Has m (suc n) (Z k) → Has m (suc n) b₂
    hasZ (suc k) h with hasSelf m n ε ρ B′ b₂ n₂ (Z k) (has-next m n (ψs j ε ρ B′ j self b₂ n₂ (Z k)) h)
    ... | inj₁ u = u
    ... | inj₂ u = hasZ k u

  out₀ : Has m (suc n) (ψs ℓ ε ρ B j (ins self) β nβ (Ωt ℓ)) → Has m (suc n) β ⊎ Has m (suc n) b₂
  out₀ (k , h) with has-cum m n F k h
  ... | i , u with hasSelf m n ε ρ B′ β nβ (Z i) (has-next m n (ψs j ε ρ B′ j self β nβ (Z i)) u)
  ...   | inj₁ v = inj₁ v
  ...   | inj₂ v = inj₂ (hasZ i v)

open Out public using (out₀)
```

## 最小实例的否定

第 2, 3 层的 Ω 树不含槽位层 0 的结点. 所以 (Ω₁, 第 3 层 Ω 树) 没有 `M` 关系 (`¬pair₀`); 底值与底都取 Ω 树时, 输出与余尾 Ω₁ 的项没有 `M` 关系.

```agda
noΩ₂ : Has 0 2 (Ωt (fin 2)) → ⊥
noΩ₂ (inj₁ ())
noΩ₂ (inj₂ (inj₁ ()))
noΩ₂ (inj₂ (inj₂ ()))

noΩ₃ : Has 0 3 (Ωt (fin 3)) → ⊥
noΩ₃ (inj₁ ())
noΩ₃ (inj₂ (inj₁ ()))
noΩ₃ (inj₂ (inj₂ ()))

¬M₀ : M 3 (Ωᴺ 1) (Ωt (fin 3)) → ⊥
¬M₀ r = noΩ₃ (invˢ 0 3 r (cofΩ 0))

¬pair₀ : Pair₀ → ⊥
¬pair₀ (_ , r) = ¬M₀ r

cof₀ : ∀ P → cof (ψᴺ 2 (P ++ Ωᴺ 1)) ≡ cΩ (natT 0)
cof₀ P = cofK (natT 2) (P ++ Ωᴺ 1) (cmp-pen {a = 0} {b = 2} (s≤s z≤n)) (cof++Ω P (Ωᴺ 1) (cofΩ 0))
```

`Async₀` 的结论的必要条件: 底值或底在第 2 层的分量含槽位层 0 的结点.

```agda
async₀-needs : (ε : Ev (fin 3)) (ρ : Rt (fin 3)) (B : Base (fin 3)) (P : E.T) (β : Tr (fin 2)) (nβ : fin 2 ⊢ zero ◃ β)
  → M 2 (ψᴺ 2 (P ++ Ωᴺ 1)) (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ (Ωt (fin 3)))
  → Has 0 2 β ⊎ Has 0 2 (bs B (fin 2) (ins self))
async₀-needs ε ρ B P β nβ r = out₀ 0 1 ε ρ B β nβ (invˢ 0 2 r (cof₀ P))

¬async₀ᶜ : Async₀ᶜ → ⊥
¬async₀ᶜ A with async₀-needs tt tt (B₀ (fin 3)) [] (Ωt (fin 2)) (Ωt-nz (fin 2)) (A tt tt)
... | inj₁ h = noΩ₂ h
... | inj₂ h = noΩ₂ h
```

`Async₀` 的前提可满足: 标准底 `B₀` 满足 `GBᶠ` (P 为空), 第 2 层 Ω 树对着 Ω₂.

```agda
MΩ : ∀ i → M i (ψᴺ i []) (Ωt (fin i))
MΩ zero    = pos⁰ (Ωt zero) (Ωt-nz zero)
MΩ (suc i) = Mβ i

gb₀ : GBᶠ 2 (B₀ (fin 3)) []
gb₀ = mkGBᶠ (λ _ → ⊴r) (λ {i} _ → MΩ i)

¬async₀ : Async₀ → ⊥
¬async₀ A = ¬async₀ᶜ (λ ε ρ → A ε ρ (B₀ (fin 3)) [] gb₀ (Ωt (fin 2)) (Ωt-nz (fin 2)) (Mβ 1))
```

## 下界: 折到低层保留低槽位的结点

m 低于目标层 j 时, `Has m` 沿折叠保持. 结点一行: 槽位层 m 的结点被保留 (`kpS`, 对 `kp` 在有限层号上的归纳); 嵌入一行经上折 (`keepUp`) 或孩子层的折叠.

```agda
sb≤ : ∀ {n j} → Sbᶠ n j → j ≤ⁿ n
sb≤ s0     = ≤-refl
sb≤ (ss s) = m≤n⇒m≤1+n (sb≤ s)

geψ : ∀ n j (ε : Ev (fin n)) (ρ : Rt (fin n)) (B : Base (fin n)) (w : fin j ≤ fin n) (β : Tr (fin j))
      (nβ : fin j ⊢ zero ◃ β) (x : Tr (fin n)) → β ⊴ ψs (fin n) ε ρ B (fin j) w β nβ x
geψ n j ε ρ B w β nβ x with zl x
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ (monos (fin n) ε ρ B (fin j) w β nβ d)

geUp : ∀ {N} n (d : FD (suc N) n) (b : Tr (fin (suc N))) (nb : fin (suc N) ⊢ zero ◃ b) (y : Tr (fin n))
     → b ⊴ Up (fin n) (dn d) b nb y
geUp n d b nb y with zl y
... | inj₁ refl = ⊴r
... | inj₂ e    = ⊴◃ (Up-mono (fin n) (dn d) b nb e)

keepUp : ∀ m {N} n (d : FD (suc N) n) (b : Tr (fin (suc N))) (nb : fin (suc N) ⊢ zero ◃ b) (y : Tr (fin n))
       → Has m n y → Has m (suc N) (Up (fin n) (dn d) b nb y)
keepUp m (suc n) d b nb (suc y)   h       = zero , keepUp m (suc n) d b nb y h
keepUp m (suc n) d b nb (lim f a) (k , h) = k , keepUp m (suc n) d b nb (f k) h
keepUp m (suc n) d b nb (Ω p g)   (inj₁ e) = inj₁ (trans (mvS d p) e)
keepUp m {N} (suc n) d b nb (Ω p g) (inj₂ h) =
  inj₂ (subst (λ t → Has m (suc N) (Up (fin (suc n)) (dn d) b nb (g t))) (sym (mvFirst (dn d) p))
         (keepUp m (suc n) d b nb (g (br0 (fin (suc n)) p)) h))
keepUp m {N} (suc n) d b nb (up y _ y′ e) (inj₁ h) =
  has⊴ m (suc N) (keepUp m (suc n) d b nb y h)
    (geUp n (fds d) (Up (fin (suc n)) (dn d) b nb y) (Up-nz (fin (suc n)) (dn d) b nb y) y′)
keepUp m (suc n) d b nb (up y _ y′ e) (inj₂ h) =
  keepUp m n (fds d) (Up (fin (suc n)) (dn d) b nb y) (Up-nz (fin (suc n)) (dn d) b nb y) y′ h

kpS : ∀ m n {j} (s : Sbᶠ (suc n) j) (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (p : Pos (fin (suc n)))
      {X : Set} (Q : X → Set) {K : (q : Pos (fin j)) → (Br (fin j) q → Br (fin (suc n)) p) → X} {d : X}
    → slot n p ≡ m → suc m ≤ⁿ j → ((q : Pos (fin j)) (cv : Br (fin j) q → Br (fin (suc n)) p) → slLᶠ j q ≡ m → Q (K q cv))
    → Q (kp (fin (suc n)) ε ρ p (pthᶠ s) K d)
kpS m n       s0     ε ρ p        Q e lt hk = hk p (λ z → z) e
kpS m n       (ss s) ε ρ (inj₁ _) Q e lt hk =
  ⊥-elim (1+n≰n (≤-trans (≤-trans (s≤s (≤-reflexive e)) lt) (sb≤ s)))
kpS m (suc n) (ss s) ε ρ (inj₂ p) Q e lt hk = kpS m n s ε ρ p Q e lt hk
kpS m zero    (ss s) ε ρ (inj₂ ())

keepHas : ∀ m n {j} (s : Sbᶠ n j) (ε : Ev (fin n)) (ρ : Rt (fin n)) (B : Base (fin n))
          (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) (x : Tr (fin n))
        → suc m ≤ⁿ j → Has m n x → Has m j (ψs (fin n) ε ρ B (fin j) (pthᶠ s) β nβ x)
keepHas m (suc n) {suc j} s ε ρ B β nβ (suc x)   (s≤s l) h       = zero , keepHas m (suc n) s ε ρ B β nβ x (s≤s l) h
keepHas m (suc n) {suc j} s ε ρ B β nβ (lim f a) (s≤s l) (k , h) = k , keepHas m (suc n) s ε ρ B β nβ (f k) (s≤s l) h
keepHas m (suc n) {suc j} s ε ρ B β nβ (Ω p g)   (s≤s l) (inj₁ e) =
  kpS m n s ε ρ p (Has m (suc j)) e (s≤s l) (λ q cv eq → inj₁ eq)
keepHas m (suc n) {suc j} s ε ρ B β nβ (Ω p g)   (s≤s l) (inj₂ h) =
  kp-ind (fin (suc n)) ε ρ p (pthᶠ s) (Has m (suc j))
    (λ q cv gd → inj₂ (subst (λ t → Has m (suc j) (ψs (fin (suc n)) ε ρ B (fin (suc j)) (pthᶠ s) β nβ (g t))) (sym gd)
                         (keepHas m (suc n) s ε ρ B β nβ (g (br0 (fin (suc n)) p)) (s≤s l) h)))
    (zero , keepHas m (suc n) s ε ρ B β nβ (g (br0 (fin (suc n)) p)) (s≤s l) h)
keepHas m (suc n) {suc j} s0 ε ρ B β nβ (up x _ y e) (s≤s l) (inj₁ h) =
  has⊴ m (suc n) (keepHas m (suc n) s0 ε ρ B β nβ x (s≤s l) h)
    (geUp n (fds fd0) (ψs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ x) (nzs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ x) y)
keepHas m (suc n) {suc j} s0 ε ρ B β nβ (up x _ y e) (s≤s l) (inj₂ h) =
  keepUp m n (fds fd0) (ψs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ x) (nzs (fin (suc n)) ε ρ B (fin (suc n)) self β nβ x) y h
keepHas m (suc n) {suc j} (ss s) ε ρ B β nβ (up x _ y e) (s≤s l) (inj₁ h) =
  has⊴ m (suc j) (keepHas m (suc n) (ss s) ε ρ B β nβ x (s≤s l) h)
    (geψ n (suc j) ε ρ (dS (fin n) ε ρ B x) (pthᶠ s)
      (ψs (fin (suc n)) ε ρ B (fin (suc j)) (ins (pthᶠ s)) β nβ x) (nzs (fin (suc n)) ε ρ B (fin (suc j)) (ins (pthᶠ s)) β nβ x) y)
keepHas m (suc n) {suc j} (ss s) ε ρ B β nβ (up x _ y e) (s≤s l) (inj₂ h) =
  keepHas m n s ε ρ (dS (fin n) ε ρ B x)
    (ψs (fin (suc n)) ε ρ B (fin (suc j)) (ins (pthᶠ s)) β nβ x) (nzs (fin (suc n)) ε ρ B (fin (suc j)) (ins (pthᶠ s)) β nβ x) y (s≤s l) h
```

## `LowKeepAsyncᶠ` 上: 细分的 "槽位不保留" 不可得

`ix`: 不同步对里余尾下标的层号 i (κ = `natT i`, i < j). 有关系的不同步对, 折叠输出含槽位层 i 的结点 (`async-kept`); 所以任何对结点 (槽位层 i), 放宽, "孩子含" 封闭的谓词在输出上成立 (`no-unkept`), `unkept→¬low` 的前提 "输出不满足 H" 在这里取不到.

```agda
ix : ∀ {n j a} {x : Tr (fin n)} → AsyncPairᶠ {n = n} j a x → ℕ
ix (κ , p , g , e , (i , _) , _) = i

async-kept : ∀ {n j} (b : Bsᴸ (fin n)) (w : fin j ≤ fin n) (β : Btᴸ (fin j)) → (Σ (Sbᶠ n j) λ s → w ≡ pthᶠ s)
  → ∀ {a x} (ap : AsyncPairᶠ {n = n} j a x) → M n a x
  → Has (ix ap) j (ψs (fin n) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (fin j) w (proj₁ β) (proj₂ β) x)
async-kept {n} (ε , ρ , B) _ (β , nβ) (s , refl) {x = x} (κ , p , g , e , (i , refl , lt) , _) r =
  keepHas i n s ε ρ B β nβ x lt (invˢ i n r e)

no-unkept : ∀ {n j} (b : Bsᴸ (fin n)) (w : fin (suc j) ≤ fin n) (β : Btᴸ (fin (suc j))) → (Σ (Sbᶠ n (suc j)) λ s → w ≡ pthᶠ s)
  → ∀ {a x} (ap : AsyncPairᶠ {n = n} (suc j) a x) → M n a x
  → (H : Tr (fin (suc j)) → Set)
  → ((p : Pos (fin (suc j))) (g : Br (fin (suc j)) p → Tr (fin (suc j))) → slot j p ≡ ix ap → H (Ω p g))
  → (∀ {x x′} → H x → fin (suc j) ⊢ x ◃ x′ → H x′)
  → (∀ {x y e} → Has (ix ap) j y → H (up x tt y e))
  → H (ψs (fin n) (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) (fin (suc j)) w (proj₁ β) (proj₂ β) x)
no-unkept {j = j} b w β wl ap r H hΩ hw hc = Least.has→H (ix ap) j H hΩ hw hc _ (async-kept b w β wl ap r)
```

不同步对的关系只能经放宽得到: 推导的最后一步不是结点规则 (槽位层不低于 j, 余尾下标低于 j), 所以有严格在下的 x′ 带同一个参照项.

```agda
async→weak : ∀ {n j a} {x : Tr (fin n)} → AsyncPairᶠ {n = n} j a x → M n a x
           → Σ (Tr (fin n)) λ x′ → M n a x′ × (fin n ⊢ x′ ◃ x)
async→weak {suc n} (κ , p , g , e , (i , refl , lt) , refl , nb) mz = ⊥-elim (no0 e)
async→weak {suc n} (κ , p , g , e , (i , refl , lt) , refl , nb) (mL e′ h) = ⊥-elim (noω e′ e)
async→weak {suc n} (κ , p , g , e , (i , refl , lt) , refl , nb) (mΩ e′ nu h) =
  ⊥-elim (1+n≰n (≤-trans lt (≤-trans nb
    (≤-reflexive (natT-inj (slot n p) i (trans (sym nu) (cΩ-inj (trans (sym e′) e))))))))
async→weak {suc n} (κ , p , g , e , (i , refl , lt) , refl , nb) (mw {x = x′} r d) = x′ , r , d
```

结论沿这一步放宽传回 (折叠单调): `LowKeepAsyncᶠ` 在一个不同步对上的结论, 由同一参照项在严格在下的 x′ 上的结论推出.

```agda
async-step : ∀ {n j} (ε : Ev (fin n)) (ρ : Rt (fin n)) (B : Base (fin n)) (w : fin j ≤ fin n) (β : Tr (fin j))
             (nβ : fin j ⊢ zero ◃ β) {s : E.T} {x′ x : Tr (fin n)} → fin n ⊢ x′ ◃ x
           → M j s (ψs (fin n) ε ρ B (fin j) w β nβ x′) → M j s (ψs (fin n) ε ρ B (fin j) w β nβ x)
async-step {n} {j} ε ρ B w β nβ d r = mwN j r (monos (fin n) ε ρ B (fin j) w β nβ d)
```

## 前提可满足: 一个有关系的不同步对

x₁ 是第 3 层上槽位层 2 的结点 (Ω 树左加 y₃), y₃ 是 Ω₁ 的树经两次嵌入搬到第 3 层. 它与 Ω₁ 的关系经两步放宽; 输出含槽位层 0 的结点.

```agda
y₂ : Tr (fin 2)
y₂ = up zero tt (Ωt (fin 1)) (Ωt-nz (fin 1))

y₃ : Tr (fin 3)
y₃ = up zero tt y₂ (◃u zero tt (Ωt (fin 1)) (Ωt-nz (fin 1)))

x₁ : Tr (fin 3)
x₁ = Ω (inj₁ tt) (λ c → up y₃ tt (suc c) (z◃s c))

M₁ : M 3 (Ωᴺ 1) x₁
M₁ = mw (mw (mU mz (mU mz (Mβ 0))) (◃u y₃ tt (suc zero) (z◃s zero))) ◃w

pair₁ : AsyncPairᶠ {n = 3} 2 (Ωᴺ 1) x₁
pair₁ = natT 0 , inj₁ tt , (λ c → up y₃ tt (suc c) (z◃s c)) , cofΩ 0 , (0 , refl , s≤s z≤n) , refl , s≤s (s≤s z≤n)

kept₁ : (ε : Ev (fin 3)) (ρ : Rt (fin 3)) (B : Base (fin 3)) (β : Tr (fin 2)) (nβ : fin 2 ⊢ zero ◃ β)
      → Has 0 2 (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ x₁)
kept₁ ε ρ B β nβ = async-kept (ε , ρ , B) (ins self) (β , nβ) (ss s0 , refl) pair₁ M₁
```
