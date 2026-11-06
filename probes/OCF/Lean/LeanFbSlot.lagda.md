# LeanFb (二): 同级拷贝一起升 (数字层号上的共享增量)

> 不含记号. 入口 [LeanFb](LeanFb.lagda.md), 接口 [LeanFbIf](LeanFbIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **同级拷贝.** `Lv k` 里每个 `ls x` (以及 `lΩ x g` 的左分量 `step (Lv x)`) 带一个新种类, 坐标是 `HB (Lv x)`, 它的级是 $x$. 同一个级 $x$ 的新种类在各站、各坐标分量里反复出现 (例如 [NegSLFbInst](../Align/NegSLFbInst.lagda.md) 的 `cp1`: 第 3 站里第 1 站头的拷贝). 参考 [SlotCp](../Align/SlotCp.lagda.md) 的 `cpSlot` (沿一切路径的拷贝一起写), 这里不建共享槽的世界证据 (`SlotIf.ShW`), 而是一次调用给**一切**级为 $x$ 的种类的界加同一个增量 (接口 `Up` 的加性形状): 不需要 "同界" 证据, 世界总是变大.
>
> **只在数字层号上.** "这个新种类的级是 $x$" 要判定层号相等; 层号含函数时不可判定 (否定一路的 `NegLeanFbPre.wdec1`, 早先的 `NegSlotWall.no-slot-κHc`: 跨级族不能同槽). 数字层号 `num j = lsʲ lz` 上的相等按构造子判定 (`eqN`), 所以对每个 $j$, 级为 `num j` 的一切拷贝 (一切站, 一切坐标分量, 下标含函数) 有一个 `Up` (`slotUp j`), 不判定含函数的下标.
>
> - `addN`, `addSt`: 对层号递归, 在每个级为 `num j` 的新种类的界上 $\boxplus\,\delta$. `addN≤`, `Lg-addN`.
> - 成员: `PosN k`, `PosSt x` (级为 `num j` 的新种类在 `Lv k` 里的一切位置), 种类 `kN`, 坐标读回 `coN`; 升后的顶 `top-addN` (对一切位置).
> - 种类查成员 `memN`, `memSt` (对种类结构递归, 只判定数字层号).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFbSlot where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt
```

## §1 数字层号

```agda
num : ℕ → LH
num zero = lz
num (suc j) = ls (num j)

eqN : (j : ℕ) (x : LH) → (num j ≡ x) ⊎ ⊤
eqN zero lz = inj₁ refl
eqN zero (ls x) = inj₂ tt
eqN zero (ll f) = inj₂ tt
eqN zero (lΩ k g) = inj₂ tt
eqN (suc j) lz = inj₂ tt
eqN (suc j) (ls x) = map₁ (cong ls) (eqN j x)
eqN (suc j) (ll f) = inj₂ tt
eqN (suc j) (lΩ k g) = inj₂ tt

eqN-num : ∀ j → eqN j (num j) ≡ inj₁ refl
eqN-num zero = refl
eqN-num (suc j) = cong (map₁ (cong ls)) (eqN-num j)
```

## §2 一起加

```agda
module Add (j : ℕ) (δ : HB (Lv (num j))) where
  cast : ∀ {x} → num j ≡ x → HB (Lv x)
  cast refl = δ

  bump : ∀ {x} → (num j ≡ x) ⊎ ⊤ → HB (Lv x) → HB (Lv x)
  bump (inj₁ e) β = β ⊞ cast e
  bump (inj₂ _) β = β

  addN  : (k : LH) → Wd (Lv k) → Wd (Lv k)
  addSt : (x : LH) → Wd (step (Lv x)) → Wd (step (Lv x))
  addSt x w = addN x (proj₁ w) , bump (eqN j x) (proj₂ w)
  addN lz w = w
  addN (ls x) w = addSt x w
  addN (ll f) w = λ i → addN (f i) (w i)
  addN (lΩ k g) w = λ { (inj₁ tt) → addSt k (w (inj₁ tt)) ; (inj₂ c) → addN (g c) (w (inj₂ c)) }

  bump-fst : ∀ {x} (m : (num j ≡ x) ⊎ ⊤) β {w} → β ⊲[ w ] bump m β
  bump-fst (inj₁ e) β = ⊞-fst β (cast e)
  bump-fst (inj₂ _) β = hself

  addN≤  : ∀ k w → _≤w_ (Lv k) w (addN k w)
  addSt≤ : ∀ x w → _≤w_ (step (Lv x)) w (addSt x w)
  addSt≤ x w = addN≤ x (proj₁ w) , bump-fst (eqN j x) (proj₂ w)
  addN≤ lz w = λ ()
  addN≤ (ls x) w = addSt≤ x w
  addN≤ (ll f) w = λ i → addN≤ (f i) (w i)
  addN≤ (lΩ k g) w = λ { (inj₁ tt) → addSt≤ k (w (inj₁ tt)) ; (inj₂ c) → addN≤ (g c) (w (inj₂ c)) }

  module _ (lδ : LgB δ) where
    Lg-cast : ∀ {x} (e : num j ≡ x) → LgB (cast e)
    Lg-cast refl = lδ

    Lg-bump : ∀ {x} (m : (num j ≡ x) ⊎ ⊤) β → LgB β → LgB (bump m β)
    Lg-bump (inj₁ e) β l = Lg-⊞ β (cast e) l (Lg-cast e)
    Lg-bump (inj₂ _) β l = l

    Lg-addN  : ∀ k w → LgW (Lv k) w → LgW (Lv k) (addN k w)
    Lg-addSt : ∀ x w → LgW (step (Lv x)) w → LgW (step (Lv x)) (addSt x w)
    Lg-addSt x w l = Lg-addN x (proj₁ w) (proj₁ l) , Lg-bump (eqN j x) (proj₂ w) (proj₂ l)
    Lg-addN lz w l = l
    Lg-addN (ls x) w l = Lg-addSt x w l
    Lg-addN (ll f) w l = λ i → Lg-addN (f i) (w i) (l i)
    Lg-addN (lΩ k g) w l = λ { (inj₁ tt) → Lg-addSt k (w (inj₁ tt)) (l (inj₁ tt)) ; (inj₂ c) → Lg-addN (g c) (w (inj₂ c)) (l (inj₂ c)) }
```

## §3 成员: 级为 `num j` 的新种类的一切位置

```agda
module Pos (j : ℕ) where
  PosN  : LH → Set
  PosSt : LH → Set
  PosSt x = (num j ≡ x) ⊎ PosN x
  PosN lz = ⊥
  PosN (ls x) = PosSt x
  PosN (ll f) = Σ ℕ (λ i → PosN (f i))
  PosN (lΩ k g) = PosSt k ⊎ Σ (HB (Lv k)) (λ c → PosN (g c))

  kN  : ∀ k → PosN k → K (Lv k)
  kSt : ∀ x → PosSt x → K (step (Lv x))
  kSt x (inj₁ e) = inj₂ tt
  kSt x (inj₂ p) = inj₁ (kN x p)
  kN lz ()
  kN (ls x) p = kSt x p
  kN (ll f) (i , p) = i , kN (f i) p
  kN (lΩ k g) (inj₁ p) = inj₁ tt , kSt k p
  kN (lΩ k g) (inj₂ (c , p)) = inj₂ c , kN (g c) p

  uncast : ∀ {x} → num j ≡ x → HB (Lv x) → HB (Lv (num j))
  uncast refl b = b

  coN  : ∀ k (p : PosN k) → E (Lv k) (kN k p) → HB (Lv (num j))
  coSt : ∀ x (p : PosSt x) → E (step (Lv x)) (kSt x p) → HB (Lv (num j))
  coSt x (inj₁ e) b = uncast e b
  coSt x (inj₂ p) b = coN x p b
  coN lz ()
  coN (ls x) p b = coSt x p b
  coN (ll f) (i , p) b = coN (f i) p b
  coN (lΩ k g) (inj₁ p) b = coSt k p b
  coN (lΩ k g) (inj₂ (c , p)) b = coN (g c) p b
```

**升后的顶 (对一切位置).** 位置是新种类本身时, 用 `eqN-num` 把判定的结果换成 `refl`.

```agda
  module _ (δ : HB (Lv (num j))) where
    open Add j δ

    top-new : ∀ {x} (e : num j ≡ x) β → uncast e (bump (eqN j x) β) ≡ uncast e β ⊞ δ
    top-new refl β = cong (λ m → bump m β) (eqN-num j)

    top-addN  : ∀ k (p : PosN k) w → coN k p (top (Lv k) (kN k p) (addN k w)) ≡ coN k p (top (Lv k) (kN k p) w) ⊞ δ
    top-addSt : ∀ x (p : PosSt x) w → coSt x p (top (step (Lv x)) (kSt x p) (addSt x w)) ≡ coSt x p (top (step (Lv x)) (kSt x p) w) ⊞ δ
    top-addSt x (inj₁ e) w = top-new e (proj₂ w)
    top-addSt x (inj₂ p) w = top-addN x p (proj₁ w)
    top-addN lz () w
    top-addN (ls x) p w = top-addSt x p w
    top-addN (ll f) (i , p) w = top-addN (f i) p (w i)
    top-addN (lΩ k g) (inj₁ p) w = top-addSt k p (w (inj₁ tt))
    top-addN (lΩ k g) (inj₂ (c , p)) w = top-addN (g c) p (w (inj₂ c))
```

**种类查成员.** 对种类结构递归; 只在新种类处判定层号是否是 `num j` (`eqN`).

```agda
  Mem : ∀ k → K (Lv k) → Set
  Mem k κ = Σ (PosN k) (λ p → kN k p ≡ κ)

  MemSt : ∀ x → K (step (Lv x)) → Set
  MemSt x κ = Σ (PosSt x) (λ p → kSt x p ≡ κ)

  memN  : ∀ k (κ : K (Lv k)) → Mem k κ ⊎ ⊤
  memSt : ∀ x (κ : K (step (Lv x))) → MemSt x κ ⊎ ⊤
  memSt x (inj₂ tt) = map₁ (λ e → inj₁ e , refl) (eqN j x)
  memSt x (inj₁ κ) = map₁ (λ m → inj₂ (proj₁ m) , cong inj₁ (proj₂ m)) (memN x κ)
  memN lz (() , _)
  memN (ls x) κ = memSt x κ
  memN (ll f) (i , κ) = map₁ (λ m → (i , proj₁ m) , cong (i ,_) (proj₂ m)) (memN (f i) κ)
  memN (lΩ k g) (inj₁ tt , κ) = map₁ (λ m → inj₁ (proj₁ m) , cong (inj₁ tt ,_) (proj₂ m)) (memSt k κ)
  memN (lΩ k g) (inj₂ c , κ) = map₁ (λ m → inj₂ (c , proj₁ m) , cong (inj₂ c ,_) (proj₂ m)) (memN (g c) κ)
```

## §4 `slotUp j`: 一切站里级为 `num j` 的拷贝

```agda
slotUp : ∀ j → Up SLs (Lv (num j))
slotUp j = record
  { J = Σ ℕ (λ m → PosSt (st m))
  ; κJ = λ mp → proj₁ mp , kSt (st (proj₁ mp)) (proj₂ mp)
  ; co = λ mp → coSt (st (proj₁ mp)) (proj₂ mp)
  ; rz = λ δ w m → Add.addSt j δ (st m) (w m)
  ; rz≤ = λ δ w m → Add.addSt≤ j δ (st m) (w m)
  ; rzLg = λ {δ} {w} lδ lw m → Add.Lg-addSt j δ lδ (st m) (w m) (lw m)
  ; rz-top = λ mp δ w → top-addSt δ (st (proj₁ mp)) (proj₂ mp) (w (proj₁ mp)) }
  where open Pos j

-- 一个站的种类查成员
memS : ∀ j m (κ : K (FS m)) → Σ (Up.J (slotUp j)) (λ i → Up.κJ (slotUp j) i ≡ (m , κ)) ⊎ ⊤
memS j m κ = map₁ (λ q → (m , proj₁ q) , cong (m ,_) (proj₂ q)) (Pos.memSt j (st m) κ)
```
