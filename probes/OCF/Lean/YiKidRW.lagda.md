# 孩子单调: 精简块的实填与违反

> 验收文件 (读回的值序取 `OCF.Align.Value`). 判决: 编译定理, 无前提. 精简块填进 `YiKidCrit.KidFrame` (`RW`); 一切树版在一切有孩子的层号, 一切证据, 一切左边 x, 一切孩子 c 上无界 (`rw-unb`), 所以只要有 c ⋖ c′ 就不成立 (`rw-¬all`, 实例 `rw-¬all-tw1`).
> `inversion⁺` 经 YiBR 的关系搬到精简块 (`inversion⁺ᴿ`), 非严格的 `inversionᴿ` 同样; 后继严格 (`suc-strict`, 一切层号); 所以任何含 `Y₁ᴿ + 1` 的量化域上判据不成立 (`rw-¬inv`, 也由吸收加严格后继得出: `rw-¬absorb`).
> 机制对塔第 1 项的一切孩子 c: 孩子 c+1 进孩子 tt 之后的底与孩子 c 的底逐字相同 (`base-sameᴿ`), c+1 的 Ω 树的折叠是孩子 c 的一列树的折叠的部分和极限 (`lhs-formᴿ`), 都是 `refl`. 不否定什么: `OnlyΩ` 上的判据没有判决.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKidRW where

open import Data.Nat using (ℕ; zero; suc) renaming (_<_ to _<ᴺ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold
open import OCF.Lean.YiRWCheck using (¬◃z)
open import OCF.Lean.YiBRValue using (readRW; rel≅)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; zs-R)
open import OCF.Lean.YiBRFold using (S; cΩ; B₀-R; iterR)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; ψ₀-R)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
import OCF.Lean.YiInv as I
import OCF.Lean.YiT2Frame as F2
import OCF.Lean.YiLSTw1 as F1
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≅→≼)
open import OCF.Lean.YiKidCrit
```

## 精简块填进框架

孩子字面上更高: Ω 形状是下标层的第一位置序, ℕ 极限形状是编号的 `<`, 后继形状只有一个孩子. 值的严格性 `irrᴼ` 对第 0 层的一切读回值成立.

```agda
Lk : {ℓ : L} → CH ℓ → CH ℓ → Set
Lk {nd (sΩ k) h} c c′ = k ⊢ c ◃ c′
Lk {nd sL g}     m n  = m <ᴺ n
Lk {_}           _ _  = ⊥

KTᴿ : (ℓ : L) → CH ℓ → Set
KTᴿ ℓ c = Σ (ChT ℓ c) (RCh ℓ c (chZ ℓ c))

upᴿ : {ℓ : L} → Tr ℓ → (c : CH ℓ) → KTᴿ ℓ c → Tr ℓ
upᴿ x c (y , e) = up x c y e

ΩKᴿ : (ℓ : L) (c : CH ℓ) → KTᴿ ℓ c
ΩKᴿ (nd s h) c = Ωt (h c)

irrᴼ : (v : L.Ordᶜ L.zero) {u : L.Ordᶜ L.zero} → L.suc u ≼ v → v ≼ u → ⊥
irrᴼ L.zero        ()
irrᴼ (L.suc v)     (s≼s p)  q = irrᴼ v (≼-trans q p) (≼-refl v)
irrᴼ (L.lim f)     (≼l n p) q = irrᴼ (f n) p (≼-trans (≼l n (≼-refl (f n))) q)
irrᴼ (L.limᵢ () f)
irrᴼ (L.up () y)

val : (ℓ : L) → Ok ℓ → Tr ℓ → L.Ordᶜ L.zero
val ℓ o x = readRW (proj₁ (ψ₀ ℓ o x))

RW : KidFrame
RW = record
  { Lv = L ; Ok = Ok ; Tr = Tr ; Kid = CH ; KT = KTᴿ ; _⋖_ = Lk ; up = upᴿ ; ΩK = ΩKᴿ
  ; V = L.Ordᶜ L.zero ; _≼_ = _≼_ ; ≼-trans = ≼-trans ; osuc = L.suc
  ; irr = λ {u} {v} p q → irrᴼ v p q
  ; val = val }

open Crit RW
```

## 一切树版: 第 0 层的折叠不低于被嵌入的可数树

`next⁺` 严格增 (`next-gt`); 所以沿 `ι` 嵌入的可数树 Z 的折叠不低于 Z (`infl`, 对一切层号, 底, 路径).

```agda
le+ : (x y : Tr zero) → readRW x ≼ readRW (x + y)
le+ x zero      = ≼-refl _
le+ x (suc y)   = ≼-suc (le+ x y)
le+ x (lim f a) = ≼l 0 (le+ x (f 0))

lt+ : (x y : Tr zero) → zero ⊢ zero ◃ y → L.suc (readRW x) ≼ readRW (x + y)
lt+ x zero      d = ⊥-elim (¬◃z d)
lt+ x (suc y)   d = s≼s (le+ x y)
lt+ x (lim f a) d = ≼l 1 (lt+ x (f 1) (z◃ (f 0) (a 0)))

next-gt : (b : Tr⁺ zero) → L.suc (readRW (proj₁ b)) ≼ readRW (proj₁ (next⁺ b))
next-gt (b , nb) = ≼l 1 (lt+ b b nb)

infl : (ℓ : L) (o : Ok ℓ) (B : Base ℓ) (w : zero ≤ ℓ) (β : Tr⁺ zero) (Z : Tr zero)
     → readRW Z ≼ readRW (proj₁ (ψ ℓ o B zero w β (ι ℓ Z)))
infl ℓ o B w β zero      = z≼
infl ℓ o B w β (suc Z)   = ≼-trans (s≼s (infl ℓ o B w β Z)) (next-gt (ψ ℓ o B zero w β (ι ℓ Z)))
infl ℓ o B w β (lim f a) = l≼ (λ n → ≼l n (infl ℓ o B w β (f n)))
```

孩子 c 里嵌入 `ι (Z+1)`, Z 是同层任一棵树 t 的折叠: 值严格高于 t 的值.

```agda
grow : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (x : Tr (nd s h)) (c : Ch s) → Grow (nd s h) o x c
grow s h o x c t =
  (ι (h c) (suc Z) , ι-mono (h c) (z◃ Z ◃s)) ,
  infl (h c) (proj₂ o c) (λ i u → ψ (nd s h) o (B₀ (nd s h)) i (inc c u) (B₀ (nd s h) i (inc c u)) x) (z≤ (h c))
       (ψ (nd s h) o (B₀ (nd s h)) zero (z≤ (nd s h)) (Ωt zero) x) (suc Z)
  where
  Z : Tr zero
  Z = proj₁ (ψ₀ (nd s h) o t)

rw-unb : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (x : Tr (nd s h)) (c : Ch s) → Unb All (nd s h) o x c
rw-unb s h o x c = grow→unb (grow s h o x c)

rw-¬all : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (x : Tr (nd s h)) (c c′ : Ch s) → Lk {nd s h} c c′
        → KidMono All → ⊥
rw-¬all s h o x c c′ r = unb→¬mono All (nd s h) o x c c′ r (rw-unb s h o x c)

rw-¬all-tw1 : KidMono All → ⊥
rw-¬all-tw1 = rw-¬all (sΩ zero) _ (Ok-tw 1) (proj₁ (Ωt (tw 1))) (suc zero) (suc (suc zero)) ◃s
```

后继严格 (一切层号, 一切 x, c, y): 嵌入 y+1 的值严格高于嵌入 y 的.

```agda
suc-strict : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → L.suc (val (nd s h) o (up x c y e)) ≼ val (nd s h) o (up x c (suc y) (z◃ y ◃s))
suc-strict s h o x c y e =
  next-gt (ψ (h c) (proj₂ o c) (λ i u → ψ (nd s h) o (B₀ (nd s h)) i (inc c u) (B₀ (nd s h) i (inc c u)) x) zero (z≤ (h c))
            (ψ (nd s h) o (B₀ (nd s h)) zero (z≤ (nd s h)) (Ωt zero) x) y)
```

## 塔第 1 项: 机制对一切孩子 c

`Bc c`: 孩子 c 的底 (左边是 β, 即 `tw 1` 的 Ω 树). 孩子 c+1 嵌入零之后进孩子 tt 的底与 `Bc c` 逐字相同; 孩子 c+1 的 Ω 树的折叠是 "孩子 c 里嵌入 z+1" 的折叠沿一条链的部分和极限.

```agda
hᴿ : Tr zero → L
hᴿ c = zero ⊕ ↑ zero c

βᴿ : Tr (tw 1)
βᴿ = proj₁ (Ωt (tw 1))

o₁ : Ok (tw 1)
o₁ = Ok-tw 1

Bc : (c : Tr zero) → Base (hᴿ c)
Bc c i u = ψ (tw 1) o₁ (B₀ (tw 1)) i (inc c u) (B₀ (tw 1) i (inc c u)) βᴿ

b₁ : Tr⁺ zero
b₁ = ψ (tw 1) o₁ (B₀ (tw 1)) zero (z≤ (tw 1)) (Ωt zero) βᴿ

base-sameᴿ : (c : Tr zero)
  → (λ i u → ψ (hᴿ (suc c)) (proj₂ o₁ (suc c)) (Bc (suc c)) i (inc tt u) (Bc (suc c) i (inc tt u)) zero) ≡ Bc c
base-sameᴿ c = refl

rowᴿ : (c : Tr zero) → Tr (hᴿ c) → Tr⁺ zero
rowᴿ c z = ψ (hᴿ c) (proj₂ o₁ c) (Bc c) zero (z≤ (hᴿ c)) b₁ (suc z)

row-form : (c : Tr zero) (z : Tr (hᴿ c)) → rowᴿ c z ≡ ψ₀ (tw 1) o₁ (up βᴿ c (suc z) (z◃ z ◃s))
row-form c z = refl

chainᴿ : (c : Tr zero) → Tr (hᴿ c) → Tr (hᴿ c)
chainᴿ c z = proj₁ (ψ (hᴿ (suc c)) (proj₂ o₁ (suc c)) (Bc (suc c)) (hᴿ c) (inc tt self)
                      (Bc (suc c) (hᴿ c) (inc tt self)) (up zero tt (suc z) (z◃ z ◃s)))

lhs-formᴿ : (c : Tr zero)
  → ψ₀ (tw 1) o₁ (up βᴿ (suc c) (proj₁ (Ωt (hᴿ (suc c)))) (proj₂ (Ωt (hᴿ (suc c)))))
  ≡ limc⁺ (λ n → rowᴿ c (iter (chainᴿ c) zero n))
lhs-formᴿ c = refl
```

## 实例: `inversion⁺` 搬到精简块

链 `zzᴿ` 与见证 `Y₁ᴿ` 与 YiInv 同文 (孩子 two 的链, 孩子 one 的树); 关系由 YiBR 的 `S` 给出.

```agda
oneᴿ twoᴿ : Tr zero
oneᴿ = suc zero
twoᴿ = suc oneᴿ

zzᴿ : ℕ → Tr (hᴿ oneᴿ)
zzᴿ = iter (chainᴿ oneᴿ) zero

selᴿ : {A : Set} → Tr zero → A → A → A
selᴿ zero      x y = x
selᴿ (suc _)   x y = y
selᴿ (lim _ _) x y = y

Tw₁ : ℕ → Tr (hᴿ oneᴿ)
Tw₁ zero    = zero
Tw₁ (suc n) = Ω (inj₂ (tt , inj₁ tt)) (λ c → selᴿ c (Tw₁ n) (up (zzᴿ n) tt (suc c) (z◃ c ◃s)))

Y₁ᴿ : Tr (hᴿ oneᴿ)
Y₁ᴿ = lim Tw₁ (λ n → ◃w)

Y₁-nz : hᴿ oneᴿ ⊢ zero ◃ Y₁ᴿ
Y₁-nz = ◃l zero
```

关系.

```agda
eΩ-c : ∀ {k h k′ h′ o ε ρ} → RelE (nd (sΩ k) h) (F.Ωₗ k′ h′) o ε ρ → (c : Tr k) (c′ : F.Tr k′) → RelT k k′ c c′
     → RelE (h c) (h′ c′) (proj₂ o c) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)
eΩ-c (eΩ _ _ rc) = rc

r₁ : RelT zero F.zero oneᴿ F2.one
r₁ = is iz

r₂ : RelT zero F.zero twoᴿ F2.two
r₂ = is (is iz)

re₁ = eΩ-c (tw-E 1) oneᴿ F2.one r₁
re₂ = eΩ-c (tw-E 1) twoᴿ F2.two r₂
rl₁ = E→L re₁
rl₂ = E→L re₂

rβ : RelT (tw 1) (F.tw 1) βᴿ F2.β
rβ = Ωt-R (tw-L 1)

rB₂ : RelBase (hᴿ twoᴿ) (F1.h₁ F2.two) (Bc twoᴿ) I.BW
rB₂ = cΩ (tw-E 1) (B₀ (tw 1)) (F.B₀ (F.tw 1)) (B₀-R (tw-L 1)) rβ twoᴿ F2.two r₂

zz-R : (n : ℕ) → RelT (hᴿ oneᴿ) (F1.h₁ F2.one) (zzᴿ n) (I.zz n)
zz-R = iterR (RelT (hᴿ oneᴿ) (F1.h₁ F2.one)) iz λ z z′ rz →
  let rb = rB₂ (hᴿ oneᴿ) I.L1 (inc tt self) (F.ins F.self) (wincS wself)
  in proj₁ (S re₂ (Bc twoᴿ) I.BW rB₂ (wincS wself) (Bc twoᴿ (hᴿ oneᴿ) (inc tt self)) (proj₁ rb) (proj₂ rb)
              (iu (iz , (is rz , zs-R rl₁ rz))))

sel-R : {A A′ : Set} (Q : A → A′ → Set) {c : Tr zero} {c′ : F.Tr F.zero} → RelT zero F.zero c c′
      → {x y : A} {x′ y′ : A′} → Q x x′ → Q y y′ → Q (selᴿ c x y) (I.sel c′ x′ y′)
sel-R Q {c = zero}    iz     qx qy = qx
sel-R Q {c = suc _}   (is _) qx qy = qy
sel-R Q {c = lim _ _} (il _) qx qy = qy

mutual
  Tw-R : (n : ℕ) → RelT (hᴿ oneᴿ) (F1.h₁ F2.one) (Tw₁ n) (I.Tw F.zero I.S₁ n)
  Tw-R zero    = iz
  Tw-R (suc n) = iw (Tw-Ω n)

  Tw-Ω : (n : ℕ) → RelP (hᴿ oneᴿ) (F1.h₁ F2.one) (inj₂ (tt , inj₁ tt)) (inj₁ tt)
    × ((z : Tr zero) (z′ : F.Tr F.zero) → RelT zero F.zero z z′
       → RelT (hᴿ oneᴿ) (F1.h₁ F2.one) (selᴿ z (Tw₁ n) (up (zzᴿ n) tt (suc z) (z◃ z ◃s))) (I.sel z′ (I.Tw F.zero I.S₁ n) (I.S₁ n z′)))
  Tw-Ω n = i₁ tt , λ z z′ rz → sel-R (RelT (hᴿ oneᴿ) (F1.h₁ F2.one)) rz (Tw-R n) (iu (zz-R n , (is rz , zs-R lz rz)))

Y₁-R : RelT (hᴿ oneᴿ) (F1.h₁ F2.one) Y₁ᴿ I.Y₁
Y₁-R = il (Tw-R , λ n → dw (Tw-Ω n))
```

两边的树相关, 值经 `rel≅` 搬过来.

```agda
lhsᴿ rhs₀ᴿ rhsᴿ : Tr (tw 1)
lhsᴿ  = up βᴿ twoᴿ (proj₁ (Ωt (hᴿ twoᴿ))) (proj₂ (Ωt (hᴿ twoᴿ)))
rhs₀ᴿ = up βᴿ oneᴿ Y₁ᴿ Y₁-nz
rhsᴿ  = up βᴿ oneᴿ (suc Y₁ᴿ) (z◃ Y₁ᴿ ◃s)

lhs-R : RelT (tw 1) (F.tw 1) lhsᴿ (F.up F2.β F2.two (F.Ωt (F1.h₁ F2.two)) (F.Ωt-nz (F1.h₁ F2.two)))
lhs-R = iu (rβ , (r₂ , Ωt-R rl₂ , Ωn-R rl₂))

rhs₀-R : RelT (tw 1) (F.tw 1) rhs₀ᴿ (F.up F2.β F2.one I.Y₁ (I.Yw-nz F.zero I.S₁))
rhs₀-R = iu (rβ , (r₁ , Y₁-R , dl))

rhs-R : RelT (tw 1) (F.tw 1) rhsᴿ (F.up F2.β F2.one (F.suc I.Y₁) (F.z◃s I.Y₁))
rhs-R = iu (rβ , (r₁ , is Y₁-R , zs-R rl₁ Y₁-R))

to≼ : {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′ → readRW x ≼ read x′
to≼ r = ≅→≼ (rel≅ r)

from≼ : {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′ → read x′ ≼ readRW x
from≼ r = ≅→≼ (L.≅-sym (rel≅ r))

inversionᴿ : val (tw 1) o₁ lhsᴿ ≼ val (tw 1) o₁ rhs₀ᴿ
inversionᴿ = ≼-trans (to≼ (ψ₀-R (tw-E 1) lhs-R)) (≼-trans I.inversion (from≼ (ψ₀-R (tw-E 1) rhs₀-R)))

inversion⁺ᴿ : L.suc (val (tw 1) o₁ lhsᴿ) ≼ val (tw 1) o₁ rhsᴿ
inversion⁺ᴿ = ≼-trans (s≼s (to≼ (ψ₀-R (tw-E 1) lhs-R))) (≼-trans I.inversion⁺ (from≼ (ψ₀-R (tw-E 1) rhs-R)))
```

## 判据的违反

任何量化域 D, 只要含 `(tw 1, β, 孩子 one, Y₁ᴿ + 1)`, 判据就不成立; 两种证法: 直接用严格倒置, 或用非严格的吸收加后继严格.

```agda
rw-¬inv : (D : Dom) → D (tw 1) o₁ βᴿ oneᴿ (suc Y₁ᴿ , z◃ Y₁ᴿ ◃s) → KidMono D → ⊥
rw-¬inv D d = strict→¬mono D (tw 1) o₁ βᴿ oneᴿ twoᴿ ◃s (suc Y₁ᴿ , z◃ Y₁ᴿ ◃s) d inversion⁺ᴿ

rw-¬absorb : (D : Dom) → D (tw 1) o₁ βᴿ oneᴿ (suc Y₁ᴿ , z◃ Y₁ᴿ ◃s) → KidMono D → ⊥
rw-¬absorb D d = absorb→¬mono D (tw 1) o₁ βᴿ oneᴿ twoᴿ ◃s (Y₁ᴿ , Y₁-nz) (suc Y₁ᴿ , z◃ Y₁ᴿ ◃s) d inversionᴿ
  (suc-strict (sΩ zero) _ o₁ βᴿ oneᴿ Y₁ᴿ Y₁-nz)
```
