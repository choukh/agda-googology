# 折叠输出与 `Cv` (二): 折叠走第 0 层坐标, 对规范坐标值不变

> 不含记号. 入口 [CvFold](CvFold.lagda.md). 对象是 `SumOneClosed` (即 `SumOneFold` 取 $S=\cdot\omega$) 的 `Run`, 输入是第 0 层的差树 $z$ (这正是 `ni` 节点分支里折叠走坐标的那一步, `SumOneFold.BNi`).
>
> 固定世界 $W$, 目标第 1 层 ($\tau=$ `inj₁ t1`), 一个动作 `A₀`. `v Y`: 状态在目标第 1 层的值 (`toB` 的值). `Out z Y = v (Y ⊕ Run z Y)`: 走完 $z$ 之后的值.
>
> - 前提 `HA`: 动作一步之后的值只单调地依赖动作之前的值 (与坐标无关).
> - `z ⊑ᴼ z′`: 对一切起点, $v$ 小的起点走 $z$ 不超过 $v$ 大的起点走 $z'$.
> - **`canon`**: `cw z ~ᴼ z`. 即走规范坐标与走原坐标值相等.
> - 证明只用和的结构: 单位 (`unit-l`, `unit-r`), 结合 (`assoc`), 平移不变 (`TI`), 加法分解 (`DEC`), 以及 `toA` 与 `dif` 的往返 (`C`, `ZL`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.SumOneClosed as F
open import OCF.Align.SumOneTree using (cnt)
open import OCF.Align.LayerTrBase using (B₁; _≼_)
open import OCF.Align.LayerTrOne using (one)
module OCF.Align.CvFoldRun {W : A} (lW : Lg W) (t1 : one ⊲ W) (ac : F.AccY (cnt azero)) (ll : azero ⊲ W) (A₀ : F.Ig (cnt azero) W) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import OCF.Align.CumReadCF using (z⊲; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_⊞_)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.BrwMidZero using (dif; toA; ⊞-fst; ⊞-⊲; Lg-⊞; pts; _+ᴸ_)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (S; Sp; toB)
open import OCF.Align.LayerTrRound using (cw)
```

## §1 值与走

```agda
τ₁ : C.Tg one W
τ₁ = inj₁ t1

v : F.St W → B₁ W
v Y = S C.self lW bz (F.yc (F.d Y) τ₁ tt)

R : ∀ {W₀} → D azero W₀ → W₀ ⊲ W → D azero W → F.St W → F.Df W
R z q w Y = F.Run ac z q lW ll A₀ w Y

Out : ∀ {W₀} → D azero W₀ → W₀ ⊲ W → D azero W → F.St W → B₁ W
Out z q w Y = v (Y F.⊕ R z q w Y)

HA : Set
HA = ∀ w w′ Y Y′ → v Y ≼ v Y′ → v (Y F.⊕ A₀ C.self lW w Y) ≼ v (Y′ F.⊕ A₀ C.self lW w′ Y′)

infix 4 _⊑ᴼ_ _~ᴼ_
_⊑ᴼ_ : ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
z ⊑ᴼ z′ = ∀ q q′ w w′ Y Y′ → v Y ≼ v Y′ → Out z q w Y ≼ Out z′ q′ w′ Y′

_~ᴼ_ : ∀ {V₁ V₂} → D azero V₁ → D azero V₂ → Set
z ~ᴼ z′ = (z ⊑ᴼ z′) × (z′ ⊑ᴼ z)
```

## §2 走的结构

```agda
-- 极限的部分和就是 Rpt 的状态的值
Sp≡ : ∀ {W₀} (d : ℕ → D azero W₀) (q : W₀ ⊲ W) w Y n →
      Sp C.self lW (v Y) (λ m → F.yc (R (d m) q (proj₁ (F.Rpt ac d q lW ll A₀ w Y m)) (proj₂ (F.Rpt ac d q lW ll A₀ w Y m))) τ₁ tt) n
      ≡ v (proj₂ (F.Rpt ac d q lW ll A₀ w Y n))
Sp≡ d q w Y zero = refl
Sp≡ d q w Y (suc n) = cong (λ c → S C.self lW c (F.yc (R (d n) q _ _) τ₁ tt)) (Sp≡ d q w Y n)

module _ (ha : HA) where

  ⨾-mono : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → x ⊑ᴼ x′ → y ⊑ᴼ y′ → (x ⨾ y) ⊑ᴼ (x′ ⨾ y′)
  ⨾-mono hx hy q q′ w w′ Y Y′ r = hy q q′ _ _ _ _ (hx q q′ w w′ Y Y′ r)

  nl-mono : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → d n ⊑ᴼ d′ n) → nl d ⊑ᴼ nl d′
  nl-mono {d = d} {d′} h q q′ w w′ Y Y′ r = l≼ (λ n → ≼l n (subst₂ (Sp≡ d q w Y n) (Sp≡ d′ q′ w′ Y′ n) (go n)))
    where
    subst₂ : ∀ {a a′ b b′ : B₁ W} → a ≡ a′ → b ≡ b′ → a′ ≼ b′ → a ≼ b
    subst₂ refl refl h = h
    go : ∀ n → v (proj₂ (F.Rpt ac d q lW ll A₀ w Y n)) ≼ v (proj₂ (F.Rpt ac d′ q′ lW ll A₀ w′ Y′ n))
    go zero = r
    go (suc n) = h n q q′ _ _ _ _ (go n)

  nw-l : ∀ {V₀ V V₂} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₂} → x ⊑ᴼ z → nw p x ⊑ᴼ z
  nw-l {p = p} h q q′ w w′ Y Y′ r = h (⊲-tr p q) q′ w w′ Y Y′ r

  nw-r : ∀ {V₀ V V₁} {p : V₀ ⊲ V} {x : D azero V₀} {z : D azero V₁} → z ⊑ᴼ x → z ⊑ᴼ nw p x
  nw-r {p = p} h q q′ w w′ Y Y′ r = h q (⊲-tr p q′) w w′ Y Y′ r

  refl⊑ : ∀ {V} (z : D azero V) → z ⊑ᴼ z
  refl⊑ n0 q q′ w w′ Y Y′ r = r
  refl⊑ n1 q q′ w w′ Y Y′ r = ha w w′ Y Y′ r
  refl⊑ (x ⨾ y) = ⨾-mono (refl⊑ x) (refl⊑ y)
  refl⊑ (nl d) = nl-mono (λ n → refl⊑ (d n))
  refl⊑ (ni () u)
  refl⊑ (nκ () u)
  refl⊑ (nw p x) = nw-l (nw-r (refl⊑ x))

  refl~ : ∀ {V} (z : D azero V) → z ~ᴼ z
  refl~ z = refl⊑ z , refl⊑ z

  sym~ : ∀ {V₁ V₂} {z : D azero V₁} {z′ : D azero V₂} → z ~ᴼ z′ → z′ ~ᴼ z
  sym~ (h , h′) = h′ , h

  tr⊑ : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → z ⊑ᴼ z′ → z′ ⊑ᴼ z″ → z ⊑ᴼ z″
  tr⊑ h h′ q q″ w w″ Y Y″ r = ≼-trans (h q q w w Y Y (≼-refl _)) (h′ q q″ w w″ Y Y″ r)

  tr⊑ʳ : ∀ {V V₁} {z : D azero V₁} {z′ z″ : D azero V} → z ⊑ᴼ z′ → z′ ⊑ᴼ z″ → z ⊑ᴼ z″
  tr⊑ʳ h h′ q q″ w w″ Y Y″ r = ≼-trans (h q q″ w w″ Y Y″ r) (h′ q″ q″ w″ w″ Y″ Y″ (≼-refl _))

  tr~ : ∀ {V V₃} {z z′ : D azero V} {z″ : D azero V₃} → z ~ᴼ z′ → z′ ~ᴼ z″ → z ~ᴼ z″
  tr~ (a , a′) (b , b′) = tr⊑ a b , tr⊑ʳ b′ a′

  ⨾~ : ∀ {V₁ V₂} {x y : D azero V₁} {x′ y′ : D azero V₂} → x ~ᴼ x′ → y ~ᴼ y′ → (x ⨾ y) ~ᴼ (x′ ⨾ y′)
  ⨾~ (a , a′) (b , b′) = ⨾-mono a b , ⨾-mono a′ b′

  nl~ : ∀ {V₁ V₂} {d : ℕ → D azero V₁} {d′ : ℕ → D azero V₂} → (∀ n → d n ~ᴼ d′ n) → nl d ~ᴼ nl d′
  nl~ h = nl-mono (λ n → proj₁ (h n)) , nl-mono (λ n → proj₂ (h n))

  nw~ : ∀ {V₀ V} {p : V₀ ⊲ V} (x : D azero V₀) → nw p x ~ᴼ x
  nw~ x = nw-l (refl⊑ x) , nw-r (refl⊑ x)
```

**单位与结合.** 走 `n0` 不改值; $(x⨾y)⨾z$ 与 $x⨾(y⨾z)$ 走完的状态不同, 但值相同, 坐标由 `HA` 吸收.

```agda
  unit-l : ∀ {V} (x : D azero V) → (n0 ⨾ x) ~ᴼ x
  unit-l x = (λ q q′ w w′ Y Y′ r → refl⊑ x q q′ _ w′ _ Y′ r) , (λ q q′ w w′ Y Y′ r → refl⊑ x q q′ w _ Y _ r)

  unit-r : ∀ {V} (x : D azero V) → (x ⨾ n0) ~ᴼ x
  unit-r x = (λ q q′ w w′ Y Y′ r → refl⊑ x q q′ w w′ Y Y′ r) , (λ q q′ w w′ Y Y′ r → refl⊑ x q q′ w w′ Y Y′ r)

  assoc : ∀ {V} (x y z : D azero V) → ((x ⨾ y) ⨾ z) ~ᴼ (x ⨾ (y ⨾ z))
  assoc x y z =
    (λ q q′ w w′ Y Y′ r → refl⊑ z q q′ _ _ _ _ (refl⊑ y q q′ _ _ _ _ (refl⊑ x q q′ w w′ Y Y′ r))) ,
    (λ q q′ w w′ Y Y′ r → refl⊑ z q q′ _ _ _ _ (refl⊑ y q q′ _ _ _ _ (refl⊑ x q q′ w w′ Y Y′ r)))
```

## §3 `dif` 与 `toA` 的形状

**平移不变** `TI`: 沿 $coxplus q$ 读的差与沿 $q$ 读的差走起来值相同.

```agda
  TI : ∀ {V} c e {x} (q : x ⊲ e) (lc : Lg c) (le : Lg e) → dif {V} (c ⊞ e) (⊞-⊲ c q) (Lg-⊞ c e lc le) ~ᴼ dif {V} e q le
  TI c e C.self lc le = (λ q q′ w w′ Y Y′ r → r) , (λ q q′ w w′ Y Y′ r → r)
  TI c (asuc e) (C.suc q) lc le = ⨾~ (TI c e q lc le) (refl~ n1)
  TI c (alim h) (C.lim n q) lc (st , wl) =
    ⨾~ (TI c (h n) q lc (wl n)) (nl~ (λ m → TI c (h (suc (m + n))) (st (m + n)) lc (wl (suc (m + n)))))
```

**加法分解** `DEC`: $aoxplus(Xoxplus B)$ 的差走起来等于先走 $aoxplus X$ 的差, 再走 $(aoxplus X)oxplus B$ 的差.

```agda
  DEC : ∀ {V} a X B (la : Lg a) (lx : Lg X) (lB : Lg B) →
        dif {V} (a ⊞ (X ⊞ B)) (⊞-fst a (X ⊞ B)) (Lg-⊞ a (X ⊞ B) la (Lg-⊞ X B lx lB)) ~ᴼ
        (dif {V} (a ⊞ X) (⊞-fst a X) (Lg-⊞ a X la lx) ⨾ dif {V} ((a ⊞ X) ⊞ B) (⊞-fst (a ⊞ X) B) (Lg-⊞ (a ⊞ X) B (Lg-⊞ a X la lx) lB))
  DEC a X azero la lx lB = sym~ (unit-r _)
  DEC a X (asuc B) la lx lB = tr~ (⨾~ (DEC a X B la lx lB) (refl~ n1)) (assoc _ _ _)
  DEC a X (alim h) la lx (st , wl) =
    tr~ (⨾~ (DEC a X (h 0) la lx (wl 0))
            (nl~ (λ m → tr~ (TI a (X ⊞ h (suc (m + 0))) (⊞-⊲ X (st (m + 0))) la (Lg-⊞ X (h (suc (m + 0))) lx (wl (suc (m + 0)))))
                       (tr~ (TI X (h (suc (m + 0))) (st (m + 0)) lx (wl (suc (m + 0))))
                            (sym~ (TI (a ⊞ X) (h (suc (m + 0))) (st (m + 0)) (Lg-⊞ a X la lx) (wl (suc (m + 0)))))))))
        (assoc _ _ _)
```

**往返** `C`: 从 $a$ 起读回 $aoxplus\mathrm{toA}\,z$ 的差, 走起来与 $z$ 相同. `ZL`: 从 $0$ 读与从 $0oxplus$ 读相同.

```agda
  C : ∀ {V W₀} (z : D azero W₀) a (la : Lg a) →
      dif {V} (a ⊞ proj₁ (toA z)) (⊞-fst a (proj₁ (toA z))) (Lg-⊞ a (proj₁ (toA z)) la (proj₂ (toA z))) ~ᴼ z
  C n0 a la = (λ q q′ w w′ Y Y′ r → r) , (λ q q′ w w′ Y Y′ r → r)
  C n1 a la = (λ q q′ w w′ Y Y′ r → ha _ w′ _ Y′ r) , (λ q q′ w w′ Y Y′ r → ha w _ Y _ r)
  C (x ⨾ y) a la =
    tr~ (DEC a (proj₁ (toA x)) (proj₁ (toA y)) la (proj₂ (toA x)) (proj₂ (toA y)))
        (⨾~ (C x a la) (C y (a ⊞ proj₁ (toA x)) (Lg-⊞ a (proj₁ (toA x)) la (proj₂ (toA x)))))
  C {V} (nl d) a la = tr~ (unit-l _) (nl~ E)
    where
    P : ℕ → A
    P k = proj₁ (pts (azero , tt) (λ n → toA (d n)) k)
    lP : ∀ k → Lg (P k)
    lP k = proj₂ (pts (azero , tt) (λ n → toA (d n)) k)
    EL : ℕ → D azero V
    EL m = dif {V} (a ⊞ P (suc (m + 0))) (⊞-⊲ a (⊞-fst (P (m + 0)) (proj₁ (toA (d (m + 0)))))) (Lg-⊞ a (P (suc (m + 0))) la (lP (suc (m + 0))))
    E′ : ∀ m → EL m ~ᴼ d (m + 0)
    E′ m = tr~ (TI a (P (suc (m + 0))) (⊞-fst (P (m + 0)) (proj₁ (toA (d (m + 0))))) la (lP (suc (m + 0))))
               (C (d (m + 0)) (P (m + 0)) (lP (m + 0)))
    E : ∀ m → EL m ~ᴼ d m
    E m = subst (λ j → EL m ~ᴼ d j) (+-identityʳ m) (E′ m)
  C (ni () u) a la
  C (nκ () u) a la
  C (nw p x) a la = let (h , h′) = C x a la in nw-r h , nw-l h′

  ZL : ∀ {V} X (lx : Lg X) → dif {V} X (z⊲ X) lx ~ᴼ dif {V} (azero ⊞ X) (⊞-fst azero X) (Lg-⊞ azero X tt lx)
  ZL azero lx = (λ q q′ w w′ Y Y′ r → r) , (λ q q′ w w′ Y Y′ r → r)
  ZL (asuc X) lx = ⨾~ (ZL X lx) (refl~ n1)
  ZL (alim f) (st , w) =
    ⨾~ (ZL (f 0) (w 0)) (nl~ (λ m → sym~ (TI azero (f (suc (m + 0))) (st (m + 0)) tt (w (suc (m + 0))))))
```

## §4 规范坐标

```agda
  canon : ∀ {W₀} (z : D azero W₀) → cw z ~ᴼ z
  canon z =
    tr~ (unit-l _)
    (tr~ (nw~ (dif (proj₁ (toA z)) (z⊲ (proj₁ (toA z))) (proj₂ (toA z))))
    (tr~ (ZL (proj₁ (toA z)) (proj₂ (toA z)))
         (C z azero tt)))
```
