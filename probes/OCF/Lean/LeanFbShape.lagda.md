# LeanFb (五): 形状定理 — 回灌那一行被执行; 谁被一起升; 剩下的有损种类

> 不含记号. 入口 [LeanFb](LeanFb.lagda.md). 第 4 层 (只新增定理, 不改定义). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 对照 [LeanT](LeanT.lagda.md) §3 的 `old-target` (那里一切目标层只有旧种类, 而旧种类一律有损, 所以任何回灌都不执行) 与否定一路的盲定理 (`NegLeanFbPre.stayFb`, `relevelFb`: 选中回灌行不说明读了数据或升了界; `NegKindLvBlind.relevel`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.LeanFbShape where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTLv
open import OCF.Lean.LeanTTree
open import OCF.Lean.LeanFbIf
open import OCF.Lean.LeanFbSt renaming (st to stL)
open import OCF.Lean.LeanFbSlot
open import OCF.Lean.LeanFbRd
open import OCF.Lean.LeanFbTm
import OCF.Lean.LeanTFold as Fold
open Tree SLs
open FoldTy SLs ΛF
open Fold SLs bkS ΛF lΛF oneF fb
```

## §1 每站的头都有回灌

```agda
IsL : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → Set
IsL (inj₁ _) = ⊤
IsL (inj₂ _) = ⊥

-- 第 n+2 站的层号是 lΩ lz _ (塔的形状)
tw-shape : ∀ m → Σ (HB (Lv lz) → HB SL) (λ g → tw (suc (suc m)) ≡ hΩ (νL lz) g)
tw-shape zero = _ , refl
tw-shape (suc m) = (λ c → Ω̂ (proj₁ (tw-shape m) c)) , cong Ω̂ (proj₂ (tw-shape m))

st-shape : ∀ m → Σ (HB (Lv lz) → LH) (λ h → stL (suc (suc m)) ≡ lΩ lz h)
st-shape m = (λ c → ofHB (proj₁ (tw-shape m) c)) , cong ofHB (proj₂ (tw-shape m))

find-lΩ : ∀ h → IsL (find0 (lΩ lz h))
find-lΩ h = tt

heads-fed : ∀ n → IsL (plan (νS n))
heads-fed zero = tt
heads-fed (suc zero) = tt
heads-fed (suc (suc m)) = lift (find0 (stL (suc (suc m)))) (subst (λ k → IsL (find0 k)) (sym (proj₂ (st-shape m))) tt)
  where
  lift : ∀ (s : AK0 (Lv (stL (suc (suc m)))) ⊎ ⊤) → IsL s → IsL (map₁ (feedH (suc (suc m))) s)
  lift (inj₁ _) _ = tt
```

## §2 回灌那一行被执行, 输出含升后的界

**一步 (定理, `refl`).** 第 $n$ 站的层 `up (1 ⊞ tws (n+1))` 是最高层的字面第一位置 (对一切世界, `stage-fst`), 头是旧种类 `inj₁ (νS n)`; 它的 $\Omega_L$ 在第 0 层目标上字面地走到 `RKa ac (fb (νS n))` (`exec-head`), 而 `fb (νS n)` 对一切 $n$ 是回灌 (`heads-fed`).

```agda
stage-head : ∀ n → Σ (HB (Lv (stL n)) → HB L₀) (λ g → up (hs hz ⊞ tws (suc n)) ≡ hΩ (inj₁ (νS n)) (λ c → g c))
stage-head n = _ , refl

exec-head : ∀ {ly W₀ W m} n (ac : AccY ly) (z : ZK ly (inj₁ (νS n))) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
  (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) (Tq : Tg W hz m) →
  yc (RunC ac (inj₁ (νS n)) z u q₀ lW lL A₀ w Y) Tq ≡ RKa ac (fb (νS n)) u q₀ lW lL A₀ w Y Tq
exec-head n ac z u q₀ lW lL A₀ w Y Tq = refl
```

**在闭项本身的计算里 (定理, `refl`).** 沿显式路径 (`nav`: `⨾` 的左右, `nl` 的第 $n$ 项) 取 `TF = sum hz ΨF` 的第 0 层数据 `ΨF` 的子项, 字面地是 `RKa _ (fb (νS n)) …`, $n=0,1,2$; 路径由否定一路先找到 (`NegLeanFbInst.exec-TF0` 等), 这里独立编译一遍. 路径的读法: 最高层的 $\mathbb N$-极限第 $n+1$ 项 (第 $n+1$ 站的层) → 上升链第 0 项 → 状态里 `Stp` 发出的 $\Omega_k$ → 闭包结点 `nc (inj₁ (νS n))` → 第 0 层目标.

```agda
data Dir : Set where
  dL dR : Dir
  dN : ℕ → Dir

nav : ∀ {W} → List Dir → D hz W → D hz W
nav [] x = x
nav (dL ∷ p) (x ⨾ y) = nav p x
nav (dR ∷ p) (x ⨾ y) = nav p y
nav (dN n ∷ p) (nl d) = nav p (d n)
nav (_ ∷ p) _ = n0

exec-TF0 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 1 ∷ dN 0 ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨF ≡ RKa _ (fb (νS 0)) _ _ _ _ _ _ _ Tq
exec-TF0 Tq = refl

exec-TF1 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 2 ∷ dN 0 ∷ dL ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨF ≡ RKa _ (fb (νS 1)) _ _ _ _ _ _ _ Tq
exec-TF1 Tq = refl

exec-TF2 : (Tq : Tg _ hz (w₀ L₀)) → nav (dR ∷ dR ∷ dN 3 ∷ dN 0 ∷ dL ∷ dL ∷ dL ∷ dR ∷ dN 0 ∷ dL ∷ dR ∷ []) ΨF ≡ RKa _ (fb (νS 2)) _ _ _ _ _ _ _ Tq
exec-TF2 Tq = refl
```

**升后的界 (定理).** 对任一有回灌的种类 (`Feed F`), 级回灌第 0 格与第 $k+1$ 格的世界是 `Up` 的 `rz` 加上读回的增量 (`refl`), 所以**每一个成员** (含触发它的种类自己, `mem`) 的顶都是原顶 $\boxplus$ 读回 (接口的 `rz-top`).

```agda
module Raise {κ} (F : Feed SLs ΛF κ) {ly W₀ W} (ac : AccY ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW L₀ W)
             (lL : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
  c : ℕ → ClA W ly
  c = κcF ac (toFb F) u q₀ lW lL A₀ w Y

  cell0 : wA (c zero) ≡ rz (U F) (LvRd.δ (R F) lW (yc (d Y) (tg ≤rf (LvRd.ℓ⊲ (R F)) lW))) (proj₁ W)
  cell0 = refl

  cellS : ∀ k → wA (c (suc k)) ≡ rz (U F) (LvRd.δ (R F) (lwA (c k) , proj₂ lW)
             (yc (κΔA ac u q₀ lW lL A₀ (c k)) (tg ≤rf (LvRd.ℓ⊲ (R F)) (lwA (c k) , proj₂ lW)))) (wA (c k))
  cellS k = refl

  raise0 : ∀ j → co (U F) j (top SLs (κJ (U F) j) (wA (c zero)))
                 ≡ co (U F) j (top SLs (κJ (U F) j) (proj₁ W)) ⊞ LvRd.δ (R F) lW (yc (d Y) (tg ≤rf (LvRd.ℓ⊲ (R F)) lW))
  raise0 j = rz-top (U F) j _ (proj₁ W)

  -- 触发回灌的种类自己是被升的成员
  self : Σ (J (U F)) (λ j → κJ (U F) j ≡ κ)
  self = mem F
```

**读回看数据 (定理).** 头 $0$ 的读回是第 0 层数据的和; 头 $1$ 与第 $n\ge2$ 站的头的读回把过第 0 层的结点读成 $\Omega$-结点 (`LeanFbRd.rdX-node`). 所以与 `relevelFb` (不看数据) 不同.

```agda
read0 : ∀ {W} (lW : LgW L₀ W) x → LvRd.δ R0 lW x ≡ sum hz x
read0 lW x = refl

read1 : ∀ {W} (lW : LgW L₀ W) x → LvRd.δ (RX newAK) lW x ≡ rdX newAK lW hz x
read1 lW x = refl
```

## §3 同级拷贝一起升; 头 0 与底种类共用增量

`cp1`: 第 3 站里第 1 站头的拷贝 (同 `NegSLFbInst.cp1` 的位置: 坐标 $1$ 的分量, 左分量的新种类, 级 `ls lz`). 在 `SLFbTm` 里它有损且不随头升 (`cp1-lossy`, `cp1-not-moved`); 这里它是级 1 的成员, 有回灌, 升头 1 的那一次调用把它与头 1 加同一个增量.

```agda
cp1 : K SLs
cp1 = 3 , inj₁ (inj₂ (hs hz) , inj₁ tt , inj₂ tt)

cp1-coord : E SLs cp1 ≡ E SLs (νS 1)
cp1-coord = refl

cp1-fed : IsL (plan cp1)
cp1-fed = tt

cp1-moves : ∀ δ w → top SLs cp1 (rz (slotUp 1) δ w) ≡ top SLs cp1 w ⊞ δ
cp1-moves δ w = refl

head1-moves : ∀ δ w → top SLs (νS 1) (rz (slotUp 1) δ w) ≡ top SLs (νS 1) w ⊞ δ
head1-moves δ w = refl
```

**底种类在级 0 的槽里 (对照 `NegRsOwnInst.bd-merge`).** 折叠的底种类 `νS 0` (新种类回灌 `rd₁` 读成它的 $\Omega$-结点) 与第 1 站里级 `lz` 的种类同在 `slotUp 0`: 升一个就给两者加同一个增量.

```agda
lz1 : K SLs
lz1 = 1 , inj₁ (inj₂ tt)

bk-merge : ∀ δ w → (top SLs (νS 0) (rz (slotUp 0) δ w) ≡ top SLs (νS 0) w ⊞ δ)
                 Data.Product.× (top SLs lz1 (rz (slotUp 0) δ w) ≡ top SLs lz1 w ⊞ δ)
bk-merge δ w = refl , refl
```

## §4 剩下的有损种类

**数字层号 $\ge 2$ 的拷贝有损.** 第 2 站坐标 $2$ 的分量是 `Lv (num 3)`, 它的新种类级是 `num 2`.

```agda
lv2 : K SLs
lv2 = 2 , inj₁ (inj₂ (hs (hs hz)) , inj₂ tt)

lv2-lossy : plan lv2 ≡ inj₂ tt
lv2-lossy = refl
```

**第 $n\ge2$ 站头的同级拷贝有损, 且头升时不动.** `cp2`: 第 4 站里坐标类型与第 2 站头相同的种类 (级 `st 2`, 含函数).

```agda
cp2 : K SLs
cp2 = 4 , inj₁ (inj₂ (hs hz) , inj₂ (hs hz) , inj₁ tt , inj₂ tt)

cp2-coord : E SLs cp2 ≡ E SLs (νS 2)
cp2-coord = refl

cp2-lossy : plan cp2 ≡ inj₂ tt
cp2-lossy = refl

cp2-not-moved : ∀ δ w → bumpH 2 δ w 4 ≡ w 4
cp2-not-moved δ w = refl
```

**有损的刻画 (定理).** 深种类有损当且仅当它不是级 `lz` 或 `ls lz` 的成员.

```agda
deep-lossy : ∀ m κ → ¬ IsL (memS 0 m (inj₁ κ)) → ¬ IsL (memS 1 m (inj₁ κ)) → plan (m , inj₁ κ) ≡ inj₂ tt
deep-lossy m κ h0 h1 with memS 0 m (inj₁ κ) | memS 1 m (inj₁ κ)
... | inj₁ _ | _ = Data.Empty.⊥-elim (h0 tt)
... | inj₂ _ | inj₁ _ = Data.Empty.⊥-elim (h1 tt)
... | inj₂ _ | inj₂ _ = refl
```
