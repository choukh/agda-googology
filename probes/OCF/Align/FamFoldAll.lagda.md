# 族增量世界上的真折叠 (五): 对一切级一条

> 不含记号. 入口 [FamFold](FamFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 第一级 ([FamFoldOne](FamFoldOne.lagda.md)) 与第二级 ([FamFoldTwo](FamFoldTwo.lagda.md)) 的折叠写成对级数 $n$ 的一条定义 (不按站写):
>
> - **第 $n+1$ 级的折叠** `FK.fold n d ld w lo p₀ v Λ W`: 层 `HB (Sk (n+2))` ↦ 第 $n+2$ 层的树. 旧种类 (`inj₁ κ`, 任一低级) 交给 [FamFoldRead](FamFoldRead.lagda.md) 的 `trK` (第 0, 1 级 ↦ 闭包, 第 $j\ge2$ 级 ↦ 过第 $j$ 层的节点); 新种类 (坐标 `HB (Sk (n+1))`) ↦ 回灌: 世界链在 $(n+1, p_0)$ 处族更新 (`rFC`), 增量是折叠自己在分支上的输出经第 $n+1$ 级读回 (`Rd (suc n)`), 下降 $d$ 到两种种类的层, 两种种类折叠 $\Omega_{(n+2)\boxplus h}$ 在第 $n+2$ 层目标上的输出, 再经 `Rd (suc n)` 读回.
> - **下降** `dnR n`: `HB (Sk (n+1))` ↦ `Ht`, 对 $n$ 递归: `dnR 0 = id`, `dnR (n+1) = dnR n ∘ idxK n`; 合法输入给合法输出.
> - **读回对坐标一致** `famK k x c`: 按构造子匹配 $c$ 与 `fin k` (`LocUipFam.mFin`), 匹配上就沿匹配给出的相等搬; `famK-at`: 在 `fin k` 处是读回值 (`mFin-diag`). 不判定任何裸坐标的相等.
> - **闭项**: 第 $n$ 级的级顶 `H n = dnR n (Ωtop (Sk n))`; 对角 `Λ∞ = hl cum`, `cum` 是 `H 0 ⊞ H 1 ⊞ … ⊞ H k` (累加, 合法由形状给出); `T∞ = T⁺ Λ∞`, `fgh∞`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFoldAll where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; Lg)
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; D; n0; n1; _⨾_; nl; ≤rf)
open import OCF.Align.HtTowerFClosed using (module At; T⁺; Lg-T⁺; ord; W₁)
open import OCF.Align.AdmWIf
open import OCF.Align.AdmWCoh using (fin; lg-fin)
open import OCF.Align.LocUipIf using (Inc; atF; monoF; legalF; cohF; CopyCoh)
open import OCF.Align.LocUipFam using (mFin; mFin-diag)
open import OCF.Align.LocUipFeed using (rFC; raiseFCᴮ; copyFC)
open import OCF.Align.UipFbClosed using (vz; lgvz; cohvz)
open import OCF.Align.FamFoldIf using (Sk; CohC; slotAt; TowerDown; Down)
open import OCF.Align.FamFoldLift using (Le; ≤r)
open import OCF.Align.FamFoldRead using (ly; Rdr; rdr; fst; lgr; pkg; Rd; trK)
open Slot
```

## §1 坐标 `fin k` 处的种类结构就是 `Sk k`

```agda
eqG : ∀ k → G₀ (fin k) ≡ Sk k
eqG zero = refl
eqG (suc k) = cong step (eqG k)

toSk : ∀ k → HB (G₀ (fin k)) → HB (Sk k)
toSk k = subst HB (eqG k)

ofSk : ∀ k → HB (Sk k) → HB (G₀ (fin k))
ofSk k = subst HB (sym (eqG k))

lg-subst : ∀ {S T : KS} (e : S ≡ T) (x : HB S) → LgB x → LgB (subst HB e x)
lg-subst refl x l = l

-- 族读回: 按构造子匹配坐标与 fin k
hK : ∀ k {c : HB S₀} → (fin k ≡ c) ⊎ ⊤ → HB (Sk k) → HB (G₀ c)
hK k (inj₁ e) x = subst (λ z → HB (G₀ z)) e (ofSk k x)
hK k (inj₂ _) x = hz

famK : ∀ k → HB (Sk k) → Inc
famK k x c = hK k (mFin k c) x

famK-at : ∀ k x → famK k x (fin k) ≡ ofSk k x
famK-at k x = cong (λ d → hK k d x) (mFin-diag k)

Lg-famK-at : ∀ k x → LgB x → LgB (famK k x (fin k))
Lg-famK-at k x l = subst LgB (sym (famK-at k x)) (lg-subst (sym (eqG k)) x l)
```

## §2 两种种类折叠在第 $L+1$ 层目标上的输出

```agda
oneL⊲ : ∀ L {w} → hs hz ⊲[ w ] ly (suc L)
oneL⊲ zero = hself
oneL⊲ (suc L) = hsuc (oneL⊲ L)

lgly : ∀ L → LgB {Sk 1} (ly L)
lgly zero = tt
lgly (suc L) = lgly L

topL : ℕ → Ht → Ht
topL L h = ly (suc L) ⊞ h

module OL (L : ℕ) (h : Ht) (lh : LgB h) where
  open At (topL L h) (Lg-⊞ (ly (suc L)) h (lgly (suc L)) lh) (⊲ᴮ-tr (oneL⊲ L) (⊞-fst (ly (suc L)) h)) public
  τL : Tg W₁ (ly (suc L)) W₁
  τL = tg ≤rf (⊞-fst (ly (suc L)) h) (tt , tt)
  outL : D (ly (suc L)) W₁
  outL = yc ΔΩ τL

-- 读回: 底 1, 第 L 级的读回
δK : ∀ L → (h : Ht) → LgB h → HB (Sk L)
δK L h lh = rdr (Rd L) (tt , tt) (hs hz) (OL.outL L h lh)
```

底是 `HB (Sk L)` 里的 $1$ (`hs hz`), 与 `UipFbClosed.δ⋆` 同. 合法由 `lgr` 给出.

```agda
lδK : ∀ L h lh → LgB (δK L h lh)
lδK L h lh = lgr (Rd L) (tt , tt) _ (OL.outL L h lh) tt
```

## §3 第 $n+1$ 级的折叠

```agda
Dn : ℕ → Set
Dn n = Σ (HB (Sk (suc n)) → Ht) (λ d → ∀ x → LgB x → LgB (d x))

module FK (n : ℕ) (d : HB (Sk (suc n)) → Ht) (ld : ∀ x → LgB x → LgB (d x))
          (w : Out) (lo : LgO w) (p₀ : AdmE w (fin (suc n))) where
  K₁ : ℕ
  K₁ = suc n

  Outₖ : Set
  Outₖ = (W : Wd₂) → D (ly (suc K₁)) W

  slot : Cmp w → HB (Sk K₁)
  slot u = toSk K₁ (slotAt u (fin K₁) p₀)

  lay : Outₖ → HB (Sk K₁)
  lay o = rdr (Rd K₁) (tt , tt) hz (o W₁)

  Lg-lay : ∀ o → LgB (lay o)
  Lg-lay o = lgr (Rd K₁) (tt , tt) hz (o W₁) tt

  rdO : Outₖ → HB (Sk K₁)
  rdO o = δK K₁ (d (lay o)) (ld (lay o) (Lg-lay o))

  lg-rdO : ∀ o → LgB (rdO o)
  lg-rdO o = lδK K₁ (d (lay o)) (ld (lay o) (Lg-lay o))

  -- 读回对坐标一致
  famOK : Σ (Outₖ → Inc) (λ F → ∀ o → F o (fin K₁) ≡ ofSk K₁ (rdO o))
  famOK = (λ o → famK K₁ (rdO o)) , (λ o → famK-at K₁ (rdO o))

  ch : (Cmp w → Outₖ) → Cmp w → ℕ → Cmp w
  ch Fo v zero = v
  ch Fo v (suc k) = rFC w lo (ch Fo v k) (fin K₁) p₀ (famK K₁ (rdO (Fo (ch Fo v k))))

  fold : Cmp w → HB (Sk (suc K₁)) → Outₖ
  fold v hz W = n0
  fold v (hs x) W = fold v x W ⨾ n1
  fold v (hl f) W = nl (λ k → fold v (f k) W)
  fold v (hΩ (inj₁ κ) g) W = trK (pkg n) ≤r κ hself (λ c W′ → fold v (g c) W′) W
  fold v (hΩ (inj₂ tt) g) W =
    nl (λ k → fold (ch (λ u → fold u (g (slot u))) v k) (g (slot (ch (λ u → fold u (g (slot u))) v k))) W)

  chain : Cmp w → (HB (Sk K₁) → HB (Sk (suc K₁))) → ℕ → Cmp w
  chain v g = ch (λ u → fold u (g (slot u))) v

  fold-Ω : ∀ v g W → fold v (hΩ (inj₂ tt) g) W ≡ nl (λ k → fold (chain v g k) (g (slot (chain v g k))) W)
  fold-Ω v g W = refl

  ch-lg : ∀ v g → LgWᴮ (w , v) → ∀ k → LgWᴮ (w , chain v g k)
  ch-lg v g lW zero = lW
  ch-lg v g lW (suc k) =
    legalF raiseFCᴮ w lo (chain v g k) (fin K₁) p₀ _
      (Lg-famK-at K₁ _ (lg-rdO (fold (chain v g k) (g (slot (chain v g k)))))) (ch-lg v g lW k)

  ch-coh : ∀ v g → CohC (w , v) → ∀ k → CohC (w , chain v g k)
  ch-coh v g cc zero = cc
  ch-coh v g cc (suc k) =
    cohF raiseFCᴮ w lo (chain v g k) (fin K₁) p₀ _ (proj₁ (ch-coh v g cc k)) ,
    copyFC w lo (chain v g k) (fin K₁) p₀ _ (proj₂ (ch-coh v g cc k))

  ch-≤ : ∀ v g k → (w , chain v g k) ≤ᴮ (w , chain v g (suc k))
  ch-≤ v g k = monoF raiseFCᴮ w lo (chain v g k) (fin K₁) p₀ _

  -- 槽的递推 (在同一个证据 p₀ 上)
  slot-s : ∀ v g k → slotAt (chain v g (suc k)) (fin K₁) p₀ ≡
           slotAt (chain v g k) (fin K₁) p₀ ⊞ famK K₁ (rdO (fold (chain v g k) (g (slot (chain v g k))))) (fin K₁)
  slot-s v g k = cong proj₂ (atF raiseFCᴮ w lo (chain v g k) (fin K₁) p₀ _)
```

## §4 下降与闭项

外层世界 $(0, n+2)$: 坐标 $n+1$ 与它的后继都可入; 分量全 $0$.

```agda
wK : ℕ → Out
wK n = azero , fin (suc (suc n))

loK : ∀ n → LgO (wK n)
loK n = tt , lg-fin (suc (suc n))

pK : ∀ n → AdmE (wK n) (fin (suc n))
pK n = hsuc hself

copyvzK : ∀ n → CopyCoh (wK n , vz (wK n))
copyvzK n c₀ q₀ q₁ = refl

cohCK : ∀ n → CohC (wK n , vz (wK n))
cohCK n = cohvz (wK n) , copyvzK n

idxK : ∀ n → Dn n → HB (Sk (suc (suc n))) → HB (Sk (suc n))
idxK n (d , ld) Λ = FK.lay n d ld (wK n) (loK n) (pK n) (FK.fold n d ld (wK n) (loK n) (pK n) (vz (wK n)) Λ)

Lg-idxK : ∀ n (D′ : Dn n) Λ → LgB (idxK n D′ Λ)
Lg-idxK n (d , ld) Λ = FK.Lg-lay n d ld (wK n) (loK n) (pK n) (FK.fold n d ld (wK n) (loK n) (pK n) (vz (wK n)) Λ)

dnR : ∀ n → Dn n
dnR zero = (λ x → x) , (λ x l → l)
dnR (suc n) = (λ Λ → proj₁ (dnR n) (idxK n (dnR n) Λ)) , (λ Λ _ → proj₂ (dnR n) _ (Lg-idxK n (dnR n) Λ))

-- 第 n 级的级顶, 降到两种种类的层
H : ℕ → Ht
H n = proj₁ (dnR n) (Ωtop (Sk n))

lgH : ∀ n → LgB (H n)
lgH n = proj₂ (dnR n) (Ωtop (Sk n)) (Lg-Ωtop (Sk n))

-- 每一级一个闭项
Tlv : ℕ → A
Tlv n = T⁺ (H n) (lgH n)

-- 对角: 各级级顶的累加
cum : ℕ → Ht
cum zero = H zero
cum (suc k) = cum k ⊞ H (suc k)

lcum : ∀ k → LgB (cum k)
lcum zero = lgH zero
lcum (suc k) = Lg-⊞ (cum k) (H (suc k)) (lcum k) (lgH (suc k))

Λ∞ : Ht
Λ∞ = hl cum

lΛ∞ : LgB Λ∞
lΛ∞ = (λ k → ⊞-fst (cum k) (H (suc k))) , lcum

T∞ : A
T∞ = T⁺ Λ∞ lΛ∞

Lg-T∞ : Lg T∞
Lg-T∞ = Lg-T⁺ Λ∞ lΛ∞

fgh∞ : ℕ → ℕ
fgh∞ = FL.FGH (ord T∞)
```

## §5 接口 §5 的实例

`Down (Sk (suc k))` 要的是把 `HB (Sk (k+2))` 折成 `HB (Sk (k+1))`, 合法由形状给出: 就是 `idxK k (dnR k)`.

```agda
towerDown : TowerDown
towerDown k = record { down = idxK k (dnR k) ; lg-down = Lg-idxK k (dnR k) }
```
