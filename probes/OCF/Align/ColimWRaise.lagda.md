# `Lev` 取并 (三): 更新, 一步回灌, `κ₂` 处的格

> 不含记号. 入口 [ColimW](ColimW.lagda.md), 接口 [ColimWIf](ColimWIf.lagda.md) §4. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> - **`raiseG`** (定理): 有判定证书 `DecAt y₀` 就有满足接口 `RaiseG y₀` 全部六条律的更新 (`base`, `at`, `off`, `mono`, `legal`). 增量只进层号 $y_0$ 的分量; 判定 "是不是 $y_0$" 由证书给出, 证书对角上给 `refl`, 所以 `at` 是 `cong` 一行, 不用 UIP (对照 `AdmWCoh.uip→raise₀-coh`: 那里分量以 (坐标, 证据) 为下标, 两个证据给两条相等证明, 要 UIP; 这里分量只以层号为下标, 没有第二条证明).
> - **`decFin`** (定理): 有限层号 `finH k` 有证书 (对一切 $k$, 一切 `S`).
> - **`raiseG→wdec`** (条件定理, 与 `CohWUpd.upd→wdec` 同族): 有 `RaiseG y₀` 就能对一切 $y$ 判定 "$y_0\ne y$, 或者不是 $y_0\ne y$". 所以对无限层号 (例如 `hl finH`) 构造 `RaiseG` 至少要这样的弱判定. 这不是否定 (不说它不存在), 只说造它要什么.
> - **一步回灌与 `κ₂`** (定理): 从最小世界 `W₀` 在层号 `finH 1` 上接 `Ωtop S₀` (含新种类的 $\Omega$-节点), 得到合法的更大世界 `W₁`; 在 `W₁` 里 `κ₂` 处的格 `hz ⊞ Ωtop S₀` **有界** (`cell₂`), 根是新种类的节点 (`root-new`). 同一个证明项也证明它在 `κ₂` 的两个拷贝 (`κ₂′`, `κ₂ω`) 与 ℕ-极限级 `xω` 的 `λ₂`, `λ₃` 处有界 (`cell₂′`, `cell₂ω`, `cellλ₂`, `cellλ₃`). 对一切世界与增量的一般形 `cell-gen`.
> - **对照: 和的世界里只改一个分量, 拷贝不跟着变** (`sum-fresh`, `sum-stale`, 定理): `Lev x₀` 自己的世界里只把坐标 2 的分量的层号 1 之界换成 `Ωtop S₀` (判定 "坐标是不是 2" 用 `eqFin`), 那么 `κ₂` 处有界, `κ₂′` 处同一个坐标不有界.
>
> **与 `ChainZNeg.no-chain` 的关系 (写明范围).** `no-chain` 说: `L′ 1` 里由 `dW 1` 经 `growL′` (一切高度界接同一个 `up h`) 生成的世界里, `κ₂` 处含新种类节点的格从不有界. 这里的世界不是那一族: `raiseG` 是**选择性**的 (只在层号 `finH 1` 上接), 选择由有限层号的判定给出. 所以 `cell₂` 不与 `no-chain` 矛盾, 也不推翻它; 它说明对有限层号, `GW` 上的选择性更新让含新节点的格有界, 并且一次更新同时作用于这一层号的一切拷贝. 对无限层号, 同样的更新撞 `raiseG→wdec` 的条件 (第一个障碍).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ColimWRaise where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.ColimWIf
open import OCF.Align.ColimWKS
```

## §1 有限层号的判定证书

```agda
hs-inj : ∀ {S} {a b : HB S} → hs a ≡ hs b → a ≡ b
hs-inj refl = refl

sucD : ∀ {S} {a b : HB S} → (a ≡ b) ⊎ ¬ (a ≡ b) → (hs a ≡ hs b) ⊎ ¬ (hs a ≡ hs b)
sucD (inj₁ e) = inj₁ (cong hs e)
sucD (inj₂ ne) = inj₂ (λ e → ne (hs-inj e))

eqFin : ∀ {S} (k : ℕ) (y : HB S) → (finH k ≡ y) ⊎ ¬ (finH k ≡ y)
eqFin zero hz = inj₁ refl
eqFin zero (hs y) = inj₂ (λ ())
eqFin zero (hl f) = inj₂ (λ ())
eqFin zero (hΩ κ g) = inj₂ (λ ())
eqFin (suc k) hz = inj₂ (λ ())
eqFin (suc k) (hs y) = sucD (eqFin k y)
eqFin (suc k) (hl f) = inj₂ (λ ())
eqFin (suc k) (hΩ κ g) = inj₂ (λ ())

eqFin-diag : ∀ {S} k → eqFin {S} k (finH k) ≡ inj₁ refl
eqFin-diag zero = refl
eqFin-diag (suc k) = cong sucD (eqFin-diag k)

decFin : ∀ {S} k → DecAt {S} (finH k)
decFin k = eqFin k , eqFin-diag k
```

## §2 有证书就有更新

```agda
module _ {S : KS} {y₀ : HB S} (D : DecAt y₀) where
  inc : ∀ {y} → (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y) → HB (Lev y₀) → HB (Lev y)
  inc (inj₁ refl) δ = δ
  inc (inj₂ _) δ = hz

  Lg-inc : ∀ {y} (d : (y₀ ≡ y) ⊎ ¬ (y₀ ≡ y)) δ → LgB δ → LgB (inc d δ)
  Lg-inc (inj₁ refl) δ l = l
  Lg-inc (inj₂ _) δ l = tt

  raiseD : GW S → HB (Lev y₀) → GW S
  raiseD W δ = proj₁ W , λ y → proj₂ W y ⊞ inc (proj₁ D y) δ

  atD : ∀ W δ → proj₂ (raiseD W δ) y₀ ≡ proj₂ W y₀ ⊞ δ
  atD W δ = cong (λ t → proj₂ W y₀ ⊞ inc t δ) (proj₂ D)

  offD : ∀ W δ y → ¬ (y₀ ≡ y) → proj₂ (raiseD W δ) y ≡ proj₂ W y
  offD W δ y ne with proj₁ D y
  ... | inj₁ e = ⊥-elim (ne e)
  ... | inj₂ _ = refl

  monoD : ∀ W δ → W ≤G raiseD W δ
  monoD W δ = C.self , λ y → ⊞-fst (proj₂ W y) (inc (proj₁ D y) δ)

  legalD : ∀ W δ → LgB δ → LgG W → LgG (raiseD W δ)
  legalD W δ lδ l =
    proj₁ l , λ y → Lg-⊞ (proj₂ W y) (inc (proj₁ D y) δ) (proj₂ l y) (Lg-inc (proj₁ D y) δ lδ)

  raiseG : RaiseG y₀
  raiseG = record
    { raise = raiseD ; base = λ W δ → refl ; at = atD ; off = offD ; mono = monoD ; legal = legalD }
```

## §3 条件定理: 更新给出与 $y_0$ 相等的弱判定

```agda
private
  hs≢hz : ∀ {S} {v : HB S} → ¬ (hs v ≡ hz)
  hs≢hz ()
  hl≢hz : ∀ {S} {f : ℕ → HB S} → ¬ (hl f ≡ hz)
  hl≢hz ()
  hΩ≢hz : ∀ {S} {κ : K S} {g : E S κ → HB S} → ¬ (hΩ κ g ≡ hz)
  hΩ≢hz ()

noHz : ∀ {S} {y₀ : HB S} (R : RaiseG y₀) {y} → y₀ ≡ y →
  proj₂ (RaiseG.raise R W₀ (hs hz)) y ≡ hz → ⊥
noHz R refl eq = hs≢hz (trans (sym (RaiseG.at R W₀ (hs hz))) eq)

raiseG→wdec : ∀ {S} {y₀ : HB S} → RaiseG y₀ → ∀ y → ¬ (y₀ ≡ y) ⊎ ¬ ¬ (y₀ ≡ y)
raiseG→wdec {S} {y₀} R y = look (proj₂ (RaiseG.raise R W₀ (hs hz)) y) refl
  where
    offR : ¬ (y₀ ≡ y) → proj₂ (RaiseG.raise R W₀ (hs hz)) y ≡ hz
    offR ne = RaiseG.off R W₀ (hs hz) y ne
    look : (v : HB (Lev y)) → proj₂ (RaiseG.raise R W₀ (hs hz)) y ≡ v → ¬ (y₀ ≡ y) ⊎ ¬ ¬ (y₀ ≡ y)
    look hz eq = inj₁ (λ e → noHz R e eq)
    look (hs v) eq = inj₂ (λ ne → hs≢hz (trans (sym eq) (offR ne)))
    look (hl f) eq = inj₂ (λ ne → hl≢hz (trans (sym eq) (offR ne)))
    look (hΩ κ g) eq = inj₂ (λ ne → hΩ≢hz (trans (sym eq) (offR ne)))
```

前提可满足: `raiseG (decFin k)` 是 `RaiseG (finH k)` 的实例 (此时结论本来就是定理).

## §4 一步回灌: `κ₂` 处含新节点的格有界

```agda
R₁ : RaiseG {S₁} (finH 1)
R₁ = raiseG (decFin 1)

δΩ : HB (Lev {S₁} (finH 1))
δΩ = Ωtop S₀

W₁ : GW S₁
W₁ = RaiseG.raise R₁ W₀ δΩ

lgW₁ : LgG W₁
lgW₁ = RaiseG.legal R₁ W₀ δΩ (Lg-Ωtop S₀) lgW₀

grow₁ : W₀ ≤G W₁
grow₁ = RaiseG.mono R₁ W₀ δΩ

-- 格的根是新种类的 Ω-节点
RootNew : ∀ {S} → HB (step S) → Set
RootNew (hΩ (inj₂ _) g) = ⊤
RootNew _ = ⊥

root-new : RootNew {S₀} (hz ⊞ Ωtop S₀)
root-new = tt

cell₂ : Cell₂ hz (Ωtop S₀) W₁
cell₂ = hself

-- 同一个证明项: 拷贝处也有界
cell₂′ : Bd (LevC x₀) κ₂′ (hz ⊞ Ωtop S₀) W₁
cell₂′ = hself

cell₂ω : Bd (LevC x₀) κ₂ω (hz ⊞ Ωtop S₀) W₁
cell₂ω = hself

cellλ₂ : Bd (LevC xω) λ₂ (hz ⊞ Ωtop S₀) W₁
cellλ₂ = hself

cellλ₃ : Bd (LevC xω) λ₃ (hz ⊞ Ωtop S₀) W₁
cellλ₃ = hself
```

**一般形.** 任一世界 $W$, 任一增量 $\delta$, 更新之后 `κ₂` 处的格 "旧界 $\boxplus\,\delta$" 有界.

```agda
cell-gen : ∀ (W : GW S₁) (δ : HB S₁) →
  Cell₂ (proj₂ W (finH 1)) δ (RaiseG.raise R₁ W δ)
cell-gen W δ = subst (λ t → (proj₂ W (finH 1) ⊞ δ) ⊲[ restr (finH 1) (RaiseG.raise R₁ W δ) ] t)
                     (sym (RaiseG.at R₁ W δ)) hself
```

## §5 对照: 和的世界里只改一个分量

`Lev x₀` 自己的世界, 只把坐标 2 的分量的层号 1 之界放成 `Ωtop S₀` (判定 "坐标是不是 2" 用 `eqFin 2`, 有限). `κ₂` 处有界, 同一个坐标在拷贝 `κ₂′` 处不有界. 这只说 "只改一个分量" 这一种和世界上的更新; 和世界上沿 `restr` 一致地改 (那就是 `GW` 的像) 不在此列.

```agda
wsel : (c : HB S₀) → (finH 2 ≡ c) ⊎ ¬ (finH 2 ≡ c) → Wd (Lev (up c))
wsel c (inj₁ refl) = dWs {S₁} (finH 1) , Ωtop S₀
wsel c (inj₂ _) = dWs (up c)

ws : Wd (Lev x₀)
ws c = wsel c (eqFin 2 c)

lg-wsel : ∀ c (d : (finH 2 ≡ c) ⊎ ¬ (finH 2 ≡ c)) → LgW (Lev (up c)) (wsel c d)
lg-wsel c (inj₁ refl) = lg-dWs {S₁} (finH 1) , Lg-Ωtop S₀
lg-wsel c (inj₂ _) = lg-dWs (up c)

lg-ws : LgW (Lev x₀) ws
lg-ws c = lg-wsel c (eqFin 2 c)

sum-fresh : Bd (Lev x₀) κ₂ (Ωtop S₀) ws
sum-fresh = hself

sum-stale : ¬ Bd (Lev x₀) κ₂′ (Ωtop S₀) ws
sum-stale ()
```
