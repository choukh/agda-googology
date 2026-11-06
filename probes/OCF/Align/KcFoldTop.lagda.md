# 种类塔上的一级折叠 (一): 级顶读回, 对一切种类结构一条定义; 由下降给出 `FoldAllK`

> 不含记号. 入口 [KcFold](KcFold.lagda.md), 接口 [KcFoldIf](KcFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 级顶 `top c : HB (Lev c)`**, 对一切种类结构 `K` 与一切 `c : HB K`, 对 $c$ 的构造子一行一个: $0$ ↦ 底种类的 $\Omega$-结点, 分支是 `A` 原样嵌入 (`toH`); 后继 `hs c` ↦ `Ωtop (Lev c)` (**新种类** `inj₂ tt` 的 $\Omega$-结点, 坐标取遍第 $c$ 级的一切高度, 分支是原样嵌入 `up`); ℕ-极限 ↦ 各支级顶的分量注入的部分和的 ℕ-极限; $\Omega$-极限 ↦ 底支的级顶 (只走底支, 同 `code-botK` 的现象; 见 §1 末). 合法由形状给出 (`Lg-top`).
> - **§2 同一条定义在带外层世界的层 `LvW a c` 上** (`topW`, `Lg-topW`). `LvW` 在极限处每支取后继, 所以极限处的项是各支的 `Ωtop`.
> - **§3 由下降给出折叠.** `foldTop K ck dn : FoldAllK K ck`: 读回是 `hs (top (tgt c))`, 回灌输出是下降 `dn` 作用在读回上 (与 `LvKtInst.foldFinK` 的形状相同: 输出 = 下降 (读回)). 带世界版 `foldTopW : FoldAllKW K ck` 同法.
>
> **这不是折叠 (如实说明).** 读回是第 $\mathrm{tgt}\,c$ 级的级顶 (后加 $1$), 不经数据树, 不读槽 $w$, 不读外层世界 $a$. 由 (R1) 的读法 (判断), 真正的一级折叠的读回与级顶同量级; 这里用级顶代替. 回灌输出 `H` 的全部内容来自参数 `dn`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KcFoldTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.LvKtCode
open import OCF.Align.LvKtIf
open import OCF.Align.KcFoldIf
```

## §1 级顶

`A` 原样嵌进一切高度类型 (只用 $0$, 后继, ℕ-极限).

```agda
toH : ∀ {S : KS} → A → HB S
toH azero = hz
toH (asuc a) = hs (toH a)
toH (alim f) = hl (λ n → toH (f n))

toH-⊲ : ∀ {S : KS} {a b} {w : Wd S} → a ⊲ b → toH {S} a ⊲[ w ] toH b
toH-⊲ C.self = hself
toH-⊲ (C.suc p) = hsuc (toH-⊲ p)
toH-⊲ (C.lim n p) = hlim n (toH-⊲ p)

Lg-toH : ∀ {S : KS} a → Lg a → LgB (toH {S} a)
Lg-toH azero l = tt
Lg-toH (asuc a) l = Lg-toH a l
Lg-toH (alim f) (st , l) = (λ n → toH-⊲ (st n)) , (λ n → Lg-toH (f n) (l n))
```

一族分量里的高度, 经分量注入累加 (部分和). 相邻项是字面第一位置 (`⊞-fst`), 所以 ℕ-极限合法 (`NegLvKtTrap.diag-trap` 说不能取注入列本身).

```agda
sumι : ∀ {F : ℕ → KS} → ((n : ℕ) → HB (F n)) → ℕ → HB (sup ℕ F)
sumι {F} t zero = ι {ℕ} {F} 0 (t 0)
sumι {F} t (suc n) = sumι t n ⊞ ι {ℕ} {F} (suc n) (t (suc n))

Lg-sumι : ∀ {F : ℕ → KS} (t : (n : ℕ) → HB (F n)) → (∀ n → LgB (t n)) → ∀ n → LgB (sumι {F} t n)
Lg-sumι {F} t lt zero = Lg-ι {ℕ} {F} 0 (t 0) (lt 0)
Lg-sumι {F} t lt (suc n) = Lg-⊞ (sumι t n) (ι {ℕ} {F} (suc n) (t (suc n))) (Lg-sumι t lt n) (Lg-ι {ℕ} {F} (suc n) (t (suc n)) (lt (suc n)))

Lg-hlsum : ∀ {F : ℕ → KS} (t : (n : ℕ) → HB (F n)) → (∀ n → LgB (t n)) → LgB (hl (sumι {F} t))
Lg-hlsum {F} t lt = (λ n → ⊞-fst (sumι t n) (ι {ℕ} {F} (suc n) (t (suc n)))) , Lg-sumι t lt

-- 底种类的 Ω-结点: 坐标 A, 分支原样嵌入
Ω₀ : HB S₀
Ω₀ = hΩ tt toH

Lg-Ω₀ : LgB Ω₀
Lg-Ω₀ = (λ lw e e′ p → toH-⊲ p) , (λ c lc → Lg-toH c lc)

top : ∀ {K : KS} (c : HB K) → HB (Lev c)
top hz = Ω₀
top (hs c) = Ωtop (Lev c)
top (hl f) = hl (sumι (λ n → top (f n)))
top {K} (hΩ κ g) = ι {E K κ} {λ x → Lev (g x)} (bot K κ) (top (g (bot K κ)))

Lg-top : ∀ {K : KS} (c : HB K) → LgB (top c)
Lg-top hz = Lg-Ω₀
Lg-top (hs c) = Lg-Ωtop (Lev c)
Lg-top (hl f) = Lg-hlsum (λ n → top (f n)) (λ n → Lg-top (f n))
Lg-top {K} (hΩ κ g) = Lg-ι {E K κ} {λ x → Lev (g x)} (bot K κ) (top (g (bot K κ))) (Lg-top (g (bot K κ)))
```

**级顶在第 $c$ 级之上 (定理).** 后继层号 `hs c` 的级顶在任一世界 $(w,\beta)$ 里以第 $c$ 级的每个在界 $\beta$ 之下的高度 $y$ (嵌入后) 为字面第一位置. 这就是 "分支沿坐标增长" 的字面形状: 坐标 $y$ 处的分支就是 $y$ 本身 (`up y`), 且 $y\lhd y'$ 给出 `up y ⊲ up y′` (`up-⊲`).

```agda
top-above : ∀ {K : KS} (c : HB K) {w : Wd (Lev c)} {β : HB (Lev c)} (y : HB (Lev c)) →
            y ⊲[ w ] β → up y ⊲[ (w , β) ] top (hs c)
top-above c y e = hLim {c = y} e hself

top-branch : ∀ {K : KS} (c : HB K) {w : Wd (Lev c)} {β : HB (Lev c)} {y y′ : HB (Lev c)} →
             y ⊲[ w ] y′ → up y ⊲[ (w , β) ] up y′
top-branch c p = up-⊲ p
```

**$\Omega$-极限层号只走底支.** `top (hΩ κ g)` 是底坐标那一支的级顶的注入; 别的坐标的支不进读回. 这是 `top` 的定义 (`refl`), 与 `NegLvKtCopy.code-botK` 同一现象, 但出现在**层号的头**是 $\Omega$-极限时. §3 的塔里层号的头从第 1 站起都是后继 (`KcFoldTower.B-suc-shape`), 所以塔不经过这一行.

## §2 同一条定义在带外层世界的层上

```agda
topW : ∀ {K : KS} (a : Wd K) (c : HB K) → HB (LvW a c)
topW a hz = Ω₀
topW a (hs c) = Ωtop (LvW a c)
topW a (hl f) = hl (sumι (λ n → Ωtop (LvW a (f n))))
topW {K} a (hΩ κ g) = ι {Σ (E K κ) (λ x → Bd K κ x a)} {λ p → step (LvW a (g (proj₁ p)))} (bot K κ , botBd K κ a) (Ωtop (LvW a (g (bot K κ))))

Lg-topW : ∀ {K : KS} (a : Wd K) (c : HB K) → LgB (topW a c)
Lg-topW a hz = Lg-Ω₀
Lg-topW a (hs c) = Lg-Ωtop (LvW a c)
Lg-topW a (hl f) = Lg-hlsum (λ n → Ωtop (LvW a (f n))) (λ n → Lg-Ωtop (LvW a (f n)))
Lg-topW {K} a (hΩ κ g) = Lg-ι {Σ (E K κ) (λ x → Bd K κ x a)} {λ p → step (LvW a (g (proj₁ p)))} (bot K κ , botBd K κ a) (Ωtop (LvW a (g (bot K κ)))) (Lg-Ωtop (LvW a (g (bot K κ))))
```

## §3 由下降给出折叠

读回 `hs (top (tgt c))`, 回灌输出 `dn (tgt c) _` 作用在读回上. 码目标的合法由界的合法与路径给出 (`lgB⊲`).

```agda
module _ (K : KS) (ck : CdK K) where
  open Codes ck using (Code; tgt; pth)

  lgTgt : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → LgB (tgt c)
  lgTgt la lb c = lgB⊲ (pth c) la lb

  foldTop : (∀ (b : HB K) → LgB b → DnK (Lev b)) → FoldAllK K ck
  foldTop dn = record
    { rt  = λ la lb c cv w lw → hs (top (tgt c))
    ; lrt = λ la lb c cv w lw → Lg-top (tgt c)
    ; H   = λ la lb c cv w lw → proj₁ (dn (tgt c) (lgTgt la lb c)) (hs (top (tgt c)))
    ; lgH = λ la lb c cv w lw → proj₂ (dn (tgt c) (lgTgt la lb c)) (hs (top (tgt c))) (Lg-top (tgt c)) }

  foldTopW : (∀ (a : Wd K) (b : HB K) → LgB b → DnK (LvW a b)) → FoldAllKW K ck
  foldTopW dn = record
    { rtW  = λ {a} la lb c cv w lw → hs (topW a (tgt c))
    ; lrtW = λ {a} la lb c cv w lw → Lg-topW a (tgt c)
    ; HW   = λ {a} la lb c cv w lw → proj₁ (dn a (tgt c) (lgTgt la lb c)) (hs (topW a (tgt c)))
    ; lgHW = λ {a} la lb c cv w lw → proj₂ (dn a (tgt c) (lgTgt la lb c)) (hs (topW a (tgt c))) (Lg-topW a (tgt c)) }

-- 一切站与极限站
foldTower : DnTower → FoldTower
foldTower dn s = foldTop (Kc s) (ckc s) (dn s)

foldLim : DnLim → FoldLimK
foldLim dn = foldTop KΛc ckΛ dn
```
