# 层号换类型 (二): 有限码与 ω 码上的 `FoldAtK` (对一切 K), `Kt 1` 与 `Kc 1` 的实例, 截断版闭项

> 不含记号. 入口 [LvKt](LvKt.lagda.md), 接口 [LvKtIf](LvKtIf.lagda.md), 塔 [LvKtTower](LvKtTower.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项与证书无模块参数.
>
> - **§1 有限码与 ω 码上的折叠, 对一切种类结构 `K`.** `Lev` 只看层号的构造子, 所以 `K` 里字面地写成 `fin n` 的层号 (`finK n`) 给出的级就是 `Sk n` (`levFinK`, 命题相等, 对 $n$ 归纳, 不要外延). `foldFinK K ck : FoldAtK K ck CovFK` 与 `foldωK K ck : FoldAtK K ck CovΩK` 原样调用 `LvTopInst` 的 `outF` (有限级折叠 `LvRdFold.FF`) 与 `outΩ` (第 ω+1 级折叠 `LvRdFold.FΩ`), 槽沿 `levFinK` 搬运 (`toS`, `Cvt`, 同 `LvTopInst`). 外层世界 $a$ 不被读 (有限码与 ω 码的目标里没有 $\Omega$-结点).
> - **§2 `K = Kt 1` 与 `K = Kc 1` 的实例.** `Kt 1 = Lev (Ωtop S₀)` 的码是 `cdLev (Ωtop S₀)`; `Kc 1` 的码是 `ckc 1`. 两个具体的码与它们上的折叠 (有限码: 界 `finK 3`, 目标 `finK 2`; ω 码: 界 `hs (hl finK)`, 目标 `hl finK`).
> - **§3 截断版 (无条件).** 塔 `LvKtTower.Tower` 取: 每站 `foldFinK (Kc s) (ckc s)`, 回灌部分取常数 `φ = 1` (读回不进层号), 起点 $b_0=0$. 各站层号字面地是 `finK s` (`B-finK`), 层号对角 `ΛB` 的各项也是 (`Bᴧ-fin`), 所以极限站在 `foldωK KΛc ckΛ` 的覆盖之内 (`covLK`). 闭项 `Tkt∞` (有限站的对角) 与 `Tkt` (加极限站). **这一版的层号换了类型, 但没有用到新类型里的任何新种类**: 层号都是 `finK s`, 和 `LvTopInst.Tr` 走到同一处 (第 $1,2,\dots$ 级与第 $\omega+1$ 级).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKtInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.HtTowerFClosed using (ord)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.LvRdIf using (Gω)
open import OCF.Align.LvRdFold using (dnF; dω)
open import OCF.Align.LvTopInst using (toS; lg-toS; module Cvt; outF; loutF; outΩ; loutΩ)
open import OCF.Align.LvTopVal using (Kt)
open import OCF.Align.LvKtCode
open import OCF.Align.LvKtIf
open import OCF.Align.LvKtTower
```

## §1 有限码与 ω 码上的折叠 (对一切 `K`)

```agda
finK : ∀ {K : KS} → ℕ → HB K
finK zero = hz
finK (suc n) = hs (finK n)

lg-finK : ∀ {K : KS} n → LgB (finK {K} n)
lg-finK zero = tt
lg-finK (suc n) = lg-finK n

levFinK : ∀ {K : KS} n → Lev {K} (finK n) ≡ Sk n
levFinK zero = refl
levFinK (suc n) = cong step (levFinK n)

eFK : ∀ {K : KS} {t : HB K} {n} → t ≡ finK n → Lev t ≡ Sk n
eFK {n = n} e = trans (cong Lev e) (levFinK n)

tpK : ∀ {K : KS} {t t′ : HB K} → t ≡ t′ → HB (Lev t) → HB (Lev t′)
tpK e x = subst (λ z → HB (Lev z)) e x

lg-tpK : ∀ {K : KS} {t t′ : HB K} (e : t ≡ t′) x → LgB x → LgB (tpK e x)
lg-tpK refl x l = l

-- 分量注入保 fin
ι-fin : ∀ {I : Set} {F : I → KS} i n → ι {I} {F} i (finK n) ≡ finK n
ι-fin i zero = refl
ι-fin i (suc n) = cong hs (ι-fin i n)

module FinK (K : KS) (ck : CdK K) where
  open Codes ck

  -- 覆盖: 码目标字面地等于某个 finK n
  CovFK : HB K → Set
  CovFK t = Σ ℕ (λ n → t ≡ finK n)

  rtFK : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → CovFK (tgt c) → (w : WbK ck a b) → LgWbK ck w → HB (Lev (tgt c))
  rtFK la lb c (zero , e) w lw = hz
  rtFK la lb c (suc m , e) w lw = toS (sym (eFK e)) (outF m (toS (eFK e) (w c)))

  lrtFK : ∀ {a b} (la : LgW K a) (lb : LgB b) c (cv : CovFK (tgt c)) w (lw : LgWbK ck w) → LgB (rtFK la lb c cv w lw)
  lrtFK la lb c (zero , e) w lw = tt
  lrtFK la lb c (suc m , e) w lw = lg-toS (sym (eFK e)) (outF m (toS (eFK e) (w c))) (loutF m (toS (eFK e) (w c)))

  HFK : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → CovFK (tgt c) → (w : WbK ck a b) → LgWbK ck w → Ht
  HFK la lb c (zero , e) w lw = Ωtop S₀
  HFK la lb c (suc m , e) w lw = proj₁ (dnF m) (outF m (toS (eFK e) (w c)))

  lgHFK : ∀ {a b} (la : LgW K a) (lb : LgB b) c (cv : CovFK (tgt c)) w (lw : LgWbK ck w) → LgB (HFK la lb c cv w lw)
  lgHFK la lb c (zero , e) w lw = Lg-Ωtop S₀
  lgHFK la lb c (suc m , e) w lw = proj₂ (dnF m) (outF m (toS (eFK e) (w c))) (loutF m (toS (eFK e) (w c)))

  foldFinK : FoldAtK K ck CovFK
  foldFinK = record { rt = rtFK ; lrt = lrtFK ; H = HFK ; lgH = lgHFK }

  -- 覆盖: 码目标字面地是 hl f, 逐项 f n ≡ finK n
  CovΩK : HB K → Set
  CovΩK t = Σ (ℕ → HB K) (λ f → (t ≡ hl f) × (∀ n → f n ≡ finK n))

  toGK : ∀ {t} → CovΩK t → HB (Lev t) → HB Gω
  toGK (f , e , ef) x = Cvt.cvt (λ n → Lev (f n)) Sk (λ n → eFK (ef n)) (tpK e x)

  ofGK : ∀ {t} → CovΩK t → HB Gω → HB (Lev t)
  ofGK (f , e , ef) y = tpK (sym e) (Cvt.cvt Sk (λ n → Lev (f n)) (λ n → sym (eFK (ef n))) y)

  lg-ofGK : ∀ {t} (cv : CovΩK t) y → LgB y → LgB (ofGK cv y)
  lg-ofGK (f , e , ef) y l = lg-tpK (sym e) _ (Cvt.Lg-cvt Sk (λ n → Lev (f n)) (λ n → sym (eFK (ef n))) y l)

  foldωK : FoldAtK K ck CovΩK
  foldωK = record
    { rt = λ la lb c cv w lw → ofGK cv (outΩ (toGK cv (w c)))
    ; lrt = λ la lb c cv w lw → lg-ofGK cv (outΩ (toGK cv (w c))) (loutΩ (toGK cv (w c)))
    ; H = λ la lb c cv w lw → proj₁ dω (outΩ (toGK cv (w c)))
    ; lgH = λ la lb c cv w lw → proj₂ dω (outΩ (toGK cv (w c))) (loutΩ (toGK cv (w c))) }

open FinK public
```

## §2 `Kt 1` 与 `Kc 1` 的实例

```agda
ckt1 : CdK (Kt 1)
ckt1 = cdLev (Ωtop S₀)

foldFinKt1 : FoldAtK (Kt 1) ckt1 (CovFK (Kt 1) ckt1)
foldFinKt1 = foldFinK (Kt 1) ckt1

foldωKt1 : FoldAtK (Kt 1) ckt1 (CovΩK (Kt 1) ckt1)
foldωKt1 = foldωK (Kt 1) ckt1

foldFinKc1 : FoldAtK (Kc 1) (ckc 1) (CovFK (Kc 1) (ckc 1))
foldFinKc1 = foldFinK (Kc 1) (ckc 1)

foldωKc1 : FoldAtK (Kc 1) (ckc 1) (CovΩK (Kc 1) (ckc 1))
foldωKc1 = foldωK (Kc 1) (ckc 1)

-- 具体的码: 界 finK 3 之下目标 finK 2 的码 (在 HB (Kt 1) 里)
kfin2 : Codes.Code ckt1 (w0 ckt1) (finK 3)
kfin2 = rP rH , tt

kfin2-tgt : Codes.tgt ckt1 kfin2 ≡ finK 2
kfin2-tgt = refl

-- 界 hs (hl finK) 之下目标 hl finK 的码 (ω 码)
bωK : HB (Kt 1)
bωK = hs (hl finK)

kωK : Codes.Code ckt1 (w0 ckt1) bωK
kωK = rP rH , tt

covωK : CovΩK (Kt 1) ckt1 (Codes.tgt ckt1 kωK)
covωK = finK , refl , (λ n → refl)

-- 第 3 级 (码目标 finK 2) 的级顶在 HB (Kt 1) 的码上折叠: 读回与输出
rt-fin2 : HB (Lev (finK {Kt 1} 2))
rt-fin2 = FoldAtK.rt foldFinKt1 {a = w0 ckt1} (lw0 ckt1) tt kfin2 (2 , refl) (w₀K ckt1) (lw₀K ckt1)

H-fin2 : Ht
H-fin2 = FoldAtK.H foldFinKt1 {a = w0 ckt1} (lw0 ckt1) tt kfin2 (2 , refl) (w₀K ckt1) (lw₀K ckt1)

-- 第 ω+1 级的级顶在 ω 码上折叠
lbωK : LgB bωK
lbωK = (λ n → hsuc hself) , lg-finK

H-ωK : Ht
H-ωK = FoldAtK.H foldωKt1 {a = w0 ckt1} (lw0 ckt1) lbωK kωK covωK (w₀K ckt1) (lw₀K ckt1)
```

## §3 截断版: 回灌常数 1, 无条件

```agda
φ₁ : ∀ s (b : HB (Kc s)) → HB (Lev b) → HB (Lev b)
φ₁ s b x = hs hz

covSK : ∀ s b x → CovFK (Kc s) (ckc s) b → CovFK (Kc (suc s)) (ckc (suc s)) (emb b ⊞ injL b (φ₁ s b x))
covSK s b x (n , e) = suc n , cong hs (trans (cong emb e) (ι-fin (inj₁ tt) n))

module TrK = Tower (λ s → CovFK (Kc s) (ckc s)) (λ s → foldFinK (Kc s) (ckc s)) φ₁ (λ _ _ _ _ → tt)
                   hz tt (zero , refl) covSK

B-finK : ∀ s → TrK.B s ≡ finK s
B-finK zero = refl
B-finK (suc s) = cong hs (trans (cong emb (B-finK s)) (ι-fin (inj₁ tt) s))

Bᴧ-fin : ∀ s → TrK.Bᴧ s ≡ finK s
Bᴧ-fin zero = refl
Bᴧ-fin (suc s) = cong hs (Bᴧ-fin s)

covLK : CovΩK KΛc ckΛ TrK.ΛB
covLK = TrK.Bᴧ , refl , Bᴧ-fin

module TrKL = TrK.Lim (CovΩK KΛc ckΛ) (foldωK KΛc ckΛ) covLK

-- 只有有限站的对角
Tkt∞ : A
Tkt∞ = TrK.TΛ∞

Lg-Tkt∞ : Lg Tkt∞
Lg-Tkt∞ = TrK.Lg-TΛ∞

-- 有限站的对角加极限站: 截断版闭项
Tkt : A
Tkt = TrKL.TΛ∞ω

Lg-Tkt : Lg Tkt
Lg-Tkt = TrKL.Lg-TΛ∞ω

fghKt : ℕ → ℕ
fghKt = FLv.FGH (ord Tkt)
```
