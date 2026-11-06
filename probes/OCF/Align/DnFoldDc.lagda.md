# 有内容的下降 (三): 层号在 `Ht` 的经求值的下降, 与一个闭项

> 不含记号. 入口 [DnFold](DnFold.lagda.md), 接口 [DnFoldIf](DnFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 读回层合法** (`LyH-mono`, `lgLyH`, `o1H`): 与 `LvOmClosed` §1 同, 层号与读回层同在 `Ht`, 路径原样搬.
> - **§2 下降 `dnH a la c lc e2 : DnK (LvH a c)`**: 接口 `DnEv` 的实例 `dnEvH` (层 `LyH c`, 求值世界就是外层世界 $a$, 翻译 `DnFoldRd.Rd.trN`) 经 `DnFoldEv.toDn`. 参数 `e2` (第 2 层在 $a$ 里是 `LyH c` 的第一位置) 与 `LvOmClosed.Dc` 的 `ev2` 同; 第 1 层在 $a$ 里是层号 $c$ 的第一位置时就有 (`e2-of`).
> - **§3 读回进入求值的输入 (形状定理, `refl`)**: 后继层号 `hs c` 的读回 `rdTop (LvH a c)` 翻译成 `n1` 之前的一个 `ni` 结点, 分支在每个更大的世界 $W'$ 与第 `LyH c` 层的数据 $y$ 上是 "把 $y$ 读回成第 $c$ 级的高度, 再翻译它的嵌入" (`tr-top`). 把分支全换成 $0$ 的截断翻译成同一个结点, 分支是常数 `n0` (`tr-cut`).
> - **§4 闭项**: 层号 `c₁H = hs X₁H`, `X₁H = hΩ κH (y ↦ 1 ⊞ up y)` (`KcFoldTower.One.B1-shape` 在 `Ht` 里的同形物: 第 1 站层号的头是坐标取遍 `H₀` 的 $\Omega$-结点, 各支是 $1\boxplus y$), 外层世界 $(\omega,\omega_0)$. 读回 `rdTop (LvH aω X₁H)` 经 `dnH` 降到 `Ht`, 作两种种类折叠的下标: `TH₁ : A`, 证书 `Lg-TH₁`, FGH `fghH₁`. 无模块参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldDc where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (S₁; H₀; Ht; Wd₂; LgW₂; D; ≤rf; ≤tr; κA; κH; ni; n0; n1; _⨾_; ss; outS; StH)
  renaming (Sk to SkH)
open import OCF.Align.HtTowerFClosed using (T⁺; Lg-T⁺; ord)
open import OCF.Align.KcFoldIf using (DnK)
open import OCF.Align.DnFoldIf
open import OCF.Align.DnFoldEv
open import OCF.Align.DnFoldRd
```

## §1 读回层合法

```agda
LyH-mono : ∀ {c c′ : Ht} {W : Wd₂} → c ⊲[ W ] c′ → LyH c ⊲[ W ] LyH c′
LyH-mono hself = hself
LyH-mono (hsuc p) = hsuc (LyH-mono p)
LyH-mono (hlim n p) = hlim n (LyH-mono p)
LyH-mono (hLim e p) = hLim e (LyH-mono p)

lgLyH : ∀ c → LgB c → LgB (LyH c)
lgLyH hz _ = tt
lgLyH (hs c) l = lgLyH c l
lgLyH (hl f) (st , l) = (λ n → LyH-mono (st n)) , (λ n → lgLyH (f n) (l n))
lgLyH (hΩ κ g) (mo , l) = (λ lw e e′ pr → LyH-mono (mo lw e e′ pr)) , (λ x lx → lgLyH (g x) (l x lx))

o1H : ∀ c {w : Wd₂} → hs hz ⊲[ w ] LyH c
o1H hz = hself
o1H (hs c) = hsuc (o1H c)
o1H (hl f) = hlim 0 (o1H (f 0))
o1H (hΩ κ g) {w} = hLim (botBd S₁ κ w) (o1H (g (bot S₁ κ)))

-- 第 1 层是层号的第一位置, 则第 2 层是读回层的第一位置
e2-of : ∀ {c} {w : Wd₂} → hs hz ⊲[ w ] c → hs (hs hz) ⊲[ w ] LyH c
e2-of p = LyH-mono p
```

## §2 下降

```agda
dnEvH : (a : Wd₂) → LgW₂ a → (c : Ht) → LgB c → hs (hs hz) ⊲[ a ] LyH c → DnEv (LvH a c)
dnEvH a la c lc e2 = record
  { Lw = LyH c ; lLw = lgLyH c lc ; o1 = o1H c ; Wv = a ; lWv = la ; ev2 = e2
  ; tr = λ x → Rd.trN a (Rd.pk a c) x a ≤rf }

dnH : (a : Wd₂) → LgW₂ a → (c : Ht) → LgB c → hs (hs hz) ⊲[ a ] LyH c → DnK (LvH a c)
dnH a la c lc e2 = toDn (dnEvH a la c lc e2)

-- 参数换成层号自己的第一位置
dnHs : (a : Wd₂) → LgW₂ a → (c : Ht) → LgB c → hs hz ⊲[ a ] c → DnK (LvH a c)
dnHs a la c lc p = dnH a la c lc (e2-of p)
```

## §3 读回进入求值的输入 (形状定理)

```agda
module TrShape (a : Wd₂) (c : Ht) where
  open Rd a

  -- 过第 LyH c 层 (读回层 LyH (hs c) 的前一层) 的结点位置
  R₀ : StH a (LyH c) (LyH (hs c))
  R₀ = SkH {W = a} {j = LyH c} {k = hs (LyH c)} {L = hs (LyH c)} (ss hself) hself

  tr-top : trN (pk (hs c)) (rdTop (Lv c)) a ≤rf ≡
           ni R₀ (λ {W′} p lW′ y → trN (pk (hs c)) (up (rdc (pk c) W′ ≤rf lW′ (≤tr ≤rf p) hz (outS R₀ y))) W′ (≤tr ≤rf p))
           ⨾ n1
  tr-top = refl

  tr-cut : trN (pk (hs c)) (rdCut (Lv c)) a ≤rf ≡
           ni R₀ (λ {W′} p lW′ y → n0) ⨾ n1
  tr-cut = refl
```

## §4 闭项

```agda
X₁H : Ht
X₁H = hΩ κH (λ y → hs hz ⊞ up y)

lX₁H : LgB X₁H
lX₁H = (λ lw e e′ pr → ⊞-⊲ (hs hz) (up-⊲ pr)) , (λ y ly → Lg-⊞ (hs hz) (up y) tt (Lg-up y ly))

c₁H : Ht
c₁H = hs X₁H

finH₀ : ℕ → H₀
finH₀ zero = hz
finH₀ (suc n) = hs (finH₀ n)

ω₀H : H₀
ω₀H = hl finH₀

lg-finH₀ : ∀ n → LgB (finH₀ n)
lg-finH₀ zero = tt
lg-finH₀ (suc n) = lg-finH₀ n

Lg-ω₀H : LgB ω₀H
Lg-ω₀H = (λ n → hsuc hself) , lg-finH₀

finA : ℕ → A
finA zero = azero
finA (suc n) = asuc (finA n)

lg-finA : ∀ n → Lg (finA n)
lg-finA zero = tt
lg-finA (suc n) = lg-finA n

ωA : A
ωA = alim finA

Lg-ωA : Lg ωA
Lg-ωA = (λ n → C.suc C.self) , lg-finA

aω : Wd₂
aω = ωA , ω₀H

laω : LgW₂ aω
laω = Lg-ωA , Lg-ω₀H

-- 第 1 层经底支 (y = 0, 那一支是 1 ⊞ 0 = 1) 是层号的第一位置
one⊲c₁ : hs hz ⊲[ aω ] c₁H
one⊲c₁ = hsuc (hLim {κ = κH} {c = hz} (z⊲ᴮ ω₀H) hself)

-- 第 1 站同形物的读回, 降到 Ht
HD₁ : Ht
HD₁ = proj₁ (dnHs aω laω c₁H lX₁H one⊲c₁) (rdTop (LvH aω X₁H))

lgHD₁ : LgB HD₁
lgHD₁ = proj₂ (dnHs aω laω c₁H lX₁H one⊲c₁) (rdTop (LvH aω X₁H)) (Lg-Ωtop (LvH aω X₁H))

TH₁ : A
TH₁ = T⁺ HD₁ lgHD₁

Lg-TH₁ : Lg TH₁
Lg-TH₁ = Lg-T⁺ HD₁ lgHD₁

fghH₁ : ℕ → ℕ
fghH₁ = FL.FGH (ord TH₁)
```
