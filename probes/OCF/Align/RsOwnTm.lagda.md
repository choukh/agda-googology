# 积世界上的升界 (三): 无条件闭项; 形状定理

> 不含记号. 入口 [RsOwn](RsOwn.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 闭项, 证书, FGH 无模块参数.
>
> - **§1 搬运 `cv`**: `HB T → HB (subW T P)` (种类与坐标定义相等, 逐构造子), 保第一位置与合法.
> - **§2 闭项.** 塔与层号对角与 [KindLvTw](KindLvTw.lagda.md) 的 `NT₁` 逐字相同 (直接引用); 只有最终坍缩换成在 `TU = subW KΛc Uf` 上: 一般坍缩 `KindLvTw.collLv`, `GenK`/`LgDn`/`FbLg` 取 [RsOwnSW](RsOwnSW.lagda.md) 的 `genU`, `ldU`, `flU`, 级回灌取 `lvU` (一切底拷贝有 `KLv`, 其余有损). 闭项 `TS`, 证书 `Lg-TS`, FGH `fghS`.
> - **§3 形状定理.** 第 1 站读回分量里含函数下标 `jx f` 的底拷贝: 在 `KindLvTw` (与 `GΛ`) 里有损 (`old-lossy-lv`, `old-lossy-fb`), 在这里有 `KLv` (`new-lv`). 后面各站的头种类 (坐标是高度) 仍有损 (`head-still-lossy`). `NegKindLvRaise.w′` 不满足不变式 (`w′-not-Uf`): 这就是本构造避开 `no-upAllR` 的地方.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RsOwnTm where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; Lg)
import OCF.Free.Level as FLv
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.GenFoldIf using (GenK; tpK; fbA; K₁)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.LvKtIf using (Kc; KΛc; ιΛ)
open import OCF.Align.NewTwrColl using (GΛ; LdΛ)
open import OCF.Align.KindLvIf using (KLv)
open import OCF.Align.KindLvTw using (collLv; module NT₁; ordK; lvΛ)
open import OCF.Align.NegGenFoldUpd using (jx)
open import OCF.Align.NegKindLvRaise using (w′)
open import OCF.Align.RsOwnIf
open import OCF.Align.RsOwnSh
open import OCF.Align.RsOwnSW
```

## §1 搬运

```agda
module Cv {T : KS} {P : Wd T → Set} where
  cv : HB T → HB (subW T P)
  cv hz = hz
  cv (hs x) = hs (cv x)
  cv (hl f) = hl (λ n → cv (f n))
  cv (hΩ κ g) = hΩ κ (λ c → cv (g c))

  cv-⊲ : ∀ {a b} {w : Wd (subW T P)} → a ⊲[ proj₁ w ] b → cv a ⊲[ w ] cv b
  cv-⊲ hself = hself
  cv-⊲ (hsuc p) = hsuc (cv-⊲ p)
  cv-⊲ (hlim n p) = hlim n (cv-⊲ p)
  cv-⊲ (hLim e p) = hLim e (cv-⊲ p)

  Lg-cv : ∀ a → LgB a → LgB (cv a)
  Lg-cv hz l = tt
  Lg-cv (hs a) l = Lg-cv a l
  Lg-cv (hl f) (st , l) = (λ {w} n → cv-⊲ {w = w} (st n)) , (λ n → Lg-cv (f n) (l n))
  Lg-cv (hΩ κ g) (mo , l) = (λ {w} lw e e′ p → cv-⊲ {w = w} (mo lw e e′ p)) , (λ c lc → Lg-cv (g c) (l c lc))
```

## §2 闭项

```agda
open SW GΛ shΛ
open Cv {KΛc} {Uf}

lΛB : LgB NT₁.ΛB
lΛB = (λ n → ⊞-fst (NT₁.Bᴧ n) (ιΛ (suc n) (NT₁.inc n))) , NT₁.lBᴧ

Λᵁ : HB (step TU)
Λᵁ = up (cv NT₁.ΛB)

lΛᵁ : LgB Λᵁ
lΛᵁ = Lg-up (cv NT₁.ΛB) (Lg-cv NT₁.ΛB lΛB)

one⊲ᵁ : ∀ {w} → hs hz ⊲[ w ] Λᵁ
one⊲ᵁ = hlim 0 (hsuc hself)

collS : Σ A Lg
collS = collLv genU (ldU LdΛ) flU Λᵁ lΛᵁ one⊲ᵁ (lvU Λᵁ)

TS : A
TS = proj₁ collS

Lg-TS : Lg TS
Lg-TS = proj₂ collS

fghS : ℕ → ℕ
fghS = FLv.FGH (ordK TS)
```

## §3 形状定理

第 1 站读回分量 `inj₂ (jx f)` 里的底拷贝 (下标含函数 $f$):

```agda
κj : (ℕ → H₀) → K KΛc
κj f = 1 , (inj₂ (jx f) , (0 , tt))

old-lossy-lv : ∀ f → lvΛ (κj f) ≡ inj₂ tt
old-lossy-lv f = refl

old-lossy-fb : ∀ f → fbA GΛ (κj f) ≡ inj₂ tt
old-lossy-fb f = refl

new-lv : ∀ f → Σ (KLv TU tpU Λᵁ (κj f)) (λ L → lvU Λᵁ (κj f) ≡ inj₁ L)
new-lv f = _ , refl

-- 每个底拷贝都有 (对一切底拷贝, 不只是 κj f)
all-bot-lv : ∀ κ → Bot shΛ κ → Σ (KLv TU tpU Λᵁ κ) (λ L → lvU Λᵁ κ ≡ inj₁ L)
all-bot-lv κ b = lv-bot Λᵁ κ b

-- 后面各站的头种类 (坐标是高度) 仍有损
head-still-lossy : ∀ s (c : HB (Kc (suc s))) → lvU Λᵁ (suc (suc s) , (inj₂ (hs c) , inj₂ tt)) ≡ inj₂ tt
head-still-lossy s c = refl
```

`no-upAllR` 的世界 `w′` (分量 `inj₁ tt` 的底拷贝界 $0$, 分量 `inj₂ hz` 的底拷贝界 $2$) 不满足 "每份底拷贝同界":

```agda
two≢z : ¬ (asuc (asuc azero) ≡ azero)
two≢z ()

w′-not-Uf : ¬ SW.Uf (genKc 1) (shKc 1) w′
w′-not-Uf (a , al) = two≢z (trans (al (inj₂ hz)) (sym (al (inj₁ tt))))
```

在第 1 站 `K₁ = Kc 1` 上 (否定一路 `NegKindLvRaise`, `NegRsOwnPre` 的对象) 同样: 读回分量 `inj₂ (jx f)` 的底拷贝 `κ₁ f` 在带不变式的世界上有 `RsK` (即 `KLv` 的三条升界律), 对一切 $f$:

```agda
module S₁ = SW (genKc 1) (shKc 1)

κ₁ : (ℕ → H₀) → K K₁
κ₁ f = inj₂ (jx f) , (0 , tt)

rsK₁ : ∀ f → RsK S₁.TU S₁.tpU (κ₁ f)
rsK₁ f = S₁.rsB (κ₁ f) tt
```

## §4 结论 (按档)

- **[构造]** `TS : A`, `Lg-TS`, `fghS`: 无条件闭项; 塔同 `KindLvTw.NT₁`, 最终坍缩在带不变式的世界上, 一切底拷贝按 `KLv` 回灌.
- **[定理]** `old-lossy-lv`, `old-lossy-fb`, `new-lv`, `all-bot-lv`, `head-still-lossy`, `w′-not-Uf`; **[构造]** `rsK₁` (`K₁` 上一切 $f$ 的 `κ₁ f`).
- **[判断]** 值: 没有 `ord` 的比较定理, 不说 `TS` 与 `KindLvTw.TK` 谁大. 与 `TK` 的差 (类型事实): 第 0 层目标下, 一切底拷贝的闭包结点从有损 (或只升一份) 换成 "升一切底拷贝到同一个 $v$" 的回灌; 坐标是高度的种类 (`head-still-lossy`) 不变; `KindLvTw` 里唯一的级回灌种类 `κ₁` (坐标是高度, 级 $1$) 在这里**不**按级回灌 (它不是底拷贝), 所以 `TS` 不是 `TK` 的加强, 是另一种取舍.
