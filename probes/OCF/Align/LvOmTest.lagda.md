# Ω-极限坐标上的读回包 (六): 有限测试 (计算)

> 不含记号. 入口 [LvOm](LvOm.lagda.md). **这是测试, 不是证明**: 对一棵具体的树用 `refl` 计算读回的头结点. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 树 `t₁`: 层号 ΩA 的读回层里, 世界 $(\omega,0)$ 上一个过第 1 支本层的结点 (证据 `lim 1 self` : $1\lhd\omega$), 继续是 $0$. 在 $(\omega,0)$ 上读回:
>
> - 外层世界 $\omega$: 判定 $1\lhd\omega$ 为真, 读成种类 $((1,\mathrm{lim}\,1\,\mathrm{self}),\text{new})$ 的结点 (`keep`).
> - 外层世界 $0$: 判定 $1\lhd0$ 为假, 结点丢掉, 读回是底 $0$ (`drop`).
>
> 比较器有分辨力: 两个读回的头一个是结点一个不是.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvOmTest where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Wd₂; D; ni; sL; n0; κA)
open import OCF.Align.LvOmLev
open import OCF.Align.LvOmRd
open import OCF.Align.LvOmFold using (hA₀; ΩA; ωA; Lg-ωA)

hd : ∀ {T} → HB T → Maybe (K T)
hd (hΩ κ _) = just κ
hd _ = nothing

Wω : Wd₂
Wω = ωA , hz

e1 : asuc azero ⊲ ωA
e1 = C.lim 1 C.self

t₁ : D (Ly ΩA) Wω
t₁ = ni (sL {κ = κA} {c = asuc azero} e1 hself) (λ _ _ _ → n0)

rdω : HB (LvM.Lv ωA ΩA)
rdω = Rd.rdc ωA (Rd.pk ωA ΩA) Wω (C.self , hself) (Lg-ωA , tt) C.self hz t₁

rd0 : HB (LvM.Lv azero ΩA)
rd0 = Rd.rdc azero (Rd.pk azero ΩA) Wω (C.self , hself) (Lg-ωA , tt) (z⊲ ωA) hz t₁

keep : hd rdω ≡ just ((asuc azero , e1) , inj₂ tt)
keep = refl

drop : rd0 ≡ hz
drop = refl

-- 比较器有分辨力
sep : rdω ≡ hz → ⊥
sep ()
```
