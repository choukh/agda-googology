# 验收: 与带标签的树比

> **验收文件.** 只有这里读 `OCF.Free` 的树 (标签贴在它上面, 见 [OCF.Free.Bridge](../Free/Bridge.lagda.md) 的 `label-on-free`). 全部是 **有限测试**, `refl`, 不是定理. 比较器 `fpO`, `fpZ`: 指纹, 只读形状 (零, 后继, 极限的前 $w$ 项), 深度 $d$ 截断, 不读后面的项.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Data.Empty
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (Ordᶜ; Ordᴵ; natᴵ; _<ᴵ_)
import OCF.Free.Level as FL
open import OCF.Free.Prefix using (Z; toZ; Ωˢ)
open import OCF.Free.Floor using (fz; fk; _⊔_)
import OCF.Free.Tree as FT
open import OCF.Align.CumReadCF
open import OCF.Align.CumReadBase using (Ord₀; natO)
open import OCF.Align.CumReadCFThm using (Y)
open import OCF.Align.CumReadTop using (ysᶜ; one)
```

## §1 指纹

```agda
data Fp : Set where
  stop : Fp
  fz′  : Fp
  fs′  : Fp → Fp
  fl′  : List Fp → Fp

take : ℕ → (ℕ → Fp) → List Fp
take zero F = []
take (suc w) F = F 0 ∷ take w (λ n → F (suc n))

fpO : ℕ → ℕ → Ord₀ → Fp
fpO zero w x = stop
fpO (suc d) w FL.zero = fz′
fpO (suc d) w (FL.suc x) = fs′ (fpO d w x)
fpO (suc d) w (FL.lim f) = fl′ (take w (λ n → fpO d w (f n)))
fpO (suc d) w (FL.limᵢ () f)
fpO (suc d) w (FL.up () x)

fpZ : ℕ → ℕ → Z → Fp
fpZ zero w x = stop
fpZ (suc d) w Z.zero = fz′
fpZ (suc d) w (Z.suc x) = fs′ (fpZ d w x)
fpZ (suc d) w (Z.lim f) = fl′ (take w (λ n → fpZ d w (f n)))
fpZ (suc d) w (Z.ĉᴸ c t g o₀ o) = stop
```

## §2 $\psi_0(\Omega_n)$: 新折叠对 `OCF.Free` 的 `ψ̄ ∘ tl`

`natA n` 的新树, 对 `OCF.Free` 的树 (对任何下标写得出, 不要证书). 这里只比闭包以下的树, 这些树在 `OCF.Free` 里也是 `zero`, `suc`, `lim`.

```agda
natA : ℕ → A
natA zero = azero
natA (suc n) = asuc (natA n)

lgn : ∀ n → Lg (natA n)
lgn zero = tt
lgn (suc n) = lgn n

zlt : ∀ (η : Ordᴵ) → FL.zero <ᴵ FL.suc η → FL.zero <ᴵ FL.suc η
zlt η p = p

zn : ∀ n → FL.zero <ᴵ FL.suc (natᴵ n)
zn zero = FL._<ᴵ_.zero
zn (suc n) = FL._<ᴵ_.suc (zn n)

-- OCF.Free 的分支 ψ₀(Ω_η) 的只读像, 下标 η 任意
gI : (η : Ordᴵ) → FL.zero <ᴵ FL.suc η → Z
gI η z = toZ (FT.ψ̄ (FT.tl {c = FL.zero} (fz ⊔ fk η) (λ e q → proj₂ e (FL._<ᴵ_.suc q)) (Ωˢ η)) (tt , (λ q → q)) z)

gF : ℕ → Z
gF n = gI (natᴵ n) (zn n)

_ : fpO 8 3 (Y (natA 0) (lgn 0)) ≡ fpZ 8 3 (gF 0)
_ = refl

_ : fpO 8 3 (Y (natA 1) (lgn 1)) ≡ fpZ 8 3 (gF 1)
_ = refl

_ : fpO 8 3 (Y (natA 2) (lgn 2)) ≡ fpZ 8 3 (gF 2)
_ = refl

_ : fpO 8 3 (Y (natA 3) (lgn 3)) ≡ fpZ 8 3 (gF 3)
_ = refl
```

对照: 比较器分得开.

```agda
ctl : fpO 4 3 (Y (natA 1) (lgn 1)) ≡ fpZ 4 3 (gF 0) → Data.Empty.⊥
ctl ()
```
