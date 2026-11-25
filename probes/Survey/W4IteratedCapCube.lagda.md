# 两次 Ω₁ 对角合成的正层原参照

第四层。原 src 闭项的全部构造均在原 src 内。对变动层号的两个方向分别递归，得到与 Level 闭项的同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedCapCube where

open import Data.Product using (_,_)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Align.BTBOValUp as U
import OCF.Align.BTBOValDn as D
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; l≼; ≼l; ≼i; i≼; ≼u; u≼)
import YiLAB10Src as Y
import B12LimitSrc as A
import B17RefAllSource as Src
import B24RExit as Exit
import Survey.W4IteratedCap as C
import Survey.W4IteratedCapSource as F
module S = Src.S
module B = Src.B

native : S.Ord₀ → A.Src₂
native S.zero = F.block Y.a
native (S.suc x) = F.block (native x)
native (S.lim f) = S.lim (λ n → native (f n))

regular : ∀ {x y} → x L.≅ y → C.family x L.≅ C.family y
regular L.z≅ = F.block-pres (L.Ω-refl _)
regular (L.s≅ d) = F.block-pres (regular d)
regular (L.l≅ d) = L.l≅ (λ n → regular (d n))

lo : ∀ y → U.Mh (native S.zero) (C.family y)
lo L.zero = F.Up.shift (A.Aligned.up A.omega2)
lo (L.suc y) = F.Up.grow (lo y)
lo (L.lim f) = U.Mlr 0 (lo (f 0))
back : ∀ x → D.Dn (C.family L.zero) (native x)
back S.zero = F.Downward.shift (A.Aligned.dn A.omega2)
back (S.suc x) = F.Downward.grow (back x)
back (S.lim f) = D.Rlr 0 (back (f 0))

up : ∀ x y → tr₀ x ≼ y → U.Mh (native x) (C.family y)
up (S.limᵢ () f) y d
up S.zero y z≼ = lo y
up (S.suc x) (L.suc y) (s≼s d) = F.Up.shift (up x y d)
up x (L.lim f) (≼l n d) = U.Mlr n (up x (f n) d)
up (S.lim f) y (l≼ d) = U.Mll (λ n → up (f n) y (d n))
up x _ (≼i {p = ()} _ _ _)
up x _ (≼u {r = ()} _)

dn : ∀ y x → y ≼ tr₀ x → D.Dn (C.family y) (native x)
dn y (S.limᵢ () f) d
dn L.zero x z≼ = back x
dn (L.suc y) (S.suc x) (s≼s d) = F.Downward.shift (dn y x d)
dn (L.lim f) x (l≼ d) = D.Rll (λ n → dn (f n) x (d n))
dn y (S.lim f) (≼l n d) = D.Rlr n (dn y (f n) d)
dn _ x (i≼ {p = ()} _)
dn _ x (u≼ {r = ()} _)

cube = S.limᵢ (B.suc B.zero) native
level = L.limᵢ (L.suc L.zero) C.family
source = S.ψ₀ (Src.pass cube)

aligned : A.Aligned cube level
aligned = A.aligned (U.Mii L.z≅ (λ s y d → up s y (U.Mh→≼ d)))
                    (D.Rii L.z≅ (λ y s d → dn y s (D.Dn→≼ d)))
                    (L.lᵢ≅ L.z≅ (λ x y d → regular d))
exact : tr₀ source ≈ᵛ C.value level
exact = A.fold (Exit.passed aligned)
```

经典地读正层参数时，写 Ω₁=ω₁。第一次分支内第 ξ 个参数的普通序数值为 p+Ω₁·(1+ξ)，对全部 ξ<ω₁ 取上确界得 p+Ω₁²。第二次分支从 Ω₂ 起，故整个参数的值为 Ω₂+Ω₁³。代码另以两个方向比较实际分支和折叠值。
