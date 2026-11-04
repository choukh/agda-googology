# 验收: 带闭包的新树对 `OCF.Free` 的树

> **验收文件.** `TF n` 是 `OCF.Free` 的 $\psi_0(\Omega_{\Omega+n})$ (带证书, 标签贴在它上面). 下面都是 **有限测试**, `refl`, 比较器 `fpO` (深 4, 宽 2, 只读形状), 很弱: 只看第 0, 1 项的前几层. 对照 `ctl-TF`: 比较器分得开 $\Omega$ 与 $\Omega+1$. `f0`, `f1`: `fgh` 算得动, 只在 0 处, 没有比较.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadAcceptW where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Empty
import OCF.Free.Level as FL
open import OCF.Free.Level using (natᴵ; Ordᴵ; _<ᴵ_)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Main using (GᴺΩ̇)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.CumReadAccept using (Fp; fpO; natA; lgn)
open import OCF.Align.CumReadWLv
open import OCF.Align.CumReadBase using (Ord₀)

ev₀ : Ev (FL.suc FL.zero) Fl
ev₀ = tt , (λ q → q)

TF : ℕ → Ord₀
TF n = forceᴺ _ (GᴺΩ̇ (natᴵ n) ev₀ FL._<ᴵ_.zero)

t0 : fpO 4 2 Tᵂ₁ ≡ fpO 4 2 (TF 0)
t0 = refl

t1 : fpO 4 2 (TΩ+ (natA 1) (lgn 1)) ≡ fpO 4 2 (TF 1)
t1 = refl

t2 : fpO 4 2 (TΩ+ (natA 2) (lgn 2)) ≡ fpO 4 2 (TF 2)
t2 = refl

f0 : fgh (TP 0) 0 ≡ 1
f0 = refl
f1 : fgh (TP 1) 0 ≡ 1
f1 = refl

ctl-TF : fpO 4 2 (TF 0) ≡ fpO 4 2 (TF 1) → Data.Empty.⊥
ctl-TF ()
```
