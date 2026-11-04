# 验收: 高度世界的树对 `OCF.Free` 带标签的树

> **验收文件**. `TF n` 是 `OCF.Free` 的 $\psi_0(\Omega_{\Omega+n})$, `FC.TΩ₂` 是 $\psi_0(\Omega_{\Omega\cdot2})$, 标签贴在它们上面 (`Free/Bridge`). **全部是有限测试** (`refl`), 比较器 `fpO d w`: 深度 $d$, 宽度 $w$, 只读形状. 盲区: 不读第 $w$ 项之后, 不读第 $d$ 层之下, 形状相同不等于树相同. 这不是基本列验收, 不是前驱结构验收, 也不是序数值验收.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpAcceptF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.Free.Level using (natᴵ)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Main using (GᴺΩ̇)
open import OCF.Free.Tree using (Fl)
open import OCF.Free.Floor using (Ev)
import OCF.Free.Closed as FC
open import OCF.Align.CumReadAccept using (fpO)
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumReadCF using (azero; z⊲)
open import OCF.Align.CumReadW using (one; g₀)
open import OCF.Align.CumUpW using (Tψ)
open import OCF.Align.CumUpAccept using (T+)

ev₀ : Ev (FL.suc FL.zero) Fl
ev₀ = tt , (λ q → q)

TF : ℕ → Ord₀
TF n = forceᴺ _ (GᴺΩ̇ (natᴵ n) ev₀ FL._<ᴵ_.zero)

t0 : fpO 4 2 (T+ 0) ≡ fpO 4 2 (TF 0)
t0 = refl
t1 : fpO 4 2 (T+ 1) ≡ fpO 4 2 (TF 1)
t1 = refl
t2 : fpO 4 2 (T+ 2) ≡ fpO 4 2 (TF 2)
t2 = refl

T·2 : Ord₀
T·2 = Tψ 2 azero one g₀ (z⊲ one)

t·2 : fpO 4 2 T·2 ≡ fpO 4 2 FC.TΩ₂
t·2 = refl
```

## 比较器能走多深

`same d w x y`: 比较到深度 $d$, 宽度 $w$. 下面记录每一对最后相等的深度和第一次不等的深度. **有限测试.** 第一次不等来自累加的毛刺 (链的下标不同), 不否定序数值; 反过来, 相等只说明顶上几层形状相同.

```agda
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import OCF.Align.CumReadAccept using (Fp; stop; fz′; fs′; fl′)
open import OCF.Align.CumReadTop using (Tᶜ)

eqF : Fp → Fp → Bool
eqL : List Fp → List Fp → Bool
eqF stop stop = true
eqF fz′ fz′ = true
eqF (fs′ a) (fs′ b) = eqF a b
eqF (fl′ a) (fl′ b) = eqL a b
eqF _ _ = false
eqL [] [] = true
eqL (a ∷ x) (b ∷ y) = eqF a b ∧ eqL x y
eqL _ _ = false

same : ℕ → ℕ → Ord₀ → Ord₀ → Bool
same d w x y = eqF (fpO d w x) (fpO d w y)
```

```agda
ok₀ : same 4 2 (T+ 0) (TF 0) ≡ true
ok₀ = refl
no₀ : same 5 2 (T+ 0) (TF 0) ≡ false
no₀ = refl
ok₁ : same 5 2 (T+ 1) (TF 1) ≡ true
ok₁ = refl
no₁ : same 6 2 (T+ 1) (TF 1) ≡ false
no₁ = refl
ok₂ : same 6 2 (T+ 2) (TF 2) ≡ true
ok₂ = refl
ok·2 : same 6 2 T·2 FC.TΩ₂ ≡ true
ok·2 = refl
no·2 : same 7 2 T·2 FC.TΩ₂ ≡ false
no·2 = refl
okᶜ : same 7 2 (T+ 0) Tᶜ ≡ true
okᶜ = refl
okᶜ′ : same 5 3 (T+ 0) Tᶜ ≡ true
okᶜ′ = refl
ctl-TF : same 4 2 (T+ 0) (T+ 1) ≡ false
ctl-TF = refl
```

