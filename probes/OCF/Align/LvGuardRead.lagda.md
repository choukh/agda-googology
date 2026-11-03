# 读回, 第二层: 树上的目标 1 回到层号 (只有定义)

> 不含记号. 结论写在 [LvGuard](LvGuard.lagda.md). `rbO`: 第 1 层的树 (带字面闭包 `oŝ`, 待计值链 `oĉ`) 读回 `LG`. **`oŝ c t g` 读成带守卫的闭包 `lc c t g`: 这就是层号要有守卫的原因.** `F⁺ x`: $\psi_1(\Omega_x)$, $x$ 是任何带证书的层号. 目标 1 要一条字面路径 (`q`): 目标的路径是输入. **这里只有定义: `F⁺` 的 `WF` 没有写, 所以 `good-feed` 对层号下标还是开放的.** 与 [LvGuardUni](LvGuardUni.lagda.md) 对照: `Ordᴵ` 下标的那一半是定理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvGuardRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Align.Level using (Ordᴵ; _⊑ᴵ_; zero; suc; lim)
import OCF.Align.Level as Lvl
open import OCF.Align.LvGuardBase
open Lv Dom₀
open import OCF.Align.LvGuardTree

emO : Ordᴵ → O zero tz
emO zero = o0
emO (suc a) = os (emO a)
emO (lim f s) = ol (λ n → emO (f n))

rbO : ∀ {π} → O (suc zero) π → LG
rbO o0 = zero
rbO (os a) = suc (rbO a)
rbO (ol F) = lim (λ n → rbO (F n))
rbO (oŝ c t g) = lc c (rbO t) (λ η e → rbO (g η e))
rbO (oĉ c z zg o₀ o) = lc c (rbO o₀) (λ η e → rbO (o η e))
rbO (owk w x) = rbO x
rbO (oΩ zero cv h) = lc (suc Lvl.zero) (rbO (h tz (emO (suc Lvl.zero)))) (λ η e → rbO (h tz (emO η)))
rbO (oΩ (suc ()) _ _)
rbO (ocl (suc ()) _ _ _ _)

-- ψ₁(Ω_x): 目标 1 的字面路径 q 与表 E 是输入
F⁺ : (x : LG) → Cfˢ x → (E : Ents) → (q : suc zero < x) → Adm (tab E) q → LG
F⁺ x (w , s) E q aq = rbO (Fold.ψ x w s {π = tz} {ρ = tz} E (Fold.tp q aq) (λ ()) (Ω̇ x))
```
