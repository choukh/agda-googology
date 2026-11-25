# YiKB 折叠: 一步坍缩与沿字面路径的下行

> 空白页独立样本 (只导入标准库与 YiKBBlock). 一步坍缩 `step ℓ acc t` 读作 "`acc` 加 ω 的 `t` 的坍缩次幂", 落在前驱或基底; `down ℓ e` 沿路径 `e : ℓ ↘ a` 逐步坍缩; `Ωtop ℓ` 是第 `ℓ` 层的顶 (Ω_ℓ).
> 闭项: `twᶜ n` (塔第 n 项, 读作 ψ₀(Ω_{tw n}), 读法是判断), `EBOᶜ` (读作 ψ₀(Λ)); 合法性由类型保证.
> 不否定什么; 值的定理与测试在 YiKBProps, YiKBTest.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKBFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import OCF.Lean.YiKBBlock
```

## 辅助

`join a b` 是两项的 ℕ 极限 (二元上确界); 它让叶上的结果同时不低于 `suc acc` 与孩子的坍缩, 不需要加法.

```agda
iter : {A : Set} → (A → A) → ℕ → A → A
iter f zero    x = x
iter f (suc n) x = f (iter f n x)

two : {A : Set} → A → A → ℕ → A
two a b zero    = a
two a b (suc _) = b

join : ∀ {P D F} → Tr P D F → Tr P D F → Tr P D F
join a b = lim (two a b)
```

## 层的顶

`Ωtop (s ℓ)` 是在 `T ℓ` 上分支的恒等; 上确界结点的顶是各孩子的顶的上确界, 沿下标类型分支 (ℕ 下标时是 ℕ 极限). 塔的第 n+1 层的顶因此是 `c ↦ Ωtop (lev c)` 的 Ω 分支: 龙骨写在这里.

```agda
Ωtop : (ℓ : L) → T ℓ
Ωtop z                   = suc zero
Ωtop (s ℓ)               = br top lf
Ωtop (sp b iℕ g w)       = lim (λ n → lf (pk n (Ωtop (g n))))
Ωtop (sp b (inj₂ q) g w) = br q (λ x → lf (pk x (Ωtop (g x))))
```

## 嵌入上的幂

`E e acc t`: `t` 在低若干个后继的层里, 结果是 `acc + ω^t`, 落在高层. 分支位置字面搬上去. 上确界结点的叶在这里只记作 `suc acc` (下界式的简化, 不比较孩子).

```agda
E : ∀ {a b} → a ≤ˢ b → T b → T a → T b
E e acc zero     = suc acc
E e acc (suc t)  = lim (λ n → iter (λ r → E e r t) n acc)
E e acc (lim f)  = lim (λ n → E e acc (f n))
E e acc (br p h) = br (lift e p) (λ x → E e acc (h (coe e p x)))
E {a = s a}          e acc (lf t) = E (pre e) acc t
E {a = sp _ _ _ _}   e acc (lf _) = suc acc
```

## 一步坍缩与下行

`pd ℓ` 是坍缩的落点: 后继的前驱, 上确界结点的基底. 目标对一切孩子一致: `gstep` 对两种层共用, 只有叶的处理不同; 分支只按位置的字面形状 (`top` / `low p`) 分两类, 顶上的分支取对角 ℕ 极限并把输出回灌, 低位置的分支保留. 上确界结点的叶 `pk x t` 沿结点里存的路径 `w x` 下行; 折叠从不比较两个孩子.

```agda
pd : L → L
pd z              = z
pd (s ℓ)          = ℓ
pd (sp b _ _ _)   = b

gstep : ∀ {P F F′} {D : P → Set} → (Tr P D F′ → F → Tr P D F′) →
        Tr P D F′ → Tr (⊤ ⊎ P) (dom⁺ (Tr P D F′) D) F → Tr P D F′
gstep k acc zero           = suc acc
gstep k acc (suc t)        = lim (λ n → iter (λ r → gstep k r t) n acc)
gstep k acc (lim f)        = lim (λ n → gstep k acc (f n))
gstep k acc (br top h)     = lim (λ n → iter (λ x → gstep k acc (h x)) n acc)
gstep k acc (br (low p) h) = br p (λ x → gstep k acc (h x))
gstep k acc (lf u)         = k acc u

step   : (ℓ : L) → T (pd ℓ) → T ℓ → T (pd ℓ)
leafsp : ∀ b i g w → T b → Lf (sp b i g w) → T b
down   : (ℓ : L) {a : L} → ℓ ↘ a → T ℓ → T a

step z            acc t = t
step (s ℓ)        acc t = gstep (E rf′) acc t
step (sp b i g w) acc t = gstep (leafsp b i g w) acc t

leafsp b i g w acc (pk x t) = join (suc acc) (down (g x) (w x) t)

down ℓ                rf       t = t
down ℓ                (ch x e) t = lf (pk x (down ℓ e t))
down (s ℓ)            (ss e)   t = down ℓ e (step (s ℓ) (Ωtop ℓ) t)
down (sp b i g w)     (sb e)   t = down b e (step (sp b i g w) (Ωtop b) t)
```

## 闭项

```agda
T₀ : Set
T₀ = T z

twᶜ : ℕ → T₀
twᶜ n = down (tw n) (tw↘ n) (Ωtop (tw n))

EBOᶜ : T₀
EBOᶜ = down Λ (sb rf) (Ωtop Λ)
```
