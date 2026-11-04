# 累加树在 $\psi_0(\Omega_{\Omega+1})$: 有限测试

> **验收文件, 全部是有限测试 (`refl`), 不是定理.** 读 `OCF.Free` 过基本列验收的树 `TF 1`. 比较器 `same d w`: 指纹 `fpO` 比到深度 $d$, 宽度 $w$, 只读形状. `le d w`: 截断的 $\preccurlyeq$, 深度用完算真, 宽度外的项不看. 盲区: `le` 的真假都可能是截断造成的, 它不是 $\preccurlyeq$ 的判定, 也不是上下界的证据; `same` 不读第 $w$ 项之后, 不读第 $d$ 层之下.
>
> 记录: `TΩ+1` 与 `TF 1` 的形状从第 0 项深度 5 起就不同 (`no-t0`). 第 0 项是 $\psi_0(\Omega_\Omega)$, 在这一项上序数值相等已是定理 (`CumVal.TΩ≈` 对 `BTBOᴵ`), 所以这个形状差本身不说明掉值或超值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1CumTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (Ord₀)
open import OCF.Align.CumVal using (TΩ; TΩ+1)
open import OCF.Align.CumUpAcceptF using (TF; same)

term : Ord₀ → ℕ → Ord₀
term (FL.lim f) n = f n
term _ n = FL.zero

L R : Ord₀
L = TΩ+1
R = TF 1

all′ any′ : ℕ → (ℕ → Bool) → Bool
all′ zero p = true
all′ (suc w) p = p w ∧ all′ w p
any′ zero p = false
any′ (suc w) p = p w ∨ any′ w p

le : ℕ → ℕ → Ord₀ → Ord₀ → Bool
le zero w x y = true
le (suc d) w FL.zero y = true
le (suc d) w (FL.suc x) FL.zero = false
le (suc d) w (FL.suc x) (FL.suc y) = le d w x y
le (suc d) w (FL.suc x) (FL.lim g) = any′ w (λ j → le d w (FL.suc x) (g j))
le (suc d) w (FL.suc x) (FL.limᵢ () g)
le (suc d) w (FL.suc x) (FL.up () g)
le (suc d) w (FL.lim f) y = all′ w (λ i → le d w (f i) y)
le (suc d) w (FL.limᵢ () f) y
le (suc d) w (FL.up () x) y
```

## §1 形状从哪里开始不同

```agda
ok-t0 : same 4 2 (term L 0) (term R 0) ≡ true
ok-t0 = refl

no-t0 : same 5 2 (term L 0) (term R 0) ≡ false
no-t0 = refl
```

## §2 截断的比较是瞎的

`le-LR`, `le-RL` 两边都真. 但 `blind` 说同一个比较器也认为 `TΩ+1` $\preccurlyeq$ `TΩ`, 而 `Om1CumGrow.step-Ω+1` 证了反面. 所以 `le` 到这个深度分不开相差一整站的两棵树, **这几条 `true` 不是上下界的证据**. `le 12 2 R L`, `le 7 3 R L` 在 40 秒内算不完 (退出码 124, 计时观察).

```agda
le-LR : le 9 2 L R ≡ true
le-LR = refl

le-RL : le 9 2 R L ≡ true
le-RL = refl

le-LR′ : le 12 2 L R ≡ true
le-LR′ = refl

blind : le 12 2 L TΩ ≡ true
blind = refl
```
