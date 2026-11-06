# 整座塔加对角 (四): 有限测试, 读法 σ₀ 在第一站的输出上

> 不含记号. 入口 [LvTop](LvTop.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. **本篇全是有限测试 (计算, `refl`), 不是证明.**
>
> 全塔版本 (`LvTopInst.FullΛ`) 的读法是 `LvRdWk.σ₀`. 若给定的 `FoldAt` 在码目标 $0$ 上与 `foldFin` 一样输出 `Ωtop S₀` (第 1 级的级顶, `LvRdFold.Hn 0`), 第 2 站的界就是 $0\boxplus\sigma_0(\Omega_{\mathrm{top}}S_0)$. 测试:
>
> - `t-head`: $\sigma_0(\Omega_{\mathrm{top}}S_0)$ 最外是 ℕ-极限.
> - `t-br0` … `t-br3`, `t-br5`: 它的第 $0,1,2,3,5$ 支都是字面的 $0$ (`isFin` 给 `just 0`).
> - `t-H1`: 对照, $\sigma_0(H_1)$ (`Hn 1`, 第 2 级的级顶) 最外是 ℕ-极限, 第 $3$ 支最外仍是 ℕ-极限 (不是 $0$).
>
> 比较器: 最外构造子 `hd` 与 "字面有限" `isFin`, 只看所列的支. 盲区: 别的支, 更深的结构, 值. 读法 (判断): 在测到的支上, $\sigma_0$ 把第 1 级的级顶读成 $0$ 的 ℕ-极限; 全塔第 2 站的界在这些支上没有长高. 这不说明全塔不长 (第 2 站之后的输出由给定的 `FoldAt` 决定), 只说明 "$\sigma_0$ 让层号逐站长高" 在第一站没有被测到.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvTopTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.LvRdWk using (σ₀)
open import OCF.Align.LvRdFold using (Hn)

-- 0: hz, 1: hs, 2: hl, 3: hΩ
hd : HB S₀ → ℕ
hd hz = 0
hd (hs _) = 1
hd (hl _) = 2
hd (hΩ _ _) = 3

isFin : HB S₀ → Maybe ℕ
isFin hz = just 0
isFin (hs t) with isFin t
... | just n = just (suc n)
... | nothing = nothing
isFin (hl _) = nothing
isFin (hΩ _ _) = nothing

br : HB S₀ → ℕ → HB S₀
br (hl f) n = f n
br (hΩ _ g) n = g azero
br t n = t

t-head : hd (σ₀ (Ωtop S₀)) ≡ 2
t-head = refl

t-br0 : isFin (br (σ₀ (Ωtop S₀)) 0) ≡ just 0
t-br0 = refl

t-br1 : isFin (br (σ₀ (Ωtop S₀)) 1) ≡ just 0
t-br1 = refl

t-br2 : isFin (br (σ₀ (Ωtop S₀)) 2) ≡ just 0
t-br2 = refl

t-br3 : isFin (br (σ₀ (Ωtop S₀)) 3) ≡ just 0
t-br3 = refl

t-br5 : isFin (br (σ₀ (Ωtop S₀)) 5) ≡ just 0
t-br5 = refl

t-H1 : (hd (σ₀ (Hn 1)) ≡ 2) × (hd (br (σ₀ (Hn 1)) 3) ≡ 2)
t-H1 = refl , refl
```
