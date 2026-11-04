# 协调者给的候选: `Rs` (切口) 能不能进判据

> **这个文件写在两次盲测封存之后.** 时间: 第一次封存 18:43, 第二次封存约 18:50, 看到候选的消息在 18:51 (都是 2026-11-03). 我在那之前没有读过 `GuardRead*`. 盲测的预测没有改. 结论写在 [TreeJudge](TreeJudge.lagda.md). 不含记号. `GuardRead*` 是别的智能体同时写的文件, 这个文件只导入, 不改.
>
> **`Rs` 不能作这份判据要的 "树的判官": 这一份列表上错的树, 它一棵也拒绝不了, 因为错不在层号上.** 它是另一样有用的东西: 写下一步的**生成器**. `Tc-of` 由 `Rs` 给紧读法, 对一切 `Good` 的第 1 层项. 与 `HF` 的关系: `Rs` 给读法, `HF` 在树上查读法. 下面的 §4 是两者独立写出来之后对上的证据.
>
> - §1 `rs-static`, `rs-Ω2`: 静态替身的输入与正确的输入都是 `Rs`; $\Omega\cdot2$ 也是, 而它上面 `Tc-id` 与没有 `trim` 的树都被 `HF` 拒绝 ([TreeJudgeCheckBad](TreeJudgeCheckBad.lagda.md)). 编译过.
> - §2 `sp-total` (**条件定理**, 条件 `Tot` 是经典的全序): 第 0 层上 $a$ 是任何 $y$ 的切口. **所以切口不是外延的限制, 是构造性的证据.** 第 1 层没有写 (`s-mv` 不跨层, `up` 要另外处理), 判断: 同样.
> - §3 `rs-cont`: `Rs` 不是空条件: `Cont` 拒绝不连续的分支函数 (编译过). 但列表上没有一棵错树错在这里.
> - §4 有限测试: `Tc-F1` ([TreeJudgeRdF](TreeJudgeRdF.lagda.md), 我写的) 与 `Tc-F` (`GuardReadRd`, 由 `Rs` 给) 在 $\psi_1(\Omega)+1$ 上指纹相同. `HF` 接受 `Tc-Lv₅`, 拒绝 `Lv₅+1` 上的 `Tc-id`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeRs where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.GuardTightCum using (Ordᴵ; Ordᶜ; natᴵ; ωᴵ; Ω; Ω-refl; add; _+_; _≅_; z≅; s≅; l≅; zero; suc; lim; limᵢ; up)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (suc)
import OCF.Align.GuardTightUni as Uni
open Uni Dom₀ using (em; em-self; F; Lv₅; Cf-F; Cf-Lv₅; _⊑ᵒ_; s-inv; l-inv)
open import OCF.Align.GuardTightBase using (Tc-id)
open import OCF.Align.GuardTightTree using (T₀)
open import OCF.Align.GuardReadCut using (Sp; s-zero; s-eq; s-mv; s-suc; s-lim)
open import OCF.Align.GuardReadRs using (Rs; Rs-Ω; Rs-add; ri; rz; rs; rl)
open import OCF.Align.GuardReadRd using (Tc-F; Tc-Lv₅)
open import OCF.Align.TreeJudgeBlind using (sucCf)
open import OCF.Align.TreeJudgeBlind2 using (TE⁺; W₁; Cf-W)
open import OCF.Align.TreeJudgeObs
open import OCF.Align.TreeJudgeRead using (rd)
```

## §1 `Rs` 看不见这些错

$\Omega+\omega$ 与 $\Omega+\Omega$ 都是 `Rs`. 把前者当后者是 `static-rejected` 的错, 错在树与输入的关系, 不在任何一个项上. $\Omega\cdot2$ 是 `Rs`: 同一个层号上有紧读法也有恒等读法, 错的是读法的选择; `UniformLvTree` 同样 (判断: 它的层号类型 `LI` 不是 `Ordᶜ`, 这里写的是同一个序数的项).

```agda
c : Ordᶜ (suc zero)
c = Ω (suc zero)

e-c : c ≅ c
e-c = Ω-refl (suc zero)

rsE : ∀ η → Rs (em η)
rsE zero = rz
rsE (suc a) = rs (rsE a)
rsE (lim f s) = rl (λ n → rsE (f n))

rs-static : Rs (add c (λ q → suc q) (em ωᴵ))
rs-static = Rs-add (Rs-Ω (suc zero)) e-c (rsE ωᴵ) (em-self ωᴵ)

rs-Ω2 : Rs (c + c)
rs-Ω2 = Rs-add (Rs-Ω (suc zero)) e-c (Rs-Ω (suc zero)) e-c
```

## §2 切口不是外延的限制 (条件定理)

**条件 `Tot`, 不是定理:** 第 0 层的树在 $\sqsubseteq^{\mathsf o}$ 下全序 (经典地成立, 构造地就是壁垒要禁止的那类东西). 在这个条件下 $a$ 是任何 $y$ 的切口. 所以 `Sp` 的内容全在 "证据由结构给出", 不在 "哪些 $y$ 过得了".

```agda
module Total (Tot : (a b : Ordᶜ zero) → a ≅ a → b ≅ b → (a ⊑ᵒ b) ⊎ (suc b ⊑ᵒ a)) where
  sp-total : ∀ (a y : Ordᶜ zero) → a ≅ a → y ≅ y → Sp a y
  sp-total a zero ea ey = s-zero ea
  sp-total a (suc b) ea ey with Tot a b ea (s-inv ey)
  ... | inj₁ le = s-suc le (s-inv ey) (sp-total a b ea (s-inv ey))
  ... | inj₂ le = s-mv le (s-eq ea)
  sp-total a (lim h) ea ey = s-lim (λ n → sp-total a (h n) ea (l-inv ey n))
  sp-total a (limᵢ () f) ea ey
  sp-total a (up () x) ea ey
```

## §3 `Cont` 是真的限制

分支函数在极限处跳到 0. 不是 `Rs`. 这说明条件不空. **列表上的错树没有一棵错在这里.**

```agda
jump : Ordᶜ zero → Ordᶜ (suc zero)
jump zero = suc zero
jump (suc _) = suc zero
jump (lim _) = zero
jump (limᵢ () _)
jump (up () _)

rs-cont : Rs (limᵢ zero jump) → ⊥
rs-cont (ri hb st ct) with ct (λ _ → zero) (λ _ → z≅)
... | ()
```

## §4 与 `HF` 的对照 (有限测试)

- **`same-F1`: 我的 `Tc-F1` 与 `Rs` 给的 `Tc-F 1` 在 $\psi_1(\Omega)+1$ 上指纹相同 (看界, 深 9, 宽 2).** 两个读法是分别写的: 我写 `Tc-F1` 时没有读 `GuardRead*`; `GuardRead*` 的作者没有 `HF`. 这个比较是在看到消息之后做的.
- **`hf-L5s`, `hf-L5s-id`: 第 5 站之上的第一个点.** `HF` 接受 `Tc-Lv₅`, 拒绝 `Tc-id`; 948 个闭包. `Tc-Lv₅` 写的时候不知道 `HF`, 所以这是 `HF` 的一次独立检验. **不算盲测:** 我先看了消息与 `GuardRead` 的结论 (`bound-Lv₅`), 才跑这一条.
- `hf-L5`: 第 5 站本身, 30 个闭包, 两个读法都不报. 取样力量不够, 不说明恒等读法在那里没问题.

```agda
TE⁺r TL TLid TLs TLsid : Obs
TE⁺r = rd (T₀ (suc W₁) (sucCf Cf-W) (Tc-F (suc zero)))
TL = rd (T₀ Lv₅ Cf-Lv₅ Tc-Lv₅)
TLid = rd (T₀ Lv₅ Cf-Lv₅ (Tc-id Lv₅))
TLs = rd (T₀ (suc Lv₅) (sucCf Cf-Lv₅) Tc-Lv₅)
TLsid = rd (T₀ (suc Lv₅) (sucCf Cf-Lv₅) (Tc-id (suc Lv₅)))

same-F1 : sameM 9 2 (just TE⁺) (just TE⁺r) ≡ true
same-F1 = refl

n-L5 : nclo 11 2 TL ≡ 30
n-L5 = refl
n-L5s : nclo 11 2 TLs ≡ 948
n-L5s = refl

hf-L5 : run 11 8 2 TL ≡ nothing
hf-L5 = refl
hf-L5-id : run 11 8 2 TLid ≡ nothing
hf-L5-id = refl
hf-L5s : run 11 8 2 TLs ≡ nothing
hf-L5s = refl
hf-L5s-id : run 11 8 2 TLsid ≡ just (vio (0 ∷ []) 1 (1 ∷ 101 ∷ 0 ∷ 500 ∷ 1 ∷ 500 ∷ 1 ∷ 1 ∷ []) 2)
hf-L5s-id = refl
```
