# 层号判决的范数模: 可数段上总判决存在

> 底座 [InaccModulusBase](InaccModulusBase.lagda.md) 不含记号, 其导入链里没有 `OCF.Align.EBO`. 本文件与 `Lift`、`Lift2`、`Term`、`Size`、`NF`、`Rank`、`Accept`、`Wall` 都是**验收节**.
>
> **判决: 可数段上回答是肯定的, 而且是定理. 奇异下标是另一堵墙, 没有被这个方法越过. 这个结果不带来记号无关的证书, 强度也没有超过现有基线.**
>
> **已编译的事实.**
>
> 1. **总判决 `Dᵐ` (`InaccModulusBase` §5).** 只读层号, 不搜索, 全程走一条路径. 在 `lim h` 目标上进 `h (1 + wk j)`, `wk` 是沿分支 1 走到 0 的步数.
> 2. **`GV-NF`: `Dᵐ` 在全部可数标准形下标上满足 `GV`.** 标准形是 Standard 的 `NF`, 下标可数 (`Ctbl`). 只以 `Funext` 为参数, 没有别的前提.
> 3. **`label-NF`: 每个可数标准形都带标签**, 同样只以 `Funext` 为参数. 实例: `ψ₀(Ω_ω)` (`label-BO`), `ψ₀(Ω_{ψ₀(Ω₁)})` (`label-ψε`), `ψ₀(Ω_{ψ₀(Ω_ω)})` (`label-ψBO`), 以及 `ψ₀(Ω_Ω)` 的整条 γ-链 (`label-γ`). 所以 `Commute` 的前提不只在自然数上可满足.
> 4. **范数可以从树读出 (`sz≤wk`, `Lift2`).** `sz t ≤ wk (L t)`. 核心是 `sz-step`: 对共尾度 ω 的任意项 (不要求标准形), `sz t ≤ 1 + sz (t[1])`. 分支 1 不丢信息, 分支 0 丢 (`ψ_u(b+1)[0] = 0`). `wk` 只是上界: `ψ₀(Ω₃)` 的 `sz` 是 5, `wk` 是 210 (Python 转写测得).
> 5. **项侧固定模 (`cofinB`, `NF`).** 标准形 `v < u`, `u` 共尾度 ω, 则 `v < u[n]`, 其中 `n ≤ 1 + sz v`. 上界不依赖 `u`. 这是 Standard 的 `cofin` 加一个计数, 证明在本仓库, 不依赖 Lean. 单调 `fs-monoᴺ` 是 GoodLBase 的 `fs-mono₁` 换成 `NF`.
> 6. **类的树侧陈述 (`Fam`, `Base` §6).** 判决的正确性只用五条: 对子树封闭; 无 `limᴼ`; `h n` 是 `h (n+1)` 的节点; 且 `f-mod`: 族内的节点落在 `h (1 + wk j)` 之下. 主定理取 `F` = `L` 在项类上的像.
> 7. **`Reg` 是纯树的充分条件 (`famReg`, `lin`, `mod`).** 每个 `lim h` 节点上 `h n` 在 `h (n+1)` 的 1-走步上, 模就是定理, 不必假设: 这是经典 Bachmann 性质的树侧形式. 证明不用任何记号. `tri`: 同一棵规整树的两个节点可比.
> 8. **编译的否定.** `pad-notReg` 与 `pad-wrong`: 单调的填充树不规整, `Dᵐ` 在它上面确实答错, 所以模只对规整类成立. `tight`: `μ = wk j` 不够, `1 + wk j` 是紧的 (`j = 3`, `i = ω`). `Reg-ω`, `Reg-ω⁺`: 两棵互不为节点的树都规整, 所以类必须是有向族, 单棵树的 `Reg` 不够. 这与 `Trich₂→WLPO` 不矛盾: `Reg` 与 "同属一族" 都不是判决能查的条件.
> 9. **奇异下标的否定 (`Wall`).** `nat-fails`: `Ω_ω < Ω_Ω`, 但 `Ω_ω` 大于每个 `Ω_Ω[n]`. **所以 `limᴼ` 目标上不存在自然数值的模**, 本文的 `wk` 不可能直接推广. 候选 `D⁺` (走步采样 + `toT` 读分支) 通过九个点, 但在 `D★` 错的两个点上照样错 (`⁺-wrong-OO`, `⁺-wrong-Ω₂`), 另有 `⁺-wrong-OO+1`. 换掉采样没有帮助; 最后一条说明 "先判相等" 的修补也不够.
>
> **第一个具体障碍.** 目标 `limᴼ k g` 上, 分支下标 `x` 属于 `Ordᴸ k`, 不是自然数. 模必须是**层号值的**: 要从 `j` 的树读出一棵 `Ordᴸ k` 的树 `x`, 并使 `g x` 仍在规整族里. `toT` 给出的 `x` 不在族里, 这就是 `⁺-wrong-OO` 的来源 (机制是观察, 不是定理).
>
> **只有采样, 没有证明.** `Reg (L t)` 对标准形是否成立. `Lift` 的 `Reg-Lt` 把它归结为 `bach`: `t[n]` 在 `t[n+1]` 的 1-走步上. Python 转写, 大小 ≤ 7 的 965 个可数标准形, 707 个极限项, `n = 0,1,2`: 命中 1875, 超出预算 246, 未命中 0. 主定理不用它. 若证出, `F` 就有不提项的刻画.
>
> **以下是判断, 不是定理.**
>
> - **强度.** 这些项都低于 `ψ₀(Ω_Ω)` (由 `Ctbl` 的值语义推断, 没有形式化), 现有路线 (Label, GoodL, Uniform3) 已经覆盖且走得更远. 新的只是方法: 没有地板, 没有 `Goodᴸ`, 判决是树上的总函数.
> - **证书.** 这里的判决正确性走记号 (`F` 是 `L` 的像), 没有产生记号无关的证书. 基线仍是带标签的 Uniform3 与记号无关的 UniformPending.
> - **建议.** `Lv` 再做**一个**定时的检验, 然后决定: 层号值的模能否让 `Ω_Ω` 对自身正确, 即找到读法 `x` 使 `g x` 留在规整族里. 做不到就关闭 `Lv` 路线的总判决方向. 可数段这一层已经不需要再做.
>
> **修正.** InaccStrike 文首第 7 点 "范数能否从树读出: 没有肯定的证据" 与 `Commute` 文首 "`OTFS_thm`, 本仓库没有" 现在都过时了: 前者见第 4 点, 后者对可数下标见 Standard 的 `NF-fsn`, `NF-pred`, `cofin`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccModulus where

open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Align.InaccStrikeBase using (Funext; dz)
open import OCF.Align.InaccStrikeCommute using (GV; module Tr)
open import OCF.Align.InaccTreeAccept using (LabN)
open import OCF.Align.InaccModulusBase using (Dᵐ)
open import OCF.Align.InaccModulusTerm
open import OCF.Align.InaccModulusRank
open import OCF.Align.InaccModulusNF
open import OCF.Align.Closure using (lt→<; <→lt)
open import OCF.Align.Standard using (NF; n[]; n∷; nψ; NF-pred; NF-fsn; Ctbl; c[]; c∷; Vis; vh; vd; vt; sz)
import OCF.Align.EBO as E
open E using (T; cof; cmpᵀ; lt; 𝟏; Ωt) renaming (ψ to ψᵗ)

Ctbl→Cnt : ∀ {t} → Ctbl t → Cnt t
Ctbl→Cnt c[]    = tt
Ctbl→Cnt (c∷ c) = Ctbl→Cnt c

prem : Prem NF
prem = record
  { B-nil = n[]
  ; B-pr  = λ b _ e → NF-pred b e
  ; B-fs  = λ b _ e n → NF-fsn b e n
  ; mono  = λ b _ e n → <→lt (fs-monoᴺ b e n)
  ; cofb  = λ {s} {t} bs _ bt _ e l → go bs bt e (lt→< s t l)
  }
  where
    go : ∀ {s t} → NF s → NF t → cof t ≡ E.cω → s E.<ᵀ t → Σ ℕ λ n → (n ≤ suc (sz s)) × (cmpᵀ s (E.fsn t n) ≡ lt)
    go bs bt e p with cofinB bt e bs p
    ... | n , n≤ , r = n , n≤ , <→lt r

module Main (fe : Funext) where
  open Strata fe prem

  NF→Hc : ∀ {t} → NF t → Hc t
  NF→Hc n[] = tt
  NF→Hc (n∷ (nψ nu cu na _) nx _) = (nu , Ctbl→Cnt cu , NF→Hc nu) , NF→Hc na , NF→Hc nx

  NF→Nω : ∀ {t} → NF t → Cnt t → Nω t
  NF→Nω {t} n c with collect t (Hc→Sub t (NF→Hc n))
  ... | d , s = suc d , n , c , s

  -- `GV` 在全部可数标准形下标上
  GV-NF : ∀ u v → NF u → Ctbl u → NF v → Ctbl v → GV (cmpᵀ u v) (Dᵐ (Tr.L Dᵐ u) (Tr.L Dᵐ v))
  GV-NF u v nu cu nv cv = agrω u v (NF→Nω nu (Ctbl→Cnt cu)) (NF→Nω nv (Ctbl→Cnt cv))

  -- 标签: 全部可数标准形
  label-NF : ∀ t → NF t → Ctbl t → LabN (dz (Tr.S Dᵐ t)) t
  label-NF t n c = label t (Ctbl→Cnt c) (NF→Hc n)
```
