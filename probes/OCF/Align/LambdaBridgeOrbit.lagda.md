# 回灌值下界的局部模拟：不要求全局单调

这是验收侧的一步定理。两边状态各自携带字面世界下界的证据；
关系只比较这样的状态，不比较裸坐标。只要求初始状态相关、
相关处的输出值有序、一次回灌保持相关，就能比较全部轨道及其部分和。
这将整条链的值义务化成一次操作，而不是每个阶段专属的支配论证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaBridgeOrbit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; _⊲_; hself; _⊞_; ⊞-fst)
open import OCF.Lean.WorldFoldIf using (State; orbit; feedback; partial)
open import OCF.Lean.WorldFoldRun using (run)
open import OCF.Lean.WorldFoldClosed using (T; U; embed)
open import OCF.Lean.NegFab6Sim using (_≼_; z≼; s≼s; l≼; ≼l; ≼-refl; ⊞-mono)

module _ (B : Cd) (h : (e : Cd) → B ⊲ e → Cd) where
  output : State B → Cd
  output s = h (proj₁ s) (proj₂ s)

  advance : State B → State B
  advance s = (B ⊞ hs (output s)) , ⊞-fst B (hs (output s))

-- 接口定稿后只增不改；只对有界状态陈述律。
record OrbitSim (B C : Cd)
  (h : (e : Cd) → B ⊲ e → Cd) (k : (e : Cd) → C ⊲ e → Cd) : Set₁ where
  field
    Related : State B → State C → Set
    initial : Related (B , hself) (C , hself)
    out-le  : ∀ {s t} → Related s t → output B h s ≼ output C k t
    next    : ∀ {s t} → Related s t → Related (advance B h s) (advance C k t)
open OrbitSim

partial-mono : ∀ {f g} → (∀ n → f n ≼ g n) → ∀ n → partial f n ≼ partial g n
partial-mono p zero = p zero
partial-mono p (suc n) = ⊞-mono (partial-mono p n) (p (suc n))

module Sound {B C h k} (s : OrbitSim B C h k) where
  related : ∀ n → Related s (orbit B h n) (orbit C k n)
  related zero = initial s
  related (suc n) = next s (related n)

  branch-le : ∀ n → output B h (orbit B h n) ≼ output C k (orbit C k n)
  branch-le n = out-le s (related n)

  feedback-le : feedback B h ≼ feedback C k
  feedback-le = l≼ (λ n → ≼l n (partial-mono branch-le n))

-- 同一分支函数上有实例，不要求证明路径相等无关或 Funext。
identity : ∀ B h → OrbitSim B B h h
identity B h = record
  { Related = _≡_
  ; initial = refl
  ; out-le = λ { {s} refl → ≼-refl (output B h s) }
  ; next = λ { refl → refl } }

-- 一个不同分支的实例：实际常值节点 T 不超过读取整个坐标的 U。
-- 不利用 U 的完整值结论，因此不循环依赖 LambdaBridgeFinite。
constant-coordinate : OrbitSim hz hz (λ e p → hs hz)
  (λ e p → hs (run (embed {hs e} e)))
constant-coordinate = record
  { Related = λ s t → ⊤
  ; initial = tt
  ; out-le = λ r → s≼s z≼
  ; next = λ r → tt }

T≤U : T ≼ U
T≤U = Sound.feedback-le constant-coordinate
```

## 它接到 EBO 时缺什么

`EmbVVMain.Y-val` 已有对任意高度结构 `HtB` 的模拟闭包，但比较的是
同一 LadderOrd 折叠与去头的变体。`EmbVVTop.vv-row` 再用 `PxB.P-row`
给每个高度的记号前缀规则；`EmbVVInstO2` 实例化到固定码，并未给任意
Ω-塔站的 `PxB`。这不是 `LHRec` 或 `Third` 的折叠模拟。

`ThirdFold` 的链在回灌处使用 `b ⊞ previous`，保留节点的坐标又经
`San.san`。把它与参照折叠比较的最小局部缺口是：关系同时覆盖回灌状态
和被洗坐标，且相关状态的分支输出有值下界。仅有 `Gd` 路径合法性，
或 `ThirdVal.rk-⊲` 的高度序保序，均不是 `out-le`。对于 `LHRec`，
连接受所有层号的折叠还没定义，尚无右边输出可填。

本接口刻意不假定所有输入上折叠单调；`WorldObstructionValue` 已显示
稳定分支也不能自动给这样的单调性。下一步是给实际高层闭项构造
状态关系并证明上述局部义务，而不是为所有坐标强求无界比较。
上述定位是代码审阅判断；本文件的编译定理只有局部模拟推出回灌值序
以及两个明确实例。没有声称已接上 EBO 参照。

翻译账：无新树或折叠构造子；记录字段来自回灌循环的一步证明义务。
没有读取记号基本列；此处只是值验收，不改变前 3 层定义。
