# K3 封顶 (二): `RadicalValueNativeFinal.closed` 的源族没有 Ω-共尾的高度

> **第 4 层 (验收侧) 的判定文件.** 不改任何候选的定义, 不进成品与证书. 本篇不导入记号模块 (用不到); 导入的是候选自己的源族 `TotalOrbitSource.Rows` 与高度结构 `LadderOrdBase.HtB`.
>
> **判决: (乙) 封顶的编译事实, 只否定写明的形状.** 候选 `RadicalValueNativeFinal.closed` 的输入是 `Producer.High.raw end zero`, 其中 `High = Rows (HB ω²ᶜ)`; 源族 `Rows` 对任一高度结构 `S : HtB` 给出 `raw : Ht → Ordᴵ → Z`, 层号是一对 (高度 `m : Ht`, 可数下标 `a : Ordᴵ`). 定理 `no-Ω-height`: **任何 `HtB` 的高度段里, 没有一个高度在可数树 `Ordᴵ` 的一份严格保序拷贝之上.** 也就是说高度段里没有 Ω-共尾的高度. 依据只是 `HtB` 自己的两个字段: 秩 `rk : Ht → Ordᴵ` 与 `rk<` (把 `<ᴸ` 送到字面路径).
>
> **它说了什么, 没说什么.**
>
> - 编译事实: 上面这条, 对一切 `S : HtB`, 无额外前提; `HtB` 有实例 (候选用的 `HB ω²ᶜ`). 被否定的形状写成记录 `Copy I` (以 `I` 为指标的严格保路径的族, 加一个公共上界): `Copy Ordᴵ` 无实例 (`no-copy`), 同一个记录在指标取 `ℕ` 时有实例 (`nat-copy`). 所以否定针对的是 "以 `Ordᴵ` 为指标" 这一级.
> - 读法 (判断): 按源族的约定层号 (m, a) 读 Ω·m+a, 所以装不下的第一站是层号 Ω·Ω=Ω² 的那一站, 即 ψ₀(Ω_{Ω²}) (它要一个高度, 一切 Ω·m 的高度 m 遍历一份 Ω-共尾的族之后仍在它下面). 具体闭项 `closed` 还把 `S` 固定在码 `ω²ᶜ` 上 (读法: 层号在 Ω·ω² 之内).
> - **不是值上界.** 本篇没有证明 `closed` 的序数值不超过任何具名序数; 已有的值定理只有下界 ψ₀(Ω_Ω)+ω (`TotalValue`). 本篇也不说换一个不满足 `HtB` 的高度结构之后的源族怎样.
>
> **第一个 Ω-共尾派发的站在哪 (读代码, 判断).** 源族的层号是字典序的一对, 第一个 Ω-共尾的层号是 "高度从 `h₀` 升一级" (读法 Ω). 那一处的派发不在树上做: 高度之间用 `HtB.tri` (段内的三歧, 是结构的字段), 可数下标之间用字面路径. 所以这一站在候选的类型之内; 值在这一站以上没有定理 (新语义 `run` 的值证明只到 ψ₀(Ω_Ω)+ω). 条件覆盖定理 (甲) 的两条一步律在这个候选上没有实填, 本篇没有去填.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K3CapRadical where

open import Data.Nat using (ℕ; zero; suc; _<′_; ≤′-step)
open import Data.Nat.Base using (≤′-refl)
open import Data.Empty using (⊥)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _⊑ᴵ_; Sim→⊑ᴵ)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.LadderInfBase using (Tri)
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdPos using (HB)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
import OCF.Align.TotalOrbitSource as Producer
```

## §1 可数树上: 严格保路径的自映射没有上界

`_<ᴵ_` 是字面路径 (走到一个真子位置). `G` 严格保路径时, `G x` 不会落在 `x` 的真子位置上 (否则 `x, G x, G (G x), …` 是一条无穷下降的路径; 这里对上界的结构递归). 于是 `G` 的像不可能都在同一棵树 `t` 之下: 取 `x = t`.

```agda
module _ (G : Ordᴵ → Ordᴵ) (mono : ∀ {a b} → a <ᴵ b → G a <ᴵ G b) where
  no-desc : ∀ t {x} → x <ᴵ t → G x <ᴵ x → ⊥
  no-desc (suc b) zero p = no-desc b p (mono p)
  no-desc (suc b) (suc r) p = no-desc b r p
  no-desc (lim f s) (lim j r) p = no-desc (f j) r p

  no-bounded-copy : ∀ t → (∀ a → G a <ᴵ t) → ⊥
  no-bounded-copy t bd = no-desc (suc t) zero (bd t)
```

## §2 高度结构 `HtB`: 没有 Ω-共尾的高度

被否定的形状: 一份以 `Ordᴵ` 为指标, 严格保序的高度族 `F`, 加一个在它全体之上的高度 `top`. 证明只用秩.

```agda
module _ (S : HtB) where
  open HtB S

  no-Ω-height : (F : Ordᴵ → Ht) (top : Ht) →
    (∀ {a b} → a <ᴵ b → F a <ᴸ F b) → (∀ a → F a <ᴸ top) → ⊥
  no-Ω-height F top mono bd =
    no-bounded-copy (λ a → rk (F a)) (λ p → rk< (mono p)) (rk top) (λ a → rk< (bd a))

  -- 高度之间的派发是段内三歧 (结构的字段), 不是树上的比较
  height-dispatch : ∀ a b → Tri _<ᴸ_ a b
  height-dispatch = tri
```

**同一形状写成记录, 在低一级可满足.** `Copy I`: 以 `I` 为指标, 严格保路径的一族可数树, 加一个公共上界. 指标取 `Ordᴵ` 时无实例 (就是 `no-bounded-copy`); 指标取 `ℕ` 时有实例: 自然数的拷贝都在 ω 之下.

```agda
record Copy (I : Set) (_<I_ : I → I → Set) : Set where
  field
    G     : I → Ordᴵ
    mono  : ∀ {a b} → a <I b → G a <ᴵ G b
    bound : Ordᴵ
    below : ∀ a → G a <ᴵ bound

no-copy : Copy Ordᴵ _<ᴵ_ → ⊥
no-copy C = no-bounded-copy G mono bound below
  where open Copy C

natᴵ : ℕ → Ordᴵ
natᴵ zero = zero
natᴵ (suc n) = suc (natᴵ n)

nat-step : ∀ n → natᴵ n ⊑ᴵ natᴵ (suc n)
nat-step n = Sim→⊑ᴵ (λ q → suc q)

nat< : ∀ {n m} → n <′ m → natᴵ n <ᴵ natᴵ m
nat< ≤′-refl = zero
nat< (≤′-step p) = suc (nat< p)

nat-copy : Copy ℕ _<′_
nat-copy = record
  { G = natᴵ
  ; mono = nat<
  ; bound = lim natᴵ nat-step
  ; below = λ n → lim (suc n) zero
  }
```

## §3 与候选的接线 (只取类型, 不展开闭项)

源族对任一 `S : HtB` 给出: 层号是一对 (高度, 可数下标). 候选闭项固定用 `High = Rows (HB ω²ᶜ)`. 这里只写出类型, 不比较任何闭项 (闭项沿证书计值, 比较会展开它).

```agda
source-family : (S : HtB) → HtB.Ht S → Ordᴵ → Z
source-family S = Producer.Rows.raw S

-- §2 的定理用在候选实际使用的高度结构上
Sᴴ : HtB
Sᴴ = HB ω²ᶜ

high-source : HtB.Ht Sᴴ → Ordᴵ → Z
high-source = Producer.High.raw

no-Ω-height-High : (F : Ordᴵ → HtB.Ht Sᴴ) (top : HtB.Ht Sᴴ) →
  (∀ {a b} → a <ᴵ b → HtB._<ᴸ_ Sᴴ (F a) (F b)) →
  (∀ a → HtB._<ᴸ_ Sᴴ (F a) top) → ⊥
no-Ω-height-High = no-Ω-height Sᴴ
```

## §4 结论 (按档)

- **[定理]** `no-bounded-copy`, `no-copy`: `Ordᴵ` 上严格保字面路径的自映射, 像没有公共上界 (记录 `Copy Ordᴵ` 无实例). `no-Ω-height`: 任一 `S : HtB` 里, 没有高度在 `Ordᴵ` 的一份严格保序拷贝之上. `no-Ω-height-High`: 上式在候选实际使用的 `HB ω²ᶜ` 上. `nat-copy`: 同一个记录在指标 `ℕ` 上有实例.
- **[判断]** 层号 (m, a) 读 Ω·m+a; 装不下的第一站是层号 Ω² (ψ₀(Ω_{Ω²})); 第一个 Ω-共尾派发的站 (层号 Ω) 在类型之内, 派发用段内三歧.
- **没有的.** 值上界; 条件覆盖定理的实填; 关于不满足 `HtB` 的其它高度结构的任何结论.
