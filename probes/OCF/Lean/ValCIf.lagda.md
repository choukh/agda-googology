# ValC: 接口 (值关系在 CRw 的层号与折叠上应满足的律)

> 不含记号. 构造一路 ValC, 否定一路 NegValC 共用. 入口 [ValC](ValC.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [CRwIf](CRwIf.lagda.md), [CRwFold](CRwFold.lagda.md), 与第 0 层的标准前序 [TLRuleSpec](../Align/TLRuleSpec.lagda.md) (`CumReadCF.A` 上, 只作锚).
>
> **接口定稿 2026-11-06 01:41 (首次编译通过).** 定稿后只增不改.
>
> **这一篇做什么.** 第 4 层 (值的验收), 不改 CRw 的树、折叠、合法性. 对象是 CRw 的同底折叠 `Φ b⊥ m … b⊥ t (sm pt) b x tt` (可数层号 $m$ 折到可数层号 $t$, 界 $b$; 即 TySup 的 sup 层, 累加). 接口把值关系 `Le t` (第 $t$ 层上的前序) 与 "值合法" `Mo t` 作为**字段**, 律是它们与折叠之间的关系. 关系本身不在接口里固定 (构造一路给一个实例, 否定一路可对一切满足律的关系说话).
>
> **锚 (防止关系退化).** `sound₀`: 第 0 层 (`Cd`, 只有 $0$, 后继, ℕ-极限) 上 `Le hz` 推出 `TLRuleSpec._≤_` (此前值验收用的标准前序). `Mo-top`, `Mo-hz`: 地板与 $0$ 值合法 (否则 `Mo = ⊥` 让一切律空真).
>
> **律, 带字面公共上界.** 律里出现的每一对层号都带字面 $\lhd$ 证据:
>
> - `Φ-mono` (目标 $t$, 公共上界 $m$: `pt : t ⊲ m`): 输入 $x\le y$ (第 $m$ 层), 界 $b\le b'$ (第 $t$ 层), 界在地板之上 (`Le t (top t) b`), 则 $\Phi_{m\to t,b}\,x\le\Phi_{m\to t,b'}\,y$.
> - `route` (路线引理; 层号 $j$ 与目标 $t$, 公共上界 $m$: `pj : hs j ⊲ m`, `pt : t ⊲ j`, 于是 $t\lhd m$ 是字面 `⊲ᴮ-tr pt (⊏⊑ pj)`): 直接折到 $t$ 不高于先以地板 `top j` 为界折到 $j$ 再折到 $t$: $\Phi_{m\to t,b}\,x\le\Phi_{j\to t,b'}(\Phi_{m\to j,\mathrm{top}\,j}\,y)$. 这是 `Φ` 的 "在上" 子句 (`above i …`) 在一般输入上的形式: 在上的结点正是这样折的.
> - `Mo-Φ`: 折叠保值合法.
> - `one≤Φ`: 折叠的输出不低于 $1$.
>
> 可达性证明取规范的 `wf b⊥`. 下一个记录 (跨底折叠 `cx`, 闭项 `TX`, `TU`) 以后在本篇末尾追加, 不改这一个.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.ValCIf (I : CRwIf) where

open import Data.Unit using (⊤; tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwFold I
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
import OCF.Align.TLRuleSpec as TL
```

## §1 第 0 层读成 `A`

```agda
toA : Cd → A
toA hz = azero
toA (hs h) = asuc (toA h)
toA (hl f) = alim (λ n → toA (f n))
toA (hΩ () _)
```

## §2 同底折叠 (可数层号) 的值律

记号: `L t = HB (Lev b⊥ t)`, `F m t pt b x` 是第 $m$ 层折到第 $t$ 层 (`sm pt`), 界 $b$.

```agda
L : Cd → Set
L t = HB (Lev b⊥ t)

F : ∀ m → LgB m → ∀ t → t ⊲ m → L t → L m → L t
F m lm t pt b x = Φ b⊥ m (wf b⊥ m) lm b⊥ t (sm pt) b x tt

record ValC⊥ : Set₁ where
  field
    Le       : ∀ t → L t → L t → Set
    Mo       : ∀ t → L t → Set
    le-refl  : ∀ t x → Le t x x
    le-trans : ∀ t {x y z} → Le t x y → Le t y z → Le t x z
    sound₀   : ∀ {x y} → Le hz x y → toA x TL.≤ toA y
    Mo-hz    : ∀ t → Mo t hz
    Mo-top   : ∀ t → LgB t → Mo t (top b⊥ t)
    one≤Φ    : ∀ m lm t pt b x → Le t (hs hz) (F m lm t pt b x)
    Mo-Φ     : ∀ m lm t pt {b} → Mo t b → Le t (top b⊥ t) b → ∀ x → Mo m x → Mo t (F m lm t pt b x)
    Φ-mono   : ∀ m lm t pt {b b′ x y} →
               Mo t b → Mo t b′ → Le t (top b⊥ t) b → Le t b b′ →
               Mo m x → Mo m y → Le m x y →
               Le t (F m lm t pt b x) (F m lm t pt b′ y)
    route    : ∀ m lm j (pj : hs j ⊲ m) t (pt : t ⊲ j) {b b′ x y} →
               Mo t b → Mo t b′ → Le t (top b⊥ t) b → Le t b b′ →
               Mo m x → Mo m y → Le m x y →
               Le t (F m lm t (⊲ᴮ-tr pt (⊏⊑ pj)) b x)
                    (F j (lg↓ pj lm) t pt b′ (F m lm j (⊏⊑ pj) (top b⊥ j) y))
```

## §3 (追加 2026-11-06) 路线引理只对真第一位置

> **追加, 不改 §2.** 否定一路 `NegValCRoute.route-hself` (定理) 证明: 按 §2 的 `ValC⊥` (`route` 对一切 `pt : t ⊲ j`, 含 `hself` 即 $t=j$), 第 0 层含 `z≤` 的关系没有实例 (直接折用界 $b$, 两步折用地板 $\mathrm{top}\,j$). 折叠的 "在上" 子句只在 $t$ 是 $j$ 的**真**第一位置时发生 (`pick` 的 `inj₁ (hsuc q)`, $q$ 以后继或 ℕ-极限开头). 这里追加一个记录 `ValC⊥ᵖ`: 其余字段同 `ValC⊥`, `route` 多一个前提 `Pp t j` (真第一位置, 定义在 [ValCRel](ValCRel.lagda.md)), 外层证据 `qo` 任意.

```agda
open import OCF.Lean.ValCRel I using (Pp)

record ValC⊥ᵖ : Set₁ where
  field
    Le       : ∀ t → L t → L t → Set
    Mo       : ∀ t → L t → Set
    le-refl  : ∀ t x → Le t x x
    le-trans : ∀ t {x y z} → Le t x y → Le t y z → Le t x z
    sound₀   : ∀ {x y} → Le hz x y → toA x TL.≤ toA y
    Mo-hz    : ∀ t → Mo t hz
    Mo-top   : ∀ t → LgB t → Mo t (top b⊥ t)
    one≤Φ    : ∀ m lm t pt b x → Le t (hs hz) (F m lm t pt b x)
    Mo-Φ     : ∀ m lm t pt {b} → Mo t b → Le t (top b⊥ t) b → ∀ x → Mo m x → Mo t (F m lm t pt b x)
    Φ-mono   : ∀ m lm t pt {b b′ x y} →
               Mo t b → Mo t b′ → Le t (top b⊥ t) b → Le t b b′ →
               Mo m x → Mo m y → Le m x y →
               Le t (F m lm t pt b x) (F m lm t pt b′ y)
    route    : ∀ m lm j (pj : hs j ⊲ m) t (qo : t ⊲ j) → Pp t j → ∀ {b b′ x y} →
               Mo t b → Mo t b′ → Le t (top b⊥ t) b → Le t b b′ →
               Mo m x → Mo m y → Le m x y →
               Le t (F m lm t (⊲ᴮ-tr qo (⊏⊑ pj)) b x)
                    (F j (lg↓ pj lm) t qo b′ (F m lm j (⊏⊑ pj) (top b⊥ j) y))
```
