# K3 封顶 (一): `HtFeedClosed.TΛ` 的高度类型里没有 Ω₂ 型的顶

> **第 4 层 (验收侧) 的判定文件.** 不改任何候选的定义, 不进成品与证书. 本篇不导入记号模块 (用不到).
>
> **判决: (乙) 封顶的编译事实, 只否定写明的形状.** 候选是一族闭项 `TΛ : (Λ : H) → LgH Λ → A`, 层号的类型是高度树 `H` (`hz`, `hs`, `hl`, 以及分支取 `A` 的 `hΩ`). 两条定理:
>
> 1. `no-Ω₂-top`: **`H` 里没有 Ω₂ 型的顶.** 记录 `Top I` 说: 有一份以 `I` 为指标的保序的合法高度族 `F : I → H`, 与一个合法高度 `top`, 每个合法指标的像都在某个世界里严格位于 `top` 之下 (世界可以逐个各取). `Top H` (指标取 `H` 自己, 序取 `H` 的严格第一位置) 没有实例.
> 2. `no-retract-H`: `hΩ` 的分支族取不遍 `H`: 不存在 `e : H → A`, `d : A → H` 使 `d (e x) ≡ x` 对一切 `x`.
>
> 对照: **同一个记录在低一级有实例.** `Ω₁-instance : Top A`: 拷贝是 `emb : A → H`, 顶是 `Ωᴴ = hΩ emb`, 每个 `emb x` 在世界 `x` 里严格位于 `Ωᴴ` 之下 (候选已有的 `top-Ω`). 所以否定针对的是 "以 `H` 自己为指标" 这一级.
>
> **它说了什么, 没说什么.**
>
> - 编译事实: 上面两条, 前提里没有假设之外的东西; `Ω₁-instance` 说明被否定的记录在低一级有实例.
> - 读法 (判断): `H` 的高度读作 Ω₂ 之下的层号. 需要层号 Ω₂ 本身的站 (例如以 Ω₂ 为最高层的 `TΛ`, 读法 ψ₀(Ω_{Ω₂+1}) 一带; 或把 Ω_{Ω₂} 当作折叠的源对象的站) 在这一族里没有对应的 `Λ : H`. ψ₀(Ω_{Ω₂}) 本身作为 `TΛ` 在一列高度上的外部 ℕ-对角, 不被这两条定理排除; 那一列高度要由第 1 层的折叠输出读回成 `H`, 候选入口记为未走通 (`HtFeedNeg.no-weak` 只否定其中一种读法).
> - **不是值上界.** 本篇没有证明任何 `TΛ Λ lΛ` 的序数值不超过某个具名序数. 候选没有任何值定理 (入口: 第 4 层没有做).
>
> **第一个 Ω-共尾派发的站在哪 (读代码, 判断).** 折叠里一切层都是最高层 `Λ` 的第一位置, 结点层与目标层的比较是 `HtFeedFold.rkT`, 即一次 `cmpH`. `Λ` 含 `hΩ` 时, 比较会走到 `cmpH` 的 `hLim` 一行: 先在公共世界里比较两个分支坐标 (`cmpF`), 再用 `LgH` 的单调搬到同一支; 这在 `Λ = Ωᴴ` (闭项 `T-Ω`) 就发生. 层号本身是 Ω-共尾的 (层 `Ωᴴ` 作为目标或结点层出现) 的第一站是最高层 `hs Ωᴴ` (闭项 `T-Ω+1`, 读法 ψ₀(Ω_{Ω+1})). 两处都在候选的类型之内. 所以这个候选的类型封顶不在第一个 Ω-共尾派发的站, 而在高一个数类的层号 Ω₂. 条件覆盖定理 (甲) 在这个候选上没有实填: 极限一步律要比较不同 `Λ` 的折叠实例 (入口 "第一个障碍" 第 1 条: 跨高度的比较没有做), 本篇没有去填.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K3CapHtFeed where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import OCF.Align.CumReadCF using (A; asuc; Lg; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
  using (H; hs; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; ⊲ᴴ-tr; LgH; StH; ss; sl; sL; AccY; acc; accL)
open import OCF.Align.HtFeedHt using (emb; emb⊲; Lg-emb; Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtFeedClosed using (TΛ)
```

## §1 形状: 一份保序的拷贝加一个顶

`StH W a b` 是候选自己的 "层 a 在世界 W 里严格位于层 b 之下" (折叠的结点种类). `Below a b`: 在某个世界里如此. 记录对指标类型 `I` (带自己的合法性与严格序) 参数化, 这样低一级的实例与高一级的否定说的是同一个记录.

```agda
Below : H → H → Set
Below a b = Σ A (λ W → StH W a b)

record Top (I : Set) (LgI : I → Set) (_<I_ : I → I → Set) : Set where
  field
    F     : I → H                                   -- I 的一份拷贝
    top   : H                                       -- 它的顶
    F-lg  : ∀ i → LgI i → LgH (F i)
    mono  : ∀ {a b} → LgI a → LgI b → a <I b → Below (F a) (F b)
    ltop  : LgH top
    below : ∀ i → LgI i → Below (F i) top

-- 指标取 H 自己: Ω₂ 型的顶
Top₂ : Set
Top₂ = Top H LgH Below
```

## §2 定理

`F` 保序时, `F x` 不会严格位于 `x` 之下: 否则 `x, F x, F (F x), …` 沿结点种类无穷下降, 而层良基 (`accL`, 候选自己的定理). 取 `x = top`.

```agda
module _ (F : H → H) (F-lg : ∀ h → LgH h → LgH (F h))
         (mono : ∀ {a b} → LgH a → LgH b → Below a b → Below (F a) (F b)) where
  no-desc : ∀ x → AccY x → LgH x → Below (F x) x → ⊥
  no-desc x (acc f) lx (W , s) =
    no-desc (F x) (f s) (F-lg x lx) (mono (F-lg x lx) lx (W , s))

no-Ω₂-top : Top₂ → ⊥
no-Ω₂-top T = no-desc F F-lg mono top (accL top) ltop (below top ltop)
  where open Top T
```

第二条: 分支族 `d : A → H` 的每一支都严格位于 `hΩ d` 之下 (世界取坐标自己), 所以 `hΩ d` 不是任何一支.

```agda
irr : ∀ x → AccY x → Below x x → ⊥
irr x (acc f) (W , s) = irr x (f s) (W , s)

branch-below : ∀ (d : A → H) c → Below (d c) (hΩ d)
branch-below d c = c , sL {c = c} C.self hself

no-self-H : ∀ (d : A → H) c → d c ≡ hΩ d → ⊥
no-self-H d c eq = irr (hΩ d) (accL (hΩ d)) (subst (λ z → Below z (hΩ d)) eq (branch-below d c))

no-retract-H : (e : H → A) (d : A → H) → (∀ x → d (e x) ≡ x) → ⊥
no-retract-H e d sec = no-self-H d (e (hΩ d)) (sec (hΩ d))
```

## §3 低一级的实例: `Ωᴴ` 是 `A` 的拷贝的顶

同一个记录, 指标从 `H` 换成 `A` (序取 "后继是第一位置"): 拷贝 `emb`, 顶 `Ωᴴ`. 字段都由候选已有的定义与定理填上.

```agda
st-of : ∀ {W k L} → hs k ⊲[ W ] L → StH W k L
st-of hself = ss hself
st-of (hsuc p) = ss (⊲ᴴ-tr (hsuc hself) p)
st-of (hlim n p) = sl n (⊲ᴴ-tr (hsuc hself) p)
st-of (hLim e p) = sL e (⊲ᴴ-tr (hsuc hself) p)

Ω₁-instance : Top A Lg (λ a b → asuc a ⊲ b)
Ω₁-instance = record
  { F = emb
  ; top = Ωᴴ
  ; F-lg = Lg-emb
  ; mono = λ _ _ p → C.azero , st-of (emb⊲ p)
  ; ltop = Lg-Ωᴴ
  ; below = λ x _ → branch-below emb x
  }
```

## §4 与候选的接线 (只取类型)

候选的每一个闭项都是 `TΛ` 在某个 `Λ : H` 上的值; 层号只经这个参数进入.

```agda
station : (Λ : H) → LgH Λ → A
station = TΛ
```

## §5 结论 (按档)

- **[定理]** `no-Ω₂-top`: 记录 `Top H LgH Below` (拷贝 `F : H → H` 保合法, 在合法高度上保 `Below`; 顶 `top` 合法; 每个合法 `h` 有 `Below (F h) top`) 无实例. `no-self-H`, `no-retract-H`: `hΩ` 的分支族取不遍 `H`. `Ω₁-instance`: 同一个记录以 `A` 为指标时有实例.
- **[判断]** `H` 读作 Ω₂ 之下的层号; 装不下的是需要层号 Ω₂ 本身的站; 第一个 Ω-共尾派发的站 (最高层 `hs Ωᴴ`) 在类型之内.
- **没有的.** 值上界; 条件覆盖定理的实填; 候选在类型之内各站的任何值结论.
