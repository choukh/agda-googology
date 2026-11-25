# RR5：无关证据骨架上的读回、Ω 与核对

**对纲领与目标意味着什么。** [YiIntr](YiIntr.lagda.md) 报告 "证据进树后成了树的数据,
`tw₃` 不满足原 `irr`", 并据此不采用。本篇在 [RR5IrrCore](RR5IrrCore.lagda.md) 上编译说明:
那处失败属于 "证据作普通参数" 这一种写法。把证据标成无关参数之后, 换证明不换树、
分支不依赖守卫证明, 都是 `refl`; 只读树的算子可以调用起点分支; Ω 是全函数, 塔与 Λ 直接写出;
守卫域为空的结点在这个类型里不存在。所以 "证据进树" 这个方向没有被 YiIntr 否定。

**本篇没有的。** 新块上的 `Legal` 闭包; 位置证据 (`Reg` 仍在树外); 任何折叠 ψ;
任何序数值; 与旧块的对应。无关证据只能在无关位置使用, 折叠是否处处只需要这样用,
要到写折叠时才知道 (判断, 见文末)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RR5IrrCheck where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
```

## 1 读回与 Ω: 四行原样, 全函数

与 `LevelFixVal` 的 `up`, `upT`, `cO` 逐行平行。多出来的只是把坐标的嵌套证据
传给新结点的无关字段; 读回本身不看守卫, 与原块一样。

```agda
cO : (k : LF) → Raw k
cO zero = G.suc G.zero
cO (suc k) = G.top
cO (lim f) = G.top
cO (lc k c w b t g) = G.top

cO-Lgl : ∀ k → Lgl k (cO k)
cO-Lgl zero = tt
cO-Lgl (suc k) = tt
cO-Lgl (lim f) = tt
cO-Lgl (lc k c w b t g) = tt

cO-Nested : ∀ k → Nested k (cO k)
cO-Nested zero = tt
cO-Nested (suc k) = tt
cO-Nested (lim f) = tt
cO-Nested (lc k c w b t g) = tt

upN : (y : LF) (r : Pre y) (c : Low y r) →
  .(LglLow y r c) → .(NestedLow y r c) → (t : LF) →
  ((η : Low y r) → .(GdL y r c η) → LF) → LF
upN zero ()
upN (suc k) (inj₁ _) c l b t g = lc k c l b t g
upN (suc k) (inj₂ r) c l b t g = upN k r c l b t g
upN (lim f) (n , r) c l b t g = upN (f n) r c l b t g
upN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₁ _)) c l b t g = lc k c l b t g
upN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₂ r)) c l b t g = upN k r c l b t g
upN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₁ r)) c l b t g = upN t₀ r c l b t g
upN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c l b t g =
  upN (g₀ η e) r c l b t g

up : (y : LF) (a : Raw y) → .(Nested y a) → LF
upT : LF → LF
upK : (y : LF) (i : Kid y) (T : KidR y i) → .(NestedKid y i T) → LF

up y G.zero nb = zero
up y (G.suc a) nb = suc (up y a nb)
up y (G.lim f) nb = lim (λ n → up y (f n) (nb n))
up y (G.lc r c t g) nb =
  upN y r c (proj₁ nb) (proj₁ (proj₂ nb))
    (up y t (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → up y (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))
up y (G.em i T) nb = upK y i T nb
up y G.top nb = upT y

upK (suc k) _ T nb = up k T nb
upK (lim f) n T nb = up (f n) T nb
upK (lc k c w b t g) (inj₁ _) T nb = up k T nb
upK (lc k c w b t g) (inj₂ (inj₁ _)) T nb = up t T nb
upK (lc k c w b t g) (inj₂ (inj₂ (η , e))) T nb = up (g η e) T nb

upT zero = suc zero
upT (suc k) = lc k (cO k) (cO-Lgl k) (cO-Nested k) (upT k)
  (λ η e → up k η (proj₂ (proj₂ e)))
upT (lim f) = lim (λ n → upT (f n))
upT (lc k c w b t g) = lc k c w b (upT t) (λ η e → upT (g η e))

Ω̂ : LF → LF
Ω̂ = upT

tw : ℕ → LF
tw zero = zero
tw (suc n) = Ω̂ (tw n)

Λ : LF
Λ = lim tw
```

`Ω̂ : LF → LF` 没有前提。YiIntr 的 `Ω̂` 要 `Ready` 环境, 并且不能对全部树给出
(`YiIntrCheck.no-total-ready`); 那里的环境只用来生产内置的位置路径, 本篇不内置它。

## 2 证据不是数据

```agda
-- 换掉结点里的两份证明, 树不变.
evidence-irrelevant : ∀ k c (w w′ : Lgl k c) (b b′ : Nested k c) t
  (g : (η : Raw k) → .(Gd k c η) → LF) →
  lc k c w b t g ≡ lc k c w′ b′ t g
evidence-irrelevant k c w w′ b b′ t g = refl

-- 原 Legal 的 irr 字段在新类型上的同形陈述, 对一切树成立.
RootIrr : LF → Set
RootIrr zero = ⊤
RootIrr (suc x) = ⊤
RootIrr (lim f) = ⊤
RootIrr (lc k c w b t g) = ∀ η (e e′ : Gd k c η) → g η e ≡ g η e′

all-root-irr : ∀ x → RootIrr x
all-root-irr zero = tt
all-root-irr (suc x) = tt
all-root-irr (lim f) = tt
all-root-irr (lc k c w b t g) = λ η e e′ → refl

-- Raw 一侧同理.
raw-irr : ∀ {P L Gl K B} r (c : L r)
  (g : (η : L r) → .(Gl r c η) → G.R P L Gl K B) η (e e′ : Gl r c η) →
  g η e ≡ g η e′
raw-irr r c g η e e′ = refl
```

YiIntr 的反例坐标照搬过来: `suc (lim (const 1))` 有两份真实的守卫, 分别在极限里选第 0, 1 项。
那里两份守卫给出不同的树 (`actual-differ`); 这里是同一棵树。

```agda
raw1 : Raw zero
raw1 = G.suc G.zero

raw0-Nested : ∀ a → Nested zero a
raw0-Nested G.zero = tt
raw0-Nested (G.suc a) = raw0-Nested a
raw0-Nested (G.lim f) = λ n → raw0-Nested (f n)
raw0-Nested (G.lc () c t g)
raw0-Nested (G.em () a)
raw0-Nested G.top = tt

coord : Raw zero
coord = G.suc (G.lim (λ _ → raw1))

coord-lawful : Lgl zero coord
coord-lawful = (λ _ → inj₁ refl) , (λ _ → tt)

coord-guard : ℕ → Gd zero raw1 coord
coord-guard n = inj₂ (inj₂ (n , inj₁ refl)) , coord-lawful , raw0-Nested coord

tw₃-form : tw 3 ≡
  lc zero raw1 tt tt (tw 2) (λ η e → Ω̂ (up zero η (proj₂ (proj₂ e))))
tw₃-form = refl

actual : ℕ → LF
actual n = Ω̂ (up zero coord (proj₂ (proj₂ (coord-guard n))))

actual-same : actual 0 ≡ actual 1
actual-same = refl

tw₃-root-irr : RootIrr (tw 3)
tw₃-root-irr = all-root-irr (tw 3)
```

## 3 只读树的算子能调用分支

起点的守卫由结点自己存的无关证据给出, 不需要树外的证书, 对一切层号成立。
下界加一的那一支同样只读树: `Cp k c (suc c)` 是一步, 合法性与嵌套证据就是下界自己的。

```agda
start-node : LF → LF
start-node zero = zero
start-node (suc x) = suc x
start-node (lim f) = lim f
start-node (lc k c w b t g) = g c (inj₁ refl , w , b)

next-node : LF → LF
next-node zero = zero
next-node (suc x) = suc x
next-node (lim f) = lim f
next-node (lc k c w b t g) = g (G.suc c) (inj₂ (inj₁ refl) , w , b)

tw₂-start : start-node (tw 2) ≡ tw 1
tw₂-start = refl

tw₃-start : start-node (tw 3) ≡ tw 2
tw₃-start = refl

tw₃-next : next-node (tw 3) ≡ Ω̂ (suc (suc zero))
tw₃-next = refl

-- 任何只读树的算子, 换结点里的证明后输出定义性相等.
module TreeOnly {X : Set} (run : LF → X) where
  node-coherence : ∀ k c (w w′ : Lgl k c) (b b′ : Nested k c) t
    (g : (η : Raw k) → .(Gd k c η) → LF) →
    run (lc k c w b t g) ≡ run (lc k c w′ b′ t g)
  node-coherence k c w w′ b b′ t g = refl
```

## 4 读证书的算子: 证书参数无关时, 一致性是 `refl`

`YiK2cIrr.lim-function-equality-required` 说: 片段接口要求换证书后两个极限函数字面相等。
证书作普通参数时这要函数外延。证书作无关参数时它是定义性相等, 对任何证书谓词与任何算子成立。
这样的算子在旧块上写不出起点 (旧分支的守卫是普通参数, 无关的证书造不出它);
在本块上, 分支的守卫是无关参数, 证书里的证明可以直接交给分支。

```agda
module CertIrr (P : LF → Set) {X : Set} (run : (x : LF) → .(P x) → X) where
  certificate-coherence : ∀ x (p q : P x) → run x p ≡ run x q
  certificate-coherence x p q = refl

  lim-function-coherence : ∀ (f : ℕ → LF) (p q : ∀ n → P (f n)) →
    (λ n → run (f n) (p n)) ≡ (λ n → run (f n) (q n))
  lim-function-coherence f p q = refl

-- 用证书里的证明调用任意一支: 坐标是数据, 守卫是无关的证明.
call : ∀ k c .(w : Lgl k c) .(b : Nested k c) (t : LF)
  (g : (η : Raw k) → .(Gd k c η) → LF) (η : Raw k) → .(Gd k c η) → LF
call k c w b t g η e = g η e
```

## 5 守卫域为空的结点不存在

`YiK2Stop.no-start-all` 与 `YiWallConditional.funext-fold-tree→wlpo` 用的探针都是下界不合法、
守卫域为空的结点。本块的结点带着下界合法的 (无关) 证明, 所以守卫域不空。
证明无关, 结论只能写成双重否定; 这已经排除空域。

```agda
GuardNonEmpty : LF → Set
GuardNonEmpty zero = ⊤
GuardNonEmpty (suc x) = ⊤
GuardNonEmpty (lim f) = ⊤
GuardNonEmpty (lc k c w b t g) = ((η : Raw k) → Gd k c η → ⊥) → ⊥

all-guard-nonempty : ∀ x → GuardNonEmpty x
all-guard-nonempty zero = tt
all-guard-nonempty (suc x) = tt
all-guard-nonempty (lim f) = tt
all-guard-nonempty (lc k c w b t g) =
  λ none → ⊥-elim-irr (none c (inj₁ refl , w , b))
```

## 结论与范围

| 档 | 结果 |
|---|---|
| 编译事实 | 带无关证据的归纳—递归块通过正性、停机检查 (`RR5IrrCore`) |
| 编译定理 | `evidence-irrelevant`, `all-root-irr`, `raw-irr`: 换证明不换树, 分支不依赖守卫证明, 对一切树 |
| 编译定理 | `actual-same`: YiIntr 反例坐标的两份守卫给出同一棵树 |
| 编译构造 | `Ω̂ : LF → LF` 全函数; `tw : ℕ → LF`; `Λ` |
| 编译定理 | `tw₂-start`, `tw₃-start`, `tw₃-next`: 只读树的起点与下一支, `refl` |
| 编译定理 | `CertIrr.lim-function-coherence`: 证书参数无关时, 换证书后的极限函数定义性相等 |
| 编译定理 | `all-guard-nonempty`: 没有守卫域为空的结点 |
| 判断 | 折叠能否只在无关位置使用这些证明, 未验证。原块的规范构造 (`up`, `Ω̂`, `cO`) 本来就不看守卫 (`Legal.irr` 是 `refl` 传下来的), 这是支持的依据, 不是证明 |
| 判断 | 目标层不为 0 时的三路派发要用位置证据作数据来分情况; 那一处无关参数帮不上, 仍要判定型证据在公共界下给出。本篇没有碰 |

没有 Funext, 没有公设, 没有洞。强度没有变化: 记号无关树侧的值前沿仍是 ψ₀(Ω_{Ω·ω²})。
