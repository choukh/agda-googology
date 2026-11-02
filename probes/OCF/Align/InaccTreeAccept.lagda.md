# 不可达层的树侧: 验收 (与 EBO 记号的比较)

> **验收节.** 记号只出现在本文件; InaccTreeBase 与 InaccTree 的定义不依赖记号 (导入链里没有 `OCF.Align.EBO`). 结论汇总在 [InaccTree](InaccTree.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccTreeAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.InaccTreeBase
open import OCF.Align.InaccTree
import OCF.Align.EBO as E
open E using (T; PT; cof; c0; c1; cω; cΩ; fsn; pred; Ωt; 𝟏) renaming (ψ to ψᵗ; natT to natᵗ)
open import OCF.Align.Stage2 using (Ωᵗ; t2; tO)
open import OCF.Align.OmegaKBase using (tΩ2)

```

## §1 比较器

`diff d w t x`: 沿宽度 `w`、深度 `d` 比较记号 `t` 的基本列树与树 `x` 的种类 (`c0`/`zero`, `c1`/`suc`, `cω`/`lim`). 返回第一个不一致的路径. `nothing` 表示范围内逐点一致.

```agda
diff  : ℕ → ℕ → T → Ordᴸ zero → Maybe (List ℕ)
diffs : ℕ → ℕ → ℕ → T → (ℕ → Ordᴸ zero) → Maybe (List ℕ)
diff zero w t x = nothing
diff (suc d) w t x with cof t | x
... | c0 | zero  = nothing
... | c1 | suc a = diff d w (pred t) a
... | cω | lim f = diffs w d w t f
... | _  | _     = just []
diffs zero d w t f = nothing
diffs (suc n) d w t f with diff d w (fsn t n) (f n)
... | just p  = just (n ∷ p)
... | nothing = diffs n d w t f

strip : T → Ordᴸ zero → T × Ordᴸ zero
strip t zero    = t , zero
strip t (suc a) = strip (pred t) a
strip t (lim f) = t , lim f

walkB : List ℕ → T → Ordᴸ zero → T × Ordᴸ zero
walkB [] t x = t , x
walkB (n ∷ rest) t x with strip t x
... | t′ , lim f = walkB rest (fsn t′ n) (f n)
... | t′ , x′    = t′ , x′

dfB : List ℕ → ℕ → ℕ → T → Ordᴸ zero → Maybe (List ℕ)
dfB rest d w t x = diff d w (proj₁ (walkB rest t x)) (proj₂ (walkB rest t x))
```

## §2 一个翻译: 记号到树, 没有阶段

把 I 层的树 `T0` 当作环境: 一切层号都是它的前驱, 所以和 (`add`) 不需要 `Sim` 证据. `⟦ ψ u w ⟧ = up (L u) (ψ_{L u} ⟦ w ⟧)`, `L u = 层号(⟦ u ⟧)`. **这一个函数覆盖 EBO 文法的全部**: 没有替身、没有前缀塔、没有阶段划分.

```agda
open ITier ver using (T0)

toLvU : T0 → Lv
toLvU zero       = zero
toLvU (suc x)    = suc (toLvU x)
toLvU (lim f)    = lim (λ n → toLvU (f n))
toLvU (limᵢ ℓ f) = limᴼ ℓ (λ y → toLvU (f y))
toLvU (limᴵ _)   = zero
toLvU (limB _)   = zero
toLvU (up ℓ x)   = toLv x
toLvU (upB _)    = zero

addU : T0 → T0 → T0
addU a zero       = a
addU a (suc b)    = suc (addU a b)
addU a (lim f)    = lim (λ n → addU a (f n))
addU a (limᵢ ℓ f) = limᵢ ℓ (λ y → addU a (f y))
addU a (limᴵ f)   = limᴵ (λ L → addU a (f L))
addU a (limB f)   = limB (λ b → addU a (f b))
addU a (up ℓ x)   = low x where
  low : ∀ {k} → Ordᴸ k → T0
  low zero    = a
  low (suc y) = suc (low y)
  low (lim f) = lim (λ n → low (f n))
  low {k} (limᵢ r f) = limᵢ (at k r) (λ y → low (f (intoL k r y)))
  low {suc k}    (up d y) = low y
  low {lim f}    (up d y) = low y
  low {limᴼ k g} (up d y) = low y
addU a (upB _)    = a

module Tr (D : Oracle) where
  open ITier D using (module I₀)

  ⟦_⟧  : T → T0
  ⟦_⟧ᴾ : PT → T0
  ⟦ [] ⟧     = zero
  ⟦ x ∷ xs ⟧ = addU ⟦ x ⟧ᴾ ⟦ xs ⟧
  ⟦ ψᵗ u w ⟧ᴾ = up (toLvU ⟦ u ⟧) (I₀.ψL {toLvU ⟦ u ⟧} ⟦ w ⟧)

down0 : T0 → Ordᴸ zero
down0 zero    = zero
down0 (suc x) = suc (down0 x)
down0 (lim f) = lim (λ n → down0 (f n))
down0 (up zero x) = x
down0 _       = zero

module Tr⁰ (D : Oracle) where
  open Tr D public

  ⟦_⟧⁰ : T → Ordᴸ zero
  ⟦ t ⟧⁰ = down0 ⟦ t ⟧

  _ : toLvU ⟦ Ωᵗ ⟧ ≡ L₁
  _ = refl
```

`verN`: 只回答两边都是有限数的比较, 其余一律 `rise`. 它下面的不一致路径就是 "第一个需要非平凡证据的点".

```agda
isNat : Lv → Bool
isNat zero       = true
isNat (suc a)    = isNat a
isNat (lim _)    = false
isNat (limᴼ _ _) = false

verN : Oracle
verN j i with isNat j ∧ isNat i
... | true  = ver j i
... | false = rise

-- 目标是 L₁ 型 (limᴼ) 时走 ver: 目标在一切可数层之上, 比较不需要证据的唯一情形
verM : Oracle
verM j i with isNat j ∧ isNat i
... | true  = ver j i
verM j (limᴼ k g) | false = ver j (limᴼ k g)
verM j (suc (limᴼ k g)) | false = ver j (suc (limᴼ k g))
verM j i | false = rise
```

## §3 逐项比较 (全部 `refl`)

所有比较都用启发式判决 `ver`, 所以结论是 "`ver` 在这些访问点上给出 EBO 的基本列", **不是** "`ver` 正确". 比较器不空洞: `t2` 对 `T₁` 在路径 `[0,1,0]` 处不一致 (`diff-detects`). `verN` (只答有限数比较) 在 `tΩ2` 上第一次出错的路径是 `first-nonnat`, 那里第一次需要非有限层的比较证据.

```agda
open Terms ver
open Tr⁰ ver
open import OCF.Align.StandardOmega using (walk)

ΩΩᵗ : PT
ΩΩᵗ = ψᵗ Ωᵗ []

t1 : T
t1 = ψᵗ [] (ΩΩᵗ ∷ []) ∷ []

diff-detects : diff 4 2 t2 T₁ ≡ just (0 ∷ 1 ∷ 0 ∷ [])
diff-detects = refl

-- 原生树 (InaccTree §2 的闭项) 与 EBO
c-T₁ : diff 7 3 t1 T₁ ≡ nothing
c-T₁ = refl
c-T₂ : diff 7 3 t2 T₂ ≡ nothing
c-T₂ = refl
c-TΩΩ : diff 6 2 tΩ2 TΩΩ ≡ nothing
c-TΩΩ = refl
c-TO : diff 6 2 tO TO+1 ≡ nothing
c-TO = refl

c-TΩΩ↓ : diff 6 2 tΩ2 TΩΩ↓ ≡ nothing
c-TΩΩ↓ = refl

-- 同一翻译 ⟦_⟧ 下的统一检验
u-t2 : diff 6 2 t2 ⟦ t2 ⟧⁰ ≡ nothing
u-t2 = refl
u-tΩ2 : diff 6 2 tΩ2 ⟦ tΩ2 ⟧⁰ ≡ nothing
u-tΩ2 = refl
u-tO : diff 6 2 tO ⟦ tO ⟧⁰ ≡ nothing
u-tO = refl
u-EBO4 : diff 6 2 (E.EBOψ 4) ⟦ E.EBOψ 4 ⟧⁰ ≡ nothing
u-EBO4 = refl

-- ψ₀(Λ): 第 n 项是 Ω-塔
lamᵀ : ℕ → Ordᴸ zero
lamᵀ n = ψ⁰ (Ω (iter ΩL zero n))

_ : EBOᵀ ≡ lim lamᵀ
_ = refl
c-EBO2 : diff 6 2 (E.EBOψ 2) (lamᵀ 2) ≡ nothing
c-EBO2 = refl
c-EBO3 : diff 6 2 (E.EBOψ 3) (lamᵀ 3) ≡ nothing
c-EBO3 = refl
```

其它形状: 共尾度 Ω₂ 的 `ψ₀(Ω_{Ω₂})` (`limᴼ` 的参数层非 0), Stage2 的前缀暴露项 `tP = ψ₀(Ω_Ω+ψ₁(Ω_Ω))`.

```agda
tΩΩ₂ tP : T
tΩΩ₂ = ψᵗ [] (Ωt (Ωt (natᵗ 2))) ∷ []
tP   = ψᵗ [] (ΩΩᵗ ∷ ψᵗ (natᵗ 1) (ΩΩᵗ ∷ []) ∷ []) ∷ []

c-tΩΩ₂ : diff 8 2 tΩΩ₂ ⟦ tΩΩ₂ ⟧⁰ ≡ nothing
c-tΩΩ₂ = refl
c-tP : diff 8 3 tP ⟦ tP ⟧⁰ ≡ nothing
c-tP = refl
```

**现行路线的障碍点.** (a) `low-term` 路径 (`noSim21` 的来源); (b) OmegaSqA §5 的路径: 外层第 1 个链点 θ₁ 处的分支, 沿 `[0,1,0,0,0]` 到第 2 份副本的首链点, 那里现行 `fold` 的极限层地板 `fk L₁` 给出过高的界. 新折叠在这些点上与 EBO 一致, 再往下 5–6 层、宽 3 也一致.

```agda
pathLow : List ℕ
pathLow = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []

Ω₂+1ᵗ : T
Ω₂+1ᵗ = ψᵗ (natᵗ 2) [] ∷ 𝟏 ∷ []

low-at-tree : proj₁ (walkB (pathLow ++ (2 ∷ 0 ∷ 0 ∷ [])) tΩ2 ⟦ tΩ2 ⟧⁰) ≡ ψᵗ [] (ψᵗ Ωᵗ Ω₂+1ᵗ ∷ []) ∷ []
low-at-tree = refl

low-ok : dfB (pathLow ++ (2 ∷ 0 ∷ 0 ∷ [])) 5 3 tΩ2 ⟦ tΩ2 ⟧⁰ ≡ nothing
low-ok = refl

-- 弹栈点 low-pop: 指数后继行再 [1]
low-pop-ok : dfB (pathLow ++ (2 ∷ 0 ∷ 0 ∷ 1 ∷ [])) 5 3 tΩ2 ⟦ tΩ2 ⟧⁰ ≡ nothing
low-pop-ok = refl

pθ : List ℕ
pθ = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ []

θ-at : walk tΩ2 pθ ≡ ψᵗ [] (ψᵗ Ωᵗ [] ∷ Ωt (natᵗ 1)) ∷ []
θ-at = refl

θ-tree : proj₁ (walkB pθ tΩ2 ⟦ tΩ2 ⟧⁰) ≡ ψᵗ [] (ψᵗ Ωᵗ [] ∷ Ωt (natᵗ 1)) ∷ []
θ-tree = refl

θ-ok : dfB pθ 6 3 tΩ2 ⟦ tΩ2 ⟧⁰ ≡ nothing
θ-ok = refl

-- verN: 第一个非有限比较
first-nonnat : diff 8 3 tΩ2 (Tr⁰.⟦_⟧⁰ verN tΩ2) ≡ just (2 ∷ 2 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
first-nonnat = refl
nonnat-t2 : diff 8 3 t2 (Tr⁰.⟦_⟧⁰ verN t2) ≡ nothing
nonnat-t2 = refl
```

## §4 "降维打击" 的陈述与第一批部件

**单一定理.** `LabN x t` 是第 0 层树对记号的逐项标签 (与 Correspond 的 `Lab` 同形, 只是在 `Ordᴸ zero` 上). 一次拿下 ψ₀(Λ) 之下全部的命题是 `Strike`: 存在一个判决 `D`, 使一个翻译 `⟦_⟧` 对类 `P` 内每个项都带标签. 它的两个分量是 `Agree` (判决与 `cmpᵀ` 一致, 只对类内下标) 与 `Commute` (翻译与基本列交换).

```agda
data LabN : Ordᴸ zero → T → Set where
  l0 : ∀ {t} → cof t ≡ c0 → LabN zero t
  l1 : ∀ {a t} → cof t ≡ c1 → LabN a (pred t) → LabN (suc a) t
  lω : ∀ {f t} → cof t ≡ cω → (∀ n → LabN (f n) (fsn t n)) → LabN (lim f) t

Strike : (T → Set) → Set
Strike P = Σ Oracle λ D → ∀ t → P t → LabN (Tr⁰.⟦_⟧⁰ D t) t

-- 判决的规格: 只对类内下标, 只看 cmpᵀ
L : Oracle → T → Lv
L D u = toLvU (Tr.⟦_⟧ D u)

data Spec (j i : Lv) : Verdict j i → E.Cmp → Set where
  sp-lt : ∀ {r b} → j ≅ at i r → Spec j i (pen r b) E.lt
  sp-eq : Spec j i rise E.eq
  sp-gt : Spec j i rise E.gt

Agree : (T → Set) → Oracle → Set
Agree P D = ∀ u v → P u → P v → Spec (L D u) (L D v) (D (L D u) (L D v)) (E.cmpᵀ u v)

-- Agree 的序内容: 项序给树序 (Lab-oc 的反方向, 即 Bachmann 性质)
OrderEmb : (T → Set) → Oracle → Set
OrderEmb P D = ∀ u v → P u → P v → E.cmpᵀ u v ≡ E.lt → L D u ≺ L D v
```

**部件 (对一切判决, 抽象项, `refl`).** 规则 0、1、4 与链的形状都是定义性的: 折叠与 EBO 六条规则逐条对应, 差别只在派发. 所以 `Commute` 的归纳里, 非平凡的只剩穿透 (`pen`, 要 `fsT` 与分支的交换) 与链 (`rise`, 要 `γ` 与 `iter` 的交换) 两种情形的下标搬运.

```agda
module Pieces (D : Oracle) where
  open Tr D renaming (⟦_⟧ to 〚_〛; ⟦_⟧ᴾ to 〚_〛ᴾ)
  open ITier D using (module I₀)
  open Fold D renaming (ψ to ψᴰ)
  open import Data.Nat using () renaming (_+_ to _+ℕ_)

  ψ-of : T → T → T0
  ψ-of u w = 〚 ψᵗ u w ∷ [] 〛

  rule0 : ∀ u → ψ-of u [] ≡ up (toLvU 〚 u 〛) (Ω (toLvU 〚 u 〛))
  rule0 u = refl

  sum-suc : ∀ x → 〚 x ∷ 𝟏 ∷ [] 〛 ≡ suc 〚 x ∷ [] 〛
  sum-suc x = refl

  rule4 : ∀ u x → 〚 ψᵗ u (x ∷ 𝟏 ∷ []) 〛ᴾ ≡
          up (toLvU 〚 u 〛) (lim (iter (I₀.ψL {toLvU 〚 u 〛} 〚 x 〛ᴾ +_) zero))
  rule4 u x = refl

  rule5 : ∀ u x r b → D (toLvU 〚 x ∷ [] 〛) (toLvU 〚 u 〛) ≡ pen r b →
          I₀.ψL {toLvU 〚 u 〛} 〚 ψᵗ (x ∷ 𝟏 ∷ []) [] ∷ [] 〛 ≡
          limᵢ r (λ y → ψᴰ {toLvU 〚 u 〛} {toLvU 〚 x ∷ [] 〛} (b (outL (toLvU 〚 u 〛) r y)))
  rule5 u x r b e with D (toLvU 〚 x ∷ [] 〛) (toLvU 〚 u 〛) | e
  ... | pen _ _ | refl = refl

  rule6 : ∀ u x → D (toLvU 〚 x ∷ [] 〛) (toLvU 〚 u 〛) ≡ rise →
          I₀.ψL {toLvU 〚 u 〛} 〚 ψᵗ (x ∷ 𝟏 ∷ []) [] ∷ [] 〛 ≡
          lim (λ n → ψᴰ {toLvU 〚 u 〛} {toLvU 〚 x ∷ [] 〛} (iter (λ y → ψᴰ {toLvU 〚 x ∷ [] 〛} {toLvU 〚 x ∷ [] 〛} y) (Ω (toLvU 〚 x ∷ [] 〛)) n))
  rule6 u x e with D (toLvU 〚 x ∷ [] 〛) (toLvU 〚 u 〛) | e
  ... | rise | refl = refl
```

**`ver` 确实是错的 (在采样范围外).** `ver` 对 `20 ≺ ω` 答 `rise`, 因为它只搜索 ω 的前 16 项. 这不影响 §3 的检验点, 但说明 §3 只是有限证据. 另外判决不可能只靠裸层号的 `≅`-不变性以外的信息: 见 InaccTree §1 的 `noBT`.

```agda
ver-wrong : ver (natL 20) (lim natL) ≡ rise
ver-wrong = refl

_ : natL 20 ≺ lim natL
_ = via (21 , inj₁ tt) (≅-refl _)
```

**`OrderEmb` 的闭点样本.** 项序给结构序, 见证是字面路径 (`Ω₂` 的 `limᴼ` 分支 `suc Ω₁` 之下的 `inj₁`).

```agda
ωᵗ : T
ωᵗ = ψᵗ [] (𝟏 ∷ []) ∷ []

ε₀ᵗ : T
ε₀ᵗ = ψᵗ [] (Ωt (natᵗ 1)) ∷ []

oe₁ : L ver ωᵗ ≺ L ver (ωᵗ ++ (𝟏 ∷ []))
oe₁ = via (inj₁ tt) (≅-refl _)

oe₂ : L ver ε₀ᵗ ≺ L ver (natᵗ 0 ++ Ωt (natᵗ 1))
oe₂ = via (inj₂ (suc (Tr⁰.⟦_⟧⁰ ver ε₀ᵗ) , inj₁ tt)) (≅-refl _)

oe₃ : L ver (Ωt (natᵗ 1)) ≺ L ver (Ωt (natᵗ 2))
oe₃ = via (inj₂ (suc (Ω (suc zero)) , inj₁ tt)) (≅-refl _)
```
