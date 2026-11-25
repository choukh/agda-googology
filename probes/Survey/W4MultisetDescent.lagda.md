# 用有限分裂验收 W4 的整树下界

第四层。一次真实下降可供同一基本列分支使用任意有限次。Agda 给出后继参数的复制、任意和前缀中的执行，以及在真实树上选择较小主项的程序。文末经典纸面证明计算任意有限层分裂的精确秩，并给出直达 EBO 的判据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4MultisetDescent where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Align.EboLeanDef hiding (lt; eq)
open import OCF.Align.EboLeanBase using (NF; Ctbl)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Lean.YiRefTw2 using (Rt)
open import WVOne using (T₀)
import Survey.W4PTOAddresses as A

-- 每步只动一个位置。顺序仅记录地址，秩使用有限自然和。
data Split {X : Set} (down : X → X → Set) : List X → List X → Set where
  replace : ∀ {x xs ys} → All (down x) ys → Split down (x ∷ xs) (ys ++ xs)
  keep : ∀ {x xs ys} → Split down xs ys → Split down (x ∷ xs) (x ∷ ys)

prefix : ∀ {X} {d : X → X → Set} ps {xs ys} →
         Split d xs ys → Split d (ps ++ xs) (ps ++ ys)
prefix [] h = h
prefix (p ∷ ps) h = keep (prefix ps h)

copies : ∀ {X : Set} {d : X → X → Set} {x y : X} → d x y → ∀ n → All (d x) (replicate n y)
copies h zero = []
copies {d = d} {x} {y} h (suc n) = h ∷ copies {d = d} {x} {y} h n

data Place (root : T₀) : T₀ → Set where
  start : Place root root
  visit : ∀ {x y} → Place root x → A.Hop x y → Place root y

Token : T₀ → Set
Token root = Σ T₀ (Place root)

data Step {root} : Token root → Token root → Set where
  follow : ∀ {x y} {p : Place root x} (e : A.Hop x y) → Step (x , p) (y , visit p e)

State : T₀ → ℕ → Set
State root zero = Token root
State root (suc d) = List (State root d)

Move : ∀ {root} d → State root d → State root d → Set
Move zero = Step
Move (suc d) = Split (Move d)

-- 证书可随分支改变。同一个父地址可给不同的较小主项各选一个孩子。
choose : ∀ {root t s} (nt : NF t) (ns : NF s) (ct : Ctbl t)
  (ht : HC t) (hs : HC s) → s <ᵀ t → (p : Token root) → Rt ht ≼ proj₁ p →
  Σ (Token root) λ q → Step p q × Rt hs ≼ proj₁ q
choose nt ns ct ht hs lt (x , p) bound with
  A.pick {x = Rt hs} {y = x} (≼-trans {b = Rt ht} (mono<ⁿ ns nt ct hs ht lt) bound)
... | y , e , fits = (y , visit p e) , follow e , fits

-- 原规则 4 的定义等式。前缀留在外层，替换的份数可为零。
rule-four : ∀ u b bs → cof (b ∷ bs) ≡ c1 → ∀ n →
  fsn (ψ u (b ∷ bs) ∷ []) n ≡ replicate n (ψ u (pred (b ∷ bs)))
rule-four u b bs eq n rewrite eq = refl

branch : ∀ {root d} {p q : State root d} → Move d p q → ∀ ps xs n →
  Move (suc d) (ps ++ (p ∷ xs)) (ps ++ (replicate n q ++ xs))
branch {d = d} h ps xs n = prefix ps (replace (copies {d = Move d} h n))

open import WVOne using (read)
import W4Fold as W
W4-state = State (read W.EBOᶜ)
W4-move : ∀ d → W4-state d → W4-state d → Set
W4-move = Move
```

**经典纸面证明。** 记 $Y$ 为 W4 整树的经典值。深度零的状态是从根出发的有限真实路径，其秩恰为路径终点的树值。一步穿过有限个极限并取一次后继前驱；`A.below` 和 `A.least` 给出所有一步后继秩加一的上确界公式。含根的整个状态域高度为 $Y+1$，这里域高度取所有状态秩加一的上确界。[真实路径](W4PTOAddresses.lagda.md)

在下一深度，给各分量秩 $r_i$ 的列表赋自然和 $\mathop{\#}_i\omega^{r_i}$。替换一个分量时，新加入的有限项的指数都严格较小，此自然和严格下降。它也是精确秩。空表秩为零；对非空表，选指数最小的一个分量 $r$，把其余贡献记为 $P$，原秩为 $P+\omega^r$。若 $r=0$，删除该分量得到直接前驱。若 $r>0$，对每个真实子步所得的指数 $b$ 可放入任意 $n$ 份，得到 $P+\omega^b n$。由 $r=\sup_b(b+1)$，这些秩加一的上确界为 $P+\omega^r$。对状态的赋值作超限归纳即得等号。每一深度的域高度 $h$ 因而变成 $\omega^h$（可重复任意一个状态，且可取空表）。这用到的替换关系可参见 [Dershowitz–Manna 的多重集序](https://doi.org/10.1145/359138.359142)。

初始时可选任一有限深度，之后固定该深度。各深度的高度上确界恰为 $\varepsilon^+(Y)$，即从 $Y+1$ 开始迭代 $x\mapsto\omega^x$ 的极限。若每个可数标准项都能从某个这样的状态模拟其严格下降，则原参照值 $R\le\varepsilon^+(Y)$，从而 $R\le Y$，最后一步使用原 EBO 为 ε 数的极限。已有值比较给出深度零的 `choose`；如何在缺少起点比较时建立模拟，由[只计回灌的验收](W4CriticalDescent.lagda.md)进一步缩小范围。
