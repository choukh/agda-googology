# K2′ 第一阶段：零层结点片段与带证书的加法链

本篇只新增树侧定义。`Only0` 按构造子检查每个 lc 的层号字面为
zero；它递归第一支和全部原守卫分支，不比较层号，不把分支降为 Raw 0。
`Source0` 保留 YiCarry V1 的 Source，另附这一结构谓词。

这里先交可以独立编译的构造部件，**不是完整 ψ 或 K2′ 的实例**。
后面的 `FoldRows0` 把本轮真正要求的完整接口原样列出；未填的记录不算定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2bBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
open F using (module G)

Only0 : F.LF → Set
Only0 F.zero = ⊤
Only0 (F.suc x) = Only0 x
Only0 (F.lim f) = ∀ n → Only0 (f n)
Only0 (F.lc F.zero c t g) = Only0 t × (∀ η e → Only0 (g η e))
Only0 (F.lc (F.suc k) c t g) = ⊥
Only0 (F.lc (F.lim f) c t g) = ⊥
Only0 (F.lc (F.lc k c₀ t₀ g₀) c t g) = ⊥

record Source0 : Set where
  constructor source0
  field
    original : C.Source
    fragment : Only0 (C.term original)
open Source0 public

branch0 : ∀ {c t g} (r : C.Carry (F.lc F.zero c t g))
  (l : V.Legal (F.lc F.zero c t g)) → Only0 (F.lc F.zero c t g) →
  C.PointB F.zero c → Source0
branch0 r l q p = source0
  (C.branch-source r l (C.coordinate p) (C.guard p) (C.bounds p))
  (proj₂ q (C.coordinate p) (C.guard p))

read0-only : ∀ a → Only0 (V.up F.zero a)
read0-only G.zero = tt
read0-only (G.suc a) = read0-only a
read0-only (G.lim f) = λ n → read0-only (f n)
read0-only (G.lc () c t g)
read0-only (G.em () a)
read0-only G.top = tt

prefix-only : ∀ a → Only0 a → ∀ b → Only0 (a V.+ᴸ V.up F.zero b)
prefix-only a q G.zero = q
prefix-only a q (G.suc b) = prefix-only a q b
prefix-only a q (G.lim f) = λ n → prefix-only a q (f n)
prefix-only a q (G.lc () c t g)
prefix-only a q (G.em () b)
prefix-only a q G.top = q

record Output : Set where
  constructor output
  field
    raw : A.R
    legal : F.Lgl F.zero raw
    positive : F.Dn F.zero G.zero raw
open Output public

output-B : ∀ o → C.LglB F.zero (raw o)
output-B o = legal o , C.raw0-nested (raw o)

output-legal : ∀ o → V.Legal (V.up F.zero (raw o))
output-legal o = V.lgl→Legal F.zero tt (raw o) (legal o)

zero-output : Output
zero-output = output A.one tt (inj₁ refl)

suc-output : Output → Output
suc-output o = output (A.successor (raw o))
  (A.copies-step (raw o) (inj₂ (positive o)) , A.copies-legal (raw o) (legal o))
  (zero , inj₁ refl)

lim-output : (f : ℕ → Output) →
  (∀ n → F.Cp F.zero (raw (f n)) (raw (f (suc n)))) → Output
lim-output f st = output (G.lim (λ n → raw (f n)))
  (st , λ n → legal (f n)) (zero , inj₂ (positive (f zero)))
```

## 链：子调用交出输出包后，下一点不再是假设

`out` 可来自任意 LF 分支的子折叠，不要求分支本身为 Raw 0。
`mono` 仍是此部件的显式前提；完整递归 ψ 必须生产它。
两坐标的公共界是后坐标，`bounds` 给该界合法性。

```agda
module AddChain (c : A.R) (out : C.PointB F.zero c → Output)
  (mono : ∀ p q → F.Gd F.zero (C.coordinate p) (C.coordinate q) →
    F.Cp F.zero (raw (out p)) (raw (out q))) where

  next : C.PointB F.zero c → C.PointB F.zero c
  next p = C.point (A._+ʳ_ (C.coordinate p) (raw (out p)))
    (F.Cp-tr F.zero (proj₁ (C.guard p))
       (A.add-cp (C.coordinate p) (inj₂ (positive (out p)))) ,
     proj₁ (C.add-B (C.coordinate p) (raw (out p)) (C.bounds p) (output-B (out p))))
    (C.add-B (C.coordinate p) (raw (out p)) (C.bounds p) (output-B (out p)))

  grow : ∀ p → F.Dn F.zero (C.coordinate p) (C.coordinate (next p))
  grow p = A.add-dn (C.coordinate p) (raw (out p)) (positive (out p))

  step : ∀ p → F.Cp F.zero (raw (out p)) (raw (out (next p)))
  step p = mono p (next p) (inj₂ (grow p) , proj₁ (C.bounds (next p)))

  chain : C.PointB F.zero c → ℕ → C.PointB F.zero c
  chain initial = C.iterate next initial

  chain-grow : ∀ initial n →
    F.Dn F.zero (C.coordinate (chain initial n))
      (C.coordinate (chain initial (suc n)))
  chain-grow initial n = grow (chain initial n)

  collapse : C.PointB F.zero c → Output
  collapse initial = lim-output (λ n → out (chain initial n))
    (λ n → step (chain initial n))

  generator : ∀ (ψ : C.Source → A.R) t g r l →
    (∀ p → raw (out p) ≡
      ψ (C.branch-source r l (C.coordinate p) (C.guard p) (C.bounds p))) →
    C.PointB F.zero c → C.GtGenerator ψ F.zero c t g r l
  generator ψ t g r l eq initial = record
    { seed = initial
    ; next = next
    ; grow = grow
    ; output-step = λ p → cast-step (eq p) (eq (next p))
        (step p) (legal (out (next p)))
    }
    where
    cast-step : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ →
      F.Cp F.zero a b → F.Lgl F.zero b → C.RawStep F.zero a′ b′
    cast-step refl refl p l = record { path = p ; target-legal = l }
```

## 本轮要求的完整记录（未实填）

这个记录不改变 YiCarry。所有 Source0 都在定义域里；没有另加
“可折叠”“分支输出已单调”或证书相等的输入条件。

```agda
record FoldRows0 : Set where
  field
    ψ : Source0 → A.R
    gt-generator : ∀ c t g (r : C.Carry (F.lc F.zero c t g))
      (l : V.Legal (F.lc F.zero c t g)) (q : Only0 (F.lc F.zero c t g)) →
      C.PointB F.zero c → C.PointB F.zero c
    zero-row : ∀ r l q →
      ψ (source0 (C.source F.zero r l) q) ≡ A.one
    suc-row : ∀ x r l q →
      ψ (source0 (C.source (F.suc x) r l) q) ≡
      A.successor (ψ (source0 (C.source x r l) q))
    lim-row : ∀ f r st l q →
      ψ (source0 (C.source (F.lim f) r (st , l)) q) ≡
      G.lim (λ n → ψ (source0 (C.source (f n) (r n) (l n)) (q n)))
    gt-grow : ∀ c t g r l q p →
      F.Dn F.zero (C.coordinate p)
        (C.coordinate (gt-generator c t g r l q p))
    gt-additive0 : ∀ c t g r l q p →
      C.coordinate (gt-generator c t g r l q p) ≡
      A._+ʳ_ (C.coordinate p) (ψ (branch0 r l q p))
    gt-output-step : ∀ c t g r l q p →
      C.RawStep F.zero (ψ (branch0 r l q p))
        (ψ (branch0 r l q (gt-generator c t g r l q p)))
    gt-row : ∀ c t g r l q →
      ψ (source0 (C.source (F.lc F.zero c t g) r l) q) ≡
      G.lim (λ n → ψ (branch0 r l q
        (C.iterate (gt-generator c t g r l q) (C.start0-B r) n)))
    fold-B : ∀ s → C.LglB F.zero (ψ s)
    read-legal : ∀ s → V.Legal (V.up F.zero (ψ s))
    fold-positive : ∀ s → F.Dn F.zero G.zero (ψ s)
    bounded-position : ∀ a b →
      C.Common (C.term (original a)) (C.term (original b)) →
      V.CP (C.term (original a)) (C.term (original b)) →
      C.RawStep F.zero (ψ a) (ψ b)
```

`gt-generator` 在此只拆出 next 字段；seed 固定为 `start0-B`。
完整记录若实填，`output-B` 与 `bounded-position` 还须给相邻子输出的
RawStep，不能以本篇条件部件的 `mono` 代替它。

## 位置保持必须跨证书给字面相等

下面是必要条件定理，**没有否定完整记录**。不把“尚未证明”写成
“不能成立”，也不假定函数外延来填证书。
Raw 0 的第一位置无环由可达性递归证明，不比较两个 Raw。

```agda
data FirstAcc (a : A.R) : Set where
  accessible : (∀ {b} → F.Dn F.zero b a → FirstAcc b) → FirstAcc a

cp-accessible : ∀ {a b} → FirstAcc b → F.Cp F.zero a b → FirstAcc a
cp-accessible w (inj₁ refl) = w
cp-accessible (accessible next) (inj₂ p) = next p

raw-accessible : ∀ a → FirstAcc a
raw-accessible G.zero = accessible (λ ())
raw-accessible (G.suc a) = accessible (λ p → cp-accessible (raw-accessible a) p)
raw-accessible (G.lim f) = accessible
  (λ { (n , p) → cp-accessible (raw-accessible (f n)) p })
raw-accessible (G.lc () c t g)
raw-accessible (G.em () a)
raw-accessible G.top = accessible (λ ())

acc-irrefl : ∀ {a} → FirstAcc a → F.Dn F.zero a a → ⊥
acc-irrefl (accessible next) p = acc-irrefl (next p) p

raw-irrefl : ∀ {a} → F.Dn F.zero a a → ⊥
raw-irrefl {a} = acc-irrefl (raw-accessible a)

raw-antisym : ∀ {a b} → F.Cp F.zero a b → F.Cp F.zero b a → a ≡ b
raw-antisym (inj₁ e) q = e
raw-antisym (inj₂ p) (inj₁ refl) = ⊥-elim (raw-irrefl p)
raw-antisym (inj₂ p) (inj₂ q) = ⊥-elim (raw-irrefl (F.Dn-tr F.zero p q))

certificate-coherence-required : (d : FoldRows0) → ∀ x
  (r r′ : C.Carry x) (l l′ : V.Legal x) (q q′ : Only0 x) →
  FoldRows0.ψ d (source0 (C.source x r l) q) ≡
  FoldRows0.ψ d (source0 (C.source x r′ l′) q′)
certificate-coherence-required d x r r′ l l′ q q′ = raw-antisym
  (C.RawStep.path (FoldRows0.bounded-position d
    (source0 (C.source x r l) q) (source0 (C.source x r′ l′) q′)
    (C.common x l V.self V.self) V.self))
  (C.RawStep.path (FoldRows0.bounded-position d
    (source0 (C.source x r′ l′) q′) (source0 (C.source x r l) q)
    (C.common x l V.self V.self) V.self))
```

这里的公共界恰是合法的 x 本身；不从必要条件反推记录可满足。
“完整记录尚未实填”与本篇已编译部件的前提非空是两件事：
后者在 YiK2bNested 用真实嵌套 LF 分支实填。
