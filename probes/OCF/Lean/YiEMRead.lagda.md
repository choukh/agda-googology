# 替身码加嵌入码
编译定理，不读记号，形状档：码 `Read⁺ b` 按偏移 b 分型，在 `YiBSRead.Read` 之外加嵌入码 `em c`（沿偏移的孩子 c 嵌入）；`read⁺ a` 在 `a ⊕ b` 上读，`fold⁺` 换到 `j ⊕ b` 上读再折；旧码逐字嵌入（`in-old`、`fold-old`、`omega-row⁺`），第一位置关系经 `fold⁺` 保持（`fold-step⁺`，证明同 `YiBSRead.fold-step`）。
闭包：码对沿偏移内 `⊑` 路由的嵌入封闭（`emb-pre`、`cp-emb`）；`Ok⊕` 形证据沿偏移内任意路径降到的每个 ℕ 极限结点上，`way` 给的路径都是这种组合（`ok-down`、`way-in`），所以 way 行嵌入码对仍是码对。
不否定什么：`BS.ψ` 的 `seen` 一支对一切块仍用 `old omega`（`omega-row⁺`），本件不改折叠；没有从树恢复码的函数。真实链点见 `YiEMChain`，否定见 `YiEMNeg`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEMRead where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase
open import OCF.Lean.YiBSRead using (Read; omega; read; source; Domain; fold; PointStep)
open import OCF.Lean.YiBCCover using (rb⊑)
```

## 码、读出、码域与换基后的折叠

码的下标是偏移 b，不是整个层号：`em c` 只沿偏移自己的结点嵌入，所以换基 `a ↦ j` 后同一个码仍读得出（`j ⊕ nd s h` 的孩子集仍是 `Ch s`）。偏移为零时只有旧码。

```agda
data Read⁺ : L → Set where
  old : ∀ {b} → Read → Read⁺ b
  em  : ∀ {s h} (c : Ch s) → Read⁺ (h c) → Read⁺ (nd s h)

read⁺ : (a : L) {b : L} → Read⁺ b → Tr⁺ (a ⊕ b)
read⁺ a {b} (old d) = read (a ⊕ b) d
read⁺ a (em c d)    = upz c (read⁺ a d)

source⁺ : ∀ {k h} (S : Schema k h) c → Read⁺ (offsets S c) → Tr⁺ (h c)
source⁺ S c d = subst Tr⁺ (sym (shape S c)) (read⁺ (floor S) d)

Domain⁺ : ∀ {k h} (S : Schema k h) c → Tr (h c) → Set
Domain⁺ S c y = Σ (Read⁺ (offsets S c)) λ d → y ≡ proj₁ (source⁺ S c d)

fold⁺ : ∀ {k h} (S : Schema k h) c → Read⁺ (offsets S c) → (j : L) → Ok j → floor S ≤ j → Tr⁺ j → Tr⁺ j
fold⁺ S c d j oj u β = R.ψ (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (B₀ _) j (lift j (offsets S c)) β (proj₁ (read⁺ j d))
```

旧码逐字嵌入；`seen` 是 `old omega` 的换基，与 `YiBSRead.omega-row` 同。

```agda
in-old : ∀ {k h} (S : Schema k h) c {y : Tr (h c)} → Domain S c y → Domain⁺ S c y
in-old S c (d , e) = old d , e

fold-old : ∀ {k h} (S : Schema k h) c d j oj u β → fold⁺ S c (old d) j oj u β ≡ fold S c d j oj u β
fold-old S c d j oj u β = refl

omega-row⁺ : ∀ {k h} (S : Schema k h) c j oj u β → fold⁺ S c (old omega) j oj u β ≡ seen S j oj u β c
omega-row⁺ S c j oj u β = refl

Ωt-subst : {x y : L} (e : x ≡ y) → proj₁ (Ωt y) ≡ proj₁ (subst Tr⁺ e (Ωt x))
Ωt-subst refl = refl

omega-any : ∀ {k h} (S : Schema k h) c → Domain⁺ S c (proj₁ (Ωt (h c)))
omega-any S c = old omega , Ωt-subst (sym (shape S c))
```

Ω 树在 ℕ 极限与 Ω 形状偏移结点上的子块是同一地板上孩子偏移的 `old omega`（后继形状结点的子块是 `suc c`，c 是分支变元，那里没有换基行）。

```agda
omega-sL : (a : L) (g : ℕ → L) → Ωt (a ⊕ nd sL g) ≡ limc⁺ (λ n → upz n (read⁺ a {g n} (old omega)))
omega-sL a g = refl

omega-sΩ : (a k : L) (h : Tr k → L) → Ωt (a ⊕ nd (sΩ k) h) ≡ Ω⁺ (inj₁ (inj₁ tt)) (λ c → upz c (read⁺ a {h c} (old omega)))
omega-sΩ a k h = refl
```

嵌入码就是一步 `emb`；`rbO` 给的证据（地板 a、偏移 h、`shape` 为 `refl`）下，码域就是 `read⁺ a` 的像。

```agda
em-emb : (a : L) {s : Sh} {h : Ch s → L} (o : Ok (a ⊕ nd s h)) (c : Ch s) (d : Read⁺ (h c))
  → read⁺ a (em c d) ≡ emb (a ⊕ nd s h) o (inc c self) (read⁺ a d)
em-emb a o c d = refl

rbO-top : (a k : L) (h : Tr k → L) (ra : Rb a) (oa : Ok a) (ob : OkO a (nd (sΩ k) h))
  → proj₁ (rbO a (nd (sΩ k) h) ra oa ob) ≡ just (schema a h oa (proj₁ (proj₁ ob)) (proj₂ ob) (λ c → refl))
rbO-top a k h ra oa ob = refl

code-in : {k : L} (a : L) (h : Tr k → L) (oa : Ok a) (v : k ≤ a) (ob : (c : Tr k) → OkO a (h c))
  (c : Tr k) (d : Read⁺ (h c)) → Domain⁺ (schema a h oa v ob (λ _ → refl)) c (proj₁ (read⁺ a d))
code-in a h oa v ob c d = d , refl
```

第一位置关系：嵌入码对同一孩子的码保序，旧码继承 `PointStep`，经 `fold⁺` 保持（`YiRBSib.mono`，同 `YiBSRead.fold-step`）。

```agda
PointStep⁺ : ∀ {b} → Read⁺ b → Read⁺ b → Set
PointStep⁺ {b} d e = (a : L) → a ⊕ b ⊢ proj₁ (read⁺ a d) ◃ proj₁ (read⁺ a e)

old-step : ∀ {b} d e → PointStep d e → PointStep⁺ {b} (old d) (old e)
old-step {b} d e st a = st (a ⊕ b)

em-step : ∀ {s h} (c : Ch s) {d e : Read⁺ (h c)} → PointStep⁺ d e → PointStep⁺ {nd s h} (em c d) (em c e)
em-step c st a = ◃c zero c (st a)

fold-step⁺ : ∀ {k h} (S : Schema k h) c d e j oj u β → PointStep⁺ d e
  → j ⊢ proj₁ (fold⁺ S c d j oj u β) ◃ proj₁ (fold⁺ S c e j oj u β)
fold-step⁺ S c d e j oj u β st = R.mono (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (B₀ _) j (lift j (offsets S c)) β (st j)
```

## 沿偏移内路由的嵌入

`pre w`：沿 `⊑` 路径 w 逐步加嵌入码（`inu` 取 `c₀`，与 `emb` 同）。`emb-pre`：沿 `wk (⊕⊑ a w)` 嵌入码读出的树对（树与非零证明）就是 `pre w` 的读出。`emb-∙`：沿复合路径的嵌入分两段。

```agda
pre : ∀ {b b′} → b ⊑ b′ → Read⁺ b → Read⁺ b′
pre self              d = d
pre (inc c v)         d = em c (pre v d)
pre (inu {s = s} vs)  d = em (c₀ s) (pre (vs (c₀ s)) d)

emb-pre : (a : L) {b b′ : L} (w : b ⊑ b′) (o : Ok (a ⊕ b′)) (d : Read⁺ b)
  → emb (a ⊕ b′) o (wk (⊕⊑ a w)) (read⁺ a d) ≡ read⁺ a (pre w d)
emb-pre a self             o d = refl
emb-pre a (inc c w)        o d = cong (upz c) (emb-pre a w (proj₂ o c) d)
emb-pre a (inu {s = s} vs) o d = cong (upz (c₀ s)) (emb-pre a (vs (c₀ s)) (proj₂ o (c₀ s)) d)

emb-∙ : (ℓ : L) (o : Ok ℓ) {i j : L} (v : i ≤ j) (w : j ⊑ ℓ) (y : Tr⁺ i)
  → emb ℓ o (v ∙ wk w) y ≡ emb ℓ o (wk w) (emb j (downOk ℓ o j (wk w)) v y)
emb-∙ ℓ o v self y = refl
emb-∙ (nd s h) o v (inc c w) y = cong (upz c) (emb-∙ (h c) (proj₂ o c) v w y)
emb-∙ (nd s h) o v (inu vs)  y = cong (upz (c₀ s)) (emb-∙ (h (c₀ s)) (proj₂ o (c₀ s)) v (vs (c₀ s)) y)
```

`CP a u`：u 是若干段 `wk (⊕⊑ a w)` 自左向右的复合（`from0` 的形状）。码对沿这样的路径嵌入仍是码对。

```agda
data CP (a : L) {b : L} : {b′ : L} → a ⊕ b ≤ a ⊕ b′ → Set where
  cp₀ : CP a {b} {b} self
  cp∙ : ∀ {b′ b″} {u : a ⊕ b ≤ a ⊕ b′} → CP a u → (w : b′ ⊑ b″) → CP a (u ∙ wk (⊕⊑ a w))

cp-emb : (a : L) {b b′ : L} {u : a ⊕ b ≤ a ⊕ b′} → CP a u → (o : Ok (a ⊕ b′)) (d : Read⁺ b)
  → Σ (Read⁺ b′) λ d′ → emb (a ⊕ b′) o u (read⁺ a d) ≡ read⁺ a d′
cp-emb a cp₀ o d = d , refl
cp-emb a (cp∙ {b′ = b′} {b″ = b″} {u = u} c w) o d with cp-emb a c (downOk (a ⊕ b″) o (a ⊕ b′) (wk (⊕⊑ a w))) d
... | d₁ , e₁ = pre w d₁ , trans (emb-∙ (a ⊕ b″) o u (⊕⊑ a w) (read⁺ a d))
  (trans (cong (emb (a ⊕ b″) o (wk (⊕⊑ a w))) e₁) (emb-pre a w o d₁))
```

## ℕ 极限结点的路由

`Ok⊕ a (nd sL g) oa (os , ob)` 的路由逐字是 `wk (⊕⊑ a (os n))`（`route⊕`），沿孩子降下的证据仍是 `Ok⊕`（`down⊕`；沿偏移内任意 `⊑` 路径，`ok-down`），换基证据仍是同一地板的 `rbO`（`rb-down`，Ω 形状结点上即 `rbO-top` 的 schema）；`way` 在这种路由上给的两种路径都是 `CP`（`way-cp`）。`way-in`：way 行 `inj₁` 一支把码对嵌成码对。

```agda
route⊕ : (a : L) (g : ℕ → L) (oa : Ok a) (os : (n : ℕ) → g n ⊑ g (suc n)) (ob : (n : ℕ) → OkO a (g n)) (n : ℕ)
  → proj₁ (Ok⊕ a (nd sL g) oa (os , ob)) n ≡ wk (⊕⊑ a (os n))
route⊕ a g oa os ob n = refl

down⊕ : (a : L) (s : Sh) (h : Ch s → L) (oa : Ok a) (ob : OkO a (nd s h)) (c : Ch s)
  → proj₂ (Ok⊕ a (nd s h) oa ob) c ≡ Ok⊕ a (h c) oa (proj₂ ob c)
down⊕ a s h oa ob c = refl

downO : (a : L) {b′ b : L} → b′ ⊑ b → OkO a b → OkO a b′
downO a self             ob = ob
downO a (inc c w)        ob = downO a w (proj₂ ob c)
downO a (inu {s = s} vs) ob = downO a (vs (c₀ s)) (proj₂ ob (c₀ s))

ok-down : (a : L) {b′ b : L} (w : b′ ⊑ b) (oa : Ok a) (ob : OkO a b)
  → downOk (a ⊕ b) (Ok⊕ a b oa ob) (a ⊕ b′) (wk (⊕⊑ a w)) ≡ Ok⊕ a b′ oa (downO a w ob)
ok-down a self             oa ob = refl
ok-down a (inc c w)        oa ob = ok-down a w oa (proj₂ ob c)
ok-down a (inu {s = s} vs) oa ob = ok-down a (vs (c₀ s)) oa (proj₂ ob (c₀ s))

rb-down : (a : L) {b′ b : L} (w : b′ ⊑ b) (ra : Rb a) (oa : Ok a) (ob : OkO a b)
  → rb⊑ (a ⊕ b) (rbO a b ra oa ob) (⊕⊑ a w) ≡ rbO a b′ ra oa (downO a w ob)
rb-down a self                   ra oa ob = refl
rb-down a (inc {s = sS} c w)     ra oa ob = rb-down a w ra oa (proj₂ ob c)
rb-down a (inc {s = sL} c w)     ra oa ob = rb-down a w ra oa (proj₂ ob c)
rb-down a (inc {s = sΩ k} c w)   ra oa ob = rb-down a w ra oa (proj₂ ob c)
rb-down a (inu {s = sS} vs)      ra oa ob = rb-down a (vs tt) ra oa (proj₂ ob tt)
rb-down a (inu {s = sL} vs)      ra oa ob = rb-down a (vs zero) ra oa (proj₂ ob zero)
rb-down a (inu {s = sΩ k} vs)    ra oa ob = rb-down a (vs zero) ra oa (proj₂ ob zero)

from0-cp : (a : L) (g : ℕ → L) (w : (n : ℕ) → g n ⊑ g (suc n)) (n : ℕ)
  → CP a {g zero} {g n} (from0 (λ i → a ⊕ g i) (λ i → wk (⊕⊑ a (w i))) n)
from0-cp a g w zero    = cp₀
from0-cp a g w (suc n) = cp∙ (from0-cp a g w n) (w n)

WayCP : (a b₁ b₂ : L) → (a ⊕ b₁ ≤ a ⊕ b₂) ⊎ (a ⊕ b₂ ≤ a ⊕ b₁) → Set
WayCP a b₁ b₂ (inj₁ u) = CP a {b₁} {b₂} u
WayCP a b₁ b₂ (inj₂ u) = CP a {b₂} {b₁} u

way-cp : (a : L) (g : ℕ → L) (w : (n : ℕ) → g n ⊑ g (suc n)) (m n : ℕ)
  → WayCP a (g m) (g n) (way (λ i → a ⊕ g i) (λ i → wk (⊕⊑ a (w i))) m n)
way-cp a g w m       zero    = from0-cp a g w m
way-cp a g w zero    (suc n) = from0-cp a g w (suc n)
way-cp a g w (suc m) (suc n) = way-cp a (λ i → g (suc i)) (λ i → w (suc i)) m n

WayIn : (a b₁ b₂ : L) → Read⁺ b₁ → (a ⊕ b₁ ≤ a ⊕ b₂) ⊎ (a ⊕ b₂ ≤ a ⊕ b₁) → Set
WayIn a b₁ b₂ d (inj₁ u) = (o : Ok (a ⊕ b₂)) → Σ (Read⁺ b₂) λ d′ → emb (a ⊕ b₂) o u (read⁺ a d) ≡ read⁺ a d′
WayIn a b₁ b₂ d (inj₂ u) = ⊤

way-in : (a : L) (g : ℕ → L) (w : (n : ℕ) → g n ⊑ g (suc n)) (m n : ℕ) (d : Read⁺ (g m))
  → WayIn a (g m) (g n) d (way (λ i → a ⊕ g i) (λ i → wk (⊕⊑ a (w i))) m n)
way-in a g w m n d = go (way (λ i → a ⊕ g i) (λ i → wk (⊕⊑ a (w i))) m n) (way-cp a g w m n)
  where
  go : (X : (a ⊕ g m ≤ a ⊕ g n) ⊎ (a ⊕ g n ≤ a ⊕ g m)) → WayCP a (g m) (g n) X → WayIn a (g m) (g n) d X
  go (inj₁ u) c = λ o → cp-emb a c o d
  go (inj₂ u) c = tt
```

合起来：`Ok⊕` 形证据与 `rbO` 形换基证据的层号 `a ⊕ b` 上，沿偏移内任意 `⊑` 路径降到的 ℕ 极限结点，way 行嵌入码对得码对（`way-at`）；降到的 Ω 形状结点，换基证据的 schema 地板是 a、`shape` 是 `refl`（`schema-at`），那里的 `Domain⁺` 就是 `read⁺ a` 的像（`code-in`）。

```agda
way-at : (a : L) {b : L} (g′ : ℕ → L) (w : nd sL g′ ⊑ b) (oa : Ok a) (ob : OkO a b) (m n : ℕ) (d : Read⁺ (g′ m))
  → WayIn a (g′ m) (g′ n) d (way (λ i → a ⊕ g′ i) (proj₁ (downOk (a ⊕ b) (Ok⊕ a b oa ob) (a ⊕ nd sL g′) (wk (⊕⊑ a w)))) m n)
way-at a g′ w oa ob m n d =
  subst (λ O → WayIn a (g′ m) (g′ n) d (way (λ i → a ⊕ g′ i) (proj₁ O) m n)) (sym (ok-down a w oa ob))
    (way-in a g′ (proj₁ (downO a w ob)) m n d)

schema-at : (a : L) {b : L} (k : L) (h : Tr k → L) (w : nd (sΩ k) h ⊑ b) (ra : Rb a) (oa : Ok a) (ob : OkO a b)
  → proj₁ (rb⊑ (a ⊕ b) (rbO a b ra oa ob) (⊕⊑ a w))
  ≡ just (schema a h oa (proj₁ (proj₁ (downO a w ob))) (proj₂ (downO a w ob)) (λ _ → refl))
schema-at a k h w ra oa ob = cong proj₁ (rb-down a w ra oa ob)
```
