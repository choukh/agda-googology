# AccTree: 记号的良基证明机械地转成树, FGH 逐点相同

> **判决: HOLDS, 带一处修正.** 通用定理与 EBO 实例都是编译过的定理. 修正: EBO 文件里字面的 `Acc` (全部项上的 `_<ᵀ_`) **恰好**只在自然数上成立 (`acc→nat`, `nat→acc`), 所以 `EBO-number` 的前提是假的 (`¬EBO-number`), `fgh-treeᴱ` 在 ω 以上没有输入. 对外那句话要读成: **基本列下降**的良基证明 (`Acc`, 关于 `_◁_`) 机械地转成树, FGH 逐点相同; 可数标准形上 `_<ᵀ_` 的良基证明能转成它 ([AccTreeLab](AccTreeLab.lagda.md) 的 `wf→HC`), EBO 全体的这个前提未证.
>
> 1. **通用定理 (§1).** 对任何带 `view` (零/前驱/基本列, 各带递减证书) 的记号系统 `Notation`: `tree : ∀ a → Acc a → Ordᶜ zero`, `fgh-tree : FGH (tree a h) n ≡ fghₙ a h n`, `tree-≅`, `fgh-indep`. 不用 funext: 无关性模 $\cong$ 与逐点相等, 不要 `Acc` 证明本身相等.
> 2. **树类型.** 选 `OCF.Align.Level` 的 `Ordᶜ zero`: `Lab` 与现有标签定理都在这个类型上. 第 0 层没有 `limᵢ`, `up`, 就是 `zero`, `suc`, `lim`. 主线 `OCF.Free.Level` 是字面相同的另一份, 经 `Bridge` 的 `⟦_⟧` 过来 ([AccTreeLab](AccTreeLab.lagda.md) §4). 选 `Ordᶜ zero` 而不是 `OCF.BTBO` 的 `Ord₀` 只为接 `Lab`, 三处 FGH 子句相同.
> 3. **没有差一 (§3).** 树上 `FGH (suc a) n = iter (FGH a) n n`, `FGH (lim f) n = FGH (f n) n`; 记号 `go c1 = iter (FGH (pred a) _) n n`, `go cω = FGH (a[n]) _ n`. 对角取 $a[n]$, 不是 $a[n+1]$; 两边的 `iter` 是两份定义, 由 `iter≡` 接上. 零行都是 `suc n`.
> 4. **`cΩ` 行.** EBO 的 FGH 对 $\Omega$-共尾的项走 ℕ-截断的基本列 (哑值). 为对一切 `a` 逐点相等, 树也走 `lim`. 代价: $\Omega$ 与 $\omega$ 给 $\cong$ 的树 (`tree-Ω≅ω`), 而记号上 `cmpᵀ Ω ω ≡ gt`. `Lab` 没有这一行, 所以标签要 "遗传地不碰 `cΩ`" 这个前提 (AccTreeLab).
> 5. **工程注记.** EBO 的 `FGH` 的分派是 `where` 里的 `go`, 不能命名, `with cof a` 又因 `refl` 的类型不能抽象. 文件不许改, 所以用反射从 `FGH` 的子句读出 `go` 的名字 (`goᴱ`). 只取名字, 结果照常过类型检查.
>
> 这是记号一侧的小定理, 读记号, 不算记号无关, 不进成品. `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AccTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.List using ([]; _∷_; replicate)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.Reflection using (TC; Term; def; getDefinition; function; clause; typeError; strErr; unify; bindTC)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level using (Ordᶜ; zero; suc; lim; _≅_; z≅; s≅; l≅; FGH; FGH-≅; iter-ext)
import OCF.Align.EBO as E
open E using (T; ψ; 𝟏; natT; Ωt; cof; pred; fsn; fsn↓; dec; cmpᵀ; _<ᵀ_; []<; hd<; tl<; lv<; ar<;
              c0; c1; cω; cΩ; gt)
```

## §1 通用定理

`View` 是 `cof`, 基本列与递减证书打包的结果: 每个项是零, 或有带证书的前驱, 或有带证书的 ℕ-基本列. `fghₙ` 是记号自己的 FGH, 沿 `Acc` 递归; `tree` 用同一个 `view` 造树. 分派写成一等函数 (`fghV`, `treeV`), 证明时对 `view` 的值分情况.

```agda
data View {Tm : Set} (_≺_ : Tm → Tm → Set) (a : Tm) : Set where
  vz : View _≺_ a
  vs : (p : Tm) → p ≺ a → View _≺_ a
  vl : (f : ℕ → Tm) → (∀ n → f n ≺ a) → View _≺_ a

record Notation : Set₁ where
  field
    Tm   : Set
    _≺_  : Tm → Tm → Set
    view : ∀ a → View _≺_ a

module Generic (N : Notation) where
  open Notation N

  data Acc (a : Tm) : Set where
    acc : (∀ {b} → b ≺ a → Acc b) → Acc a

  Rs : Tm → Set
  Rs a = ∀ {b} → b ≺ a → Acc b

  fghₙ : ∀ a → Acc a → ℕ → ℕ
  fghV : ∀ {a} → View _≺_ a → Rs a → ℕ → ℕ
  fghₙ a (acc rs) = fghV (view a) rs
  fghV vz       rs n = suc n
  fghV (vs p q) rs n = iter (fghₙ p (rs q)) n n
  fghV (vl f q) rs n = fghₙ (f n) (rs (q n)) n

  tree  : ∀ a → Acc a → Ordᶜ zero
  treeV : ∀ {a} → View _≺_ a → Rs a → Ordᶜ zero
  tree a (acc rs) = treeV (view a) rs
  treeV vz       rs = zero
  treeV (vs p q) rs = suc (tree p (rs q))
  treeV (vl f q) rs = lim (λ n → tree (f n) (rs (q n)))

  fgh-tree  : ∀ a h n → FGH (tree a h) n ≡ fghₙ a h n
  fgh-treeV : ∀ {a} (v : View _≺_ a) (rs : Rs a) n → FGH (treeV v rs) n ≡ fghV v rs n
  fgh-tree a (acc rs) = fgh-treeV (view a) rs
  fgh-treeV vz       rs n = refl
  fgh-treeV (vs p q) rs n = iter-ext (fgh-tree p (rs q)) n n
  fgh-treeV (vl f q) rs n = fgh-tree (f n) (rs (q n)) n

  tree-≅  : ∀ a (h h′ : Acc a) → tree a h ≅ tree a h′
  tree-≅V : ∀ {a} (v : View _≺_ a) (rs rs′ : Rs a) → treeV v rs ≅ treeV v rs′
  tree-≅ a (acc rs) (acc rs′) = tree-≅V (view a) rs rs′
  tree-≅V vz       rs rs′ = z≅
  tree-≅V (vs p q) rs rs′ = s≅ (tree-≅ p (rs q) (rs′ q))
  tree-≅V (vl f q) rs rs′ = l≅ (λ n → tree-≅ (f n) (rs (q n)) (rs′ (q n)))

  fgh-indep : ∀ a h h′ n → fghₙ a h n ≡ fghₙ a h′ n
  fgh-indep a h h′ n = trans (sym (fgh-tree a h n)) (trans (FGH-≅ (tree-≅ a h h′) n) (fgh-tree a h′ n))
```

## §2 EBO 实例: 基本列下降

树只用到 `pred` 与 `fsn`, 所以最弱的前提是沿这两步的良基. `_◁_` 就是这两步; `cΩ` 行照 EBO 的 FGH 走截断基本列. 这个实例的 `Acc` 比 `E.Acc` 弱 (`toAcc`), 而它的 `fghₙ` 与 `E.FGH` 是同一组方程 (§3).

```agda
data _◁_ : T → T → Set where
  ◁p : ∀ {a} → cof a ≡ c1 → pred a ◁ a
  ◁ω : ∀ {x xs} → cof (x ∷ xs) ≡ cω → ∀ n → fsn (x ∷ xs) n ◁ (x ∷ xs)
  ◁Ω : ∀ {x xs μ} → cof (x ∷ xs) ≡ cΩ μ → ∀ n → fsn (x ∷ xs) n ◁ (x ∷ xs)

◁→< : ∀ {a b} → b ◁ a → b <ᵀ a
◁→< (◁p {a} e)         = E.pred-< a e
◁→< (◁ω {x} {xs} e n)  = dec (fsn↓ x xs n)
◁→< (◁Ω {x} {xs} e n)  = dec (fsn↓ x xs n)

viewᶜ : ∀ a c → cof a ≡ c → View _◁_ a
viewᶜ a        c0     e = vz
viewᶜ a        c1     e = vs (pred a) (◁p e)
viewᶜ []       cω     ()
viewᶜ (x ∷ xs) cω     e = vl (fsn (x ∷ xs)) (◁ω e)
viewᶜ []       (cΩ μ) ()
viewᶜ (x ∷ xs) (cΩ μ) e = vl (fsn (x ∷ xs)) (◁Ω e)

EBOᴺ : Notation
EBOᴺ = record { Tm = T ; _≺_ = _◁_ ; view = λ a → viewᶜ a (cof a) refl }

open Generic EBOᴺ public

toAcc : ∀ {a} → E.Acc a → Acc a
toAcc (E.acc rs) = acc (λ q → toAcc (rs (◁→< q)))

treeᴱ : ∀ a → E.Acc a → Ordᶜ zero
treeᴱ a h = tree a (toAcc h)
```

## §3 与 `E.FGH` 逐点相等

`goᴱ` 是 `E.FGH` 里 `where` 的 `go`, 由反射取名字. `E.FGH (x ∷ xs) (acc rs) n` 定义性地是 `goᴱ x xs rs n (cof (x ∷ xs)) refl` (`refl` 检查). 于是对一般的 `c` 与 `e : cof (x ∷ xs) ≡ c` 证明, 再取 `c = cof (x ∷ xs)`.

```agda
private
  goTerm : Term → TC ⊤
  goTerm hole = bindTC (getDefinition (quote E.FGH)) λ where
    (function (_ ∷ clause _ _ (def nm _) ∷ [])) → unify hole (def nm [])
    _ → typeError (strErr "E.FGH 的形状变了" ∷ [])

goᴱ : ∀ x xs → (∀ {b} → b <ᵀ (x ∷ xs) → E.Acc b) → ℕ → ∀ c → cof (x ∷ xs) ≡ c → ℕ
goᴱ = unquote goTerm

iter≡ : ∀ {f g : ℕ → ℕ} → (∀ m → f m ≡ g m) → ∀ a k → iter f a k ≡ E.iter g a k
iter≡ h a zero    = refl
iter≡ {g = g} h a (suc k) = trans (h _) (cong g (iter≡ h a k))

fgh-eq  : ∀ a (h : E.Acc a) n → fghₙ a (toAcc h) n ≡ E.FGH a h n
fgh-eqᶜ : ∀ x xs (rs : ∀ {b} → b <ᵀ (x ∷ xs) → E.Acc b) n c (e : cof (x ∷ xs) ≡ c) →
          fghV (viewᶜ (x ∷ xs) c e) (λ q → toAcc (rs (◁→< q))) n ≡ goᴱ x xs rs n c e
fgh-eq []       (E.acc rs) n = refl
fgh-eq (x ∷ xs) (E.acc rs) n = fgh-eqᶜ x xs rs n (cof (x ∷ xs)) refl
fgh-eqᶜ x xs rs n c0     e = refl
fgh-eqᶜ x xs rs n c1     e = iter≡ (fgh-eq (pred (x ∷ xs)) (rs (E.pred-< (x ∷ xs) e))) n n
fgh-eqᶜ x xs rs n cω     e = fgh-eq (fsn (x ∷ xs) n) (rs (dec (fsn↓ x xs n))) n
fgh-eqᶜ x xs rs n (cΩ μ) e = fgh-eq (fsn (x ∷ xs) n) (rs (dec (fsn↓ x xs n))) n

fgh-treeᴱ : ∀ a (h : E.Acc a) n → FGH (treeᴱ a h) n ≡ E.FGH a h n
fgh-treeᴱ a h n = trans (fgh-tree a (toAcc h) n) (fgh-eq a h n)

treeᴱ-≅ : ∀ a (h h′ : E.Acc a) → treeᴱ a h ≅ treeᴱ a h′
treeᴱ-≅ a h h′ = tree-≅ a (toAcc h) (toAcc h′)

E-fgh-indep : ∀ a (h h′ : E.Acc a) n → E.FGH a h n ≡ E.FGH a h′ n
E-fgh-indep a h h′ n = trans (sym (fgh-treeᴱ a h n)) (trans (FGH-≅ (treeᴱ-≅ a h h′) n) (fgh-treeᴱ a h′ n))
```

## §4 `E.Acc` 恰好在自然数上成立

`_<ᵀ_` 不要求标准形. 对任何 $t$, 若 $1+t<t$, 则 $t>1+t>1+1+t>\cdots$ 是无穷降链 (`no-self`). 首项不是 $\mathbf 1$ 的项都满足前提, 第一步走 `hd<`. 这比 EBO §9 说的强: 不只 "不良基", 而是 $\omega$ 已经没有 `Acc`. 与 `Uniform5NF` 的 `¬Acc-T` (从 $\Omega$ 下降) 同类, 但这里给的是确切的边界.

```agda
no-self : ∀ {t} → E.Acc t → (𝟏 ∷ t) <ᵀ t → ⊥
no-self (E.acc rs) q = no-self (rs q) (tl< q)

acc-tail : ∀ {x xs} → E.Acc (x ∷ xs) → E.Acc xs
acc-tail (E.acc rs) = E.acc (λ q → acc-tail (rs (tl< q)))

acc→nat : ∀ a → E.Acc a → Σ ℕ λ k → a ≡ natT k
acc→nat []                  h = 0 , refl
acc→nat (ψ (w ∷ ws) b ∷ xs) h = ⊥-elim (no-self h (hd< (lv< []<)))
acc→nat (ψ [] (y ∷ ys) ∷ xs) h = ⊥-elim (no-self h (hd< (ar< []<)))
acc→nat (ψ [] [] ∷ xs)      h with acc→nat xs (acc-tail h)
... | k , refl = suc k , refl

nat→acc : ∀ {a} → (Σ ℕ λ k → a ≡ natT k) → E.Acc a
nat→acc (k , refl) = E.accNat k

ωt : T
ωt = ψ [] (natT 1) ∷ []

¬acc-ω : E.Acc ωt → ⊥
¬acc-ω h with acc→nat ωt h
... | zero , ()
... | suc k , ()

¬EBO-number : (∀ n → E.Acc (E.EBOψ n)) → ⊥
¬EBO-number wf = ¬acc-ω (wf 0)
```

## §5 测试与实例

有限测试, 不是证明. `E.Acc` 的实例都是自然数. 基本列下降的实例走得更远: $\omega$ 在这里, ψ₀(Ω_Ω) 及以上见 [AccTreeLab](AccTreeLab.lagda.md) §3–§4, 由现有标签定理给出.

```agda
_ : FGH (treeᴱ (natT 2) (E.accNat 2)) 2 ≡ 8
_ = refl

_ : FGH (treeᴱ (natT 3) (E.accNat 3)) 2 ≡ 2048
_ = refl

_ : E.FGH (natT 3) (E.accNat 3) 2 ≡ 2048
_ = refl

fsn-ω : ∀ n → fsn ωt n ≡ natT n
fsn-ω n = trans (E.rep-trm [] (E.pred-< (natT 1) refl) n) (rep≡ n) where
  rep≡ : ∀ n → replicate n 𝟏 ≡ natT n
  rep≡ zero    = refl
  rep≡ (suc n) = cong (𝟏 ∷_) (rep≡ n)

acc-ω : Acc ωt
acc-ω = acc λ where
  (◁p ())
  (◁ω refl n) → subst Acc (sym (fsn-ω n)) (toAcc (E.accNat n))

_ : FGH (tree ωt acc-ω) 2 ≡ 8       -- f_ω(2) = f₂(2)
_ = refl

_ : fghₙ ωt acc-ω 2 ≡ 8
_ = refl
```

## §6 树不保留比较

`Ωᵗ = ψ_1(0)`. FGH 的 `cΩ` 行把 $\Omega$ 截成 $\omega$, 树照抄, 所以两棵树 $\cong$; 记号上 $\Omega>\omega$. 这只是 `cΩ` 哑值造成的; 一般地, 第 0 层的树只有 $\cong$ 与结构序, 比较要证据, 没有 `cmpᵀ` 那样的判定 (`Stage2` 的 `dec→WLPO`: 对任意层号判定 $a\prec^\mathsf I\mathrm{suc}\,\omega$ 推出 WLPO). 所以 `tree` 单向: 记号给树, 树不给回 `cmpᵀ`.

```agda
Ωᵗ : T
Ωᵗ = Ωt (natT 1)

acc-Ω : Acc Ωᵗ
acc-Ω = acc λ where
  (◁p ())
  (◁Ω refl n) → toAcc (E.accNat n)

_ : cmpᵀ Ωᵗ ωt ≡ gt
_ = refl

tree-≡ : ∀ {a b} → a ≡ b → (h : Acc a) (h′ : Acc b) → tree a h ≅ tree b h′
tree-≡ refl h h′ = tree-≅ _ h h′

tree-Ω≅ω : tree Ωᵗ acc-Ω ≅ tree ωt acc-ω
tree-Ω≅ω = l≅ (λ n → tree-≡ (sym (fsn-ω n)) _ _)
```
