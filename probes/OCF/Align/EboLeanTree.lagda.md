# EboLeanTree: 可数标准形的 `HC`, 极限树 `EBO-tree′` 与 `fgh-EBO′`

> **记号侧验收工作**, 读记号, 不进成品. [EboLean](EboLean.lagda.md) 第 3 层的出口.
>
> **结论 (编译过的定理, 无前提).**
>
> 1. `hc : NF t → Ctbl t → HC t`: 每个可数 EBO 标准形的基本列遗传良基且可数 (§2). 由 `wfNF′` (可数标准形上 $<^\mathsf T$ 良基), `cl-fsn-NF` (标准形对 ω-基本列封闭), `Ctbl-fsn` 与递减 (`Trian` 的 `t<`) 得出.
> 2. `EBO-tree′ = lim (k ↦ tree (hc (Ω-塔ₖ)))` 与 `fgh-EBO′ : FGH EBO-tree′ n ≡ fgh (EBOψ n) (hc-tower n) n` (§3): 极限树的 FGH 在 $n$ 处等于记号沿基本列的 FGH $f_{\psi_0(\Omega\text{-塔}_n)}(n)$. 这里不用标签: 树由 `HC` 推导直接造 (`tree`), `fgh-tree` 是三行的结构归纳.
>
> 树的类型是本文 §1 的三构造子布朗威尔树 `Ord` (与 `OCF.Align.Level` 的 `Ordᶜ zero` 同形, 在 [EboLeanCmp](EboLeanCmp.lagda.md) 里逐点对上现有的 `WfFsn.EBO-tree`). `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLeanTree where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase using (NF; InG; gp; gtl; gh; gw; gc; n[]; nf-pred; nf-ψ; nf-Ω;
  Ctbl; c[]; c∷; Ctbl-pred)
open import OCF.Align.EboLeanTrian using (t<; T-pred)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn; Ctbl-fsn; Ctbl-cof)
open import OCF.Align.EboLeanTau using (AccNF; accNF; wfNF′)
```

## §1 树与 FGH

```agda
data Ord : Set where
  zero : Ord
  suc  : Ord → Ord
  lim  : (ℕ → Ord) → Ord

FGH : Ord → ℕ → ℕ
FGH zero    n = suc n
FGH (suc a) n = iter (FGH a) n n
FGH (lim f) n = FGH (f n) n

tree : ∀ {t} → HC t → Ord
tree (h0 _)   = zero
tree (h1 _ h) = suc (tree h)
tree (hω _ h) = lim (λ n → tree (h n))

iter-ext : ∀ {f g : ℕ → ℕ} → (∀ m → f m ≡ g m) → ∀ x k → iter f x k ≡ iter g x k
iter-ext h x zero    = refl
iter-ext {g = g} h x (suc k) rewrite iter-ext h x k = h _

fgh-tree : ∀ {t} (h : HC t) n → FGH (tree h) n ≡ fgh t h n
fgh-tree (h0 _)   n = refl
fgh-tree (h1 _ h) n = iter-ext (fgh-tree h) n n
fgh-tree (hω _ h) n = fgh-tree (h n) n
```

## §2 可数标准形的 `HC`

```agda
hcA : ∀ {t} → NF t → Ctbl t → AccNF t → HC t
hcA {t} nt ct (accNF rs) = go (cof t) refl where
  go : ∀ c → cof t ≡ c → HC t
  go c0     e = h0 e
  go c1     e = h1 e (hcA (nf-pred nt) (Ctbl-pred ct) (rs (nf-pred nt) (Ctbl-pred ct) (t< (T-pred t e))))
  go cω     e = hω e (λ n → hcA (cl-fsn-NF nt e n) (Ctbl-fsn ct e n)
                          (rs (cl-fsn-NF nt e n) (Ctbl-fsn ct e n) (t< (trian-fsn nt e n))))
  go (cΩ μ) e = ⊥-elim (Ctbl-cof ct e)

hc : ∀ {t} → NF t → Ctbl t → HC t
hc nt ct = hcA nt ct (wfNF′ nt ct)
```

## §3 Ω-塔与极限树

$\psi_0(\Omega\text{-塔}_k)$ 是标准形, 对一切 $k$: $G_0$ 沿塔收集到的参数都是 $0$.

```agda
G0-tower : ∀ k {z} → InG [] z (ΩTower k) → z ≡ []
G0-tower zero    (gp (gh _))    = refl
G0-tower zero    (gp (gw _ ()))
G0-tower zero    (gp (gc _ ()))
G0-tower zero    (gtl ())
G0-tower (suc k) (gp (gh _))    = refl
G0-tower (suc k) (gp (gw _ i))  = G0-tower k i
G0-tower (suc k) (gp (gc _ ()))
G0-tower (suc k) (gtl ())

pos-tower : ∀ k → [] <ᵀ ΩTower k
pos-tower zero    = []<
pos-tower (suc k) = []<

nf-ΩT : ∀ k → NF (ΩTower k)
nf-ΩT zero    = nf-Ω n[]
nf-ΩT (suc k) = nf-Ω (nf-ΩT k)

nf-tower : ∀ k → NF (EBOψ k)
nf-tower k = nf-ψ n[] (nf-ΩT k) (λ i → subst (_<ᵀ ΩTower k) (sym (G0-tower k i)) (pos-tower k))

hc-tower : ∀ k → HC (EBOψ k)
hc-tower k = hc (nf-tower k) (c∷ c[])

EBO-tree′ : Ord
EBO-tree′ = lim (λ k → tree (hc-tower k))

fgh-EBO′ : ∀ n → FGH EBO-tree′ n ≡ fgh (EBOψ n) (hc-tower n) n
fgh-EBO′ n = fgh-tree (hc-tower n) n
```

## §4 有限测试 (测试档, 不是证明)

`fsn` 的值由 `refl` 算出 (与 [WfFsn](WfFsn.lagda.md) §3 相同的项). FGH 的值太大, 不算.

```agda
_ : fsn (EBOψ 1) 2 ≡ ψ [] (ψ [] (ψ [] (𝟏 ∷ []) ∷ []) ∷ []) ∷ []
_ = refl
```
