# EboLean3Tree: 可数标准形的 `HC`, 极限树 `EBO-tree″` 与 `fgh-EBO″`

> **记号侧验收工作**, 读记号, 不进成品. [EboLean3](EboLean3.lagda.md) 第 3 层的出口.
>
> **结论 (编译过的定理, 无前提).** `hc : NF t → Ctbl t → HC t`; `EBO-tree″ = lim (k ↦ tree (hc (Ω-塔ₖ)))`; `fgh-EBO″ : FGH EBO-tree″ n ≡ fgh (EBOψ n) (hc-tower n) n`. 与 [EboLeanTree](EboLeanTree.lagda.md) 同形, 只把良基换成 [EboLean3Omega](EboLean3Omega.lagda.md) 的 `wf` (一切标准形良基, 不经 τ), 所以导入闭包里没有 Setzer 的 OT_I. 封闭性 (`cl-fsn-NF`, `trian-fsn`, `Ctbl-fsn`, `Ctbl-cof`) 原样复用 [EboLeanClosure](EboLeanClosure.lagda.md). 本文的定义本来就短 (树、FGH、`hcA`、Ω-塔是标准形), 按原样的形状重写.
>
> `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3Tree where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase using (NF; n[]; nf-pred; nf-ψ; nf-Ω; InG; gp; gtl; gh; gw; gc;
  Ctbl; c[]; c∷; Ctbl-pred)
open import OCF.Align.EboLeanTrian using (t<; T-pred)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn; Ctbl-fsn; Ctbl-cof)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)
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
iter-ext h x (suc k) rewrite iter-ext h x k = h _

fgh-tree : ∀ {t} (h : HC t) n → FGH (tree h) n ≡ fgh t h n
fgh-tree (h0 _)   n = refl
fgh-tree (h1 _ h) n = iter-ext (fgh-tree h) n n
fgh-tree (hω _ h) n = fgh-tree (h n) n
```

## §2 可数标准形的 `HC`

```agda
hcA : ∀ {t} → NF t → Ctbl t → Acc′ t → HC t
hcA {t} nt ct (acc rs) = go (cof t) refl where
  go : ∀ c → cof t ≡ c → HC t
  go c0     e = h0 e
  go c1     e = h1 e (hcA (nf-pred nt) (Ctbl-pred ct) (rs (nf-pred nt) (t< (T-pred t e))))
  go cω     e = hω e (λ n → hcA (cl-fsn-NF nt e n) (Ctbl-fsn ct e n) (rs (cl-fsn-NF nt e n) (t< (trian-fsn nt e n))))
  go (cΩ μ) e = ⊥-elim (Ctbl-cof ct e)

hc : ∀ {t} → NF t → Ctbl t → HC t
hc nt ct = hcA nt ct (wf nt)
```

## §3 Ω-塔与极限树

```agda
G0 : ∀ k {z} → InG [] z (ΩTower k) → z ≡ []
G0 zero    (gp (gh _))   = refl
G0 zero    (gp (gw _ ()))
G0 zero    (gp (gc _ ()))
G0 zero    (gtl ())
G0 (suc k) (gp (gh _))   = refl
G0 (suc k) (gp (gw _ i)) = G0 k i
G0 (suc k) (gp (gc _ ()))
G0 (suc k) (gtl ())

nf-ΩT : ∀ k → NF (ΩTower k)
nf-ΩT zero    = nf-Ω n[]
nf-ΩT (suc k) = nf-Ω (nf-ΩT k)

hc-tower : ∀ k → HC (EBOψ k)
hc-tower k = hc (nf-ψ n[] (nf-ΩT k) (λ i → subst (_<ᵀ ΩTower k) (sym (G0 k i)) (pos k))) (c∷ c[])
  where
    pos : ∀ k → [] <ᵀ ΩTower k
    pos zero    = []<
    pos (suc k) = []<

EBO-tree″ : Ord
EBO-tree″ = lim (λ k → tree (hc-tower k))

fgh-EBO″ : ∀ n → FGH EBO-tree″ n ≡ fgh (EBOψ n) (hc-tower n) n
fgh-EBO″ n = fgh-tree (hc-tower n) n
```
