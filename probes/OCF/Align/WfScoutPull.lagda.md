# WfScoutPull: 沿 τ 拉回 OT_I 的良基, 剩下的义务

> 侦察实验 (报告在 [NotationWF](../../Survey/NotationWF.md)). 验收侧, 读记号与标签, 不进成品.
>
> **条件定理 (`Pull`, `Std`).** 设类 `P` 对 `pred`, `fsn` 封闭, 其元素可数 (`Ctbl`), 且 τ 把 `P` 送进 Setzer 的 `OT`. 那么 `P` 上 `_<ᵀ_` 良基 (`wf`, 即 [AccTreeLab](AccTreeLab.lagda.md) 的 `AccP`), 于是有遗传良基 `HC`, 带标签的树 (`lab`), FGH 逐点等于记号沿基本列的 FGH (`fgh`). 证明只是把归档 OT_I 的 `Acc-endpt 1` 沿 τ 拉回: τ 严格保序 (`τ-mono`) 与 `τ-bd` 已在 [WfScoutTau](WfScoutTau.lagda.md) 证明, 不是前提.
>
> **取 `P` = EBO 标准形 × 可数 (`Std`).** 剩下三个前提, 都是记号侧的句法定理, 都没证: `cl-pred` (标准形对 `pred` 封闭, 平凡), `cl-fsn` (对 `fsn` 封闭, 即 Lean `OTFS_thm` 的 ℕ-下标部分, 但证明要带上 Ω-基本列), `τ-NF` (τ 保标准形, 义务 3). 给定它们, Ω-塔 `EBOψ k` 对一切 $k$ 有标签 (`ebo-lab`; `isOTᵉ (EBOψ k)` 已证, `nf-tower`), 极限树 `EBO-tree` 的 FGH 在 $n$ 处就是 $f_{\psi_0(\Omega\text{-塔}_n)}(n)$ (`fgh-EBO`).
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 编译要把归档 (或其拷贝) 加进 `-i`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfScoutPull where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

import OCF.Align.EBO as E
open E using (T; cof; pred; fsn; c1; cω; EBOψ; ΩTower)
open import OCF.Align.EBOI using (isOTᵉ; isOTᵉᴾ; Gᵉ; Gᵉᴾ)
open import OCF.Align.Standard using (Ctbl; c[]; c∷; Ctbl-pred; Ctbl-fsn; Ctbl-cof)
open import OCF.Align.Level using (Ordᶜ; zero; lim; FGH)
open import OCF.Align.Correspond using (Lab)
open import OCF.Align.AccTree using (fghₙ; fgh-tree)
open import OCF.Align.AccTreeLab using (module Class; HC; treeᴴ; HC→Acc)

open import Mahlo.Inacc.Closure using (OT)
open import Mahlo.Inacc.BoolLemmas using (∧-intro)
open import Mahlo.Inacc.FactsImpl using (facts)
import Mahlo.Inacc.WO.Main facts as M
open import OCF.Align.WfScoutTau using (τ; τ-mono; τ-bd)
```

## §1 拉回

`go` 对 OT_I 的可达性证书递归: $b<^\mathsf T t$ 且 $b\in P$ 时 $\tau b\prec\tau t$ 且 $\tau b\in\mathrm{OT}$, 所以 $\tau b$ 的证书是 $\tau t$ 的证书的分支.

```agda
module Pull (P : T → Set)
  (P-pred : ∀ {t} → P t → cof t ≡ c1 → P (pred t))
  (P-fsn  : ∀ {t} → P t → cof t ≡ cω → ∀ n → P (fsn t n))
  (P-ctbl : ∀ {t} → P t → Ctbl t)
  (τ-OT   : ∀ {t} → P t → OT (τ t)) where

  open Class P P-pred P-fsn (λ p e → Ctbl-cof (P-ctbl p) e) public

  go : ∀ {t} → P t → M.Acc (τ t) → AccP t
  go pt (M.acc rs) = acc (λ pb b<t → go pb (rs (τ-OT pb) (τ-mono b<t)))

  wf : ∀ {t} → P t → AccP t
  wf pt = go pt (M.Acc-endpt 1 (τ-OT pt) (τ-bd (P-ctbl pt)))

  hc : ∀ {t} → P t → HC t
  hc pt = wf→HC pt (wf pt)

  lab : ∀ {t} (pt : P t) → Lab (treeᴴ (hc pt)) t
  lab pt = wf→lab pt (wf pt)

  fgh : ∀ {t} (pt : P t) n → FGH (treeᴴ (hc pt)) n ≡ fghₙ t (HC→Acc (hc pt)) n
  fgh {t} pt n = fgh-tree t (HC→Acc (hc pt)) n
```

## §2 标准形实例与 Ω-塔

`nf-tower`: Ω-塔是 EBO 标准形 (对一切 $k$, 不是测试). $G_0$ 沿塔收集到的参数都是 $0$.

```agda
∧t : ∀ {x} → x ≡ true → (x ∧ true) ≡ true
∧t refl = refl

G-tower : ∀ k {y ys} → Gᵉ [] (ΩTower k) (y ∷ ys) ≡ true
G-tower zero          = refl
G-tower (suc zero)    = refl
G-tower (suc (suc k)) = ∧t (∧t (G-tower (suc k)))

nf-Ω : ∀ k → isOTᵉ (ΩTower k) ≡ true
nf-Ω zero          = refl
nf-Ω (suc zero)    = refl
nf-Ω (suc (suc k)) = ∧t (nf-Ω (suc k))

nf-tower : ∀ k → isOTᵉ (EBOψ k) ≡ true
nf-tower zero    = refl
nf-tower (suc k) = ∧t (∧-intro (nf-Ω (suc k)) (G-tower (suc k)))

module Std
  (cl-pred : ∀ {t} → isOTᵉ t ≡ true → cof t ≡ c1 → isOTᵉ (pred t) ≡ true)
  (cl-fsn  : ∀ {t} → isOTᵉ t ≡ true → Ctbl t → cof t ≡ cω → ∀ n → isOTᵉ (fsn t n) ≡ true)
  (τ-NF    : ∀ {t} → isOTᵉ t ≡ true → OT (τ t)) where

  P : T → Set
  P t = (isOTᵉ t ≡ true) × Ctbl t

  open Pull P (λ (n , c) e → cl-pred n e , Ctbl-pred c)
              (λ (n , c) e k → cl-fsn n c e k , Ctbl-fsn c e k)
              proj₂ (λ (n , _) → τ-NF n) public

  p-tower : ∀ k → P (EBOψ k)
  p-tower k = nf-tower k , c∷ c[]

  ebo-lab : ∀ k → Lab (treeᴴ (hc (p-tower k))) (EBOψ k)
  ebo-lab k = lab (p-tower k)

  EBO-tree : Ordᶜ zero
  EBO-tree = lim (λ k → treeᴴ (hc (p-tower k)))

  fgh-EBO : ∀ n → FGH EBO-tree n ≡ fghₙ (EBOψ n) (HC→Acc (hc (p-tower n))) n
  fgh-EBO n = fgh (p-tower n) n
```
