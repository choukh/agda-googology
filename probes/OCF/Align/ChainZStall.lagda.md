# 链从 0 起 (四): 字面的 $x_0=\mathrm{bot}$ 停在底

> 不含记号. 入口 [ChainZ](ChainZ.lagda.md). 种子取 `bot₀` ($x_0=\mathrm{hz}$, 审查 D2 的原文) 时, 若闭包节点的高度界与当前世界的高度界之间的路是空的 (`q₀` 的高度分量是 `hself`, 节点就在当前高度界下造的, 闭项里最常见的情形), 那么**链的每一格都是 `hz`, 每一格的输出都是空树** (`stall`, `stall-out`). 原因: 第 0 格的界是 $\beta\boxplus\mathrm{hz}=\beta$, 从节点的界走到 $\beta$ 是空路, $\Delta_0$ 空, $x_1=\mathrm{rd}(\mathrm{hz},\Delta_0)=\mathrm{hz}$, 归纳.
>
> 这是差树 (输出是增量) 与 BTBO 的不同: BTBO 的 $\gamma_1=\psi_q(f\,0)$ 是分支在 $0$ 处的**值**; 这里第 $n$ 格的输出是沿 "上一格到这一格" 的路走出的**增量**, 路空则增量空. 所以链从 0 起必须有一个不空的种子; 种子取状态里的输出 (`out₀`) 不读界, 也不停 (见 `ChainZTest`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (D₊; Ht; Wd₂)
module OCF.Align.ChainZStall
  (S : ∀ {Kd : Wd₂ → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wd₂ → Set} {Z₀ Z₁ : Set} {W} → D₊ Kd V′ Z₀ Z₁ W → D₊ Kd V′ Z₀ Z₁ W)
  (Λ : Ht) (lΛ : LgB Λ) (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (_⊲_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Align.HtTowerTy hiding (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFRead using (D₁; rd; rd-fst)
open import OCF.Align.HtTowerFFold S Λ lΛ one⊲ using (yc; Tg; τ₁; Cl₁; v₁; lv₁; av₁; Bu; LW; Ig; St)
open import OCF.Align.ChainZFold S Λ lΛ one⊲ (λ _ _ → hz) (λ _ _ → tt)
```

`Triv P`: 第一位置的证据是 `hself` (空路).

```agda
Triv : ∀ {S} {a b : HB S} {w} → a ⊲[ w ] b → Set
Triv hself = ⊤
Triv (hsuc p) = ⊥
Triv (hlim n p) = ⊥
Triv (hLim e p) = ⊥

⊞⊲-triv : ∀ {S} {w} (a : HB S) {x y} (p : x ⊲[ w ] y) → Triv p → Triv (⊞-⊲ a p)
⊞⊲-triv a hself t = tt

rdfst-triv : ∀ {W} (lW : LgW₂ W) b (t : D₁ W) → t ≡ n0 → ∀ {w} → Triv (rd-fst lW b t {w})
rdfst-triv lW b .n0 refl = tt

walk-triv : ∀ {ly W₀ V₁} (ac : AccY ly) (zy : NZ ly) (u : Bu ly W₀) (b : H₀) {a : H₀} (P : a ⊲[ proj₁ V₁ ] b)
  (ap : proj₂ W₀ ⊲[ proj₁ V₁ ] a) (lb : LgB b) (bV : b ⊲[ proj₁ V₁ ] proj₂ V₁) (q : proj₁ W₀ ⊲ proj₁ V₁) (lV : LgW₂ V₁)
  (ll : LW ly V₁) (A₀ : Ig ly V₁) (co : D ly V₁) (Y : St V₁) →
  Triv P → ∀ {t m} (T : Tg V₁ t m) → yc (Walk₁ ac zy u b P ap lb bV q lV ll A₀ co Y) T ≡ n0
walk-triv ac zy u b hself ap lb bV q lV ll A₀ co Y tt T = refl
```

**链停在底.**

```agda
stall : ∀ {ly W₀ W} (ac : AccY ly) (zy : NZ ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW₂ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
  Triv (proj₂ q₀) → ∀ n →
  (xz (κc₁ {ly} ac zy u q₀ lW ll A₀ w Y n) ≡ hz) × Triv (av₁z (κc₁ {ly} ac zy u q₀ lW ll A₀ w Y n))
stall ac zy u q₀ lW ll A₀ w Y t zero = refl , t′
  where
  t′ : Triv (⊲ᴮ-tr (proj₂ q₀) hself)
  t′ = t
stall {ly} {W₀} {W} ac zy u q₀ lW ll A₀ w Y t (suc n) =
  trans (cong (rd (proj₁ lW , lv₁ c₀) (xz z₀)) e) (proj₁ ih) ,
  ⊞⊲-triv (proj₂ W) (rd-fst (proj₁ lW , lv₁ c₀) (xz z₀) Δ₁) (rdfst-triv (proj₁ lW , lv₁ c₀) (xz z₀) Δ₁ e)
  where
  z₀ = κc₁ {ly} ac zy u q₀ lW ll A₀ w Y n
  c₀ = toCl lW z₀
  ih = stall ac zy u q₀ lW ll A₀ w Y t n
  Δ₁ : D₁ (proj₁ W , v₁ c₀)
  Δ₁ = yc (κΔ₁ ac zy u q₀ lW ll A₀ c₀) (τ₁ (proj₁ lW , lv₁ c₀))
  e : Δ₁ ≡ n0
  e = walk-triv ac zy u (v₁ c₀) (av₁ c₀) _ _ _ _ _ _ _ _ _ (proj₂ ih) (τ₁ (proj₁ lW , lv₁ c₀))

-- 每一格的输出都是空树 (对一切目标)
stall-out : ∀ {ly W₀ W} (ac : AccY ly) (zy : NZ ly) (u : Bu ly W₀) (q₀ : W₀ ≤ W) (lW : LgW₂ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) →
  Triv (proj₂ q₀) → ∀ n {t m} (T : Tg (proj₁ W , v₁ (toCl lW (κc₁ {ly} ac zy u q₀ lW ll A₀ w Y n))) t m) →
  yc (κΔ₁ ac zy u q₀ lW ll A₀ (toCl lW (κc₁ {ly} ac zy u q₀ lW ll A₀ w Y n))) T ≡ n0
stall-out ac zy u q₀ lW ll A₀ w Y t n T =
  walk-triv ac zy u _ (av₁ (toCl lW (κc₁ ac zy u q₀ lW ll A₀ w Y n))) _ _ _ _ _ _ _ _ _ (proj₂ (stall ac zy u q₀ lW ll A₀ w Y t n)) T
```

**前提可满足.** 节点就在当前世界造的 (`≤rf`), 高度分量是 `hself`.

```agda
sat-stall : ∀ {W} → Triv (proj₂ (≤rf {W}))
sat-stall = tt
```
