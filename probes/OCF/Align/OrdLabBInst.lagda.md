# 主线直接标: `HtB` 上的前缀实例与它的边界

> **验收文件, 读记号.** 结论写在 [OrdLab](OrdLab.lagda.md). 标签类 `OrdLabB*` 对高度结构 `HtB` 成立 (`label-cert`, 对一切 `HtB`, `PxB`). 这里回答它能贴到哪里:
>
> - `Px-ω`: 码 `ωᶜ` 有前缀结构, 直接从 `Px∞` 经位置到高度的映射给出. 所以 `label-ω` 是 `LadderOrdTree (HB ωᶜ)` 上的标签, 不经 `agree∞`.
> - `no-PxB`: 对一切 `HtB`: 若 $m$ 是链行, $F_0$ 是链行, $F_1$ 是闭包行, 则**没有任何**前缀结构, 不管读法是什么. `no-PxB-M₂`: 码 `ω·ᶜ 1` 是这种形状, 没有 `PxB`.
>
> 证明: `Row₀` 的链行要 $X[0]=0$ 且 $X$ 是 $\omega$-共尾. 这样的项只能是 $\psi_v(b+1)$ (`rule4`), 所以 $X[1]=y$, $X[2]=y+y$. 而 $X[1]$ 是链行要 $\omega$-共尾, $y+y$ 的共尾度与 $y$ 相同, $X[2]$ 是闭包行要 $\Omega$-共尾. 矛盾.
>
> 这只否定 "用 `PxB`/`Row₀` 的逐项一致" 这条路线在这种码上的做法, 不否定别的读法 (比如 [OrdLabRead](OrdLabRead.lagda.md) 的除第 0 项外一致), 也不否定树本身的强度.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabBInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (_∷_; []; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import OCF.Align.EBO as E
open E using (T; PT; natT; Ωt; cof; fsn; c0; c1; cω; cΩ) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (cof-ne; fs-rep)
open import OCF.Align.LadderOrdBase using (HtB; View; base; clos; chain)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ωᶜ)
open import OCF.Align.LadderOrdInst using (M₂)
open import OCF.Align.LadderLabZStandardOmega using (Ω₁; Ωᵐ; ψ¹; cof-Ωᵐ[]; fsT-Ωᵐ; fsn-ψ¹)
open import OCF.Align.LadderNFTree using (z<s; s<s) renaming (_<ᴸ_ to _N<ᴸ_)
open import OCF.Align.LadderInfTop using (HS∞; fin; ∞; inf; _<∞_) renaming (H to H∞)
open import OCF.Align.OrdLabBase using (PxS)
open import OCF.Align.OrdLabInst using (Px∞)
open import OCF.Align.OrdLabBBase
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.LadderLabZStandardOmega using (NF₁)
open import OCF.Align.OrdLabZGoodLBase using (Lab→Ctbl)
open import OCF.Align.OrdLabZUniform3Base using (ψ₀ᵗ)
open import OCF.Align.OrdLabNFOmega using (NF-Ωᵐ)
open import OCF.Align.OrdLabNFTop using (NF-ψ)
open import OCF.Align.OrdLabAccept using (B∞)
import OCF.Align.OrdLabBTop
import OCF.Align.LadderOrdMain
```

## §1 记号: 第 0 项是 0 的 $\omega$-共尾项

```agda
rule4 : ∀ X → cof X ≡ cω → fsn X 0 ≡ [] → Σ PT λ y → (fsn X 1 ≡ y ∷ []) × (fsn X 2 ≡ y ∷ y ∷ [])
rule4 [] () f
rule4 (x ∷ y ∷ ys) c ()
rule4 (ψᵗ [] [] ∷ []) () f
rule4 (ψᵗ (w ∷ ws) [] ∷ []) c f = ⊥-elim (go (cof (w ∷ ws)) refl c (trans (sym (E.fsn0-eq w ws 0 refl)) f))
  where
  go : ∀ k (ue : cof (w ∷ ws) ≡ k) → E.cofψ0 (w ∷ ws) k ≡ cω → E.trm (E.fsn↓0 w ws k ue 0) ≡ [] → ⊥
  go c0 ue c′ f′ = cof-ne w ws ue
  go c1 ue () f′
  go cω ue c′ ()
  go (cΩ μ) ue () f′
rule4 (ψᵗ u (y ∷ ys) ∷ []) c f = go (cof (y ∷ ys)) refl c
  where
  go : ∀ k (be : cof (y ∷ ys) ≡ k) → E.cofA u k ≡ cω → Σ PT λ z → (fsn (ψᵗ u (y ∷ ys) ∷ []) 1 ≡ z ∷ []) × (fsn (ψᵗ u (y ∷ ys) ∷ []) 2 ≡ z ∷ z ∷ [])
  go c0 be c′ = ⊥-elim (cof-ne y ys be)
  go c1 be c′ = ψᵗ u (E.pred (y ∷ ys)) , fs-rep u y ys be 1 , fs-rep u y ys be 2
  go cω be c′ with trans (sym (E.fsn₊-eq u y ys 0 be)) f
  ... | ()
  go (cΩ ν) be c′ = ⊥-elim (gc (E.cmpᵀ (E.sucT ν) u) (trans (sym (E.fsn₊-eq u y ys 0 be)) f))
    where
    gc : ∀ m → E.trm (E.fsn↓c u y ys ν be m 0) ≡ [] → ⊥
    gc E.lt ()
    gc E.eq ()
    gc E.gt ()
```

## §2 否定

```agda
module NoPx (𝕊 : HtB) (𝕏 : PxB 𝕊) where
  open HtB 𝕊
  open PxB 𝕏

  rowL→ : ∀ {m F qf} → Row₀ 𝕊 P m (chain F qf) → (cof (P m []) ≡ cω) × (fsn (P m []) 0 ≡ []) × (∀ i → fsn (P m []) (suc i) ≡ P (F i) [])
  rowL→ (rl F qs c f0 fs) = c , f0 , fs

  rowC→ : ∀ {m n} {r : n <ᴸ m} → Row₀ 𝕊 P m (clos r) → cof (P m []) ≡ cΩ []
  rowC→ (rc q c f) = c

  no-PxB : ∀ {m F qf G qg n} {r : n <ᴸ F 1} → view m ≡ chain F qf → view (F 0) ≡ chain G qg → view (F 1) ≡ clos r → ⊥
  no-PxB {m} {F} {qf} {G} {qg} {n} {r} cm c₀ c₁ = cont (trans (sym c₀′) c₁′)
    where
    Rm = rowL→ (subst (Row₀ 𝕊 P m) cm (P-row m))
    fs = proj₂ (proj₂ Rm)
    Y = rule4 (P m []) (proj₁ Rm) (proj₁ (proj₂ Rm))
    y = proj₁ Y
    c₀′ : cof (y ∷ []) ≡ cω
    c₀′ = subst (λ z → cof z ≡ cω) (trans (sym (fs 0)) (proj₁ (proj₂ Y))) (proj₁ (rowL→ (subst (Row₀ 𝕊 P (F 0)) c₀ (P-row (F 0)))))
    c₁′ : cof (y ∷ y ∷ []) ≡ cΩ []
    c₁′ = subst (λ z → cof z ≡ cΩ []) (trans (sym (fs 1)) (proj₂ (proj₂ Y))) (rowC→ (subst (Row₀ 𝕊 P (F 1)) c₁ (P-row (F 1))))
    cont : cω ≡ cΩ [] → ⊥
    cont ()

-- 码 ω·ᶜ 1 的顶: F 0 是 ω, F 1 是 ω+1
no-PxB-M₂ : PxB (HB M₂) → ⊥
no-PxB-M₂ 𝕏 = NoPx.no-PxB (HB M₂) 𝕏 {end} {λ i → low (blk i end)} {λ i → tt} {λ i → low (blk 0 (low (blk i end)))} {λ i → tt} {low (blk 0 end)} {tt} refl refl refl
```

## §3 码 `ωᶜ` 的实例

位置到高度的映射: `Px∞` 经它搬过来. `no-PxB` 的前提在这里不成立, 所以它不空: `PxB` 是可以有的.

```agda
d : Pos (cs ωᶜ) → H∞
d end = ∞
d (low (blk n end)) = fin n
d (low (blk n (low ())))

ltBℕ : ∀ j k → ltB (λ _ → cz) j k end end → j N<ᴸ k
ltBℕ zero (suc k) x = z<s k
ltBℕ (suc j) (suc k) x = s<s (ltBℕ j k x)

d< : ∀ p q → p <ᴾ q → d p <∞ d q
d< (low (blk j end)) end x = inf j
d< (low (blk j end)) (low (blk k end)) x = fin (ltBℕ j k x)
d< (low (blk j end)) (low (blk k (low ()))) x
d< (low (blk j (low ()))) q x

Pω : Pos (cs ωᶜ) → T → T
Pω m = PxS.P Px∞ (d m)

rowω : ∀ m → Row₀ (HB ωᶜ) Pω m (HtB.view (HB ωᶜ) m)
rowω end = rl _ _ refl (fsn-ψ¹ 0) (λ i → fsn-ψ¹ (suc i))
rowω (low (blk zero end)) = rb refl
rowω (low (blk (suc j) end)) = rc _ (cof-Ωᵐ[] (suc j)) (fsT-Ωᵐ (suc j))
rowω (low (blk j (low ())))

Px-ω : PxB (HB ωᶜ)
Px-ω = record
  { P = Pω
  ; P-cof = λ m → PxS.P-cof Px∞ (d m)
  ; P-pred = λ m → PxS.P-pred Px∞ (d m)
  ; P-fsn = λ m → PxS.P-fsn Px∞ (d m)
  ; P-tail = λ m → PxS.P-tail Px∞ (d m)
  ; P-occ = λ m → PxS.P-occ Px∞ (d m)
  ; P-lt = λ m → PxS.P-lt Px∞ (d m)
  ; P-gt = λ m → PxS.P-gt Px∞ (d m)
  ; P-cmp≡ = λ m → PxS.P-cmp≡ Px∞ (d m)
  ; P-cmp-lt = λ {n} {H} {ν} τ q I → PxS.P-cmp-lt Px∞ {d n} {d H} {ν} τ (d< n H q) I
  ; P-cmp-gt = λ {n} {H} ν {τ} q I → PxS.P-cmp-gt Px∞ {d n} {d H} ν {τ} (d< H n q) I
  ; P-row = rowω
  }
```

## §4 直接贴在 `LadderOrdTree` 上

不经 `agree∞`. 与 [OrdLabAccept](OrdLabAccept.lagda.md) 的 `ord-∞`, `ord-fin∞` 同陈述, 经 `Lab-uniq` 自然一致.

```agda
module Lω = OCF.Align.OrdLabBTop (HB ωᶜ) Px-ω
module Gω = OCF.Align.LadderOrdMain (HB ωᶜ)

label-ω : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ B∞ → ∀ {α} → α ≅ᴵ toLevel Y hY →
          ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (Gω.GᴺTᵠ end α ev p)) (ψ₀ᵗ (Ωt (ψ¹ ∷ θ)))
label-ω Y hY lY nθ pm e ev p = Lω.label-cert end Y hY lY nθ (NF-ψ 0 nθ (Lab→Ctbl lY nθ) pm) e ev p

label-ωfin : ∀ m {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → θ <ᵗ ψ₀ᵗ (Ωt (Ω₁ ∷ Ω₁ ∷ Ωᵐ m [])) → ∀ {α} → α ≅ᴵ toLevel Y hY →
             ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (Gω.GᴺTᵠ (low (blk m end)) α ev p)) (ψ₀ᵗ (Ωt (Ω₁ ∷ Ωᵐ m θ)))
label-ωfin m Y hY lY nθ pm e ev p = Lω.label-cert (low (blk m end)) Y hY lY nθ (NF-Ωᵐ m nθ (Lab→Ctbl lY nθ) pm) e ev p
```
