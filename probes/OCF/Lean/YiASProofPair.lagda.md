# 不同步引理 (构造一路): 最小实例里的对不在关系里; 第 2 层余尾的一例成立

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. (一) 余尾为 Ω_{κ+1} 的记号项只对着 "一阶位置可达处有槽位层恰为 κ 的结点" 的树 (`Slot.inv`, 比 `YiAbsGFinInv.invᶠ` 多记槽位层); 所以 (Ω₁, 第 n+2 层 Ω 树) 与 (Ω₂, 第 3 层 Ω 树) 都没有 `M` 关系 (`no-Ω₁`, `no-Ω₂`; n = 1 的 `no-Ω₁` 与 `YiASNeg.¬M₀` 重合, 这里要一般的 n).
> (二) `M` 上读法的零、后继两条与 `Leaf` 不能同时成立 (`no-leaf`). (三) `async₀⁺`: 参照 ψ₂(P + Ω₂) (余尾下标 1 低于目标 2, 保留) 对着第 3 层 Ω 树折到第 2 层的输出 (对角) 成立, 虽然这一对不在 `M` 里.
> `Async₀`, `Async₀ᶜ`, `Pair₀` 的否定在 [YiASNeg](YiASNeg.lagda.md), 这里不重证; (三) 不与它们矛盾 (参照不同). 接口见 [YiASIface](YiASIface.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiASProofPair where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt)
open import OCF.Lean.YiLegFold
import OCF.Align.EboLeanDef as E
open E using (cof; c0; c1; cω; cΩ; natT)
open import OCF.Lean.YiMEBase hiding (Rt)
open import OCF.Lean.YiANFam
open import OCF.Lean.YiANKp using (vch)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsGIface using (Graded; module Laws)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGFin using (blkᶠ; foldᶠ; rowsᶠ; module Ind)
open import OCF.Lean.YiAbsGFinInv using (cof++ne)
open import OCF.Lean.YiASIface
```

## 带槽位层的反演

`H n o`: o 在某个槽位层为 κ 的结点之上, 或在孩子满足 `H` 的嵌入之上. `clean n o`: 从 o 沿第一位置序往下 (含孩子) 碰不到这样的结点; 它对第一位置序向下封闭.

```agda
module Slot (κ : E.T) where

  data H : (n : ℕ) → Tr (fin n) → Set where
    hn : ∀ {n} (p : Pos (fin (suc n))) (g : Br (fin (suc n)) p → Tr (fin (suc n))) → Nw n p κ → H (suc n) (Ω p g)
    hw : ∀ {n x x′} → H n x → fin n ⊢ x ◃ x′ → H n x′
    hc : ∀ {n x y e} → H n y → H (suc n) (up x tt y e)

  private
    no0 : ∀ {c} → c ≡ c0 → c ≡ cΩ κ → ⊥
    no0 refl ()
    no1 : ∀ {c} → c ≡ c1 → c ≡ cΩ κ → ⊥
    no1 refl ()
    noω : ∀ {c} → c ≡ cω → c ≡ cΩ κ → ⊥
    noω refl ()
    cΩ-inj : ∀ {a b} → cΩ a ≡ cΩ b → a ≡ b
    cΩ-inj refl = refl

  invU : ∀ n t s (x : Tr (fin (suc n))) (y : Tr (fin n)) (e : fin n ⊢ zero ◃ y)
       → (cof t ≡ cΩ κ → H (suc n) x) → (cof s ≡ cΩ κ → H n y) → cof (t ++ s) ≡ cΩ κ → H (suc n) (up x tt y e)
  invU n t []       x y e qx qy w = hw (qx (subst (λ r → cof r ≡ cΩ κ) (++-identityʳ t) w)) (◃u x tt y e)
  invU n t (a ∷ as) x y e qx qy w = hc (qy (trans (sym (cof++ne t a as)) w))

  inv : ∀ n {s o} → M n s o → cof s ≡ cΩ κ → H n o
  inv zero    = Ind.ind (λ s o → cof s ≡ cΩ κ → H zero o)
    (λ w → ⊥-elim (no0 refl w)) (λ e _ _ w → ⊥-elim (no1 e w)) (λ e _ _ w → ⊥-elim (noω e w))
    (λ ()) (λ ()) (λ _ q d w → hw (q w) d)
  inv (suc n) = Ind.ind (λ s o → cof s ≡ cΩ κ → H (suc n) o)
    (λ w → ⊥-elim (no0 refl w)) (λ e _ _ w → ⊥-elim (no1 e w)) (λ e _ _ w → ⊥-elim (noω e w))
    (λ p g e nu _ _ w → hn p g (trans (sym (cΩ-inj (trans (sym e) w))) nu))
    (λ {t} {s} {x} c y e _ q ch w → invU n t s x y e q (inv n ch) w)
    (λ _ q d w → hw (q w) d)

  clean : (n : ℕ) → Tr (fin n) → Set
  clean n       zero         = ⊤
  clean n       (suc x)      = clean n x
  clean n       (lim f a)    = ∀ k → clean n (f k)
  clean (suc n) (Ω p g)      = (Nw n p κ → ⊥) × clean (suc n) (g (br0 (fin (suc n)) p))
  clean (suc n) (up x c y e) = clean (suc n) x × clean n y
  clean zero    (Ω () g)
  clean zero    (up x () y e)

  clean↓ : ∀ n {x x′} → fin n ⊢ x ◃ x′ → clean n x′ → clean n x
  clean↓ n       ◃s             cl = cl
  clean↓ n       (◃l k)         cl = cl k
  clean↓ (suc n) ◃w             cl = proj₂ cl
  clean↓ (suc n) (◃u x c y e)   cl = proj₁ cl
  clean↓ (suc n) (◃c x c d)     cl = proj₁ cl , clean↓ n d (proj₂ cl)
  clean↓ n       (◃t d e)       cl = clean↓ n d (clean↓ n e cl)
  clean↓ zero    (◃w {p = ()})
  clean↓ zero    (◃u x () y e)
  clean↓ zero    (◃c x () d)

  clean→¬H : ∀ {n o} → H n o → clean n o → ⊥
  clean→¬H (hn p g nu) cl = proj₁ cl nu
  clean→¬H (hw h d)    cl = clean→¬H h (clean↓ _ d cl)
  clean→¬H (hc h)      cl = clean→¬H h (proj₂ cl)

  no-rel : ∀ n {s o} → cof s ≡ cΩ κ → clean n o → M n s o → ⊥
  no-rel n e cl m = clean→¬H (inv n m e) cl
```

## 最小实例里的对

Ω 树的头部槽位层是层号减一, 第一分支是 `up zero tt 1`. 所以 Ω₁ (余尾下标 0) 与第 n+2 层 Ω 树, Ω₂ (余尾下标 1) 与第 3 层 Ω 树都没有关系.

```agda
no-Ω₁ : ∀ n → M (suc (suc n)) (Ωᴺ 1) (Ωt (fin (suc (suc n)))) → ⊥
no-Ω₁ n = Slot.no-rel [] (suc (suc n)) (cofΩ 0) ((λ ()) , tt , tt)

no-Ω₂ : M 3 (Ωᴺ 2) (Ωt (fin 3)) → ⊥
no-Ω₂ = Slot.no-rel (natT 1) 3 (cofΩ 1) ((λ ()) , tt , tt)
```

## 读法的松弛与 `Leaf`

关系取 `M`, 读法 `Rd` 任取: 零 (`Rd0`), 后继 (`RdS`) 两条给出 `Rd 2 (natT 1)`, `Leaf` 就要 (Ω₁, 第 2 层 Ω 树) 有关系. 两条读法单独可满足 (`Rd n ν` 取 "ν 是不超过 n 的自然数"), `Leaf` 单独可满足 (`YiAbsGFin.leafᶠ`, `Rd` 取字面相等).

```agda
gradedᴿ : (ℕ → E.T → Set) → Graded blkᶠ foldᶠ rowsᶠ refᴱ 𝕍
gradedᴿ Rd = record gradedᴬ { Rd = Rd }

no-leaf : (Rd : ℕ → E.T → Set) → Laws.Rd0 (gradedᴿ Rd) domsᴬ → Laws.RdS (gradedᴿ Rd) domsᴬ
        → Laws.Leaf (gradedᴿ Rd) domsᴬ → ⊥
no-leaf Rd r0 rS lf = no-Ω₁ 0 (lf {ℓ = 2} {ν = natT 1} (rS {ℓ = 1} {ν = natT 1} refl (r0 {ℓ = 1} {ν = []} refl)))
```

## 第 2 层余尾的一例

参照 ψ₂(P + Ω₂): 余尾下标 1 低于目标 2, 记号一侧保留. 树一侧第 3 层 Ω 树的槽位层是 2, 折到第 2 层取回灌链的部分和极限. 链的第 1 项在底的第 2 层分量之上, 从而在第 2 层 Ω 树之上; 部分和极限的第 1 项在 "第 2 层 Ω 树折到自身" 之上, 后者由 `Self.PF` 对着 ψ₂(P + Ω₂) (同步的保留). 只用到 `GBᶠ` 的 `gΩ` 在第 2 层的一项.

```agda
async₀⁺ : (ε : Ev (fin 3)) (ρ : Rt (fin 3)) (B : Base (fin 3)) (P : E.T) → GBᶠ 2 B P
        → (β : Tr (fin 2)) (nβ : fin 2 ⊢ zero ◃ β) → M 2 (ψᴺ 2 P) β
        → M 2 (ψᴺ 2 (P ++ Ωᴺ 2)) (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ (Ωt (fin 3)))
async₀⁺ ε ρ B P gb β nβ hβ =
  cumN 2 (λ m → ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ (g (vch 2 ε ρ B (inj₁ tt) g m)))
         (λ m → nzs (fin 3) ε ρ B (fin 2) (ins self) β nβ (g (vch 2 ε ρ B (inj₁ tt) g m))) 1
    (mw (mw (Self.PF 1 ε ρ (dS (fin 2) ε ρ B zero) β nβ hβ (Mβ 1))
            (Self.monoF 1 ε ρ (dS (fin 2) ε ρ B zero) β nβ (⊴-◃ (gΩ gb s0) (◃l zero))))
        (◃l zero))
  where
  g : Tr (fin 2) → Tr (fin 3)
  g c = up zero tt (suc c) (z◃s c)
```
