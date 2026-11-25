# 新比较的有限测试: `YiDlLost` 那一对保留, 跨支的一对也保留

非验收文件. 有限测试 (`refl`, `tt`) 与编译定理, 无前提. `lostP` 那一对 (目标 `rN`, 源 `pN`, 源层号是 ℕ 极限): 旧的 `cmpw` 折叠, 新的 `cmpz` 保留在槽位 `s` 上, 搬运是 `mv L L` (`kept-at`, 折叠里的结点 `node-kept`); 旧派发保留的根仍在原槽位 (`root-kept′`).
编译定理: `tw 2` 一切位置的层号只含零, 后继, ℕ 极限 (`tw2-sm`), 所以这份搬运与恒等互模拟 (`kept-copy`); R9Same 由 `Shift` 算出的层号相等上, 搬运与 `subst` 互模拟 (`shift-copy`).
反面 (有限测试加 `no-slot`): 目标层没有与源层号相等的槽位时, 跨支的结构对齐仍保留 (`cross-keep`), 层号字面不同. 不陈述折叠输出的值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZipLost where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; fold; Shift; ⌜_⌝)
open import OCF.Lean.YiLamFold using (Lw; ws; wl; nrmk; nrmk-lgl; witU)
open import OCF.Lean.YiDlFold using (cmpw)
open import OCF.Lean.YiDlInst using (V2; rN; ξa)
open import OCF.Lean.YiDlLost using (pN; lostP; LN; Vw; comp) renaming (s to sN)
open import OCF.Lean.YiZipMove
open import OCF.Lean.YiZipSim using (Sm; z; s; l; Sim; mv-sim; mv-subst; up0-sm; lev-sm)
open import OCF.Lean.YiZipWay
open import OCF.Lean.YiZipFold using (cmpz; rootZ; Ψ′)
```

```agda
IsKeep′ : ∀ {m j} → Way′ m j → Set
IsKeep′ (keep′ _ _) = ⊤
IsKeep′ fold′ = ⊥

old-fold : cmpw V2 rN pN ≡ fold
old-fold = lostP

kept : IsKeep′ (cmpz V2 rN pN)
kept = tt

L : LF
L = lev (tw 2) pN

kept-at : cmpz V2 rN pN ≡ keep′ sN (byEq refl ⨾ byMv L L)
kept-at = refl

tw2-sm : ∀ (p : Pre (tw 2)) → Sm (lev (tw 2) p)
tw2-sm (η , _ , r) = lev-sm (up0-sm η) r

kept-copy : ∀ {x y} → Sim L x y → Sim L (run (byEq refl ⨾ byMv L L) x) y
kept-copy = mv-sim (tw2-sm pN)

-- 折叠到目标层 LN 时, pN 上的结点 (分支任意) 落在槽位 s 上
node-kept : ∀ (g : Raw L → Raw (tw 2)) →
  Ψ′ LN V2 (cmpz V2 rN) (G.lc pN g) ≡ G.lc sN (λ η → Ψ′ LN V2 (cmpz V2 rN) (g (mv L L η)))
node-kept g = refl

```

R9Same 的另一对: `LN` 的第 0 分量里的位置经 `Shift` (来自合法性) 搬到第 1 分量, 层号相等由搬运算出.

```agda
unws : ∀ {k} → Lw (suc k) → Lw k
unws (ws V) = V

stOf : ∀ {f : ℕ → LF} → Lw (lim f) → ∀ n → Shift (f n) (f (suc n))
stOf (wl V st) = st

VLN : Lw LN
VLN = unws (Vw (nrmk zero ξa) (nrmk-lgl zero ξa))

s₀ : Pre (comp LN 0)
s₀ = proj₂ sN

s₁ : Pre (comp LN 1)
s₁ = proj₁ (stOf VLN 0 s₀)

shift-eq : lev (comp LN 1) s₁ ≡ lev (comp LN 0) s₀
shift-eq = proj₂ (stOf VLN 0 s₀)

comp-sm : ∀ {a} → Sm a → ∀ n → Sm (comp a n)
comp-sm z n = z
comp-sm (s _) n = z
comp-sm (l sf) n = sf n

shift-copy : ∀ {x y} → Sim (lev (comp LN 1) s₁) x y →
  Sim (lev (comp LN 0) s₀) (mv (lev (comp LN 1) s₁) (lev (comp LN 0) s₀) x) (subst Raw shift-eq y)
shift-copy = mv-subst shift-eq (lev-sm (comp-sm (tw2-sm rN) 1) s₁)
```

旧派发保留的根 (`YiDlInst.root-kept`) 仍保留在同一槽位. 跨支: 目标在第 2 支 (层号 1 的位置), 源在第 3 支 (层号 1); 目标层 1 没有层号 1 的槽位 (`no-slot`), 旧比较折叠, 新比较按结构对齐保留到层号 0 的槽位 (`cross-keep`): 结构对齐不知道两支不同.

```agda
root-kept′ : rootZ (lev (tw 2) rN) zero ⌜_⌝ (witU zero) (cmpz V2 rN) ≡ keep′ (0 , 0 , 0 , inj₂ (inj₁ tt)) (byEq refl)
root-kept′ = refl

q₂ r₃ : Pre (tw 2)
q₂ = G.suc (G.suc G.zero) , tt , inj₁ tt
r₃ = G.suc (G.suc (G.suc G.zero)) , tt , inj₂ (inj₁ tt)

cross-old : cmpw V2 q₂ r₃ ≡ fold
cross-old = refl

cross-keep : cmpz V2 q₂ r₃ ≡ keep′ (inj₁ tt) (byEq refl ⨾ byMv zero (suc zero))
cross-keep = refl

no-slot : (p : Pre (lev (tw 2) q₂)) → lev (lev (tw 2) q₂) p ≡ lev (tw 2) r₃ → ⊥
no-slot (inj₁ _) ()
no-slot (inj₂ ())
```
