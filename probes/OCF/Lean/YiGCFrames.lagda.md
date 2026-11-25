# 沿帧状态的底界与标准底保持
验收文件；NoΩ 源层上的状态单调、底界与 OKst 保持。
来源：YiLSFold.nxtβ/ok-nxt；状态与执行等式复用 YiFPFrames，折叠底界复用 YiTBFam.ψ-⊵。
不涉及 EboLean 标签读回；供 YiGCFold 的 Level 主引理使用。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCFrames where
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.YiRWBlock renaming (L to LF)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiNRHit using (NoΩ; chN)
open import OCF.Lean.YiFPFrames
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃; ⊴-◃)
open import OCF.Lean.YiKCStep using (OKB; ⊴-trans)
open import OCF.Lean.YiTBFam using (ψ-⊵)
import OCF.Lean.YiTBRow as TB

stβ : ∀ {j a} → St j a → Tr j
stβ (fo C w β) = proj₁ β
stβ (uf d β) = proj₁ β
run-mono : ∀ {j a} (st : St j a) {x y} → a ⊢ x ◃ y → j ⊢ run st x ◃ run st y
run-mono {j} {a} (fo (o , r , B) w β) e = TB.mono a o r B j w β e
run-mono {j} {a} (uf d b) e = Upm a d b e
run-⊵ : ∀ {j a} (st : St j a) x → stβ st ⊴ run st x
run-⊵ (fo (o , r , B) w β) x = ψ-⊵ _ o r B _ w β x
run-⊵ {a = a} (uf d b) x with zl x
... | inj₁ refl = ⊴r
... | inj₂ e = ⊴◃ (Upm a d b e)

mutual
  nxtβ : ∀ {a} (ns : NoΩ a) {j} (st : St j a) x (c : CH a) → run st x ⊴ stβ (nxt ns st x c)
  nxtβ {a = zero} ns st x ()
  nxtβ {nd s h} ns (fo C self β) x c = ⊴r
  nxtβ {nd s h} ns (fo C (inu ws) β) x c = ⊴r
  nxtβ {nd sS h} ns (fo C (inc tt w) β) x tt = ⊴r
  nxtβ {nd sL g} ns (fo C (inc n w) β) x m = nxtWβ ns C x m n (way g (proj₁ (proj₁ C)) m n) w _
  nxtβ {nd (sΩ k) h} () (fo C (inc c w) β) x c′
  nxtβ {nd (sΩ k) h} () (fo C (ink w) β) x c
  nxtβ {nd s h} ns (uf d b) x c = ⊴r
  nxtWβ : ∀ {g} (ns : ∀ n → NoΩ (g n)) (C : Cfg (nd sL g)) x m n
    (W : (g m ≤ g n) ⊎ (g n ≤ g m)) {j} (w : j ≤ g n) β → proj₁ β ⊴ stβ (nxtW ns C x m n W w β)
  nxtWβ ns C x m n (inj₁ v) w β = thruβ (ns n) v (fo (child C x n) w β)
  nxtWβ ns C x m n (inj₂ v) w β = ⊴r
  thruβ : ∀ {a} (ns : NoΩ a) {k} (v : k ≤ a) {j} (st : St j a) → stβ st ⊴ stβ (thru ns v st)
  thruβ ns self st = ⊴r
  thruβ {nd s h} ns (inc c v) st = ⊴-trans (⊴-trans (run-⊵ st zero) (nxtβ ns st zero c)) (thruβ (chN s h ns c) v (nxt ns st zero c))
  thruβ {nd s h} ns (inu vs) st = ⊴-trans (⊴-trans (run-⊵ st zero) (nxtβ ns st zero (c₀ s))) (thruβ (chN s h ns (c₀ s)) (vs (c₀ s)) (nxt ns st zero (c₀ s)))
  thruβ {nd (sΩ k) h} () (ink v) st
nxt-⊵ : ∀ {a} (ns : NoΩ a) {j} (st : St j a) x c y → run st x ⊴ run (nxt ns st x c) y
nxt-⊵ ns st x c y = ⊴-trans (nxtβ ns st x c) (run-⊵ (nxt ns st x c) y)

OKst : ∀ {j a} → St j a → Set
OKst (fo (o , r , B) w β) = OKB B
OKst (uf d b) = ⊤
ok-child : ∀ {s h} (C : Cfg (nd s h)) → OKB (proj₂ (proj₂ C)) → ∀ x c → OKB (proj₂ (proj₂ (child C x c)))
ok-child {s} {h} (o , r , B) ok x c i u = ⊴-trans (ok i (inc c u)) (ψ-⊵ (nd s h) o r B i (inc c u) (B i (inc c u)) x)
mutual
  ok-nxt : ∀ {a} (ns : NoΩ a) {j} (st : St j a) x c → OKst st → OKst (nxt ns st x c)
  ok-nxt {a = zero} ns st x () ok
  ok-nxt {nd s h} ns (fo C self β) x c ok = tt
  ok-nxt {nd s h} ns (fo C (inu ws) β) x c ok = ok-child C ok x c
  ok-nxt {nd sS h} ns (fo C (inc tt v) β) x tt ok = ok-child C ok x tt
  ok-nxt {nd sL g} ns (fo C (inc n v) β) x m ok = ok-nxtW ns C ok x m n (way g (proj₁ (proj₁ C)) m n) v _
  ok-nxt {nd (sΩ k) h} () (fo C (inc c v) β) x c′ ok
  ok-nxt {nd (sΩ k) h} () (fo C (ink v) β) x c ok
  ok-nxt {nd s h} ns (uf d b) x c ok = tt
  ok-nxtW : ∀ {g} (ns : ∀ n → NoΩ (g n)) (C : Cfg (nd sL g)) → OKB (proj₂ (proj₂ C)) → ∀ x m n
    (W : (g m ≤ g n) ⊎ (g n ≤ g m)) {j} (w : j ≤ g n) β → OKst (nxtW ns C x m n W w β)
  ok-nxtW ns C ok x m n (inj₁ v) w β = ok-thru (ns n) v (fo (child C x n) w β) (ok-child C ok x n)
  ok-nxtW ns C ok x m n (inj₂ v) w β = ok-child C ok x m
  ok-thru : ∀ {a} (ns : NoΩ a) {k} (v : k ≤ a) {j} (st : St j a) → OKst st → OKst (thru ns v st)
  ok-thru ns self st ok = ok
  ok-thru {nd s h} ns (inc c v) st ok = ok-thru (chN s h ns c) v (nxt ns st zero c) (ok-nxt ns st zero c ok)
  ok-thru {nd s h} ns (inu vs) st ok = ok-thru (chN s h ns (c₀ s)) (vs (c₀ s)) (nxt ns st zero (c₀ s)) (ok-nxt ns st zero (c₀ s) ok)
  ok-thru {nd (sΩ k) h} () (ink v) st ok
ok-stOf : ∀ {a j} (ns : NoΩ a) (st : St j a) → OKst st → ∀ {b} {d : Dc a b} (Γ : Ctx a d) → OKst (stOf ns st Γ)
ok-stOf ns st ok [] = ok
ok-stOf ns st ok (fr x c Γ) = ok-stOf (kidN ns c) (nxt ns st x c) (ok-nxt ns st x c ok) Γ
```
