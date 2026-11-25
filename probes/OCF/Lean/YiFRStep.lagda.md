# 实际回灌链上的归纳义务
验收文件；每站的真实链给 branch-upper，上一站供给第 0 个参照项 start-match；start0 实填前提。
Step.step 把归纳余项写为 Tail；Tail 整族及 FirstMissing 未填，不计作新增强度或可实填接口。
来源：链从 YiTBRow 定义展开，分支上界复用 YiKSDesc.rowN，两种读回用 YiKCSem/YiKQSuff；参照等式用 YiKDStep。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFRStep where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Data.List using ([]; _∷_)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_; z≼; ≼-trans; ≼-refl; l≼)
open import OCF.Lean.YiFRStations
open import OCF.Lean.YiGIInst
open import OCF.Lean.YiGIEnd using (row-eq)
open import OCF.Lean.YiExSuff
open import OCF.Lean.YiKCSem using (rr≼)
open import OCF.Lean.YiKQSuff using (read≤)
open import OCF.Lean.YiKSDesc using (rowN)
import OCF.Lean.YiKDStep as KD
open ExSuff gradedᵍ domsᵍ using (Keel⁻)

rowω : ∀ n → E.cof (Keel⁻.row keelᴱ (suc n)) ≡ E.cω
rowω zero = refl
rowω (suc n) = subst (λ t → E.cof t ≡ E.cω) (sym (row-eq (suc (suc n)))) (KD.Rows.wT n)

tower-id : ∀ n → KD.Ωn n (E.natT 1) ≡ E.ΩTower n
tower-id zero = refl
tower-id (suc n) = cong E.Ωt (tower-id n)
ref-zero : ∀ n → E.fsn (E.EBOψ (suc n)) 0 ≡ E.EBOψ n
ref-zero zero = refl
ref-zero (suc n) = trans (KD.Rows.rowE n 0) (cong (λ a → E.ψ [] a ∷ []) (tower-id (suc n)))
row-zero : ∀ n → E.fsn (Keel⁻.row keelᴱ (suc n)) 0 ≡ Keel⁻.row keelᴱ n
row-zero n = trans (cong (λ t → E.fsn t 0) (row-eq (suc n))) (trans (ref-zero n) (sym (row-eq n)))
tree-transport : ∀ {a b} (e : a ≡ b) (h : SI.E.HC a) → SI.E.tree h ≼ SI.E.tree (subst SI.E.HC e h)
tree-transport refl h = ≼-refl _

module Step (n : ℕ) where
  ℓ = B.tw (suc n)
  k = B.tw n
  child : B.Tr k → B.L
  child c = k B.⊕ B.↑ k c
  g : B.Tr k → B.Tr ℓ
  g c = proj₁ (O.upz {s = B.sΩ k} {h = child} c (O.Ωt (child c)))
  feed : B.Tr k → B.Tr k
  feed c = proj₁ (TB.ψ ℓ (P.Ok-tw (suc n)) (MT.rbᶻ ℓ) (baseᴱ (suc n)) k (P.ink P.self)
    (baseᴱ (suc n) k (P.ink P.self)) (g c))
  out : B.Tr k → O.Tr⁺ B.zero
  out c = TB.ψ ℓ (P.Ok-tw (suc n)) (MT.rbᶻ ℓ) (baseᴱ (suc n)) B.zero (P.z≤ ℓ) (betaᴱ (suc n)) (g c)
  chain : ℕ → B.Tr k
  chain = O.iter feed B.zero
  branch-upper : ∀ m → K.readRW (proj₁ (out (chain m))) ≼ K.readRW (Keel⁻.twc keelᴱ (suc n))
  branch-upper m = ≼-trans (rowN (F.kp ℓ (P.Ok-tw (suc n)) (inj₁ (inj₁ tt)) (P.z≤ ℓ)) out feed m (read≤ (proj₁ (out (chain m)))))
    (rr≼ (Keel⁻.twc keelᴱ (suc n)))
  Match : Set
  Match = (m : ℕ) → Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ (suc n)) m))
    → SI.E.tree h ≼ K.readRW (proj₁ (out (chain q)))
  match→station : Match → Kᴱ (suc n)
  match→station mt (SI.E.h0 _) = z≼
  match→station mt (SI.E.h1 e _) = ⊥-elim (bad (trans (sym e) (rowω n)))
    where
    bad : E.c1 ≡ E.cω → ⊥
    bad ()
  match→station mt (SI.E.hω _ hs) = l≼ (λ m → ≼-trans (proj₂ (mt m) (hs m)) (branch-upper (proj₁ (mt m))))

  prior-upper : K.readRW (Keel⁻.twc keelᴱ n) ≼ K.readRW (proj₁ (out (chain 0)))
  prior-upper = subst (λ x → K.readRW x ≼ K.readRW (proj₁ (out (chain 0)))) (sym (branch-form n))
    (K.◃→≼ (TB.mono ℓ (P.Ok-tw (suc n)) (MT.rbᶻ ℓ) (baseᴱ (suc n)) B.zero (P.z≤ ℓ) (betaᴱ (suc n))
      (B.◃u B.zero B.zero (proj₁ (O.Ωt k)) (proj₂ (O.Ωt k)))))
  start-match : Kᴱ n → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ (suc n)) 0))
    → SI.E.tree h ≼ K.readRW (proj₁ (out (chain 0)))
  start-match kn h = ≼-trans (tree-transport (row-zero n) h)
    (≼-trans (kn (subst SI.E.HC (row-zero n) h)) prior-upper)
  Tail : Set
  Tail = (m : ℕ) → Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ (suc n)) (suc m)))
    → SI.E.tree h ≼ K.readRW (proj₁ (out (chain q)))
  step : Kᴱ n → Tail → Kᴱ (suc n)
  step kn tl = match→station λ { zero → 0 , start-match kn ; (suc m) → tl m }

start0 : (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 1) 0))
  → SI.E.tree h ≼ K.readRW (proj₁ (Step.out 0 (Step.chain 0 0)))
start0 = Step.start-match 0 k0

Remaining : Set
Remaining = ∀ n → Kᴱ n → Step.Tail n

FirstMissing : Set
FirstMissing = Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → SI.E.tree h ≼ K.readRW (proj₁ (Step.out 2 (Step.chain 2 q)))
```
