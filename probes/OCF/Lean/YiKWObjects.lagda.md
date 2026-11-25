# 实际 child-feed 的封装与 Ω 截段规格
验收文件；编译定理：包装与原 child-feed 相等，指定截段的头为 Ω，并给出全部分支。
不声称原名 BranchNeed 到 NextSlot 的接线或第 1 项值下界；该接线工程仍未走通。
来源：YiBVRows.Node.row 只在 End 实例化；路径分解使用 YiKWRows，实际对象只读 YiC0Next。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKWObjects where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiC0Local as C
import OCF.Lean.YiC0Next as N
import OCF.Lean.YiC1Slot as S
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiBVRows as V
import OCF.Lean.YiKWRows as R
import OCF.Lean.YiKWKeep as KV
fallback : R.Lim
fallback = R.limctx (λ _ → K.one) ((λ _ → P.self) , (λ _ → tt , λ _ → tt))
  (tt , λ _ → MT.rbᶻ K.one) (F.B₀ (B.nd B.sL (λ _ → K.one))) (λ _ → P.self) (O.Ωt K.one)
asLim : R.Ctx → R.Lim
asLim (R.ctx (B.nd B.sL g) o r b (P.inu w) beta) = R.limctx g o r b w beta
asLim _ = fallback
fallbackS : R.Suc
fallbackS = R.succtx (λ _ → K.one) (tt , (λ _ → tt , λ _ → tt))
  (tt , λ _ → MT.rbᶻ K.one) (F.B₀ (B.nd B.sS (λ _ → K.one))) (λ _ → P.self) (O.Ωt K.one)
asSuc : R.Ctx → R.Suc
asSuc (R.ctx (B.nd B.sS h) o r b (P.inu w) beta) = R.succtx h o r b w beta
asSuc _ = fallbackS
record Omega : Set where
  constructor omgctx
  field
    h : B.Tr B.zero → B.L
    okay : P.Ok (B.nd (B.sΩ B.zero) h)
    table : TB.Rb (B.nd (B.sΩ B.zero) h)
    base : F.Base (B.nd (B.sΩ B.zero) h)
    lower : ∀ d → P._≤_ K.one (h d)
    beta : O.Tr⁺ K.one
packΩ : Omega → R.Ctx
packΩ (omgctx h o r b w beta) = R.ctx (B.nd (B.sΩ B.zero) h) o r b (P.inu w) beta
fallbackΩ : Omega
fallbackΩ = omgctx (λ _ → K.one) ((tt , (λ _ → P.z≤ K.one)) , (λ _ → tt , λ _ → tt))
  (TB.rbS-no (B.sΩ B.zero) (λ _ → K.one) , λ _ → MT.rbᶻ K.one)
  (F.B₀ (B.nd (B.sΩ B.zero) (λ _ → K.one))) (λ _ → P.self) (O.Ωt K.one)
asOmega : R.Ctx → Omega
asOmega (R.ctx (B.nd (B.sΩ B.zero) h) o r b (P.inu w) beta) = omgctx h o r b w beta
asOmega _ = fallbackΩ
opaque
  unfolding C.c₁ U.Inner.feed U.Inner.g
  -- perf: S-1/C-10，出生处封装原折叠，定义等式单独导出。
  child-feed : O.Tr⁺ K.one
  child-feed = N.child-feed
  child-feed-eq : child-feed ≡ N.child-feed
  child-feed-eq = refl
  c0 : R.Ctx
  c0 = R.ctx C.ℓ₁ (proj₂ U.o₂ C.c₁) (MT.rbᶻ C.ℓ₁) (F.B₀ C.ℓ₁) N.w₁ (O.Ωt K.one)
  original : proj₁ child-feed ≡ R.value c0
  original = refl
  s0 : R.Suc
  s0 = asSuc c0
  e0 : c0 ≡ R.packS s0
  e0 = refl
  std : R.Suc.base s0 (R.Suc.h s0 tt) (P.inc tt P.self) ≡ O.Ωt (R.Suc.h s0 tt)
  std = refl
  c1 : R.Ctx
  c1 = R.downS s0
  l1 : R.Lim
  l1 = asLim c1
  e1 : R.downS s0 ≡ R.pack l1
  e1 = refl
  c2 : R.Ctx
  c2 = R.down0 l1
  l2 : R.Lim
  l2 = asLim c2
  e2 : R.down0 l1 ≡ R.pack l2
  e2 = refl
  c3 : R.Ctx
  c3 = R.down0 l2
  omega : Omega
  omega = asOmega c3
  e3 : R.down0 l2 ≡ packΩ omega
  e3 = refl

-- perf: C-9，Ω 行在变量上证明，仅在这里实例化。
module End = V.Node (Omega.h omega) (Omega.okay omega) (Omega.table omega)
  (Omega.base omega) (Omega.lower omega) (Omega.beta omega)
opaque
  unfolding omega c3 l2 c2 l1 c1 s0 c0 C.c₁ U.Inner.feed U.Inner.g
  -- perf: C-9，只检查保留判定的外层，换型函数按原值保留。
  keep : KV.Keep
  keep = End.keep
  keep-eq : keep ≡ End.keep
  keep-eq = refl
  keep-good : KV.Good keep
  keep-good = tt
pre : B.Tr K.one
pre = proj₁ (O.next⁺ (R.Suc.beta s0))
opaque
  branches : B.Tr B.zero → B.Tr K.one
  branches d = pre O.+ proj₁ (End.child-out (KV.cv keep d))
  branches-eq : ∀ d → branches d ≡ pre O.+ proj₁ (End.child-out (KV.cv keep d))
  branches-eq d = refl
  omega-row : R.value (packΩ omega) ≡ B.Ω V.q1 (λ d → proj₁ (End.child-out (KV.cv keep d)))
  omega-row = trans (cong proj₁ End.row)
    (trans (cong (λ k → proj₁ (F.node⁺ {j = K.one} {X = B.Tr B.zero} {x₀ = B.zero} k End.child-out End.feed)) (sym keep-eq))
      (KV.node-row keep End.child-out End.feed keep-good))
  tail-row : pre O.+ R.value (packΩ omega) ≡ B.Ω V.q1 branches
  tail-row = KV.prepend pre (R.value (packΩ omega)) (λ d → proj₁ (End.child-out (KV.cv keep d))) omega-row
cut-row : S.cut S.path (proj₁ child-feed) ≡ B.Ω V.q1 branches
cut-row = trans (cong (S.cut S.path) original)
  (trans (cong (λ c → S.cut S.path (R.value c)) e0)
  (trans (R.cutS s0 (0 ∷ 0 ∷ []) std)
  (trans (cong (λ c → S.cut (0 ∷ 0 ∷ []) (pre O.+ R.value c)) e1)
  (trans (R.cut0-add l1 (0 ∷ []) pre)
  (trans (cong (λ c → S.cut (0 ∷ []) (pre O.+ R.value c)) e2)
  (trans (R.cut0-add l2 [] pre)
  (trans (cong (λ c → pre O.+ R.value c) e3) tail-row)))))))
opaque
  kept : B.Tr K.one
  kept = S.cut S.path (proj₁ child-feed)
  kept-eq : kept ≡ S.cut S.path (proj₁ child-feed)
  kept-eq = refl
  kept-row : kept ≡ B.Ω V.q1 branches
  kept-row = cut-row
  head-eq : S.head kept ≡ S.hΩ
  head-eq = cong S.head kept-row
  branch-eq : ∀ d → S.br kept d ≡ branches d
  branch-eq d = cong (λ x → S.br x d) kept-row
  branch-form : ∀ d → S.br kept d ≡ pre O.+ proj₁ (End.child-out (KV.cv keep d))
  branch-form d = trans (branch-eq d) (branches-eq d)
```
