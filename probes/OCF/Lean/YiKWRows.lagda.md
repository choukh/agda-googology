# 截取后继行与极限行的变量等式
验收文件；编译定理：后继行沿 1,0,0 截取时保留累计和前缀，极限行沿 0 截取。
不构造 BranchNeed 或新的值下界；实际环境见 YiKWObjects。
来源：逐行展开 YiTBRow，截取复用 YiC1Slot.cut，Ω 行接口复用 YiBVRows。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKWRows where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiBVRows as V
import OCF.Lean.YiC1Slot as S
record Ctx : Set where
  constructor ctx
  field
    layer : B.L
    okay : P.Ok layer
    table : TB.Rb layer
    base : F.Base layer
    path : P._≤_ V.one layer
    beta : O.Tr⁺ V.one
value : Ctx → B.Tr V.one
value (ctx l o r b w beta) = proj₁ (TB.ψ l o r b V.one w beta (proj₁ (O.Ωt l)))
record Lim : Set where
  constructor limctx
  field
    g : ℕ → B.L
    okay : P.Ok (B.nd B.sL g)
    table : TB.Rb (B.nd B.sL g)
    base : F.Base (B.nd B.sL g)
    lower : ∀ n → P._≤_ V.one (g n)
    beta : O.Tr⁺ V.one
pack : Lim → Ctx
pack (limctx g o r b w beta) = ctx (B.nd B.sL g) o r b (P.inu w) beta
down0 : Lim → Ctx
down0 (limctx g o r b w beta) = ctx (g 0) (proj₂ o 0) (proj₂ r 0) (λ i u → b i (P.inc 0 u)) (w 0) beta
cut0 : ∀ c ns → S.cut (0 ∷ ns) (value (pack c)) ≡ S.cut ns (value (down0 c))
cut0 (limctx g o r b w beta) ns = refl
record Suc : Set where
  constructor succtx
  field
    h : B.Ch B.sS → B.L
    okay : P.Ok (B.nd B.sS h)
    table : TB.Rb (B.nd B.sS h)
    base : F.Base (B.nd B.sS h)
    lower : ∀ n → P._≤_ V.one (h n)
    beta : O.Tr⁺ V.one
packS : Suc → Ctx
packS (succtx h o r b w beta) = ctx (B.nd B.sS h) o r b (P.inu w) beta
downS : Suc → Ctx
downS (succtx h o r b w beta) = ctx (h tt) (proj₂ o tt) (proj₂ r tt) (λ i u → b i (P.inc tt u)) (w tt) beta
cutSraw : ∀ h o r b w beta ns → S.cut (1 ∷ 0 ∷ 0 ∷ ns) (value (packS (succtx h o r b w beta)))
  ≡ S.cut ns (proj₁ (O.next⁺ beta) O.+ proj₁ (TB.ψ (h tt) (proj₂ o tt) (proj₂ r tt) (λ i u → b i (P.inc tt u)) V.one (w tt) beta (proj₁ (b (h tt) (P.inc tt P.self)))))
cutSraw h o r b w beta ns = refl
cutS : ∀ c ns → Suc.base c (Suc.h c tt) (P.inc tt P.self) ≡ O.Ωt (Suc.h c tt)
  → S.cut (1 ∷ 0 ∷ 0 ∷ ns) (value (packS c)) ≡ S.cut ns (proj₁ (O.next⁺ (Suc.beta c)) O.+ value (downS c))
cutS (succtx h o r b w beta) ns e = trans (cutSraw h o r b w beta ns)
  (cong (λ z → S.cut ns (proj₁ (O.next⁺ beta) O.+ proj₁ (TB.ψ (h tt) (proj₂ o tt) (proj₂ r tt) (λ i u → b i (P.inc tt u)) V.one (w tt) beta (proj₁ z)))) e)
cut0-add : ∀ c ns x → S.cut (0 ∷ ns) (x O.+ value (pack c)) ≡ S.cut ns (x O.+ value (down0 c))
cut0-add (limctx g o r b w beta) ns x = refl
```
