# 生成跨世界的模拟 LadderOrdCross: 左边 LadderInfTree 𝕊, 右边 LadderOrdTree 𝔹, 高度经保序映射 e.
# 正文从 LadderInfBridge 改写: 左边的 ℕ 换成一般的 𝕊, 只有与 ℕ 相关的段落是手写的.
import os,re
R=os.environ.get('REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','..','..','..'))
A=R+'/probes/OCF/Align/'
src=open(A+'LadderInfBridge.lagda.md',encoding='utf-8').read()
body=src.split('open NR using (flo-∼)\n',1)[1].split('```',1)[0]

def between(t,a,b,new):
    i=t.index(a); j=t.index(b,i)
    return t[:i]+new+t[j:]

# 关系的索引
body=body.replace('record Sm (m : ℕ)','record Sm (m : N.Ht)').replace('module _ (m : ℕ) (a b','module _ (m : N.Ht) (a b')
body=body.replace(' <ᴸ ',' N.<ᴸ ').replace('(tr< q qH)','(N.tr< q qH)')

# §1 递归定义的关系
body=between(body,'Rq : ∀ m a b {φ χ ψ ρ}','outRq :','''XR : N.Ht → Set₁
XR n = ∀ {k k′ ξ ζ ξ′ ζ′} → N.Q n k ξ ζ → I.Q (e n) k′ ξ′ ζ′ → Set

RV : ∀ m (v : ∀ {n} → n N.<ᴸ m → XR n) a b {φ χ ψ ρ} → N.Q m a φ χ → I.Q (e m) b ψ ρ → Set
LRV : ∀ m (v : ∀ {n} → n N.<ᴸ m → XR n) a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → N.Q m k ξ ζ → I.Q (e m) k′ ξ′ ζ′ → Set
RV m v a b x y = R₊ m a b (LRV m v a) v x y
LRV m v (suc k)   zero      {k′} x y = RV m v k k′ x y
LRV m v (suc c)   (suc r)   x y = LRV m v c r x y
LRV m v (lim f s) (self n)  {k′} x y = RV m v (f n) k′ x y
LRV m v (lim f s) (lim n r) x y = LRV m v (f n) r x y

FR : ∀ m → (∀ {n} → n N.<ᴸ m → XR n) → XR m
FR m v {k} {k′} x y = RV m v k k′ x y

LVq : ∀ m {n} → n N.<ᴸ m → XR n
LVq = N.Rec XR FR

Rq : ∀ m a b {φ χ ψ ρ} → N.Q m a φ χ → I.Q (e m) b ψ ρ → Set
Rq m = RV m (LVq m)

LRq : ∀ m a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → N.Q m k ξ ζ → I.Q (e m) k′ ξ′ ζ′ → Set
LRq m = LRV m (LVq m)

''')
body=between(body,'outVq : ∀ {m n}','rwk : ∀ {m a b','''outVq : ∀ {m n} (q : n N.<ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : N.Q n k ξ ζ} {z′ : I.Q (e n) k′ ξ′ ζ′} → LVq m q z z′ → Rq n k k′ z z′
outVq {m} q {z = z} {z′ = z′} l = subst (λ X → X z z′) (N.Rec-β XR FR m q) l

intoVq : ∀ {m n} (q : n N.<ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : N.Q n k ξ ζ} {z′ : I.Q (e n) k′ ξ′ ζ′} → Rq n k k′ z z′ → LVq m q z z′
intoVq {m} q {z = z} {z′ = z′} l = subst (λ X → X z z′) (sym (N.Rec-β XR FR m q)) l

''')

# ι↓ 与地板
body=between(body,'-- 两边 ι↓ 的地板','R-tl : ∀ {c c′','''-- 两边三歧对齐
cap∼ : ∀ {m χ ρ x y} n → Sm n χ ρ → x ∼ᶠ y → Sm m (N.cap χ n x) (I.cap ρ (e n) y)
cap∼ {m} {χ} {ρ} {x} {y} n s c = sm go
  where
  go : ∀ i → i N.<ᴸ m → N.cap χ n x i ∼ᶠ I.cap ρ (e n) y (e i)
  go i q with N.tri i n
  ... | tlt l = subst₂ _∼ᶠ_ refl (sym (I.cap-lt ρ y (ε l))) (unSm s i l)
  ... | teq refl = subst₂ _∼ᶠ_ refl (sym (I.cap-self ρ (e n) y)) c
  ... | tgt l = subst₂ _∼ᶠ_ refl (sym (I.cap-gt ρ y (ε l))) fz∼

-- 右边的节点号只差命题相等
R-Ω↓-castʳ : ∀ {m a b n k k′ φ χ ψ ρ} {q : n N.<ᴸ m} {Q₂ : e n I.<ᴸ e m} → Q₂ ≡ ε q → {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ (e n)) → k′ <ᴵ L}
          {h : ∀ ξ ζ → N.Vs m q k ξ ζ → N.Q m a (ξ ⊔ φ) (N.lo n ζ N.∪ χ)} {h′ : ∀ ξ ζ → I.Vs (e m) Q₂ k′ ξ ζ → I.Q (e m) b (ξ ⊔ ψ) (I.lo (e n) ζ I.∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sm m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sm n ζ ζ′ → (z : N.Q n k ξ ζ) (z′ : I.Q (e n) k′ ξ′ ζ′) → LVq m q z z′ → Rq m a b (h ξ ζ (N.intoV q z)) (h′ ξ′ ζ′ (I.intoV Q₂ z′))) → Rq m a b (N.qΩ↓ q fe ac h) (I.qΩ↓ Q₂ fe′ ac′ h′)
R-Ω↓-castʳ refl ek s c f = rΩ↓ ek s c f

R-cl-castʳ : ∀ {m a b n κ₁ κ₂ φ χ ψ ρ} {q : n N.<ᴸ m} {Q₂ : e n I.<ᴸ e m} → Q₂ ≡ ε q → {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ (e n)) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : N.Q m a φ χ} {t′ : I.Q (e m) b ψ ρ} {g : (η : Ordᴵ) → N.Q m a φ (N.upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → I.Q (e m) b ψ (I.upd ρ (e n) (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → Rq m a b t t′ → (∀ η η′ → η ≅ᴵ η′ → Rq m a b (g η) (g′ η′)) → Rq m a b (N.qcl q κ₁ s t g) (I.qcl Q₂ κ₂ s′ t′ g′)
R-cl-castʳ refl e₂ r h = rcl e₂ r h

R-ι↓ : ∀ {n m k k′ α α′ φ ψ χ ρ} (dq : n N.<ᴸ m) → k ≅ᴵ k′ → {x : N.Q n k φ χ} {x′ : I.Q (e n) k′ ψ ρ} → Rq n k k′ x x′ → Rq m α α′ (N.ι↓ dq x) (I.ι↓ (ε dq) x′)
R-ι↓ dq ek rz = rz
R-ι↓ {n = n} dq ek (rs sa sb r) = rs sa (cap∼ n sb (flo-∼ ek)) (R-ι↓ dq ek r)
R-ι↓ dq ek (rl h) = rl (λ n → R-ι↓ dq ek (h n))
R-ι↓ dq ek (ri e₁ h) = ri e₁ (λ x y d → R-ι↓ dq ek (h x y d))
R-ι↓ dq ek (rŝ e₁ r h) = rŝ e₁ (R-ι↓ dq ek r) (λ η ee η′ e′ d → R-ι↓ dq ek (h η ee η′ e′ d))
R-ι↓ dq ek (rĉ e₁ dz dg r h) = rĉ e₁ dz dg (R-ι↓ dq ek r) (λ η ee η′ e′ d → R-ι↓ dq ek (h η ee η′ e′ d))
R-ι↓ dq ek (rclo s r h) = rclo s (R-ι↓ dq ek r) (λ η η′ d → R-ι↓ dq ek (h η η′ d))
R-ι↓ dq ek (rcl {q = q} s r h) = R-cl-castʳ {q = N.tr< q dq} (I.<-prop _ _) s (R-ι↓ dq ek r) (λ η η′ d → rwk (R-ι↓ dq ek (h η η′ d)))
R-ι↓ dq ek (rwkˡ r) = rwkˡ (R-ι↓ dq ek r)
R-ι↓ dq ek (rwkʳ r) = rwkʳ (R-ι↓ dq ek r)
R-ι↓ {n = n} {m = m} {α = α} {α′ = α′} dq ek (rΩ↓ {q = q} {h = h} {h′ = h′} ei s c f) =
  R-Ω↓-castʳ {q = N.tr< q dq} (I.<-prop _ _) ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk
    (subst₂ (λ u v → Rq m α α′ (N.ι↓ dq (h ξ ζ (N.intoV q u))) (I.ι↓ (ε dq) (h′ ξ′ ζ′ (I.intoV (ε q) v)))) (sym (N.out-intoV (N.tr< q dq) z)) (sym (I.out-intoV (I.tr< (ε q) (ε dq)) z′))
      (R-ι↓ dq ek (f ξ ξ′ ζ ζ′ d dc _ _ (intoVq q (outVq (N.tr< q dq) l))))))
R-ι↓ {n = n} {m = m} {α = α} {α′ = α′} dq ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c f) =
  rΩ↓ {q = dq} ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk
    (subst₂ (λ u v → Rq m α α′ (N.ι↓ dq (h ξ ζ (N.intoU (<→◃ r) u))) (I.ι↓ (ε dq) (h′ ξ′ ζ′ (I.intoU (<→◃ r′) v)))) (sym (N.out-intoV dq z)) (sym (I.out-intoV (ε dq) z′))
      (R-ι↓ dq ek (f ξ ξ′ ζ ζ′ d dc _ _ (intoRq (<→◃ r) (outVq dq l))))))
R-ι↓ dq (s≅ e₁) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ dq ea l)
R-ι↓ dq (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ dq ea l)

''')
body=body.replace('Rq 0 c c′','Rq N.h₀ c c′').replace('(sm (λ i ()))','(sm (λ i q → ⊥-elim (N.no< q)))')

# RΩ̇
body=between(body,'RΩ̇ : ∀ m {a b}','R-trˡ  : ∀ {m a a′ b','''XRΩ : N.Ht → Set
XRΩ m = ∀ {a b} → a ≅ᴵ b → Rq m a b (N.Ω̇ m a) (I.Ω̇ (e m) b)

R-rowC : ∀ {m n} (q : n N.<ᴸ m) → XRΩ n → Rq m zero zero (N.rowC q (N.Ω̇ n)) (I.rowC (ε q) (I.Ω̇ (e n)))
R-rowC q I₁ = rcl {q = q} fz∼ (rwk (R-ι↓ q (s≅ z≅) (I₁ (s≅ z≅)))) (λ η η′ eη → rwk (R-ι↓ q eη (I₁ eη)))

R-𝟏L : ∀ {m} → Rq m zero zero (N.𝟏L {m}) (I.𝟏L {e m})
R-𝟏L = rwk (rs fz∼ (sm (λ i q → fz∼)) rz)

R-stepL : ∀ {m n} (q : n N.<ᴸ m) → XRΩ n → Rq m zero zero (N.stepL q (N.Ω̇ n)) (I.stepL (ε q) (I.Ω̇ (e n)))
R-stepL q I₁ = rwk (R-ι↓ q z≅ (I₁ z≅))

R-rowL : ∀ {m} F (qs₁ : ∀ i → F i N.<ᴸ m) → (∀ {n} → n N.<ᴸ m → XRΩ n) → ∀ i →
         Rq m zero zero (N.rowL F qs₁ (λ i₁ → N.ΩI m (qs₁ i₁)) i) (I.rowL (λ i₁ → e (F i₁)) (λ i₁ → ε (qs₁ i₁)) (λ i₁ → I.ΩI (e m) (ε (qs₁ i₁))) i)
R-rowL F qs₁ I₁ zero = R-𝟏L
R-rowL {m} F qs₁ I₁ (suc i) = subst₂ (λ X Y → Rq m zero zero (N.stepL (qs₁ i) X) (I.stepL (ε (qs₁ i)) Y)) (sym (N.ΩI≡ (qs₁ i))) (sym (I.ΩI≡ (ε (qs₁ i)))) (R-stepL (qs₁ i) (I₁ (qs₁ i)))

R-row : ∀ m → (∀ {n} → n N.<ᴸ m → XRΩ n) → (v : View N._<ᴸ_ N.h₀ m) → CE.RowEq 𝕊 𝔹 e ε m v → Rq m zero zero (N.rowV m (N.ΩI m) v) (I.Ω̇ (e m) zero)
R-row _ I₁ base rq = subst (Rq N.h₀ zero zero (N.rowB {N.h₀})) (sym rq)
  (rclo (∼ᶠ-refl fz)
    (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
    (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη))))
R-row m I₁ (clos q) rq = subst (Rq m zero zero (N.rowC q (N.ΩI m q))) (sym (cong (I.rowV (e m) (I.ΩI (e m))) rq))
  (subst₂ (λ X Y → Rq m zero zero (N.rowC q X) (I.rowC (ε q) Y)) (sym (N.ΩI≡ q)) (sym (I.ΩI≡ (ε q))) (R-rowC q (I₁ q)))
R-row m I₁ (chain F qs₁) rq = subst (Rq m zero zero (N.ql (N.rowL F qs₁ (λ i → N.ΩI m (qs₁ i))))) (sym (cong (I.rowV (e m) (I.ΩI (e m))) rq))
  (rl (R-rowL F qs₁ I₁))

FRΩ : ∀ m → (∀ {n} → n N.<ᴸ m → XRΩ n) → XRΩ m
FRΩ m I₁ (s≅ e₁) = rΩ e₁ (⊔∼ fz∼ (fk∼ z≅)) Fl∼ (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} e₁ l (R-ι zero zero l)))
FRΩ m I₁ (l≅ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (FRΩ m I₁ (h n)) (R-ι (self n) (self n) (FRΩ m I₁ (h n))))
FRΩ m I₁ z≅ = R-row m I₁ (N.view m) (rowq m)

RΩ̇ : ∀ m {a b} → a ≅ᴵ b → Rq m a b (N.Ω̇ m a) (I.Ω̇ (e m) b)
RΩ̇ m = FRΩ m (N.Rec XRΩ FRΩ m)

''')

# 三歧对齐
def fix_psi(t):
    t=t.replace('''R-Ψ {H} qH ok e₁ p ok′ e′ p′ et (rcl {n = n} s r h) with N.tri n H
... | tlt l = rcl''','''R-Ψ {H} qH ok e₁ p ok′ e′ p′ et (rcl {n = n} s r h) with N.tri n H | I.tri (e n) (e H) | al n H
... | _ | _ | all l = rcl''')
    t=t.replace('''... | teq refl = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et)''','''... | _ | _ | ale = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et)''')
    t=t.replace('''... | tgt l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (N.zr ok n)''','''... | _ | _ | alg l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (N.zr ok n)''')
    t=t.replace('''{h} {h′} ek s c f) with N.tri n H
... | tlt l = rΩ↓ {q = l}''','''{h} {h′} ek s c f) with N.tri n H | I.tri (e n) (e H) | al n H
... | _ | _ | all l = rΩ↓ {q = l}''')
    t=t.replace('''... | teq refl with <ᴵ-dec (ac (e₁ n (inj₁ refl) q)) p''','''... | _ | _ | ale with <ᴵ-dec (ac (e₁ n (inj₁ refl) q)) p''')
    t=t.replace('''{h} {h′} ek s c f) | tgt l =
''','''{h} {h′} ek s c f) | _ | _ | alg l =
''')
    return t
body=fix_psi(body)
body=body.replace('(e₁ : N.Eh zero m w χ)','(e₁ : N.Eh N.h₀ m w χ)').replace('NR.out-intoV','N.out-intoV').replace('IR.out-intoV','I.out-intoV')

HEAD='''# 序数高度: 跨世界的模拟

> **判决: HOLDS (对结构参数, 编译过; 条件是下面三个参数).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 由 `Survey/scripts/ladderord/mk_cross.py` 从 [LadderInfBridge](LadderInfBridge.lagda.md) 改写. 左边是 `LadderInfTree 𝕊`, 右边是 `LadderOrdTree 𝔹`. 参数: 保序映射 `e`, `ε`; 右边 `tri` 在对角线上是 `teq refl` (`tri-self`); 第 0 行的写法对齐 (`rowq`). 这些是结构参数, 每个实例都要闭合地给出. **`bridge m α α′ d : N.Tᵠ m α ≈ᴿ I.Tᵠ (e m) α′`**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase using (HtS)
open import OCF.Align.LadderOrdBase
import OCF.Align.LadderOrdCrossEq as CE
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module OCF.Align.LadderOrdCross (𝕊 : HtS) (𝔹 : HtB) (e : HtS.Ht 𝕊 → HtB.Ht 𝔹) (ε : ∀ {n m} → HtS._<ᴸ_ 𝕊 n m → HtB._<ᴸ_ 𝔹 (e n) (e m))
  (tri-self : ∀ a → HtB.tri 𝔹 a a ≡ teq refl) (rowq : ∀ m → CE.RowEq 𝕊 𝔹 e ε m (HtS.view 𝕊 m)) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Free.Base using (clash; r∅)
import OCF.Align.LadderInfTree
import OCF.Align.LadderInfRel
import OCF.Align.LadderOrdTree
import OCF.Align.LadderOrdRel
module N = OCF.Align.LadderInfTree 𝕊
module NR = OCF.Align.LadderInfRel 𝕊
module I = OCF.Align.LadderOrdTree 𝔹
module IR = OCF.Align.LadderOrdRel 𝔹
open NR using (flo-∼)

-- 两边的三歧对齐: 只用 ε 保序, 右边 irr, 右边 < 是命题, 右边对角线
data Al : ∀ n H → Tri N._<ᴸ_ n H → Tri I._<ᴸ_ (e n) (e H) → Set where
  all : ∀ {n H} (l : n N.<ᴸ H) → Al n H (tlt l) (tlt (ε l))
  ale : ∀ {n} → Al n n (teq refl) (teq refl)
  alg : ∀ {n H} (l : H N.<ᴸ n) → Al n H (tgt l) (tgt (ε l))

al-lt : ∀ {n H} (l : n N.<ᴸ H) (t : Tri I._<ᴸ_ (e n) (e H)) → Al n H (tlt l) t
al-lt l (tlt l′) = subst (λ w → Al _ _ (tlt l) (tlt w)) (I.<-prop (ε l) l′) (all l)
al-lt {n} {H} l (teq x) = ⊥-elim (I.irr (subst (I._<ᴸ e H) x (ε l)))
al-lt l (tgt l′) = ⊥-elim (I.irr (I.tr< (ε l) l′))

al-gt : ∀ {n H} (l : H N.<ᴸ n) (t : Tri I._<ᴸ_ (e n) (e H)) → Al n H (tgt l) t
al-gt l (tgt l′) = subst (λ w → Al _ _ (tgt l) (tgt w)) (I.<-prop (ε l) l′) (alg l)
al-gt {n} {H} l (teq x) = ⊥-elim (I.irr (subst (e H I.<ᴸ_) x (ε l)))
al-gt l (tlt l′) = ⊥-elim (I.irr (I.tr< (ε l) l′))

al : ∀ n H → Al n H (N.tri n H) (I.tri (e n) (e H))
al n H with N.tri n H
... | tlt l = al-lt l (I.tri (e n) (e H))
... | tgt l = al-gt l (I.tri (e n) (e H))
... | teq refl = subst (Al n n (teq refl)) (sym (tri-self (e n))) ale
'''
TAIL='''
```
'''
open(A+'LadderOrdCross.lagda.md','w',encoding='utf-8').write(HEAD+body.rstrip()+TAIL)

EQ='''# 序数高度: 跨世界的第 0 行对齐

> **判决: HOLDS (只有声明).** 结论写在 [LadderOrd](LadderOrd.lagda.md). `RowEq` 说右边第 0 行的写法与左边一致. 由 `Survey/scripts/ladderord/mk_cross.py` 写出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase using (HtS)
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdCrossEq (𝕊 : HtS) (𝔹 : HtB) (e : HtS.Ht 𝕊 → HtB.Ht 𝔹) (ε : ∀ {n m} → HtS._<ᴸ_ 𝕊 n m → HtB._<ᴸ_ 𝔹 (e n) (e m)) where

open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.LadderInfTree
import OCF.Align.LadderOrdTree
module N = OCF.Align.LadderInfTree 𝕊
module I = OCF.Align.LadderOrdTree 𝔹

RowEq : ∀ m → View N._<ᴸ_ N.h₀ m → Set
RowEq m base = I.rowV (e m) (I.ΩI (e m)) (I.view (e m)) ≡ I.rowB {e m}
RowEq m (clos q) = I.view (e m) ≡ clos (ε q)
RowEq m (chain F qs) = I.view (e m) ≡ chain (λ i → e (F i)) (λ i → ε (qs i))
```
'''
open(A+'LadderOrdCrossEq.lagda.md','w',encoding='utf-8').write(EQ)
