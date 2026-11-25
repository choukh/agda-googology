# 标准底上颈链的前两项
验收文件；编译定理：每项合法（最小表给闭项）；第一项值至少 ψ₀(Ω₃)，却不能精确标为 ψ₀(Ω₃)（第 0 个孩子为 ω）。
第一项弱链等价于存在精确读回 `FirstExact`：`first-if` 与 `first-only` 给两向；第二项 γ 目标是 ψ₀(Ω₁)，`second-fs0≤ω` 给必要条件。
首个未构造引理是标准底上的 `FirstExact`；第二项弱链、一般 `NeckLabChain` 与颈结点 LowKeep 未证；特定标签的否定不排除其他标签。
来源：值下界复用 `YiTBFam.sΩ-LF`、`YiKVRel.lower⁰`；标签比较复用 `YiGLFrame.uniq`、`YiELChain.ex-ω′`；不修改已有定义。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNCFirst where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R; C)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
import OCF.Lean.YiTBFam as TF
open import OCF.Lean.YiRBFam using (tu; pu; can)
open import OCF.Lean.YiCLLow using (s0)
import OCF.Lean.YiMGFrame as MF
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiMGNeck as N
import OCF.Lean.YiLKIface as I
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiELZero as Z
open import OCF.Lean.YiELChain using (ex-ω′)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiGLFrame using (uniq)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤¬>; NF; InG; gp; gtl; gh; gw; gc; n[]; nf-Ω; nf-ψ; c∷; c[])
open import OCF.Lean.YiANEnd using (natB)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_)
open import OCF.Align.EboLean3Base using (sucT≤)

step : Rb S.layer → Tr zero → Tr zero
step r = I.feed S.layer S.okay r (B₀ S.layer) N.neck N.gL

C : Rb S.layer → ℕ → Tr zero
C r n = O.iter (step r) zero (suc n)

out⁺ : (r : Rb S.layer) → Tr zero → O.Tr⁺ zero
out⁺ r c = ψ (S.child c) (proj₂ S.okay c) (proj₂ r c) (B₀ (S.child c))
 zero (self ∙ z≤ (S.child c)) (O.Ωt zero) (proj₁ (O.Ωt (S.child c)))

step-row : ∀ r c → step r c ≡ proj₁ (out⁺ r c)
step-row r c = refl

C-legal : ∀ r n → zero ⊢ zero ◃ C r n
C-legal r zero = proj₂ (out⁺ r zero)
C-legal r (suc n) = proj₂ (out⁺ r (C r n))

FirstExact : Rb S.layer → Set
FirstExact r = Σ E.T λ μ → Z.Ex⁰ μ (C r 0)

SecondExact : Rb S.layer → Set
SecondExact r = Σ E.T λ μ → Z.Ex⁰ μ (C r 1)

Item : Rb S.layer → E.T → E.T → ℕ → Set
Item r t a n = Σ E.T λ μ → Z.Ex⁰ μ (C r n) × (E.γT (t ++ a) [] n ≤ᵀ μ)

lim-one : ∀ {μ} → E.cof μ ≡ E.cω → E.natT 1 ≤ᵀ μ
lim-one {μ = []} ()
lim-one {μ = _ ∷ _} e = sucT≤ E.[]<

first-if : ∀ r t a → FirstExact r → Item r t a 0
first-if r t a (μ , q) = μ , q , lim-one (proj₁ q)

first-only : ∀ r t a → Item r t a 0 → FirstExact r
first-only r t a (μ , q , lo) = μ , q

closed-chain : ℕ → Tr zero
closed-chain n = C (MT.rbᶻ S.layer) n

closed-legal : ∀ n → zero ⊢ zero ◃ closed-chain n
closed-legal n = C-legal (MT.rbᶻ S.layer) n

first-needed : ∀ r t a → N.NeckLabChain r (B₀ S.layer) t a → FirstExact r
first-needed r t a c = proj₁ (c 0) , proj₁ (proj₂ (c 0))

first-lower : ∀ (r : Rb S.layer) → K.M⁰ (E.ψ [] (E.Ωt (E.natT 3)) ∷ []) (C r 0)
first-lower r = TF.sΩ-LF {n = 2} {j = 0} (proj₂ S.okay zero) (proj₂ r zero) (tu (pu (pu (can s0))))
 (B₀ (S.child zero)) (O.Ωt zero) (λ i u → K.⊴r) (K.m1 {t = E.natT 1} {x = zero} refl K.mz)

ω<first-fs0 : ωᵀ E.<ᵀ E.fsn (E.ψ [] (E.Ωt (E.natT 3)) ∷ []) 0
ω<first-fs0 = E.hd< (E.ar< (E.hd< (E.lv< E.[]<)))

no-first-at-natural : ∀ (r : Rb S.layer) → Z.Ex⁰ (E.ψ [] (E.Ωt (E.natT 3)) ∷ []) (C r 0) → ⊥
no-first-at-natural r (e , nf , la , k) = ≤¬> lo ω<first-fs0
 where
 eq = uniq (↑ zero (proj₁ (O.next⁺ (O.Ωt zero)))) (proj₁ (proj₂ (k 0))) ex-ω′
 lo = subst (E.fsn (E.ψ [] (E.Ωt (E.natT 3)) ∷ []) 0 ≤ᵀ_) eq (proj₁ (proj₂ (proj₂ (k 0))))

second-needed : ∀ r t a → N.NeckLabChain r (B₀ S.layer) t a → SecondExact r
second-needed r t a c = proj₁ (c 1) , proj₁ (proj₂ (c 1))

second-row : ∀ r → C r 1 ≡ proj₁ (out⁺ r (C r 0))
second-row r = refl

first-fs0≤ω : ∀ r {μ} → Z.Ex⁰ μ (C r 0) → E.fsn μ 0 ≤ᵀ ωᵀ
first-fs0≤ω r {μ} (e , nf , la , k) = subst (E.fsn μ 0 ≤ᵀ_)
 (uniq (↑ zero (proj₁ (O.next⁺ (O.Ωt zero)))) (proj₁ (proj₂ (k 0))) ex-ω′)
 (proj₁ (proj₂ (proj₂ (k 0))))

second-fs0≤ω : ∀ r {μ} → Z.Ex⁰ μ (C r 1) → E.fsn μ 0 ≤ᵀ ωᵀ
second-fs0≤ω r {μ} (e , nf , la , k) = subst (E.fsn μ 0 ≤ᵀ_)
 (uniq (↑ zero (proj₁ (O.next⁺ (O.Ωt zero)))) (proj₁ (proj₂ (k 0))) ex-ω′)
 (proj₁ (proj₂ (proj₂ (k 0))))

first-target : E.γT (E.ΩTower 2) [] 0 ≡ E.natT 1
first-target = refl

second-target : E.γT (E.ΩTower 2) [] 1 ≡ E.ψ [] (E.Ωt (E.natT 1)) ∷ []
second-target = refl

nat-G : ∀ n {z} → InG [] z (E.natT n) → z ≡ []
nat-G zero ()
nat-G (suc n) (gp (gh _)) = refl
nat-G (suc n) (gp (gw _ ()))
nat-G (suc n) (gp (gc _ ()))
nat-G (suc n) (gtl p) = nat-G n p

Ω₃-G : ∀ {z} → InG [] z (E.Ωt (E.natT 3)) → z ≡ []
Ω₃-G (gp (gh _)) = refl
Ω₃-G (gp (gw _ p)) = nat-G 3 p
Ω₃-G (gp (gc _ ()))
Ω₃-G (gtl ())

nf-first : NF (E.ψ [] (E.Ωt (E.natT 3)) ∷ [])
nf-first = nf-ψ n[] (nf-Ω (natB 3))
 (λ i → subst (E._<ᵀ E.Ωt (E.natT 3)) (sym (Ω₃-G i)) E.[]<)

opaque
 first-hc : E.HC (E.ψ [] (E.Ωt (E.natT 3)) ∷ [])
 first-hc = hc nf-first (c∷ c[])

first-value-lower : ∀ r → Rt first-hc ≼ K.readRW (C r 0)
first-value-lower r = K.lower⁰ (first-lower r) first-hc
```
