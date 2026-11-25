# 目标孩子 ω: 替身的值到 ψ_ω(Ω_{ω+1})

> 验收文件 (读记号), 不进成品; 树、折叠、合法性不改. 判决: 编译定理, 无前提. d = `YiTBTab.ωᶜ`, 关系是 `YiHCLim` 的封闭族 `Mω`: `seen` 在一切非零孩子 c 处 (字面延伸 ω 的都是) 承载 ψ_ω(Ω_{ω+1}) (`seen-ω`, `seen-ext`; c = ω+1 是 `step0`), 在一切 c 处承载 ψ_ω(Ω_ω) (`seen-ω₀`); 实际证据下塔第 1 项 Ω 树的各支同样 (`branch-nz`, `branch-all`); 顶结点保留在 `q₀` 上 (`top-shape`), 各支承载 t[η] 时它承载 t (`top-from-branch`, 前提未判定).
> 不给出什么: 参照不随 c 增长 (不是 ψ_ω(Ω_c)); 上确界的归约见 [YiSVRed](YiSVRed.lagda.md). 第二个实例 `Fin` 是有限目标层 (`fin-nz`: ψ_n(Ω_{n+1})).
> 来源: 接口实例取 `YiHCOmega.Tω` (`leafω`, `Self.PFω`) 与 `YiHCFold.Self.PF`; 层号参数照 `YiLTLift.Hω`, 孩子换成 `YiTBRow.nat` 读回的 (`eG` 是逐点相等).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSVOmega where
open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib using (Rb)
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; natT; sucT; cmpᵀ)
open import OCF.Lean.YiANFam using (cofΩ; fsTΩ; Pen)
open import OCF.Lean.YiDCRel using (suc-nat)
open import OCF.Lean.YiCLFam using (fn; Nw; penN; ≤ⁿ-refl)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth; gtJ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
import OCF.Lean.YiHCFam as HF
import OCF.Lean.YiHCFold as HD
open import OCF.Lean.YiLRBridge using (Sᶜ; NwB; τ₂; τ₂S; τ₂self)
open import OCF.Lean.YiHCBridge using (MB)
open import OCF.Lean.YiHCLim using (module Lim)
open import OCF.Lean.YiHCOmega using (ψᵘ; gtω-self; penB; module Tω)
open import OCF.Lean.YiTBRow using (h₁; nat)
open import OCF.Lean.YiTBTab using (ωᶜ)
open import OCF.Lean.YiBSBase using (seen; rb-tw)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiVALeaf using (nzl)
open import OCF.Lean.YiRKCell using (Ext; q₀)
open import OCF.Lean.YiSVMono
open import OCF.Lean.YiSVStep
open import OCF.Lean.YiSVCell

G : ℕ → L
G n = h₁ (nat n)

eG : ∀ n → G n ≡ fn n
eG zero    = refl
eG (suc n) = cong Sᶜ (eG n)

Rr : (n : ℕ) → G n ≤ G (suc n)
Rr n = inc tt self

canR : ∀ n → Σ (Sb (suc n) n) λ s → τ₂ (eG n) (eG (suc n)) (Rr n) ≡ pth s
canR n = ss s0 , trans (τ₂S (eG n) (eG n) self) (cong (inc tt) (τ₂self (eG n)))

lvl : h₁ ωᶜ ≡ nd sL G
lvl = refl

module Wω = Lim G (λ n → n) eG Rr canR
module Hω = Tω G (λ n → n) eG Rr canR
open Wω using (Lω; Mω; Lowω; Nuω)

penω′ : (p : Pos Lω) {ν′ : E.T} → Nuω p ν′ → Pen (cmpᵀ (sucT ν′) ωᵀ)
penω′ (inj₁ ())
penω′ (inj₂ (m , t)) nu = penB (G m) (eG m) t nu

module Sω (oc : (k : ℕ) → Ok (G k)) =
  Step Lω (Rr , oc) ωᵀ Lowω (λ m → MB (G m) (eG m)) Nuω gtω-self refl (λ η → refl) penω′
       (Hω.leafω (λ _ → ≤-refl)) (λ r B β → Hω.Self.PFω oc r B β)

ψω : E.T → E.T
ψω = ψᵘ ωᵀ

seen-ω : (oc : (k : ℕ) → Ok (G k)) (c : Tr zero) → zero ⊢ zero ◃ c → (u : zero ≤ Lω) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β)
       → Mω (ψω (E.Ωt (sucT ωᵀ))) (proj₁ (seen Sᶻ (h₁ ωᶜ) (Rr , oc) u β c))
seen-ω oc = Sω.seen-nz oc

seen-ext : (oc : (k : ℕ) → Ok (G k)) {c : Tr zero} → Ext ωᶜ c → (u : zero ≤ Lω) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β)
         → Mω (ψω (E.Ωt (sucT ωᵀ))) (proj₁ (seen Sᶻ (h₁ ωᶜ) (Rr , oc) u β c))
seen-ext oc {c} x = seen-ω oc c (z◃ ωᶜ x)

step0 : (oc : (k : ℕ) → Ok (G k)) (u : zero ≤ Lω) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β)
      → Mω (ψω (E.Ωt (sucT ωᵀ))) (proj₁ (seen Sᶻ (h₁ ωᶜ) (Rr , oc) u β (suc ωᶜ)))
step0 oc = seen-ext oc ◃s

seen-ω₀ : (oc : (k : ℕ) → Ok (G k)) (c : Tr zero) (u : zero ≤ Lω) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β)
        → Mω (ψω (E.Ωt ωᵀ)) (proj₁ (seen Sᶻ (h₁ ωᶜ) (Rr , oc) u β c))
seen-ω₀ oc = Sω.seen-all oc
```

## 实际证据下塔第 1 项 Ω 树的各支与顶结点

```agda
ocᴬ : (k : ℕ) → Ok (G k)
ocᴬ k = proj₂ (proj₂ (Ok-tw 1) ωᶜ) k

okᴬ : proj₂ (Ok-tw 1) ωᶜ ≡ (Rr , ocᴬ)
okᴬ = refl

nzω : _
nzω = nzl nat (λ n → ◃s)

Fᴬ : Base (tw 1) → Tr⁺ Lω → Tr (tw 1) → Tr⁺ Lω
Fᴬ B β x = BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B (h₁ ωᶜ) (inc ωᶜ self) β x

blk : (c : Tr zero) → Tr (tw 1)
blk c = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))

branch-nz : (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → (c : Tr zero) → zero ⊢ zero ◃ c
          → Mω (ψω (E.Ωt (sucT ωᵀ))) (proj₁ (Fᴬ B β (blk c)))
branch-nz B β hβ c d =
  cell nzω (Ok-tw 1) (Mω (ψω (E.Ωt (sucT ωᵀ)))) mw c B β zero (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c))) (seen-ω ocᴬ c d (lift zero (↑ zero ωᶜ)) β hβ)

branch-all : (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → (c : Tr zero)
           → Mω (ψω (E.Ωt ωᵀ)) (proj₁ (Fᴬ B β (blk c)))
branch-all B β hβ c =
  cell nzω (Ok-tw 1) (Mω (ψω (E.Ωt ωᵀ))) mw c B β zero (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c))) (seen-ω₀ ocᴬ c (lift zero (↑ zero ωᶜ)) β hβ)

top-shape : (B : Base (tw 1)) (β : Tr⁺ Lω)
          → proj₁ (Fᴬ B β (proj₁ (Ωt (tw 1)))) ≡ Ω q₀ (λ z → proj₁ (Fᴬ B β (blk z)))
top-shape B β = refl

top-from-branch : (B : Base (tw 1)) (β : Tr⁺ Lω) {t ν : E.T} → cof t ≡ cΩ ν → ν ≡ natT 0
                → (∀ η c → HF.M 0 η c → Mω (fsT t η) (proj₁ (Fᴬ B β (blk c))))
                → Mω t (proj₁ (Fᴬ B β (proj₁ (Ωt (tw 1)))))
top-from-branch B β e nu h = mΩ e nu h
```

## 第二个实例: 有限目标层

```agda
module Fin (N : ℕ) (oj : Ok (fn (suc N))) =
  Step (fn (suc N)) oj (natT (suc N)) (HF.LwP (suc N)) (λ _ → HF.M N) (Nw N)
       (gtJ {j = suc N} {i = suc N} (≤ⁿ-refl (suc N)) refl)
       (subst (λ z → cof (E.Ωt z) ≡ cΩ (natT (suc N))) (sym (suc-nat (suc N))) (cofΩ (suc N)))
       (λ η → subst (λ z → fsT (E.Ωt z) η ≡ η) (sym (suc-nat (suc N))) (fsTΩ (suc N) η))
       (λ p nu → penN N p nu) (HF.Mβ N) (λ r B β → HD.Self.PF N oj r B β)

fin-nz : ∀ N (oj : Ok (fn (suc N))) (c : Tr zero) → zero ⊢ zero ◃ c → (u : zero ≤ fn (suc N)) (β : Tr⁺ (fn (suc N)))
       → HF.M (suc N) (ψᵘ (natT (suc N)) []) (proj₁ β)
       → HF.M (suc N) (ψᵘ (natT (suc N)) (E.Ωt (sucT (natT (suc N))))) (proj₁ (seen Sᶻ (fn (suc N)) oj u β c))
fin-nz N oj = Fin.seen-nz N oj
```
