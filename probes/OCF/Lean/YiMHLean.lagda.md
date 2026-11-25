# 验收一侧 (精简块, 兄弟孩子折叠): 带 ℕ 极限规则的封闭关系上的合成, 律与出口

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `M̂ᴺ n = M̂ (YiCLFam.M n)`. 合成 `synˢ`: 孩子在 `Can` 内且对着 ω 时, ψ₂(Ω_ω) 对着兄弟孩子的那一支 (由 `YiRLCrit.ω̃ˢ` 加一步 `l̂`).
> 律: `leaf̂` (Ω_m 对第 n+1 层 Ω 树, m ≤ n+1), `lowKeep̂` (由 `YiRBFam.LF`), `selfKeep̂` (由 `Self.PF`), `weakᴺ`, 极限律即构造子 `l̂`. 出口 `exitᴺ`: 条件 `Ex`; 可满足的一例 `exit-ω̂`.
> 边界: `synˢ` 以空前缀折到第 0 层的那个推导上 `Ex` 不成立 (`¬ex-low0`: 见证项 ψ₀(ψ₂(Ω₃)) 不是标准形). 这只否定这一个推导上的条件, 不否定别的推导或别的前缀.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMHLean where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBFam using (Tp; tp; GB; mkGB; LF; OKB; module Self)
open import OCF.Lean.YiRBCrit using (gˢ; gᵗ)
open import OCF.Lean.YiRLCrit using (Can; ω̃ˢ; ω̃ᵗ; at-nat; le3)
open import OCF.Lean.YiKVRel using (M⁰; readRW; lower⁰)
import OCF.Align.EboLeanDef as E
open E using (HC; fsn; natT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF; n∷; nψ; gp; gh; Ctbl; c[]; c∷)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiANEnd using (natB)
open import OCF.Lean.YiCLFam using (nat; fn; M; mwN; Mβ)
open import OCF.Lean.YiCLLow using (pth; ΩJ)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᶜ-M)
open import OCF.Lean.YiDCRel using (nat≤; Ω≤)
open import OCF.Lean.YiMHRel
```

## 关系与合成

```agda
M̂ᴺ : (n : ℕ) → E.T → Tr (fn n) → Set
M̂ᴺ n = M̂ (M n)

synˢ : ∀ {c} → Can c → M⁰ ωᵀ c → M̂ᴺ 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gˢ c))
synˢ cc l = l̂ refl (λ k → ĉ (proj₁ (proj₂ (ω̃ˢ cc l k))) (proj₂ (proj₂ (ω̃ˢ cc l k))))

synᵗ : ∀ {c} → M⁰ ωᵀ c → M̂ᴺ 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gᵗ c))
synᵗ l = l̂ refl (λ k → ĉ (proj₁ (proj₂ (ω̃ᵗ l k))) (proj₂ (proj₂ (ω̃ᵗ l k))))
```

## 律

陈述照 `YiAbsGIface.Laws` 的 `Weak`, `Leaf`, `SelfKeep`, `LowKeep` 的形状写在精简块上 (精简块没有 `Graded` 的实例; 底与底值的前提仍用 `M` 陈述). 极限律 `Lim` 就是构造子 `l̂`.

```agda
weakᴺ : ∀ n {s x x′} → M̂ᴺ n s x → fn n ⊢ x ◃ x′ → M̂ᴺ n s x′
weakᴺ n m d = weak (λ r → mwN n r d) m

leaf̂ : ∀ {m} n → m ≤ⁿ suc n → M̂ᴺ (suc n) (Ωᴺ m) (proj₁ (Ωt (fn (suc n))))
leaf̂ n l = ĉ (Ω≤ l) (Mβ n)

lowKeep̂ : ∀ {n j} (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (s : Tp n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
         → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
         → ∀ {a x} → M̂ᴺ (suc n) a x
         → M̂ᴺ j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β x))
lowKeep̂ {j = j} o r s t₀ B gb β hβ = keep j t₀ (LF o r s t₀ B gb β hβ)

selfKeep̂ : ∀ N (o : Ok (fn (suc N))) (r : Rb (fn (suc N))) (B : Base (fn (suc N))) (β : Tr⁺ (fn (suc N))) {P₀}
          → M (suc N) (ψᴺ (suc N) P₀) (proj₁ β)
          → ∀ {a x} → M̂ᴺ (suc N) a x → M̂ᴺ (suc N) (ψᴺ (suc N) (P₀ ++ a)) (Self.F N o r B β x)
selfKeep̂ N o r B β {P₀} hP = keep (suc N) P₀ (Self.PF N o r B β hP)
```

## 出口

```agda
exitᴺ : ∀ {s x} (m : M̂ᴺ 0 s x) → Ex m → (h : HC s) → Rt h ≼ readRW x
exitᴺ = exit̂ readRW lower⁰
```

条件可满足, 且极限规则与放宽都用到的一例: ω 对着第 0 层的树 `ωᶜ`, 第 k 片叶子的见证项取 k + 3 (与 `ω̃ˢ` 的错位相同).

```agda
ω̂ : M̂ᴺ 0 ωᵀ ωᶜ
ω̂ = l̂ refl (λ k → ĉ (subst (λ t → t ≤ᵀ natT (suc (suc (suc k)))) (sym (rep1 k)) (nat≤ (le3 k)))
                     (at-nat ωᶜ-M (suc (suc (suc k)))))

ctN : ∀ n → Ctbl (natT n)
ctN zero    = c[]
ctN (suc n) = c∷ (ctN n)

ex-ω̂ : Ex ω̂
ex-ω̂ k = subst NF (sym (rep1 k)) (natB k) , natB (suc (suc (suc k))) , ctN (suc (suc (suc k)))

exit-ω̂ : (h : HC ωᵀ) → Rt h ≼ readRW ωᶜ
exit-ω̂ = exitᴺ ω̂ ex-ω̂
```

## 合成的推导折到第 0 层: 出口条件的边界

`low0`: `synˢ` 经 `lowKeep̂` (空前缀, 底的各分量在 Ω 树之上) 折到第 0 层. 它的第 0 片叶子的见证项是 ψ₀(ψ₂(Ω₃)); Ω₃ 是其 `InG` 元素而不低于 ψ₂(Ω₃), 所以不是标准形, `Ex` 在这个推导上不成立 (与 `YiDCExit.¬nf₂` 同一类).

```agda
low0 : (o : Ok (fn 2)) (r : Rb (fn 2)) (s : Tp 1 0) (B : Base (fn 2)) → OKB B → (β : Tr⁺ (fn 0)) → M⁰ (Ωᴺ 0) (proj₁ β)
     → ∀ {c} → Can c → M⁰ ωᵀ c
     → M̂ᴺ 0 (ψᴺ 0 (ψᴺ 2 (E.Ωt ωᵀ))) (proj₁ (ψ (fn 2) o r B (fn 0) (tp s) β (proj₁ (gˢ c))))
low0 o r s B ok β hβ cc l =
  lowKeep̂ o r s [] B (mkGB (λ {i} si → ok (fn i) (inc tt (pth si)))
                            (λ {i} si → ΩJ i (B (fn i) (inc tt (pth si))) (ok (fn i) (inc tt (pth si))))) β hβ (synˢ cc l)

¬Ω₃<ψ₂ : Ωᴺ 3 <ᵀ ψᴺ 2 (Ωᴺ 3) → ⊥
¬Ω₃<ψ₂ (hd< (lv< (hd< (lv< ()))))
¬Ω₃<ψ₂ (hd< (lv< (hd< (ar< ()))))
¬Ω₃<ψ₂ (hd< (lv< (tl< (hd< (lv< ())))))
¬Ω₃<ψ₂ (hd< (lv< (tl< (hd< (ar< ())))))
¬Ω₃<ψ₂ (hd< (lv< (tl< (tl< ()))))

¬nf-wit : NF (ψᴺ 0 (ψᴺ 2 (Ωᴺ 3))) → ⊥
¬nf-wit (n∷ (nψ _ _ g) _ _) = ¬Ω₃<ψ₂ (g (gp (gh (inj₁ []<))))

¬ex-low0 : ∀ o r s B ok β hβ {c} (cc : Can c) (l : M⁰ ωᵀ c) → Ex (low0 o r s B ok β hβ cc l) → ⊥
¬ex-low0 o r s B ok β hβ cc l ex =
  ¬nf-wit (proj₁ (proj₂ (all-keep⁻ {P = Leafᴺ} 0 [] (LF o r s [] B _ β hβ) (synˢ cc l) ex 0)))
```
