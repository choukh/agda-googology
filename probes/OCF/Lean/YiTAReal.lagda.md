# 每个可数标准形都有带精确读回的第 0 层树; `Real` 与 `CofΩ` 成立

> 验收文件 (读记号)。编译定理, 无前提: 低于 Ω₁ 的标准形 η 都有第 0 层的树 d 使 `Ex⁰ η d` (`real-exact`), 所以 `YiELChain.Real` 成立 (`real`), 共尾度 Ω₁ 的 ν 都满足 `YiELOmega.CofΩ` (`cofΩ-all`)。
> 构造: 主项 ψ₀(a) 沿 `HC` 推导递归 (`EboLeanTree.hc` 给出 `HC`, 无前提); a 后继时取 `next⁺`, 否则基本列各项仍是主项, 取 `limc⁺`, 部分和吸收 (`YiTAChain.lbl-limc`); 和逐项用 `YiELChain.ex-add`。
> 不涉及折叠: 这些树不是折叠的输出, 不给 LowKeep 或折叠链点的标签。入口: [YiTAChain](YiTAChain.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTAReal where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open O using (_+_)
import OCF.Align.EboLeanDef as E
open E using (ψ)
open import OCF.Align.EboLeanBase using (NF; n[]; n∷; nf-hd; cofA≢c1; Ctbl; c[]; c∷)
open import OCF.Align.EboLeanView using (cof0; cofA0; ne)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiELZero using (Ex⁰; ctbl<)
open import OCF.Lean.YiELChain using (ex-add; ex-next; Real; cofΩ-real)
open import OCF.Lean.YiELOmega using (CofΩ)
open import OCF.Lean.YiTAChain using (lbl-limc)
```

## 主项

a ≠ 0 时 ψ₀(a) 的共尾度是 ω; a 不是后继时基本列的每一项仍是 ψ₀(·) (`fsn-prin`, 规则 5ω 与规则 6)。

```agda
cv : ∀ a → (E.cof a ≡ E.c1) ⊎ (E.cof a ≡ E.c1 → ⊥)
cv a with E.cof a
... | E.c0   = inj₂ λ ()
... | E.c1   = inj₁ refl
... | E.cω   = inj₂ λ ()
... | E.cΩ μ = inj₂ λ ()

fsn-prin : ∀ b bs → (E.cof (b ∷ bs) ≡ E.c1 → ⊥) → ∀ n
  → Σ E.T λ a′ → E.fsn (ψ [] (b ∷ bs) ∷ []) n ≡ ψ [] a′ ∷ []
fsn-prin b bs n1 n = go (E.cof (b ∷ bs)) (cof0 (b ∷ bs) ne) n1
  where
  go : ∀ c → (c ≡ E.c0 → ⊥) → (c ≡ E.c1 → ⊥) → Σ E.T λ a′ → E.fsn₊ [] (b ∷ bs) c n ≡ ψ [] a′ ∷ []
  go E.c0 z _ = ⊥-elim (z refl)
  go E.c1 _ o = ⊥-elim (o refl)
  go E.cω _ _ = E.fsn (b ∷ bs) n , refl
  go (E.cΩ μ) _ _ = fc (E.cmpᵀ (E.sucT μ) [])
    where
    fc : ∀ m → Σ E.T λ a′ → E.fsnc [] (b ∷ bs) μ m n ≡ ψ [] a′ ∷ []
    fc E.lt = _ , refl
    fc E.eq = _ , refl
    fc E.gt = _ , refl

prin : ∀ {t} → E.HC t → ∀ a → t ≡ ψ [] a ∷ [] → NF t → Σ (O.Tr⁺ zero) λ d → Ex⁰ t (proj₁ d)
prin _ [] refl _ = O.Ωt zero , refl , refl
prin (E.h0 e) (b ∷ bs) refl _ = ⊥-elim (cofA0 [] (E.cof (b ∷ bs)) e)
prin (E.h1 e _) (b ∷ bs) refl _ = ⊥-elim (cofA≢c1 [] (E.cof (b ∷ bs)) e)
prin (E.hω e h) (b ∷ bs) refl nf with cv (b ∷ bs)
... | inj₁ ec = O.next⁺ (proj₁ k₁)
  , ex-next (proj₁ k₁) (nf-hd nf₁) nf e q (subst (λ ν → Ex⁰ ν (proj₁ (proj₁ k₁))) eq₁ (proj₂ k₁))
  where
  eq₁ : E.fsn (ψ [] (b ∷ bs) ∷ []) 1 ≡ ψ [] (E.pred (b ∷ bs)) ∷ []
  eq₁ = cong (λ c → E.fsn₊ [] (b ∷ bs) c 1) ec
  k₁ = prin (h 1) (E.pred (b ∷ bs)) eq₁ (cl-fsn-NF nf e 1)
  nf₁ = subst NF eq₁ (cl-fsn-NF nf e 1)
  q : ∀ n → E.fsn (ψ [] (b ∷ bs) ∷ []) n ≡ replicate n (ψ [] (E.pred (b ∷ bs)))
  q n = cong (λ c → E.fsn₊ [] (b ∷ bs) c n) ec
... | inj₂ n1 = O.limc⁺ (λ n → proj₁ (kid n))
  , lbl-limc (λ n → proj₁ (kid n)) nf e (λ n → γ n , proj₂ (kid n) , inj₂ refl , t< (trian-fsn nf e n))
  where
  γ : ℕ → E.T
  γ n = E.fsn (ψ [] (b ∷ bs) ∷ []) n
  kid : ∀ n → Σ (O.Tr⁺ zero) λ d → Ex⁰ (γ n) (proj₁ d)
  kid n = prin (h n) (proj₁ (fsn-prin b bs n1 n)) (proj₂ (fsn-prin b bs n1 n)) (cl-fsn-NF nf e n)
```

## 和, `Real`, `CofΩ`

```agda
real-ctbl : ∀ {η} → NF η → Ctbl η → Σ (Tr zero) (Ex⁰ η)
real-ctbl n[] c[] = zero , refl
real-ctbl (n∷ p h nt) (c∷ {a = a} ct) =
  proj₁ (proj₁ k₁) + proj₁ k₂ , ex-add (proj₁ (proj₁ k₁)) (proj₁ k₂) p (proj₂ k₁) (proj₂ k₂) h
  where
  nf₁ = n∷ p tt n[]
  k₁ = prin (hc nf₁ (c∷ c[])) a refl nf₁
  k₂ = real-ctbl nt ct

real-exact : ∀ {η} → NF η → η E.<ᵀ E.Ωs [] → Σ (Tr zero) (Ex⁰ η)
real-exact nf lt = real-ctbl nf (ctbl< nf lt)

real : Real
real {η} nf lt with real-exact nf lt
... | d , x = d , η , x , inj₂ refl

cofΩ-all : ∀ {ν} (h : Tr zero → L) → E.cof ν ≡ E.cΩ [] → CofΩ h ν
cofΩ-all = cofΩ-real real
```
