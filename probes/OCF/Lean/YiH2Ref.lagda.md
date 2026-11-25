# 带高度族：ψ₀(Ω_{Ω·ω³}) 的参照
验收文件；编译定理：`Y₃-lab` 构造中间点的逐项标签，尚无 `Y₃ ≼ T⊤`，不算新值前沿。
参照生成取自 `TTopValRef.Rf`，用完整 `EboLeanBase.NF`；`fs-third-suc` 列出全部后继编号分支，覆盖判据见 `YiH2Cover.covers-iff`。
尚未实填所需分支覆盖；第 1 项是旧 ψ₀(Ω_{Ω·ω²})，其进入原 `T⊤` 的界也未证明；本轮没有中间点或终点下界。
首个工程阻点：合并旧验收的最小导入文件在去掉新值证明、改用旧已实例化模块后仍 6G 堆耗尽，依简报暂停；不否定路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiH2Ref where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
import Data.Sum
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Free.Level using (Ordᶜ; zero; lim; ≅-refl⁰)
open import OCF.Align.EBO using (T; ψ; 𝟏; natT; Ωt; cof; fsn; cω; []<)
open import OCF.Align.EboLeanBase using (NF; n[]; n∷; nψ; nf-ψ; nf-Ω; GB; GB[]; InG; gp; gh; gw; gc; gtl; noG∷; lt→<; c∷; c[])
open import OCF.Align.OrdLabZCorrespond using (Lab; lω)
open import OCF.Align.TTopValRef using (lab-ι; lab-ω)
import OCF.Align.EboLeanLab as LL
open import OCF.Align.Correspond using (fs-rep; fs-Ωω)

natNF : ∀ n → NF (natT n)
natNF zero = n[]
natNF (suc zero) = n∷ (nψ n[] n[] GB[]) tt n[]
natNF (suc (suc n)) = n∷ (nψ n[] n[] GB[]) (Data.Sum.inj₂ refl) (natNF (suc n))

zeroNat : ∀ n {z} → InG [] z (natT n) → z ≡ []
zeroNat (suc n) (gp (gh _)) = refl
zeroNat (suc n) (gp (gw _ ()))
zeroNat (suc n) (gp (gc _ ()))
zeroNat (suc n) (gtl i) = zeroNat n i

P₃ : T
P₃ = ψ (natT 1) (natT 3) ∷ []
Third : T
Third = ψ [] (Ωt P₃) ∷ []

nfP₃ : NF P₃
nfP₃ = nf-ψ (natNF 1) (natNF 3) (λ i → ⊥-elim (noG∷ (natNF 3) []< i))

nfThird : NF Third
nfThird = nf-ψ n[] (nf-Ω nfP₃) g
  where
  g : GB [] (Ωt P₃) (Ωt P₃)
  g (gp (gh _)) = []<
  g (gp (gw _ (gp (gh _)))) = lt→< _ _ refl
  g (gp (gw _ (gp (gw _ i)))) rewrite zeroNat 1 i = []<
  g (gp (gw _ (gp (gc _ i)))) rewrite zeroNat 3 i = []<
  g (gp (gw _ (gtl ())))
  g (gp (gc _ ()))
  g (gtl ())

opaque
  R₃ : Σ (ℕ → Ordᶜ zero) λ F → ∀ n → Lab (F n) (fsn Third n)
  R₃ = lab-ω (lab-ι (LL.lab-NF′ nfThird (c∷ c[]))) refl

Z₃ : ℕ → Ordᶜ zero
Z₃ = proj₁ R₃
Y₃ : Ordᶜ zero
Y₃ = lim Z₃
Z₃-lab : ∀ n → Lab (Z₃ n) (fsn Third n)
Z₃-lab = proj₂ R₃
Y₃-lab : Lab Y₃ Third
Y₃-lab = lω refl (≅-refl⁰ Y₃) Z₃-lab

Branch₃ : ℕ → T
Branch₃ n = ψ [] (Ωt (replicate (suc n) (ψ (natT 1) (natT 2)))) ∷ []

fs-third-suc : ∀ n → fsn Third (suc n) ≡ Branch₃ n
fs-third-suc n = trans (fs-Ωω (ψ (natT 1) (natT 3)) [] refl (suc n))
  (cong (λ u → ψ [] (Ωt u) ∷ []) (fs-rep (natT 1) 𝟏 (natT 2) refl (suc n)))

Z₃-suc-lab : ∀ n → Lab (Z₃ (suc n)) (Branch₃ n)
Z₃-suc-lab n = subst (Lab (Z₃ (suc n))) (fs-third-suc n) (Z₃-lab (suc n))

fs-third₀ : fsn Third 0 ≡ (ψ [] (natT 1) ∷ [])
fs-third₀ = refl
fs-third₁ : fsn Third 1 ≡ (ψ [] (Ωt (ψ (natT 1) (natT 2) ∷ [])) ∷ [])
fs-third₁ = refl
fs-third₂ : fsn Third 2 ≡ (ψ [] (Ωt (ψ (natT 1) (natT 2) ∷ ψ (natT 1) (natT 2) ∷ [])) ∷ [])
fs-third₂ = refl
```
