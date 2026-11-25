# V2 的反例在重述后的命名关系下不成立

> 判决: 编译定理, 条件 (排中律作模块参数), 验收侧. `YiNMAbsorb` 的树 `T* = ε₀ + Ω₁` 在 `YiNPName` 的关系下不名为 Ω₁ (`¬named-T*`), 所以 `YiNMAbsorb.B-false` 的前提不再可满足.
> 用到的只有结点一行的 ◁: 下标 0 处的分支名为 b + 1 (b 是 `E` 的名字, 余尾 ω), `b + 1 ◁₀ Ω₁` 迫使 G₀(b) 只含 0, 这样的项余尾不是 ω (`noω`).
> 另有 `lvn-tw1`: 遗传的层号命名在 `tw 1` 上可填 (名为 Ω₁, 无额外前提).
> 不否定什么: 不说明 B 在新关系下成立 (保留支的反例见 `YiNPWild`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNPAbsorb where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Induction.WellFounded using (Acc; acc)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRVLevel
open import OCF.Lean.YiNMSharp
open import OCF.Lean.YiNMTerm
open import OCF.Lean.YiNMAbsorb using (one; o₁; module Absorb)
open import OCF.Lean.YiNPName
import OCF.Align.EboLeanDef as E
import OCF.Align.EBO as E0
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanTrian as ET
open EB using (NF; _≤ᵀ_)
```

## 记号侧: G₀ 只含 0 的项余尾不是 ω

```agda
[]≤ : ∀ {w} → [] ≤ᵀ w
[]≤ {w = []}    = inj₂ refl
[]≤ {w = _ ∷ _} = inj₁ E.[]<

ψ0-ω : ∀ {u} c → E.cofψ0 u c ≡ E.cω → c ≡ E.cω
ψ0-ω E.c0 ()
ψ0-ω E.c1 ()
ψ0-ω E.cω _ = refl
ψ0-ω (E.cΩ _) ()

noω : ∀ b → (∀ {x} → EB.InG [] x b → x ≡ []) → E.cof b ≡ E.cω → ⊥
noω [] g ()
noω (x ∷ y ∷ ys) g e = noω (y ∷ ys) (λ i → g (EB.gtl i)) e
noω (E.ψ u (c ∷ cs) ∷ []) g e with g (EB.gp (EB.gh ([]≤ {w = u})))
... | ()
noω (E.ψ (w ∷ ws) [] ∷ []) g e = noω (w ∷ ws) (λ i → g (EB.gp (EB.gw []≤ i))) (ψ0-ω (E.cof (w ∷ ws)) e)
noω (E.𝟏 ∷ []) g ()

∔𝟏 : ∀ K → K ∔ (E.𝟏 ∷ []) ≡ E.sucT K
∔𝟏 K = trans (∔-sucT K []) (cong E.sucT (∔-[] K))
```

## T* 不名为 Ω₁

```agda
module AbsorbP (lem : LEM) where
  open Sharp lem
  open Term lem
  open NameP lem
  open Absorb lem using (E⁺; E′; T*; Ω₁ᵗ)

  G0Ω₁ : ∀ {y} → EB.InG [] y Ω₁ᵗ → y ≡ []
  G0Ω₁ (EB.gp (EB.gh _))                         = refl
  G0Ω₁ (EB.gp (EB.gw _ (EB.gp (EB.gh _))))       = refl
  G0Ω₁ (EB.gp (EB.gw _ (EB.gp (EB.gw _ ()))))
  G0Ω₁ (EB.gp (EB.gw _ (EB.gp (EB.gc _ ()))))
  G0Ω₁ (EB.gp (EB.gw _ (EB.gtl ())))
  G0Ω₁ (EB.gp (EB.gc _ ()))
  G0Ω₁ (EB.gtl ())

  dom0 : ∀ {x} → ET.Dom [] [] Ω₁ᵗ x → x ≡ []
  dom0 {x} (inj₁ (y , i , l))    = EB.≤[] (subst (x ≤ᵀ_) (G0Ω₁ i) l)
  dom0 (inj₂ (inj₁ e))           = e
  dom0 (inj₂ (inj₂ (y , () , l)))

  core : ∀ {F0 a₁ a₂ b₁ b₂} → F0 ≡ a₁ ∔ a₂ → a₁ ≡ b₁ ∔ b₂ → b₁ ≡ [] → E.cof a₂ ≡ E.c1 → E.pred a₂ ≡ []
       → E.cof b₂ ≡ E.cω → ET.Trian [] F0 Ω₁ᵗ → ⊥
  core {a₂ = a₂} {b₂ = b₂} refl refl refl c1e pz cωe t = noω b₂ allz cωe
    where
    ea₂ : a₂ ≡ E.𝟏 ∷ []
    ea₂ = trans (sym (E0.pred-suc a₂ c1e)) (cong E.sucT pz)
    t′ : ET.Trian [] (E.sucT b₂) Ω₁ᵗ
    t′ = subst (λ s → ET.Trian [] s Ω₁ᵗ) (trans (cong (b₂ ∔_) ea₂) (∔𝟏 b₂)) t
    allz : ∀ {x} → EB.InG [] x b₂ → x ≡ []
    allz i = dom0 (ET.tb t′ [] Ω₁ᵗ (ET.t< t′) (inj₂ refl) (EB.G-sucT b₂ i))

  ¬named-T* : (ac : Acc _≺ᴸ_ one) → Nmd one o₁ ac T* Ω₁ᵗ → ⊥
  ¬named-T* (acc r) (_ , _ , (_ , refl , _ , F , hF , sw)) =
    let (_ , _ , (a₁ , a₂ , nE′ , ns , eq , _))   = hF zero [] (EB.n[] , ≈ᴸ-refl zero , refl)
        (_ , _ , (b₁ , b₂ , nz′ , nE , eq′ , _))  = nE′
        (_ , _ , (c1e , (_ , _ , pz)))            = ns
    in core eq eq′ (proj₂ (proj₂ nz′)) c1e pz (proj₁ (proj₂ (proj₂ nE))) (proj₂ (sw [] EB.n[] E.[]<))
```

## 层号的遗传命名在 `tw 1` 上可填

`tw 1` 名为 Ω₁: 下标层 (第 0 层) 名为 0, 下标树 c 名为 η 时孩子 `zero ⊕ ↑ c` 名为 η (`rb`: 第 0 层有名字的树的读回逐行有名字), F 取恒等; 值与 `lev Ω₁` 相同 (`v-tw1`); 正规取 `Nm-tw`.

```agda
  one⊕ : (y : L) → one ⊕ y ≼ᴸ sc y
  one⊕ zero     = ≼ᴸ-refl one
  one⊕ (nd s h) = n≼ (λ c → tt , ≼ᴸ-trans (one⊕ (h c)) (n≼ (λ _ → c , ≼ᴸ-refl (h c))))

  v-tw1 : tw 1 ≈ᴸ lev Ω₁ᵗ
  v-tw1 = n≼ (λ c → c , up≼ tt (≼⊕ʳ one (zero ⊕ ↑ zero c))) ,
          n≼ (λ c → suc (suc c) , n≼ (λ _ → tt , one⊕ (zero ⊕ ↑ zero c)))

  rb : (c : Tr zero) (η : E.T) {ac : Acc _≺ᴸ_ zero} (o′ : Ok (zero ⊕ ↑ zero c)) (ac′ : Acc _≺ᴸ_ (zero ⊕ ↑ zero c))
     → Nmd zero tt ac c η → LvH (zero ⊕ ↑ zero c) o′ ac′ η
  rb zero η o′ ac′ (_ , _ , e) = e
  rb (suc c) η o′ (acc r′) (_ , _ , (c1e , nc)) = c1e , rb c (E.pred η) _ _ nc
  rb (lim f m) η o′ (acc r′) (_ , _ , (cωe , G , ng , tg , cg)) = cωe , G , (λ n → rb (f n) (G n) _ _ (ng n)) , tg , cg
  rb (Ω () g) η o′ ac′ n
  rb (up x () y e) η o′ ac′ n

  lvn-tw1 : (o : Ok (tw 1)) (ac : Acc _≺ᴸ_ (tw 1)) → LvN (tw 1) o ac Ω₁ᵗ
  lvn-tw1 o (acc r) = v-tw1 , Nm-tw 1 , [] , refl , refl , (λ η → η) , (λ c η nc → rb c η _ _ nc) ,
    (λ η nη lt → inj₂ refl , ET.T-self lt)
```
