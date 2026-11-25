# 命名关系的重述 (◁ 与遗传的层号命名), B 的零行与后继行

> 判决: 验收侧定义与编译定理, 条件 (排中律作模块参数), 读记号, 不进成品. 相对 `YiNMName`: ℕ 极限, 结点, 嵌入三行的 "低于 a" 换成记号的 ◁ (`Trian`); 层号命名加遗传一项 `LvH` (层号按形状逐行有名字, Ω 形状的孩子随有名字的下标树有名字).
> 编译定理: 零行 `zeroRow` 无额外前提; 后继行 `sucRow` 以 `AddRep` (命名对同一棵树的有限次树加法封闭, 未证) 为前提. 结点行, ℕ 极限行, 嵌入行没有证.
> 不否定什么. V2 的反例在这里不成立, `tw 1` 的层号命名可填, 见 `YiNPAbsorb`; 这个关系在结点保留支上仍太宽 (`BRow` 有反例), 底族前提在第 1 层上是定理, 见 `YiNPWild`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNPName where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Induction.WellFounded using (Acc; acc)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRVLevel
open import OCF.Lean.YiNMSharp
open import OCF.Lean.YiNMTerm
open import OCF.Lean.YiNMName using (cof-sucT; pred-sucT; cofψ-sucT; fsnψ-sucT; rep-lt; nfψ-pred; ≈ᴸ-sym; ↑-iter)
import OCF.Align.EboLeanDef as E
import OCF.Align.EBO as E0
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanTrian as ET
open EB using (NF; _≤ᵀ_)
```

## 命名关系

`LvH ℓ ν`: 层号 ℓ 按形状遗传地名为 ν. 零对 0; 后继形状对后继项; ℕ 极限形状各孩子名为 `G n`, `G n ◁₀ ν` 且在 ν 的基本列里共尾; Ω 形状的下标层名为 κ, 下标树 c 名为 η 时孩子 `h c` 名为 `F η`, 且 ν[η] ≤ F(η), F(η) ◁_η ν. `LvN` 再带值 (与 `lev ν` 同值) 与正规. 树的 `Hd` 相对 `YiNMName`: ℕ 极限行的 `G n < a` 换成 `G n ◁₀ a`; 结点行的 `F η < a` 换成 `F η ◁_η a`; 嵌入行加 `a₁ ◁₀ a` (左项不被吸收时它由 `T-cons` 自动成立, 被吸收时是限制). 三者都对层号的 `Acc` 递归.

```agda
module NameP (lem : LEM) where
  open Sharp lem
  open Term lem

  Vl : (ℓ : L) → Tr ℓ → E.T → Set
  Vl ℓ x a = ↑ ℓ x ≈ᴸ sv ⟦ a ⟧

  k≺ : ∀ {k h} (o : Ok (nd (sΩ k) h)) → k ≺ᴸ nd (sΩ k) h
  k≺ {k} {h} o = posLt (nd (sΩ k) h) o (inj₁ (inj₁ tt))

  mutual
    LvH : (ℓ : L) → Ok ℓ → Acc _≺ᴸ_ ℓ → E.T → Set
    LvH zero o ac ν = ν ≡ []
    LvH (nd sS h) o (acc r) ν = (E.cof ν ≡ E.c1) × LvH (h tt) (proj₂ o tt) (r (tt , ≼ᴸ-refl (h tt))) (E.pred ν)
    LvH (nd sL g) o (acc r) ν = (E.cof ν ≡ E.cω) × Σ (ℕ → E.T) λ G →
      ((n : ℕ) → LvH (g n) (proj₂ o n) (r (n , ≼ᴸ-refl (g n))) (G n))
      × ((n : ℕ) → ET.Trian [] (G n) ν) × ((n : ℕ) → Σ ℕ λ m → E.fsn ν n ≤ᵀ G m)
    LvH (nd (sΩ k) h) o (acc r) ν = Σ E.T λ κ → (E.cof ν ≡ E.cΩ κ) × LvH k (proj₁ (proj₁ o)) (r (k≺ o)) κ
      × Σ (E.T → E.T) λ F →
        ((c : Tr k) (η : E.T) → Nmd k (proj₁ (proj₁ o)) (r (k≺ o)) c η → LvH (h c) (proj₂ o c) (r (c , ≼ᴸ-refl (h c))) (F η))
        × ((η : E.T) → NF η → η E.<ᵀ E.Ωs κ → (E.fsT ν η ≤ᵀ F η) × ET.Trian η (F η) ν)

    LvN : (ℓ : L) → Ok ℓ → Acc _≺ᴸ_ ℓ → E.T → Set
    LvN ℓ o ac ν = (ℓ ≈ᴸ lev ν) × Nm ℓ × LvH ℓ o ac ν

    Nmd : (ℓ : L) → Ok ℓ → Acc _≺ᴸ_ ℓ → Tr ℓ → E.T → Set
    Nmd ℓ o ac x a = NF a × Vl ℓ x a × Hd ℓ o ac x a

    Hd : (ℓ : L) → Ok ℓ → Acc _≺ᴸ_ ℓ → Tr ℓ → E.T → Set
    Hd ℓ o ac zero a = a ≡ []
    Hd ℓ o ac (suc x) a = (E.cof a ≡ E.c1) × Nmd ℓ o ac x (E.pred a)
    Hd ℓ o ac (lim f m) a = (E.cof a ≡ E.cω) × Σ (ℕ → E.T) λ G →
      ((n : ℕ) → Nmd ℓ o ac (f n) (G n)) × ((n : ℕ) → ET.Trian [] (G n) a) × ((n : ℕ) → Σ ℕ λ k → E.fsn a n ≤ᵀ G k)
    Hd ℓ o (acc r) (Ω p g) a = Σ E.T λ κ → (E.cof a ≡ E.cΩ κ) × LvN (at ℓ p) (Ok-at ℓ o p) (r (posLt ℓ o p)) κ
      × Σ (E.T → E.T) λ F →
        ((z : Tr (at ℓ p)) (η : E.T) → Nmd (at ℓ p) (Ok-at ℓ o p) (r (posLt ℓ o p)) z η
           → Nmd ℓ o (acc r) (g (fromBr ℓ p z)) (F η))
        × ((η : E.T) → NF η → η E.<ᵀ E.Ωs κ → (E.fsT a η ≤ᵀ F η) × ET.Trian η (F η) a)
    Hd (nd s h) o (acc r) (up x c y e) a = Σ E.T λ a₁ → Σ E.T λ a₂ →
      Nmd (nd s h) o (acc r) x a₁ × Nmd (h c) (proj₂ o c) (r (c , ≼ᴸ-refl (h c))) y a₂
      × (a ≡ a₁ ∔ a₂) × ET.Trian [] a₁ a
```

## B 的陈述

与 `YiNMName.BRow` 同形, 换成新的 `Nmd`, `LvN`. 结点一行要的 "ψ_u(K) 是标准形" 已在底值的前提里 (`Nmd` 的第一项). 域 D 仍留作参数.

```agda
  CtxN : (L → Set) → Base♯ → E.T → E.T → Set
  CtxN D B K u = (i : L) (oi : Ok i) (aci : Acc _≺ᴸ_ i) (ι : E.T) → D i → LvN i oi aci ι → u ≤ᵀ ι
               → Nmd i oi aci (proj₁ (B i oi)) (E.ψ ι K ∷ [])

  BRowJ : (L → Set) → (L → Set) → (ℓ : L) → Ok ℓ → Tr ℓ → Set
  BRowJ Q D ℓ o x = (ac : Acc _≺ᴸ_ ℓ) (B : Base♯) (j : L) (oj : Ok j) (acj : Acc _≺ᴸ_ j) (β : Tr⁺ j)
      (a u K : E.T) → Q j → Nmd ℓ o ac x a → LvN j oj acj u → CtxN D B K u → Nmd j oj acj (proj₁ β) (E.ψ u K ∷ [])
    → NF (E.ψ u (K ∔ a) ∷ [])
    → Nmd j oj acj (proj₁ (ψ♯ ℓ o B j oj β x)) (E.ψ u (K ∔ a) ∷ [])

  BRow : (L → Set) → (ℓ : L) → Ok ℓ → Tr ℓ → Set
  BRow = BRowJ (λ _ → ⊤)
```

## 零行与后继行

零行同 `YiNMName`. 后继行: 输出的 ℕ 极限行取 G n = ψ_u(c)·(n+1); 它对 ψ_u(c+1) 的 ◁₀ 由记号侧的 `T-rep`, `T-psi`, `T-pred` 给出 (与 `EboLeanClosure.Tω` 的规则 4 一支同一条).

```agda
  zeroRow : (D : L → Set) (ℓ : L) (o : Ok ℓ) → BRow D ℓ o zero
  zeroRow D ℓ o ac B j oj acj β a u K _ (_ , _ , refl) lj cx nβ nfo =
    subst (λ t → Nmd j oj acj (proj₁ β) (E.ψ u t ∷ [])) (sym (∔-[] K)) nβ

  AddRep : Set
  AddRep = (j : L) (oj : Ok j) (acj : Acc _≺ᴸ_ j) (b : Tr j) (P : E.PT) (n : ℕ)
         → Nmd j oj acj b (P ∷ []) → Nmd j oj acj (iter (b +_) b n) (replicate (suc n) P)

  foldM : E.T → M → M
  foldM u m = mk (lev u) (levOk u) (proj₁ (ψ♯ (lv m) (ok m) B♯ (lev u) (levOk u) (Ωt (lev u)) (tr m)))

  suc-core : AddRep → (j : L) (oj : Ok j) (acj : Acc _≺ᴸ_ j) (b : Tr⁺ j) (u c : E.T)
           → Nmd j oj acj (proj₁ b) (E.ψ u c ∷ []) → NF (E.ψ u (E.sucT c) ∷ [])
           → Nmd j oj acj (proj₁ (next⁺ b)) (E.ψ u (E.sucT c) ∷ [])
  suc-core ar j oj acj b u c (nb , vb , hb) nfo = nfo , vv , hh
    where
    Pm : E.PT
    Pm = E.ψ u c
    vv : Vl j (proj₁ (next⁺ b)) (E.ψ u (E.sucT c) ∷ [])
    vv = subst (λ m → nd sL (λ n → ↑ j (iter (proj₁ b +_) (proj₁ b) n)) ≈ᴸ sv (foldM u m)) (sym (⟦sucT⟧ c))
           (nd-cong (↑-iter (proj₁ b) (tr (foldM u ⟦ c ⟧)) vb))
    t1 : ET.Trian [] (Pm ∷ []) (E.ψ u (E.sucT c) ∷ [])
    t1 = subst (λ t → ET.Trian [] (E.ψ u t ∷ []) (E.ψ u (E.sucT c) ∷ [])) (pred-sucT c)
           (ET.T-psi u (ET.T-pred (E.sucT c) (cof-sucT c)))
    hh : Hd j oj acj (proj₁ (next⁺ b)) (E.ψ u (E.sucT c) ∷ [])
    hh = cofψ-sucT u c , (λ n → replicate (suc n) Pm) ,
         (λ n → ar j oj acj (proj₁ b) Pm n (nb , vb , hb)) ,
         (λ n → ET.T-rep t1 (suc n) (E.hd< (E.ar< (E0.<-sucT c)))) ,
         (λ n → n , subst (_≤ᵀ replicate (suc n) Pm) (sym (fsnψ-sucT u c n)) (inj₁ (rep-lt Pm n)))

  sucRow : AddRep → (D : L → Set) (ℓ : L) (o : Ok ℓ) (x : Tr ℓ) → BRow D ℓ o x → BRow D ℓ o (suc x)
  sucRow ar D ℓ o x ih ac B j oj acj β a u K _ (na , va , (e , nx)) lj cx nβ nfo =
    subst (λ t → Nmd j oj acj (proj₁ (next⁺ (ψ♯ ℓ o B j oj β x))) (E.ψ u t ∷ [])) (sym eq)
      (suc-core ar j oj acj (ψ♯ ℓ o B j oj β x) u (K ∔ E.pred a)
        (ih ac B j oj acj β (E.pred a) u K tt nx lj cx nβ (nfψ-pred (K ∔ E.pred a) nfo′)) nfo′)
    where
    eq : K ∔ a ≡ E.sucT (K ∔ E.pred a)
    eq = trans (cong (K ∔_) (sym (E0.pred-suc a e))) (∔-sucT K (E.pred a))
    nfo′ : NF (E.ψ u (E.sucT (K ∔ E.pred a)) ∷ [])
    nfo′ = subst (λ t → NF (E.ψ u t ∷ [])) eq nfo
```
