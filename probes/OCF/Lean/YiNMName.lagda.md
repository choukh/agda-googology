# 命名关系与 B 的零行, 后继行

> 判决: 验收侧定义与编译定理, 条件 (排中律作模块参数), 读记号, 不进成品. 命名关系 `Nmd` 写得出: 对层号的 `Acc` 与树递归, (V) 严格值与项模型同值, (H) 按构造子遗传, 结点带函数 F 与夹逼 a[η] ≤ F(η) < a.
> 编译定理: B (名字经 ψ♯ 保持) 的零行 `zeroRow` 无额外前提; 后继行 `sucRow` 以 "命名对同一棵树的有限次树加法封闭" (`AddRep`) 为前提, 其中 (V) 是证出来的. 结点行只陈述 (`NodeRow`, 由 `KeepRow` 与 `ChainRow` 合成 `node-split`), 未证; A 只陈述.
> `AddRep` 未证, n = 0 的情形是恒等 (`addRep₀`). 这里的命名关系 (只有夹逼) 太宽: `YiNMAbsorb.B-false` 表明 `BRow` 在一棵纸面上有名字的树上不成立, 嵌入与结点两行要加条件 (候选是记号侧的 `Trian`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNMName where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
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
import OCF.Align.EboLeanDef as E
import OCF.Align.EBO as E0
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanTrian as ET
open EB using (NF; _≤ᵀ_)
```

## 记号侧: 后继项的余尾, 前驱, 基本列

```agda
cof-sucT : ∀ c → E.cof (E.sucT c) ≡ E.c1
cof-sucT []           = refl
cof-sucT (x ∷ [])     = refl
cof-sucT (x ∷ y ∷ ys) = cof-sucT (y ∷ ys)

pred-sucT : ∀ c → E.pred (E.sucT c) ≡ c
pred-sucT []           = refl
pred-sucT (x ∷ [])     = refl
pred-sucT (x ∷ y ∷ ys) = cong (x ∷_) (pred-sucT (y ∷ ys))

cofψ-sucT : ∀ u c → E.cof (E.ψ u (E.sucT c) ∷ []) ≡ E.cω
cofψ-sucT u []       = refl
cofψ-sucT u (z ∷ zs) = cong (E.cofA u) (cof-sucT (z ∷ zs))

fsn₊-c1 : ∀ u b {k} → E.cof b ≡ k → k ≡ E.c1 → ∀ n → E.fsn₊ u b k n ≡ replicate n (E.ψ u (E.pred b))
fsn₊-c1 u b refl e n = cong (λ k → E.fsn₊ u b k n) e

fsnψ-sucT : ∀ u c n → E.fsn (E.ψ u (E.sucT c) ∷ []) n ≡ replicate n (E.ψ u c)
fsnψ-sucT u []       n = refl
fsnψ-sucT u (z ∷ zs) n =
  trans (fsn₊-c1 u (E.sucT (z ∷ zs)) refl (cof-sucT (z ∷ zs)) n)
        (cong (λ t → replicate n (E.ψ u t)) (pred-sucT (z ∷ zs)))

rep-lt : ∀ (P : E.PT) n → replicate n P E.<ᵀ replicate (suc n) P
rep-lt P zero    = E.[]<
rep-lt P (suc n) = E.tl< (rep-lt P n)

nfψ-pred : ∀ {u} c → NF (E.ψ u (E.sucT c) ∷ []) → NF (E.ψ u c ∷ [])
nfψ-pred {u} c n = subst (λ t → NF (E.ψ u t ∷ [])) (pred-sucT c)
  (EB.nf-ψ (EB.nfp-u (EB.nf-hd n)) (EB.nf-pred (EB.nfp-a (EB.nf-hd n)))
           (ET.Gtri (ET.T-pred (E.sucT c) (cof-sucT c)) (EB.nfp-g (EB.nf-hd n)) EB.GB[]))
```

## 层号值的同余

```agda
≈ᴸ-sym : ∀ {a b} → a ≈ᴸ b → b ≈ᴸ a
≈ᴸ-sym (d , e) = e , d

⊕-cong : ∀ {a a′ b b′} → a ≈ᴸ a′ → b ≈ᴸ b′ → a ⊕ b ≈ᴸ a′ ⊕ b′
⊕-cong {a} {a′} {b} {b′} (d , d′) (e , e′) =
  ≼ᴸ-trans (⊕-monoˡ d b) (⊕-monoʳ a′ e) , ≼ᴸ-trans (⊕-monoˡ d′ b′) (⊕-monoʳ a e′)

↑-iter : ∀ {j j′} (b : Tr j) (b′ : Tr j′) → ↑ j b ≈ᴸ ↑ j′ b′
       → ∀ n → ↑ j (iter (b +_) b n) ≈ᴸ ↑ j′ (iter (b′ +_) b′ n)
↑-iter b b′ e zero = e
↑-iter {j} {j′} b b′ e (suc n) =
  ≈ᴸ-trans (↑-+ j b (iter (b +_) b n))
    (≈ᴸ-trans (⊕-cong e (↑-iter b b′ e n)) (≈ᴸ-sym (↑-+ j′ b′ (iter (b′ +_) b′ n))))
```

## 命名关系

层号: `LvN ℓ ν` 指 ℓ 与 `lev ν` 同值且 ℓ 正规 (`Nm`). 树: `Nmd ℓ o ac x a` 指 a 是标准形, (V) x 的严格值与 `⟦ a ⟧` 的严格值相同, (H) `Hd`. `Hd` 各行: 零对 0; 后继对后继项, 前驱有名字; ℕ 极限各项有名字 `G n`, 都低于 a 且在 a 的基本列里共尾; 结点的槽位层名为 κ (a 的余尾是 Ω_{κ+1}), 分支下标 z 名为 η 时分支名为 `F η`, 且 a[η] ≤ F(η) < a; 嵌入的两个成分各有名字, a 是它们的标准形的和. 结点一行在槽位层 (值严格更低) 上引用关系自己, 所以对 `Acc` 递归.

```agda
module Name (lem : LEM) where
  open Sharp lem
  open Term lem

  LvN : L → E.T → Set
  LvN ℓ ν = (ℓ ≈ᴸ lev ν) × Nm ℓ

  Vl : (ℓ : L) → Tr ℓ → E.T → Set
  Vl ℓ x a = ↑ ℓ x ≈ᴸ sv ⟦ a ⟧

  mutual
    Nmd : (ℓ : L) → Ok ℓ → Acc _≺ᴸ_ ℓ → Tr ℓ → E.T → Set
    Nmd ℓ o ac x a = NF a × Vl ℓ x a × Hd ℓ o ac x a

    Hd : (ℓ : L) → Ok ℓ → Acc _≺ᴸ_ ℓ → Tr ℓ → E.T → Set
    Hd ℓ o ac zero a = a ≡ []
    Hd ℓ o ac (suc x) a = (E.cof a ≡ E.c1) × Nmd ℓ o ac x (E.pred a)
    Hd ℓ o ac (lim f m) a = (E.cof a ≡ E.cω) × Σ (ℕ → E.T) λ G →
      ((n : ℕ) → Nmd ℓ o ac (f n) (G n)) × ((n : ℕ) → G n E.<ᵀ a) × ((n : ℕ) → Σ ℕ λ k → E.fsn a n ≤ᵀ G k)
    Hd ℓ o (acc r) (Ω p g) a = Σ E.T λ κ → (E.cof a ≡ E.cΩ κ) × LvN (at ℓ p) κ × Σ (E.T → E.T) λ F →
      ((z : Tr (at ℓ p)) (η : E.T) → Nmd (at ℓ p) (Ok-at ℓ o p) (r (posLt ℓ o p)) z η
         → Nmd ℓ o (acc r) (g (fromBr ℓ p z)) (F η))
      × ((η : E.T) → NF η → η E.<ᵀ E.Ωs κ → (E.fsT a η ≤ᵀ F η) × (F η E.<ᵀ a))
    Hd (nd s h) o (acc r) (up x c y e) a = Σ E.T λ a₁ → Σ E.T λ a₂ →
      Nmd (nd s h) o (acc r) x a₁ × Nmd (h c) (proj₂ o c) (r (c , ≼ᴸ-refl (h c))) y a₂ × (a ≡ a₁ ∔ a₂)

  Named : (ℓ : L) → Ok ℓ → Tr ℓ → E.T → Set
  Named ℓ o = Nmd ℓ o (wfL ℓ)
```

## 不变式 A 与 B 的陈述

A: 标准形上项模型读成的层号按记号的序严格单调. B 对一棵树 x 的陈述 `BRow D`: x 名为 a, 目标层名为 u, 底族 (在域 D 内, 下标不低于 u 的有名字的层上) 与底值名为 ψ(K), 且 ψ_u(K ∔ a) 是标准形, 则输出名为 ψ_u(K ∔ a). 域 D 是底族被问到的层号的范围: 只按值与正规定的 `LvN` 不保证层号的孩子有名字, 对一切 `LvN` 的层号要求底族有名字可能不可满足, 所以留作参数. `Acc` 的证明全称量化, 所以陈述不依赖用哪一个.

```agda
  AStmt : Set
  AStmt = ∀ s t → NF s → NF t → s E.<ᵀ t → lev s ≺ᴸ lev t

  CtxN : (L → Set) → Base♯ → E.T → E.T → Set
  CtxN D B K u = (i : L) (oi : Ok i) (aci : Acc _≺ᴸ_ i) (ι : E.T) → D i → LvN i ι → u ≤ᵀ ι
               → Nmd i oi aci (proj₁ (B i oi)) (E.ψ ι K ∷ [])

  BRowJ : (L → Set) → (L → Set) → (ℓ : L) → Ok ℓ → Tr ℓ → Set
  BRowJ Q D ℓ o x = (ac : Acc _≺ᴸ_ ℓ) (B : Base♯) (j : L) (oj : Ok j) (acj : Acc _≺ᴸ_ j) (β : Tr⁺ j)
      (a u K : E.T) → Q j → Nmd ℓ o ac x a → LvN j u → CtxN D B K u → Nmd j oj acj (proj₁ β) (E.ψ u K ∷ [])
    → NF (E.ψ u (K ∔ a) ∷ [])
    → Nmd j oj acj (proj₁ (ψ♯ ℓ o B j oj β x)) (E.ψ u (K ∔ a) ∷ [])

  BRow : (L → Set) → (ℓ : L) → Ok ℓ → Tr ℓ → Set
  BRow = BRowJ (λ _ → ⊤)
```

## 零行

x = 0 的名字只能是 0, K ∔ 0 = K, 输出就是底值.

```agda
  zeroRow : (D : L → Set) (ℓ : L) (o : Ok ℓ) → BRow D ℓ o zero
  zeroRow D ℓ o ac B j oj acj β a u K _ (_ , _ , refl) lj cx nβ nfo =
    subst (λ t → Nmd j oj acj (proj₁ β) (E.ψ u t ∷ [])) (sym (∔-[] K)) nβ
```

## 后继行

前提 `AddRep`: 名为主项 P 的树自加 n 次, 名为 P 重复 n+1 次. 核心 `suc-core`: b 名为 ψ_u(c), 则 b·ω (`next⁺`) 名为 ψ_u(c+1). (V) 用 `⟦sucT⟧` (项模型里 c+1 的树是 c 的树的后继) 与 `↑-iter`; (H) 取 G n = ψ_u(c)·(n+1), 记号的基本列是 ψ_u(c)·n.

```agda
  AddRep : Set
  AddRep = (j : L) (oj : Ok j) (acj : Acc _≺ᴸ_ j) (b : Tr j) (P : E.PT) (n : ℕ)
         → Nmd j oj acj b (P ∷ []) → Nmd j oj acj (iter (b +_) b n) (replicate (suc n) P)

  addRep₀ : (j : L) (oj : Ok j) (acj : Acc _≺ᴸ_ j) (b : Tr j) (P : E.PT)
          → Nmd j oj acj b (P ∷ []) → Nmd j oj acj (iter (b +_) b zero) (replicate 1 P)
  addRep₀ j oj acj b P nb = nb

  foldM : E.T → M → M
  foldM u m = mk (lev u) (levOk u) (proj₁ (ψ♯ (lv m) (ok m) B♯ (lev u) (levOk u) (Ωt (lev u)) (tr m)))

  ⟦ψ⟧ : ∀ u a → ⟦ E.ψ u a ∷ [] ⟧ ≡ foldM u ⟦ a ⟧
  ⟦ψ⟧ u a = refl

  suc-core : AddRep → (j : L) (oj : Ok j) (acj : Acc _≺ᴸ_ j) (b : Tr⁺ j) (u c : E.T)
           → Nmd j oj acj (proj₁ b) (E.ψ u c ∷ []) → NF (E.ψ u (E.sucT c) ∷ [])
           → Nmd j oj acj (proj₁ (next⁺ b)) (E.ψ u (E.sucT c) ∷ [])
  suc-core ar j oj acj b u c (nb , vb , hb) nfo = nfo , vv , hh
    where
    Pm : E.PT
    Pm = E.ψ u c
    bt : Tr (lev u)
    bt = tr (foldM u ⟦ c ⟧)
    vv : Vl j (proj₁ (next⁺ b)) (E.ψ u (E.sucT c) ∷ [])
    vv = subst (λ m → nd sL (λ n → ↑ j (iter (proj₁ b +_) (proj₁ b) n)) ≈ᴸ sv (foldM u m)) (sym (⟦sucT⟧ c))
           (nd-cong (↑-iter (proj₁ b) bt vb))
    hh : Hd j oj acj (proj₁ (next⁺ b)) (E.ψ u (E.sucT c) ∷ [])
    hh = cofψ-sucT u c , (λ n → replicate (suc n) Pm) ,
         (λ n → ar j oj acj (proj₁ b) Pm n (nb , vb , hb)) ,
         (λ n → E.hd< (E.ar< (E0.<-sucT c))) ,
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

## 其余各行的陈述 (未证)

结点行: 槽位层在域内, 一切分支都满足 B, 则结点满足 B. 按目标层与槽位层的值分成保留 (`KeepRow`, 槽位层严格更低) 与走链 (`ChainRow`); 经典二分把两支合成整行 (`node-split`). 链的回灌是同一分支朝槽位层的折叠, 已在 "一切分支满足 B (目标任意)" 里.

```agda
  NodeRow KeepRow ChainRow LimRow UpRow : Set₁
  NodeRow  = (D : L → Set) (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → D (at ℓ p)
           → ((z : Br ℓ p) → BRow D ℓ o (g z)) → BRow D ℓ o (Ω p g)
  KeepRow  = (D : L → Set) (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → D (at ℓ p)
           → ((z : Br ℓ p) → BRow D ℓ o (g z)) → BRowJ (λ j → at ℓ p ≺ᴸ j) D ℓ o (Ω p g)
  ChainRow = (D : L → Set) (ℓ : L) (o : Ok ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → D (at ℓ p)
           → ((z : Br ℓ p) → BRow D ℓ o (g z)) → BRowJ (λ j → j ≼ᴸ at ℓ p) D ℓ o (Ω p g)
  LimRow   = (D : L → Set) (ℓ : L) (o : Ok ℓ) (f : ℕ → Tr ℓ) (m : (n : ℕ) → ℓ ⊢ f n ◃ f (suc n))
           → ((n : ℕ) → BRow D ℓ o (f n)) → BRow D ℓ o (lim f m)
  UpRow    = (D : L → Set) (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (x : Tr (nd s h)) (c : Ch s) (y : Tr (h c))
             (e : h c ⊢ zero ◃ y)
           → BRow D (nd s h) o x → BRow D (h c) (proj₂ o c) y → BRow D (nd s h) o (up x c y e)

  node-split : KeepRow → ChainRow → NodeRow
  node-split kr cr D ℓ o p g dp ih ac B j oj acj β a u K _ =
    [ cr D ℓ o p g dp ih ac B j oj acj β a u K , kr D ℓ o p g dp ih ac B j oj acj β a u K ]′ (Dk j (at ℓ p))
```
