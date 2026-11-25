# 两条 ℕ 极限层号上的前缀：一切 n 的值界
不读记号；编译定理：两条 ℕ 极限层号 `nd sL g`、`nd sL h`，若相邻孩子按等式是后继一级（`Adj`）、`h n` 按等式是 `g n` 高两级（`eh`）、`g n` 是有限后继塔、两侧零层路径对齐（`Hw`），则第 0 项按 `N` 有序推出一切前缀 n 的值界（`mainV`）。
做法：前缀 m 沿第 n 支的折叠化成嵌入 Ω 树的折叠（`row`，经 `way-eq`），对 m 归纳用 `YiPTTow.step`（`CmpD`、`hb` 互递归），顶层用 `stepTop`。`Side` 照 `YiOFLimit.At` 逐字重写为透明定义。
不否定什么；实例在 [YiPTAll](YiPTAll.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPTChain where
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiVRRel using (NoΩ≤)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiLXClimb using (_⊴◃_)
open import OCF.Lean.YiRRRel
open import OCF.Lean.YiRRFold using (geβ)
open import OCF.Lean.YiPTLadder using (S1; S2; Tw; ups; ups′)
import OCF.Lean.YiVWVal as V
open import OCF.Lean.YiPTTow
```

## 一侧的前缀与折叠

```agda
module Side (k : ℕ → L) (o : Ok (nd sL k)) (w : (n : ℕ) → zero ≤ k n) where
  ℓ : L
  ℓ = nd sL k
  fold : Tr ℓ → Tr⁺ zero
  fold = ψ ℓ o (rbᶻ ℓ) (B₀ ℓ) zero (inu w) (Ωt zero)
  part : (n : ℕ) → Tr⁺ ℓ
  part n = upz n (Ωt (k n))
  prefix : ℕ → Tr ℓ
  prefix = cum (λ n → proj₁ (part n))
  piece : ℕ → Tr⁺ zero
  piece n = fold (prefix n)
  previous : ℕ → Tr ℓ
  previous zero = zero
  previous (suc n) = prefix n
  Fp : (n m : ℕ) → Base (k n)
  Fp n m i u = ψ ℓ o (rbᶻ ℓ) (B₀ ℓ) i (inc n u) (Ωt i) (prefix m)
  Bp : (n m : ℕ) → Base (k n)
  Bp n m i u = ψ ℓ o (rbᶻ ℓ) (B₀ ℓ) i (inc n u) (Ωt i) (previous m)
  Fb : (n m : ℕ) (i : L) (u : i ≤ k n) → k m ≤ k n → Tr⁺ i
  Fb n m i u v = ψ (k n) (proj₂ o n) (rbᶻ (k n)) (Bp n m) i u (Bp n m i u) (proj₁ (emb (k n) (proj₂ o n) v (Ωt (k m))))
  row : (m d : ℕ) (i : L) (u : i ≤ k (suc (m +ₙ d))) → Fp (suc (m +ₙ d)) m i u ≡ Fb (suc (m +ₙ d)) m i u (Pw k (proj₁ o) m d)
  row zero d i u = refl
  row (suc m) d i u = cWl {F = Fb (suc (suc m +ₙ d)) (suc m) i u} (way-eq k (proj₁ o) (suc m) d)
```

## 前提与逐级比较

`π n`: 源第 n 支的路径沿 `eh n` 拉到目标第 n 支 (上两级取 `inc`).

```agda
module Chain (g h : ℕ → L) (og : Ok (nd sL g)) (oh : Ok (nd sL h))
  (Hg : Adj g (proj₁ og)) (Hh : Adj h (proj₁ oh)) (eh : (n : ℕ) → h n ≡ S2 (g n)) (tg : (n : ℕ) → Tow (g n))
  (wg : (n : ℕ) → zero ≤ g n) (wh : (n : ℕ) → zero ≤ h n)
  (Hw : (n : ℕ) → subst (zero ≤_) (eh n) (wh n) ≡ inu (λ _ → inu (λ _ → wg n))) where
  module Src = Side g og wg
  module Tgt = Side h oh wh

  π : (n : ℕ) {i : L} → i ≤ g n → i ≤ h n
  π n {i} u = subst (i ≤_) (sym (eh n)) (inc tt (inc tt u))

  Cmp : ℕ → ℕ → Set
  Cmp n m = (i : L) (u : i ≤ g n) → N i (proj₁ (Src.Fp n m i u)) (proj₁ (Tgt.Fp n m i (π n u)))

  domT : (n m : ℕ) (i : L) (w : i ≤ h n) → proj₁ (Ωt i) ⊴◃ proj₁ (Tgt.Bp n m i w)
  domT n m i w = geβ Tgt.ℓ oh (rbᶻ Tgt.ℓ) (B₀ Tgt.ℓ) i (inc n w) (Ωt i) (Tgt.previous m)

  eS : (m d : ℕ) → g (suc (m +ₙ d)) ≡ Tw (g m) (suc d)
  eS m d = twr g (proj₁ og) Hg m d

  eT′ : (m d : ℕ) → h (suc (m +ₙ d)) ≡ S2 (Tw (g m) (suc d))
  eT′ m d = trans (twr h (proj₁ oh) Hh m d) (trans (cong (λ Z → Tw Z (suc d)) (eh m)) (swap (g m) (suc d)))

  Xt : (m d : ℕ) → Tr⁺ (h (suc (m +ₙ d)))
  Xt m d = emb (h (suc (m +ₙ d))) (proj₂ oh (suc (m +ₙ d))) (Pw h (proj₁ oh) m d) (Ωt (h m))

  treeT′ : (m d : ℕ) → subst Tr⁺ (eT′ m d) (Xt m d) ≡ ups′ (g m) (suc d)
  treeT′ m d = trans (sym (subst-subst {P = Tr⁺} (twr h (proj₁ oh) Hh m d)))
     (trans (cong (subst Tr⁺ (trans (cong (λ Z → Tw Z (suc d)) (eh m)) (swap (g m) (suc d)))) (tree h (proj₁ oh) Hh m d _))
       (trans (sym (subst-subst {P = Tr⁺} (cong (λ Z → Tw Z (suc d)) (eh m))))
         (trans (cong (subst Tr⁺ (swap (g m) (suc d))) (ups-cong (eh m) (suc d))) (ups-swap (g m) (suc d)))))

  treeT : (m d : ℕ) → subst Tr⁺ (trans (eh (suc (m +ₙ d))) (cong S2 (eS m d))) (Xt m d) ≡ ups′ (g m) (suc d)
  treeT m d = trans (cong (λ e → subst Tr⁺ e (Xt m d))
      (uipR (ts (ts (towTw (tg m) (suc d)))) (trans (eh (suc (m +ₙ d))) (cong S2 (eS m d))) (eT′ m d))) (treeT′ m d)
```

## 对前缀归纳

```agda
  mutual
    CmpD : (m d : ℕ) → Cmp (suc (m +ₙ d)) m
    CmpD m d i u = subst₂ (λ x y → N i (proj₁ x) (proj₁ y)) (sym (Src.row m d i u)) (sym (Tgt.row m d i (π (suc (m +ₙ d)) u)))
      (step (g m) (tg m) (suc d) (eS m d) (eh (suc (m +ₙ d))) (proj₂ og (suc (m +ₙ d))) (proj₂ oh (suc (m +ₙ d)))
         (rbᶻ (g (suc (m +ₙ d)))) (rbᶻ (h (suc (m +ₙ d)))) (Src.Bp (suc (m +ₙ d)) m) (Tgt.Bp (suc (m +ₙ d)) m)
         (emb (g (suc (m +ₙ d))) (proj₂ og (suc (m +ₙ d))) (Pw g (proj₁ og) m d) (Ωt (g m))) (Xt m d)
         (tree g (proj₁ og) Hg m d _) (treeT m d)
         (hb m d) (domT (suc (m +ₙ d)) m) i u (Src.Bp (suc (m +ₙ d)) m i u) (Tgt.Bp (suc (m +ₙ d)) m i (π (suc (m +ₙ d)) u)) (hb m d i u))

    hb : (m d : ℕ) (i : L) (u : i ≤ g (suc (m +ₙ d)))
       → N i (proj₁ (Src.Bp (suc (m +ₙ d)) m i u)) (proj₁ (Tgt.Bp (suc (m +ₙ d)) m i (π (suc (m +ₙ d)) u)))
    hb zero d i u = Ωt≼ i (NoΩ≤ u (towNoΩ (tg (suc d))))
    hb (suc m) d i u = subst (λ n → Cmp n m) (cong suc (+-suc m d)) (CmpD m (suc d)) i u

  CmpTop : (k : ℕ) → Cmp (suc k) k
  CmpTop k = subst (λ n → Cmp n k) (cong suc (+-identityʳ k)) (CmpD k zero)

  main : N zero (proj₁ (Src.piece 0)) (proj₁ (Tgt.piece 0)) → (n : ℕ) → N zero (proj₁ (Src.piece n)) (proj₁ (Tgt.piece n))
  main h0 zero = h0
  main h0 (suc k) = stepTop (tg (suc k)) (eh (suc k)) (proj₂ og (suc k)) (proj₂ oh (suc k)) (rbᶻ (g (suc k))) (rbᶻ (h (suc k)))
     (Src.Bp (suc k) (suc k)) (Tgt.Bp (suc k) (suc k)) (CmpTop k) (domT (suc k) (suc k)) (wg (suc k)) (wh (suc k)) (Hw (suc k))
     (Src.piece k) (Tgt.piece k) (main h0 k)

  mainV : N zero (proj₁ (Src.piece 0)) (proj₁ (Tgt.piece 0)) → (n : ℕ) → V.val zero (proj₁ (Src.piece n)) V.≼ V.val zero (proj₁ (Tgt.piece n))
  mainV h0 n = sound zero ser₀ (main h0 n)
```
