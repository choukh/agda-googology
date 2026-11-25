# YiKB 验收: 龙骨判据的陈述, 条件出口, ε₀ 锚点

> 验收文件 (读记号, 不进成品). 判决: `K 1`, `K 2` 与步骤引理 **未证** (只是 `Set`). 编译定理, 无前提: 塔第 1 项不低于 ψ₀(Ω) = ε₀ 的参照 (`anchor`); 条件定理: 一切 `K (n+1)` 推出 EBO 参照树不高于 Λ 的闭项 (`keel→ebo`, 前提未证).
> 做了什么: 只含下标 0 的记号项 (`C0`) 读成第 0 层树 `ev`, 对 `pred`/`fsn` 封闭且值不升 (`closed-P`), 经 `YiMonoExit.exit` 得锚点.
> 不否定什么, 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKBAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List.Base using (List; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiKBBlock
open import OCF.Lean.YiKBFold
open import OCF.Lean.YiKBProps as P using (_≼ᵗ_; rfl)
open import OCF.Lean.YiKBRead

import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; cof; cofA; fsn; fsn₊; pred; EBOψ; ΩTower; γT; ψ; 𝟏; c0; c1; cω; cΩ)
open import OCF.Align.EboLeanTree using (hc-tower; EBO-tree′)
open import OCF.Lean.YiRefTw2 using (Rt; endpoint; fs≼; tree-≼; hω-inv)
open import OCF.Lean.YiMonoExit using (toL; Closed; exit)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans)
```

## 判据的陈述

`K n`: 塔第 n 项的闭项不低于 EBO 基本列第 n+1 行的参照. `K 1` 是 ψ₀(Ω_Ω), `K 2` 是 ψ₀(Ω_{Ω_Ω}). 都未证.

```agda
K : ℕ → Set
K n = (h : HC (EBOψ (suc n))) → Rt h ≼ read (twᶜ n)
```

## 只含下标 0 的项读成第 0 层树

`ev t acc` 读作 `acc + t`: 逐项 `acc ↦ acc + ω^b`. 这与折叠在第 0 层的 `E` 是同一个运算.

```agda
data C0 : E.T → Set where
  k[] : C0 []
  k∷  : ∀ {b xs} → C0 b → C0 xs → C0 (ψ [] b ∷ xs)

ev  : E.T → T₀ → T₀
evP : E.PT → T₀ → T₀
ev []       acc = acc
ev (x ∷ xs) acc = ev xs (evP x acc)
evP (ψ u b) acc = E rf′ acc (ev b zero)

noΩ-A : ∀ c → (∀ μ → c ≡ cΩ μ → ⊥) → ∀ μ → cofA [] c ≡ cΩ μ → ⊥
noΩ-A c0     n μ ()
noΩ-A c1     n μ ()
noΩ-A cω     n μ ()
noΩ-A (cΩ ν) n μ _ = n ν refl

noΩ : ∀ {t} → C0 t → ∀ μ → cof t ≡ cΩ μ → ⊥
noΩ k[] μ ()
noΩ (k∷ {b = []} k[] k[]) μ ()
noΩ (k∷ {b = _ ∷ _} kb k[]) μ e = noΩ-A _ (noΩ kb) μ e
noΩ (k∷ kb ks@(k∷ _ _)) μ e = noΩ ks μ e

no0-A : ∀ c → (∀ μ → c ≡ cΩ μ → ⊥) → cofA [] c ≡ c0 → ⊥
no0-A c0     n ()
no0-A c1     n ()
no0-A cω     n ()
no0-A (cΩ ν) n _ = n ν refl

no0 : ∀ {y ys} → C0 (y ∷ ys) → cof (y ∷ ys) ≡ c0 → ⊥
no0 (k∷ {b = []} k[] k[]) ()
no0 (k∷ {b = _ ∷ _} kb k[]) e = no0-A _ (noΩ kb) e
no0 (k∷ kb ks@(k∷ _ _)) e = no0 ks e

no1-A : ∀ c → (∀ μ → c ≡ cΩ μ → ⊥) → cofA [] c ≡ c1 → ⊥
no1-A c0     n ()
no1-A c1     n ()
no1-A cω     n ()
no1-A (cΩ ν) n _ = n ν refl
```

后继: `pred` 剥掉末尾的 1, 读回恰好少一个后继.

```agda
pred-ev : ∀ {t} → C0 t → cof t ≡ c1 → ∀ acc → ev t acc ≡ suc (ev (pred t) acc)
pred-ev k[] () acc
pred-ev (k∷ {b = []} k[] k[]) e acc = refl
pred-ev (k∷ {b = _ ∷ _} kb k[]) e acc = ⊥-elim (no1-A _ (noΩ kb) e)
pred-ev (k∷ {b = b} kb ks@(k∷ _ _)) e acc = pred-ev ks e (E rf′ acc (ev b zero))

C0-pred : ∀ {t} → C0 t → C0 (pred t)
C0-pred k[] = k[]
C0-pred (k∷ {b = []} k[] k[]) = k[]
C0-pred (k∷ {b = _ ∷ _} kb k[]) = k∷ kb k[]
C0-pred (k∷ kb ks@(k∷ _ _)) = k∷ kb (C0-pred ks)
```

极限: 规则 4 的 `replicate n` 读成 `E` 在后继上的第 n 次迭代, 规则 5 (ω) 用 `E-mono`. 这两条规则在证明里出现, 不在折叠的定义里.

```agda
iter-comm : ∀ {A : Set} (f : A → A) n a → iter f n (f a) ≡ f (iter f n a)
iter-comm f zero    a = refl
iter-comm f (suc n) a = cong f (iter-comm f n a)

rep-ev : ∀ p n acc → ev (replicate n (ψ [] p)) acc ≡ iter (λ r → E rf′ r (ev p zero)) n acc
rep-ev p zero    acc = refl
rep-ev p (suc n) acc = trans (rep-ev p n _) (iter-comm (λ r → E rf′ r (ev p zero)) n acc)

C0-rep : ∀ {p} → C0 p → ∀ n → C0 (replicate n (ψ [] p))
C0-rep kp zero    = k[]
C0-rep kp (suc n) = k∷ kp (C0-rep kp n)

fsn-ev  : ∀ {t} → C0 t → cof t ≡ cω → ∀ n acc → ev (fsn t n) acc ≼ᵗ ev t acc
fsn₊-ev : ∀ {y ys} → C0 (y ∷ ys) → ∀ c → cof (y ∷ ys) ≡ c → ∀ n acc →
          ev (fsn₊ [] (y ∷ ys) c n) acc ≼ᵗ E rf′ acc (ev (y ∷ ys) zero)
fsn-ev k[] () n acc
fsn-ev (k∷ {b = []} k[] k[]) () n acc
fsn-ev (k∷ {b = _ ∷ _} kb k[]) e n acc = fsn₊-ev kb _ refl n acc
fsn-ev (k∷ {b = b} kb ks@(k∷ _ _)) e n acc = fsn-ev ks e n (E rf′ acc (ev b zero))
fsn₊-ev kb c0 e n acc = ⊥-elim (no0 kb e)
fsn₊-ev {y = y} {ys = ys} kb c1 e n acc = let b = y ∷ ys in
  subst (λ X → ev (replicate n (ψ [] (pred b))) acc ≼ᵗ E rf′ acc X) (sym (pred-ev kb e zero))
    (P.≼l n (subst (λ Y → ev (replicate n (ψ [] (pred b))) acc ≼ᵗ Y) (rep-ev (pred b) n acc) (rfl _)))
fsn₊-ev kb cω e n acc = E-mono (rfl acc) (fsn-ev kb e n zero)
fsn₊-ev kb (cΩ ν) e n acc = ⊥-elim (noΩ kb ν e)

C0-fsn  : ∀ {t} → C0 t → cof t ≡ cω → ∀ n → C0 (fsn t n)
C0-fsn₊ : ∀ {b} → C0 b → ∀ c → cof b ≡ c → ∀ n → C0 (fsn₊ [] b c n)
C0-fsn k[] () n
C0-fsn (k∷ {b = []} k[] k[]) () n
C0-fsn (k∷ {b = _ ∷ _} kb k[]) e n = C0-fsn₊ kb _ refl n
C0-fsn (k∷ kb ks@(k∷ _ _)) e n = k∷ kb (C0-fsn ks e n)
C0-fsn₊ kb c0 e n = k[]
C0-fsn₊ kb c1 e n = C0-rep (C0-pred kb) n
C0-fsn₊ kb cω e n = k∷ (C0-fsn kb e n) k[]
C0-fsn₊ kb (cΩ ν) e n = ⊥-elim (noΩ kb ν e)
```

## 封闭的一族与 ε₀ 锚点

```agda
PK : E.T → L.Ordᶜ L.zero → Set
PK t X = C0 t × (read (ev t zero) ≼ X)

closed-P : Closed PK
closed-P = record { step1 = st1 ; stepω = stω }
  where
  st1 : ∀ {t X} → PK t X → cof t ≡ c1 → Σ (L.Ordᶜ L.zero) λ X′ → PK (pred t) X′ × (L.suc X′ ≼ X)
  st1 {t = t} {X = X} (k , q) e = read (ev (pred t) zero) , (C0-pred k , ≼-refl _) ,
    subst (λ Y → read Y ≼ X) (pred-ev k e zero) q
  stω : ∀ {t X} → PK t X → cof t ≡ cω → ∀ n → Σ (L.Ordᶜ L.zero) λ X′ → PK (fsn t n) X′ × (X′ ≼ X)
  stω {t = t} (k , q) e n = read (ev (fsn t n) zero) , (C0-fsn k e n , ≼-refl _) ,
    ≼-trans (≼ᵗ→≼ (fsn-ev k e n zero)) q
```

记号的 γ 链在 ψ₀(Ω) 这一行是 1, ψ₀(1), ψ₀(ψ₀(1)), …; 折叠的对角列是 `one`, `E one one`, …. 逐项不高.

```agda
one : T₀
one = suc zero

γC : ∀ n → C0 (γT (ΩTower 1) [] n)
γC zero    = k∷ k[] k[]
γC (suc n) = k∷ (γC n) k[]

γev : ∀ n → ev (γT (ΩTower 1) [] n) zero ≼ᵗ iter (λ x → E rf′ one x) n one
γev zero    = rfl one
γev (suc n) = E-mono P.z≼ (γev n)

anchor : (h : HC (EBOψ 1)) → Rt h ≼ read (twᶜ 1)
anchor (h0 ())
anchor (h1 () _)
anchor (hω _ hs) = l≼ (λ n → exit closed-P
  (γC (suc n) , ≼-trans (≼ᵗ→≼ (γev (suc n))) (≼l 1 (≼l 1 (≼l (suc n) (≼-refl _))))) (hs n))
```

## 条件出口

一切 `K (n+1)` 给出 EBO 参照树的下界. 第 0, 1 行由锚点给出. 前提未证, 所以这只是蕴涵.

```agda
low0 : Rt (hc-tower 0) ≼ Rt (hc-tower 1)
low0 = ≼-trans (tree-≼ refl (hc-tower 0) (hω-inv (hc-tower 1) refl 0)) (fs≼ (hc-tower 1) refl 0)

keel→ebo : (∀ n → K (suc n)) → toL EBO-tree′ ≼ read EBOᶜ
keel→ebo r = endpoint (read EBOᶜ) rows
  where
  rows : ∀ k → Rt (hc-tower k) ≼ read EBOᶜ
  rows zero          = ≼-trans low0 (≼-trans (anchor (hc-tower 1)) (into 1))
  rows (suc zero)    = ≼-trans (anchor (hc-tower 1)) (into 1)
  rows (suc (suc n)) = ≼-trans (r n (hc-tower (suc (suc n)))) (into (suc n))
```
