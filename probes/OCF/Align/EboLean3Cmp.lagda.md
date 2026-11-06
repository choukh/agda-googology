# EboLean3Cmp: `EBO-tree″` 与 `EBO-tree′` 的 FGH 逐点相同

> **记号侧验收工作**, 读记号, 不进成品, **不计入** [EboLean3](EboLean3.lagda.md) 的行数表 (它导入旧路线 [EboLeanTree](EboLeanTree.lagda.md), 后者经 τ 导入 Setzer 的 OT_I, 只为核对).
>
> **结论 (编译过的定理).** `fgh≡ : FGH EBO-tree″ n ≡ EboLeanTree.FGH EBO-tree′ n` 对一切 $n$. 两棵树都是 `lim (k ↦ tree (h_k))`, $h_k$ 是 `HC (EBOψ k)` 的两个推导 (一个来自本路线的 `wf`, 一个来自 τ 路线的 `wfNF′`); 沿 `HC` 的 `fgh` 与推导无关 (`fgh-irr`: `cof t` 的三种值互斥), 所以 FGH 相同. 不用函数外延.
>
> `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3Cmp where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import OCF.Align.EboLeanDef using (T; HC; h0; h1; hω; fgh; Cof; c0; c1; cω; cof; EBOψ)
open import OCF.Align.EboLean3Tree using (FGH; EBO-tree″; fgh-EBO″; hc-tower; iter-ext)
import OCF.Align.EboLeanTree as LT

c≢ : ∀ {t c c′} → cof t ≡ c → cof t ≡ c′ → c ≡ c′
c≢ e e′ = trans (sym e) e′

fgh-irr : ∀ {t} (h h′ : HC t) n → fgh t h n ≡ fgh t h′ n
fgh-irr (h0 _)   (h0 _)    n = refl
fgh-irr (h1 _ h) (h1 _ h′) n = iter-ext (fgh-irr h h′) n n
fgh-irr (hω _ h) (hω _ h′) n = fgh-irr (h n) (h′ n) n
fgh-irr (h0 e) (h1 e′ _) n with c≢ e e′
... | ()
fgh-irr (h0 e) (hω e′ _) n with c≢ e e′
... | ()
fgh-irr (h1 e _) (h0 e′) n with c≢ e e′
... | ()
fgh-irr (h1 e _) (hω e′ _) n with c≢ e e′
... | ()
fgh-irr (hω e _) (h0 e′) n with c≢ e e′
... | ()
fgh-irr (hω e _) (h1 e′ _) n with c≢ e e′
... | ()

fgh≡ : ∀ n → FGH EBO-tree″ n ≡ LT.FGH LT.EBO-tree′ n
fgh≡ n = trans (fgh-EBO″ n) (trans (fgh-irr (hc-tower n) (LT.hc-tower n) n) (sym (LT.fgh-EBO′ n)))
```
