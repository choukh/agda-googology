# 紧界树比值 (四): 占位 $0$ 的树没有证书

> [TightVal](TightVal.lagda.md) 的第四篇. [TightValCap](TightValCap.lagda.md) 的上界带证书前提. 本文说这个前提在 $\Omega_3$ 处就无居留: `ψᵉ′` 的占位 $0$ 破坏极限节点的单调. **`no-low`, `no-Ω₃`: 在给定的具体环境上, $\psi_0(\psi_\Omega(\psi_2(1)))$ 与 $\psi_0(\psi_\Omega(\Omega_3))$ 的紧界树没有 `Goodᴺ`.**
>
> 坏节点是 $W=\psi_0(\psi_\Omega(\Omega_2+\omega))$: 第 $0$ 项 $\psi_0(\psi_\Omega(\Omega_2))$, 第 $1$ 项是占位 $0$. `gl` 要第 0 项 $\sqsubseteq$ 第 1 项, 假. 它在 `lowˢ` 里的位置是 $[2,0,2,0,0,1,0,0]$, `refl` 算出.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 不读记号的定义. 路径是 `refl`, 否定是定理, 只对写明的具体环境. 一切环境的版本在 [TightValGlobal](TightValGlobal.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ; sqˢ; walkˢ; Kind; kind; kz; ks; kl)
open import OCF.Align.NotFree using (Goodᴺ; gz; gs; gl; gc; forceᴺ)
open import OCF.Align.OmegaExpBase using (∅ˢ)
open import OCF.Align.OmegaSqBase using (ψᵉ′; lowˢ; z3; three)
```

## §1 沿路径取证书, 读前驱

```agda
sqG : (x : Ordˢ zero) (n : ℕ) → Goodᴺ (toZ x) → Goodᴺ (toZ (sqˢ x n))
sqG Ord₊ˢ.zero n G = G
sqG (Ord₊ˢ.suc x) n G = G
sqG (Ord₊ˢ.lim f) n (gl G st) = G n
sqG (Ord₊ˢ.limᵢ () f) n G
sqG (Ord₊ˢ.up () x) n G
sqG (Ord₊ˢ.ŝ c t₀ g) zero (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Go₀
sqG (Ord₊ˢ.ŝ c t₀ g) (suc n) G = G
sqG (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) zero (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) = Go₀
sqG (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) (suc n) G = G

walkG : (x : Ordˢ zero) (p : List ℕ) → Goodᴺ (toZ x) → Goodᴺ (toZ (walkˢ x p))
walkG x []      G = G
walkG x (n ∷ p) G = walkG (sqˢ x n) p (sqG x n G)

Has : Ordᶜ zero → Set
Has a = Σ (Ordᶜ zero) λ c → c ≺ a

hasW : (x : Ordˢ zero) (p : List ℕ) (G : Goodᴺ (toZ x)) → kind (walkˢ x p) ≡ ks → Has (forceᴺ _ G)
hasW Ord₊ˢ.zero [] G ()
hasW (Ord₊ˢ.suc x) [] (gs G) e = forceᴺ _ G , ≺z (≅-refl⁰ _)
hasW (Ord₊ˢ.lim f) [] G ()
hasW (Ord₊ˢ.limᵢ () f) [] G e
hasW (Ord₊ˢ.up () x) [] G e
hasW (Ord₊ˢ.ŝ c t₀ g) [] G ()
hasW (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) [] G ()
hasW Ord₊ˢ.zero (n ∷ p) G e = hasW Ord₊ˢ.zero p G e
hasW (Ord₊ˢ.suc x) (n ∷ p) G e = hasW (Ord₊ˢ.suc x) p G e
hasW (Ord₊ˢ.lim f) (n ∷ p) (gl G st) e with hasW (f n) p (G n) e
... | c , h = c , ≺l n h
hasW (Ord₊ˢ.limᵢ () f) (n ∷ p) G e
hasW (Ord₊ˢ.up () x) (n ∷ p) G e
hasW (Ord₊ˢ.ŝ c′ t₀ g) (zero ∷ p) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) e with hasW t₀ p Go₀ e
... | c , h = c , ≺l 0 h
hasW (Ord₊ˢ.ŝ c t₀ g) (suc n ∷ p) G e = hasW (Ord₊ˢ.ŝ c t₀ g) p G e
hasW (Ord₊ˢ.ĉᴸ c′ t₀ g o₀ o) (zero ∷ p) (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) e with hasW o₀ p Go₀ e
... | c , h = c , ≺l 0 h
hasW (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) (suc n ∷ p) G e = hasW (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) p G e

kz-empty : (y : Ordˢ zero) → kind y ≡ kz → (G : Goodᴺ (toZ y)) → Has (forceᴺ _ G) → ⊥
kz-empty Ord₊ˢ.zero e gz (c , ())
kz-empty (Ord₊ˢ.suc y) () G h
kz-empty (Ord₊ˢ.lim f) () G h
kz-empty (Ord₊ˢ.limᵢ () f) e G h
kz-empty (Ord₊ˢ.up () x) e G h
kz-empty (Ord₊ˢ.ŝ c t₀ g) () G h
kz-empty (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) () G h
```

## §2 坏节点

`mono-bad`: 极限节点的第 0 项沿某条路到后继 (所以非零), 第 1 项字面是 $0$, 就没有证书.

```agda
mono-bad : (x : Ordˢ zero) (p : List ℕ) → kind x ≡ kl → kind (walkˢ (sqˢ x 0) p) ≡ ks → kind (sqˢ x 1) ≡ kz → Goodᴺ (toZ x) → ⊥
mono-bad (Ord₊ˢ.lim f) p _ e₀ e₁ (gl G st) with hasW (f 0) p (G 0) e₀
... | c , h = kz-empty (f 1) e₁ (G 1) (c , st 0 h)
mono-bad Ord₊ˢ.zero p () e₀ e₁ G
mono-bad (Ord₊ˢ.suc x) p () e₀ e₁ G
mono-bad (Ord₊ˢ.limᵢ () f) p _ e₀ e₁ G
mono-bad (Ord₊ˢ.up () x) p _ e₀ e₁ G
mono-bad (Ord₊ˢ.ŝ c t₀ g) p () e₀ e₁ G
mono-bad (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) p () e₀ e₁ G

toW : List ℕ
toW = 2 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ []

W : Ordˢ zero
W = walkˢ lowˢ toW

no-W : Goodᴺ (toZ W) → ⊥
no-W = mono-bad W (0 ∷ 0 ∷ 0 ∷ []) refl refl refl

no-low : Goodᴺ (toZ lowˢ) → ⊥
no-low G = no-W (walkG lowˢ toW G)
```

**读法.** `W` 里 $\psi_0(\psi_\Omega(\Omega_2+0))$ 的第 $[0,0,0]$ 项是 `suc zero`, 所以它非零; $\psi_0(\psi_\Omega(\Omega_2+1))$ 是占位 $0$. 不是 `HS` 的问题: 是极限节点本身的单调. 换句话说 `low-tree` 那个 $0$ 不只是值小, 它让树不合法.

## §3 $\Omega_3$

环境取第 4 层, 其余与 `lowˢ` 同. 从 $\psi_0(\psi_\Omega(\Omega_3))$ 沿 $[1,0,0,1,0,0]$ 到 $\psi_0(\psi_\Omega(\psi_2(1)))$, 再接 `toW`. 这段路径的两端都是 `refl`.

```agda
four : Ordᴵ
four = suc three

z4 : zero <ᴵ four
z4 = suc z3

F₃ : Ordˢ zero
F₃ = ψᵉ′ ∅ˢ z4 z4 (λ q → suc q) (Ωˢ three)

toW₃ : List ℕ
toW₃ = 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ toW

no-Ω₃ : Goodᴺ (toZ F₃) → ⊥
no-Ω₃ G = mono-bad (walkˢ F₃ toW₃) (0 ∷ 0 ∷ 0 ∷ []) refl refl refl (walkG F₃ toW₃ G)
```
