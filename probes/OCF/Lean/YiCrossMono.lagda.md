# 折叠对跨层模拟 `Simʰ` 单调: `monoʰ`

验收文件. 编译定理 `monoʰ : MonoH D`, 对任意派发 `D`: 由接口的前提 `Compat` (派发) 与 `KeepRow` (Ω 结点层号的根保留时的分支族) 推出一般折叠把 `Simʰ k k′ ξ ξ′` 送到 `Simʰ m m′ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)`.
一条对 (左上界, 右上界, 推导) 的归纳, 不按站. 不说明 `Compat`, `KeepRow` 对哪个派发成立; 可满足的实例与回归在 [YiCrossInst](YiCrossInst.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCrossMono where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using
  (lev; Way; keep; fold; Ext; nodeAt; chain; Ψn; ΨN; succ; psum; self; ΩT)
open import OCF.Lean.YiLamFold using
  (Kfk; nrmk; nrmk-lgl; Wit; none; at; Lw; w0; ws; wl; wΩ; rootW; Pk; pk)
import OCF.Lean.YiDlFold as W
open import OCF.Lean.YiCrossIface
open import OCF.Lean.YiCrossAdd
open Pk

module M (D : ∀ k K → Ext k K) where
  open W.Fold D
```

`tbʰ`: 目标层的顶相关时, 左边的顶不高于右边任何折叠值 (只动右边). `ztʰ`: 第 0 层的 `top` 的像 `succ M top` 不高于右边任何层的 `top` 的像.

```agda
  tbʰ : ∀ {M} m′ {k′} (V′ : Lw k′) (x′ : Ext m′ k′) → Simʰ M m′ G.top G.top → ∀ ξ′ →
    Simʰ M m′ G.top (Ψ m′ V′ x′ ξ′)
  tbʰ m′ V′ x′ t G.zero = t
  tbʰ m′ V′ x′ t (G.suc a) = lR 0 (tbʰ m′ V′ x′ t a)
  tbʰ m′ V′ x′ t (G.lim f) = lR 0 (tbʰ m′ V′ x′ t (f 0))
  tbʰ m′ {k′} V′ x′ t (G.lc r g) = ΨN-bbʰ m′ k′ r (x′ r) _ _ (tbʰ m′ V′ x′ t (g _))
  tbʰ m′ w0 x′ t (G.em () a)
  tbʰ m′ (ws V′) x′ t (G.em _ a) = tbʰ m′ V′ _ t a
  tbʰ m′ (wl V′ st) x′ t (G.em n a) = tbʰ m′ (V′ n) _ t a
  tbʰ m′ (wΩ V′ w) x′ t (G.em (η , l) a) = tbʰ m′ (V′ η l) _ t a
  tbʰ m′ w0 x′ t G.top = lR 0 t
  tbʰ m′ {suc k′} (ws V′) x′ t G.top = Ψn-bbʰ m′ k′ (x′ (inj₁ tt)) _ _ (tbʰ m′ V′ _ t G.top)
  tbʰ m′ (wl V′ st) x′ t G.top = lR 0 (tbʰ m′ (V′ 0) _ t G.top)
  tbʰ m′ (wΩ {k = k′} {g = g′} V′ w) x′ t G.top =
    ΩT-bbʰ m′ k′ (rootW m′ k′ g′ w x′) _ _ (tbʰ m′ (V′ _ _) _ t G.top) (tbʰ m′ (V′ _ _) _ t G.top)

  ztʰ : ∀ M m′ {k′} (V′ : Lw k′) (x′ : Ext m′ k′) → Simʰ M m′ G.top G.top →
    Simʰ M m′ (succ M G.top) (Ψ m′ V′ x′ G.top)
  ztʰ M m′ w0 x′ t = succ-monoʰ M m′ t
  ztʰ M m′ {suc k′} (ws V′) x′ t = Ψn-bbʰ m′ k′ (x′ (inj₁ tt)) _ _ (ztʰ M m′ V′ _ t)
  ztʰ M m′ (wl V′ st) x′ t = lR 0 (ztʰ M m′ (V′ 0) _ t)
  ztʰ M m′ (wΩ {k = k′} {g = g′} V′ w) x′ t =
    ΩT-bbʰ m′ k′ (rootW m′ k′ g′ w x′) _ _ (ztʰ M m′ (V′ _ _) _ t) (ztʰ M m′ (V′ _ _) _ t)
```

主定理. `nN`: 两边同为保留或同为折叠 (`c-way`), 内层的链由 `c-cmp` 给出的配置对递归. `tT` 按两边上界的形状: 后继对后继是根位置的一行 (`c-self`), ℕ 极限对 ℕ 极限逐项, Ω 结点层号对 Ω 结点层号: 折叠行逐个链点递归 (那一支的顶相关由 `c-obs`), 保留行的分支族用 `KeepRow`.

```agda
  module Mono (S : Compat D) (R : KeepRow D S) where
    open Compat S
    open KeepRow R

    mono : ∀ {m k m′ k′} (V : Lw k) (x : Ext m k) (V′ : Lw k′) (x′ : Ext m′ k′) → C V x V′ x′ →
      ∀ {ξ ξ′} → Simʰ k k′ ξ ξ′ → Simʰ m m′ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)
    mono {m′ = m′} V x V′ x′ c {ξ′ = ξ′} zS = tbʰ m′ V′ x′ (c-top c) ξ′
    mono {m} {m′ = m′} V x V′ x′ c (sS d) = succ-monoʰ m m′ (mono V x V′ x′ c d)
    mono V x V′ x′ c (wS d) = lR 0 (mono V x V′ x′ c d)
    mono V x V′ x′ c (lR n d) = lR n (mono V x V′ x′ c d)
    mono V x V′ x′ c (lL h) = lL (λ n → mono V x V′ x′ c (h n))
    mono {m′ = m′} {k′} V x V′ x′ c (bR {r′ = r′} d) = ΨN-bbʰ m′ k′ r′ (x′ r′) _ _ (mono V x V′ x′ c d)
    mono {m} {k} {m′} {k′} V x V′ x′ c (nN {r = r} {r′ = r′} e p h) =
      ΨN-nnʰ m m′ k r (x r) k′ r′ (x′ r′) (c-way c r r′ e p) e p
        (λ η η′ q → mono V x V′ x′ c (h η η′ q))
        (λ η η′ q → mono V (cmpw V r) V′ (cmpw V′ r′) (c-cmp c r r′ e p) (h η η′ q))
    mono w0 x V′ x′ c (eL {i = ()} d)
    mono (ws V) x V′ x′ c (eL d) = mono V _ V′ x′ (c-Ls c) d
    mono (wl V st) x V′ x′ c (eL {i = n} d) = mono (V n) _ V′ x′ (c-Ll c n) d
    mono (wΩ V w) x V′ x′ c (eL {i = (η , l)} d) = mono (V η l) _ V′ x′ (c-LΩ c η l) d
    mono V x w0 x′ c (eR {i′ = ()} d)
    mono V x (ws V′) x′ c (eR d) = mono V x V′ _ (c-Rs c) d
    mono V x (wl V′ st′) x′ c (eR {i′ = n} d) = mono V x (V′ n) _ (c-Rl c n) d
    mono V x (wΩ V′ w′) x′ c (eR {i′ = (η , l)} d) = mono V x (V′ η l) _ (c-RΩ c η l) d
    mono {m} {m′ = m′} w0 x V′ x′ c (tT e) = ztʰ m m′ V′ x′ (c-top c)
    mono (ws V) x w0 x′ c (tT ())
    mono {m} {suc k} {m′} {suc k′} (ws V) x (ws V′) x′ c (tT (e , t)) =
      Ψn-nnʰ m m′ k k′ (x (inj₁ tt)) (x′ (inj₁ tt)) (c-way c (inj₁ tt) (inj₁ tt) e t) e t
        (λ η η′ q → mono V _ V′ _ (c-Rs (c-Ls c)) q)
        (λ η η′ q → mono V (self k) V′ (self k′) (c-self c e t) q)
    mono (ws V) x (wl V′ st′) x′ c (tT ())
    mono (ws V) x (wΩ V′ w′) x′ c (tT ())
    mono (wl V st) x w0 x′ c (tT ())
    mono (wl V st) x (ws V′) x′ c (tT ())
    mono {m} {m′ = m′} (wl V st) x (wl V′ st′) x′ c (tT e) =
      psum-monoʰ m m′ (λ n → mono (V n) _ (V′ n) _ (c-Rl (c-Ll c n) n) (e n))
    mono (wl V st) x (wΩ V′ w′) x′ c (tT ())
    mono (wΩ V w) x w0 x′ c (tT ())
    mono (wΩ V w) x (ws V′) x′ c (tT ())
    mono (wΩ V w) x (wl V′ st′) x′ c (tT ())
    mono {m} {lc k g} {m′} {lc k′ g′} (wΩ V w) x (wΩ V′ w′) x′ c (tT (e , t)) =
      ΩT-nnʰ m m′ k k′ (rootW m k g w x) (rootW m′ k′ g′ w′ x′) (c-root c e t) e t
        (λ kp kp′ → c-keep c (e , t) kp kp′
          (λ η l η′ l′ y y′ c″ d → mono (V η l) y (V′ η′ l′) y′ c″ d))
        (psum-monoʰ m m′ (λ n → mono (V _ _) _ (V′ _ _) _ (c-RΩ (c-LΩ c _ _) _ _) (c-obs c n)))
    mono V x w0 x′ c (cR {i′ = ()} ct d)
    mono {m′ = m′} {suc k′} V x (ws V′) x′ c (cR ct d) =
      Ψn-bbʰ m′ k′ (x′ (inj₁ tt)) _ _ (mono V x V′ _ (c-Rs c) d)
    mono V x (wl V′ st′) x′ c (cR refl d) = lR 0 (mono V x (V′ 0) _ (c-Rl c 0) d)
    mono V x (wΩ V′ w′) x′ c (cR () d)
    mono {m} {m′ = m′} w0 x V′ x′ c (t0 {b = b} z) = succ-monoʰ m m′ (tbʰ m′ V′ x′ (c-top c) b)
    mono (ws V) x V′ x′ c (t0 ())
    mono (wl V st) x V′ x′ c (t0 ())
    mono (wΩ V w) x V′ x′ c (t0 ())

  monoʰ : MonoH D
  monoʰ S R {V = V} {x} {V′} {x′} c d = Mono.mono S R V x V′ x′ c d
```
