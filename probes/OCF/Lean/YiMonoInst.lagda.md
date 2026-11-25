# 同层单调的出口与前提的实例

验收文件. 编译定理: `sim→≼` (第 0 层上 `Sim` 推出读回的值序); `Inst.mw2`, `Inst.value2`: 主线的上界 `Lw-tw 2` 的前提 `MW` 归到根见证上的一条 `KeepMono` (未证未否定).
来自第十一次路线审查 ([RR11](../../Survey/RR11-RouteOverview.md)), 代码未改, 只换模块名.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
-- OCF.Lean.YiMono 的出口与前提的实例:
--  (1) 第 0 层上 Sim 推出读回的值序;
--  (2) 自相关的树上, 第一位置 (合法性用的序) 含在 Sim 里;
--  (3) 前提 MW 可满足: tw 2 的无根见证的公共上界 (含 wΩ) 满足 MW, 于是对它的折叠单调无前提;
--  (4) 主线的 Lw-tw 2: MW 恰好归到根见证上的 KeepMono 一条.
module OCF.Lean.YiMonoInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (Way; keep; fold; Ext; R)
open import OCF.Lean.YiLamFold using (Wit; none; at; Lw; w0; ws; wl; wΩ; lgl→Lw; Lw-tw; witU)
import OCF.Lean.YiNextTower as T
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-suc; z≼; s≼s; ≼l; l≼)
open import OCF.Lean.YiMono

-- (1)
sim→≼ : ∀ {a b : R} → Sim zero a b → NA.read a ≼ NA.read b
sim→≼ zS = z≼
sim→≼ (sS d) = s≼s (sim→≼ d)
sim→≼ (wS d) = ≼-suc (sim→≼ d)
sim→≼ (lR n d) = ≼l n (sim→≼ d)
sim→≼ (lL h) = l≼ (λ n → sim→≼ (h n))
sim→≼ (bR {r = ()} d)
sim→≼ (nN {r = ()} h)
sim→≼ (eE {i = ()} d)
sim→≼ tT = ≼-refl _

-- (2) Sim 对右边沿第一位置上移封闭; 于是自相关的树上第一位置含在 Sim 里.
sim-cp : ∀ k {x a b} → Sim k x a → Cp k a b → Sim k x b
sim-dn : ∀ k {x a} b → Sim k x a → Dn k a b → Sim k x b
em-ws : ∀ k {x a d} → Sim (suc k) x (G.em tt a) → Dn k a d → Sim (suc k) x (G.em tt d)
em-wl : ∀ f n {x a d} → Sim (lim f) x (G.em n a) → Dn (f n) a d → Sim (lim f) x (G.em n d)
em-wc : ∀ k g η l {x a d} → Sim (lc k g) x (G.em (η , l) a) → Dn (g η) a d →
  Sim (lc k g) x (G.em (η , l) d)
sim-cp k s (inj₁ refl) = s
sim-cp k s (inj₂ p) = sim-dn k _ s p
sim-dn k (G.suc d) s p = wS (sim-cp k s p)
sim-dn k (G.lim f) s (n , p) = lR n (sim-cp k s p)
sim-dn k (G.lc r g) s p = bR (sim-cp k s p)
sim-dn (suc k) {a = G.em _ a} (G.em _ d) s (refl , p) = em-ws k s p
sim-dn (lim f) {a = G.em n a} (G.em _ d) s (refl , p) = em-wl f n s p
sim-dn (lc k g) {a = G.em (η , l) a} (G.em _ d) s (refl , p) = em-wc k g η l s p
em-ws k zS p = zS
em-ws k (lL h) p = lL (λ n → em-ws k (h n) p)
em-ws k (eE s) p = eE (sim-dn k _ s p)
em-wl f n zS p = zS
em-wl f n (lL h) p = lL (λ i → em-wl f n (h i) p)
em-wl f n (eE s) p = eE (sim-dn (f n) _ s p)
em-wc k g η l zS p = zS
em-wc k g η l (lL h) p = lL (λ i → em-wc k g η l (h i) p)
em-wc k g η l (eE s) p = eE (sim-dn (g η) _ s p)

cp-sim : ∀ k {a b} → Sim k a a → Cp k a b → Sim k a b
cp-sim k = sim-cp k

module Inst (D : ∀ k K → Ext k K) where
  open W.Fold D
  open M D

  -- (3) 第 0 层的树读成的层号的公共上界不含 wΩ, 满足 MW.
  mw0 : ∀ η (l : Lgl zero η) → MW (lgl→Lw zero tt w0 η l)
  mw0 G.zero l = m0
  mw0 (G.suc a) l = ms (mw0 a l)
  mw0 (G.lim f) (st , lf) = ml (λ n → mw0 (f n) (lf n))
  mw0 (G.lc () g) l
  mw0 (G.em () a) l
  mw0 G.top l = ms m0

  V2n : Lw (tw 2)
  V2n = wΩ (λ η l → lgl→Lw zero tt w0 η l) none

  mw2n : MW V2n
  mw2n = mΩ mw0 tt

  -- 无前提: 无根见证的 tw 2 折叠, 一切目标层, 一切外部派发.
  mono2n : ∀ m (x : Ext m (tw 2)) {ξ ξ′} → Sim (tw 2) ξ ξ′ → Sim m (Ψ m V2n x ξ) (Ψ m V2n x ξ′)
  mono2n m = mono m mw2n

  value2n : ∀ {ξ ξ′} → Sim (tw 2) ξ ξ′ →
    NA.read (Ψ zero V2n (λ _ → fold) ξ) ≼ NA.read (Ψ zero V2n (λ _ → fold) ξ′)
  value2n d = sim→≼ (mono2n zero (λ _ → fold) d)

  -- (4) 主线的 Lw-tw 2 (根见证 witU zero): MW 归到 KeepMono 一条.
  V2-form : Lw-tw 2 ≡ wΩ (λ η l → lgl→Lw zero tt w0 η l) (witU zero)
  V2-form = refl

  mw2 : KeepMono (λ η l → lgl→Lw zero tt w0 η l) (witU zero) → MW (Lw-tw 2)
  mw2 kh = mΩ mw0 kh

  value2 : KeepMono (λ η l → lgl→Lw zero tt w0 η l) (witU zero) → ∀ {ξ ξ′} → Sim (tw 2) ξ ξ′ →
    NA.read (Ψ zero (Lw-tw 2) (λ _ → fold) ξ) ≼ NA.read (Ψ zero (Lw-tw 2) (λ _ → fold) ξ′)
  value2 kh d = sim→≼ (mono zero (mw2 kh) (λ _ → fold) d)
```
