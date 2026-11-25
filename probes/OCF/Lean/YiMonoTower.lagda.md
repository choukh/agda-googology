# 无见证上界上的同层单调: 塔的一切项与 Λ, 无前提

验收文件. 编译定理, 无前提: `Tower.mw-tw`, `Tower.mw-Λ`, `Tower.TΛⁿ-legal`, `Tower.mono-tw`, `Tower.mono-Λ`, `Tower.value-Λ`. 公共上界 `Lw-twⁿ`, `VΛⁿ` 的根见证全取 none (与裸折叠的上界同形), 所以闭项 `TΛⁿ` 不是主线带见证的 `TΛ`.
来自第十一次路线审查 ([RR11](../../Survey/RR11-RouteOverview.md)), 代码未改, 只换模块名.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
-- 无根见证的公共上界: 对塔的一切项与 Λ, MW 由一条对结构的归纳给出 (与 Lw-Ω̂ 同形),
-- 于是无根见证的一致折叠 (任意派发 D) 在塔的一切项与 Λ 上对 Sim 单调, 无前提.
module OCF.Lean.YiMonoTower where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (Way; keep; fold; Ext; R)
open import OCF.Lean.YiLamFold using (Wit; none; at; Lw; w0; ws; wl; wΩ; cps; lwN)
import OCF.Lean.YiNextTower as T
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMono
open import OCF.Lean.YiMonoInst using (sim→≼)

Lw-Ω̂ⁿ : ∀ x → T.Legal x → Lw x → Lw (upT x)
lgl→Lwⁿ : ∀ y → T.Legal y → Lw y → ∀ a → Lgl y a → Lw (up y a)

Lw-Ω̂ⁿ zero L W = ws w0
Lw-Ω̂ⁿ (suc k) L (ws W) = wΩ (λ η l → lgl→Lwⁿ k L W η l) none
Lw-Ω̂ⁿ (lim f) (st , L) (wl W s) = wl (λ n → Lw-Ω̂ⁿ (f n) (L n) (W n)) (λ n → cps (T.Ω̂-CP (st n)))
Lw-Ω̂ⁿ (lc k g) (Lk , lg , mo) (wΩ W w) = wΩ (λ η l → Lw-Ω̂ⁿ (g η) (lg η l) (W η l)) none

lgl→Lwⁿ y L W G.zero l = w0
lgl→Lwⁿ y L W (G.suc a) l = ws (lgl→Lwⁿ y L W a l)
lgl→Lwⁿ y L W (G.lim f) (st , lf) =
  wl (λ n → lgl→Lwⁿ y L W (f n) (lf n)) (λ n → cps (T.cp→CP y (st n)))
lgl→Lwⁿ y L W (G.lc r h) (lg , mo) =
  lwN y r (λ η → up y (h η)) (λ η l → lgl→Lwⁿ y L W (h η) (lg η l))
lgl→Lwⁿ (suc k) L (ws W) (G.em _ a) l = lgl→Lwⁿ k L W a l
lgl→Lwⁿ (lim f) (st , L) (wl W s) (G.em n a) l = lgl→Lwⁿ (f n) (L n) (W n) a l
lgl→Lwⁿ (lc k g) (Lk , lg , mo) (wΩ W w) (G.em (η , lη) a) l = lgl→Lwⁿ (g η) (lg η lη) (W η lη) a l
lgl→Lwⁿ y L W G.top l = Lw-Ω̂ⁿ y L W

Lw-twⁿ : ∀ n → Lw (tw n)
Lw-twⁿ zero = w0
Lw-twⁿ (suc n) = Lw-Ω̂ⁿ (tw n) (T.Legal-tw n) (Lw-twⁿ n)

VΛⁿ : Lw Λ
VΛⁿ = wl Lw-twⁿ (λ n → cps (T.tw-step n))

module Tower (D : ∀ k K → Ext k K) where
  open W.Fold D
  open M D

  mwN : ∀ y r (h : Lay.A (Lo y r) → LF) (Wh : ∀ η → Lay.lg (Lo y r) η → Lw (h η)) →
    (∀ η l → MW (Wh η l)) → MW (lwN y r h Wh)
  mwN (suc k) (inj₁ _) h Wh q = mΩ q tt
  mwN (suc k) (inj₂ r) h Wh q = mwN k r h Wh q
  mwN (lim f) (n , r) h Wh q = mwN (f n) r h Wh q
  mwN (lc k g) (η , _ , r) h Wh q = mwN (g η) r h Wh q

  mw-Ω̂ : ∀ x (L : T.Legal x) (V : Lw x) → MW V → MW (Lw-Ω̂ⁿ x L V)
  mw-lgl : ∀ y (L : T.Legal y) (V : Lw y) → MW V → ∀ a (l : Lgl y a) → MW (lgl→Lwⁿ y L V a l)

  mw-Ω̂ zero L V Q = ms m0
  mw-Ω̂ (suc k) L (ws V) (ms Q) = mΩ (λ η l → mw-lgl k L V Q η l) tt
  mw-Ω̂ (lim f) (st , L) (wl V s) (ml Q) = ml (λ n → mw-Ω̂ (f n) (L n) (V n) (Q n))
  mw-Ω̂ (lc k g) (Lk , lg , mo) (wΩ V w) (mΩ Q kh) = mΩ (λ η l → mw-Ω̂ (g η) (lg η l) (V η l) (Q η l)) tt

  mw-lgl y L V Q G.zero l = m0
  mw-lgl y L V Q (G.suc a) l = ms (mw-lgl y L V Q a l)
  mw-lgl y L V Q (G.lim f) (st , lf) = ml (λ n → mw-lgl y L V Q (f n) (lf n))
  mw-lgl y L V Q (G.lc r h) (lg , mo) =
    mwN y r (λ η → up y (h η)) _ (λ η l → mw-lgl y L V Q (h η) (lg η l))
  mw-lgl (suc k) L (ws V) (ms Q) (G.em _ a) l = mw-lgl k L V Q a l
  mw-lgl (lim f) (st , L) (wl V s) (ml Q) (G.em n a) l = mw-lgl (f n) (L n) (V n) (Q n) a l
  mw-lgl (lc k g) (Lk , lg , mo) (wΩ V w) (mΩ Q kh) (G.em (η , lη) a) l =
    mw-lgl (g η) (lg η lη) (V η lη) (Q η lη) a l
  mw-lgl y L V Q G.top l = mw-Ω̂ y L V Q

  mw-tw : ∀ n → MW (Lw-twⁿ n)
  mw-tw zero = m0
  mw-tw (suc n) = mw-Ω̂ (tw n) (T.Legal-tw n) (Lw-twⁿ n) (mw-tw n)

  mw-Λ : MW VΛⁿ
  mw-Λ = ml mw-tw

  -- 闭项 (无根见证的 Λ 闭项) 与它的合法性 (折叠的合法性对任意公共上界成立).
  TΛⁿ : R
  TΛⁿ = Ψ zero VΛⁿ (λ _ → fold) G.top

  TΛⁿ-legal : Lgl zero TΛⁿ
  TΛⁿ-legal = Ψ-lgl zero VΛⁿ (λ _ → fold) G.top tt

  -- 整体的单调: 塔的一切项, Λ, 一切目标层, 一切外部派发; 无前提.
  mono-tw : ∀ n m (x : Ext m (tw n)) {ξ ξ′} → Sim (tw n) ξ ξ′ →
    Sim m (Ψ m (Lw-twⁿ n) x ξ) (Ψ m (Lw-twⁿ n) x ξ′)
  mono-tw n m = mono m (mw-tw n)

  mono-Λ : ∀ m (x : Ext m Λ) {ξ ξ′} → Sim Λ ξ ξ′ → Sim m (Ψ m VΛⁿ x ξ) (Ψ m VΛⁿ x ξ′)
  mono-Λ m = mono m mw-Λ

  value-Λ : ∀ {ξ ξ′} → Sim Λ ξ ξ′ →
    NA.read (Ψ zero VΛⁿ (λ _ → fold) ξ) ≼ NA.read (Ψ zero VΛⁿ (λ _ → fold) ξ′)
  value-Λ d = sim→≼ (mono-Λ zero (λ _ → fold) d)
```
