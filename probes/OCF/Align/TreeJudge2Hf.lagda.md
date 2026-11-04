# `HF` 在一类闭包上是定理, 在别处是假的

> 不含记号. 结论写在 [TreeJudge2](TreeJudge2.lagda.md). 对象: $\psi_0(\Omega_{\Omega+1})$ 这棵树的折叠 (`Fold (suc c₁)`), **任意读法** `tc`, 闭包 $\Omega_\Omega$ (位置 `suc self`), 上下文为空, 第一支与 $\Omega_1$ 相关 (`rel-t` 给的就是). 这正是 `ψ o0` 长出来的那个闭包.
>
> - `head-any`: **头不读目标, 不读世界, 不读状态.** 层 0 的任意两个目标, 任意两个世界, 头 $\cong^{\mathsf z}$. 所以上一轮要的桥 "头相同推出目标相同" 是假的: `no-bridge` 给一对不同的目标 (`t0` 与 `tp q₁ tt`). **于是 `free-bound` ("同一个目标同一个界") 永远推不出 `HF`.**
> - `hf-class`: 目标是 `t0` 或在第一支里: 头 $\cong^{\mathsf z}$, 界模前序就是 1. 这是 `HF` 对这一类闭包的**定理**, 对任意读法.
> - `bd-bra`, `hf-fails`: 目标穿过 `bra τ`: 头还是同一个, 界 $\succ$ `pr τ`. $\tau$ 是极限时 ($\tau$ 读进了界), 界 $\not\sqsubseteq1$. **这就是 `HF` 的全部内容: 在这类闭包上, `HF` 等价于 "读法把层 0 的目标放进第一支".** 这一句的 "等价" 是这三条定理的合取, 只对这一类闭包.
>
> 模块参数 `tc` 是读法, 任意, 不是假设. `no-id` 用的是 `tc = tcI`; `hf-class` 对紧的 `tc₁` 同样成立.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudge2Hf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (Ordᴵ; _⊑ᴵ_; _≺ᴵ_; _<ᴵ_; via; ⊑ᴵ-refl; ⊑ᴵ-trans; s⊑; sim; ≅ᴵ-trans)
open import OCF.Free.Prefix using (Z; _≅ᶻ_; ≅ᶻ-sym; ≅ᶻ-trans; Ωˢ; Ordˢ)
open import OCF.Free.Floor using (InF; inl; inr; ink)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardTightCertRel using (⌜_⌝; Emp; Rs)
open import OCF.Align.GuardTightCert using (c₁; wf₁; sf₁)
open import OCF.Align.GuardTightBound using (module Land)
open import OCF.Align.GuardReadBound using (module NoOcc)
open import OCF.Align.TreeJudge2Rel using (L₁; sfL; module RelT)

module HfT (tc : Tc L₁) where
  open Fold L₁ wf₁ sfL tc
  open Land L₁ wf₁ sfL tc
  open NoOcc L₁ wf₁ sfL tc using (no-occ-f)
  open RelT tc

  One : Ordᴵ
  One = Ordᴵ.suc Ordᴵ.zero

  π₀ : Fl
  π₀ = tz ∪ tz

  emp₀ : Emp π₀
  emp₀ (ml ())
  emp₀ (mr ())

  q₁ : Lv.zero < L₁
  q₁ = Lv.suc (fst zero)

  -- 第一支: 界的来源是空的
  module Fst {E : Ents} {ρ : Fl} (st : St E ρ π₀) where
    W₁ = Sel.wit (SSc E (tp q₁ tt) st (Lv.suc self) tt)

    none : ∀ {K} → InF K (Sel.φ (SSc E (tp q₁ tt) st (Lv.suc self) tt)) → ⊥
    none i with floors E (tp q₁ tt) st (Lv.suc self) tt i
    ... | fromSt (Occ.sfr (ml ()) _ _)
    ... | fromSt (Occ.sfr (mr ()) _ _)
    ... | fromSt (Occ.spf _ (ml ()) _)
    ... | fromSt (Occ.spf _ (mr ()) _)
    ... | fromTgt refl (os′ (of′ ()))
    ... | fromPos (os′ ())

    ub : cOf W₁ ⊑ᴵ One
    ub = cOf-ub W₁ ⊑ᴵ-refl (λ i → ⊥-elim (none i))

    lb : One ⊑ᴵ cOf W₁
    lb = cOf-lb₁ W₁

  -- 目标 0: 界字面上是 1
  bd-t0 : ∀ {E : Ents} {ρ : Fl} (st : St E ρ π₀) → cOf (Sel.wit (SSc E t0 st (Lv.suc self) tt)) ≡ One
  bd-t0 st = refl

  -- 目标穿过 bra τ: 界读到 pr τ
  bd-bra : ∀ {E : Ents} {ρ : Fl} (st : St E ρ π₀) (τ : Ordᴵ) (e : One ⊑ᴵ τ) (X : Lv.zero < ⌜ τ ⌝) (aq : Adm (tab E) (Lv.suc (bra τ e X))) →
           pr τ ≺ᴵ cOf (Sel.wit (SSc E (tp (Lv.suc (bra τ e X)) aq) st (Lv.suc self) tt))
  bd-bra {E} st τ e X aq = cOf-lb₂ (Sel.wit (SSc E (tp (Lv.suc (bra τ e X)) aq) st (Lv.suc self) tt)) (inr (inl (inl ink))) refl

  -- 头不读目标
  head-any : ∀ {π π′ ρ ρ′} (E E′ : Ents) (T : Tg E Lv.zero) (T′ : Tg E′ Lv.zero) (tg : Tgt T Ordᴵ.zero) (tg′ : Tgt T′ Ordᴵ.zero) (st : St E ρ π) (st′ : St E′ ρ′ π′) →
             Emp π → Emp π′ → {x : O L₁ π} {x′ : O L₁ π′} → Rs One x (Ωˢ One) → Rs One x′ (Ωˢ One) →
             rdZ (ψ E T st x) ≅ᶻ rdZ (ψ E′ T′ st′ x′)
  head-any E E′ T T′ tg tg′ st st′ em em′ r r′ = ≅ᶻ-trans (head-≅ E T tg st em r) (≅ᶻ-sym (head-≅ E′ T′ tg′ st′ em′ r′))

  -- 上一轮的桥是假的: 两个不同的目标, 同一个头
  no-bridge : ∀ {E E′ : Ents} {ρ ρ′} (st : St E ρ π₀) (st′ : St E′ ρ′ π₀) (w : Wk π₀ tz) →
              rdZ (ψ E t0 st (Emb.ι L₁ tc c₁ (Lv.suc self) (inj₂ refl) (t-c w))) ≅ᶻ rdZ (ψ E′ (tp q₁ tt) st′ (Emb.ι L₁ tc c₁ (Lv.suc self) (inj₂ refl) (t-c w)))
  no-bridge {E} {E′} st st′ w = head-any E E′ t0 (tp q₁ tt) tg0 (tgp Lv.z≈) st st′ emp₀ emp₀ (rel-t w) (rel-t w)

  -- `HF` 在这一类上: 目标是 0 或第一支, 头 ≅, 界模前序就是 1
  hf-class : ∀ {E E′ : Ents} {ρ ρ′} (st : St E ρ π₀) (st′ : St E′ ρ′ π₀) (w : Wk π₀ tz) →
             (rdZ (ψ E (tp q₁ tt) st (Emb.ι L₁ tc c₁ (Lv.suc self) (inj₂ refl) (t-c w))) ≅ᶻ rdZ (ψ E′ (tp q₁ tt) st′ (Emb.ι L₁ tc c₁ (Lv.suc self) (inj₂ refl) (t-c w)))) ×
             (cOf (Fst.W₁ st) ⊑ᴵ cOf (Fst.W₁ st′)) × (cOf (Fst.W₁ st′) ⊑ᴵ cOf (Fst.W₁ st))
  hf-class {E} {E′} st st′ w =
    head-any E E′ (tp q₁ tt) (tp q₁ tt) (tgp Lv.z≈) (tgp Lv.z≈) st st′ emp₀ emp₀ (rel-t w) (rel-t w) ,
    ⊑ᴵ-trans (Fst.ub st) (Fst.lb st′) , ⊑ᴵ-trans (Fst.ub st′) (Fst.lb st)

  -- 目标穿过极限分支: 同一个头, 界不 ⊑ 1. 所以这一类上 `HF` 假
  hf-fails : ∀ {E : Ents} {ρ : Fl} {f s} (st : St E ρ π₀) (e : One ⊑ᴵ Ordᴵ.lim f s) (X : Lv.zero < ⌜ Ordᴵ.lim f s ⌝) (aq : Adm (tab E) (Lv.suc (bra (Ordᴵ.lim f s) e X))) →
             cOf (Sel.wit (SSc E (tp (Lv.suc (bra (Ordᴵ.lim f s) e X)) aq) st (Lv.suc self) tt)) ⊑ᴵ One → ⊥
  hf-fails st e X aq le with bd-bra st _ e X aq
  ... | via d q with sim le q
  ...   | via d′ (_<ᴵ_.suc ())
  ...   | via d′ _<ᴵ_.zero with ≅ᴵ-trans d d′
  ...     | ()
```
