# 桥 (一): 改一行的折叠 `T′`

> 不含记号. 结论写在 [GuardBridge](GuardBridge.lagda.md). 与 [GuardTightTree](GuardTightTree.lagda.md) 的 `Fold` 只差一行: **`owk` 这一行也收窄输出的地板**, 与 `ocv` 同一行. 那里 `ψ E T st (owk w x) = ψ E T (st ∘ w) x`, 输入收窄了, 输出还带全部的 $\rho$. 于是过两遍折叠之后, 一个保留下来的闭包的上下文里多出了它根本不依赖的帧, 读成多余的地板 ([GuardBridgeNeg](GuardBridgeNeg.lagda.md) 的 `T₀-too-high`). [ScafLadderQ](ScafLadderQ.lagda.md) 的 `qwk` 与 [OCF.Free.Tree](../Free/Tree.lagda.md) 的 `owk` 都在输出上留着这个收窄. 其余定义全部从 `Fold` 取来, 只重写互相递归的四个函数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardBridgeTree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as Lvl
open import OCF.Free.Level using (Ordᴵ; suc; _⊑ᴵ_; ⊑ᴵ-trans; _<ᴵ_)
open import OCF.Free.Aux using (Mlev)
open import OCF.Free.Floor using (Flr; Ev; Bd; Fc; evF; iF; FB; liftEv; Top; FM; bound)
open import OCF.Free.Prefix using (Z)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree

module Fold′ (c : LG) (wf : WFˢ c) (sf : c ≈ c) (tc : Tc c) where
  open Fold c wf sf tc hiding (ψ; evalC; goC; riseΩ)

  ψ : ∀ {t π ρ} (E : Ents) → Tg E t → St E ρ π → O c π → O t ρ
  evalC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) → Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁) → AdmC (cov π) P →
          O c π → (∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) → O t ρ
  goC : ∀ {t π ρ c₁ t₁ g₁ c₂ t₂ g₂} (E : Ents) → Tg E t → St E ρ π → (P : Cp (lc c₂ t₂ g₂) c) → Lk (lc c₂ t₂ g₂) (lc c₁ t₁ g₁) → (ap : AdmC (tab E) P) →
        O c π → (∀ η e → O c (π ∪ tk (frm c₁ t₁ g₁ η e))) → (SS : Sel.S P E ap (λ F → St F ρ π × (Tg F t × AdmC (tab F) P))) → Sel.Sl P E ap (Sel.φ SS) → O t ρ
  riseΩ : ∀ {t π ρ k} (E : Ents) → Tg E t → St E ρ π → (r : k < c) → Adm (cov π) r → (∀ ξ → Us c r ξ → O c (ξ ∪ π)) → O t ρ

  ψ {t} E T st o0 = owk (λ ()) (Ω̇ t (tcT T))
  ψ E T st (os a) = ol (repᵒ (ψ E T st a))
  ψ E T st (ol F) = ol (λ n → ψ E T st (F n))
  ψ E T st (oŝ c₀ x g) = oŝ c₀ (ψ E T st x) (λ η e → ψ E T st (g η e))
  ψ E T st (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψ E T st o₀) (λ η e → ψ E T st (o η e))
  -- 唯一改动: 输出的地板也收窄, 与 ocv 同一行
  ψ E T st (owk {π = π′} w x) with lowerSt π′ (cov-exact w) st
  ... | σ , st′ , cv₁ = ocv cv₁ (ψ E T st′ x)
  ψ E T st (ocv {π = π′} w x) with lowerSt π′ w st
  ... | σ , st′ , cv₁ = ocv cv₁ (ψ E T st′ x)
  ψ E T st (omk R lk ad z x) = ψ E T st x
  ψ E t0 st (oΩ r cv h) = riseΩ E t0 st r cv h
  ψ E (tp q aq) st (oΩ r cv h) with Vis.cmpN st wf sf r q cv aq
  ... | Vis.cb d s a = oΩ s a (λ ξ y → ψ E (tp q aq) (stξ ξ st) (h ξ (intoU r (tr⁻O d (outU s y)))))
  ... | Vis.cu _ = riseΩ E (tp q aq) st r cv h
  ... | Vis.cj = o0
  ψ E t0 st (ocl P k cv x g) = evalC E t0 st P k cv x g
  ψ {π = π} {ρ = ρ} E (tp q aq) st (ocl {c₁ = c₁} {t₁} {g₁} P k cv x g) with Vis.cmpK st wf sf P q cv aq
  ... | Vis.kb = evalC E (tp q aq) st P k cv x g
  ... | Vis.kj = o0
  ... | Vis.ka {c′} {t′} {g′} Q d a =
    ocl Q (inj₂ refl) a (ψ E (tp q aq) st x)
      (λ η e′ → ψ E (tp q aq) (st″ η e′) (g η (eg e′)))
    where
    lks₁ : lc c₁ t₁ g₁ ≈ lc c′ t′ g′
    lks₁ = ≈-trans (≈-sym (lk→≈ (selfC sf P) k)) d
    eg : ∀ {η} → c′ ⊑ᴵ η → c₁ ⊑ᴵ η
    eg e′ = conv (oc≅ (≈-sym lks₁)) e′
    st″ : ∀ η e′ → St E (ρ ∪ tk (frm c′ t′ g′ η e′)) (π ∪ tk (frm c₁ t₁ g₁ η (eg e′)))
    st″ η e′ (ml m) = mapFs ml (st m)
    st″ η e′ (mr hr) = fs nothing (just (ab {c₄ = c′} {t₄ = t′} {g₄ = g′} {e₄ = e′} (mr hr) (inj₁ lks₁)))

  riseΩ {π = π} E T st r cv h with Vis.toTab st r cv
  ... | nothing = o0
  ... | just a with nfT c tc r | trim π st {r} a
  ...   | nft d r′ tb | mkTr ξ w bk = ol (λ n → ψ E T (stBody ξ w st) (h ξ (intoU r (chainᵒ (Tc-at r tc) (λ z → trL⁻ d (ψ E (tp r′ (tb E a)) (stChain ξ bk w st) (h ξ (intoU r z)))) n))))

  evalC E T st P k cv x g with Vis.toTabC st P cv
  ... | nothing = o0
  ... | just ap = goC E T st P k ap x g (SSc E T st P ap) (Sel.wit (SSc E T st P ap))

  goC {t} {π} {ρ} {c₁} {t₁} {g₁} {c₂} {t₂} {g₂} E T st P k ap x g SS w = go w
    where
    module M = Sel P E ap
    lk₂ : lc c₂ t₂ g₂ ≈ lc c₁ t₁ g₁
    lk₂ = lk→≈ M.kself k
    guardC : ∀ {η} → c₂ ⊑ᴵ η → c₁ ⊑ᴵ η
    guardC d = conv (oc≅ lk₂) d
    body : ∀ η (e : c₁ ⊑ᴵ η) X → Ev X (M.φ SS) → η <ᴵ X → O t ρ
    body η e X ex q = ψ (M.E′ X) (proj₁ (proj₂ L)) stn (g η e)
      where
      L = M.lft SS X ex
      stn : St (M.E′ X) ρ (π ∪ tk (frm c₁ t₁ g₁ η e))
      stn (ml m) = proj₁ L m
      stn (mr hr) = fs (just (evd P (proj₂ (proj₂ L)) lk₂ (X , inj₁ (≈-sym lk₂ , refl) , lt→pr q))) nothing
    go : M.Sl (M.φ SS) → O t ρ
    go (M.emp f) = oŝ c₂ (ψ E T st x) (λ η d → body η (guardC d) (suc η) (f (suc η)) Lvl.zero)
    go (M.sel ℓ K₀ a q y i dm) = oŝ (Bd B) (ψ E T st x)
         (λ η d → body η (guardC (⊑ᴵ-trans (dm (Fc B) (evF B)) (⊑ᴵ-trans (FM B) d)))
                       (Mlev (Fc B) (suc η) (FB B d))
                       (liftEv (M.φ SS) (λ r → Lvl.lim 0 r) (evF B))
                       (Lvl.lim 1 Lvl.zero))
      where
      B : Top K₀ ℓ (M.φ SS)
      B = bound (M.φ SS) y q

T′ : (L : LG) → Cfˢ L → Tc L → O zero tz
T′ L (w , s) tc = Fold′.ψ L w s tc (∅ Lvl.zero) Fold.t0 (λ ()) (Ω̇ L tc)

T₀′ : (L : LG) → Cfˢ L → Tc L → Z
T₀′ L cf tc = rdZ (T′ L cf tc)
```
