# 全部 $\theta$ 的证书: $\Omega$ 对层号单调, `F` 的闭包 (底座)

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). `Ω-mono`: $\theta\sqsubseteq^\mathsf{A}\theta'$ 推出 $\Omega_\theta\sqsubseteq^\mathsf{o}\Omega_{\theta'}$, 两个层号都有证书. 这里第一次要第 0 层节点的左右规则 (`limᵢ-l₀`, `limᵢ-r₀`), 它们成立正因为第 0 层永远穿透. `lvp`: 第 0, 1 层的好树, 只要 `S` 在它的层号上正确 (`LvG`), 其层号就是好层号. 所以 `F` 的输出可以回灌作下标.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccThetaMono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; fin; upM; verdict; chM; natL)
open import OCF.Align.InaccFloorBase using (Aℓ; em)
open import OCF.Align.InaccThetaObs using (BL; b0; b1)
open import OCF.Align.InaccThetaFin using (module Fin)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; zero; suc; lim)
```

## §1 含 0 路径

```agda
module Mono (S : Sib) (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) (B₀ : Ordᴸ zero → Set) (a⊆b : ∀ x → Aℓ ℓ zero x → B₀ x) where
  open Fin S ℓ one B₀ a⊆b public

  zp-base : ∀ {k} {x : Ordᴸ k} → BL k → Zp k x → zero ≺ᴬ toLv x
  zp-base b zpZ = viaᴬ (inj₁ tt) tt z≈
  zp-base b (zpS z) with zp-base b z
  ... | viaᴬ q d e = viaᴬ (inj₂ q) d e
  zp-base b (zpL n z) with zp-base b z
  ... | viaᴬ q d e = viaᴬ (n , q) d e
  zp-base b1 (zpI {r = inj₁ _}) = viaᴬ (inj₁ (inj₁ tt)) tt z≈
  zp-base b1 (zpU z) = zp-base b0 z

  Zp-add : ∀ {k l} {a : Ordᴸ l} {σ : Sim k l} {x : Ordᴸ k} → Zp l a → Zp k x → Zp l (add a σ x)
  Zp-add za zpZ = zpS za
  Zp-add za (zpS z) = zpS (Zp-add za z)
  Zp-add za (zpL n z) = zpL n (Zp-add za z)
  Zp-add za zpI = zpI
  Zp-add {suc k} za (zpU z) = Zp-add za z
  Zp-add {lim f} za (zpU z) = Zp-add za z
  Zp-add {limᴼ k g} za (zpU z) = Zp-add za z

  zp-run : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {y : Ordᴸ k′} → O ≈ᵒ O′ → Zp k′ y → zero ≺ᴬ run O′ y
  zp-run {O′ = idO b′} idO z = zp-base b′ z
  zp-run {y = y} (ψo m m′ a b ti o) z = zp-run o (ZpΨ m′ y (proj₂ (proj₁ (proj₂ ti))))
  zp-run (addo o ea g g′ rl s s′ za) z = zp-run o (Zp-add za z)

  z≺→ZpΩ : ∀ θ → zero ≺ᴬ θ → Zp θ (Ω θ)
  z≺→ZpΩ (suc k)    _ = zpI
  z≺→ZpΩ (limᴼ k g) _ = zpI
  z≺→ZpΩ (lim f)    (viaᴬ (n , q) d e) = zpL n (zpU (z≺→ZpΩ (f n) (viaᴬ q d e)))
```

## §2 第 0 层节点的左右规则

第 0 层的节点在一切观测下都还是第 0 层的节点 (`rise≠0`). 所以右规则可以取 `Aℓ` 里**任意**的元, 不只起点; 左规则逐分支. [Uniform](Uniform.lagda.md) 没有这两条, 因为它的 $\psi^0$ 是观测.

```agda
  sub-sym : ∀ {a b} (e : a ≡ b) (z : Ordᴸ b) → subst Ordᴸ e (subst Ordᴸ (sym e) z) ≡ z
  sub-sym refl z = refl

  limᵢ-l₀ : ∀ {k k′} {r : Pre k} {f : Low k r → Ordᴸ k} {y : Ordᴸ k′} → AdmB k r → at k r ≡ zero →
            (∀ z → Gi (at k r) z → f (intoL k r z) ⊑ᵒ y) → Zp k′ y → limᵢ r f ⊑ᵒ y
  limᵢ-l₀ {r = inj₁ _} d e0 K zy (idO {b = b1} {b′ = b′}) (inj₁ (inj₁ _)) _ = zp-base b′ zy
  limᵢ-l₀ {r = inj₁ _} d e0 K zy (idO {b = b1} {b′ = b′}) (inj₂ (x , q)) (ax , dq) = K x ax (idO {b = b1} {b′ = b′}) q dq
  limᵢ-l₀ {k} {k′} {r} {f} {y} d e0 K zy (ψo {i = i} m m′ a b ti o) with verdict S m r | okV k m a r d
  ... | _ | cvp r₁ e₁ a₁ =
    limᵢ-l₀ {r = r₁} {f = λ w → ψᵖ m (f (intoL k r (subst Ordᴸ e₁ (outL i r₁ w))))} {y = ψᵖ m′ y} a₁ (trans e₁ e0)
      (λ z gw → subst (λ u → ψᵖ m (f (intoL k r (subst Ordᴸ e₁ u))) ⊑ᵒ ψᵖ m′ y) (sym (out-into i r₁ z))
                      (λ o′ → K _ (Gi-sub e₁ gw) (ψo m m′ a b ti o′)))
      (ZpΨ m′ y (proj₂ (proj₁ (proj₂ ti)))) o
  ... | _ | cvr kk = ⊥-elim (rise≠0 kk (proj₁ (proj₂ ti)) e0)
  limᵢ-l₀ {k} {k′} {r} {f} {y} d e0 K zy (addo {l = l} {a = a₀} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    let e = proj₂ (σ r) in
    limᵢ-l₀ {r = proj₁ (σ r)} {f = λ w → add a₀ σ (f (intoL k r (subst Ordᴸ e (outL l (proj₁ (σ r)) w))))} {y = add a′ σ′ y}
      (s r d) (trans e e0)
      (λ z gw → subst (λ u → add a₀ σ (f (intoL k r (subst Ordᴸ e u))) ⊑ᵒ add a′ σ′ y) (sym (out-into l (proj₁ (σ r)) z))
                      (λ o′ → K _ (Gi-sub e gw) (addo o′ ea g g′ rl s s′ za)))
      (Zp-add za zy) o

  limᵢ-r₀ : ∀ {k₀ k} {x : Ordᴸ k₀} {r : Pre k} {f : Low k r → Ordᴸ k} → AdmB k r → at k r ≡ zero →
            ∀ z → Gi (at k r) z → x ⊑ᵒ f (intoL k r z) → x ⊑ᵒ limᵢ r f
  limᵢ-r₀ {r = inj₁ _} d e0 z gw p (idO {b = b} {b′ = b1}) q dq with p (idO {b = b} {b′ = b1}) q dq
  ... | viaᴬ s ds e = viaᴬ (inj₂ (z , s)) (gw , ds) e
  limᵢ-r₀ {k = k} {x = x} {r = r} {f = f} d e0 z gw p (ψo {i = i} m m′ a b ti o) with verdict S m′ r | okV k m′ b r d
  ... | _ | cvp r₁ e₁ a₁ =
    let z′ = subst Ordᴸ (sym e₁) z in
    limᵢ-r₀ {x = ψᵖ m x} {r = r₁} {f = λ w → ψᵖ m′ (f (intoL k r (subst Ordᴸ e₁ (outL i r₁ w))))} a₁ (trans e₁ e0) z′ (Gi-sub (sym e₁) gw)
      (subst (λ u → ψᵖ m x ⊑ᵒ ψᵖ m′ (f (intoL k r u)))
             (sym (trans (cong (subst Ordᴸ e₁) (out-into i r₁ z′)) (sub-sym e₁ z)))
             (λ o′ → p (ψo m m′ a b ti o′))) o
  ... | _ | cvr kk = ⊥-elim (rise≠0 kk (proj₁ (proj₂ ti)) e0)
  limᵢ-r₀ {k = k} {x = x} {r = r} {f = f} d e0 z gw p (addo {l′ = l′} {a = a₀} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    let e = proj₂ (σ′ r)
        z′ = subst Ordᴸ (sym e) z in
    limᵢ-r₀ {x = add a₀ σ x} {r = proj₁ (σ′ r)} {f = λ w → add a′ σ′ (f (intoL k r (subst Ordᴸ e (outL l′ (proj₁ (σ′ r)) w))))}
      (s′ r d) (trans e e0) z′ (Gi-sub (sym e) gw)
      (subst (λ u → add a₀ σ x ⊑ᵒ add a′ σ′ (f (intoL k r u)))
             (sym (trans (cong (subst Ordᴸ e) (out-into l′ (proj₁ (σ′ r)) z′)) (sub-sym e z)))
             (λ o′ → p (addo o′ ea g g′ rl s s′ za))) o
```

## §3 $\Omega$ 对层号单调

`Ω-path`: 后继的字面前驱. `limᴼ` 上的路径由 `branchᴬ` (证书的 `par`) 搬到某个 `Aℓ` 分支里, 这正是 `<-decᴬ` 用的同一步. `Ω-mono` 对左边递归. 第 0 层以外的 `limᴼ` 没有证书 (`¬WF-L₂`), 所以这里不覆盖它们; 那种层号的单调性由 `GLv` 的树语言条件提供.

```agda
  lvp-o : ∀ {g : Ordᴸ zero → Lv} → LvP (limᴼ zero g) → ∀ x → A zero x → LvP (g x)
  lvp-o (lg , lr , _ , vg , _) x a = proj₂ (proj₂ lg) x (a⊆b x a) , proj₁ (proj₂ lr) x (a⊆b x a) , vg x a

  Ω-path : ∀ θ′ (q : Pre θ′) → Adm θ′ q → WFᴬ θ′ → LvP θ′ → ∀ κ → LvP (suc κ) → κ ≈ᴮ at θ′ q → Ω (suc κ) ⊑ᵒ Ω θ′
  Ω-path (suc k) (inj₁ _) d w (lg , lr , _) κ (lk , rk , _) e = ≃→⊑ᵒ (Ω≃ (s≈ e) lk lg rk)
  Ω-path (suc k) (inj₂ q) d w ((_ , lt) , lr , v) κ pκ e =
    limᵢ-r tt (up-r (suc k) tt (Ω-path k q d w (t→g k lt , lr , v) κ pκ e))
  Ω-path (lim f) (n , q) d (_ , w) (lg , lr , v , _) κ pκ e =
    lim-r n (up-r (lim f) tt (Ω-path (f n) q d (w n) (lg n , lr n , v n) κ pκ e))
  Ω-path (limᴼ zero g) q d w@(dir , par , her) p κ pκ e with branchᴬ {k = zero} {g = g} par q d
  ... | x , ax , viaᴬ q′ d′ e′ =
    limᵢ-r₀ tt refl x ax
      (up-r (limᴼ zero g) (a⊆b x ax) (Ω-path (g x) q′ d′ (her x ax) (lvp-o p x ax) κ pκ (≈ᴮ-trans e e′)))
  Ω-path (limᴼ (suc _) g) q d (_ , (_ , () , _) , _)
  Ω-path (limᴼ (lim _) g) q d (_ , (_ , () , _) , _)
  Ω-path (limᴼ (limᴼ _ _) g) q d (_ , (_ , () , _) , _)

  Ω-mono : ∀ θ θ′ → WFᴬ θ → WFᴬ θ′ → LvP θ → LvP θ′ → θ ⊑ᴬ θ′ → Ω θ ⊑ᵒ Ω θ′
  Ω-mono zero θ′ w w′ p p′ σ = Ω0 θ′
  Ω-mono (suc κ) θ′ w w′ p@(_ , rk , vk) p′ σ with σ (inj₁ tt) tt
  ... | viaᴬ q d e = Ω-path θ′ q d w′ p′ κ p e
  Ω-mono (lim h) θ′ (_ , w) w′ (lg , lr , v , _) p′ σ =
    lim-l (λ n → up-l (lim h) tt (Ω-mono (h n) θ′ (w n) w′ (lg n , lr n , v n) p′ (λ r d → σ (n , r) d)))
  Ω-mono (limᴼ zero g) θ′ (_ , _ , her) w′ p p′ σ =
    limᵢ-l₀ tt refl
      (λ z az → up-l (limᴼ zero g) (a⊆b z az)
                  (Ω-mono (g z) θ′ (her z az) w′ (lvp-o p z az) p′ (λ r d → σ (inj₂ (z , r)) (az , d))))
      (z≺→ZpΩ θ′ (σ (inj₁ (inj₁ tt)) tt))
  Ω-mono (limᴼ (suc _) g) θ′ (_ , (_ , () , _) , _)
  Ω-mono (limᴼ (lim _) g) θ′ (_ , (_ , () , _) , _)
  Ω-mono (limᴼ (limᴼ _ _) g) θ′ (_ , (_ , () , _) , _)

  F-mono : ∀ θ θ′ → WFᴬ θ → WFᴬ θ′ → LvP θ → LvP θ′ → θ ⊑ᴬ θ′ → toLv (F θ) ⊑ᴬ toLv (F θ′)
  F-mono θ θ′ w w′ p p′ σ =
    Ω-mono θ θ′ w w′ p p′ σ (ψo (fin 1 refl) (fin 1 refl) (okF θ 1 refl) (okF θ′ 1 refl) Ti₁ (idO {b = b1} {b′ = b1}))
```

## §4 第 0, 1 层的好树给好层号

`lvp` 把**树的**好性翻成**层号的**好性. 唯一的前提 `LvG (toLv y)` 说 `S` 在这个层号的 $\Omega$ 节点所要的链上正确. `b⊆a` 要求叶子只看 `Aℓ`, 否则 `LvR` 要对原始分支负责.

```agda
  module Feed (b⊆a : ∀ x → B₀ x → A zero x) where
    lvp : ∀ {k} (b : BL k) {y : Ordᴸ k} → GoodT k y → Eq k y y → LvG (toLv y) → LvP (toLv y)
    lvp b gz ex _ = tt , tt , tt
    lvp b (gs g) ex lg with lvp b g (s-inv ex) (t→g _ (proj₂ lg))
    ... | _ , r , v = lg , r , v
    lvp b (gl hg st) ex lg =
      let P = λ n → lvp b (hg n) (l-inv ex n) (lg n)
      in lg , (λ n → proj₁ (proj₂ (P n))) , (λ n → proj₂ (proj₂ (P n))) ,
         (λ n → Ω-mono _ _ (wf b (hg n)) (wf b (hg (suc n))) (P n) (P (suc n)) (st n (idO {b = b} {b′ = b})))
    lvp b1 (gi {r = inj₁ _} {f = f} hb hm gΩ pos) ex@(i≃ nd nd′ e lr h) lg =
      let P = λ x (ax : A zero x) → lvp b1 (hb x ax) (i-self ex x (a⊆b x ax) (eq₀ x)) (proj₂ (proj₂ lg) x (a⊆b x ax))
      in lg ,
         (tt , (λ x bx → proj₁ (proj₂ (P x (b⊆a x bx)))) ,
               (λ z z′ bz bz′ d → b≃ b1 b1 (h z z′ bz bz′ d))) ,
         (tt , (λ z az → proj₂ (proj₂ (P z az))) ,
               (λ z z′ az az′ p → Ω-mono _ _ (wf b1 (hb z az)) (wf b1 (hb z′ az′)) (P z az) (P z′ az′) (hm z z′ az az′ p (idO {b = b1} {b′ = b1}))))
    lvp b1 (gu db g) ex lg = lvp b0 g (u-self (suc zero) ex) lg

    -- F 的输出回灌作下标
    F-self : ∀ θ → LvG θ → LvR θ → Eq (natL 1) (F θ) (F θ)
    F-self θ g r = ψ≃ (fin 1 refl) (fin 1 refl) (okF θ 1 refl) (okF θ 1 refl) (tgOf Ti₁) (Ω-self θ g r)

    lvp-F : ∀ θ → LvP θ → LvG (toLv (F θ)) → LvP (toLv (F θ))
    lvp-F θ p@(g , r , _) lg = lvp b1 (Good-F θ p) (F-self θ g r) lg

    Cert-F : ∀ θ → LvP θ → LvG (toLv (F θ)) → WFᴬ (toLv (F (toLv (F θ))))
    Cert-F θ p lg = Cert _ (lvp-F θ p lg)
```
