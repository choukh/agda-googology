# 分层的 $\approx$: 闭包定理与证书 (底座)

> 底座, 不含记号. 结论写在 [LvStrat](LvStrat.lagda.md). 由 [LevelKClose](LevelKClose.lagda.md) 改写, 证明大部分逐字: 差别只有 `pos` 用 `blL`, `ZA-ψ`, `ZA-add` 带 `Eq`, `wf` 的 `up` 不再是空情形.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratClose where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM)
open import OCF.Align.LvStratBase using (Stage)
open import OCF.Align.LvStratGood using (module Good)
```

## §1 加法

```agda
module Close (S : Sib) (St : Stage) where
  open Good S St public

  Ωs : ∀ {k} {r : Pre k} → ND k r → LRo k r → Eq (at k r) (Ω (at k r)) (Ω (at k r))
  Ωs {k} {r} nd lr = Ω≃ (≈ᴮ-refl _) (t→g _ (proj₂ (proj₂ nd))) (t→g _ (proj₂ (proj₂ nd))) (L→R k r (proj₁ nd) lr)

  Good-add : ∀ {k l} {a : Ordᴸ l} {σ : Sim k l} {b : Ordᴸ k} → LvT l → LvR l → SD σ → Eq l a a → ZA l a →
             GoodT l a → GoodT k b → Eq k b b → GoodT l (add a σ b)
  Good-add gv rl s ea za ga gz ex = ga
  Good-add gv rl s ea za ga (gs g) ex = gs (Good-add gv rl s ea za ga g (s-inv ex))
  Good-add {a = a} {σ = σ} gv rl s ea za ga (gl {h = h} hg st) ex =
    gl (λ n → Good-add gv rl s ea za ga (hg n) (l-inv ex n))
       (λ n o → st n (addo o ea gv gv rl s s (za , ea , rl)))
  Good-add {k} {l} {a} {σ} gv rl s ea za ga (gi {r = r} {f = f} hb hm gΩ pos) ex =
    let e = proj₂ (σ r)
        nd = proj₁ (proj₂ (i-nd ex))
        lr = proj₂ (proj₂ (i-nd ex))
    in gi∘ {g = λ z → add a σ (f (intoL k r (subst Ordᴸ e z)))}
      (λ z d → let gz′ = Gi-sub e (L→Gi l _ d)
               in Good-add gv rl s ea za ga (hb _ (Gi→L k r gz′))
                    (i-self ex _ (Gi→Bs (at k r) gz′) (Gi→PE (at k r) gz′)))
      (λ z z′ d d′ p o → hm _ _ (Gi→L k r (Gi-sub e (L→Gi l _ d))) (Gi→L k r (Gi-sub e (L→Gi l _ d′)))
                            (⊑ᵒ-sub e p) (addo o ea gv gv rl s s (za , ea , rl)))
      (Gi→L l _ (GiΩ-sub e (L→Gi k r gΩ)))
      (λ bl → let l′ = blL bl (proj₁ (σ r)) (s r (proj₁ (i-nd ex)))
                  gz′ = Gi-sub e (inj₁ (ΩA _ l′))
              in Ω _ , ΩA _ l′ , ZA-add {σ = σ} s za (i-self ex _ (Gi→Bs (at k r) gz′) (Gi→PE (at k r) gz′)) _ l′ bl)
  Good-add {suc k} {σ = σ} gv rl s ea za ga (gu {d = d} db g) ex =
    Good-add gv rl (sd∘ι (suc k) d σ s db) ea za ga g (u-self (suc k) ex)
  Good-add {lim f} {σ = σ} gv rl s ea za ga (gu {d = d} db g) ex =
    Good-add gv rl (sd∘ι (lim f) d σ s db) ea za ga g (u-self (lim f) ex)
  Good-add {limᴼ k h} {σ = σ} gv rl s ea za ga (gu {d = d} db g) ex =
    Good-add gv rl (sd∘ι (limᴼ k h) d σ s db) ea za ga g (u-self (limᴼ k h) ex)

  Good-iter : ∀ {i} {c : Ordᴸ i} → LvT i → LvR i → Eq i c c → ZA i c → GoodT i c →
              ∀ n → GoodT i (iter (c +_) Tree.zero n)
  Good-iter gv rl ec zc gc zero    = gz
  Good-iter {i} gv rl ec zc gc (suc n) =
    Good-add gv rl (sd-id {i}) ec zc gc (Good-iter gv rl ec zc gc n) (iter≃ gv gv rl ec n)

  rule4ᵒ : ∀ {i} {c : Ordᴸ i} → LvT i → LvR i → Eq i c c → ZA i c → ∀ n → iter (c +_) Tree.zero n ⊑ᵒ iter (c +_) Tree.zero (suc n)
  rule4ᵒ gv rl ec zc zero    = zero-l ec
  rule4ᵒ {i} gv rl ec zc (suc n) o = rule4ᵒ gv rl ec zc n (addo o ec gv gv rl (sd-id {i}) (sd-id {i}) (zc , ec , rl))
```

## §2 折叠与链

`Good-ψ` 的两个分支: 穿透时新节点的分支还是单调的, 起点经 `subst-Ω` 还是 $\Omega$; 上升时要 `chain-good` 与 `chain-step`. 链的目标是 `at k r`, 由 `rise≠low` 它不是低层, 所以链点是好且自相似的树, 不碰地板.

```agda
  chain-self : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) → (Lw (at k r) → ⊥) →
               ∀ n → Eq (at k r) (chain k r f n) (chain k r f n)
  chain-self {f = f} (i≃ nd nd′ e lr h) n₀ n = chain≃ {f = f} {f′ = f} nd nd′ e lr n₀ n₀ h n

  Ti-ch : ∀ {k} {r : Pre k} → ND k r → LRo k r → (Lw (at k r) → ⊥) → OK k (chM k r) × Ti (at k r)
  Ti-ch {k} {r} nd lr n₀ =
    let c = chOK k r (proj₁ (proj₂ nd)) n₀
    in proj₁ c , proj₂ (proj₂ nd) , proj₂ c , L→R k r (proj₁ nd) lr

  Good-ψ : ∀ {k i} (m : Mode k i) {x : Ordᴸ k} → OK k m → Ti i → GoodT i (Ω i) → GoodT k x → Eq k x x → GoodT i (ψᵖ m x)
  chain-good : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) → (Lw (at k r) → ⊥) →
               (∀ z → GLo k r z → GoodT k (f (intoL k r z))) → GLo k r (Ω (at k r)) →
               ∀ n → Gi (at k r) (chain k r f n)
  chain-step : ∀ {k} {r : Pre k} {f : Low k r → Ordᴸ k} → Eq k (limᵢ r f) (limᵢ r f) → (Lw (at k r) → ⊥) →
               (∀ z → GLo k r z → GoodT k (f (intoL k r z))) →
               (∀ z z′ → GLo k r z → GLo k r z′ → z ⊑ᵒ z′ → f (intoL k r z) ⊑ᵒ f (intoL k r z′)) →
               GLo k r (Ω (at k r)) →
               ∀ n → chain k r f n ⊑ᵒ chain k r f (suc n)

  Good-ψ m ok ti gΩi gz ex = gΩi
  Good-ψ m ok ti gΩi (gs {a} g) ex =
    let ea = s-inv ex
        ec = ψ≃ m m ok ok (tgOf ti) ea
        zc = ZA-ψ m ok (proj₁ (proj₂ ti)) ea
    in gl (Good-iter (proj₁ ti) (proj₂ (proj₂ ti)) ec zc (Good-ψ m ok ti gΩi g ea))
          (rule4ᵒ (proj₁ ti) (proj₂ (proj₂ ti)) ec zc)
  Good-ψ m ok ti gΩi (gl hg st) ex =
    gl (λ n → Good-ψ m ok ti gΩi (hg n) (l-inv ex n)) (λ n o → st n (ψo m m ok ok ti o))
  Good-ψ {k} {i} m ok ti gΩi (gi {r = r} {f = f} hb hm gΩ pos) ex
    with verdict S m r | okV k m ok r (proj₁ (i-nd ex))
  ... | _ | cvp r₁ e₁ a₁ =
    gi∘ {g = λ z → ψᵖ m (f (intoL k r (subst Ordᴸ e₁ z)))}
      (λ z d → let gz′ = Gi-sub e₁ (L→Gi i r₁ d)
               in Good-ψ m ok ti gΩi (hb _ (Gi→L k r gz′)) (i-self ex _ (Gi→Bs (at k r) gz′) (Gi→PE (at k r) gz′)))
      (λ z z′ d d′ p o → hm _ _ (Gi→L k r (Gi-sub e₁ (L→Gi i r₁ d))) (Gi→L k r (Gi-sub e₁ (L→Gi i r₁ d′)))
                            (⊑ᵒ-sub e₁ p) (ψo m m ok ok ti o))
      (Gi→L i r₁ (GiΩ-sub e₁ (L→Gi k r gΩ)))
      (λ bi → let l′ = blL bi r₁ a₁
                  gz′ = Gi-sub e₁ (inj₁ (ΩA _ l′))
              in Ω _ , ΩA _ l′ , ZA-ψ m ok (proj₁ (proj₂ ti)) (i-self ex _ (Gi→Bs (at k r) gz′) (Gi→PE (at k r) gz′)) _ l′ bi)
  ... | _ | cvr kk =
    let n₀ = rise≠low kk (proj₁ (proj₂ ti))
        cg = chain-good ex n₀ hb gΩ
    in gl (λ n → Good-ψ m ok ti gΩi (hb _ (Gi→L k r (cg n))) (i-self ex _ (Gi→Bs (at k r) (cg n)) (Gi→PE (at k r) (cg n))))
          (λ n o → hm _ _ (Gi→L k r (cg n)) (Gi→L k r (cg (suc n))) (chain-step ex n₀ hb hm gΩ n) (ψo m m ok ok ti o))
  Good-ψ {suc k} m ok ti gΩi (gu {d = d} db g) ex = Good-ψ (upM (suc k) d m) (okU (suc k) m ok d db) ti gΩi g (u-self (suc k) ex)
  Good-ψ {lim f} m ok ti gΩi (gu {d = d} db g) ex = Good-ψ (upM (lim f) d m) (okU (lim f) m ok d db) ti gΩi g (u-self (lim f) ex)
  Good-ψ {limᴼ k h} m ok ti gΩi (gu {d = d} db g) ex = Good-ψ (upM (limᴼ k h) d m) (okU (limᴼ k h) m ok d db) ti gΩi g (u-self (limᴼ k h) ex)

  chain-good {k} {r} ex n₀ hb gΩ zero = L→Gi k r gΩ
  chain-good {k} {r} {f} ex n₀ hb gΩ (suc n) =
    let nd = proj₁ (proj₂ (i-nd ex))
        lr = proj₂ (proj₂ (i-nd ex))
        c  = Ti-ch {k} {r} nd lr n₀
        gn = chain-good ex n₀ hb gΩ n
    in G→Gi (at k r) n₀
         (Good-ψ (chM k r) (proj₁ c) (proj₂ c) (Gi→Gd (at k r) (L→Gi k r gΩ))
                 (hb _ (Gi→L k r gn)) (i-self ex _ (Gi→Bs (at k r) gn) (Gi→PE (at k r) gn)))
         (chain-self ex n₀ (suc n))

  chain-step {k} {r} {f} ex n₀ hb hm gΩ zero =
    let nd = proj₁ (proj₂ (i-nd ex))
        lr = proj₂ (proj₂ (i-nd ex))
        c  = Ti-ch {k} {r} nd lr n₀
    in ΩB (chM k r) (proj₁ c) (≃→⊑ᵒ (Ωs nd lr)) (i-self ex _ (BsΩ (at k r)) (inj₁ (Ωs nd lr)))
  chain-step {k} {r} {f} ex n₀ hb hm gΩ (suc n) o =
    let nd = proj₁ (proj₂ (i-nd ex))
        lr = proj₂ (proj₂ (i-nd ex))
        c  = Ti-ch {k} {r} nd lr n₀
        cg = chain-good ex n₀ hb gΩ
    in hm _ _ (Gi→L k r (cg n)) (Gi→L k r (cg (suc n))) (chain-step ex n₀ hb hm gΩ n)
          (ψo (chM k r) (chM k r) (proj₁ c) (proj₁ c) (proj₂ c) o)
```

## §3 好的层号

`GLv θ` 是**树语言**里的条件: 极限脊上 $\Omega$ 单调, `limᴼ` 的分支在好输入上好且单调. `LvG`, `LvR` 是判决与尊重. 三者合起来就是 "$\theta$ 是好层号" (`LvP`).

```agda
  GLv : Lv → Set
  GLv zero       = ⊤
  GLv (suc j)    = GLv j
  GLv (lim f)    = (∀ n → GLv (f n)) × (∀ n → Ω (f n) ⊑ᵒ Ω (f (suc n)))
  GLv (limᴼ j g) = GLv j × (∀ z → Gi j z → GLv (g z)) × (∀ z z′ → Gi j z → Gi j z′ → z ⊑ᵒ z′ → Ω (g z) ⊑ᵒ Ω (g z′)) ×
                   (BL (limᴼ j g) → Σ (Ordᴸ j) λ x₀ → A j x₀ × j ≺ᴬ toLv (Ω (g x₀)))

  LvP : Lv → Set
  LvP θ = LvG θ × LvR θ × GLv θ

  Ω-self : ∀ θ → LvG θ → LvR θ → Eq θ (Ω θ) (Ω θ)
  Ω-self θ g r = Ω≃ (≈ᴮ-refl θ) g g r

  Good-Ω : ∀ θ → LvP θ → GoodT θ (Ω θ)
  Gi-Ω : ∀ j → LvP j → Gi j (Ω j)

  Gi-Ω j p@(g , r , _) = inj₂ (Good-Ω j p , Ω-self j g r , BsΩ j)

  Good-Ω zero _ = gs gz
  Good-Ω (suc j) (g , r , v) =
    gi {r = inj₁ tt} {f = up tt} (λ z d → gu tt (Gi→Gd j d))
       (λ z z′ d d′ p → up-l (suc j) tt (up-r (suc j) tt p))
       (Gi-Ω j (t→g j (proj₂ g) , r , v))
       (λ b → let l = b (inj₁ tt) tt in Ω j , ΩA j l , pΩ j l)
  Good-Ω (lim f) (g , r , v , st) =
    gl (λ n → gu tt (Good-Ω (f n) (g n , r n , v n)))
       (λ n → up-l (lim f) tt (up-r (lim f) tt (st n)))
  Good-Ω (limᴼ j h) (g , r , v , vg , mo , pr) =
    gi {r = inj₁ (inj₁ tt)} {f = λ x → up x (Ω (h x))}
       (λ z d → let bz = Gi→Bs j d in gu bz (Good-Ω (h z) (proj₂ (proj₂ g) z bz , proj₁ (proj₂ r) z bz , vg z d)))
       (λ z z′ d d′ p → up-l (limᴼ j h) (Gi→Bs j d) (up-r (limᴼ j h) (Gi→Bs j d′) (mo z z′ d d′ p)))
       (Gi-Ω j (t→g j (proj₁ (proj₂ g)) , proj₁ r , v))
       pr
```

## §4 可取层号的层上的好树有证书

这里才用到地板的有向性 (`A-dir`). `limᴼ` 节点: 比较落在 `dir`, 起点给 `par`, 分支给 `her`. **这个定理不提阶段**: 层是 `BL` 就行.

```agda
  wf : ∀ {k} → BL k → {x : Ordᴸ k} → GoodT k x → WFᴬ (toLv x)
  wf b gz = tt
  wf b (gs g) = wf b g
  wf b (gl hg st) = (λ n → st n (idO {b = b} {b′ = b})) , (λ n → wf b (hg n))
  wf {k} b (gi {r = r} {f = f} hb hm gΩ pos) =
    (λ x y ax ay → let z , az , px , py = A-dir (at k r) x y ax ay
                   in z , az ,
                      hm x z (Gi→L k r (inj₁ ax)) (Gi→L k r (inj₁ az)) px (idO {b = b} {b′ = b}) ,
                      hm y z (Gi→L k r (inj₁ ay)) (Gi→L k r (inj₁ az)) py (idO {b = b} {b′ = b})) ,
    (let x₀ , ax , p = pos b in x₀ , ax , p , ≺→⊑ p) ,
    (λ x ax → wf b (hb x (Gi→L k r (inj₁ ax))))
  wf {suc k} b (gu db g) = wf (bl-suc b) g
  wf {lim f} b (gu {d = n} db g) = wf (bl-lim n b) g
  wf {limᴼ k h} b (gu {d = x} db g) = wf (bl-o b (db (bl-par b))) g
```
