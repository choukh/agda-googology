# 证书与阶段无关: 观测前序 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). 由 [InaccThetaObs](InaccThetaObs.lagda.md) 改写, 大部分证明逐字. 差别: (1) 观测的底部 `idO` 在任何可取层号的层 `BL` 上, 不只第 0, 1 层; (2) 折叠观测的目标 `Ti` 有**全部**低层的字面路径, 所以全部低层的节点永远穿透, 这是 "$\psi_0$ 不是观测" 的一般形式; (3) 含 0 路径 `Zp` 换成语义的 `ZA`: "目标可取层号时, 每个低层都是它的字面前驱". 折叠与加法的输出无条件满足它 (`ZpΨ`, `ZpAdd`), 不要看输入.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKObs where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM; module PF)
open import OCF.Align.LevelKBase using (NoO; Stage)
open import OCF.Align.LevelKEq using (module Eqv)
```

## §1 观测

`idO` 在任何 `BL` 层上. 折叠观测的目标层有全部低层的字面路径 (`Ti`), 所以低层的节点永远穿透, 低层的输入不进任何链. 低层没有 Bachmann 条件: 地板里的任意元都能进分支.

```agda
module Core (S : Sib) (St : Stage) where
  open Eqv S St public

  BsΩ : ∀ j → Bs j (Ω j)
  BsΩ j l = ΩA j l

  -- 可取层号时, 每个低层都是字面前驱
  ZA : (l : Lv) → Ordᴸ l → Set
  ZA l a = ∀ j → Lw j → BL l → j ≺ᴬ toLv a

  data Obs : Lv → Set where
    idO  : ∀ {k} → BL k → Obs k
    ψo   : ∀ {k i} → Mode k i → Obs i → Obs k
    addo : ∀ {k l} → Obs l → Ordᴸ l → Sim k l → Obs k

  run : ∀ {k} → Obs k → Ordᴸ k → Lv
  run (idO _)      x = toLv x
  run (ψo m O)     x = run O (ψᵖ m x)
  run (addo O a σ) x = run O (add a σ x)

  Ti : Lv → Set
  Ti i = LvT i × Zt i × LvR i

  tgOf : ∀ {i} → Ti i → Tg i i
  tgOf {i} (g , z , r) = tg (≈ᴮ-refl i) g g z z r

  infix 4 _≈ᵒ_ _⊑ᵒ_
  data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
    idO  : ∀ {k k′} {b : BL k} {b′ : BL k′} → idO b ≈ᵒ idO b′
    ψo   : ∀ {k k′ i} {O O′ : Obs i} (m : Mode k i) (m′ : Mode k′ i) → OK k m → OK k′ m′ → Ti i → O ≈ᵒ O′ → ψo m O ≈ᵒ ψo m′ O′
    addo : ∀ {k k′ l l′} {O : Obs l} {O′ : Obs l′} {a : Ordᴸ l} {a′ : Ordᴸ l′} {σ : Sim k l} {σ′ : Sim k′ l′} →
           O ≈ᵒ O′ → Eq l a a′ → LvT l → LvT l′ → LvR l → SD σ → SD σ′ → ZA l′ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′

  run-≃ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordᴸ k} {y : Ordᴸ k′} → O ≈ᵒ O′ → Eq k x y → run O x ≈ᴮ run O′ y
  run-≃ {O = idO b} {O′ = idO b′} idO e = b≃ b b′ e
  run-≃ (ψo m m′ ok ok′ ti o) e = run-≃ o (ψ≃ m m′ ok ok′ (tgOf ti) e)
  run-≃ (addo o ea gl gl′ rl s s′ za) e = run-≃ o (add≃ gl gl′ rl s s′ ea e)

  _⊑ᵒ_ : ∀ {k k′} → Ordᴸ k → Ordᴸ k′ → Set
  _⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → run O x ⊑ᴬ run O′ y

  ≃→⊑ᵒ : ∀ {k k′} {x : Ordᴸ k} {y : Ordᴸ k′} → Eq k x y → x ⊑ᵒ y
  ≃→⊑ᵒ e o = ≈⊑ (run-≃ o e)
```

## §2 上界引理

每条都是对观测归纳: 把运算同时推进两侧. 底部是层号上的路径. `up-l`, `up-r` 对 `k` 与观测分情况, `up` 对一切运算都透明. `limᵢ-r∘` 处理所有输出节点的形状 $y\mapsto G(\mathtt{subst}\,e\,(\mathtt{out}\,y))$: 起点 $\Omega$ 经 `subst` 还是 $\Omega$ (`subst-Ω`), 这是字面穿透省掉 [Uniform](Uniform.lagda.md) 的 "$\forall z\cong\Omega_j$" 的地方.

```agda
  subst-Ω : ∀ {a b} (e : a ≡ b) → subst Ordᴸ e (Ω a) ≡ Ω b
  subst-Ω refl = refl

  lim-r : ∀ {k k′} {x : Ordᴸ k} {h : ℕ → Ordᴸ k′} n → x ⊑ᵒ h n → x ⊑ᵒ Tree.lim h
  lim-r n p (idO {b = b} {b′ = b′}) r d with p (idO {b = b} {b′ = b′}) r d
  ... | viaᴬ s ds e = viaᴬ (n , s) ds e
  lim-r {x = x} {h = h} n p (ψo m m′ a b c o) =
    lim-r {x = ψᵖ m x} {h = λ k → ψᵖ m′ (h k)} n (λ o′ → p (ψo m m′ a b c o′)) o
  lim-r {x = x} {h = h} n p (addo {a = a₀} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    lim-r {x = add a₀ σ x} {h = λ k → add a′ σ′ (h k)} n (λ o′ → p (addo o′ ea g g′ rl s s′ za)) o

  lim-l : ∀ {k k′} {h : ℕ → Ordᴸ k} {y : Ordᴸ k′} → (∀ n → h n ⊑ᵒ y) → Tree.lim h ⊑ᵒ y
  lim-l K (idO {b = b} {b′ = b′}) (n , r) d = K n (idO {b = b} {b′ = b′}) r d
  lim-l {h = h} {y = y} K (ψo m m′ a b c o) =
    lim-l {h = λ n → ψᵖ m (h n)} {y = ψᵖ m′ y} (λ n o′ → K n (ψo m m′ a b c o′)) o
  lim-l {h = h} {y = y} K (addo {a = a₀} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    lim-l {h = λ n → add a₀ σ (h n)} {y = add a′ σ′ y} (λ n o′ → K n (addo o′ ea g g′ rl s s′ za)) o

  suc-r : ∀ {k k′} {x : Ordᴸ k} {y : Ordᴸ k′} → x ⊑ᵒ y → x ⊑ᵒ Tree.suc y
  suc-r p (idO {b = b} {b′ = b′}) r d with p (idO {b = b} {b′ = b′}) r d
  ... | viaᴬ s ds e = viaᴬ (inj₂ s) ds e
  suc-r {x = x} {y = y} p (ψo m m′ a b c o) =
    lim-r {x = ψᵖ m x} {h = iter (ψᵖ m′ y +_) Tree.zero} 1 (λ o′ → p (ψo m m′ a b c o′)) o
  suc-r {x = x} {y = y} p (addo {a = a₀} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    suc-r {x = add a₀ σ x} {y = add a′ σ′ y} (λ o′ → p (addo o′ ea g g′ rl s s′ za)) o

  up-l : ∀ k {d} {x : DnT k d} {k′} {y : Ordᴸ k′} → DB k d → outD k d x ⊑ᵒ y → up d x ⊑ᵒ y
  up-l (suc k) db p (idO {b = b} {b′ = b′}) = p (idO {b = bl-suc b} {b′ = b′})
  up-l (lim f) {d} db p (idO {b = b} {b′ = b′}) = p (idO {b = bl-lim d b} {b′ = b′})
  up-l (limᴼ k g) db p (idO {b = () , _})
  up-l (suc k) {d} db p (ψo m m′ a b c o) = p (ψo (upM (suc k) d m) m′ (okU (suc k) m a d db) b c o)
  up-l (suc k) {d} db p (addo {σ = σ} o ea g g′ rl s s′ za) = p (addo o ea g g′ rl (sd∘ι (suc k) d σ s db) s′ za)
  up-l (lim f) {d} db p (ψo m m′ a b c o) = p (ψo (upM (lim f) d m) m′ (okU (lim f) m a d db) b c o)
  up-l (lim f) {d} db p (addo {σ = σ} o ea g g′ rl s s′ za) = p (addo o ea g g′ rl (sd∘ι (lim f) d σ s db) s′ za)
  up-l (limᴼ k g) {d} db p (ψo m m′ a b c o) = p (ψo (upM (limᴼ k g) d m) m′ (okU (limᴼ k g) m a d db) b c o)
  up-l (limᴼ k h) {d} db p (addo {σ = σ} o ea g g′ rl s s′ za) = p (addo o ea g g′ rl (sd∘ι (limᴼ k h) d σ s db) s′ za)

  up-r : ∀ k′ {d} {y : DnT k′ d} {k} {x : Ordᴸ k} → DB k′ d → x ⊑ᵒ outD k′ d y → x ⊑ᵒ up d y
  up-r (suc k) db p (idO {b = b} {b′ = b′}) = p (idO {b = b} {b′ = bl-suc b′})
  up-r (lim f) {d} db p (idO {b = b} {b′ = b′}) = p (idO {b = b} {b′ = bl-lim d b′})
  up-r (limᴼ k g) db p (idO {b′ = () , _})
  up-r (suc k) {d} db p (ψo m m′ a b c o) = p (ψo m (upM (suc k) d m′) a (okU (suc k) m′ b d db) c o)
  up-r (suc k) {d} db p (addo {σ′ = σ} o ea g g′ rl s s′ za) = p (addo o ea g g′ rl s (sd∘ι (suc k) d σ s′ db) za)
  up-r (lim f) {d} db p (ψo m m′ a b c o) = p (ψo m (upM (lim f) d m′) a (okU (lim f) m′ b d db) c o)
  up-r (lim f) {d} db p (addo {σ′ = σ} o ea g g′ rl s s′ za) = p (addo o ea g g′ rl s (sd∘ι (lim f) d σ s′ db) za)
  up-r (limᴼ k g) {d} db p (ψo m m′ a b c o) = p (ψo m (upM (limᴼ k g) d m′) a (okU (limᴼ k g) m′ b d db) c o)
  up-r (limᴼ k h) {d} db p (addo {σ′ = σ} o ea g g′ rl s s′ za) = p (addo o ea g g′ rl s (sd∘ι (limᴼ k h) d σ s′ db) za)

  into-Ω : ∀ {k′} k (r : Pre k) {j} (e : at k r ≡ j) (G : Ordᴸ j → Ordᴸ k′) →
           (λ y → G (subst Ordᴸ e (outL k r y))) (intoL k r (Ω (at k r))) ≡ G (Ω j)
  into-Ω k r refl G = cong G (out-into k r (Ω (at k r)))

  limᵢ-r : ∀ {k k′} {x : Ordᴸ k} {r : Pre k′} {f : Low k′ r → Ordᴸ k′} → AdmB k′ r →
           x ⊑ᵒ f (intoL k′ r (Ω (at k′ r))) → x ⊑ᵒ limᵢ r f
  limᵢ-r {k′ = k′} {r = r} d p (idO {b = b} {b′ = b′}) q dq with p (idO {b = b} {b′ = b′}) q dq
  ... | viaᴬ s ds e = viaᴬ (inj₂ (Ω (at k′ r) , s)) (ΩA (at k′ r) (proj₂ b′ r) , ds) e
  limᵢ-r {k′ = k′} {x = x} {r = r} {f = f} d p (ψo {i = i} m m′ a b c o) with verdict S m′ r | okV k′ m′ b r d
  ... | _ | cvp r₁ e₁ a₁ =
    limᵢ-r {x = ψᵖ m x} {r = r₁} {f = λ y → ψᵖ m′ (f (intoL k′ r (subst Ordᴸ e₁ (outL i r₁ y))))} a₁
      (subst (λ u → ψᵖ m x ⊑ᵒ u) (sym (into-Ω i r₁ e₁ (λ z → ψᵖ m′ (f (intoL k′ r z)))))
             (λ o′ → p (ψo m m′ a b c o′))) o
  ... | _ | cvr _ =
    lim-r {x = ψᵖ m x} {h = λ n → ψᵖ m′ (f (intoL k′ r (iter (λ w → ψᵖ (chM k′ r) (f (intoL k′ r w))) (Ω (at k′ r)) n)))} 0
      (λ o′ → p (ψo m m′ a b c o′)) o
  limᵢ-r {k′ = k′} {x = x} {r = r} {f = f} d p (addo {l′ = l′} {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o ea g g′ rl s s′ za) =
    limᵢ-r {x = add a σ x} {r = proj₁ (σ′ r)} {f = λ y → add a′ σ′ (f (intoL k′ r (subst Ordᴸ (proj₂ (σ′ r)) (outL l′ (proj₁ (σ′ r)) y))))} (s′ r d)
      (subst (λ u → add a σ x ⊑ᵒ u)
             (sym (into-Ω l′ (proj₁ (σ′ r)) (proj₂ (σ′ r)) (λ z → add a′ σ′ (f (intoL k′ r z)))))
             (λ o′ → p (addo o′ ea g g′ rl s s′ za))) o

  limᵢ-r∘ : ∀ {k k′ j} {x : Ordᴸ k} {r : Pre k′} (e : at k′ r ≡ j) {G : Ordᴸ j → Ordᴸ k′} → AdmB k′ r →
            x ⊑ᵒ G (Ω j) → x ⊑ᵒ limᵢ r (λ y → G (subst Ordᴸ e (outL k′ r y)))
  limᵢ-r∘ {k′ = k′} {x = x} {r = r} e {G} d p =
    limᵢ-r d (subst (λ u → x ⊑ᵒ u) (sym (into-Ω k′ r e G)) p)
```

## §3 起点

`ΩB` 是 Bachmann 性质的下半: 任何折叠都不低于目标的 $\Omega$. `add-r`, `zero-l` 同 [Uniform](Uniform.lagda.md). 对 `Eq` 的推导归纳, 所以任何自相似的树都行. `Ω0`: $1\sqsubseteq^\mathsf{o}\Omega_\theta$ 对一切原始的 $\theta$.

```agda
  ΩL : ∀ k r → ND k r → LRo k r → ∀ {k′} (r′ : Pre k′) → ND k′ r′ → at k r ≈ᴮ at k′ r′ → RLo k r (Ω (at k r)) (Ω (at k′ r′))
  ΩL k r nd lr r′ nd′ e = Eq→R k r (Ω≃ e (t→g _ (proj₂ (proj₂ nd))) (t→g _ (proj₂ (proj₂ nd′))) (L→R k r (proj₁ nd) lr))

  ΩB : ∀ {k k₀ k′ i} {x : Ordᴸ k₀} (m : Mode k i) {z : Ordᴸ k} {y : Ordᴸ k′} → OK k m → x ⊑ᵒ Ω i → Eq k z y → x ⊑ᵒ ψᵖ m z
  ΩB m ok p z≃ = p
  ΩB m ok p (s≃ e) = lim-r 1 (ΩB m ok p e)
  ΩB m ok p (l≃ h) = lim-r 0 (ΩB m ok p (h 0))
  ΩB {k} {k′ = k′} {i = i} m ok p (i≃ {k′ = k₁} {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h) with verdict S m r | okV k m ok r (proj₁ nd)
  ... | _ | cvp r₁ e₁ a₁ = limᵢ-r∘ e₁ {G = λ z → ψᵖ m (f (intoL k r z))} a₁
        (ΩB m ok p (h _ _ (BsΩ (at k r)) (BsΩ (at k₁ r′)) (inj₁ (ΩL k r nd lr r′ nd′ e))))
  ... | _ | cvr _ = lim-r 0 (ΩB m ok p (h _ _ (BsΩ (at k r)) (BsΩ (at k₁ r′)) (inj₁ (ΩL k r nd lr r′ nd′ e))))
  ΩB {suc k} m ok p (uˡ {d = d} db e) = ΩB (upM (suc k) d m) (okU (suc k) m ok d db) p e
  ΩB {lim f} m ok p (uˡ {d = d} db e) = ΩB (upM (lim f) d m) (okU (lim f) m ok d db) p e
  ΩB {limᴼ k g} m ok p (uˡ {d = d} db e) = ΩB (upM (limᴼ k g) d m) (okU (limᴼ k g) m ok d db) p e
  ΩB m ok p (uʳ db e) = ΩB m ok p e

  add-r : ∀ {k k₀ k′ l} {x : Ordᴸ k₀} {a : Ordᴸ l} {σ : Sim k l} {b : Ordᴸ k} {y : Ordᴸ k′} → SD σ → x ⊑ᵒ a → Eq k b y → x ⊑ᵒ add a σ b
  add-r s p z≃ = p
  add-r s p (s≃ e) = suc-r (add-r s p e)
  add-r s p (l≃ h) = lim-r 0 (add-r s p (h 0))
  add-r {k} {a = a} {σ = σ} s p (i≃ {k′ = k₁} {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h) =
    limᵢ-r∘ (proj₂ (σ r)) {G = λ z → add a σ (f (intoL k r z))} (s r (proj₁ nd))
      (add-r s p (h _ _ (BsΩ (at k r)) (BsΩ (at k₁ r′)) (inj₁ (ΩL k r nd lr r′ nd′ e))))
  add-r {suc k} {σ = σ} s p (uˡ {d = d} db e) = add-r (sd∘ι (suc k) d σ s db) p e
  add-r {lim f} {σ = σ} s p (uˡ {d = d} db e) = add-r (sd∘ι (lim f) d σ s db) p e
  add-r {limᴼ k g} {σ = σ} s p (uˡ {d = d} db e) = add-r (sd∘ι (limᴼ k g) d σ s db) p e
  add-r s p (uʳ db e) = add-r s p e

  Ωi≃ : ∀ {i} → Ti i → Eq i (Ω i) (Ω i)
  Ωi≃ {i} (g , _ , r) = Ω≃ (≈ᴮ-refl i) (t→g i g) (t→g i g) r

  𝟎 : ∀ {k} → Ordᴸ k
  𝟎 = Tree.zero

  zero-l : ∀ {k k′ k″} {y : Ordᴸ k′} {y′ : Ordᴸ k″} → Eq k′ y y′ → 𝟎 {k} ⊑ᵒ y
  zero-l e idO = λ ()
  zero-l e (ψo m m′ a b c o) = ΩB m′ b (≃→⊑ᵒ (Ωi≃ c)) e o
  zero-l e (addo o ea g g′ rl s s′ za) = add-r s′ (≃→⊑ᵒ ea) e o

  Ω0 : ∀ θ → Ω zero ⊑ᵒ Ω θ
  Ω0 zero       = ≃→⊑ᵒ (s≃ z≃)
  Ω0 (suc b)    = limᵢ-r tt (up-r (suc b) tt (Ω0 b))
  Ω0 (lim f)    = lim-r 0 (up-r (lim f) tt (Ω0 (f 0)))
  Ω0 (limᴼ k g) = limᵢ-r tt (up-r (limᴼ k g) (BsΩ k) (Ω0 (g (Ω k))))
```

## §4 低层是输出的字面前驱

折叠与加法的输出在可取层号的目标上含全部低层: 新节点的分支取 $\Omega$, 递归. 输入是什么都行. 这里没有用到 Bachmann 性质, 只用了 `Ti` 的 `Zt` 给的字面路径 (`Ω≺`).

```agda
  Ω≺ : ∀ {i} → Zt i → BL i → ∀ j → Lw j → j ≺ᴬ toLv (Ω i)
  Ω≺ {i} z b j l with z j l
  ... | r , d , refl = path→Ω i r d

  zpBr : ∀ {j l} {r′ : Pre l} {G : Low l r′ → Ordᴸ l} → BL l → ∀ z → A (at l r′) z → j ≺ᴬ toLv (G (intoL l r′ z)) → j ≺ᴬ toLv (limᵢ r′ G)
  zpBr b z az (viaᴬ q d e) = viaᴬ (inj₂ (z , q)) (az , d) e

  ZpAdd : ∀ {k l} {a : Ordᴸ l} {σ : Sim k l} j → BL l → j ≺ᴬ toLv a → (x : Ordᴸ k) → j ≺ᴬ toLv (add a σ x)
  ZpAdd j b p Tree.zero = p
  ZpAdd {σ = σ} j b p (Tree.suc x) with ZpAdd {σ = σ} j b p x
  ... | viaᴬ q d e = viaᴬ (inj₂ q) d e
  ZpAdd {σ = σ} j b p (Tree.lim f) with ZpAdd {σ = σ} j b p (f 0)
  ... | viaᴬ q d e = viaᴬ (0 , q) d e
  ZpAdd {k} {l} {a} {σ = σ} j b p (limᵢ r f) =
    let r′ = proj₁ (σ r)
        ez = Ω (at l r′)
    in zpBr {l = l} {r′ = r′} {G = λ y → add a σ (f (intoL k r (subst Ordᴸ (proj₂ (σ r)) (outL l r′ y))))} b ez (ΩA (at l r′) (proj₂ b r′))
         (ZpAdd {σ = σ} j b p (f (intoL k r (subst Ordᴸ (proj₂ (σ r)) (outL l r′ (intoL l r′ ez))))))
  ZpAdd {suc k} {l} {a} {σ} j b p (up d x) = ZpAdd {k} {l} {a} {_∘σ_ {b = suc k} {c = l} σ (ι (suc k) d)} j b p x
  ZpAdd {lim f} {l} {a} {σ} j b p (up d x) = ZpAdd {f d} {l} {a} {_∘σ_ {b = lim f} {c = l} σ (ι (lim f) d)} j b p x
  ZpAdd {limᴼ k g} {l} {a} {σ} j b p (up d x) = ZpAdd {g d} {l} {a} {_∘σ_ {b = limᴼ k g} {c = l} σ (ι (limᴼ k g) d)} j b p x
```

```agda
  ZpΨ : ∀ {k i} (m : Mode k i) j → BL i → j ≺ᴬ toLv (Ω i) → (x : Ordᴸ k) → j ≺ᴬ toLv (ψᵖ m x)
  ZpΨ m j b p Tree.zero = p
  ZpΨ m j b p (Tree.suc x) with ZpΨ m j b p x
  ... | viaᴬ q d e = viaᴬ (1 , q) d e
  ZpΨ m j b p (Tree.lim f) with ZpΨ m j b p (f 0)
  ... | viaᴬ q d e = viaᴬ (0 , q) d e
  ZpΨ {k} {i} m j b p (limᵢ r f) with verdict S m r
  ... | pen r′ g = zpBr {l = i} {r′ = r′} {G = λ y → ψᵖ m (f (intoL k r (g (outL i r′ y))))} b (Ω (at i r′)) (ΩA (at i r′) (proj₂ b r′))
                     (ZpΨ m j b p (f (intoL k r (g (outL i r′ (intoL i r′ (Ω (at i r′))))))))
  ... | rise with ZpΨ m j b p (f (intoL k r (Ω (at k r))))
  ...   | viaᴬ q d e = viaᴬ (0 , q) d e
  ZpΨ {suc k}    m j b p (up d x) = ZpΨ (upM (suc k) d m) j b p x
  ZpΨ {lim f}    m j b p (up d x) = ZpΨ (upM (lim f) d m) j b p x
  ZpΨ {limᴼ k g} m j b p (up d x) = ZpΨ (upM (limᴼ k g) d m) j b p x

  ZA-ψ : ∀ {k i} (m : Mode k i) → Zt i → (x : Ordᴸ k) → ZA i (ψᵖ m x)
  ZA-ψ m z x j l b = ZpΨ m j b (Ω≺ z b j l) x

  ZA-add : ∀ {k l} {a : Ordᴸ l} {σ : Sim k l} → ZA l a → (x : Ordᴸ k) → ZA l (add a σ x)
  ZA-add {σ = σ} za x j lw b = ZpAdd {σ = σ} j b (za j lw b) x
```
