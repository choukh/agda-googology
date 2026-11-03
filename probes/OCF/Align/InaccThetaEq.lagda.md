# 全部 $\theta$ 的证书: 判决的正确性与树的相似 (底座)

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). `CV` 说一个判决在语义上正确: 穿透的路径字面地落在节点层上, 上升时目标里没有可容许的路径 $\approx$ 节点层. `OK` 把它沿 `up` 遗传. `Eq` 是 [Level](Level.lagda.md) 的 $\cong$ 在 `Lv` 上的版本, 跨层, 分支只在 `Bs` 里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccThetaEq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv;
   Sim; σ-id; ι; _∘σ_; add; _+_; iter; Verdict; pen; rise)
open import OCF.Align.InaccFloorTree using (Sib; Mode; upM; verdict; chM; module PF)
open import OCF.Align.InaccThetaRel using (module Leaf)
```

## §1 判决的正确性

`verdict S m r` 的类型不要求它为真. 这里把 "真" 写出来. 穿透: 路径字面地落在节点层上. 上升: 目标里没有可容许的路径 $\approx$ 节点层. 所以两个 `≈ᴮ`-相关的层不可能一个穿透一个上升 (`clash`).

```agda
module Eqv (S : Sib) (B₀ : Ordᴸ zero → Set) where
  open Leaf B₀ public
  open PF S public

  data CV {j i : Lv} : Verdict j i → Set where
    cvp : ∀ (r : Pre i) (e : at i r ≡ j) → AdmB i r → CV (pen r (subst Ordᴸ e))
    cvr : (∀ (r : Pre i) → AdmB i r → at i r ≈ᴮ j → ⊥) → CV rise

  OK : (k : Lv) {i : Lv} → Mode k i → Set
  OK zero       m = ⊤
  OK (suc k)    m = (∀ r → AdmB (suc k) r → CV (verdict S m r)) × OK k (upM (suc k) tt m)
  OK (lim f)    m = (∀ r → AdmB (lim f) r → CV (verdict S m r)) × (∀ n → OK (f n) (upM (lim f) n m))
  OK (limᴼ k g) m = (∀ r → AdmB (limᴼ k g) r → CV (verdict S m r)) × (∀ x → Bs k x → OK (g x) (upM (limᴼ k g) x m))

  -- `up` 的条件: 跨过 `limᴼ` 时分支要在 `Bs` 里
  DB : (k : Lv) → Dn k → Set
  DB (suc _)    _ = ⊤
  DB (lim _)    _ = ⊤
  DB (limᴼ k _) x = Bs k x

  okV : ∀ k {i} (m : Mode k i) → OK k m → ∀ r → AdmB k r → CV (verdict S m r)
  okV (suc k)    m w = proj₁ w
  okV (lim f)    m w = proj₁ w
  okV (limᴼ k g) m w = proj₁ w

  okU : ∀ k {i} (m : Mode k i) → OK k m → ∀ d → DB k d → OK (down k d) (upM k d m)
  okU (suc k)    m w d _  = proj₂ w
  okU (lim f)    m w d _  = proj₂ w d
  okU (limᴼ k g) m w d db = proj₂ w d db

  -- 结构上的 "含 0 路径": 折叠与加法都保持它, 第 1 层就给出 `zero ≺ᴬ toLv x`
  data Zp : (k : Lv) → Ordᴸ k → Set where
    zpZ : ∀ {k} → Zp k (Tree.suc Tree.zero)
    zpS : ∀ {k} {a : Ordᴸ k} → Zp k a → Zp k (Tree.suc a)
    zpL : ∀ {k} {h : ℕ → Ordᴸ k} n → Zp k (h n) → Zp k (Tree.lim h)
    zpI : ∀ {k} {r} {f : Low k r → Ordᴸ k} → Zp k (limᵢ r f)
    zpU : ∀ {k} {d} {x : DnT k d} → Zp (down k d) (outD k d x) → Zp k (up d x)

  ZpΨ : ∀ {k i} (m : Mode k i) (x : Ordᴸ k) → Zp i (Ω i) → Zp i (ψᵖ m x)
  ZpΨ m Tree.zero z = z
  ZpΨ m (Tree.suc x) z = zpL 1 (ZpΨ m x z)
  ZpΨ m (Tree.lim f) z = zpL 0 (ZpΨ m (f 0) z)
  ZpΨ {k} m (limᵢ r f) z with verdict S m r
  ... | pen _ _ = zpI
  ... | rise    = zpL 0 (ZpΨ m (f (intoL k r (Ω (at k r)))) z)
  ZpΨ {suc k}    m (up d x) z = ZpΨ (upM (suc k) d m) x z
  ZpΨ {lim f}    m (up d x) z = ZpΨ (upM (lim f) d m) x z
  ZpΨ {limᴼ k g} m (up d x) z = ZpΨ (upM (limᴼ k g) d m) x z

  -- 目标有可容许的 0 路径: 第 0 层的节点必穿透
  Zt : Lv → Set
  Zt i = (Σ (Pre i) λ r → AdmB i r × at i r ≡ zero) × Zp i (Ω i)

  ChOK : (k : Lv) → Pre k → Set
  ChOK k r = (at k r ≡ zero) ⊎ (OK k (chM k r) × Zt (at k r))

  rise≠0 : ∀ {i j} → (∀ (r : Pre i) → AdmB i r → at i r ≈ᴮ j → ⊥) → Zt i → j ≡ zero → ⊥
  rise≠0 k ((r , d , e) , _) refl = k r d (subst (_≈ᴮ zero) (sym e) z≈)

  Bs-nz : ∀ j → (j ≡ zero → ⊥) → (z : Ordᴸ j) → Bs j z
  Bs-nz zero       n z = ⊥-elim (n refl)
  Bs-nz (suc _)    n z = tt
  Bs-nz (lim _)    n z = tt
  Bs-nz (limᴼ _ _) n z = tt

  Bs-subst : ∀ {a b} (e : a ≡ b) {z : Ordᴸ a} → Bs a z → Bs b (subst Ordᴸ e z)
  Bs-subst refl d = d

  -- `at` 的路径与 `≈ᴮ`
  ≈≡ : ∀ {a a′ b b′} → a ≡ a′ → b ≡ b′ → a′ ≈ᴮ b′ → a ≈ᴮ b
  ≈≡ refl refl e = e

  clash : ∀ {i i′ j j′} → i ≈ᴮ i′ → j ≈ᴮ j′ → (r : Pre i) → at i r ≡ j → AdmB i r →
          (∀ (r′ : Pre i′) → AdmB i′ r′ → at i′ r′ ≈ᴮ j′ → ⊥) → ⊥
  clash ii jj r e d k with path≈ ii r d
  ... | r′ , d′ , e′ = k r′ d′ (≈ᴮ-trans (≈ᴮ-sym e′) (≈≡ e refl jj))

  LvT : Lv → Set
  LvT zero       = ⊤
  LvT (suc k)    = (∀ r → AdmB (suc k) r → ChOK (suc k) r) × LvT k
  LvT (lim f)    = (∀ r → AdmB (lim f) r → ChOK (lim f) r) × (∀ n → LvT (f n))
  LvT (limᴼ k g) = (∀ r → AdmB (limᴼ k g) r → ChOK (limᴼ k g) r) × LvT k × (∀ x → Bs k x → LvT (g x))

  lvCh : ∀ i → LvT i → ∀ r → AdmB i r → ChOK i r
  lvCh (suc k)    w = proj₁ w
  lvCh (lim f)    w = proj₁ w
  lvCh (limᴼ k g) w = proj₁ w

  lvt-at : ∀ i → LvT i → ∀ r → AdmB i r → LvT (at i r)
  lvt-at (suc k)    w (inj₁ _) _ = proj₂ w
  lvt-at (suc k)    w (inj₂ r) d = lvt-at k (proj₂ w) r d
  lvt-at (lim f)    w (n , r)  d = lvt-at (f n) (proj₂ w n) r d
  lvt-at (limᴼ k g) w (inj₁ (inj₁ _)) _ = proj₁ (proj₂ w)
  lvt-at (limᴼ k g) w (inj₁ (inj₂ r)) d = lvt-at k (proj₁ (proj₂ w)) r d
  lvt-at (limᴼ k g) w (inj₂ (x , r)) (a , d) = lvt-at (g x) (proj₂ (proj₂ w) x a) r d

  -- 输入层: 只要 `Ω` 的节点的链合法. `LvT` 要全部路径, 只有作目标的层才需要
  LvG : Lv → Set
  LvG zero       = ⊤
  LvG (suc k)    = ChOK (suc k) (inj₁ tt) × LvT k
  LvG (lim f)    = ∀ n → LvG (f n)
  LvG (limᴼ k g) = ChOK (limᴼ k g) (inj₁ (inj₁ tt)) × LvT k × (∀ x → Bs k x → LvG (g x))

  t→g : ∀ i → LvT i → LvG i
  t→g zero       w = tt
  t→g (suc k)    w = proj₁ w (inj₁ tt) tt , proj₂ w
  t→g (lim f)    w = λ n → t→g (f n) (proj₂ w n)
  t→g (limᴼ k g) w = proj₁ w (inj₁ (inj₁ tt)) tt , proj₁ (proj₂ w) , (λ x b → t→g (g x) (proj₂ (proj₂ w) x b))

  -- 节点的合法性
  ND : (k : Lv) → Pre k → Set
  ND k r = AdmB k r × ChOK k r × LvT (at k r)

  nd-of : ∀ i → LvT i → ∀ r → AdmB i r → ND i r
  nd-of i w r d = d , lvCh i w r d , lvt-at i w r d

  out-into : ∀ k r y → outL k r (intoL k r y) ≡ y
  out-into (suc k)    (inj₁ _) y = refl
  out-into (suc k)    (inj₂ r) y = out-into k r y
  out-into (lim f)    (n , r)  y = out-into (f n) r y
  out-into (limᴼ k g) (inj₁ (inj₁ _)) y = refl
  out-into (limᴼ k g) (inj₁ (inj₂ r)) y = out-into k r y
  out-into (limᴼ k g) (inj₂ (x , r))  y = out-into (g x) r y
```

## §2 相似

跨层的相似, 正性的处理与 [Level](Level.lagda.md) 的 `Eq₊`/`R` 相同: 节点的分支条件 `RL` 对层号递归. `LR` 是节点层的 "尊重": `limᴼ k g` 的 `g` 把相似的输入送到 `≈ᴮ` 的层, 这是 `Ω` 相似所要的全部. 只记左侧: `g z ≈ g z′ ≈ g′ z′`.

```agda
  Resp : (k : Lv) → (Ordᴸ k → Lv) → (Eqk : Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set) → Set
  Resp k g Eqk = ∀ z z′ → Bs k z → Bs k z′ → Eqk z {k} z′ → g z ≈ᴮ g z′

  data Eq₊ (k : Lv)
           (RL : (r : Pre k) → Ordᴸ (at k r) → ∀ {k′} → Ordᴸ k′ → Set)
           (RD : (d : Dn k) → Ordᴸ (down k d) → ∀ {k′} → Ordᴸ k′ → Set)
           (LR : Pre k → Set) : Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set where
    z≃ : ∀ {k′} → Eq₊ k RL RD LR Tree.zero {k′} Tree.zero
    s≃ : ∀ {k′} {a} {b : Ordᴸ k′} → Eq₊ k RL RD LR a b → Eq₊ k RL RD LR (Tree.suc a) (Tree.suc b)
    l≃ : ∀ {k′} {f} {g : ℕ → Ordᴸ k′} → (∀ n → Eq₊ k RL RD LR (f n) (g n)) → Eq₊ k RL RD LR (Tree.lim f) (Tree.lim g)
    i≃ : ∀ {k′} {r} {r′ : Pre k′} {f} {f′} → ND k r → ND k′ r′ → at k r ≈ᴮ at k′ r′ → LR r →
         (∀ z z′ → Bs _ z → Bs _ z′ → RL r z z′ → Eq₊ k RL RD LR (f (intoL k r z)) (f′ (intoL k′ r′ z′))) →
         Eq₊ k RL RD LR (limᵢ r f) (limᵢ r′ f′)
    uˡ : ∀ {k′} {d} {x} {b : Ordᴸ k′} → DB k d → RD d (outD k d x) b → Eq₊ k RL RD LR (up d x) b
    uʳ : ∀ {k′} {a} {d} {y} → DB k′ d → Eq₊ k RL RD LR a (outD k′ d y) → Eq₊ k RL RD LR a {k′} (up d y)

  Eq  : (k : Lv) → Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set
  RLo : (k : Lv) (r : Pre k) → Ordᴸ (at k r) → ∀ {k′} → Ordᴸ k′ → Set
  RDn : (k : Lv) (d : Dn k) → Ordᴸ (down k d) → ∀ {k′} → Ordᴸ k′ → Set
  LRo : (k : Lv) → Pre k → Set
  LvR : Lv → Set

  Eq k x y = Eq₊ k (RLo k) (RDn k) (LRo k) x y

  RLo (suc k)    (inj₁ _)        z b = Eq k z b
  RLo (suc k)    (inj₂ r)        z b = RLo k r z b
  RLo (lim f)    (n , r)         z b = RLo (f n) r z b
  RLo (limᴼ k g) (inj₁ (inj₁ _)) z b = Eq k z b
  RLo (limᴼ k g) (inj₁ (inj₂ r)) z b = RLo k r z b
  RLo (limᴼ k g) (inj₂ (x , r))  z b = RLo (g x) r z b

  RDn (suc k)    _ z b = Eq k z b
  RDn (lim f)    n z b = Eq (f n) z b
  RDn (limᴼ k g) x z b = Eq (g x) z b

  LRo (suc k)    (inj₁ _)        = LvR k
  LRo (suc k)    (inj₂ r)        = LRo k r
  LRo (lim f)    (n , r)         = LRo (f n) r
  LRo (limᴼ k g) (inj₁ (inj₁ _)) = LvR k
  LRo (limᴼ k g) (inj₁ (inj₂ r)) = LRo k r
  LRo (limᴼ k g) (inj₂ (x , r))  = LRo (g x) r

  LvR zero       = ⊤
  LvR (suc k)    = LvR k
  LvR (lim f)    = ∀ n → LvR (f n)
  LvR (limᴼ k g) = LvR k × (∀ x → Bs k x → LvR (g x)) × Resp k g (λ z {k′} b → Eq k z {k′} b)

  R→Eq : ∀ k r {z : Ordᴸ (at k r)} {k′} {b : Ordᴸ k′} → RLo k r z b → Eq (at k r) z b
  R→Eq (suc k)    (inj₁ _)        d = d
  R→Eq (suc k)    (inj₂ r)        d = R→Eq k r d
  R→Eq (lim f)    (n , r)         d = R→Eq (f n) r d
  R→Eq (limᴼ k g) (inj₁ (inj₁ _)) d = d
  R→Eq (limᴼ k g) (inj₁ (inj₂ r)) d = R→Eq k r d
  R→Eq (limᴼ k g) (inj₂ (x , r))  d = R→Eq (g x) r d

  Eq→R : ∀ k r {z : Ordᴸ (at k r)} {k′} {b : Ordᴸ k′} → Eq (at k r) z b → RLo k r z b
  Eq→R (suc k)    (inj₁ _)        d = d
  Eq→R (suc k)    (inj₂ r)        d = Eq→R k r d
  Eq→R (lim f)    (n , r)         d = Eq→R (f n) r d
  Eq→R (limᴼ k g) (inj₁ (inj₁ _)) d = d
  Eq→R (limᴼ k g) (inj₁ (inj₂ r)) d = Eq→R k r d
  Eq→R (limᴼ k g) (inj₂ (x , r))  d = Eq→R (g x) r d

  lvr-at : ∀ i → LvR i → ∀ r → AdmB i r → LRo i r
  lvr-at (suc k)    w (inj₁ _) _ = w
  lvr-at (suc k)    w (inj₂ r) d = lvr-at k w r d
  lvr-at (lim f)    w (n , r)  d = lvr-at (f n) (w n) r d
  lvr-at (limᴼ k g) w (inj₁ (inj₁ _)) _ = proj₁ w
  lvr-at (limᴼ k g) w (inj₁ (inj₂ r)) d = lvr-at k (proj₁ w) r d
  lvr-at (limᴼ k g) w (inj₂ (x , r)) (a , d) = lvr-at (g x) (proj₁ (proj₂ w) x a) r d

  L→R : ∀ i r → AdmB i r → LRo i r → LvR (at i r)
  L→R (suc k)    (inj₁ _) _ w = w
  L→R (suc k)    (inj₂ r) d w = L→R k r d w
  L→R (lim f)    (n , r)  d w = L→R (f n) r d w
  L→R (limᴼ k g) (inj₁ (inj₁ _)) _ w = w
  L→R (limᴼ k g) (inj₁ (inj₂ r)) d w = L→R k r d w
  L→R (limᴼ k g) (inj₂ (x , r)) (a , d) w = L→R (g x) r d w
```

## §3 `Ω` 的相似

`uL`, `uR` 是对 `k` 分情况后的 `uˡ`, `uʳ`, 只是把 `RDn` 展开. `i≃∘` 处理 `limᵢ r (g ∘ out)` 这个所有输出节点的共同形状, `out-into` 只在这里出现.

```agda
  uL : ∀ k {d} {x : DnT k d} {k′} {b : Ordᴸ k′} → DB k d → Eq (down k d) (outD k d x) b → Eq k (up d x) b
  uL (suc k)    db e = uˡ db e
  uL (lim f)    db e = uˡ db e
  uL (limᴼ k g) db e = uˡ db e

  i≃∘ : ∀ {k k′} {r : Pre k} {r′ : Pre k′} {g : Ordᴸ (at k r) → Ordᴸ k} {g′ : Ordᴸ (at k′ r′) → Ordᴸ k′} →
        ND k r → ND k′ r′ → at k r ≈ᴮ at k′ r′ → LRo k r →
        (∀ z z′ → Bs _ z → Bs _ z′ → Eq (at k r) z z′ → Eq k (g z) (g′ z′)) →
        Eq k (limᵢ r (λ y → g (outL k r y))) (limᵢ r′ (λ y → g′ (outL k′ r′ y)))
  i≃∘ {k} {k′} {r} {r′} {g} {g′} nd nd′ e lr h = i≃ nd nd′ e lr λ z z′ bz bz′ d →
    subst₂ (λ u v → Eq k (g u) (g′ v)) (sym (out-into k r z)) (sym (out-into k′ r′ z′))
           (h z z′ bz bz′ (R→Eq k r d))

  Ω≃ : ∀ {a b} → a ≈ᴮ b → LvG a → LvG b → LvR a → Eq a (Ω a) (Ω b)
  Ω≃ z≈ _ _ _ = s≃ z≃
  Ω≃ {suc a} {suc b} (s≈ e) ga gb ra =
    i≃ (tt , proj₁ ga , proj₂ ga) (tt , proj₁ gb , proj₂ gb) e ra
       (λ z z′ _ _ d → uˡ tt (uʳ tt d))
  Ω≃ (l≈ h) ga gb ra = l≃ (λ n → uˡ tt (uʳ tt (Ω≃ (h n) (ga n) (gb n) (ra n))))
  Ω≃ {limᴼ k g} {limᴼ .k g′} (o≈ h) ga gb ra =
    i≃ (tt , proj₁ ga , proj₁ (proj₂ ga)) (tt , proj₁ gb , proj₁ (proj₂ gb)) (≈ᴮ-refl k) (proj₁ ra)
       (λ z z′ bz bz′ d → uˡ bz (uʳ bz′
          (Ω≃ (≈ᴮ-trans (proj₂ (proj₂ ra) z z′ bz bz′ d) (h z′ bz′))
              (proj₂ (proj₂ ga) z bz) (proj₂ (proj₂ gb) z′ bz′) (proj₁ (proj₂ ra) z bz))))
```

## §4 加法与折叠的相似

`SD σ`: `Sim` 把可容许路径送到可容许路径. `ψ≃` 的目标层只要 $\approx$-相关: 两条链分别在 `at k r` 与 `at k′ r′` 上, 这是 [Level](Level.lagda.md) 的 `ψ-≅` 同样被迫的推广. 混合的判决由 `clash` 排除. 所有条件都在节点上: `ND` (可容许, 链的模式 `OK`, 节点层 `LvT`) 与 `LRo`.

```agda
  SD : ∀ {k l} → Sim k l → Set
  SD {k} {l} σ = ∀ r → AdmB k r → AdmB l (proj₁ (σ r))

  sd-id : ∀ {k} → SD (σ-id k)
  sd-id r d = d

  sd∘ι : ∀ {l} k d (σ : Sim (k) l) → SD σ → DB k d → SD (σ ∘σ ι k d)
  sd∘ι (suc k) d σ s db r dr with σ (inj₂ r) | s (inj₂ r) dr
  ... | r″ , e′ | d″ = d″
  sd∘ι (lim f) n σ s db r dr with σ (n , r) | s (n , r) dr
  ... | r″ , e′ | d″ = d″
  sd∘ι (limᴼ k g) x σ s db r dr with σ (inj₂ (x , r)) | s (inj₂ (x , r)) (db , dr)
  ... | r″ , e′ | d″ = d″

  Eq-sub : ∀ {a a′ b b′} (e : a ≡ b) (e′ : a′ ≡ b′) {z : Ordᴸ a} {z′ : Ordᴸ a′} → Eq a z z′ → Eq b (subst Ordᴸ e z) (subst Ordᴸ e′ z′)
  Eq-sub refl refl d = d

  add≃ : ∀ {k k′ l l′} {a : Ordᴸ l} {a′ : Ordᴸ l′} {σ : Sim k l} {σ′ : Sim k′ l′} {x : Ordᴸ k} {y : Ordᴸ k′} →
         LvT l → LvT l′ → LvR l → SD σ → SD σ′ → Eq l a a′ → Eq k x y → Eq l (add a σ x) (add a′ σ′ y)
  add≃ gl gl′ rl s s′ ea z≃ = ea
  add≃ gl gl′ rl s s′ ea (s≃ e) = s≃ (add≃ gl gl′ rl s s′ ea e)
  add≃ gl gl′ rl s s′ ea (l≃ h) = l≃ (λ n → add≃ gl gl′ rl s s′ ea (h n))
  add≃ {k} {k′} {l} {l′} {a} {a′} {σ} {σ′} gl gl′ rl s s′ ea (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h) =
    i≃∘ {g = λ z → add a σ (f (intoL k r (subst Ordᴸ (proj₂ (σ r)) z)))}
        {g′ = λ z → add a′ σ′ (f′ (intoL k′ r′ (subst Ordᴸ (proj₂ (σ′ r′)) z)))}
      (nd-of l gl _ (s r (proj₁ nd))) (nd-of l′ gl′ _ (s′ r′ (proj₁ nd′)))
      (≈≡ (proj₂ (σ r)) (proj₂ (σ′ r′)) e) (lvr-at l rl _ (s r (proj₁ nd)))
      (λ z z′ bz bz′ d → add≃ gl gl′ rl s s′ ea
         (h _ _ (Bs-subst (proj₂ (σ r)) bz) (Bs-subst (proj₂ (σ′ r′)) bz′) (Eq→R k r (Eq-sub (proj₂ (σ r)) (proj₂ (σ′ r′)) d))))
  add≃ {suc k} {σ = σ} gl gl′ rl s s′ ea (uˡ {d = d} db e) = add≃ gl gl′ rl (sd∘ι (suc k) d σ s db) s′ ea e
  add≃ {lim f} {σ = σ} gl gl′ rl s s′ ea (uˡ {d = d} db e) = add≃ gl gl′ rl (sd∘ι (lim f) d σ s db) s′ ea e
  add≃ {limᴼ k g} {σ = σ} gl gl′ rl s s′ ea (uˡ {d = d} db e) = add≃ gl gl′ rl (sd∘ι (limᴼ k g) d σ s db) s′ ea e
  add≃ {k′ = suc k} {σ′ = σ} gl gl′ rl s s′ ea (uʳ {d = d} db e) = add≃ gl gl′ rl s (sd∘ι (suc k) d σ s′ db) ea e
  add≃ {k′ = lim f} {σ′ = σ} gl gl′ rl s s′ ea (uʳ {d = d} db e) = add≃ gl gl′ rl s (sd∘ι (lim f) d σ s′ db) ea e
  add≃ {k′ = limᴼ k g} {σ′ = σ} gl gl′ rl s s′ ea (uʳ {d = d} db e) = add≃ gl gl′ rl s (sd∘ι (limᴼ k g) d σ s′ db) ea e

  iter≃ : ∀ {i i′} {c : Ordᴸ i} {c′ : Ordᴸ i′} → LvT i → LvT i′ → LvR i → Eq i c c′ →
          ∀ n → Eq i (iter (c +_) Tree.zero n) (iter (c′ +_) Tree.zero n)
  iter≃ gi gi′ ri ec zero    = z≃
  iter≃ {i} {i′} gi gi′ ri ec (suc n) = add≃ gi gi′ ri (sd-id {i}) (sd-id {i′}) ec (iter≃ gi gi′ ri ec n)

  record Tg (i i′ : Lv) : Set where
    constructor tg
    field
      te : i ≈ᴮ i′
      gL : LvT i
      gR : LvT i′
      zL : Zt i
      zR : Zt i′
      rL : LvR i
  open Tg public

  chain : ∀ k r (f : Low k r → Ordᴸ k) → ℕ → Ordᴸ (at k r)
  chain k r f = iter (λ x → ψᵖ (chM k r) (f (intoL k r x))) (Ω (at k r))

  chOK : ∀ k r → ChOK k r → (at k r ≡ zero → ⊥) → OK k (chM k r) × Zt (at k r)
  chOK k r (inj₁ z) n = ⊥-elim (n z)
  chOK k r (inj₂ p) n = p

  ψ≃ : ∀ {k k′ i i′} (m : Mode k i) (m′ : Mode k′ i′) {x : Ordᴸ k} {y : Ordᴸ k′} → OK k m → OK k′ m′ → Tg i i′ →
       Eq k x y → Eq i (ψᵖ m x) (ψᵖ m′ y)
  chain≃ : ∀ {k k′} {r : Pre k} {r′ : Pre k′} {f : Low k r → Ordᴸ k} {f′ : Low k′ r′ → Ordᴸ k′} →
           ND k r → ND k′ r′ → at k r ≈ᴮ at k′ r′ → LRo k r → (at k r ≡ zero → ⊥) → (at k′ r′ ≡ zero → ⊥) →
           (∀ z z′ → Bs _ z → Bs _ z′ → RLo k r z z′ → Eq k (f (intoL k r z)) (f′ (intoL k′ r′ z′))) →
           ∀ n → Eq (at k r) (chain k r f n) (chain k′ r′ f′ n)

  ψ≃ m m′ ok ok′ t z≃ = Ω≃ (te t) (t→g _ (gL t)) (t→g _ (gR t)) (rL t)
  ψ≃ m m′ ok ok′ t (s≃ e) = l≃ (iter≃ (gL t) (gR t) (rL t) (ψ≃ m m′ ok ok′ t e))
  ψ≃ m m′ ok ok′ t (l≃ h) = l≃ (λ n → ψ≃ m m′ ok ok′ t (h n))
  ψ≃ {k} {k′} {i} {i′} m m′ ok ok′ t (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h)
    with verdict S m r | okV k m ok r (proj₁ nd) | verdict S m′ r′ | okV k′ m′ ok′ r′ (proj₁ nd′)
  ... | _ | cvp r₁ e₁ a₁ | _ | cvp r₂ e₂ a₂ =
    i≃∘ {g = λ z → ψᵖ m (f (intoL k r (subst Ordᴸ e₁ z)))} {g′ = λ z → ψᵖ m′ (f′ (intoL k′ r′ (subst Ordᴸ e₂ z)))}
      (nd-of i (gL t) r₁ a₁) (nd-of i′ (gR t) r₂ a₂) (≈≡ e₁ e₂ e) (lvr-at i (rL t) r₁ a₁)
      (λ z z′ bz bz′ d → ψ≃ m m′ ok ok′ t (h _ _ (Bs-subst e₁ bz) (Bs-subst e₂ bz′) (Eq→R k r (Eq-sub e₁ e₂ d))))
  ... | _ | cvp r₁ e₁ a₁ | _ | cvr kk = ⊥-elim (clash (te t) e r₁ e₁ a₁ kk)
  ... | _ | cvr kk | _ | cvp r₂ e₂ a₂ = ⊥-elim (clash (≈ᴮ-sym (te t)) (≈ᴮ-sym e) r₂ e₂ a₂ kk)
  ... | _ | cvr kk | _ | cvr kk′ =
    l≃ (λ n → ψ≃ m m′ ok ok′ t (h _ _ (Bs-nz _ n₀ _) (Bs-nz _ n₀′ _)
         (Eq→R k r (chain≃ {f = f} {f′ = f′} nd nd′ e lr n₀ n₀′ h n))))
    where
    n₀ = rise≠0 kk (zL t)
    n₀′ = rise≠0 kk′ (zR t)
  ψ≃ {suc k} m m′ ok ok′ t (uˡ {d = d} db e) = ψ≃ (upM (suc k) d m) m′ (okU (suc k) m ok d db) ok′ t e
  ψ≃ {lim f} m m′ ok ok′ t (uˡ {d = d} db e) = ψ≃ (upM (lim f) d m) m′ (okU (lim f) m ok d db) ok′ t e
  ψ≃ {limᴼ k g} m m′ ok ok′ t (uˡ {d = d} db e) = ψ≃ (upM (limᴼ k g) d m) m′ (okU (limᴼ k g) m ok d db) ok′ t e
  ψ≃ {k′ = suc k} m m′ ok ok′ t (uʳ {d = d} db e) = ψ≃ m (upM (suc k) d m′) ok (okU (suc k) m′ ok′ d db) t e
  ψ≃ {k′ = lim f} m m′ ok ok′ t (uʳ {d = d} db e) = ψ≃ m (upM (lim f) d m′) ok (okU (lim f) m′ ok′ d db) t e
  ψ≃ {k′ = limᴼ k g} m m′ ok ok′ t (uʳ {d = d} db e) = ψ≃ m (upM (limᴼ k g) d m′) ok (okU (limᴼ k g) m′ ok′ d db) t e

  chain≃ {k} {k′} {r} {r′} nd nd′ e lr n₀ n₀′ h zero =
    Ω≃ e (t→g _ (proj₂ (proj₂ nd))) (t→g _ (proj₂ (proj₂ nd′))) (L→R k r (proj₁ nd) lr)
  chain≃ {k} {k′} {r} {r′} {f} {f′} nd nd′ e lr n₀ n₀′ h (suc n) =
    let c  = chOK k r (proj₁ (proj₂ nd)) n₀
        c′ = chOK k′ r′ (proj₁ (proj₂ nd′)) n₀′
    in ψ≃ (chM k r) (chM k′ r′) (proj₁ c) (proj₁ c′)
          (tg e (proj₂ (proj₂ nd)) (proj₂ (proj₂ nd′)) (proj₂ c) (proj₂ c′) (L→R k r (proj₁ nd) lr))
          (h _ _ (Bs-nz _ n₀ _) (Bs-nz _ n₀′ _) (Eq→R k r (chain≃ {f = f} {f′ = f′} nd nd′ e lr n₀ n₀′ h n)))
```
