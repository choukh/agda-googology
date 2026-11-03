# 证书与阶段无关: 判决的正确性与树的相似 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). 由 [InaccThetaEq](InaccThetaEq.lagda.md) 改写, 大部分证明逐字. 差别只有三处: (1) `Bs`, `Zt`, `ChOK` 对抽象的低层 `Low` 说话, 不再是 "第 0 层"; (2) `i≃` 的分支前提多一个析取支: 低层节点的两个输入, 只要它们的**层号** $\approx$, 分支就要相似 (`PE`); (3) `T→E`: 在可取层号的层上, 层号 $\approx$ 蕴含 `Eq`. 它**不**用 `Eq` 的传递性 (异层的 `Eq` 的传递性要跨 `at k r ≈ᴮ at k′ r′` 搬输入, 这里没有), 只用 `≈ᴮ` 的传递性加 `Rp`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelKEq where

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
open import OCF.Align.LevelKBase using (NoO; Fl; module Leaf; Stage)
```

## §1 判决的正确性

`verdict S m r` 的类型不要求它为真. 这里把 "真" 写出来. 穿透: 路径字面地落在节点层上. 上升: 目标里没有可容许的路径 $\approx$ 节点层. 所以两个 `≈ᴮ`-相关的层不可能一个穿透一个上升 (`clash`).

```agda
module Eqv (S : Sib) (St : Stage) where
  open Stage St public
  open Leaf fl public
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

  -- 目标有全部低层的字面路径: 低层的节点必穿透
  Zt : Lv → Set
  Zt i = ∀ j → Lw j → Σ (Pre i) λ r → Adm i r × at i r ≡ j

  ChOK : (k : Lv) → Pre k → Set
  ChOK k r = Lw (at k r) ⊎ (OK k (chM k r) × Zt (at k r))

  rise≠low : ∀ {i j} → (∀ (r : Pre i) → AdmB i r → at i r ≈ᴮ j → ⊥) → Zt i → Lw j → ⊥
  rise≠low {i} {j} k z l with z j l
  ... | r , d , refl = k r (Adm→B i r d) (≈ᴮ-refl _)

  Bs-nz : ∀ j → (Lw j → ⊥) → (z : Ordᴸ j) → Bs j z
  Bs-nz j n z l = ⊥-elim (n l)

  Bs-subst : ∀ {a b} (e : a ≡ b) {z : Ordᴸ a} → Bs a z → Bs b (subst Ordᴸ e z)
  Bs-subst refl d = d

  ≡→≈ : ∀ {a b} → a ≡ b → a ≈ᴮ b
  ≡→≈ {a} refl = ≈ᴮ-refl a

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

跨层的相似, 正性的处理与 [Level](Level.lagda.md) 的 `Eq₊`/`R` 相同: 节点的分支条件 `RL` 对层号递归. `LR` 是节点层的 "尊重": `limᴼ k g` 的 `g` 把相似的输入送到 `≈ᴮ` 的层, 这是 `Ω` 相似所要的全部. 只记左侧: `g z ≈ g z′ ≈ g′ z′`. 低层节点的输入相等可以只看层号: 这是**断开循环的地方**, 低层的相等不再回到 `Eq`.

```agda
  Resp : (k : Lv) → (Ordᴸ k → Lv) → (Eqk : Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set) → Set
  Resp k g Eqk = ∀ z z′ → Bs k z → Bs k z′ → (Eqk z {k} z′ ⊎ (Lw k × k ≡ k × toLv z ≈ᴮ toLv z′)) → g z ≈ᴮ g z′

  data Eq₊ (k : Lv)
           (RL : (r : Pre k) → Ordᴸ (at k r) → ∀ {k′} → Ordᴸ k′ → Set)
           (RD : (d : Dn k) → Ordᴸ (down k d) → ∀ {k′} → Ordᴸ k′ → Set)
           (LR : Pre k → Set) : Ordᴸ k → ∀ {k′} → Ordᴸ k′ → Set where
    z≃ : ∀ {k′} → Eq₊ k RL RD LR Tree.zero {k′} Tree.zero
    s≃ : ∀ {k′} {a} {b : Ordᴸ k′} → Eq₊ k RL RD LR a b → Eq₊ k RL RD LR (Tree.suc a) (Tree.suc b)
    l≃ : ∀ {k′} {f} {g : ℕ → Ordᴸ k′} → (∀ n → Eq₊ k RL RD LR (f n) (g n)) → Eq₊ k RL RD LR (Tree.lim f) (Tree.lim g)
    i≃ : ∀ {k′} {r} {r′ : Pre k′} {f} {f′} → ND k r → ND k′ r′ → at k r ≈ᴮ at k′ r′ → LR r →
         (∀ z z′ → Bs _ z → Bs _ z′ → (RL r z z′ ⊎ (Lw (at k r) × at k r ≡ at k′ r′ × toLv z ≈ᴮ toLv z′)) → Eq₊ k RL RD LR (f (intoL k r z)) (f′ (intoL k′ r′ z′))) →
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

## §2′ 层号决定相似

`PE`: 分支前提的通用形状. `b≃`: 可取层号的层上, 相似给层号 $\approx$. `T→E`: 反过来. 这两条就是 "地板上的相等只读层号" 的内容. 节点都在低层, 所以判决从不出现: `ChOK` 走左支. `b≃` 的 `i≃` 情形要 `low-≈`: 两侧节点的参数层字面相同, 否则 `o≈` 写不出来. 分支前提的层号支带字面的 `a ≡ a′`: 地板读层号只读字面同一层.

```agda
  PE : ∀ a → Ordᴸ a → ∀ {a′} → Ordᴸ a′ → Set
  PE a z {a′} z′ = Eq a z z′ ⊎ (Lw a × a ≡ a′ × toLv z ≈ᴮ toLv z′)

  P→PE : ∀ k r {z : Ordᴸ (at k r)} {j′} {b : Ordᴸ j′} → (RLo k r z b ⊎ (Lw (at k r) × at k r ≡ j′ × toLv z ≈ᴮ toLv b)) → PE (at k r) z b
  P→PE k r (inj₁ d) = inj₁ (R→Eq k r d)
  P→PE k r (inj₂ d) = inj₂ d

  PE→P : ∀ k r {z : Ordᴸ (at k r)} {j′} {b : Ordᴸ j′} → PE (at k r) z b → (RLo k r z b ⊎ (Lw (at k r) × at k r ≡ j′ × toLv z ≈ᴮ toLv b))
  PE→P k r (inj₁ d) = inj₁ (Eq→R k r d)
  PE→P k r (inj₂ d) = inj₂ d

  PE-sub : ∀ {a a′ b b′} (e : a ≡ b) (e′ : a′ ≡ b′) {z : Ordᴸ a} {z′ : Ordᴸ a′} → PE a z z′ → PE b (subst Ordᴸ e z) (subst Ordᴸ e′ z′)
  PE-sub refl refl d = d

  lvr-noo : ∀ j → NoO j → LvR j
  lvr-noo zero    _ = tt
  lvr-noo (suc j) n = lvr-noo j n
  lvr-noo (lim f) n = λ m → lvr-noo (f m) (n m)

  lro-noo : ∀ k → NoO k → ∀ r → LRo k r
  lro-noo (suc k) n (inj₁ _) = lvr-noo k n
  lro-noo (suc k) n (inj₂ r) = lro-noo k n r
  lro-noo (lim f) n (m , r)  = lro-noo (f m) (n m) r

  low→lvt : ∀ j → Lw j → LvT j
  low→lvt zero    l = tt
  low→lvt (suc k) l = (λ r _ → inj₁ (low-at (suc k) l r)) , low→lvt k (low-at (suc k) l (inj₁ tt))
  low→lvt (lim f) l = (λ r _ → inj₁ (low-at (lim f) l r)) , (λ n → low→lvt (f n) (low-lim f n l))
  low→lvt (limᴼ k g) l with low-noo _ l
  ... | ()

  nd-bl : ∀ {k} → BL k → ∀ r → ND k r
  nd-bl {k} b r = noo-adm k (proj₁ b) r , inj₁ (proj₂ b r) , low→lvt _ (proj₂ b r)

  tl-sub : ∀ {a b} (e : a ≡ b) (z : Ordᴸ a) → toLv z ≈ᴮ toLv (subst Ordᴸ e z)
  tl-sub refl z = ≈ᴮ-refl _

  b≃ : ∀ {k k′} {x : Ordᴸ k} {y : Ordᴸ k′} → BL k → BL k′ → Eq k x y → toLv x ≈ᴮ toLv y
  b≃ b b′ z≃ = z≈
  b≃ b b′ (s≃ e) = s≈ (b≃ b b′ e)
  b≃ b b′ (l≃ h) = l≈ (λ n → b≃ b b′ (h n))
  b≃ b b′ (i≃ {r = r} {r′ = r′} nd nd′ e lr h) =
    let eq = low-≈ (proj₂ b r) (proj₂ b′ r′) e
    in o≈′ eq (λ x bx → b≃ b b′ (h x _ bx (Bs-subst eq bx) (inj₂ (proj₂ b r , eq , tl-sub eq x))))
  b≃ {suc k} b b′ (uˡ db e) = b≃ {k} (bl-suc b) b′ e
  b≃ {lim f} b b′ (uˡ {d = n} db e) = b≃ {f n} (bl-lim n b) b′ e
  b≃ {limᴼ _ _} (() , _) b′ (uˡ db e)
  b≃ {k′ = suc k} b b′ (uʳ db e) = b≃ {k′ = k} b (bl-suc b′) e
  b≃ {k′ = lim f} b b′ (uʳ {d = n} db e) = b≃ {k′ = f n} b (bl-lim n b′) e
  b≃ {k′ = limᴼ _ _} b (() , _) (uʳ db e)

  br≈ : ∀ {j j′} (eq : j ≡ j′) {g : Ordᴸ j → Lv} {g′ : Ordᴸ j′ → Lv} →
        (∀ x → Bs j x → g x ≈ᴮ g′ (subst Ordᴸ eq x)) →
        (∀ z z′ → Bs j′ z → Bs j′ z′ → toLv z ≈ᴮ toLv z′ → g′ z ≈ᴮ g′ z′) →
        ∀ z z′ → Bs j z → Bs j′ z′ → toLv z ≈ᴮ toLv z′ → g z ≈ᴮ g′ z′
  br≈ refl h r z z′ bz bz′ e = ≈ᴮ-trans (h z bz) (r z z′ bz bz′ e)

  T→E : ∀ {a a′} → BL a → BL a′ → (x : Ordᴸ a) (y : Ordᴸ a′) → Rp (toLv y) → toLv x ≈ᴮ toLv y → Eq a x y
  T→E {suc k} b b′ (up d x) y r e = uˡ tt (T→E (bl-suc b) b′ x y r e)
  T→E {lim f} b b′ (up n x) y r e = uˡ tt (T→E (bl-lim n b) b′ x y r e)
  T→E {limᴼ _ _} (() , _) b′ (up d x) y r e
  T→E {a′ = suc k} b b′ x (up d y) r e = uʳ tt (T→E b (bl-suc b′) x y r e)
  T→E {a′ = lim f} b b′ x (up n y) r e = uʳ tt (T→E b (bl-lim n b′) x y r e)
  T→E {a′ = limᴼ _ _} b (() , _) x (up d y) r e
  T→E b b′ Tree.zero Tree.zero r e = z≃
  T→E b b′ (Tree.suc x) (Tree.suc y) r (s≈ e) = s≃ (T→E b b′ x y r e)
  T→E b b′ (Tree.lim h) (Tree.lim h′) r (l≈ e) = l≃ (λ n → T→E b b′ (h n) (h′ n) (r n) (e n))
  T→E {a} {a′} b b′ (limᵢ r f) (limᵢ r′ f′) (rb , rr) e =
    let eq = proj₁ (o≈-inv e)
        h  = proj₂ (o≈-inv e)
    in i≃ (nd-bl b r) (nd-bl b′ r′) (≡→≈ eq) (lro-noo a (proj₁ b) r)
       (λ z z′ bz bz′ d →
          T→E b b′ (f (intoL a r z)) (f′ (intoL a′ r′ z′)) (rb z′ bz′)
            (br≈ eq {g = λ y → toLv (f (intoL a r y))} {g′ = λ y → toLv (f′ (intoL a′ r′ y))} h rr z z′ bz bz′
               (tlOf d)))
    where
    tlOf : ∀ {z z′} → (RLo a r z z′ ⊎ (Lw (at a r) × at a r ≡ at a′ r′ × toLv z ≈ᴮ toLv z′)) → toLv z ≈ᴮ toLv z′
    tlOf (inj₁ d) = b≃ (lw→bl (proj₂ b r)) (lw→bl (proj₂ b′ r′)) (R→Eq a r d)
    tlOf (inj₂ d) = proj₂ (proj₂ d)
  T→E b b′ Tree.zero (Tree.suc y) r ()
  T→E b b′ Tree.zero (Tree.lim h) r ()
  T→E b b′ Tree.zero (limᵢ r′ f) r ()
  T→E b b′ (Tree.suc x) Tree.zero r ()
  T→E b b′ (Tree.suc x) (Tree.lim h) r ()
  T→E b b′ (Tree.suc x) (limᵢ r′ f) r ()
  T→E b b′ (Tree.lim h) Tree.zero r ()
  T→E b b′ (Tree.lim h) (Tree.suc y) r ()
  T→E b b′ (Tree.lim h) (limᵢ r′ f) r ()
  T→E b b′ (limᵢ r′ f) Tree.zero r ()
  T→E b b′ (limᵢ r′ f) (Tree.suc y) r ()
  T→E b b′ (limᵢ r′ f) (Tree.lim h) r ()

  -- 地板上的层号 ≈ 就是 `Eq`
  tl→Eq : ∀ {a b} (eq : a ≡ b) {z : Ordᴸ a} {z′ : Ordᴸ b} → Lw a → Bs b z′ → toLv z ≈ᴮ toLv z′ → Eq a z z′
  tl→Eq refl {z} {z′} l bz′ t = T→E (lw→bl l) (lw→bl l) z z′ (proj₁ (proj₂ (cxA _ z′ (bz′ l)))) t
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
        (∀ z z′ → Bs _ z → Bs _ z′ → PE (at k r) z z′ → Eq k (g z) (g′ z′)) →
        Eq k (limᵢ r (λ y → g (outL k r y))) (limᵢ r′ (λ y → g′ (outL k′ r′ y)))
  i≃∘ {k} {k′} {r} {r′} {g} {g′} nd nd′ e lr h = i≃ nd nd′ e lr λ z z′ bz bz′ d →
    subst₂ (λ u v → Eq k (g u) (g′ v)) (sym (out-into k r z)) (sym (out-into k′ r′ z′))
           (h z z′ bz bz′ (P→PE k r d))

  dOf : ∀ {a b} (e : a ≈ᴮ b) {z : Ordᴸ a} {z′ : Ordᴸ b} → PE a z z′ → Bs b z′ → Eq a z z′
  dOf e (inj₁ d) _ = d
  dOf e (inj₂ (l , eq , t)) bz′ = tl→Eq eq l bz′ t

  Ω≃ : ∀ {a b} → a ≈ᴮ b → LvG a → LvG b → LvR a → Eq a (Ω a) (Ω b)
  Ω≃ z≈ _ _ _ = s≃ z≃
  Ω≃ {suc a} {suc b} (s≈ e) ga gb ra =
    i≃ (tt , proj₁ ga , proj₂ ga) (tt , proj₁ gb , proj₂ gb) e ra
       (λ z z′ bz bz′ d → uˡ tt (uʳ tt (dOf e d bz′)))
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
         (h _ _ (Bs-subst (proj₂ (σ r)) bz) (Bs-subst (proj₂ (σ′ r′)) bz′) (PE→P k r (PE-sub (proj₂ (σ r)) (proj₂ (σ′ r′)) d))))
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

  chOK : ∀ k r → ChOK k r → (Lw (at k r) → ⊥) → OK k (chM k r) × Zt (at k r)
  chOK k r (inj₁ z) n = ⊥-elim (n z)
  chOK k r (inj₂ p) n = p

  ψ≃ : ∀ {k k′ i i′} (m : Mode k i) (m′ : Mode k′ i′) {x : Ordᴸ k} {y : Ordᴸ k′} → OK k m → OK k′ m′ → Tg i i′ →
       Eq k x y → Eq i (ψᵖ m x) (ψᵖ m′ y)
  chain≃ : ∀ {k k′} {r : Pre k} {r′ : Pre k′} {f : Low k r → Ordᴸ k} {f′ : Low k′ r′ → Ordᴸ k′} →
           ND k r → ND k′ r′ → at k r ≈ᴮ at k′ r′ → LRo k r → (Lw (at k r) → ⊥) → (Lw (at k′ r′) → ⊥) →
           (∀ z z′ → Bs _ z → Bs _ z′ → (RLo k r z z′ ⊎ (Lw (at k r) × at k r ≡ at k′ r′ × toLv z ≈ᴮ toLv z′)) → Eq k (f (intoL k r z)) (f′ (intoL k′ r′ z′))) →
           ∀ n → Eq (at k r) (chain k r f n) (chain k′ r′ f′ n)

  ψ≃ m m′ ok ok′ t z≃ = Ω≃ (te t) (t→g _ (gL t)) (t→g _ (gR t)) (rL t)
  ψ≃ m m′ ok ok′ t (s≃ e) = l≃ (iter≃ (gL t) (gR t) (rL t) (ψ≃ m m′ ok ok′ t e))
  ψ≃ m m′ ok ok′ t (l≃ h) = l≃ (λ n → ψ≃ m m′ ok ok′ t (h n))
  ψ≃ {k} {k′} {i} {i′} m m′ ok ok′ t (i≃ {r = r} {r′ = r′} {f = f} {f′ = f′} nd nd′ e lr h)
    with verdict S m r | okV k m ok r (proj₁ nd) | verdict S m′ r′ | okV k′ m′ ok′ r′ (proj₁ nd′)
  ... | _ | cvp r₁ e₁ a₁ | _ | cvp r₂ e₂ a₂ =
    i≃∘ {g = λ z → ψᵖ m (f (intoL k r (subst Ordᴸ e₁ z)))} {g′ = λ z → ψᵖ m′ (f′ (intoL k′ r′ (subst Ordᴸ e₂ z)))}
      (nd-of i (gL t) r₁ a₁) (nd-of i′ (gR t) r₂ a₂) (≈≡ e₁ e₂ e) (lvr-at i (rL t) r₁ a₁)
      (λ z z′ bz bz′ d → ψ≃ m m′ ok ok′ t (h _ _ (Bs-subst e₁ bz) (Bs-subst e₂ bz′) (PE→P k r (PE-sub e₁ e₂ d))))
  ... | _ | cvp r₁ e₁ a₁ | _ | cvr kk = ⊥-elim (clash (te t) e r₁ e₁ a₁ kk)
  ... | _ | cvr kk | _ | cvp r₂ e₂ a₂ = ⊥-elim (clash (≈ᴮ-sym (te t)) (≈ᴮ-sym e) r₂ e₂ a₂ kk)
  ... | _ | cvr kk | _ | cvr kk′ =
    l≃ (λ n → ψ≃ m m′ ok ok′ t (h _ _ (Bs-nz _ n₀ _) (Bs-nz _ n₀′ _)
         (inj₁ (Eq→R k r (chain≃ {f = f} {f′ = f′} nd nd′ e lr n₀ n₀′ h n)))))
    where
    n₀ = rise≠low kk (zL t)
    n₀′ = rise≠low kk′ (zR t)
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
          (h _ _ (Bs-nz _ n₀ _) (Bs-nz _ n₀′ _) (inj₁ (Eq→R k r (chain≃ {f = f} {f′ = f′} nd nd′ e lr n₀ n₀′ h n))))
```
