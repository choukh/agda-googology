# 证书与阶段无关: 对 $k$ 递归的地板塔 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). `Next`: 给阶段 `St`, 新层 `new` 与一个好层号 $L$, 新地板就是 "层号 $\approx$ $L$ 的某个可容许字面前驱的树". 这一步只用 `St` 的字段和 `<-decᴬ`, 没有对阶段分情况. `step` 把它接到 $K\mapsto K+1$; `tower` 是对 $K$ 的递归. $L$ 由一个**选择** `Choice` 给出, 所以世界可以取到 $\Omega_K+1+\psi_K(\Omega_\theta)$ (`W-ψ`), 不只最小的 $\Omega_K+1$ (`W-Ω`). 第 0 层的世界 `W-ω` 是 $\omega$; 任何 $\ell\ge\omega$ 见 [LevelKWorld](LevelKWorld.lagda.md).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKTower where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; m≤n⇒m<n∨m≡n; <-irrefl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; Tree; limᵢ; up; Ω; toLv; σ-id; add; intoL)
open import OCF.Align.InaccFloorTree using (Sib; natL; fin; module PF)
open import OCF.Align.LevelKBase using (NoO; Fl; module Leaf; Stage; Ext; module Move)
open import OCF.Align.LevelKFin using (IsK; module Fin; noo-nat; at-nat; natL-inj)
```

## §1 第 0 阶段: 没有地板

```agda
fl₀ : Fl
fl₀ = record
  { Lw = λ _ → ⊥ ; A = λ _ _ → ⊥ ; A→Lw = λ _ _ () ; low-noo = λ _ () ; low-at = λ _ () ; low-lim = λ _ _ () }

St₀ : Stage
St₀ = record
  { fl = fl₀ ; low-≈ = λ () ; low-wf = λ _ () ; ΩA = λ _ () ; pΩ = λ _ () ; cmpA = λ _ _ _ () ; cxA = λ _ _ () }

isK₀ : IsK 0 St₀
isK₀ = record { lw⇒ = λ _ () ; ⇐lw = λ _ () }
```

## §2 加一层地板

`NewLevel`: `new` 是新层, 不 $\approx$ 任何旧的低层, 它的前驱都低, 它是 $\Omega_{\mathtt{new}}$ 的字面前驱. `World`: 下一层地板的界 $L$, 层号好, $\Omega_{\mathtt{new}}$ 是它的字面前驱. 地板元的比较就是 $L$ 的 `<-decᴬ`: **公共上界是字面的**, 不要全局三歧, 也不问 `S`. 地板的成员资格是证据, 折叠不读它.

```agda
record NewLevel (St : Stage) (new : Lv) : Set where
  open Stage St
  open Leaf fl
  field
    nw-noo : NoO new
    nw-at  : ∀ r → Lw (at new r)
    nw-lim : ∀ f n → new ≡ lim f → Lw (f n)
    nw-new : Lw new → ⊥
    nw-≉   : ∀ {b} → Lw b → new ≈ᴮ b → ⊥
    nw-wf  : WFᴬ new
    nw-pΩ  : new ≺ᴬ toLv (Ω new)

record World (St : Stage) (new : Lv) : Set where
  open Stage St
  open Leaf fl
  field
    L   : Lv
    loL : Lo L
    cxL : Cx L
    hΩ  : toLv (Ω new) ≺ᴬ L

module Next (St : Stage) (new : Lv) (N : NewLevel St new) (W : World St new) where
  open Stage St
  open Leaf fl
  open NewLevel N
  open World W

  A′ : (j : Lv) → Ordᴸ j → Set
  A′ j x = A j x ⊎ (j ≡ new × Σ (Pre L) λ p → Adm L p × toLv x ≈ᴮ at L p)

  fl′ : Fl
  fl′ = record
    { Lw = λ j → Lw j ⊎ j ≡ new
    ; A = A′
    ; A→Lw = λ { k x (inj₁ a) → inj₁ (A→Lw k x a) ; k x (inj₂ (e , _)) → inj₂ e }
    ; low-noo = λ { j (inj₁ l) → low-noo j l ; _ (inj₂ refl) → nw-noo }
    ; low-at = λ { j (inj₁ l) r → inj₁ (low-at j l r) ; _ (inj₂ refl) r → inj₁ (nw-at r) }
    ; low-lim = λ { f n (inj₁ l) → inj₁ (low-lim f n l) ; f n (inj₂ e) → inj₁ (nw-lim f n (sym e)) }
    }

  ext : Ext fl fl′
  ext = record
    { low⊂ = inj₁
    ; A⊂ = inj₁
    ; A⊃ = λ { l (inj₁ a) → a ; l (inj₂ (refl , _)) → ⊥-elim (nw-new l) }
    }

  open Move fl fl′ ext public

  lo-new : Lo new
  lo-new = noo→lo new nw-noo

  bl-new : BL new
  bl-new = nw-noo , nw-at

  cmp′ : ∀ j x y → A′ j x → A′ j y → L′.Tri (toLv x) (toLv y)
  cmp′ j x y (inj₁ a) (inj₁ a′) = Tri↑ (cmpA j x y a a′)
  cmp′ j x y (inj₁ a) (inj₂ (refl , _)) = ⊥-elim (nw-new (A→Lw j x a))
  cmp′ j x y (inj₂ (refl , _)) (inj₁ a′) = ⊥-elim (nw-new (A→Lw j y a′))
  cmp′ j x y (inj₂ (_ , p , dp , e)) (inj₂ (_ , q , dq , e′)) =
    Tri↑ (shL e (shR e′ (<-decᴬ L (proj₁ cxL) p q dp dq)))

  cx′ : ∀ j x → A′ j x → L′.Cx (toLv x)
  cx′ j x (inj₁ a) = Cx↑ (toLv x) (lo-toLv (lw→bl (A→Lw j x a)) x) (cxA j x a)
  cx′ j x (inj₂ (refl , p , dp , e)) = Cx↑ (toLv x) (lo-toLv bl-new x) (cx≈ e (cx-at low-wf L loL cxL p dp))

  St′ : Stage
  St′ = record
    { fl = fl′
    ; low-≈ = λ { (inj₁ l) (inj₁ l′) e → low-≈ l l′ (≈↓ (lo-par l) e)
                ; (inj₁ l) (inj₂ refl) e → ⊥-elim (nw-≉ l (L.≈ᴮ-sym (≈↓ (lo-par l) e)))
                ; (inj₂ refl) (inj₁ l′) e → ⊥-elim (nw-≉ l′ (≈↓ lo-new e))
                ; (inj₂ refl) (inj₂ refl) e → refl }
    ; low-wf = λ { j (inj₁ l) → wf↑ j (lo-par l) (low-wf j l) ; _ (inj₂ refl) → wf↑ new lo-new nw-wf }
    ; ΩA = λ { j (inj₁ l) → inj₁ (ΩA j l) ; _ (inj₂ refl) → inj₂ (refl , hΩ′) }
    ; pΩ = λ { j (inj₁ l) → ≺↑ (pΩ j l) ; _ (inj₂ refl) → ≺↑ nw-pΩ }
    ; cmpA = cmp′
    ; cxA = cx′
    }
    where
    hΩ′ : Σ (Pre L) λ p → Adm L p × toLv (Ω new) ≈ᴮ at L p
    hΩ′ with hΩ
    ... | viaᴬ p d e = p , d , e
```

## §3 自然数的塔

`Big`: 每层地板都有含任意自然数的元. 这只是为了 $\Omega_K$ 含 $K$ (`nw-pΩ`). `One`: 每层地板都含 $1$. 这只是为了 $\Omega_K$ 是 $\psi_K(\Omega_\theta)$ 的字面前驱 (`W-F`). 第 0 层的世界要含全部自然数, 第 $\ge 1$ 层自动.

```agda
module NatStep (K : ℕ) (St : Stage) (isK : IsK K St) where
  open Stage St
  open Leaf fl
  open IsK isK

  Big : Set
  Big = ∀ m → m < K → ∀ n → Σ (Ordᴸ (natL m)) λ z → A (natL m) z × natL n ≺ᴬ toLv z

  One : Set
  One = ∀ m → m < K → A (natL m) (Tree.suc Tree.zero)

  nat≈ : ∀ n {b} → natL n ≈ᴮ b → natL n ≡ b
  nat≈ zero z≈ = refl
  nat≈ (suc n) (s≈ e) = cong Lv.suc (nat≈ n e)

  nat-wf : ∀ n → WFᴬ (natL n)
  nat-wf zero    = tt
  nat-wf (suc n) = nat-wf n

  lw-K : Lw (natL K) → ⊥
  lw-K l with lw⇒ _ l
  ... | m , p , e = <-irrefl (natL-inj m K (sym e)) p

  bigΩ : Big → ∀ k → k < K → ∀ n → natL n ≺ᴬ toLv (Ω (natL (suc k)))
  bigΩ b k p n with b k p n
  ... | z , az , viaᴬ q d e = viaᴬ (inj₂ (z , q)) (az , d) e

  module WithBig (bg : Big) where
    pΩ-K : natL K ≺ᴬ toLv (Ω (natL K))
    pΩ-K = go K ≤-refl where
      go : ∀ k → k ≤ K → natL k ≺ᴬ toLv (Ω (natL k))
      go zero    _ = viaᴬ (inj₁ tt) tt z≈
      go (suc k) p = bigΩ bg k p (suc k)

    new : NewLevel St (natL K)
    new = record
      { nw-noo = noo-nat K
      ; nw-at = λ r → let m , p , e = at-nat K r in subst Lw (sym e) (⇐lw m p)
      ; nw-lim = nw-lim′ K
      ; nw-new = lw-K
      ; nw-≉ = λ l e → lw-K (subst Lw (sym (nat≈ K e)) l)
      ; nw-wf = nat-wf K
      ; nw-pΩ = pΩ-K
      }
      where
      nw-lim′ : ∀ n f m → natL n ≡ lim f → Lw (f m)
      nw-lim′ zero f m ()
      nw-lim′ (suc n) f m ()

-- 世界: 第 0 层要含全部自然数
record WorldK (K : ℕ) (St : Stage) : Set where
  open Stage St
  open Leaf fl
  field
    w   : World St (natL K)
    b0  : K ≡ 0 → ∀ n → natL n ≺ᴬ World.L w

Tw : ℕ → Set₁
Tw K = Σ Stage λ St → Σ (IsK K St) λ isK → NatStep.Big K St isK × NatStep.One K St isK

nt : ℕ → Ordᴸ zero
nt zero    = Tree.zero
nt (suc n) = Tree.suc (nt n)

nt≡ : ∀ n → toLv (nt n) ≡ natL n
nt≡ zero    = refl
nt≡ (suc n) = cong Lv.suc (nt≡ n)

module Step (K : ℕ) (St : Stage) (isK : IsK K St) (bg : NatStep.Big K St isK) (on : NatStep.One K St isK) (WK : WorldK K St) where
  open NatStep K St isK
  open WithBig bg
  open WorldK WK
  open Next St (natL K) new w public

  isK′ : IsK (suc K) St′
  isK′ = record
    { lw⇒ = λ { j (inj₁ l) → let m , p , e = IsK.lw⇒ isK j l in m , ≤-trans p (<⇒≤ ≤-refl) , e
              ; _ (inj₂ refl) → K , ≤-refl , refl }
    ; ⇐lw = λ m p → go m p
    }
    where
    go : ∀ m → m < suc K → Fl.Lw fl′ (natL m)
    go m (s≤s p) with m≤n⇒m<n∨m≡n p
    ... | inj₁ q = inj₁ (IsK.⇐lw isK m q)
    ... | inj₂ refl = inj₂ refl

  bg′ : NatStep.Big (suc K) St′ isK′
  bg′ m (s≤s p) n with m≤n⇒m<n∨m≡n p
  ... | inj₁ q = let z , az , h = bg m q n in z , inj₁ az , ≺↑ h
  ... | inj₂ refl = top K refl n
    where
    top : ∀ K₀ → K₀ ≡ K → ∀ n → Σ (Ordᴸ (natL K)) λ z → A′ (natL K) z × natL n L′.≺ᴬ toLv z
    top zero    e n with sym e
    ... | refl with b0 refl (suc n)
    ...   | Leaf.viaᴬ q d h =
      nt (suc n) , inj₂ (refl , q , d , subst (λ u → u L.≈ᴮ at (World.L w) q) (sym (nt≡ (suc n))) h) ,
      L′.viaᴬ (inj₁ tt) tt (L′.≡→≈′ (sym (nt≡ n)))
    top (suc k) refl n =
      Ω (natL (suc k)) , Stage.ΩA St′ _ (inj₂ refl) , ≺↑ (bigΩ bg k ≤-refl n)

  on′ : NatStep.One (suc K) St′ isK′
  on′ m (s≤s p) with m≤n⇒m<n∨m≡n p
  ... | inj₁ q = inj₁ (on m q)
  ... | inj₂ refl = inj₂ (refl , top K refl)
    where
    top : ∀ K₀ → K₀ ≡ K → Σ (Pre (World.L w)) λ q → L.Adm (World.L w) q × Lv.suc Lv.zero L.≈ᴮ at (World.L w) q
    top zero e with sym e
    ... | refl with b0 refl 1
    ...   | Leaf.viaᴬ q d h = q , d , h
    top (suc k) refl with L.≺⊑ (bigΩ bg k ≤-refl 1) (L.≺→⊑ (World.hΩ w))
    ... | Leaf.viaᴬ q d h = q , d , h

  next : Tw (suc K)
  next = St′ , isK′ , bg′ , on′
```

## §4 世界的选择

`W-ω`: 第 0 层的世界是 $\omega$. `W-Ω`: 第 $K\ge1$ 层的最小世界 $\Omega_K+1$. `W-ψ`: 第 $K$ 层的世界 $\Omega_K+1+\psi_K(\Omega_\theta)+1$, 对任何好层号 $\theta$. 它的 `Cx` 由 `cx-tree` 给: 证书定理的输出就是下一层地板的来源.

```agda
module W-ω₀ where
  open Stage St₀
  open Leaf fl
  open NatStep 0 St₀ isK₀

  ω : Lv
  ω = lim natL

  W-ω : WorldK 0 St₀
  W-ω = record
    { w = record
        { L = ω
        ; loL = λ n → noo→lo (natL n) (noo-nat n)
        ; cxL = ((λ n r d → viaᴬ (inj₂ r) d (≈ᴮ-refl _)) , nat-wf) ,
                (λ n → noo→rp (natL n) (noo-nat n)) ,
                (λ n → noo→mn (natL n) (noo-nat n))
        ; hΩ = viaᴬ (2 , inj₁ tt) tt (≈ᴮ-refl _)
        }
    ; b0 = λ _ n → viaᴬ (suc n , inj₁ tt) tt (≈ᴮ-refl _)
    }
open W-ω₀ using (W-ω; ω) public

module Worlds (S : Sib) (k : ℕ) (St : Stage) (isK : IsK (suc k) St) where
  open Fin S St
  K : ℕ
  K = suc k
  open K-stage K isK

  ΩK : Ordᴸ (natL K)
  ΩK = Ω (natL K)

  ΩK-self : Eq (natL K) ΩK ΩK
  ΩK-self = Ω-self (natL K) (proj₁ (lvp-nat K)) (proj₁ (proj₂ (lvp-nat K)))

  W-Ω : WorldK K St
  W-Ω = record
    { w = record
        { L = suc (toLv ΩK)
        ; loL = lo-toLv bl-K ΩK
        ; cxL = cx-tree bl-K GΩ-K ΩK-self
        ; hΩ = viaᴬ (inj₁ tt) tt (≈ᴮ-refl _)
        }
    ; b0 = λ ()
    }

  module WF (one : ∀ m → m < K → A (natL m) (Tree.suc Tree.zero)) (θ : Lv) (p : LvP θ) where
    -- ψ_K(1) 含 Ω_K: 第 2 项 Ω_K + Ω_K 的 1 号分支是 Ω_K + 1
    Ω≺ψ₁ : toLv ΩK ≺ᴬ toLv (ψⁿ K (Ω zero))
    Ω≺ψ₁ = viaᴬ (2 , inj₂ (Tree.suc Tree.zero , inj₁ tt)) (one k ≤-refl , tt) (≈ᴮ-refl _)

    ψ₁⊑ψ : toLv (ψⁿ K (Ω zero)) ⊑ᴬ toLv (ψⁿ K (Ω θ))
    ψ₁⊑ψ = Ω0 θ (ψo (fin K refl) (fin K refl) tt (ok-K θ) Ti-K (idO {b = bl-K} {b′ = bl-K}))

    w₀ : Ordᴸ (natL K)
    w₀ = ψⁿ K (Ω θ)

    w₀-self : Eq (natL K) w₀ w₀
    w₀-self = Eq-ψᴷ (Ω-self θ (proj₁ p) (proj₁ (proj₂ p)))

    Ω≺w : toLv ΩK ≺ᴬ toLv w₀
    Ω≺w = ≺⊑ Ω≺ψ₁ ψ₁⊑ψ

    W-F : WorldK K St
    W-F = record
      { w = record
          { L = suc (toLv w₀)
          ; loL = lo-toLv bl-K w₀
          ; cxL = cx-tree bl-K (Good-F θ p) w₀-self
          ; hΩ = pth Ω≺w
          }
      ; b0 = λ ()
      }
      where
      pth : toLv ΩK ≺ᴬ toLv w₀ → toLv ΩK ≺ᴬ suc (toLv w₀)
      pth (viaᴬ q d e) = viaᴬ (inj₂ q) d e

    -- 世界里字面地有 ψ_K(Ω_θ): 下一层的节点可以取它作分支
    w₀∈ : Σ (Pre (suc (toLv w₀))) λ q → Adm (suc (toLv w₀)) q × toLv w₀ ≈ᴮ at (suc (toLv w₀)) q
    w₀∈ = inj₁ tt , tt , ≈ᴮ-refl _
```

## §5 塔

`tower`: 对 $K$ 递归. 每一步由 `Choice` 选世界. **递归的只是地板, 不是证书**: `K-stage.Cert` 对 $K$ 没有递归, 它对一切满足 `IsK` 的阶段成立.

```agda
Choice : Set₁
Choice = ∀ k (t : Tw (suc k)) → WorldK (suc k) (proj₁ t)

tower : WorldK 0 St₀ → Choice → ∀ K → Tw K
tower W₀ ch zero = St₀ , isK₀ , (λ _ ()) , (λ _ ())
tower W₀ ch (suc zero) = Step.next 0 St₀ isK₀ (λ _ ()) (λ _ ()) W₀
tower W₀ ch (suc (suc k)) =
  let t = tower W₀ ch (suc k)
  in Step.next (suc k) (proj₁ t) (proj₁ (proj₂ t)) (proj₁ (proj₂ (proj₂ t))) (proj₂ (proj₂ (proj₂ t))) (ch k t)

canon : Sib → Choice
canon S k t = Worlds.W-Ω S k (proj₁ t) (proj₁ (proj₂ t))

-- 每一层都取给定的层号 θ 的 ψ_K(Ω_θ) 作世界 (θ 由 `th` 选, 要是好层号)
chooseF : (S : Sib) → (∀ k (t : Tw (suc k)) → Σ Lv (Fin.LvP S (proj₁ t))) → Choice
chooseF S th k t =
  Worlds.WF.W-F S k (proj₁ t) (proj₁ (proj₂ t)) (proj₂ (proj₂ (proj₂ t))) (proj₁ (th k t)) (proj₂ (th k t))

module AtK (S : Sib) (W₀ : WorldK 0 St₀) (ch : Choice) (K : ℕ) where
  St : Stage
  St = proj₁ (tower W₀ ch K)

  isK : IsK K St
  isK = proj₁ (proj₂ (tower W₀ ch K))

  open Fin S St public
  open K-stage K isK public
  open IsK isK public using (⇐lw)

  ⇐lw′ : 1 < K → Lw (natL 1)
  ⇐lw′ = ⇐lw 1

-- 主定理: 对一切 K, 目标 K 的折叠在第 K 阶段有证书
Cert∀ : ∀ (S : Sib) W₀ (ch : Choice) K θ → AtK.LvP S W₀ ch K θ → AtK.WFᴬ S W₀ ch K (toLv (PF.ψⁿ S K (Ω θ)))
Cert∀ S W₀ ch K θ p = AtK.Cert S W₀ ch K θ p

-- 输入是自然数的层号: 无条件, 对任何 S
Cert∀ₙ : ∀ (S : Sib) W₀ (ch : Choice) K n → AtK.WFᴬ S W₀ ch K (toLv (PF.ψⁿ S K (Ω (natL n))))
Cert∀ₙ S W₀ ch K n = AtK.Cert S W₀ ch K (natL n) (AtK.lvp-nat S W₀ ch K n)

-- 目标 2: ψ₂(Ω_θ) 的证书, 第 1 层的地板是实在的
Cert₂ : ∀ (S : Sib) W₀ (ch : Choice) θ → AtK.LvP S W₀ ch 2 θ → AtK.WFᴬ S W₀ ch 2 (toLv (PF.ψⁿ S 2 (Ω θ)))
Cert₂ S W₀ ch = Cert∀ S W₀ ch 2

-- 第 1 层的地板非空, 且含 Ω₁
A₁∋Ω₁ : ∀ (S : Sib) W₀ (ch : Choice) → Fl.A (Stage.fl (AtK.St S W₀ ch 2)) (natL 1) (Ω (natL 1))
A₁∋Ω₁ S W₀ ch = AtK.ΩA S W₀ ch 2 (natL 1) (AtK.⇐lw′ S W₀ ch 2 (s≤s (s≤s z≤n)))
```
