# 证书与阶段无关: 与 `no-Ω₂` 共存, 壁垒对照 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). **共存.** [InaccThetaNeg](InaccThetaNeg.lagda.md) 的 `no-Ω₂` 说: 在 "`Bs 1 = ⊤`" 下, `LvG (toLv Ω₂)` 推出 WLPO. 这里的 `no-Ω₂′` 把那个隐含前提写出来: 第 1 层的 `Bs` 含每个 `up tt (em a)`, 这时结论不变. 而 `lvg-Ω` 说: 地板是塔的地板时, 对**任何** `S`, `LvG (toLv Ω_m)` ($m\le K$) 是定理. 所以唯一改变的前提是 "第 1 层的分支全称" 变成 "第 1 层的分支在地板里". 两者合起来: `¬full`: 塔的第 1 层地板要是含全部 `up tt (em a)`, 就有 WLPO.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKNeg where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; m≤n⇒m<n∨m≡n)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; toLv; Verdict; pen; rise; Tree; up; Ω)
open import OCF.Align.InaccFloorTree using (Sib; natL; module PF)
open import OCF.Align.LevelKWorld using (Ordᴵ; _<ᴵ_; suc; lim; ωᴵ; natᴵ; em; E; flag; sel; ω₂; g; i; G; κ; tF; tT; flag-false; flag-true; at-natE)
open import OCF.Align.LevelKBase using (NoO; Fl; module Leaf; Stage; Ext; module Move)
open import OCF.Align.LevelKFin using (IsK; module Fin; noo-nat; at-nat)
open import OCF.Align.LevelKLvP using (module LvPs)
open import OCF.Align.LevelKTower
```

## §1 地板要是全称, `no-Ω₂` 回来

`WLPO` 与 [InaccSingularBase](InaccSingularBase.lagda.md) 的定义逐字相同. 这里不导入它: 它的导入链含 [Finite](Finite.lagda.md). 与旧定理并排的陈述在 [LevelKCoexist](LevelKCoexist.lagda.md).

这是 [InaccThetaNeg](InaccThetaNeg.lagda.md) §2 的逐字搬运: 反例族一样, 判决读出来的方式一样. 差别只在 `read` 多一支: 节点层若低, 它就是自然数, 而它的头是 `suc (lim _)`.

```agda
WLPO : Set
WLPO = ∀ (s : ℕ → Bool) → (∀ n → s n ≡ false) ⊎ ¬ (∀ n → s n ≡ false)

module NegK (S : Sib) (St : Stage) (K : ℕ) (isK : IsK K St) where
  open Fin S St
  open IsK isK

  J : Lv
  J = E (suc ωᴵ)

  I : (ℕ → Bool) → Lv
  I s = E (suc (i s))

  natL≢ : ∀ m {f : ℕ → Lv} → natL m ≡ Lv.suc (Lv.lim f) → ⊥
  natL≢ zero ()
  natL≢ (suc zero) ()
  natL≢ (suc (suc m)) ()

  read : ∀ s → LvT (κ s) → CV (S J (I s))
  read s w with proj₁ w (1 , inj₁ tt) tt
  ... | inj₁ l = ⊥-elim (let m , _ , e = lw⇒ _ l in natL≢ m (sym e))
  ... | inj₂ (ok , _) = proj₁ ok (0 , inj₁ tt) tt

  no-pen : ∀ s → (∀ n → s n ≡ false) → ∀ (r : Pre (I s)) → at (I s) r ≡ J → ⊥
  no-pen s h (inj₁ _) ()
  no-pen s h (inj₂ (n , r)) e = go (flag s n) (flag-false s h n) r e where
    go : ∀ b → b ≡ false → (r : Pre (E (sel b n))) → at (E (sel b n)) r ≡ J → ⊥
    go _ refl r e with at-natE n r
    ... | m , e′ = natL≢ m (trans (sym e′) e)

  yes-path : ∀ b n → b ≡ true → Σ (Pre (E (sel b n))) λ r → AdmB (E (sel b n)) r × at (E (sel b n)) r ≈ᴮ J
  yes-path _ n refl = inj₁ tt , tt , ≈ᴮ-refl J

  dec : ∀ s (v : Verdict J (I s)) → ((∀ n → s n ≡ false) → CV v) → (∀ n → s n ≡ true → CV v) →
        (∀ n → s n ≡ false) ⊎ ((∀ n → s n ≡ false) → ⊥)
  dec s (pen r b) c₁ c₂ = inj₂ λ h → absurd h (c₁ h) where
    absurd : (∀ n → s n ≡ false) → CV (pen r b) → ⊥
    absurd h (cvp _ e _) = no-pen s h r e
  dec s rise c₁ c₂ = inj₁ λ n → go n (s n) refl where
    go : ∀ n b → s n ≡ b → s n ≡ false
    go n false p = p
    go n true  p with c₂ n p
    ... | cvr k with yes-path (flag s n) n (flag-true s n p)
    ...   | r , d , e = ⊥-elim (k (inj₂ (n , r)) d e)

  no-uniform : (∀ a → LvT (E a)) → WLPO
  no-uniform H s = dec s (S J (I s))
    (λ h → read s (H (lim (G s) (tF s h))))
    (λ n p → read s (H (lim (G s) (tT s n p))))

  no-uniformG : (∀ a → LvG (E a)) → WLPO
  no-uniformG H = no-uniform (λ a → proj₂ (H (suc a)))

  -- `no-Ω₂` 的一般形式: 前提 `full` 把原来隐含的 "第 1 层分支全称" 写出来
  no-Ω₂′ : LvG (toLv (Ω (natL 2))) → (∀ a → Bs (natL 1) (up tt (em a))) → WLPO
  no-Ω₂′ w full = no-uniformG (λ a → proj₂ (proj₂ w) (up tt (em a)) (full a))
```

## §2 地板是塔的地板时, `LvG` 是定理

`Sp a`: $a$ 的节点要么在低层, 要么是自然数之后的后继. 这个类里 `S` 从来不被问到. 它对路径与 $\approx$ 封闭. 最小的世界 (`canon`, 第 0 层取 $\omega$) 的地板都在这个类里, 所以 `Ω_m` ($m\le K$) 的层号是好层号, 对任何 `S`, 没有 `HE`.

```agda
module SpF (F : Fl) where
  open Leaf F

  Sp : Lv → Set
  Sp zero       = ⊤
  Sp (suc k)    = Σ ℕ λ n → k ≡ natL n
  Sp (lim _)    = ⊥
  Sp (limᴼ k g) = Lw k × (∀ x → A k x → Sp (g x))

  sp-nat : ∀ n → Sp (natL n)
  sp-nat zero    = tt
  sp-nat (suc n) = n , refl

  nat≈′ : ∀ n {a} → a ≈ᴮ natL n → a ≡ natL n
  nat≈′ zero z≈ = refl
  nat≈′ (suc n) (s≈ e) = cong Lv.suc (nat≈′ n e)

  sp≈ : ∀ {a b} → a ≈ᴮ b → Sp b → Sp a
  sp≈ z≈ p = tt
  sp≈ (s≈ e) (n , refl) = n , nat≈′ n e
  sp≈ (o≈ {k} h) (l , p) = l , (λ x a → sp≈ (h x (A⊆B k x a)) (p x a))

module SpNat (St : Stage) (K : ℕ) (isK : IsK K St) where
  open Stage St
  open Leaf fl
  open SpF fl public
  open IsK isK

  sp-at-nat : ∀ n r → Sp (at (natL n) r)
  sp-at-nat n r with at-nat n r
  ... | m , _ , e = subst Sp (sym e) (sp-nat m)

  sp-at : ∀ a → Sp a → ∀ r → Adm a r → Sp (at a r)
  sp-at (suc k) (n , refl) (inj₁ _) _ = sp-nat n
  sp-at (suc k) (n , refl) (inj₂ r) _ = sp-at-nat n r
  sp-at (limᴼ k g) (l , p) (inj₁ (inj₁ _)) _ with lw⇒ k l
  ... | m , _ , refl = sp-nat m
  sp-at (limᴼ k g) (l , p) (inj₁ (inj₂ r)) _ with lw⇒ k l
  ... | m , _ , refl = sp-at-nat m r
  sp-at (limᴼ k g) (l , p) (inj₂ (x , r)) (a , d) = sp-at (g x) (p x a) r d

module SpLvG (S : Sib) (St : Stage) (K : ℕ) (isK : IsK K St) where
  open Fin S St
  open K-stage K isK
  open SpF fl

  sp→lvg : ∀ a → Sp a → LvG a
  sp→lvg zero p = tt
  sp→lvg (suc k) (n , refl) =
    ch-fin (suc (natL n)) (inj₁ tt) n refl , lvt-fin (natL n) (fin-nat n)
  sp→lvg (limᴼ k g) (l , p) =
    inj₁ l , low→lvt k l , (λ x b → sp→lvg (g x) (p x (b l)))
```

## §3 塔上的不变量

`Spinv`: 地板元的层号都在 `Sp` 里. `sp↑` 是单步的搬运. `sp-canon` 是对 $K$ 的递归, 只有这里展开塔.

```agda
module SpUp (F F′ : Fl) (X : Ext F F′) where
  open Ext X
  module S₁ = SpF F
  module S₂ = SpF F′

  sp↑ : ∀ a → S₁.Sp a → S₂.Sp a
  sp↑ zero p = tt
  sp↑ (suc k) p = p
  sp↑ (limᴼ k g) (l , p) = low⊂ l , (λ x a → sp↑ (g x) (p x (A⊃ l a)))

Spinv : Stage → Set
Spinv St = ∀ j x → Fl.A (Stage.fl St) j x → SpF.Sp (Stage.fl St) (toLv x)

module SpStep (K : ℕ) (St : Stage) (isK : IsK K St) (bg : NatStep.Big K St isK) (on : NatStep.One K St isK) (WK : WorldK K St)
              (inv : Spinv St)
              (hL : ∀ p → Leaf.Adm (Stage.fl St) (World.L (WorldK.w WK)) p → SpF.Sp (Stage.fl St) (at (World.L (WorldK.w WK)) p)) where
  open Step K St isK bg on WK
  open SpUp (Stage.fl St) fl′ ext
  open SpF (Stage.fl St)

  inv′ : Spinv St′
  inv′ j x (inj₁ a) = sp↑ (toLv x) (inv j x a)
  inv′ _ x (inj₂ (refl , p , d , e)) = sp↑ (toLv x) (sp≈ e (hL p d))

canonT : Sib → ∀ K → Tw K
canonT S = tower W-ω (canon S)

sp-step : ∀ (S : Sib) k → Spinv (proj₁ (canonT S (suc k))) → Spinv (proj₁ (canonT S (suc (suc k))))
sp-step S k inv =
  let t = canonT S (suc k)
      St = proj₁ t
      isK = proj₁ (proj₂ t)
      θp = IsK.⇐lw isK k ≤-refl , (λ x a → inv _ x a)
  in SpStep.inv′ (suc k) St isK (proj₁ (proj₂ (proj₂ t))) (proj₂ (proj₂ (proj₂ t))) (canon S k t) inv
       (λ { (inj₁ _) d → θp
          ; (inj₂ q) d → SpNat.sp-at St (suc k) isK (toLv (Ω (natL (suc k)))) θp q d })

sp-canon : ∀ (S : Sib) K → Spinv (proj₁ (canonT S K))
sp-canon S zero = λ j x ()
sp-canon S (suc zero) =
  SpStep.inv′ 0 St₀ isK₀ (λ _ ()) (λ _ ()) W-ω (λ _ _ ())
    (λ { (n , r) d → SpNat.sp-at-nat St₀ 0 isK₀ n r })
sp-canon S (suc (suc k)) = sp-step S k (sp-canon S (suc k))
```

## §4 $\Omega_{\Omega_2}$ 的层号是好层号

`lvp-Ω`: $m\le K$ 时 `toLv (Ω m)` 是第 $K$ 阶段的好层号, 对任何 `S`. `Cert-ΩΩ`: 所以 $\psi_K(\Omega_{\Omega_m})$ 有证书, 无条件. 取 $K=m=2$ 就是 `no-Ω₂` 问的那个层号.

```agda
module Canon (S : Sib) (K : ℕ) where
  St : Stage
  St = proj₁ (canonT S K)

  isK : IsK K St
  isK = proj₁ (proj₂ (canonT S K))

  open LvPs S St public
  open K-stage K isK public
  open IsK isK using (⇐lw)
  private module SL = SpLvG S St K isK

  bl-nat : ∀ m → m ≤ K → BL (natL m)
  bl-nat m p = noo-nat m , (λ r → let j , q , e = at-nat m r in subst Lw (sym e) (⇐lw j (≤-trans q p)))

  lvg-Ω : ∀ m → m ≤ K → LvG (toLv (Ω (natL m)))
  lvg-Ω zero    p = SL.sp→lvg (Lv.suc Lv.zero) (0 , refl)
  lvg-Ω (suc j) p = SL.sp→lvg (toLv (Ω (natL (suc j)))) (⇐lw j p , (λ x a → sp-canon S K _ x a))

  Ωself : ∀ m → Eq (natL m) (Ω (natL m)) (Ω (natL m))
  Ωself m = Ω-self (natL m) (proj₁ (lvp-nat m)) (proj₁ (proj₂ (lvp-nat m)))

  cx-Ω : ∀ m → m ≤ K → Cx (toLv (Ω (natL m)))
  cx-Ω m p = cx-tree (bl-nat m p) (Good-Ω (natL m) (lvp-nat m)) (Ωself m)

  lvp-Ω : ∀ m → m ≤ K → LvP (toLv (Ω (natL m)))
  lvp-Ω m p = lvp-cx _ (lo-toLv (bl-nat m p) (Ω (natL m))) (cx-Ω m p) (lvg-Ω m p)

  Cert-ΩΩ : ∀ m → m ≤ K → WFᴬ (toLv (ψⁿ K (Ω (toLv (Ω (natL m))))))
  Cert-ΩΩ m p = Cert _ (lvp-Ω m p)

-- 目标 2, 输入 Ω_{Ω₂}: 对任何 S
Cert-Ω₂ : ∀ S → Canon.WFᴬ S 2 (toLv (PF.ψⁿ S 2 (Ω (toLv (Ω (natL 2))))))
Cert-Ω₂ S = Canon.Cert-ΩΩ S 2 2 ≤-refl

-- 对一切 K, 一切 m ≤ K
Cert-ΩΩ∀ : ∀ S K m → m ≤ K → Canon.WFᴬ S K (toLv (PF.ψⁿ S K (Ω (toLv (Ω (natL m))))))
Cert-ΩΩ∀ S K m = Canon.Cert-ΩΩ S K m
```

## §5 共存

`new`: 地板是塔的地板时, `LvG` 是定理. `¬full`: 塔的第 1 层地板不能含全部 `up tt (em a)`, 否则 WLPO. 旧定理并排的陈述在 [LevelKCoexist](LevelKCoexist.lagda.md).

```agda
module Co (S : Sib) where
  new : Canon.LvG S 2 (toLv (Ω (natL 2)))
  new = Canon.lvg-Ω S 2 2 ≤-refl

  ¬full : (∀ a → Canon.Bs S 2 (natL 1) (up tt (em a))) → WLPO
  ¬full = NegK.no-Ω₂′ S (Canon.St S 2) 2 (Canon.isK S 2) new
```

## §6 壁垒对照

`¬Reg-floor`: 第 0 层的地板不能同时含 $\omega_0+1$ 与 $\omega_1+1$ (两个基本列不字面 $\approx$ 的 $\omega$). 这是 `¬WF-Reg` 的地板版: 地板不能是 "全部规整的树". `bounded`: 新地板都严格低于它的界 $L$, 所以它绝不是 "`Ordᴰ` 的精确初始段含 $\Omega$-共尾元" 的那种下标类型.

```agda
ω₀ ω₁ : Ordᴸ zero
ω₀ = Tree.lim nt
ω₁ = Tree.lim (λ n → nt (suc n))

at-nt : ∀ n (r : Pre (toLv (nt n))) → Σ ℕ λ m → at (toLv (nt n)) r ≡ toLv (nt m)
at-nt (suc n) (inj₁ _) = n , refl
at-nt (suc n) (inj₂ r) = at-nt n r

lim≉ᴮ : ∀ (F : Fl) {f} {c} m → c ≡ toLv (nt m) → Leaf._≈ᴮ_ F (Lv.suc (Lv.lim f)) c → ⊥
lim≉ᴮ F zero refl ()
lim≉ᴮ F (suc zero) refl (Leaf.s≈ ())
lim≉ᴮ F (suc (suc m)) refl (Leaf.s≈ ())

¬Reg-floor : (St : Stage) → let open Stage St ; open Leaf fl in
             A zero (Tree.suc ω₀) → A zero (Tree.suc ω₁) → ⊥
¬Reg-floor St a a′ with Stage.cmpA St zero (Tree.suc ω₀) (Tree.suc ω₁) a a′
... | injᵃ (Leaf.viaᴬ (inj₁ _) _ ())
... | injᵃ (Leaf.viaᴬ (inj₂ (n , r)) _ e) =
  lim≉ᴮ (Stage.fl St) (proj₁ (at-nt (suc n) r)) (proj₂ (at-nt (suc n) r)) e
... | injᵇ (Leaf.viaᴬ (inj₁ _) _ ())
... | injᵇ (Leaf.viaᴬ (inj₂ (n , r)) _ e) =
  lim≉ᴮ (Stage.fl St) (proj₁ (at-nt n r)) (proj₂ (at-nt n r)) e
... | injᶜ (Leaf.s≈ (Leaf.l≈ h)) with h 0
...   | ()

bounded : ∀ (St : Stage) new N W j x → Next.A′ St new N W j x → Leaf.Lw (Stage.fl St) j ⊎ Leaf._≺ᴬ_ (Stage.fl St) (toLv x) (World.L W)
bounded St new N W j x (inj₁ a) = inj₁ (Leaf.A→Lw (Stage.fl St) j x a)
bounded St new N W j x (inj₂ (_ , p , d , e)) = inj₂ (Leaf.viaᴬ p d e)
```

## §7 判决相对的版本: 丰富的世界

世界丰富时 (`chooseF`), 地板元的层号可以含 `suc (limᴼ …)`, `LvG` 问 `S`. 这里把它写成前提 `HE`: `S` 在第 $j$ 层地板元的层号上正确. 只要这个, $\Omega_{j+1}$ 的层号就是好层号. `HE` **只问地板**, 不问原始分支, 所以 `no-Ω₂′` 的反例族进不来. `HE` 能不能兑现是定义一侧 ([UniformLvBase](UniformLvBase.lagda.md)) 的问题.

```agda
module HE (S : Sib) (St : Stage) (K : ℕ) (isK : IsK K St) where
  open LvPs S St
  open K-stage K isK
  open IsK isK using (⇐lw)

  bl-nat : ∀ m → m ≤ K → BL (natL m)
  bl-nat m p = noo-nat m , (λ r → let j , q , e = at-nat m r in subst Lw (sym e) (⇐lw j (≤-trans q p)))

  lvp-ΩHE : ∀ j → suc j ≤ K → (∀ x → A (natL j) x → LvG (toLv x)) → LvP (toLv (Ω (natL (suc j))))
  lvp-ΩHE j p he =
    let lj = ⇐lw j p
        b  = bl-nat (suc j) p
        pn = lvp-nat (suc j)
    in lvp-cx (toLv (Ω (natL (suc j)))) (lo-toLv b (Ω (natL (suc j))))
         (cx-tree b (Good-Ω (natL (suc j)) pn) (Ω-self (natL (suc j)) (proj₁ pn) (proj₁ (proj₂ pn))))
         (inj₁ lj , low→lvt (natL j) lj , (λ x bx → he x (bx lj)))

  Cert-ΩHE : ∀ j → suc j ≤ K → (∀ x → A (natL j) x → LvG (toLv x)) → WFᴬ (toLv (ψⁿ K (Ω (toLv (Ω (natL (suc j)))))))
  Cert-ΩHE j p he = Cert (toLv (Ω (natL (suc j)))) (lvp-ΩHE j p he)
```

## §8 第一个障碍: 低层必须字面分离

`Stage` 要 `low-≈`: 两个低层若 $a\approx b$ 就 $a\equiv b$. 它在 `b≃` 里用到: `o≈` 两侧的参数层必须字面相同. 这对自然数成立, 对单个 $\omega$ 也成立 (见 [LevelKOmega](LevelKOmega.lagda.md)). **对两个 $\approx$ 而不字面相同的低层不成立.** `ω-low→ext`: $\omega$ 与 $\omega'$ 同时作低层就给函数外延性的一个实例 (`--without-K` 不可证, 同 [Level](Level.lagda.md) 的 `lit→ext`). `¬both-low`: `limᴼ 0 g₀`, `limᴼ 0 g₁` 同时作低层, 只要地板是真子集 (有一个可判定的性质把某棵树分出去), 就是**矛盾**: 两个分支族在地板上一致, 在外面不同. `sep-1` 是实例: 第 1 阶段, 世界 $\omega$. 丰富的世界里, 同一个节点的两个相似的分支 ($z\approx z'$, $f\,z$ 与 $f\,z'$) 的层号正是这种情形, 所以低层不能含 `limᴼ`, 字面目标 $L$ 只能取前驱不含 `limᴼ` 且字面分离的层号.

```agda
+0 : ∀ a → a + 0 ≡ a
+0 zero    = refl
+0 (suc a) = cong suc (+0 a)

ω-low→ext : (St : Stage) → Fl.Lw (Stage.fl St) (lim natL) → Fl.Lw (Stage.fl St) (lim (λ n → natL (n + 0))) →
            natL ≡ (λ n → natL (n + 0))
ω-low→ext St l l′ = lim-inj (Stage.low-≈ St l l′ (Leaf.l≈ (λ n → Leaf.≡→≈′ (Stage.fl St) (cong natL (sym (+0 n))))))
  where
  lim-inj : ∀ {f g : ℕ → Lv} → Lv.lim f ≡ Lv.lim g → f ≡ g
  lim-inj refl = refl

module SepO (F : Fl) (sep : Ordᴸ zero → Bool) (lz : Fl.Lw F zero)
            (hA : ∀ x → Fl.A F zero x → sep x ≡ false) (x₁ : Ordᴸ zero) (h₁ : sep x₁ ≡ true) where
  open Leaf F

  bval : Bool → Lv
  bval true  = Lv.suc Lv.zero
  bval false = zero

  g₀ g₁ : Ordᴸ zero → Lv
  g₀ _ = zero
  g₁ x = bval (sep x)

  ≈g : limᴼ zero g₀ ≈ᴮ limᴼ zero g₁
  ≈g = o≈ λ x b → z≈g x (hA x (b lz))
    where
    z≈g : ∀ x → sep x ≡ false → g₀ x ≈ᴮ g₁ x
    z≈g x e rewrite e = z≈

  ¬lit-limᴼ : limᴼ zero g₀ ≡ limᴼ zero g₁ → ⊥
  ¬lit-limᴼ e = bad (inj e)
    where
    inj : ∀ {u v : Ordᴸ zero → Lv} → limᴼ zero u ≡ limᴼ zero v → u x₁ ≡ v x₁
    inj refl = refl
    bad′ : ∀ b → b ≡ true → Lv.zero ≡ bval b → ⊥
    bad′ _ refl ()
    bad : g₀ x₁ ≡ g₁ x₁ → ⊥
    bad = bad′ (sep x₁) h₁

  -- 字面分离对这两个层号是假的
  ¬both-low : (∀ {a b} → Lw a → Lw b → a ≈ᴮ b → a ≡ b) → Lw (limᴼ zero g₀) → Lw (limᴼ zero g₁) → ⊥
  ¬both-low h l l′ = ¬lit-limᴼ (h l l′ ≈g)

isLim : Ordᴸ zero → Bool
isLim (Tree.lim _) = true
isLim _            = false

-- 实例: 第 1 阶段, 世界 ω. 这里的 `Lw` 换成任何含这两个层号的集合都一样
module Sep1 (S : Sib) where
  no-lim : ∀ {h : ℕ → Ordᴸ zero} {c} m → c ≡ natL m → Leaf._≈ᴮ_ fl₀ (toLv (Tree.lim h)) c → ⊥
  no-lim zero refl ()
  no-lim (suc m) refl ()

  hA : ∀ x → Fl.A (Stage.fl (proj₁ (canonT S 1))) zero x → isLim x ≡ false
  hA Tree.zero _ = refl
  hA (Tree.suc x) _ = refl
  hA (Tree.lim h) (inj₁ ())
  hA (Tree.lim h) (inj₂ (_ , (n , r) , d , e)) with at-nat n r
  ... | m , _ , q = ⊥-elim (no-lim {h = h} m q e)

  open SepO (Stage.fl (proj₁ (canonT S 1))) isLim (inj₂ refl) hA (Tree.lim (λ _ → Tree.zero)) refl public
```
