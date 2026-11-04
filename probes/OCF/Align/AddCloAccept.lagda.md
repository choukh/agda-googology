# 换一步: 验收

> **验收文件.** 只有这里读 `NoCumsum`, `BTBOFull` 一带 (序数值验收的尺). 定义 ([AddCloRel](AddCloRel.lagda.md), [AddCloStr](AddCloStr.lagda.md)) 不读. 入口 [AddClo](AddClo.lagda.md).
>
> 主定理 `Up.T≼`: 只要 `S` 被 $\cdot\omega$ 盖住 (`SubS S ω⋅`) 且保持严格 (`SSt S`), 就有 `trA (Gen S).Top ≼ BTBOᴵ`. 实例 `T⁺≼`, `T²≼`, `T³≼`. 这是上界, 下界见 [AddClo](AddClo.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AddCloAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.Level hiding (below)
import OCF.Align.NoCumsum as NC
open NC using (BTBOᴵ)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ≼-suc)
open import OCF.Align.Uniform using (Uniform)
open import OCF.Align.BTBOValNeg using (HS-≅; ≼-irr; two-preds; ≺ᴵ→s≼; forget-≅ᴵ)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.TLRuleAccept using (PEb)
open import OCF.Align.TLRuleSpec using (_≤_; ⊲→≤)
open import OCF.Align.AddCloEmb using (Gr; emb)
import OCF.Align.AddCloEmb as E
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl; SV-L; Pos; pos≺; z<SV)
open import OCF.Align.BTBOFull using (γ-step)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; _≪_; _⊲_; lg⊲; ≪⊲; cmpN; keep; rise)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumUpAcceptSim using (Ix; iz; is; il; fr; Y-sim; Ix-≅)
import OCF.Align.TLRuleSum as N
open N using (D; n1; _⨾_; nl; module Gen; ω⋅)
open import OCF.Align.TLRuleMain using (Co-Ψ)
open import OCF.Align.TLRuleAccept using (lv; Ix-lv; forget-lv; VE; VEv; vr; vs; vz; CoV; Fψ; toFψ; Bump; Fψ≅; T≈)
open import OCF.Align.TLRuleVar using (trA; ≤→≼)
open import OCF.Align.AddCloRel using (Rel; r⨾; rn; rp; rt; rf; rs; r1; SubS; module Step)
open import OCF.Align.AddCloStr using (SA; SSt; SSt-ω; SSt-·2; SSt-+1; module Cell; Str; Pz; t⨾; tl; t1; ≪→s≤)
open import Data.Sum using (inj₁; inj₂)
```

## §1 严格的层是 `SV`

```agda
≪→≺ : ∀ {a b a′ b′} → a ≪ b → Ix a a′ → Ix b b′ → a′ ≺ᴵ b′
≪→≺ C.zero ia (is ib) = via (Ix-≅ ia ib) zero
≪→≺ (C.suc r) ia (is ib) with ≪→≺ r ia ib
... | via e q = via e (suc q)
≪→≺ (C.lim n r) ia (il h) with ≪→≺ r ia (h n)
... | via e q = via e (lim n q)

svA : ∀ a (w : Lg a) → SA a → SV (lv a w)
svA azero w s = svz
svA (asuc a) w s = svs (svA a w s)
svA (alim f) (st , ws) (sa , ss) =
  svl (λ n → svA (f n) (ws n) (ss n))
      (λ n → lv (f n) (ws n) , ≪→≺ (sa n) (Ix-lv (f n) (ws n)) (Ix-lv (f (suc n)) (ws (suc n))) , ⊑ᴵ-refl)
```

## §2 第 0 层的对应给层的嵌入

`grE`: [AddCloEmb](AddCloEmb.lagda.md) 的 `Gr` (只讲值) 搬成 `PEmb`. 前驱反映回字面的第一位置, 两个第一位置用 `cmpN` 比 (有界, 同一个层), 矛盾走值.

```agda
refl< : ∀ a (w : Lg a) {c} → c <ᴵ lv a w → Σ A (λ t → Σ (t ≪ a) (λ r → c ≅ᴵ lv t (lg⊲ (≪⊲ r) w)))
refl< (asuc a) w zero = a , C.zero , ≅ᴵ-refl _
refl< (asuc a) w (suc q) = let t , r , e = refl< a w q in t , C.suc r , e
refl< (alim f) (st , ws) (lim n q) = let t , r , e = refl< (f n) (ws n) q in t , C.lim n r , e

module GrE {a a′ : A} (w : Lg a) (w′ : Lg a′) (P : Gr a a′) where
  open Gr P

  Rf : ∀ {c} → c ≺ᴵ lv a w → Σ A (λ t → Σ (t ≪ a) (λ r → c ≅ᴵ lv t (lg⊲ (≪⊲ r) w)))
  Rf (via e q) = let t , r , e′ = refl< a w q in t , r , ≅ᴵ-trans e e′

  tg : ∀ {c} (r : c ≺ᴵ lv a w) → Σ A (λ t′ → (t′ ≪ a′) × G (proj₁ (Rf r)) t′)
  tg r = tot (proj₁ (proj₂ (Rf r)))

  m : ∀ {c} → c ≺ᴵ lv a w → Ordᴵ
  m r = lv (proj₁ (tg r)) (lg⊲ (≪⊲ (proj₁ (proj₂ (tg r)))) w′)

  vm : ∀ {c} (r : c ≺ᴵ lv a w) → forget (m r) ≅ trA (proj₁ (tg r))
  vm r = ≅-sym (forget-lv _ _)

  vc : ∀ {c} (r : c ≺ᴵ lv a w) → forget c ≅ trA (proj₁ (Rf r))
  vc r = ≅-trans (forget-≅ᴵ (proj₂ (proj₂ (Rf r)))) (≅-sym (forget-lv _ _))

  bd : ∀ {c} (r : c ≺ᴵ lv a w) → m r ≺ᴵ lv a′ w′
  bd r = ≪→≺ (proj₁ (proj₂ (tg r))) (Ix-lv _ _) (Ix-lv a′ w′)

  -- 两个第一位置: 前者严格小, 或后者不大于前者
  ord₂ : ∀ {c d} (r : c ≺ᴵ lv a w) (s : d ≺ᴵ lv a w) → (asuc (proj₁ (Rf r)) ≤ proj₁ (Rf s)) ⊎ (proj₁ (Rf s) ≤ proj₁ (Rf r))
  ord₂ r s with cmpN (proj₁ (proj₂ (Rf r))) (≪⊲ (proj₁ (proj₂ (Rf s)))) w
  ... | keep k = inj₁ (≪→s≤ k)
  ... | rise k = inj₂ (⊲→≤ k)

  mn : ∀ {c d} (r : c ≺ᴵ lv a w) (s : d ≺ᴵ lv a w) → c ≺ᴵ d → m r ≺ᴵ m s
  mn r s x with ord₂ r s
  ... | inj₂ k = ⊥-elim (≼-irr (forget _) (≼-trans (≺ᴵ→s≼ x) (≼-trans (≅→≼ (vc s)) (≼-trans (≤→≼ k) (≅→≼ (≅-sym (vc r)))))))
  ... | inj₁ k with lt (proj₂ (proj₂ (tg r))) (proj₂ (proj₂ (tg s))) k
  ...   | k′ with two-preds (bd r) (bd s)
  ...     | injᵃ y = y
  ...     | injᵇ y = ⊥-elim (≼-irr (forget (m s)) (≼-trans (≺ᴵ→s≼ y) (≼-trans (≅→≼ (vm r)) (≼-trans (≼-suc (≼-refl _)) (≼-trans (≤→≼ k′) (≅→≼ (≅-sym (vm s))))))))
  ...     | injᶜ y = ⊥-elim (≼-irr (trA (proj₁ (tg r))) (≼-trans (≤→≼ k′) (≼-trans (≅→≼ (≅-sym (vm s))) (≼-trans (≅→≼ (forget-≅ᴵ (≅ᴵ-sym y))) (≅→≼ (vm r))))))

  ch : ∀ {c d} (r : c ≺ᴵ lv a w) (s : d ≺ᴵ lv a w) → c ≅ᴵ d → m r ≅ᴵ m s
  ch r s x with ord₂ r s | ord₂ s r
  ... | inj₁ k | _ = ⊥-elim (≼-irr (forget _) (≼-trans (s≼s (≅→≼ (vc r))) (≼-trans (≤→≼ k) (≼-trans (≅→≼ (≅-sym (vc s))) (≅→≼ (forget-≅ᴵ (≅ᴵ-sym x)))))))
  ... | inj₂ _ | inj₁ k = ⊥-elim (≼-irr (forget _) (≼-trans (s≼s (≅→≼ (vc s))) (≼-trans (≤→≼ k) (≼-trans (≅→≼ (≅-sym (vc r))) (≅→≼ (forget-≅ᴵ x))))))
  ... | inj₂ k₁ | inj₂ k₂ with le (proj₂ (proj₂ (tg s))) (proj₂ (proj₂ (tg r))) k₁ | le (proj₂ (proj₂ (tg r))) (proj₂ (proj₂ (tg s))) k₂ | two-preds (bd r) (bd s)
  ...   | l₁ | l₂ | injᵃ y = ⊥-elim (≼-irr (forget (m r)) (≼-trans (≺ᴵ→s≼ y) (≼-trans (≅→≼ (vm s)) (≼-trans (≤→≼ l₁) (≅→≼ (≅-sym (vm r)))))))
  ...   | l₁ | l₂ | injᵇ y = ⊥-elim (≼-irr (forget (m s)) (≼-trans (≺ᴵ→s≼ y) (≼-trans (≅→≼ (vm r)) (≼-trans (≤→≼ l₂) (≅→≼ (≅-sym (vm s)))))))
  ...   | l₁ | l₂ | injᶜ y = y

  pe : PEmb (lv a w) (lv a′ w′)
  pe = record { map = m ; bnd = bd ; mono = mn ; coh = ch }
```

## §3 上界和下界

`Cells`: 一个 `S` 的对角线. 一步: 同一个世界里 $\psi^S$ 与 $\psi^{\omega}$ 比 (`Step.Ψ≤`), 跨世界用 $\cdot\omega$ 现成的 `Bump`. 下界还要把 $\psi^\omega$ 的层嵌进 $\psi^S$ 的层 (`grE`).

```agda
module Cells (S : ∀ {t} → D t → D t) (hT : SSt S) where
  module G = Gen S
  module C₀ = Cell S hT

  u : ℕ → A
  u n = proj₁ (G.cell n)

  lu : ∀ n → Lg (u n)
  lu n = proj₂ (G.cell n)

  a : ℕ → Ordᴵ
  a n = lv (u n) (lu n)

  sv : ∀ n → SV (a n)
  sv n = svA (u n) (lu n) (C₀.SA-cell n)

  ps : ∀ n → Pos (a n)
  ps n = pos≺ (≪→≺ (C₀.z≪cell n) iz (Ix-lv (u n) (lu n)))

  -- ψ^ω 在世界 u n 上对上旧折叠
  V : ∀ n → VE (lv (N.Ψ (u n) (lu n)) (N.Lg-Ψ (u n) (lu n))) (toFψ (a n))
  V n = vr (CoV (Co-Ψ (u n) (lu n)) (N.Lg-Ψ (u n) (lu n)) h) (toLevel-≅ h (Uniform (a n)) E)
    where
    E = Y-sim (lu n) (Ix-lv (u n) (lu n)) (z<SV (sv n) (ps n))
    h = HS-≅ E (Uniform (a n))

  Lv : ℕ → Ordᴵ
  Lv = NC.L

  γ≼L : ∀ m → NC.γ m ≼ forget (Lv m)
  γ≼L m = ≅→≼ (≅-sym (forget-toLevel (NC.γ m) (NC.cert m)))

  L≼γ : ∀ m → forget (Lv m) ≼ NC.γ m
  L≼γ m = ≅→≼ (forget-toLevel (NC.γ m) (NC.cert m))

  toF≅ : ∀ m → toFψ (Lv m) ≅ᴵ Lv (suc m)
  toF≅ m = toLevel-≅ (Uniform (Lv m)) (NC.cert (suc m)) (≅-refl⁰ (NC.γ (suc m)))

  g : ℕ → ℕ
  g zero = 0
  g (suc n) = suc (suc (g n))

module Up (S : ∀ {t} → D t → D t) (hS : SubS S ω⋅) (hT : SSt S) where
  open Cells S hT public
  module M = Step S ω⋅ hS

  Ψ≼F : ∀ n → forget (a (suc n)) ≼ Fψ (a n)
  Ψ≼F n =
    ≼-trans (≅→≼ (≅-sym (forget-lv (u (suc n)) (lu (suc n)))))
    (≼-trans (≤→≼ (M.Ψ≤ (u n) (lu n)))
    (≼-trans (≅→≼ (forget-lv (N.Ψ (u n) (lu n)) (N.Lg-Ψ (u n) (lu n))))
    (≼-trans (proj₁ (VEv (V n)))
             (≅→≼ (forget-toLevel (Fψ (a n)) (Uniform (a n)))))))

  UpL : ∀ n → forget (a n) ≼ forget (Lv (g n))
  UpL zero = ≼-refl _
  UpL (suc n) =
    ≼-trans (Ψ≼F n)
    (≼-trans (Bump (sv n) (SV-L (g n)) (UpL n))
    (≼-trans (Fψ≅ (toF≅ (g n)))
             (γ≼L (suc (suc (g n))))))

  T≼ : trA G.Top ≼ BTBOᴵ
  T≼ = l≼ (λ n → ≼l (g (suc n))
    (≼-trans (≅→≼ (forget-lv (u (suc n)) (lu (suc n))))
    (≼-trans (UpL (suc n))
    (≼-trans (L≼γ (g (suc n))) (γ-step (g (suc n)))))))

module Dn (S : ∀ {t} → D t → D t) (hS : SubS ω⋅ S) (hT : SSt S) where
  open Cells S hT public
  module M = Step ω⋅ S hS

  GE : ∀ k → PEmb (lv (N.Ψ (u k) (lu k)) (N.Lg-Ψ (u k) (lu k))) (a (suc k))
  GE k = GrE.pe (N.Lg-Ψ (u k) (lu k)) (lu (suc k)) (emb (r⨾ r1 (M.Rψ (u k) (lu k))))

  stp : ∀ k → Fψ (toFψ (a k)) ≼ Fψ (a (suc k))
  stp k = ≼-trans (Ψ-emb (PEb (V k))) (Ψ-emb (GE k))

  upS : ∀ k → Fψ (a k) ≼ forget (a (suc k))
  upS k =
    ≼-trans (≅→≼ (≅-sym (forget-toLevel (Fψ (a k)) (Uniform (a k)))))
    (≼-trans (proj₂ (VEv (V k)))
    (≼-trans (≅→≼ (≅-sym (forget-lv (N.Ψ (u k) (lu k)) (N.Lg-Ψ (u k) (lu k)))))
    (≼-trans (≤→≼ (M.Ψ≤ (u k) (lu k)))
             (≅→≼ (forget-lv (u (suc k)) (lu (suc k)))))))

  DnL : ∀ m → forget (Lv m) ≼ forget (a (g m))
  DnL zero = proj₂ (VEv {a = a 0} {b = suc zero} (vs vz))
  DnL (suc m) =
    ≼-trans (L≼γ (suc m))
    (≼-trans (Bump (SV-L m) (sv (g m)) (DnL m))
    (≼-trans (stp (g m))
             (upS (suc (g m)))))

  T≽ : BTBOᴵ ≼ trA G.Top
  T≽ = l≼ (λ m → ≼l (suc (g m))
    (≼-trans (γ≼L (suc m)) (≼-trans (DnL (suc m)) (≅→≼ (≅-sym (forget-lv (u (suc (suc (g m)))) (lu (suc (suc (g m))))))))))
```

## §4 实例

```agda
hS⁺ : SubS (λ _ → n1) ω⋅
hS⁺ _ o _ = rn 0 o

hS² : SubS (λ c → c) ω⋅
hS² _ _ q = rn 0 q

-- ·3: 第一位置含两个 c
·3ˢ : ∀ {t} → D t → D t
·3ˢ c = c ⨾ c

hS³ : SubS ·3ˢ ω⋅
hS³ _ _ q = rt 0 q (rn 0 q)

SSt-·3 : SSt ·3ˢ
SSt-·3 h p = t⨾ h h , inj₁ p

T⁺≼ : trA (Gen.Top (λ _ → n1)) ≼ BTBOᴵ
T⁺≼ = Up.T≼ (λ _ → n1) hS⁺ SSt-+1

T²≼ : trA (Gen.Top (λ c → c)) ≼ BTBOᴵ
T²≼ = Up.T≼ (λ c → c) hS² SSt-·2

T³≼ : trA (Gen.Top ·3ˢ) ≼ BTBOᴵ
T³≼ = Up.T≼ ·3ˢ hS³ SSt-·3

-- 对照: 这条路线对 S = ω⋅ 重新证明上半
Tʷ≼ : trA N.Top ≼ BTBOᴵ
Tʷ≼ = Up.T≼ ω⋅ (λ _ _ q → rp (λ _ → q)) SSt-ω
```

### 更强的 $S$: 下界

```agda
-- c·ω²
ω²ˢ : ∀ {t} → D t → D t
ω²ˢ c = nl (λ _ → nl (λ _ → c))

hω² : SubS ω⋅ ω²ˢ
hω² _ _ q = rp (λ _ → rn 0 q)

SSt-ω² : SSt ω²ˢ
SSt-ω² h p = tl (λ _ → tl (λ _ → h) (λ _ → p)) (λ _ → 0 , p) , (0 , (0 , p))

Tω²≽ : BTBOᴵ ≼ trA (Gen.Top ω²ˢ)
Tω²≽ = Dn.T≽ ω²ˢ hω² SSt-ω²

-- 对照: 这条路线对 S = ω⋅ 重新证明下半
Tʷ≽ : BTBOᴵ ≼ trA N.Top
Tʷ≽ = Dn.T≽ ω⋅ (λ _ _ q → rp (λ _ → q)) SSt-ω
```

### 夹在中间: 两边都有, 值相等

`1+c·ω` 与 `c+c·ω` 字面上不是 `ω⋅`, 但上下都被它夹住. 所以 $\psi_0(\Omega_\Omega)$ 这一站的值不认 $\cdot\omega$ 这一个写法.

```agda
o+ωˢ : ∀ {t} → D t → D t
o+ωˢ c = n1 ⨾ nl (λ _ → c)

c+ωˢ : ∀ {t} → D t → D t
c+ωˢ c = c ⨾ nl (λ _ → c)

T-1+cω : trA (Gen.Top o+ωˢ) ≈ᵛ BTBOᴵ
T-1+cω = Up.T≼ o+ωˢ (λ _ o′ q → rt 0 o′ (rp (λ _ → q))) SS , Dn.T≽ o+ωˢ (λ _ _ q → rs (rp (λ _ → q))) SS
  where
  SS : SSt o+ωˢ
  SS h p = t⨾ t1 (tl (λ _ → h) (λ _ → p)) , inj₁ tt

T-c+cω : trA (Gen.Top c+ωˢ) ≈ᵛ BTBOᴵ
T-c+cω = Up.T≼ c+ωˢ (λ _ _ q → rt 0 q (rp (λ _ → q))) SS , Dn.T≽ c+ωˢ (λ _ _ q → rs (rp (λ _ → q))) SS
  where
  SS : SSt c+ωˢ
  SS h p = t⨾ h (tl (λ _ → h) (λ _ → p)) , inj₁ p

-- c+ω: 加法封闭换成后继封闭的最小点 (见 AddCloNeg). 只有上界.
c+1ωˢ : ∀ {t} → D t → D t
c+1ωˢ c = c ⨾ nl (λ _ → n1)

T-c+ω≼ : trA (Gen.Top c+1ωˢ) ≼ BTBOᴵ
T-c+ω≼ = Up.T≼ c+1ωˢ (λ _ o′ q → rt 0 q (rp (λ _ → o′))) (λ h p → t⨾ h (tl (λ _ → t1) (λ _ → tt)) , inj₁ p)
```

## §5 一般的下界, 换初态

`DnG`: 任何对角线 $u_0=1$, $u_{n+1}=\mathtt{sum}\;0\;(X\,u_n)$, 只要 $X$ 严格且在同一世界里盖住 $\psi^\omega$ 的输入 ($1+\psi^\omega_0(\Omega_y)\trianglelefteq X\,y$), 值就不低于 $\psi_0(\Omega_\Omega)$. `Dn` 是它的特例; 这里用于初态 $\Omega_t+1$.

```agda
open import OCF.Align.AddCloStr using (saSum; pos≪)
open import OCF.Align.TLRuleSum using (sum; Lg-sum)
open import OCF.Align.AddCloRel using (sum-mono)
open import OCF.Align.TLRuleSpec using (z≤; ≤l)
open import OCF.Align.TLRuleSpec using () renaming (l≤ to l≤′; ≤l to ≤l′; ≤-refl to ≤-refl′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import OCF.Align.AddCloInit as I

module DnG (X : ∀ y → Lg y → D azero) (sX : ∀ y w → SA y → Str azero (X y w)) (pX : ∀ y w → Pz (X y w))
           (R : ∀ y w → Rel azero (n1 ⨾ N.Ψd y w) (X y w)) where
  cl : ℕ → Σ A Lg
  cl zero = asuc azero , tt
  cl (suc n) = sum azero (X (proj₁ (cl n)) (proj₂ (cl n))) , Lg-sum azero (X (proj₁ (cl n)) (proj₂ (cl n))) tt

  TopG : A
  TopG = alim (λ n → proj₁ (cl (suc n)))

  u : ℕ → A
  u n = proj₁ (cl n)
  lu : ∀ n → Lg (u n)
  lu n = proj₂ (cl n)

  sa : ∀ n → SA (u n)
  sa zero = tt
  sa (suc n) = saSum azero tt (sX (u n) (lu n) (sa n))

  a : ℕ → Ordᴵ
  a n = lv (u n) (lu n)

  sv : ∀ n → SV (a n)
  sv n = svA (u n) (lu n) (sa n)

  z≪ : ∀ n → azero ≪ u n
  z≪ zero = C.zero
  z≪ (suc n) = pos≪ azero (sX (u n) (lu n) (sa n)) (pX (u n) (lu n))

  ps : ∀ n → Pos (a n)
  ps n = pos≺ (≪→≺ (z≪ n) iz (Ix-lv (u n) (lu n)))

  V : ∀ n → VE (lv (N.Ψ (u n) (lu n)) (N.Lg-Ψ (u n) (lu n))) (toFψ (a n))
  V n = vr (CoV (Co-Ψ (u n) (lu n)) (N.Lg-Ψ (u n) (lu n)) h) (toLevel-≅ h (Uniform (a n)) E)
    where
    E = Y-sim (lu n) (Ix-lv (u n) (lu n)) (z<SV (sv n) (ps n))
    h = HS-≅ E (Uniform (a n))

  open Cells ω⋅ SSt-ω using (Lv; γ≼L; L≼γ; g)

  stp : ∀ k → Fψ (toFψ (a k)) ≼ Fψ (a (suc k))
  stp k = ≼-trans (Ψ-emb (PEb (V k))) (Ψ-emb (GrE.pe (N.Lg-Ψ (u k) (lu k)) (lu (suc k)) (emb (R (u k) (lu k)))))

  upS : ∀ k → Fψ (a k) ≼ forget (a (suc k))
  upS k =
    ≼-trans (≅→≼ (≅-sym (forget-toLevel (Fψ (a k)) (Uniform (a k)))))
    (≼-trans (proj₂ (VEv (V k)))
    (≼-trans (≅→≼ (≅-sym (forget-lv (N.Ψ (u k) (lu k)) (N.Lg-Ψ (u k) (lu k)))))
    (≼-trans (≤→≼ (sum-mono {azero} {azero} z≤ (R (u k) (lu k))))
             (≅→≼ (forget-lv (u (suc k)) (lu (suc k)))))))

  DnL : ∀ m → forget (Lv m) ≼ forget (a (g m))
  DnL zero = proj₂ (VEv {a = a 0} {b = suc zero} (vs vz))
  DnL (suc m) =
    ≼-trans (L≼γ (suc m))
    (≼-trans (Bump (SV-L m) (sv (g m)) (DnL m))
    (≼-trans (stp (g m))
             (upS (suc (g m)))))

  T≽ : BTBOᴵ ≼ trA TopG
  T≽ = l≼ (λ m → ≼l (suc (g m))
    (≼-trans (γ≼L (suc m)) (≼-trans (DnL (suc m)) (≅→≼ (≅-sym (forget-lv (u (suc (suc (g m)))) (lu (suc (suc (g m))))))))))

-- 初态 Ω_t + 1: 值不低于 ψ₀(Ω_Ω)
module DI = DnG I.GenI.XI I.GenI.strXI (λ _ _ → inj₁ tt) I.GenI.RψI

cl≡ : ∀ n → DI.cl n ≡ I.GenI.cellI n
cl≡ zero = refl
cl≡ (suc n) = cong (λ c → sum azero (I.GenI.XI (proj₁ c) (proj₂ c)) , Lg-sum azero (I.GenI.XI (proj₁ c) (proj₂ c)) tt) (cl≡ n)

TI≽ : BTBOᴵ ≼ trA I.GenI.TopI
TI≽ = ≼-trans DI.T≽ (≤→≼ (l≤′ (λ n → ≤l′ n (subst (λ c → proj₁ (DI.cl (suc n)) ≤ proj₁ c) (cl≡ (suc n)) (≤-refl′ _)))))
```

## §6 去掉地板: 值掉下来

```agda
one₀ two₀ : A
one₀ = asuc azero
two₀ = asuc one₀

two≤Top : two₀ ≤ N.Top
two≤Top = ≤l 0 (sum-mono {azero} {azero} {n1 ⨾ n1} {n1 ⨾ N.Ψd one₀ tt} z≤ (r⨾ r1 (rf (rn 0 (rf (rf r1))))))

-- ψ(0)=0 这一行的对角线严格低于 ψ₀(Ω_Ω)
TD≺ : suc (trA I.D₀.Top) ≼ BTBOᴵ
TD≺ = ≼-trans (s≼s (≤→≼ I.TopD≤1)) (≼-trans (≤→≼ two≤Top) (proj₁ T≈))

TD≇ : ¬ (BTBOᴵ ≼ trA I.D₀.Top)
TD≇ le = ≼-irr (trA I.D₀.Top) (≼-trans TD≺ le)
```
