# 证书 (一): 互模拟, `os` 处带地板的上界

> 不含记号. 结论写在 [GuardCert](GuardCert.lagda.md). 由 [GuardWeakRel](GuardWeakRel.lagda.md) 改写 (脚本 + 手写): 同一个互模拟, 三处改动, 都是 $\psi_0(\Omega_{\Omega+1})$ 的桥逼出来的.
>
> 1. **`rs` 带 `FlrLe π B`: 这个 `os` 的输入地板上每个帧的值 $\sqsubseteq B$.** 这是不变量该写的地方 ([GuardWeak](GuardWeak.lagda.md) 的判断: 写在 `os` 与闭包处). 没有它, `W ⊕ ocl` 的地板读得太高, `≲` 不成立. 用 $\sqsubseteq$ 不用 `Simᴵ`: `Simᴵ` 不尊重 $\cong$.
> 2. **`rup` 删掉.** 它只在 `rmk` 的第二个参数里出现. `rmk r dk l iv m`: `m` 直接是 $x$ 与 $\hat y'$ 在低一层的关系. `dk`: 节点是 $\lceil k\rceil$.
> 3. **模式 `Md`.** `gd`: 严格的 $\dot\Omega$ 的像, `rs` 只在 $B$ 是 0 时出现. `rmk (self n)` 的 $z$ 是 `gd` 的: 极限层 $\dot\Omega$ 的头只有 `ol`, 下一个 `omk` 就下降, 所以 `cover-false` 那个帧 (规范位置留在 $\lim f$) 碰不到 `rs`. **这就是 "`rmk (self n)` 要记下它是 $\dot\Omega$ 的像" 的形式; 不记字面的 $\dot\Omega$, 因为它要过 `≈` 的搬运.**
>
> `InvS R k`: `rmk zero` 的位置的不变量. `iE`: $R$ 以 `suc self` 结尾 (读法在 [GuardCertNf](GuardCertNf.lagda.md) 给出帧的值 $\cong k$). `iL`: 层有闭包, 帧的值 $\sqsubseteq k$.
>
> `HPf L tc`: `R-ι` 要的读法性质. 无闭包的层平凡 (`hp-free`). $c_1$, $c_1+1$ 的实例在 [GuardCertNf](GuardCertNf.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardCertRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.GuardTightCum
open import OCF.Free.Aux using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ʳ)
open import OCF.Free.Prefix using (Z; toZ; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; out-intoˢ; coeˢ; addˢ; _+ˢ_; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Restrˢ; Ωˢ)
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; zl; sl; ll; ĉl)
open Ord₊ˢ
open Restrˢ
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightTab Dom₀ using (Strict; st-suc; st-lim; st-fst; st-bra; stCp; st⊙; _⊙_)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardWeakRel using (⌜_⌝; ⌜≈⌝; ⌜≈⁻⌝; pullG; FrL; fz; fs′; fl; FrG; Fr≈; cb-sem; cu-sem; clash; Emp; ZZ; zz-≈; zz-≅; ZB; zb-≅; out-intoU; out-intoC; out-intoV; cv-into; lk≈; ZNL; zz-any; zz-nz; zz-cp₁)
```

## §1 地板的上界, 位置的不变量

```agda
FlrLe : Fl → Ordᴵ → Set
FlrLe π B = ∀ f → Mem π f → fη f ⊑ᴵ B

le-≅ : ∀ {π a b} → a ≅ᴵ b → FlrLe π a → FlrLe π b
le-≅ e c f m = ⊑ᴵ-≅ʳ (c f m) e

le-Sim : ∀ {π k ℓ} → Simᴵ k ℓ → FlrLe π k → FlrLe π ℓ
le-Sim σ c f m = ⊑ᴵ-trans (c f m) (Sim→⊑ᴵ σ)

le-emp : ∀ {π B} → Emp π → FlrLe π B
le-emp e f m = ⊥-elim (e m)

le-∪ : ∀ {π ρ B} → FlrLe π B → FlrLe ρ B → FlrLe (π ∪ ρ) B
le-∪ a b f (ml m) = a f m
le-∪ a b f (mr m) = b f m

-- 位置以 suc self 结尾
data EndS : ∀ {k a} → Cp k a → Set where
  es0  : ∀ {b} → EndS (Lv.suc (Lv.self {c = b}))
  es-s : ∀ {k b} {P : Cp k b} → EndS P → EndS (Lv.suc P)
  es-l : ∀ {k f n} {P : Cp k (f n)} → EndS P → EndS (Lv.lim {f = f} n P)
  es-f : ∀ {k c t g} {P : Cp k t} → EndS P → EndS (Lv.fst {c = c} {t = t} {g = g} P)
  es-b : ∀ {k c t g η e} {P : Cp k (g η e)} → EndS P → EndS (Lv.bra {c = c} {t = t} {g = g} η e P)

data InvS {k₁ a} (R : Strict k₁ a) (k : Ordᴵ) : Set where
  iE : EndS (stCp R) → InvS R k
  iL : (FrL a → ⊥) → FlrLe (pF (stCp R)) k → InvS R k

iv-≅ : ∀ {k₁ a} {R : Strict k₁ a} {k k′} → k ≅ᴵ k′ → InvS R k → InvS R k′
iv-≅ e (iE h) = iE h
iv-≅ e (iL n c) = iL n (le-≅ e c)

-- 帧的值沿可容许性搬运
le-adm : ∀ {π B a c} (Q : Cp a c) → AdmC (cov π) Q → FlrLe π B → FlrLe (pF Q) B
le-adm (Lv.suc Q) a h f m = le-adm Q a h f m
le-adm (Lv.lim n Q) a h f m = le-adm Q a h f m
le-adm (Lv.fst Q) a h f m = le-adm Q a h f m
le-adm (Lv.bra η e Q) ((_ , _ , _ , _ , m₁ , _) , a) h f (ml hr) = h _ m₁
le-adm (Lv.bra η e Q) (_ , a) h f (mr m) = le-adm Q a h f m

⊲→⊑ : ∀ {a η} → a ⊲ η → a ⊑ᴵ η
⊲→⊑ ⊲= = ⊑ᴵ-refl
⊲→⊑ {a} (⊲ˢ h) = pr⊑ a (h (λ q → q))

le-cov : ∀ {π ρ B} → Cov π ρ → FlrLe ρ B → FlrLe π B
le-cov w c f m with w m
... | f′ , m₁ , _ , lt = ⊑ᴵ-trans (⊲→⊑ lt) (c f′ m₁)

-- 无闭包的层
fr-cp : ∀ {a L} → FrL L → Cp a L → FrL a
fr-cp h Lv.self = h
fr-cp (fs′ h) (Lv.suc P) = fr-cp h P
fr-cp (fl h) (Lv.lim n P) = fr-cp (h n) P

fr-emp : ∀ {a L} → FrL L → (P : Cp a L) → Emp (pF P)
fr-emp h Lv.self ()
fr-emp (fs′ h) (Lv.suc P) m = fr-emp h P m
fr-emp (fl h) (Lv.lim n P) m = fr-emp (h n) P m

fr≈⁻ : ∀ {a b} → FrL b → a ≈ b → FrL a
fr≈⁻ h e = Fr≈ h (≈-sym e)

-- 接上位置保持结尾
end⊙ : ∀ {k a b} {Q : Cp k a} → EndS Q → (P : Cp a b) → EndS (P ⊙ Q)
end⊙ h Lv.self = h
end⊙ h (Lv.suc P) = es-s (end⊙ h P)
end⊙ h (Lv.lim n P) = es-l (end⊙ h P)
end⊙ h (Lv.fst P) = es-f (end⊙ h P)
end⊙ h (Lv.bra η e P) = es-b (end⊙ h P)

EndT : ∀ {k₁ a} (R : Strict k₁ a) → EndS (stCp R) → ∀ {b} (P : Cp a b) → EndS (stCp (st⊙ P R))
EndT R h Lv.self = h
EndT R h (Lv.suc P) = es-s (end⊙ h P)
EndT R h (Lv.lim n P) = es-l (end⊙ h P)
EndT R h (Lv.fst P) = es-f (end⊙ h P)
EndT R h (Lv.bra η e P) = es-b (end⊙ h P)

-- 读法要满足的性质: 规范位置的帧有上界
HPf : (L : LG) (tc : Tc L) → Set
HPf L tc = ∀ {k₁ a′ k} (P : Cp a′ L) (R′ : Strict k₁ a′) → k₁ ≈ ⌜ k ⌝ →
           (ZB k → FlrLe (pF (stCp (posS (nfS L tc (st⊙ P R′))))) k) ×
           (InvS R′ k → FlrLe (pF (stCp (posS (nfS L tc (st⊙ P R′))))) k × InvS (posS (nfS L tc (st⊙ P R′))) k)
```

## §2 关系

```agda
data Md : Set where
  fr gd : Md

RsC : Md → Ordᴵ → Set
RsC fr B = ⊤
RsC gd B = ZB B

rc-≅ : ∀ {m a b} → a ≅ᴵ b → RsC m a → RsC m b
rc-≅ {m = fr} e a = tt
rc-≅ {m = gd} e a = zb-≅ e a

mdOf : ∀ {k B} → k ◃₁ B → Md
mdOf zero = fr
mdOf (self n) = gd

IvOf : ∀ {k B k₁ A} → k ◃₁ B → Strict k₁ A → Set
IvOf {k} zero R = InvS R k
IvOf (self n) R = ⊤

module _ (B : Ordᴵ) (LR : Md → ∀ {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordˢ i → Set) where
  data R₊ (m₀ : Md) : ∀ {A π} → O A π → Ordˢ B → Set where
    rz  : ∀ {A π} → R₊ m₀ {A} {π} o0 zero
    rs  : ∀ {A π} {x : O A π} {ŷ} → RsC m₀ B → FlrLe π B → R₊ m₀ x ŷ → R₊ m₀ (os x) (suc ŷ)
    rl  : ∀ {A π} {F : ℕ → O A π} {f} → (∀ n → R₊ m₀ (F n) (f n)) → R₊ m₀ (ol F) (lim f)
    rwk : ∀ {A π ρ} {w : Wk π ρ} {x : O A π} {ŷ} → R₊ m₀ x ŷ → R₊ m₀ (owk w x) ŷ
    rcv : ∀ {A π ρ} {w : Cov π ρ} {x : O A π} {ŷ} → R₊ m₀ x ŷ → R₊ m₀ (ocv w x) ŷ
    rmk : ∀ {A π ξ k₁ k} {R : Strict k₁ A} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs A R ξ} {x : O A π}
            (r : k ◃₁ B) {ŷ′ : Uˢ k (◃₁→◃ r)} → k₁ ≈ ⌜ k ⌝ →
            LR (mdOf r) (◃₁→◃ r) (outV R z) (outˢ (◃₁→◃ r) ŷ′) → IvOf r R →
            LR (mdOf r) (◃₁→◃ r) x (outˢ (◃₁→◃ r) ŷ′) → R₊ m₀ (omk R lk ad z x) (up r ŷ′)
    rΩ  : ∀ {A π k j} (r : k < A) (cv : Adm (cov π) r) (q : j <ᴵ B) {h : ∀ ξ → Us A r ξ → O A (ξ ∪ π)} {f : Uˢ j (<→◃ q) → Ordˢ B} →
          k ≈ ⌜ j ⌝ →
          (∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → LR fr (<→◃ q) z ẑ → R₊ m₀ (h ξ (intoU r z)) (f (intoˢ (<→◃ q) ẑ))) →
          R₊ m₀ (oΩ r cv h) (limᵢ q f)
    rŝ  : ∀ {A π c₀ c′} {t : O A π} {g : ∀ η → c₀ ⊑ᴵ η → O A π} {t̂ : Ordˢ B} {ĝ : ∀ η → c′ ⊑ᴵ η → Ordˢ B} →
          ZZ A B → c₀ ⊑ᴵ c′ → R₊ m₀ t t̂ → (∀ η e e′ → R₊ m₀ (g η e) (ĝ η e′)) → R₊ m₀ (oŝ c₀ t g) (ŝ c′ t̂ ĝ)
    rĉ  : ∀ {A π c₀ c′ z ẑ} {zg : ∀ η → c₀ ⊑ᴵ η → Z} {ẑg : ∀ η → c′ ⊑ᴵ η → Z} {o₀ : O A π} {o : ∀ η → c₀ ⊑ᴵ η → O A π} {ô₀ : Ordˢ B} {ô : ∀ η → c′ ⊑ᴵ η → Ordˢ B} →
          c₀ ⊑ᴵ c′ → z ≲ᶻ ẑ → (∀ η e e′ → zg η e ≲ᶻ ẑg η e′) → R₊ m₀ o₀ ô₀ → (∀ η e e′ → R₊ m₀ (o η e) (ô η e′)) → R₊ m₀ (oĉ c₀ z zg o₀ o) (ĉᴸ c′ ẑ ẑg ô₀ ô)
    rĉŝ : ∀ {A π π′ c₀ c′} {t₀ : O Lv.zero π′} {g₀ : ∀ η → c₀ ⊑ᴵ η → O Lv.zero π′} {o₀ : O A π} {o : ∀ η → c₀ ⊑ᴵ η → O A π} {t̂ : Ordˢ B} {ĝ : ∀ η → c′ ⊑ᴵ η → Ordˢ B} →
          ZB B → c₀ ⊑ᴵ c′ → R₊ m₀ t₀ t̂ → (∀ η e e′ → R₊ m₀ (g₀ η e) (ĝ η e′)) → R₊ m₀ o₀ t̂ → (∀ η e e′ → R₊ m₀ (o η e) (ĝ η e′)) →
          R₊ m₀ (oĉ c₀ (rdZ t₀) (λ η e → rdZ (g₀ η e)) o₀ o) (ŝ c′ t̂ ĝ)

Rs : ∀ B → Md → ∀ {A π} → O A π → Ordˢ B → Set
LRs : ∀ B → Md → ∀ {i} → i ◃ B → ∀ {A ξ} → O A ξ → Ordˢ i → Set
Rs B m x y = R₊ B (LRs B) m x y
LRs (suc k)   m zero      x y = Rs k m x y
LRs (suc c)   m (suc r)   x y = LRs c m r x y
LRs (lim f s) m (self n)  x y = Rs (f n) m x y
LRs (lim f s) m (lim n r) x y = LRs (f n) m r x y

outR : ∀ {c m k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordˢ k} → LRs c m r z ẑ → Rs k m z ẑ
outR zero      l = l
outR (suc r)   l = outR r l
outR (self n)  l = l
outR (lim n r) l = outR r l

intoR : ∀ {c m k} (r : k ◃ c) {A ξ} {z : O A ξ} {ẑ : Ordˢ k} → Rs k m z ẑ → LRs c m r z ẑ
intoR zero      l = l
intoR (suc r)   l = intoR r l
intoR (self n)  l = l
intoR (lim n r) l = intoR r l

fr-of : ∀ {B m A π} {x : O A π} {ŷ : Ordˢ B} → Rs B m x ŷ → Rs B fr x ŷ
fr-of rz = rz
fr-of (rs a c r) = rs tt c (fr-of r)
fr-of (rl h) = rl (λ n → fr-of (h n))
fr-of (rwk r) = rwk (fr-of r)
fr-of (rcv r) = rcv (fr-of r)
fr-of (rmk r dk l iv m) = rmk r dk l iv m
fr-of (rΩ r cv q d h) = rΩ r cv q d (λ ξ em z ẑ l → fr-of (h ξ em z ẑ l))
fr-of (rŝ z ec rt rg) = rŝ z ec (fr-of rt) (λ η e e′ → fr-of (rg η e e′))
fr-of (rĉ ec dz dg ro rg) = rĉ ec dz dg (fr-of ro) (λ η e e′ → fr-of (rg η e e′))
fr-of (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ zb ec (fr-of rt) (λ η e e′ → fr-of (rg₀ η e e′)) (fr-of ro) (λ η e e′ → fr-of (rg η e e′))
```

## §2′ 第 0 层, 读成 `Z`

```agda
Rz : ∀ {m π} {y : O Lv.zero π} {ŷ : Ordˢ zero} → Rs zero m y ŷ → rdZ y ≲ᶻ toZ ŷ
Rz rz = zl
Rz (rs a c r) = sl (Rz r)
Rz (rl h) = ll (λ n → Rz (h n))
Rz (rwk {π = π′} {x = x} r) = Rz {π = π′} {y = x} r
Rz (rcv {π = π′} {x = x} r) = Rz {π = π′} {y = x} r
Rz (rmk () dk l iv m)
Rz (rΩ () cv q d h)
Rz (rŝ z ec rt rg) = ĉl ec (Rz rt) (λ η e e′ → Rz (rg η e e′)) (Rz rt) (λ η e e′ → Rz (rg η e e′))
Rz (rĉ ec dz dg ro rg) = ĉl ec dz dg (Rz ro) (λ η e e′ → Rz (rg η e e′))
Rz (rĉŝ tt ec rt rg₀ ro rg) = ĉl ec (Rz rt) (λ η e e′ → Rz (rg₀ η e e′)) (Rz ro) (λ η e e′ → Rz (rg η e e′))
```

## §3 加法

`W` 的地板有上界时才能写 `rs`: 折叠的 `os` 那一行给的是空地板 ([GuardCertFold](GuardCertFold.lagda.md)).

```agda
R-⊕ : ∀ {A φ ψ k ℓ m₁ m₂} {W : O A φ} {t : O A ψ} {Ŵ : Ordˢ ℓ} {σ : Simᴵ k ℓ} {t̂ : Ordˢ k} → ZZ A ℓ → FlrLe φ ℓ → Rs ℓ m₁ W Ŵ → Rs k m₂ t t̂ → Rs ℓ fr (W ⊕ t) (addˢ Ŵ σ t̂)
R-⊕ zz cW rW rz = rwk (fr-of rW)
R-⊕ {σ = σ} zz cW rW (rs a c r) = rs tt (le-∪ cW (le-Sim σ c)) (R-⊕ zz cW rW r)
R-⊕ zz cW rW (rl h) = rl (λ n → R-⊕ zz cW rW (h n))
R-⊕ zz cW rW (rwk r) = rwk (R-⊕ zz cW rW r)
R-⊕ zz cW rW (rcv r) = rcv (R-⊕ zz cW rW r)
R-⊕ zz cW rW (rmk zero dk l iv m) = R-⊕ zz cW rW m
R-⊕ zz cW rW (rmk (self n) dk l iv m) = R-⊕ zz cW rW m
R-⊕ {ℓ = ℓ} {Ŵ = Ŵ} {σ = σ} zz cW rW (rΩ r cv q {f = f} d h) =
  rΩ r _ (σ q) d (λ ξ em′ z ẑ l → rwk (subst (λ u → Rs ℓ fr (_ ⊕ _) (addˢ Ŵ σ (f (intoˢ (<→◃ q) u))))
                                         (sym (out-intoˢ (<→◃ (σ q)) ẑ))
                                         (R-⊕ zz cW rW (h ξ em′ z ẑ (intoR (<→◃ q) (outR (<→◃ (σ q)) l))))))
R-⊕ {A = Lv.zero} {k = zero} zz cW rW (rŝ tt ec rt rg) = rĉ ec (Rz rt) (λ η e e′ → Rz (rg η e e′)) (R-⊕ zz cW rW rt) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {A = Lv.suc _} {k = suc _} zz cW rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz cW rW rt) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {A = Lv.suc _} {k = lim _ _} zz cW rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz cW rW rt) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {A = Lv.lim _} {k = suc _} zz cW rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz cW rW rt) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {A = Lv.lim _} {k = lim _ _} zz cW rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz cW rW rt) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {A = Lv.lc _ _ _} {k = suc _} zz cW rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz cW rW rt) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {A = Lv.lc _ _ _} {k = lim _ _} zz cW rW (rŝ z ec rt rg) = rŝ zz ec (R-⊕ zz cW rW rt) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {A = Lv.zero} {k = suc _} zz cW rW (rŝ () ec rt rg)
R-⊕ {A = Lv.zero} {k = lim _ _} zz cW rW (rŝ () ec rt rg)
R-⊕ {A = Lv.suc _} {k = zero} zz cW rW (rŝ () ec rt rg)
R-⊕ {A = Lv.lim _} {k = zero} zz cW rW (rŝ () ec rt rg)
R-⊕ {A = Lv.lc _ _ _} {k = zero} zz cW rW (rŝ () ec rt rg)
R-⊕ zz cW rW (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-⊕ zz cW rW ro) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
R-⊕ {k = zero} zz cW rW (rĉŝ tt ec rt rg₀ ro rg) = rĉ ec (Rz rt) (λ η e e′ → Rz (rg₀ η e e′)) (R-⊕ zz cW rW ro) (λ η e e′ → R-⊕ zz cW rW (rg η e e′))
```

## §3′ 不变量过搬运

```agda
end-trC : ∀ {k a b ξ} (P : Cp k a) (e : a ≈ b) (z : Vc a P ξ) → EndS P → EndS (posC (trC P e z))
end-trC (Lv.suc Lv.self) (Lv.s≈ e) z es0 = es0
end-trC (Lv.suc P) (Lv.s≈ e) z (es-s h) with trC P e z | end-trC P e z h
... | restrC Q u z′ | h′ = es-s h′
end-trC (Lv.lim n P) (Lv.l≈ g) z (es-l h) with trC P (g n) z | end-trC P (g n) z h
... | restrC Q u z′ | h′ = es-l h′
end-trC (Lv.fst P) (Lv.o≈ d e g) z (es-f h) with trC P e z | end-trC P e z h
... | restrC Q u z′ | h′ = es-f h′
end-trC (Lv.bra η e₁ P) (Lv.o≈ d e g) z (es-b h) with trC P (g η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | end-trC P (g η e₁ η (conv d e₁) (≅ᴰ-refl η)) z h
... | restrC Q u z′ | h′ = es-b h′

end-tr⁻C : ∀ {k a b ξ} (P : Cp k b) (e : a ≈ b) (z : Vc b P ξ) → EndS P → EndS (posC (tr⁻C P e z))
end-tr⁻C (Lv.suc Lv.self) (Lv.s≈ e) z es0 = es0
end-tr⁻C (Lv.suc P) (Lv.s≈ e) z (es-s h) with tr⁻C P e z | end-tr⁻C P e z h
... | restrC Q u z′ | h′ = es-s h′
end-tr⁻C (Lv.lim n P) (Lv.l≈ g) z (es-l h) with tr⁻C P (g n) z | end-tr⁻C P (g n) z h
... | restrC Q u z′ | h′ = es-l h′
end-tr⁻C (Lv.fst P) (Lv.o≈ d e g) z (es-f h) with tr⁻C P e z | end-tr⁻C P e z h
... | restrC Q u z′ | h′ = es-f h′
end-tr⁻C (Lv.bra η e₁ P) (Lv.o≈ d e g) z (es-b h) with tr⁻C P (g η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | end-tr⁻C P (g η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z h
... | restrC Q u z′ | h′ = es-b h′

end-trV : ∀ {k a b ξ} (R : Strict k a) (e : a ≈ b) (z : Vs a R ξ) → EndS (stCp R) → EndS (stCp (posW (trV R e z)))
end-trV (st-suc Lv.self) (Lv.s≈ e) z es0 = es0
end-trV (st-suc P) (Lv.s≈ e) z (es-s h) with trC P e z | end-trC P e z h
... | restrC Q u z′ | h′ = es-s h′
end-trV (st-lim n P) (Lv.l≈ g) z (es-l h) with trC P (g n) z | end-trC P (g n) z h
... | restrC Q u z′ | h′ = es-l h′
end-trV (st-fst P) (Lv.o≈ d e g) z (es-f h) with trC P e z | end-trC P e z h
... | restrC Q u z′ | h′ = es-f h′
end-trV (st-bra η e₁ P) (Lv.o≈ d e g) z (es-b h) with trC P (g η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | end-trC P (g η e₁ η (conv d e₁) (≅ᴰ-refl η)) z h
... | restrC Q u z′ | h′ = es-b h′

end-tr⁻V : ∀ {k a b ξ} (R : Strict k b) (e : a ≈ b) (z : Vs b R ξ) → EndS (stCp R) → EndS (stCp (posW (tr⁻V R e z)))
end-tr⁻V (st-suc Lv.self) (Lv.s≈ e) z es0 = es0
end-tr⁻V (st-suc P) (Lv.s≈ e) z (es-s h) with tr⁻C P e z | end-tr⁻C P e z h
... | restrC Q u z′ | h′ = es-s h′
end-tr⁻V (st-lim n P) (Lv.l≈ g) z (es-l h) with tr⁻C P (g n) z | end-tr⁻C P (g n) z h
... | restrC Q u z′ | h′ = es-l h′
end-tr⁻V (st-fst P) (Lv.o≈ d e g) z (es-f h) with tr⁻C P e z | end-tr⁻C P e z h
... | restrC Q u z′ | h′ = es-f h′
end-tr⁻V (st-bra η e₁ P) (Lv.o≈ d e g) z (es-b h) with tr⁻C P (g η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | end-tr⁻C P (g η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z h
... | restrC Q u z′ | h′ = es-b h′

-- 节点模 ≈ 不变
trC-≈ : ∀ {k a b ξ j} (P : Cp k a) (e : a ≈ b) (z : Vc a P ξ) → k ≈ j → repC (trC P e z) ≈ j
trC-≈ Lv.self e z d = ≈-trans (≈-sym e) d
trC-≈ (Lv.suc P) (Lv.s≈ e) z d with trC P e z | trC-≈ P e z d
... | restrC Q u z′ | h = h
trC-≈ (Lv.lim n P) (Lv.l≈ g) z d with trC P (g n) z | trC-≈ P (g n) z d
... | restrC Q u z′ | h = h
trC-≈ (Lv.fst P) (Lv.o≈ c e g) z d with trC P e z | trC-≈ P e z d
... | restrC Q u z′ | h = h
trC-≈ (Lv.bra η e₁ P) (Lv.o≈ c e g) z d with trC P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) z | trC-≈ P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) z d
... | restrC Q u z′ | h = h

tr⁻C-≈ : ∀ {k a b ξ j} (P : Cp k b) (e : a ≈ b) (z : Vc b P ξ) → k ≈ j → repC (tr⁻C P e z) ≈ j
tr⁻C-≈ Lv.self e z d = ≈-trans e d
tr⁻C-≈ (Lv.suc P) (Lv.s≈ e) z d with tr⁻C P e z | tr⁻C-≈ P e z d
... | restrC Q u z′ | h = h
tr⁻C-≈ (Lv.lim n P) (Lv.l≈ g) z d with tr⁻C P (g n) z | tr⁻C-≈ P (g n) z d
... | restrC Q u z′ | h = h
tr⁻C-≈ (Lv.fst P) (Lv.o≈ c e g) z d with tr⁻C P e z | tr⁻C-≈ P e z d
... | restrC Q u z′ | h = h
tr⁻C-≈ (Lv.bra η e₁ P) (Lv.o≈ c e g) z d with tr⁻C P (g η (conv (≅ᴰ-sym c) e₁) η e₁ (≅ᴰ-refl η)) z | tr⁻C-≈ P (g η (conv (≅ᴰ-sym c) e₁) η e₁ (≅ᴰ-refl η)) z d
... | restrC Q u z′ | h = h

trV-≈ : ∀ {k a b ξ j} (R : Strict k a) (e : a ≈ b) (z : Vs a R ξ) → k ≈ j → repW (trV R e z) ≈ j
trV-≈ (st-suc P) (Lv.s≈ e) z d with trC P e z | trC-≈ P e z d
... | restrC Q u z′ | h = h
trV-≈ (st-lim n P) (Lv.l≈ g) z d with trC P (g n) z | trC-≈ P (g n) z d
... | restrC Q u z′ | h = h
trV-≈ (st-fst P) (Lv.o≈ c e g) z d with trC P e z | trC-≈ P e z d
... | restrC Q u z′ | h = h
trV-≈ (st-bra η e₁ P) (Lv.o≈ c e g) z d with trC P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) z | trC-≈ P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) z d
... | restrC Q u z′ | h = h

tr⁻V-≈ : ∀ {k a b ξ j} (R : Strict k b) (e : a ≈ b) (z : Vs b R ξ) → k ≈ j → repW (tr⁻V R e z) ≈ j
tr⁻V-≈ (st-suc P) (Lv.s≈ e) z d with tr⁻C P e z | tr⁻C-≈ P e z d
... | restrC Q u z′ | h = h
tr⁻V-≈ (st-lim n P) (Lv.l≈ g) z d with tr⁻C P (g n) z | tr⁻C-≈ P (g n) z d
... | restrC Q u z′ | h = h
tr⁻V-≈ (st-fst P) (Lv.o≈ c e g) z d with tr⁻C P e z | tr⁻C-≈ P e z d
... | restrC Q u z′ | h = h
tr⁻V-≈ (st-bra η e₁ P) (Lv.o≈ c e g) z d with tr⁻C P (g η (conv (≅ᴰ-sym c) e₁) η e₁ (≅ᴰ-refl η)) z | tr⁻C-≈ P (g η (conv (≅ᴰ-sym c) e₁) η e₁ (≅ᴰ-refl η)) z d
... | restrC Q u z′ | h = h

iv-trV : ∀ {k₁ a b ξ k} (R : Strict k₁ a) (e : a ≈ b) (z : Vs a R ξ) → InvS R k → InvS (posW (trV R e z)) k
iv-trV R e z (iE h) = iE (end-trV R e z h)
iv-trV R e z (iL n c) = iL (λ fb → n (fr≈⁻ fb e)) (le-adm (stCp (posW (trV R e z))) (trfW (trV R e z) (cov (pF (stCp R))) (admP (stCp R))) c)

iv-tr⁻V : ∀ {k₁ a b ξ k} (R : Strict k₁ b) (e : a ≈ b) (z : Vs b R ξ) → InvS R k → InvS (posW (tr⁻V R e z)) k
iv-tr⁻V R e z (iE h) = iE (end-tr⁻V R e z h)
iv-tr⁻V R e z (iL n c) = iL (λ fa → n (Fr≈ fa e)) (le-adm (stCp (posW (tr⁻V R e z))) (trfW (tr⁻V R e z) (cov (pF (stCp R))) (admP (stCp R))) c)

-- 沿 ≈ 或字面相等
end-mvC : ∀ {k a b} (P : Cp k a) (e : a ≈ b) → EndS P → EndS (posM (mvC {k} {a} {b} P e))
end-mvC (Lv.suc Lv.self) (Lv.s≈ e) es0 = es0
end-mvC (Lv.suc P) (Lv.s≈ e) (es-s h) with mvC P e | end-mvC P e h
... | mvc d Q t | h′ = es-s h′
end-mvC (Lv.lim n P) (Lv.l≈ g) (es-l h) with mvC P (g n) | end-mvC P (g n) h
... | mvc d Q t | h′ = es-l h′
end-mvC (Lv.fst P) (Lv.o≈ c e g) (es-f h) with mvC P e | end-mvC P e h
... | mvc d Q t | h′ = es-f h′
end-mvC (Lv.bra η e₁ P) (Lv.o≈ c e g) (es-b h) with mvC P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) | end-mvC P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) h
... | mvc d Q t | h′ = es-b h′

end-mvS : ∀ {k a b} (R : Strict k a) (e : a ≈ b) → EndS (stCp R) → EndS (stCp (posV (mvS {k} {a} {b} R e)))
end-mvS (st-suc Lv.self) (Lv.s≈ e) es0 = es0
end-mvS (st-suc P) (Lv.s≈ e) (es-s h) with mvC P e | end-mvC P e h
... | mvc d Q t | h′ = es-s h′
end-mvS (st-lim n P) (Lv.l≈ g) (es-l h) with mvC P (g n) | end-mvC P (g n) h
... | mvc d Q t | h′ = es-l h′
end-mvS (st-fst P) (Lv.o≈ c e g) (es-f h) with mvC P e | end-mvC P e h
... | mvc d Q t | h′ = es-f h′
end-mvS (st-bra η e₁ P) (Lv.o≈ c e g) (es-b h) with mvC P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) | end-mvC P (g η e₁ η (conv c e₁) (≅ᴰ-refl η)) h
... | mvc d Q t | h′ = es-b h′

iv-mvL : ∀ {k₁ a a′ k} (R : Strict k₁ a) (d : Lk a a′) → InvS R k → InvS (posV (mvL R d)) k
iv-mvL R (inj₂ refl) iv = iv
iv-mvL R (inj₁ e) (iE h) = iE (end-mvS R e h)
iv-mvL R (inj₁ e) (iL n c) = iL (λ fb → n (fr≈⁻ fb e)) (le-adm (stCp (posV (mvS R e))) (trfV (mvS R e) (cov (pF (stCp R))) (admP (stCp R))) c)
```

## §4 搬运

左边 (`trO`, `tr⁻O`): 对 `≈` 与推导字典序递归. 右边 (`trˢ`, `tr⁻ˢ`): 对 `≅ᴵ` 与推导字典序递归.

```agda
BkOK : ∀ {k a b} {r : k < a} → RestrO r b → Set
BkOK w = ∀ {B m ξ} {z : O (repO w) ξ} {ẑ : Ordˢ B} → Rs B m z ẑ → Rs B m (backO w z) ẑ

R-trO  : ∀ {B m A A′ π} (e : A ≈ A′) {x : O A π} {ŷ : Ordˢ B} → Rs B m x ŷ → Rs B m (trO e x) ŷ
R-tr⁻O : ∀ {B m A A′ π} (e : A ≈ A′) {x : O A′ π} {ŷ : Ordˢ B} → Rs B m x ŷ → Rs B m (tr⁻O e x) ŷ
R-bk   : ∀ {k A A′} (q : k < A) (e : A ≈ A′) → BkOK (resO q e)
R-bk⁻  : ∀ {k A A′} (q : k < A′) (e : A ≈ A′) → BkOK (res⁻O q e)
R-trC  : ∀ {B m k A A′ ξ} (P : Cp k A) (e : A ≈ A′) (z : Vc A P ξ) {ẑ : Ordˢ B} → Rs B m (outC P z) ẑ → Rs B m (outC (posC (trC P e z)) (valC (trC P e z))) ẑ
R-tr⁻C : ∀ {B m k A A′ ξ} (P : Cp k A′) (e : A ≈ A′) (z : Vc A′ P ξ) {ẑ : Ordˢ B} → Rs B m (outC P z) ẑ → Rs B m (outC (posC (tr⁻C P e z)) (valC (tr⁻C P e z))) ẑ
R-trV  : ∀ {B m k A A′ ξ} (R : Strict k A) (e : A ≈ A′) (z : Vs A R ξ) {ẑ : Ordˢ B} → Rs B m (outV R z) ẑ → Rs B m (outV (posW (trV R e z)) (valW (trV R e z))) ẑ
R-tr⁻V : ∀ {B m k A A′ ξ} (R : Strict k A′) (e : A ≈ A′) (z : Vs A′ R ξ) {ẑ : Ordˢ B} → Rs B m (outV R z) ẑ → Rs B m (outV (posW (tr⁻V R e z)) (valW (tr⁻V R e z))) ẑ

R-trO e rz = rz
R-trO e (rs a c r) = rs a c (R-trO e r)
R-trO e (rl h) = rl (λ n → R-trO e (h n))
R-trO e (rwk r) = rwk (R-trO e r)
R-trO e (rcv r) = rcv (R-trO e r)
R-trO e (rmk {R = R} {z = z} zero dk l iv r) with trV R e z | R-trV R e z l | iv-trV R e z iv | trV-≈ R e z dk
... | restrV R′ u z′ | l′ | iv′ | dk′ = rmk zero dk′ l′ iv′ (R-trO e r)
R-trO e (rmk {R = R} {z = z} (self n) dk l iv r) with trV R e z | R-trV R e z l | trV-≈ R e z dk
... | restrV R′ u z′ | l′ | dk′ = rmk (self n) dk′ l′ tt (R-trO e r)
R-trO {B = B} {m = m₀} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ (ltO (resO r e)) _ q (≈-trans (≈-sym (eqO (resO r e))) d)
     (λ ξ em′ z ẑ l → R-trO e (subst (λ u → Rs B m₀ (h₁ ξ (intoU r (backO (resO r e) u))) (f (intoˢ (<→◃ q) ẑ))) (sym (out-intoU (ltO (resO r e)) z))
                                     (h ξ em′ _ ẑ (intoR (<→◃ q) (R-bk r e (outR (<→◃ q) l))))))
R-trO e (rŝ z ec rt rg) = rŝ (zz-≈ e z) ec (R-trO e rt) (λ η d d′ → R-trO e (rg η d d′))
R-trO e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-trO e ro) (λ η d d′ → R-trO e (rg η d d′))
R-trO e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ zb ec rt rg₀ (R-trO e ro) (λ η d d′ → R-trO e (rg η d d′))

R-tr⁻O e rz = rz
R-tr⁻O e (rs a c r) = rs a c (R-tr⁻O e r)
R-tr⁻O e (rl h) = rl (λ n → R-tr⁻O e (h n))
R-tr⁻O e (rwk r) = rwk (R-tr⁻O e r)
R-tr⁻O e (rcv r) = rcv (R-tr⁻O e r)
R-tr⁻O e (rmk {R = R} {z = z} zero dk l iv r) with tr⁻V R e z | R-tr⁻V R e z l | iv-tr⁻V R e z iv | tr⁻V-≈ R e z dk
... | restrV R′ u z′ | l′ | iv′ | dk′ = rmk zero dk′ l′ iv′ (R-tr⁻O e r)
R-tr⁻O e (rmk {R = R} {z = z} (self n) dk l iv r) with tr⁻V R e z | R-tr⁻V R e z l | tr⁻V-≈ R e z dk
... | restrV R′ u z′ | l′ | dk′ = rmk (self n) dk′ l′ tt (R-tr⁻O e r)
R-tr⁻O {B = B} {m = m₀} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ (ltO (res⁻O r e)) _ q (≈-trans (≈-sym (eqO (res⁻O r e))) d)
     (λ ξ em′ z ẑ l → R-tr⁻O e (subst (λ u → Rs B m₀ (h₁ ξ (intoU r (backO (res⁻O r e) u))) (f (intoˢ (<→◃ q) ẑ))) (sym (out-intoU (ltO (res⁻O r e)) z))
                                      (h ξ em′ _ ẑ (intoR (<→◃ q) (R-bk⁻ r e (outR (<→◃ q) l))))))
R-tr⁻O e (rŝ z ec rt rg) = rŝ (zz-≈ (≈-sym e) z) ec (R-tr⁻O e rt) (λ η d d′ → R-tr⁻O e (rg η d d′))
R-tr⁻O e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-tr⁻O e ro) (λ η d d′ → R-tr⁻O e (rg η d d′))
R-tr⁻O e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ zb ec rt rg₀ (R-tr⁻O e ro) (λ η d d′ → R-tr⁻O e (rg η d d′))

R-bk Lv.zero (Lv.s≈ e) = R-tr⁻O e
R-bk (Lv.suc r) (Lv.s≈ e) with resO r e | R-bk r e
... | restrO d m t b | H = H
R-bk (Lv.lim n r) (Lv.l≈ h) with resO r (h n) | R-bk r (h n)
... | restrO d m t b | H = H
R-bk (Lv.fst r) (Lv.o≈ d′ e h) with resO r e | R-bk r e
... | restrO d m t b | H = H
R-bk (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with resO r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η)) | R-bk r (h η e₁ η (conv d′ e₁) (≅ᴰ-refl η))
... | restrO d m t b | H = H

R-bk⁻ Lv.zero (Lv.s≈ e) = R-trO e
R-bk⁻ (Lv.suc r) (Lv.s≈ e) with res⁻O r e | R-bk⁻ r e
... | restrO d m t b | H = H
R-bk⁻ (Lv.lim n r) (Lv.l≈ h) with res⁻O r (h n) | R-bk⁻ r (h n)
... | restrO d m t b | H = H
R-bk⁻ (Lv.fst r) (Lv.o≈ d′ e h) with res⁻O r e | R-bk⁻ r e
... | restrO d m t b | H = H
R-bk⁻ (Lv.bra η e₁ r) (Lv.o≈ d′ e h) with res⁻O r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η)) | R-bk⁻ r (h η (conv (≅ᴰ-sym d′) e₁) η e₁ (≅ᴰ-refl η))
... | restrO d m t b | H = H

R-trC Lv.self e z l = R-trO e l
R-trC (Lv.suc P) (Lv.s≈ e) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.lim n P) (Lv.l≈ h) z l with trC P (h n) z | R-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.fst P) (Lv.o≈ d e h) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trC (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | R-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-tr⁻C Lv.self e z l = R-tr⁻O e l
R-tr⁻C (Lv.suc P) (Lv.s≈ e) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | R-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻C (Lv.bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | R-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-trV (st-suc P) (Lv.s≈ e) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trV (st-lim n P) (Lv.l≈ h) z l with trC P (h n) z | R-trC P (h n) z l
... | restrC Q u z′ | l′ = l′
R-trV (st-fst P) (Lv.o≈ d e h) z l with trC P e z | R-trC P e z l
... | restrC Q u z′ | l′ = l′
R-trV (st-bra η e₁ P) (Lv.o≈ d e h) z l with trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z | R-trC P (h η e₁ η (conv d e₁) (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-tr⁻V (st-suc P) (Lv.s≈ e) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-lim n P) (Lv.l≈ h) z l with tr⁻C P (h n) z | R-tr⁻C P (h n) z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-fst P) (Lv.o≈ d e h) z l with tr⁻C P e z | R-tr⁻C P e z l
... | restrC Q u z′ | l′ = l′
R-tr⁻V (st-bra η e₁ P) (Lv.o≈ d e h) z l with tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z | R-tr⁻C P (h η (conv (≅ᴰ-sym d) e₁) η e₁ (≅ᴰ-refl η)) z l
... | restrC Q u z′ | l′ = l′

R-trL⁻ : ∀ {B m A A′ π} (d : Lk A A′) {x : O A′ π} {ŷ : Ordˢ B} → Rs B m x ŷ → Rs B m (trL⁻ d x) ŷ
R-trL⁻ (inj₁ e) r = R-tr⁻O e r
R-trL⁻ (inj₂ refl) r = r

R-trL : ∀ {B m A A′ π} (d : Lk A A′) {x : O A π} {ŷ : Ordˢ B} → Rs B m x ŷ → Rs B m (trL d x) ŷ
R-trL (inj₁ e) r = R-trO e r
R-trL (inj₂ refl) r = r
```

**右边.** `Ordˢ` 上的搬运.

```agda
R-trˢ  : ∀ {a b m A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordˢ a} → Rs a m x ŷ → Rs b m x (trˢ e ŷ)
R-tr⁻ˢ : ∀ {a b m A π} (e : a ≅ᴵ b) {x : O A π} {ŷ : Ordˢ b} → Rs b m x ŷ → Rs a m x (tr⁻ˢ e ŷ)
R-bkˢ  : ∀ {j a b m A ξ} (q : j <ᴵ a) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordˢ (repˢ (resˢ q e))} → Rs (repˢ (resˢ q e)) m z ẑ → Rs j m z (backˢ (resˢ q e) ẑ)
R-bk⁻ˢ : ∀ {j a b m A ξ} (q : j <ᴵ b) (e : a ≅ᴵ b) {z : O A ξ} {ẑ : Ordˢ (repˢ (res⁻ˢ q e))} → Rs (repˢ (res⁻ˢ q e)) m z ẑ → Rs j m z (backˢ (res⁻ˢ q e) ẑ)

R-trˢ e rz = rz
R-trˢ e (rs a c r) = rs (rc-≅ e a) (le-≅ e c) (R-trˢ e r)
R-trˢ e (rl h) = rl (λ n → R-trˢ e (h n))
R-trˢ e (rwk r) = rwk (R-trˢ e r)
R-trˢ e (rcv r) = rcv (R-trˢ e r)
R-trˢ (s≅ e) (rmk zero dk l iv r) = rmk zero (≈-trans dk (⌜≈⌝ e)) (R-trˢ e l) (iv-≅ e iv) (R-trˢ e r)
R-trˢ (l≅ h) (rmk (self n) dk l iv r) = rmk (self n) (≈-trans dk (⌜≈⌝ (h n))) (R-trˢ (h n) l) tt (R-trˢ (h n) r)
R-trˢ {b = b} {m = m₀} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (ltˢ (resˢ q e)) (≈-trans d (⌜≈⌝ (eqˢ (resˢ q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs b m₀ (h₁ ξ (intoU r z)) (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) u))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) ẑ))
                             (R-trˢ e (h ξ em′ z _ (intoR (<→◃ q) (R-bkˢ q e (outR (<→◃ (ltˢ (resˢ q e))) l))))))
R-trˢ e (rŝ z ec rt rg) = rŝ (zz-≅ e z) ec (R-trˢ e rt) (λ η d d′ → R-trˢ e (rg η d d′))
R-trˢ e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-trˢ e ro) (λ η d d′ → R-trˢ e (rg η d d′))
R-trˢ e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ (zb-≅ e zb) ec (R-trˢ e rt) (λ η d d′ → R-trˢ e (rg₀ η d d′)) (R-trˢ e ro) (λ η d d′ → R-trˢ e (rg η d d′))

R-tr⁻ˢ e rz = rz
R-tr⁻ˢ e (rs a c r) = rs (rc-≅ (≅ᴵ-sym e) a) (le-≅ (≅ᴵ-sym e) c) (R-tr⁻ˢ e r)
R-tr⁻ˢ e (rl h) = rl (λ n → R-tr⁻ˢ e (h n))
R-tr⁻ˢ e (rwk r) = rwk (R-tr⁻ˢ e r)
R-tr⁻ˢ e (rcv r) = rcv (R-tr⁻ˢ e r)
R-tr⁻ˢ (s≅ e) (rmk zero dk l iv r) = rmk zero (≈-trans dk (⌜≈⌝ (≅ᴵ-sym e))) (R-tr⁻ˢ e l) (iv-≅ (≅ᴵ-sym e) iv) (R-tr⁻ˢ e r)
R-tr⁻ˢ (l≅ h) (rmk (self n) dk l iv r) = rmk (self n) (≈-trans dk (⌜≈⌝ (≅ᴵ-sym (h n)))) (R-tr⁻ˢ (h n) l) tt (R-tr⁻ˢ (h n) r)
R-tr⁻ˢ {a = a} {m = m₀} e (rΩ r cv q {h = h₁} {f = f} d h) =
  rΩ r cv (ltˢ (res⁻ˢ q e)) (≈-trans d (⌜≈⌝ (eqˢ (res⁻ˢ q e))))
     (λ ξ em′ z ẑ l → subst (λ u → Rs a m₀ (h₁ ξ (intoU r z)) (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) u))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) ẑ))
                             (R-tr⁻ˢ e (h ξ em′ z _ (intoR (<→◃ q) (R-bk⁻ˢ q e (outR (<→◃ (ltˢ (res⁻ˢ q e))) l))))))
R-tr⁻ˢ e (rŝ z ec rt rg) = rŝ (zz-≅ (≅ᴵ-sym e) z) ec (R-tr⁻ˢ e rt) (λ η d d′ → R-tr⁻ˢ e (rg η d d′))
R-tr⁻ˢ e (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-tr⁻ˢ e ro) (λ η d d′ → R-tr⁻ˢ e (rg η d d′))
R-tr⁻ˢ e (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ (zb-≅ (≅ᴵ-sym e) zb) ec (R-tr⁻ˢ e rt) (λ η d d′ → R-tr⁻ˢ e (rg₀ η d d′)) (R-tr⁻ˢ e ro) (λ η d d′ → R-tr⁻ˢ e (rg η d d′))

R-bkˢ zero (s≅ e) l = R-tr⁻ˢ e l
R-bkˢ (suc q) (s≅ e) l = R-bkˢ q e l
R-bkˢ (lim n q) (l≅ h) l = R-bkˢ q (h n) l

R-bk⁻ˢ zero (s≅ e) l = R-trˢ e l
R-bk⁻ˢ (suc q) (s≅ e) l = R-bk⁻ˢ q e l
R-bk⁻ˢ (lim n q) (l≅ h) l = R-bk⁻ˢ q (h n) l
```

## §5 嵌入, $\dot\Omega$

`R-ι`: 嵌入不改对面的树. 要的是 `HPf`. 新的一件: 模式 `fr` 下 $P$ 的帧要 $\sqsubseteq B$ (`Hr`), 这样 `os` 的地板还有上界; 模式 `gd` 下只在 $B$ 是 0 时要.

```agda
Hr : Md → ∀ {a c} → Cp a c → Ordᴵ → Set
Hr fr P B = FlrLe (pF P) B
Hr gd P B = ZB B → FlrLe (pF P) B

hr-fr : ∀ {m a c} {P : Cp a c} {B} → Hr m P B → RsC m B → FlrLe (pF P) B
hr-fr {m = fr} h _ = h
hr-fr {m = gd} h z = h z

lk≈′ : ∀ {k rep j} → Lk k rep → k ≈ j → rep ≈ j
lk≈′ (inj₁ x) y = ≈-trans (≈-sym x) y
lk≈′ (inj₂ refl) y = y

BLOK : ∀ {k a b} {r : k < a} → RL r b → Set
BLOK w = ∀ {B m ξ} {z : O (repL w) ξ} {ẑ : Ordˢ B} → Rs B m z ẑ → Rs B m (backL w z) ẑ

R-bL : ∀ {k a b} (r : k < a) (d : Lk a b) → BLOK (resL r d)
R-bL r (inj₁ e) with resO r e | R-bk r e
... | restrO d′ l t b | H = H
R-bL r (inj₂ refl) = λ l → l

module EmbR (L : LG) (tc : Tc L) (HP : HPf L tc) where
  open Emb L tc

  ιC-eq : ∀ a {k ξ a′} (Q : Cp k a) (P : Cp a′ L) (d : Lk k a′) (z : Vc a Q ξ) → ιC a Q P d z ≡ ι k P d (outC Q z)
  ιC-eq a Lv.self P d z = refl
  ιC-eq (Lv.suc b) (Lv.suc Q) P d z = ιC-eq b Q P d z
  ιC-eq (Lv.lim f) (Lv.lim n Q) P d z = ιC-eq (f n) Q P d z
  ιC-eq (Lv.lc c t g) (Lv.fst Q) P d z = ιC-eq t Q P d z
  ιC-eq (Lv.lc c t g) (Lv.bra η e Q) P d z = ιC-eq (g η e) Q P d z

  ιV-eq : ∀ a {k ξ a′} (R : Strict k a) (P : Cp a′ L) (d : Lk k a′) (z : Vs a R ξ) → ιV a R P d z ≡ ι k P d (outV R z)
  ιV-eq (Lv.suc b) (st-suc Q) P d z = ιC-eq b Q P d z
  ιV-eq (Lv.lim f) (st-lim n Q) P d z = ιC-eq (f n) Q P d z
  ιV-eq (Lv.lc c t g) (st-fst Q) P d z = ιC-eq t Q P d z
  ιV-eq (Lv.lc c t g) (st-bra η e Q) P d z = ιC-eq (g η e) Q P d z

  R-ι : ∀ {B m a a′ π} (P : Cp a′ L) (d : Lk a a′) → Hr m P B → {z : O a π} {ŷ : Ordˢ B} → Rs B m z ŷ → Rs B m (ι a P d z) ŷ
  R-ι P d H rz = rz
  R-ι P d H (rs a₀ c r) = rs a₀ (le-∪ c (hr-fr H a₀)) (R-ι P d H r)
  R-ι P d H (rl h) = rl (λ n → R-ι P d H (h n))
  R-ι P d H (rwk r) = rwk (R-ι P d H r)
  R-ι P d H (rcv r) = rcv (R-ι P d H r)
  R-ι {B = suc k₀} {a = a} P d H (rmk {R = R} {z = z} zero dk l iv m) with mvL R d | iv-mvL R d iv
  ... | mvs e R′ u | iv′ with nfS L tc (st⊙ P R′) | proj₂ (HP P R′ (lk≈′ e dk)) iv′
  ...   | nfs e₂ pos t r′ | hv =
    rcv (rmk zero (lk≈′ e₂ (lk≈′ e dk)) (subst (λ w → Rs k₀ fr w _) (sym (out-intoV pos (trL (lkC e e₂) (outV R z)))) (R-trL (lkC e e₂) l))
             (proj₂ hv)
             (subst (λ w → Rs k₀ fr w _) (sym (ιV-eq a R (stCp pos) (lkC e e₂) z)) (R-ι (stCp pos) (lkC e e₂) (proj₁ hv) l)))
  R-ι {B = lim f₀ s₀} {a = a} P d H (rmk {R = R} {z = z} (self n) dk l iv m) with mvL R d
  ... | mvs e R′ u with nfS L tc (st⊙ P R′) | proj₁ (HP P R′ (lk≈′ e dk))
  ...   | nfs e₂ pos t r′ | hq =
    rcv (rmk (self n) (lk≈′ e₂ (lk≈′ e dk)) (subst (λ w → Rs (f₀ n) gd w _) (sym (out-intoV pos (trL (lkC e e₂) (outV R z)))) (R-trL (lkC e e₂) l))
             tt
             (subst (λ w → Rs (f₀ n) gd w _) (sym (ιV-eq a R (stCp pos) (lkC e e₂) z)) (R-ι (stCp pos) (lkC e e₂) hq l)))
  R-ι {B = B} {m = m₀} {a = a} P d H (rΩ {j = j} r cv q {h = h₁} {f = f} dk h) with resL r d | R-bL r d
  ... | rl e′ s u b | H′ =
    rΩ (P ◁ s) _ q (lk≈′ e′ dk)
       (λ ξ em′ z ẑ l → rwk (R-ι P d H (subst (λ w → Rs B m₀ (h₁ ξ (intoU r (b w))) (f (intoˢ (<→◃ q) ẑ))) (sym (cv-into P s z))
                                             (h ξ em′ (b z) ẑ (intoR (<→◃ q) (H′ (outR (<→◃ q) l)))))))
  R-ι {B = zero} {a = Lv.zero} P d H (rŝ z ec rt rg) = rĉŝ tt ec rt rg (R-ι P d H rt) (λ η e e′ → R-ι P d H (rg η e e′))
  R-ι {B = suc _} {a = Lv.zero} P d H (rŝ () ec rt rg)
  R-ι {B = lim _ _} {a = Lv.zero} P d H (rŝ () ec rt rg)
  R-ι {a = Lv.suc _} P d H (rŝ z ec rt rg) = rŝ (zz-cp₁ d z {tt} P) ec (R-ι P d H rt) (λ η e e′ → R-ι P d H (rg η e e′))
  R-ι {a = Lv.lim _} P d H (rŝ z ec rt rg) = rŝ (zz-cp₁ d z {tt} P) ec (R-ι P d H rt) (λ η e e′ → R-ι P d H (rg η e e′))
  R-ι {a = Lv.lc _ _ _} P d H (rŝ z ec rt rg) = rŝ (zz-cp₁ d z {tt} P) ec (R-ι P d H rt) (λ η e e′ → R-ι P d H (rg η e e′))
  R-ι P d H (rĉ ec dz dg ro rg) = rĉ ec dz dg (R-ι P d H ro) (λ η e e′ → R-ι P d H (rg η e e′))
  R-ι P d H (rĉŝ zb ec rt rg₀ ro rg) = rĉŝ zb ec rt rg₀ (R-ι P d H ro) (λ η e e′ → R-ι P d H (rg η e e′))
```

## §6 无闭包的层

```agda
nf-free-end : ∀ {k L} (h : FrL L) (tc : Tc L) (P : Cp k L) → EndS P → EndS (posN (nfC L tc P))
nf-free-end (fs′ h) tc (Lv.suc Lv.self) es0 = es0
nf-free-end (fs′ h) tc (Lv.suc P) (es-s e) with nfC _ tc P | nf-free-end h tc P e
... | nfc d Q t r | e′ = es-s e′
nf-free-end (fl h) tc (Lv.lim n P) (es-l e) with nfC _ (tc n) P | nf-free-end (h n) (tc n) P e
... | nfc d Q t r | e′ = es-l e′

nfS-free-end : ∀ {k L} (h : FrL L) (tc : Tc L) (R : Strict k L) → EndS (stCp R) → EndS (stCp (posS (nfS L tc R)))
nfS-free-end (fs′ h) tc (st-suc Lv.self) es0 = es0
nfS-free-end (fs′ h) tc (st-suc P) (es-s e) with nfC _ tc P | nf-free-end h tc P e
... | nfc d Q t r | e′ = es-s e′
nfS-free-end (fl h) tc (st-lim n P) (es-l e) with nfC _ (tc n) P | nf-free-end (h n) (tc n) P e
... | nfc d Q t r | e′ = es-l e′

hp-free : ∀ {L} (fL : FrL L) (tc : Tc L) → HPf L tc
hp-free {L} fL tc P R′ dk = (λ _ → le-emp (fr-emp fL (stCp pos))) , go
  where
  pos = posS (nfS L tc (st⊙ P R′))
  go : InvS R′ _ → _ × _
  go (iE h) = le-emp (fr-emp fL (stCp pos)) , iE (nfS-free-end fL tc (st⊙ P R′) (EndT R′ h P))
  go (iL n c) = ⊥-elim (n (fr-cp fL P))

RΩ̇ : ∀ i {t} → t ≈ ⌜ i ⌝ → (tc : Tc t) → Rs i gd (Ω̇ t tc) (Ωˢ i)
RΩ̇ zero Lv.z≈ tc = rs tt (λ _ ()) rz
RΩ̇ (suc b) {t = Lv.suc t′} (Lv.s≈ e) tc =
  rΩ Lv.zero tt zero e (λ ξ em′ z ẑ l →
    rmk zero e l (iE es0)
        (EmbR.R-ι (Lv.suc t′) tc (hp-free (fs′ (Fr≈ (FrG b) (≈-sym e))) tc) (Lv.suc Lv.self) (inj₂ refl) (λ _ ()) l))
RΩ̇ (lim g s) {t = Lv.lim f′} (Lv.l≈ h) tc =
  rl (λ n → rwk (rmk (self n) (h n) (RΩ̇ (g n) (h n) (tc n)) tt
                    (EmbR.R-ι (Lv.lim f′) tc (hp-free (fl (λ m → Fr≈ (FrG (g m)) (≈-sym (h m)))) tc) (Lv.lim n Lv.self) (inj₂ refl) (λ _ _ ()) (RΩ̇ (g n) (h n) (tc n)))))
```
