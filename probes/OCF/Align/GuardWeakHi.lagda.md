# 证书 (二): 第一个闭包所在的层, 对 [OCF.Free.Tree](../Free/Tree.lagda.md) 的 `O`

> 不含记号. 结论写在 [GuardWeak](GuardWeak.lagda.md). `Rc fl x y`: 左边 $x$ 是 [GuardWeakTree](GuardWeakTree.lagda.md) 的树 (层 $c_1=\Omega$ 或 $c_1+1$), 右边 $y$ 是 `FT.O`. 与 `Rs` 同形, 多闭包 `ccl`. 闭包带 `CvL π φ`: 左边地板的每个帧的值都被右边的地板 $\varphi$ 盖住, 这就是证书要的 "$c\sqsubseteq$ 对面的界" 的来源.
>
> `fl`: `pre` 是嵌入之前 (层 $c_1$), `post` 是嵌入之后 (层 $c_1+1$). `cm₀` 把 $z$ 的嵌入的结果存下来, 所以 `ι-Rc` 不用看 $z$.
>
> `_≃_`: 右边的结合律. 左边的 `repᵒ` 右结合, `FT.ψᵒ` 的 `repᵒ` 左结合. `T`: 关系沿 `≃` 搬运.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardWeakHi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.GuardTightCum hiding (ψ; _+_)
open import OCF.Free.Prefix using (Z; toZ; Ordˢ; Ord₊ˢ; Uˢ; outˢ; intoˢ; Ωˢ)
open Ord₊ˢ
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; flo; cvFlo; toFlo)
import OCF.Free.Tree as FT
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; zl; sl; ll; ĉl)
open import OCF.Align.GuardTightLv
open Lv Dom₀ hiding (zero; suc; lim)
open import OCF.Align.GuardTightBase
open import OCF.Align.GuardTightTab Dom₀ using (Strict; stCp)
open import OCF.Align.GuardTightTree
open import OCF.Align.GuardWeakRel
open import OCF.Align.GuardTightCert using (c₁)
open import OCF.Align.GuardWeakRd using (Tc-Ω₁)

one : Ordᴵ
one = suc zero

G₁ : (η : Ordᴵ) → one ⊑ᴵ η → LG
G₁ η _ = ⌜ η ⌝

cT : LG
cT = Lv.suc c₁

tcʷ : Tc cT
tcʷ = Tc-Ω₁

ι₁ : ∀ {π} → O c₁ π → O cT (π ∪ tz)
ι₁ = Emb.ι cT tcʷ c₁ (Lv.suc Lv.self) (inj₂ refl)

Fr₁ : (η : Ordᴵ) → one ⊑ᴵ η → Frm
Fr₁ η e = frm one ⌜ one ⌝ G₁ η e

CvL : Fl → Flr → Set
CvL π φ = ∀ {f} → Mem π f → ∀ {ℓ} → Ev ℓ φ → Simᴵ (fη f) ℓ

data Fg : Set where
  pre post : Fg

-- 按标记定层: 不把 c₁ 放进下标 (模式匹配要消去函数的等式, 没有 K 不行)
Lvl : Fg → LG
Lvl pre = c₁
Lvl post = cT

Pk : ∀ fl → Cp c₁ (Lvl fl)
Pk pre = Lv.self
Pk post = Lv.suc Lv.self

data Rc : (fl : Fg) → ∀ {π B φ} → O (Lvl fl) π → FT.O B φ → Set where
  cz  : ∀ {fl π B φ} → Rc fl {π} {B} {φ} o0 FT.o0
  cs  : ∀ {fl π B φ} {x : O (Lvl fl) π} {y : FT.O B φ} → Rc fl x y → Rc fl (os x) (FT.os y)
  cl  : ∀ {fl π B φ} {F : ℕ → O (Lvl fl) π} {H : ℕ → FT.O B φ} → (∀ n → Rc fl (F n) (H n)) → Rc fl (ol F) (FT.ol H)
  cwl : ∀ {fl π ρ B φ} {w : Wk π ρ} {x : O (Lvl fl) π} {y : FT.O B φ} → Rc fl x y → Rc fl (owk w x) y
  cvl : ∀ {fl π ρ B φ} {w : Cov π ρ} {x : O (Lvl fl) π} {y : FT.O B φ} → Rc fl x y → Rc fl (ocv w x) y
  cwr : ∀ {fl π B φ ψ} {le : ∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ} {x : O (Lvl fl) π} {y : FT.O B φ} → Rc fl x y → Rc fl x (FT.owk le y)
  cmp : ∀ {π ξ k B φ} {R : Strict k cT} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs cT R ξ} {x : O cT π} {y : FT.O B φ} →
        Rc post x y → Rc post (omk R lk ad z x) y
  cm₀ : ∀ {π ξ k φ} {R : Strict k c₁} {lk : Wk ξ π} {ad : AdmC (cov π) (stCp R)} {z : Vs c₁ R ξ} {x : O c₁ π} {y : FT.O zero φ} →
        Rc post (ι₁ (omk R lk ad z x)) (FT.ι {zero} {suc zero} zero y) → Rc pre x y → Rc pre (omk R lk ad z x) y
  ci  : ∀ {fl π B φ k j} (r : k < Lvl fl) {cv : Adm (cov π) r} {ac : ∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ} {h : ∀ ξ → Us (Lvl fl) r ξ → O (Lvl fl) (ξ ∪ π)} {f : Ordˢ j → FT.O B φ} →
        k ≈ ⌜ j ⌝ → (∀ ξ → Emp ξ → (z : O k ξ) (ẑ : Ordˢ j) → Rs j z ẑ → Rc fl (h ξ (intoU r z)) (f ẑ)) → Rc fl (oΩ r cv h) (FT.oi ac f)
  cŝ  : ∀ {fl π B φ c₀ c′} {t : O (Lvl fl) π} {g : ∀ η → c₀ ⊑ᴵ η → O (Lvl fl) π} {t̂ : FT.O B φ} {ĝ : ∀ η → c′ ⊑ᴵ η → FT.O B φ} →
        c₀ ⊑ᴵ c′ → Rc fl t t̂ → (∀ η e e′ → Rc fl (g η e) (ĝ η e′)) → Rc fl (oŝ c₀ t g) (FT.oŝ c′ t̂ ĝ)
  cĉ  : ∀ {fl π B φ c₀ c′ z ẑ} {zg : ∀ η → c₀ ⊑ᴵ η → Z} {ẑg : ∀ η → c′ ⊑ᴵ η → Z} {o₀ : O (Lvl fl) π} {o : ∀ η → c₀ ⊑ᴵ η → O (Lvl fl) π} {ô₀ : FT.O B φ} {ô : ∀ η → c′ ⊑ᴵ η → FT.O B φ} →
        c₀ ⊑ᴵ c′ → z ≲ᶻ ẑ → (∀ η e e′ → zg η e ≲ᶻ ẑg η e′) → Rc fl o₀ ô₀ → (∀ η e e′ → Rc fl (o η e) (ô η e′)) → Rc fl (oĉ c₀ z zg o₀ o) (FT.oĉ c′ ẑ ẑg ô₀ ô)
  ccl : ∀ {fl π B φ} {ad : AdmC (cov π) (Pk fl)} {t : O (Lvl fl) π} {g : ∀ η e → O (Lvl fl) (π ∪ tk (Fr₁ η e))}
          {t̂ : FT.O B (φ ⊔ fk zero)} {ĝ : ∀ η → FT.O B (φ ⊔ fk η)} →
        CvL π φ → Rc fl t t̂ → (∀ η e → Rc fl (g η e) (ĝ η)) → Rc fl (ocl {c₁ = one} {⌜ one ⌝} {G₁} (Pk fl) (inj₂ refl) ad t g) (FT.oclo t̂ ĝ)
```

## §1 从 `Rs`

```agda
module RsT where
  open EmbR cT tcʷ

  fromRsP : ∀ {k₀ π φ} {x : O cT π} {ŷ : Ordˢ k₀} (cv : ∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) → Rs k₀ x ŷ →
            Rc post x (FT.ι {zero} {suc zero} zero (FT.tl {c = zero} φ cv ŷ))
  fromRsP cv rz = cz
  fromRsP cv (rs r) = cs (fromRsP cv r)
  fromRsP cv (rl h) = cl (λ n → fromRsP cv (h n))
  fromRsP cv (rwk r) = cwl (fromRsP cv r)
  fromRsP cv (rcv r) = cvl (fromRsP cv r)
  fromRsP cv (rmk r′ l r) = cmp (fromRsP cv r)
  fromRsP {k₀ = suc k′} cv (rup zero l) = cwr (fromRsP (cvFlo k′) l)
  fromRsP {k₀ = lim g s} cv (rup (self n) l) = cwr (fromRsP (cvFlo (g n)) l)
  fromRsP cv (rΩ r _ q dk prem) = ci r dk (λ ξ em z ẑ l → fromRsP cv (prem ξ em z ẑ (intoR (<→◃ q) l)))
  fromRsP {k₀ = suc _} cv (rŝ z ec rt rg) = cŝ ec (fromRsP cv rt) (λ η e e′ → fromRsP cv (rg η e e′))
  fromRsP {k₀ = lim _ _} cv (rŝ z ec rt rg) = cŝ ec (fromRsP cv rt) (λ η e e′ → fromRsP cv (rg η e e′))
  fromRsP {k₀ = zero} cv (rŝ () ec rt rg)
  fromRsP cv (rĉ ec dz dg ro rg) = cĉ ec dz dg (fromRsP cv ro) (λ η e e′ → fromRsP cv (rg η e e′))
  fromRsP {k₀ = zero} cv (rĉŝ tt ec rt rg₀ ro rg) = cĉ ec (Rz rt) (λ η e e′ → Rz (rg₀ η e e′)) (fromRsP cv ro) (λ η e e′ → fromRsP cv (rg η e e′))

  R-ι₁ : ∀ {B π} {z : O c₁ π} {ŷ : Ordˢ B} → Rs B z ŷ → Rs B (ι₁ z) ŷ
  R-ι₁ = R-ι (Lv.suc Lv.self) (inj₂ refl)

  fromRs : ∀ {k₀ π φ} {x : O c₁ π} {ŷ : Ordˢ k₀} (cv : ∀ {ℓ} → Ev ℓ φ → Simᴵ k₀ ℓ) → Rs k₀ x ŷ → Rc pre x (FT.tl {c = zero} φ cv ŷ)
  fromRs cv rz = cz
  fromRs cv (rs r) = cs (fromRs cv r)
  fromRs cv (rl h) = cl (λ n → fromRs cv (h n))
  fromRs cv (rwk r) = cwl (fromRs cv r)
  fromRs cv (rcv r) = cvl (fromRs cv r)
  fromRs cv (rmk r′ l r) = cm₀ (fromRsP cv (R-ι₁ (rmk r′ l r))) (fromRs cv r)
  fromRs {k₀ = suc k′} cv (rup zero l) = cwr (fromRs (cvFlo k′) l)
  fromRs {k₀ = lim g s} cv (rup (self n) l) = cwr (fromRs (cvFlo (g n)) l)
  fromRs cv (rΩ r _ q dk prem) = ci r dk (λ ξ em z ẑ l → fromRs cv (prem ξ em z ẑ (intoR (<→◃ q) l)))
  fromRs {k₀ = suc _} cv (rŝ z ec rt rg) = cŝ ec (fromRs cv rt) (λ η e e′ → fromRs cv (rg η e e′))
  fromRs {k₀ = lim _ _} cv (rŝ z ec rt rg) = cŝ ec (fromRs cv rt) (λ η e e′ → fromRs cv (rg η e e′))
  fromRs {k₀ = zero} cv (rŝ () ec rt rg)
  fromRs cv (rĉ ec dz dg ro rg) = cĉ ec dz dg (fromRs cv ro) (λ η e e′ → fromRs cv (rg η e e′))
  fromRs {k₀ = zero} cv (rĉŝ tt ec rt rg₀ ro rg) = cĉ ec (Rz rt) (λ η e e′ → Rz (rg₀ η e e′)) (fromRs cv ro) (λ η e e′ → fromRs cv (rg η e e′))

open RsT public
```

## §2 嵌入

```agda
cvL-tz : ∀ {π φ} → CvL π φ → CvL (π ∪ tz) φ
cvL-tz c (ml m) = c m
cvL-tz c (mr ())

ι-Rc : ∀ {π φ} {x : O c₁ π} {y : FT.O zero φ} → Rc pre x y → Rc post (ι₁ x) (FT.ι {zero} {suc zero} zero y)
ι-Rc cz = cz
ι-Rc (cs r) = cs (ι-Rc r)
ι-Rc (cl h) = cl (λ n → ι-Rc (h n))
ι-Rc (cwl r) = cwl (ι-Rc r)
ι-Rc (cvl r) = cvl (ι-Rc r)
ι-Rc (cwr r) = cwr (ι-Rc r)
ι-Rc (cm₀ d r) = d
ι-Rc {π = π} (ci {k = k} {j = j} r {h = h} {f = f} dk prem) =
  ci (Lv.suc Lv.self ◁ r) dk (λ ξ em z ẑ l →
    cwl (ι-Rc (subst (λ w → Rc pre (h ξ (intoU r w)) (f ẑ)) (sym (cv-into (Lv.suc Lv.self) r z)) (prem ξ em z ẑ l))))
ι-Rc (cŝ ec rt rg) = cŝ ec (ι-Rc rt) (λ η e e′ → ι-Rc (rg η e e′))
ι-Rc (cĉ ec dz dg ro rg) = cĉ ec dz dg (ι-Rc ro) (λ η e e′ → ι-Rc (rg η e e′))
ι-Rc (ccl cv rt rg) = ccl (cvL-tz cv) (ι-Rc rt) (λ η e → cwl (ι-Rc (rg η e)))
```

## §3 $\dot\Omega$

```agda
RΩ̇₀ : Rc pre (Ω̇ c₁ tcʷ) (FT.Ω̇ zero)
RΩ̇₀ = ccl (λ ()) (cwl (fromRs proj₂ (EmbR.R-ι c₁ tcʷ (Lv.fst Lv.self) (inj₂ refl) (RΩ̇ one (⌜≈⌝ (≅ᴵ-refl one)) (proj₁ (proj₂ tcʷ))))))
                     (λ η e → cwl (fromRs (λ e₁ q → proj₂ e₁ (suc q)) (EmbR.R-ι c₁ tcʷ (Lv.bra η e Lv.self) (inj₂ refl) (RΩ̇ η (⌜≈⌝ (≅ᴵ-refl η)) (proj₂ (proj₂ tcʷ) η e)))))
```

## §4 加法

```agda
cvL-∪ : ∀ {π ρ φ ψ} → CvL π φ → CvL ρ ψ → CvL (π ∪ ρ) (φ ⊔ ψ)
cvL-∪ a b (ml m) e = a m (proj₁ e)
cvL-∪ a b (mr m) e = b m (proj₂ e)

R⊕ : ∀ {φW φ̂W π φ} {W : O c₁ φW} {Ŵ : FT.O zero φ̂W} {t : O c₁ π} {t̂ : FT.O zero φ} → CvL φW φ̂W → Rc pre W Ŵ → Rc pre t t̂ → Rc pre (W ⊕ t) (Ŵ FT.⊕ t̂)
R⊕ cW rW cz = cwl (cwr rW)
R⊕ cW rW (cs r) = cs (R⊕ cW rW r)
R⊕ cW rW (cl h) = cl (λ n → R⊕ cW rW (h n))
R⊕ cW rW (cwl r) = cwl (R⊕ cW rW r)
R⊕ cW rW (cvl r) = cvl (R⊕ cW rW r)
R⊕ cW rW (cwr r) = cwr (R⊕ cW rW r)
R⊕ cW rW (cm₀ {x = x} d r) = R⊕ {t = x} cW rW r
R⊕ cW rW (ci r dk prem) = ci r dk (λ ξ em z ẑ l → cwl (R⊕ cW rW (prem ξ em z ẑ l)))
R⊕ cW rW (cŝ ec rt rg) = cŝ ec (R⊕ cW rW rt) (λ η e e′ → R⊕ cW rW (rg η e e′))
R⊕ cW rW (cĉ ec dz dg ro rg) = cĉ ec dz dg (R⊕ cW rW ro) (λ η e e′ → R⊕ cW rW (rg η e e′))
R⊕ cW rW (ccl cv rt rg) = cwr (ccl (cvL-∪ cW cv) (cwr (R⊕ cW rW rt)) (λ η e → cwl (cwr (R⊕ cW rW (rg η e)))))
```

## §5 右边的结合律

```agda
infix 4 _≃_
data _≃_ {B : Ordᴵ} : ∀ {φ φ′} → FT.O B φ → FT.O B φ′ → Set where
  ≃id : ∀ {φ} {y : FT.O B φ} → y ≃ y
  ≃z  : ∀ {φ φ′} → FT.o0 {φ = φ} ≃ FT.o0 {φ = φ′}
  ≃s  : ∀ {φ φ′} {y : FT.O B φ} {y′ : FT.O B φ′} → y ≃ y′ → FT.os y ≃ FT.os y′
  ≃l  : ∀ {φ φ′} {H : ℕ → FT.O B φ} {H′ : ℕ → FT.O B φ′} → (∀ n → H n ≃ H′ n) → FT.ol H ≃ FT.ol H′
  ≃i  : ∀ {φ φ′ j} {ac : ∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ} {ac′ : ∀ {ℓ} → Ev ℓ φ′ → j <ᴵ ℓ} {f : Ordˢ j → FT.O B φ} {f′ : Ordˢ j → FT.O B φ′} →
        (∀ x → f x ≃ f′ x) → FT.oi ac f ≃ FT.oi ac′ f′
  ≃ŝ  : ∀ {φ φ′ c₀} {t : FT.O B φ} {t′ : FT.O B φ′} {g : ∀ η → c₀ ⊑ᴵ η → FT.O B φ} {g′ : ∀ η → c₀ ⊑ᴵ η → FT.O B φ′} →
        t ≃ t′ → (∀ η e → g η e ≃ g′ η e) → FT.oŝ c₀ t g ≃ FT.oŝ c₀ t′ g′
  ≃ĉ  : ∀ {φ φ′ c₀ z zg} {t : FT.O B φ} {t′ : FT.O B φ′} {g : ∀ η → c₀ ⊑ᴵ η → FT.O B φ} {g′ : ∀ η → c₀ ⊑ᴵ η → FT.O B φ′} →
        t ≃ t′ → (∀ η e → g η e ≃ g′ η e) → FT.oĉ c₀ z zg t g ≃ FT.oĉ c₀ z zg t′ g′
  ≃c  : ∀ {φ φ′} {t : FT.O B (φ ⊔ fk zero)} {t′ : FT.O B (φ′ ⊔ fk zero)} {g : ∀ η → FT.O B (φ ⊔ fk η)} {g′ : ∀ η → FT.O B (φ′ ⊔ fk η)} →
        (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → t ≃ t′ → (∀ η → g η ≃ g′ η) → FT.oclo t g ≃ FT.oclo t′ g′
  ≃wl : ∀ {φ φ₀ φ′} {le : ∀ {ℓ} → Ev ℓ φ → Ev ℓ φ₀} {y : FT.O B φ₀} {y′ : FT.O B φ′} → y ≃ y′ → FT.owk le y ≃ y′
  ≃wr : ∀ {φ φ₀ φ′} {le : ∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ₀} {y : FT.O B φ} {y′ : FT.O B φ₀} → y ≃ y′ → y ≃ FT.owk le y′

≃-ι : ∀ {φ φ′} {y : FT.O zero φ} {y′ : FT.O zero φ′} → y ≃ y′ → FT.ι {zero} {suc zero} zero y ≃ FT.ι {zero} {suc zero} zero y′
≃-ι ≃id = ≃id
≃-ι ≃z = ≃z
≃-ι (≃s e) = ≃s (≃-ι e)
≃-ι (≃l h) = ≃l (λ n → ≃-ι (h n))
≃-ι (≃i h) = ≃i (λ x → ≃-ι (h x))
≃-ι (≃ŝ e h) = ≃ŝ (≃-ι e) (λ η d → ≃-ι (h η d))
≃-ι (≃ĉ e h) = ≃ĉ (≃-ι e) (λ η d → ≃-ι (h η d))
≃-ι (≃c f e h) = ≃c f (≃-ι e) (λ η → ≃-ι (h η))
≃-ι (≃wl e) = ≃wl (≃-ι e)
≃-ι (≃wr e) = ≃wr (≃-ι e)

Tᴿ : ∀ {fl π B φ φ′} {x : O (Lvl fl) π} {y : FT.O B φ} {y′ : FT.O B φ′} → Rc fl x y → y ≃ y′ → Rc fl x y′
Tᴿ D ≃id = D
Tᴿ D (≃wr E) = cwr (Tᴿ D E)
Tᴿ (cwl D) E = cwl (Tᴿ D E)
Tᴿ (cvl D) E = cvl (Tᴿ D E)
Tᴿ (cmp D) E = cmp (Tᴿ D E)
Tᴿ (cm₀ d D) E = cm₀ (Tᴿ d (≃-ι E)) (Tᴿ D E)
Tᴿ (cwr D) (≃wl E) = Tᴿ D E
Tᴿ cz ≃z = cz
Tᴿ (cs D) (≃s E) = cs (Tᴿ D E)
Tᴿ (cl h) (≃l H) = cl (λ n → Tᴿ (h n) (H n))
Tᴿ (ci r dk prem) (≃i H) = ci r dk (λ ξ em z ẑ l → Tᴿ (prem ξ em z ẑ l) (H ẑ))
Tᴿ (cŝ ec rt rg) (≃ŝ E H) = cŝ ec (Tᴿ rt E) (λ η e e′ → Tᴿ (rg η e e′) (H η e′))
Tᴿ (cĉ ec dz dg ro rg) (≃ĉ E H) = cĉ ec dz dg (Tᴿ ro E) (λ η e e′ → Tᴿ (rg η e e′) (H η e′))
Tᴿ (ccl cv rt rg) (≃c f E H) = ccl (λ m e → cv m (f e)) (Tᴿ rt E) (λ η e → Tᴿ (rg η e) (H η))

≃⊕l : ∀ {φa φa′ φ} {a : FT.O zero φa} {a′ : FT.O zero φa′} (c : FT.O zero φ) → (∀ {ℓ} → Ev ℓ φa′ → Ev ℓ φa) → a ≃ a′ → (a FT.⊕ c) ≃ (a′ FT.⊕ c)
≃⊕l FT.o0 m E = ≃wl (≃wr E)
≃⊕l (FT.os c) m E = ≃s (≃⊕l c m E)
≃⊕l (FT.ol F) m E = ≃l (λ n → ≃⊕l (F n) m E)
≃⊕l (FT.oi ac f) m E = ≃i (λ x → ≃⊕l (f x) m E)
≃⊕l (FT.oŝ c₀ t g) m E = ≃ŝ (≃⊕l t m E) (λ η d → ≃⊕l (g η d) m E)
≃⊕l (FT.oĉ c₀ z zg o₀ o) m E = ≃ĉ (≃⊕l o₀ m E) (λ η d → ≃⊕l (o η d) m E)
≃⊕l (FT.oclo t g) m E = ≃wl (≃wr (≃c (λ e → m (proj₁ e) , proj₂ e) (≃wl (≃wr (≃⊕l t m E))) (λ η → ≃wl (≃wr (≃⊕l (g η) m E)))))
≃⊕l (FT.owk le c) m E = ≃wl (≃wr (≃⊕l c m E))
≃⊕l (FT.oΩ fe () h) m E

≃as : ∀ {φa φb φ} (a : FT.O zero φa) (b : FT.O zero φb) (c : FT.O zero φ) → (a FT.⊕ (b FT.⊕ c)) ≃ ((a FT.⊕ b) FT.⊕ c)
≃as a b FT.o0 = ≃wl (≃wr ≃id)
≃as a b (FT.os c) = ≃s (≃as a b c)
≃as a b (FT.ol F) = ≃l (λ n → ≃as a b (F n))
≃as a b (FT.oi ac f) = ≃i (λ x → ≃as a b (f x))
≃as a b (FT.oŝ c₀ t g) = ≃ŝ (≃as a b t) (λ η d → ≃as a b (g η d))
≃as a b (FT.oĉ c₀ z zg o₀ o) = ≃ĉ (≃as a b o₀) (λ η d → ≃as a b (o η d))
≃as a b (FT.oclo t g) =
  ≃wl (≃wl (≃wr (≃c (λ { ((u , v) , w) → u , (v , w) }) (≃wl (≃wl (≃wr (≃as a b t)))) (λ η → ≃wl (≃wl (≃wr (≃as a b (g η))))))))
≃as a b (FT.owk le c) = ≃wl (≃wr (≃as a b c))
≃as a b (FT.oΩ fe () h)

≃-trans : ∀ {B φ φ′ φ″} {x : FT.O B φ} {y : FT.O B φ′} {w : FT.O B φ″} → x ≃ y → y ≃ w → x ≃ w
≃-trans ≃id E = E
≃-trans E ≃id = E
≃-trans (≃wl E) E′ = ≃wl (≃-trans E E′)
≃-trans E (≃wr E′) = ≃wr (≃-trans E E′)
≃-trans (≃wr E) (≃wl E′) = ≃-trans E E′
≃-trans ≃z ≃z = ≃z
≃-trans (≃s E) (≃s E′) = ≃s (≃-trans E E′)
≃-trans (≃l H) (≃l H′) = ≃l (λ n → ≃-trans (H n) (H′ n))
≃-trans (≃i H) (≃i H′) = ≃i (λ x → ≃-trans (H x) (H′ x))
≃-trans (≃ŝ E H) (≃ŝ E′ H′) = ≃ŝ (≃-trans E E′) (λ η d → ≃-trans (H η d) (H′ η d))
≃-trans (≃ĉ E H) (≃ĉ E′ H′) = ≃ĉ (≃-trans E E′) (λ η d → ≃-trans (H η d) (H′ η d))
≃-trans (≃c f E H) (≃c f′ E′ H′) = ≃c (λ e → f (f′ e)) (≃-trans E E′) (λ η → ≃-trans (H η) (H′ η))

-- ŷ ⊕ rep n ≃ rep (n+1)
rep≃ : ∀ {φ} (ŷ : FT.O zero φ) n → (ŷ FT.⊕ FT.repᵒ ŷ n) ≃ FT.repᵒ ŷ (suc n)
rep≃ ŷ zero = ≃wl ≃id
rep≃ ŷ (suc zero) = ≃wr ≃id
rep≃ ŷ (suc (suc n)) = ≃wl (≃wr (≃-trans (≃as ŷ (FT.repᵒ ŷ (suc n)) ŷ) (≃⊕l ŷ (λ e → e , e) (rep≃ ŷ (suc n)))))

rep-Rc : ∀ {ρ φ} {y : O c₁ ρ} {ŷ : FT.O zero φ} → CvL ρ φ → Rc pre y ŷ → ∀ n → Rc pre (repᵒ y n) (FT.repᵒ ŷ n)
rep-Rc c r zero = cz
rep-Rc c r (suc zero) = cwl (cwl r)
rep-Rc {ŷ = ŷ} c r (suc (suc n)) = cwl (Tᴿ (R⊕ c r (rep-Rc c r (suc n))) (rep≃ ŷ (suc n)))
```
