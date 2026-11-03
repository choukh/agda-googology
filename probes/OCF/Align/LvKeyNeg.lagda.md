# 自然数标签的断点: 编译的否定

> 不含记号. 结论写在 [LvKey](LvKey.lagda.md). 对象是**旧**树 [UniformLvTree](UniformLvTree.lagda.md) 与它的标签. `noTimes`: $\psi_1(1)+\Omega$ 上外层标签 1 与内层 $\Omega\cdot2$ 相撞, 不能对一切 $K$ 有证书. `noNest`: 对任何标签 $h$, 嵌套同标签就如此. `noTag`: 把嵌套的节点分开的自然数标签推出 WLPO. 注意 `Clo K` 用树自己的 `ι (db K) o0 ⊕` 造出, 不是从 `T₀` 走到的; 走到的版本是 [LvCertNeg](LvCertNeg.lagda.md) 的 `noW`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.Align.Level hiding (z≅; s≅; l≅)
import OCF.Align.Level as Level
open Level using () renaming (z≅ to z≅ᴵ; s≅ to s≅ᴵ; l≅ to l≅ᴵ)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.NotFree using (Goodᴺ; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3Eq using (_≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; R→≅ˢ; toZ-≅; _≅ᶻ_; Ωˢ-≅; addˢ-≅; kd-≅; tr⁻ˢ-≅; ≅-tr⁻ˢ)
open import OCF.Align.Uniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; InF; ink; inb; inl; inr; Top; Bd; sb; accT; ins; insB; sup₁-up; sup₁-K; sup-K; sup-up; top₀; mapTop; bound; bound-≅; _∼ᶠ_; fz∼; fk∼; fb∼; zk∼; kz∼; ⊔∼; ∼ᶠ-refl; Fc; evF; iF; FB; liftEv)
open import OCF.Align.UniformLvNeg using (lvG; clo⊑)
open import OCF.Align.UniformLvBase
open import OCF.Align.UniformLvTree
open import OCF.Align.InaccThetaNeg using (i; ω≅i; ω₁<sel; flag-true; flag)
open import OCF.Align.InaccSingularBase using (WLPO)
open import OCF.Align.LvCertRel using (module Rel; ᶠ→ᶜ)
```

## §1 标签在 $\psi_1(1)+\Omega$ 上确实相撞

```agda
tag-out : times Ω·ω ≡ lcl 1 (Ω·ω ⊞_)
tag-out = refl

tag-in : Ω· 2 ≡ lcl 1 (base ⊞_)
tag-in = refl
```

## §2 界不低于进界的项

`Bd-in`: 任何形状的地板, 只要 `fk K` 在里面, 界就 $\ge K+1$. 是 [UniformLvNeg](UniformLvNeg.lagda.md) 的 `Bd-K` 的一般形.

```agda
accUp : ∀ {i ℓ φ₁} (t : Top i ℓ φ₁) φ (e : Ev ℓ φ) → Bd t ⊑ᴵ Bd (accT t φ e)
accUp t fz      e = ⊑ᴵ-refl
accUp t (fk K)  e = sup₁-up (Bd t) K (sb t) e
accUp t (fb K)  e = sup-up (Bd t) K (sb t) e
accUp t (a ⊔ b) (x , y) = ⊑ᴵ-trans (accUp t a x) (accUp (accT t a x) b y)

data Inᵏ (K : Ordᴵ) : Flr → Set where
  ink′ : Inᵏ K (fk K)
  inl′ : ∀ {a b} → Inᵏ K a → Inᵏ K (a ⊔ b)
  inr′ : ∀ {a b} → Inᵏ K b → Inᵏ K (a ⊔ b)

accIn : ∀ {i ℓ φ₁} (t : Top i ℓ φ₁) φ (e : Ev ℓ φ) {K} → Inᵏ K φ → suc K ⊑ᴵ Bd (accT t φ e)
accIn t (fk K)  e ink′ = sup₁-K (Bd t) K (sb t) e
accIn t (a ⊔ b) (x , y) (inl′ k) = ⊑ᴵ-trans (accIn t a x k) (accUp (accT t a x) b y)
accIn t (a ⊔ b) (x , y) (inr′ k) = accIn (accT t a x) b y k

Bd-in : ∀ {i ℓ} φ (e : Ev ℓ φ) (p : i <ᴵ ℓ) {K} → Inᵏ K φ → suc K ⊑ᴵ Bd (bound φ e p)
Bd-in φ e p k = accIn (top₀ p) φ e k
```

## §3 外层标签 1 的闭包

```agda
c₁ : LI
c₁ = times Ω·ω

cf₁ : Cf c₁
cf₁ = Mono.WF-times Ω·ω selfΩ·ω WFΩ·ω , ≈times selfΩ·ω

open module F₁ = Fold {c₁} cf₁ using () renaming (ψ̄ to ψ̄₁)

Inner : O c₁ (((Fl₀ ∪ tz) ∪ tz) ∪ tz)
Inner = ι df (ι ds (ι (dl 2) (Ω̇ (Ω· 2))))

Fst : O c₁ (((Fl₀ ∪ tz) ∪ tz) ∪ tz)
Fst = ι df (ι ds (ι (dl 2) (owk pt (ι df (Ω̇ (base ⊞ one))))))

Clo : ∀ K → O c₁ ((tz ∪ tk 1 K) ∪ (((Fl₀ ∪ tz) ∪ tz) ∪ tz))
Clo K = ι (db K) o0 ⊕ Inner

Fst₀ : ∀ K → O c₁ ((tz ∪ tk 1 K) ∪ (((Fl₀ ∪ tz) ∪ tz) ∪ tz))
Fst₀ K = ι (db K) o0 ⊕ Fst

-- 世界: 第 0 层固定, 第 1 层放得下 K
wK : Ordᴵ → Wd
wK K zero    = suc zero
wK K (suc _) = suc K

okK : ∀ K → zero <ᴵ K → Wok (wK K)
okK K q zero    = zero
okK K q (suc _) = suc q

evK : ∀ K → Evt (wK K) ((tz ∪ tk 1 K) ∪ (((Fl₀ ∪ tz) ∪ tz) ∪ tz))
evK K = (tt , (λ q → q)) , ((((tt , (λ q → q)) , tt) , tt) , tt)
```

## §4 否定: `times Ω·ω` 本身

`val K q`: 闭包的值. `first K q`: 它的第 0 个链点. 界 $\ge K+1$ (`Bd-in`), `gc` 要界不高于第 0 点的层号 (`clo⊑`). 第 0 点不随 $K$ 变 (`free`), 所以矛盾. 这是 [UniformLvNeg](UniformLvNeg.lagda.md) 的 `noAll` 的形状, 落在 $\psi_1(1)+\Omega$ 自己的层号上, 标签是 `times` 算出来的.

`Free` 由 [LvCertRel](LvCertRel.lagda.md) 的带掩码互模拟 `Rel Ne1` 证出: 高度 1 被掩掉, 第 0 点里没有高度 1 的闭包, 所以地板 `tk 1 K` 不同的两棵树相关. 我自己先试过对一切 $x\cong^{\mathsf s}y$ 的逻辑关系, 没有通过; `Rel` 用的是语义的地板对齐 `_∼ᶜ_`.

```agda
πK : Ordᴵ → Fᵗ
πK K = (tz ∪ tk 1 K) ∪ (((Fl₀ ∪ tz) ∪ tz) ∪ tz)

Gb : ∀ K η → O c₁ (πK K ∪ tk 1 η)
Gb K η = owk asr (ι (db K) o0 ⊕ owk sw₃ (ι df (owk sw₃ (ι ds (owk sw₃ (ι (dl 2) (ι (db η) (Ω̇ (base ⊞ η)))))))))

val first : ∀ K → zero <ᴵ K → Ordˢ zero
val K q = ψ̄₁ (ocl 1 (Fst₀ K) (Gb K)) (okK K q) (evK K) zero
first K q = ψ̄₁ (Fst₀ K) (okK K q) (evK K) zero

domᵗ : ∀ {π} h (t : Runᵗ π) (g : (η : Ordᴵ) → Runᵗ (π ∪ tk (suc h) η)) {w} (ok : Wok w) (ev : Evt w π) (p : zero <ᴵ w 0) {K} →
       Inᵏ K (prj (suc h) π ⊔ fk zero) → Goodᴺ (toZ (cloᵗ (suc h) t g ok ev p)) → Σ (Goodᴺ (toZ (t ok ev p))) λ G₀ → suc K ⊑ᴵ lvG G₀
domᵗ {π} h t g {w} ok ev p k G with clo⊑ G
... | G₀ , d = G₀ , ⊑ᴵ-trans (Bd-in (prj (suc h) π ⊔ fk zero) _ _ k) d

-- 外层加法与嵌入之后, 闭包就是这个节点: 树的等式, 不求值
clo-eq : ∀ K → Clo K ≡ ocl 1 (Fst₀ K) (Gb K)
clo-eq K = refl

Dom : ∀ K (q : zero <ᴵ K) → Goodᴺ (toZ (val K q)) → Σ (Goodᴺ (toZ (first K q))) λ G₀ → suc K ⊑ᴵ lvG G₀
Dom K q G = domᵗ {πK K} 0 (ψ̄₁ (Fst₀ K)) (λ η → ψ̄₁ (Gb K η)) (okK K q) (evK K) zero (inl′ (inl′ (inr′ ink′)))
              G

-- 抽象的矛盾: 第 0 点不随 K 变, 而每个 K 都被它支配. 对抽象的 X 证, 避开 `with` 展开大项
absurdGen : (X : ∀ K → zero <ᴵ K → Z) → (∀ K K′ q q′ → X K q ≅ᶻ X K′ q′) →
            (∀ K q → Σ (Goodᴺ (X K q)) λ G₀ → suc K ⊑ᴵ lvG G₀) → ⊥
absurdGen X fr D with D (suc zero) zero
... | G₀ , s⊑ (s≅ᴵ z≅ᴵ) q′ with D (lvG G₀) (<ᴵ-trans zero q′)
...   | G₁ , s⊑ e q = ≺ᴵ-irrefl (≺ᴵ-respʳ (via e q) (toLevel-≅ _ _ (forceᴺ-≅ (fr _ _ _ _) G₁ G₀)))

Free : Set
Free = ∀ K K′ (q : zero <ᴵ K) (q′ : zero <ᴵ K′) → toZ (first K q) ≅ᶻ toZ (first K′ q′)

Ne1 : ℕ → Set
Ne1 (suc zero) = ⊥
Ne1 _          = ⊤

module M = Rel Ne1

tk∼₁ : ∀ K K′ → tk 1 K M.∼ₛ tk 1 K′
tk∼₁ K K′ zero n = ᶠ→ᶜ fz∼
tk∼₁ K K′ (suc (suc m)) n = ᶠ→ᶜ fz∼

K∼ : ∀ K K′ → (tz ∪ tk 1 K) M.∼ₛ (tz ∪ tk 1 K′)
K∼ K K′ = M.∪∼ (M.frefl tz) (tk∼₁ K K′)

R-first : ∀ K K′ → M.Rᵒ c₁ c₁ (Fst₀ K) (Fst₀ K′)
R-first K K′ = M.R-⊕ (K∼ K K′) M.rz (M.R-ι df df (M.frefl tz) (M.R-ι ds ds (M.frefl tz) (M.R-ι (dl 2) (dl 2) (M.frefl tz) (M.rwk (M.R-ι df df (M.frefl tz) (M.RΩ̇ (s≈ b≈) tt))))))

free : Free
free K K′ q q′ = toZ-≅ (M.R→≈ cf₁ cf₁ (R-first K K′) (okK K q) (evK K) zero (okK K′ q′) (evK K′) zero z≅ᴵ)

-- $\psi_1(1)+\Omega$ 上: 无条件
noTimes : ((K : Ordᴵ) (q : zero <ᴵ K) → Goodᴺ (toZ (val K q))) → ⊥
noTimes all = absurdGen (λ K q → toZ (first K q)) free (λ K q → Dom K q (all K q))
```


## §5 否定: 无条件形 (同标签的嵌套)

外层与内层标签都取 $h+1$, 内层是 $\Omega_\Omega$ 的层号 `lcl (suc h) (zero ⊞_)`. 它的第 0 点是 $\psi_0(\Omega_1)$ 的折叠, 全在第 0 层: 没有 `oi`, 没有闭包, 所以 "同形" 的关系 `≃₀` 只有四条, `Free` 是定理. **这就是标签必须做的事: 嵌套的两个节点不能同标签. 对任何 $h$, 对任何证书 `cf`.**

```agda
Ln : ℕ → LI
Ln h = lcl (suc h) (zero ⊞_)

selfLn : ∀ h → Ln h ≈ Ln h
selfLn h = o≈ refl (λ η η′ d → ≈⊞ z≈ d)

Nest : ℕ → LI
Nest h = lcl (suc h) (Ln h ⊞_)

cfN : ∀ h → Cf (Nest h)
cfN h = Mono.WF-times (Ln h) (selfLn h) (Mono.WF-times zero z≈ tt) , o≈ refl (λ η η′ d → ≈⊞ (selfLn h) d)

data _≃₀_ {a : LI} : ∀ {π ρ} → O a π → O a ρ → Set where
  ≃0  : ∀ {π ρ} → _≃₀_ {a} {π} {ρ} o0 o0
  ≃s  : ∀ {π ρ} {x : O a π} {y : O a ρ} → x ≃₀ y → os x ≃₀ os y
  ≃l  : ∀ {π ρ} {F : ℕ → O a π} {G : ℕ → O a ρ} → (∀ n → F n ≃₀ G n) → ol F ≃₀ ol G
  ≃w  : ∀ {π π′ ρ ρ′} {le : ∀ {w} → Evt w π′ → Evt w π} {le′ : ∀ {w} → Evt w ρ′ → Evt w ρ} {x : O a π} {y : O a ρ} → x ≃₀ y → owk le x ≃₀ owk le′ y

ι≃ : ∀ {a b} (d : Dn a b) {π ρ} {x : O a π} {y : O a ρ} → x ≃₀ y → ι d x ≃₀ ι d y
ι≃ d ≃0 = ≃0
ι≃ d (≃s r) = ≃s (ι≃ d r)
ι≃ d (≃l h) = ≃l (λ n → ι≃ d (h n))
ι≃ d (≃w r) = ≃w (ι≃ d r)

⊕≃ : ∀ {k φ φ′ π ρ} {W : O k φ} {W′ : O k φ′} {x : O k π} {y : O k ρ} → W ≃₀ W′ → x ≃₀ y → (W ⊕ x) ≃₀ (W′ ⊕ y)
⊕≃ w ≃0 = ≃w w
⊕≃ w (≃s r) = ≃s (⊕≃ w r)
⊕≃ w (≃l h) = ≃l (λ n → ⊕≃ w (h n))
⊕≃ w (≃w r) = ≃w (⊕≃ w r)

rep≃ : ∀ {k π ρ} {x : O k π} {y : O k ρ} → x ≃₀ y → ∀ m → repᵒ x m ≃₀ repᵒ y m
rep≃ r zero          = ≃0
rep≃ r (suc zero)    = r
rep≃ r (suc (suc m)) = ≃w (⊕≃ (rep≃ r (suc m)) r)

chain≃ : ∀ {k π ρ} {fe : ∀ {w} → Evt w π → Evt w Fl₀} {fe′ : ∀ {w} → Evt w ρ → Evt w Fl₀} {f : O k π → O k π} {f′ : O k ρ → O k ρ} →
         Ω̇ k ≃₀ Ω̇ k → (∀ {x y} → x ≃₀ y → f x ≃₀ f′ y) → ∀ m → chainᵒ fe f m ≃₀ chainᵒ fe′ f′ m
chain≃ b s zero    = ≃w b
chain≃ b s (suc m) = s (chain≃ b s m)

-- 一层 Ω 节点: 输入是同形的树
data Nd {a : LI} : ∀ {π ρ} → O a π → O a ρ → Set where
  n-w : ∀ {π π′ ρ ρ′} {le : ∀ {w} → Evt w π′ → Evt w π} {le′ : ∀ {w} → Evt w ρ′ → Evt w ρ} {x : O a π} {y : O a ρ} → Nd x y → Nd (owk le x) (owk le′ y)
  n-Ω : ∀ {π ρ k} {fe : ∀ {w} → Evt w π → Evt w Fl₀} {fe′ : ∀ {w} → Evt w ρ → Evt w Fl₀} {r : k <ᴸ a} {ac : ∀ {w} → Evt w π → Adm w r} {ac′ : ∀ {w} → Evt w ρ → Adm w r}
        {h : ∀ ξ → Us a r ξ → O a (ξ ∪ π)} {h′ : ∀ ξ → Us a r ξ → O a (ξ ∪ ρ)} → Ω̇ k ≃₀ Ω̇ k →
        (∀ ξ ξ′ (z : Us a r ξ) (z′ : Us a r ξ′) → outU r z ≃₀ outU r z′ → h ξ z ≃₀ h′ ξ′ z′) → Nd (oΩ fe r ac h) (oΩ fe′ r ac′ h′)

⊕N : ∀ {k φ φ′ π ρ} {W : O k φ} {W′ : O k φ′} {x : O k π} {y : O k ρ} → W ≃₀ W′ → Nd x y → Nd (W ⊕ x) (W′ ⊕ y)
⊕N w (n-w r) = n-w (⊕N w r)
⊕N w (n-Ω b h) = n-Ω b (λ ξ ξ′ z z′ d → ≃w (⊕≃ w (h ξ ξ′ z z′ d)))

ιN : ∀ {a b} (d : Dn a b) {π ρ} {x : O a π} {y : O a ρ} → Nd x y → Nd (ι d x) (ι d y)
ιN d (n-w r) = n-w (ιN d r)
ιN ds (n-Ω b h) = n-Ω b (λ ξ ξ′ z z′ c → ≃w (ι≃ ds (h ξ ξ′ z z′ c)))
ιN (dl n) (n-Ω b h) = n-Ω b (λ ξ ξ′ z z′ c → ≃w (ι≃ (dl n) (h ξ ξ′ z z′ c)))
ιN df (n-Ω b h) = n-Ω b (λ ξ ξ′ z z′ c → ≃w (ι≃ df (h ξ ξ′ z z′ c)))
ιN (db η) (n-Ω b h) = n-Ω b (λ ξ ξ′ z z′ c → ≃w (ι≃ (db η) (h ξ ξ′ z z′ c)))

inSel : ∀ h K → Inᵏ K (sel h h (fk K))
inSel zero    K = ink′
inSel (suc h) K = inSel h K

module N (h : ℕ) (cf : Cf (Nest h)) where
  open Fold {Nest h} cf renaming (ψ̄ to ψ̄ₙ)

  fund : ∀ {π ρ} {x : O (Nest h) π} {y : O (Nest h) ρ} → x ≃₀ y → ∀ {i i′ w w′} (ok : Wok w) (e : Evt w π) (p : i <ᴵ w 0) (ok′ : Wok w′) (e′ : Evt w′ ρ) (p′ : i′ <ᴵ w′ 0) → i ≅ᴵ i′ → ψ̄ₙ x ok e p ≅ˢ ψ̄ₙ y ok′ e′ p′
  fund ≃0 ok e p ok′ e′ p′ ei = Ωˢ-≅ ei
  fund (≃s r) ok e p ok′ e′ p′ ei = l≅ (iter-R _≅ˢ_ (λ d → addˢ-≅ ei (fund r ok e p ok′ e′ p′ ei) d) z≅)
  fund (≃l h) ok e p ok′ e′ p′ ei = l≅ (λ n → fund (h n) ok e p ok′ e′ p′ ei)
  fund (≃w r) ok e p ok′ e′ p′ ei = fund r ok _ p ok′ _ p′ ei

  ψ≃ : ∀ {t χ χ′} (q : t <ᴸ Nest h) {fl : ∀ {w} → Evt w χ → Evt w Fl₀} {aq : ∀ {w} → Evt w χ → Adm w q}
       {fl′ : ∀ {w} → Evt w χ′ → Evt w Fl₀} {aq′ : ∀ {w} → Evt w χ′ → Adm w q} →
       Ω̇ t ≃₀ Ω̇ t → ∀ {π ρ} {x : O (Nest h) π} {y : O (Nest h) ρ} → x ≃₀ y → ψᵒ q fl aq x ≃₀ ψᵒ q fl′ aq′ y
  ψ≃ q Ωt ≃0 = ≃w Ωt
  ψ≃ q Ωt (≃s r) = ≃l (rep≃ (ψ≃ q Ωt r))
  ψ≃ q Ωt (≃l h) = ≃l (λ n → ψ≃ q Ωt (h n))
  ψ≃ q Ωt (≃w r) = ≃w (ψ≃ q Ωt r)

  Inn Fs : O (Nest h) ((Fl₀ ∪ tz) ∪ tz)
  Inn = ι df (ι ds (Ω̇ (Ln h)))
  Fs = ι df (ι ds (owk pt (ι df (Ω̇ (zero ⊞ one)))))

  πₙ : Ordᴵ → Fᵗ
  πₙ K = (tz ∪ tk (suc h) K) ∪ ((Fl₀ ∪ tz) ∪ tz)

  Cl Fs₀ : ∀ K → O (Nest h) (πₙ K)
  Cl K = ι (db K) o0 ⊕ Inn
  Fs₀ K = ι (db K) o0 ⊕ Fs

  Gₙ : ∀ K η → O (Nest h) (πₙ K ∪ tk (suc h) η)
  Gₙ K η = owk asr (ι (db K) o0 ⊕ owk sw₃ (ι df (owk sw₃ (ι ds (ι (db η) (Ω̇ (zero ⊞ η)))))))

  cl-eq : ∀ K → Cl K ≡ ocl (suc h) (Fs₀ K) (Gₙ K)
  cl-eq K = refl

  wN : Ordᴵ → Wd
  wN K zero    = suc zero
  wN K (suc _) = suc K

  okN : ∀ K → zero <ᴵ K → Wok (wN K)
  okN K q zero    = zero
  okN K q (suc _) = suc q

  evN : ∀ K → Evt (wN K) (πₙ K)
  evN K = (tt , (λ q → q)) , (((tt , (λ q → q)) , tt) , tt)

  valₙ firstₙ : ∀ K → zero <ᴵ K → Ordˢ zero
  valₙ K q = ψ̄ₙ (ocl (suc h) (Fs₀ K) (Gₙ K)) (okN K q) (evN K) zero
  firstₙ K q = ψ̄ₙ (Fs₀ K) (okN K q) (evN K) zero

  Dmₙ : ∀ K q → Goodᴺ (toZ (valₙ K q)) → Σ (Goodᴺ (toZ (firstₙ K q))) λ G₀ → suc K ⊑ᴵ lvG G₀
  Dmₙ K q G = domᵗ {πₙ K} h (ψ̄ₙ (Fs₀ K)) (λ η → ψ̄ₙ (Gₙ K η)) (okN K q) (evN K) zero (inl′ (inl′ (inr′ (inSel h K)))) G

  Ω1≃ : Ω̇ zero ≃₀ Ω̇ zero
  Ω1≃ = ≃s ≃0

  outInto : ∀ {L k} (r : k <ᴸ L) {ξ} (x : O k ξ) → outU r (intoU r x) ≡ x
  outInto zero      x = refl
  outInto (suc r)   x = outInto r x
  outInto (lim n r) x = outInto r x
  outInto (fst r)   x = outInto r x
  outInto (bra η r) x = outInto r x

  fundN : ∀ {π ρ} {x : O (Nest h) π} {y : O (Nest h) ρ} → Nd x y → ∀ {i i′ w w′} (ok : Wok w) (e : Evt w π) (p : i <ᴵ w 0) (ok′ : Wok w′) (e′ : Evt w′ ρ) (p′ : i′ <ᴵ w′ 0) → i ≅ᴵ i′ → ψ̄ₙ x ok e p ≅ˢ ψ̄ₙ y ok′ e′ p′
  fundN (n-w r) ok e p ok′ e′ p′ ei = fundN r ok _ p ok′ _ p′ ei
  fundN {π} {ρ} (n-Ω {r = r} b hr) ok e p ok′ e′ p′ ei =
    l≅ (λ m → fund (hr π ρ _ _ (conv (chain≃ b (λ d → ≃w (ψ≃ r b (hr π ρ _ _ (conv d)))) m))) ok (e , e) p ok′ (e′ , e′) p′ ei)
    where
    conv : ∀ {ξ ξ′} {x : O _ ξ} {y : O _ ξ′} → x ≃₀ y → outU r (intoU r x) ≃₀ outU r (intoU r y)
    conv {x = x} {y = y} d = subst₂ _≃₀_ (sym (outInto r x)) (sym (outInto r y)) d

  XN : Nd (Ω̇ (zero ⊞ one)) (Ω̇ (zero ⊞ one))
  XN = n-Ω Ω1≃ (λ ξ ξ′ z z′ d → ≃w (ι≃ ds d))

  freeₙ : ∀ K K′ q q′ → firstₙ K q ≅ˢ firstₙ K′ q′
  freeₙ K K′ q q′ = fundN {x = Fs₀ K} {y = Fs₀ K′} (⊕N ≃0 (ιN df (ιN ds (n-w (ιN df XN))))) (okN K q) (evN K) zero (okN K′ q′) (evN K′) zero z≅ᴵ

noNest : ∀ h (cf : Cf (Nest h)) → ((K : Ordᴵ) (q : zero <ᴵ K) → Goodᴺ (toZ (N.valₙ h cf K q))) → ⊥
noNest h cf all = absurdGen (λ K q → toZ (N.firstₙ h cf K q)) (λ K K′ q q′ → toZ-≅ (N.freeₙ h cf K K′ q q′)) (λ K q → N.Dmₙ h cf K q (all K q))
```

## §6 否定: 没有带判定相等的键

上面说嵌套的节点必须分开. 这里说**这种分开不能用任何带判定相等的键做**, 自然数只是特例. `Sep t`: $t:\mathsf{Ord}^\mathsf I\to\mathbb N$ 尊重 $\cong^\mathsf I$ (由 `≈` 的 `o≈` 强制: `resp-of`), 且分开严格序 (由 `noNest`: 分支 $\theta\prec\theta'$ 上的节点是嵌套的). 这蕴含 WLPO. 反例族就是 `no-uniform` 的 $i\,s$. 所以键的比较必须读证据 (`kdec`).

```agda
record Sep (t : Ordᴵ → ℕ) : Set where
  field
    resᵗ : ∀ {a b} → a ≅ᴵ b → t a ≡ t b
    sepᵗ : ∀ {a b} → a ≺ᴵ b → t a ≡ t b → ⊥
open Sep

noTag : ∀ t → Sep t → WLPO
noTag t S s with t ωᴵ ≟ t (i s)
... | yes e = inj₁ (λ n → go n (s n) refl)
  where
  go : ∀ n b → s n ≡ b → s n ≡ false
  go n false p = p
  go n true p = ⊥-elim (sepᵗ S (via (≅ᴵ-refl _) (<ᴵ-trans zero (lim n (ω₁<sel (flag s n) n (flag-true s n p))))) e)
... | no ne = inj₂ (λ h → ne (resᵗ S (ω≅i s h)))

-- 一个带标签的族: 每个分支一个节点. `≈` 自反就强制标签尊重 ≅ᴵ
Fam : (Ordᴵ → ℕ) → LI
Fam t = lcl 1 (λ θ → lcl (t θ) (zero ⊞_))

resp-of : ∀ {t} → Fam t ≈ Fam t → ∀ {a b} → a ≅ᴵ b → t a ≡ t b
resp-of (o≈ _ h) {a} {b} e with h a b e
... | o≈ r _ = r
```
