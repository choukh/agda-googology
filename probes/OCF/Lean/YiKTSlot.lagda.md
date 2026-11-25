# 塔第 1 项前缀下的 LowKeep：新证据 "槽位有更高的读法" 与它在 d = 1 上的空处
验收文件（读记号），树、折叠、合法性不改。编译定理：`above`（共尾 Ω_{κ+1} 的项不高于它在不低于 Ω_{κ+1} 处的 Ω-基本列项）；`node-above`（"树走链、记号保留" 的结点，槽位有不低于 κ+1 的读法时保持，只用链的第 1 项与底的前缀）；`spec-top`（Ω 形状朝自己下标层折时顶槽位对一切 κ 有证据）；`spec-hh`（`YiTLReduce.block-frame` 的结点在 ν ≤ Ω₁ 时对一切 κ 有证据）。
有限测试（实际层号证据 `oᴱ`，d = 1）：槽位 `p*` 走链（`kp*`），分支类型相同的叶槽位 `p₀` 保留（`kp₀`）。编译否定（只否定证据域）：`p*` 上 κ = 0、ν = 1 时新旧证据都为空（`no-above`、`no-spec*`）。
条件定理：`tight-at`（`TightStep 1` 连同底的两条前提推出 `Cand`：一棵 ℕ 极限树承载共尾度 Ω₁ 的参照 ψ₁(Ω_{Ω₁})；两条关系前提已实填）。`Cand` 未判定。
不否定 `TightStep`、`KeepOut`、`KeepFeed`，也不否定别的证据形式。入口：`node-above`、`spec-hh`、`no-spec*`、`tight-at`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKTSlot where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK; feed)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiGTGen using (closeᴿ; cumᴿ; app≤ν)
open import OCF.Lean.YiGTNode using (KeepSpec; NodeFrame; ChainAt; start-prefix; module Core)
open import OCF.Lean.YiHCRel using (∷≤)
open import OCF.Lean.YiCNTw1 using (rd-zero)
open import OCF.Lean.YiSYReduce using (a₁; h₁; oᴱ; Bᴱ)
open import OCF.Lean.YiTLReduce using (hh; NotSelf; not-self; noΩ-h₁; TightStep)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiGLDom using (dz; dC; dom-top)
open import OCF.Lean.YiNLCtx using (prefix; Top)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLeanBase using (≤-trans′)
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiSYDesc as D
import OCF.Lean.YiHCRel as H
open import OCF.Align.EBO using (pred-suc; cΩ-inj)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; lt→<; eq→≡)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open E using (cof; cofA; cofψ0; cofψ₊; cΩ; c0; c1; cω; fsT; fsT0; fsT₊; fsTc; lt; eq; gt; 𝟏)
```

## 记号一侧：基本列项在高处不低于原项

`above a e le`：`cof a ≡ cΩ κ` 且 Ω_{κ+1} ≤ η 时 a ≤ a[η]（项序）。子句与 `E.fsT` 一一对应；哑值分支被共尾度前提排除。

```agda
above  : ∀ a {κ η} → cof a ≡ cΩ κ → E.Ωs κ ≤ᵀ η → a ≤ᵀ fsT a η
above0 : ∀ u c → cof u ≡ c → ∀ {κ η} → cofψ0 u c ≡ cΩ κ → E.Ωs κ ≤ᵀ η → (E.ψ u [] ∷ []) ≤ᵀ fsT0 u c η
above₊ : ∀ u b c → cof b ≡ c → ∀ {κ η} → cofA u c ≡ cΩ κ → E.Ωs κ ≤ᵀ η → (E.ψ u b ∷ []) ≤ᵀ fsT₊ u b c η
abovec : ∀ u b ν → cof b ≡ cΩ ν → ∀ m {κ η} → cofψ₊ u ν m ≡ cΩ κ → E.Ωs κ ≤ᵀ η → (E.ψ u b ∷ []) ≤ᵀ fsTc u b ν m η

lv≤ : ∀ {u v} → u ≤ᵀ v → (E.ψ u [] ∷ []) ≤ᵀ (E.ψ v [] ∷ [])
lv≤ (inj₁ p) = inj₁ (E.hd< (E.lv< p))
lv≤ (inj₂ refl) = inj₂ refl

ar≤ : ∀ u {a b} → a ≤ᵀ b → (E.ψ u a ∷ []) ≤ᵀ (E.ψ u b ∷ [])
ar≤ u (inj₁ p) = inj₁ (E.hd< (E.ar< p))
ar≤ u (inj₂ refl) = inj₂ refl

above [] ()
above (x ∷ xs@(_ ∷ _)) e le = ∷≤ x (above xs e le)
above (E.ψ u (y ∷ ys) ∷ []) e le = above₊ u (y ∷ ys) (cof (y ∷ ys)) refl e le
above (E.ψ (w ∷ ws) [] ∷ []) e le = above0 (w ∷ ws) (cof (w ∷ ws)) refl e le
above (𝟏 ∷ []) ()

above0 u c0 ue ()
above0 u c1 ue {η = η} e′ le = subst (λ z → (E.ψ z [] ∷ []) ≤ᵀ η)
  (trans (cong E.sucT (sym (cΩ-inj e′))) (pred-suc u ue)) le
above0 u cω ue ()
above0 u (cΩ ν) ue e′ le = lv≤ (above u (trans ue (cong cΩ (cΩ-inj e′))) le)

above₊ u b c0 be ()
above₊ u b c1 be ()
above₊ u b cω be ()
above₊ u b (cΩ ν) be e′ le = abovec u b ν be (E.cmpᵀ (E.sucT ν) u) e′ le

abovec u b ν be lt e″ le = ar≤ u (above b (trans be (cong cΩ (cΩ-inj e″))) le)
abovec u b ν be eq e″ le = ar≤ u (above b (trans be (cong cΩ (cΩ-inj e″))) le)
abovec u b ν be gt ()
```

## 证据与结点一行

`KeepSpec′` 只改走链一支：记号也走链（原条件），或槽位有读法 κ″ 满足 κ+1 ≤ κ″（`Above`）。后一种情形记号保留而树走链；链的第 1 项由 `start-prefix` 不低于 Ω_κ″，于是该分支的折叠不低于 ψ_ν(t ++ a[Ω_κ″])，再由 `above` 与向下封闭得到 ψ_ν(t ++ a)。不需要 `StepU′`，也不需要分支关系 `hg`。

```agda
Ωs≤Ωt : ∀ {κ κ″} → E.sucT κ ≤ᵀ κ″ → E.Ωs κ ≤ᵀ E.Ωt κ″
Ωs≤Ωt = lv≤

Above : ∀ ℓ (p : Pos ℓ) → E.T → Set
Above ℓ p κ = Σ E.T λ κ″ → GR.Nu ℓ p κ″ × (E.sucT κ ≤ᵀ κ″)

KeepSpec′ : ∀ ℓ j ν (p : Pos ℓ) κ → Keep j (Br ℓ p) (fromBr ℓ p zero) → Set
KeepSpec′ ℓ j ν p κ nothing = (E.cmpᵀ (E.sucT κ) ν ≡ gt) ⊎ Above ℓ p κ
KeepSpec′ ℓ j ν p κ (just K) = KeepSpec ℓ j ν p κ (just K)

module Row′ (ℓ j : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ)
  (ν t : E.T) (β : Tr⁺ j) where
  private module C = Core ℓ j o r B w ν t β
  open C using (F)

  node-above : PrefixU B t → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → cof a ≡ cΩ κ → Above ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ fsT a η) ∷ []) (proj₁ (F (g c))))
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (node⁺ nothing (λ c → F (g c)) (feed ℓ o r B p g)))
  node-above pref p {a} g e (κ″ , nu″ , le) bh =
    closeᴿ j (app≤ν ν t (above a e (Ωs≤Ωt le)))
      (cumᴿ j (λ k → F (g (iter (feed ℓ o r B p g) (fromBr ℓ p zero) k))) 1
        (bh (E.Ωt κ″) _ (start-prefix ℓ o r B t pref p κ″ nu″ g)))

  node-at′ : PrefixU B t → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → cof a ≡ cΩ κ → GR.Nu ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (fsT a η) (g c))
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ fsT a η) ∷ []) (proj₁ (F (g c))))
    → ChainAt ℓ o r B t a p κ g
    → (K : Keep j (Br ℓ p) (fromBr ℓ p zero)) → KeepSpec′ ℓ j ν p κ K
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (node⁺ K (λ c → F (g c)) (feed ℓ o r B p g)))
  node-at′ pref p g e nu hg bh hc (just K) sp = C.node-at p g e nu hg bh hc (just K) sp
  node-at′ pref p g e nu hg bh hc nothing (inj₁ q) = C.node-at p g e nu hg bh hc nothing q
  node-at′ pref p g e nu hg bh hc nothing (inj₂ ab) = node-above pref p g e ab bh
```

## 有居民的两处

顶槽位朝自己的下标层（`kp` 走链）：目标下标 ν 自己就是槽位的读法。后继形状层号的孩子槽位经非 `self` 路径（`kp` 走链）：孩子层号有不低于 ν 的读法即可；`tw 1 ⊕ X` 都读作 Ω₁，所以 `YiTLReduce.block-frame` 判为只容 ν = 0 的结点在这里对一切 ν ≤ Ω₁ 有证据。

```agda
Ω₁ : E.T
Ω₁ = E.Ωt (𝟏 ∷ [])

rd-tw1Ω : GR.Rd (tw 1) Ω₁
rd-tw1Ω = GR.ca (inj₂ ([] , refl , GR.c0 refl , λ η c r → GR.rd-add zero (↑ zero c) (LL.read0 r)))

rd-pre : ∀ X → GR.Rd (tw 1 ⊕ X) Ω₁
rd-pre zero = rd-tw1Ω
rd-pre (nd s h) = GR.rd-child s (λ c → tw 1 ⊕ h c) (c₀ s) (rd-pre (h (c₀ s)))

split : ∀ κ ν → (E.cmpᵀ (E.sucT κ) ν ≡ gt) ⊎ (E.sucT κ ≤ᵀ ν)
split κ ν with E.cmpᵀ (E.sucT κ) ν in q
... | gt = inj₁ refl
... | lt = inj₂ (inj₁ (lt→< _ _ q))
... | eq = inj₂ (inj₂ (eq→≡ _ _ q))

from-split : ∀ ℓ (p : Pos ℓ) κ ν ρ → GR.Nu ℓ p ρ → ν ≤ᵀ ρ
  → (E.cmpᵀ (E.sucT κ) ν ≡ gt) ⊎ (E.sucT κ ≤ᵀ ν) → (E.cmpᵀ (E.sucT κ) ν ≡ gt) ⊎ Above ℓ p κ
from-split ℓ p κ ν ρ nu le (inj₁ q) = inj₁ q
from-split ℓ p κ ν ρ nu le (inj₂ l) = inj₂ (ρ , nu , ≤-trans′ l le)

spec-child : (h : ⊤ → L) (o : Ok (nd sS h)) {j : L} (w : j ≤ nd sS h) → NotSelf w
  → ∀ ν ρ → GR.Rd (h tt) ρ → ν ≤ᵀ ρ → ∀ κ
  → KeepSpec′ (nd sS h) j ν (inj₂ (tt , inj₁ tt)) κ (kp (nd sS h) o (inj₂ (tt , inj₁ tt)) w)
spec-child h o (inc tt v) _ ν ρ rd le κ = from-split (nd sS h) (inj₂ (tt , inj₁ tt)) κ ν ρ rd le (split κ ν)
spec-child h o (inu vs) _ ν ρ rd le κ = from-split (nd sS h) (inj₂ (tt , inj₁ tt)) κ ν ρ rd le (split κ ν)

spec-hh : ∀ d z (o : Ok (hh d z)) (w : h₁ d ≤ hh d z) ν → ν ≤ᵀ Ω₁ → ∀ κ
  → KeepSpec′ (hh d z) (h₁ d) ν (inj₂ (tt , inj₁ tt)) κ (kp (hh d z) o (inj₂ (tt , inj₁ tt)) w)
spec-hh d z o w ν le κ = spec-child (λ _ → tw 1 ⊕ (zero ⊕ (zero ⊕ ↑ (h₁ d) z))) o w
  (not-self (zero ⊕ (zero ⊕ ↑ (h₁ d) z)) (noΩ-h₁ d) w) ν Ω₁ (rd-pre (zero ⊕ (zero ⊕ ↑ (h₁ d) z))) le κ

one≤Ω₁ : (𝟏 ∷ []) ≤ᵀ Ω₁
one≤Ω₁ = inj₁ (E.hd< (E.lv< E.[]<))

spec-top : ∀ k h (o : Ok (nd (sΩ k) h)) ν → GR.Rd k ν → ∀ κ
  → KeepSpec′ (nd (sΩ k) h) k ν (inj₁ (inj₁ tt)) κ (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (ink self))
spec-top k h o ν nu κ = from-split (nd (sΩ k) h) (inj₁ (inj₁ tt)) κ ν ν nu (inj₂ refl) (split κ ν)
```

## d = 1 上的空处

`z*` 是第 `h₁ 1` 层的 Ω 树；孩子 `hh 1 z*` 里有一个下标层为第 0 层的 Ω 形状层号（`tw 1 ⊕ ↑ z*` 一类），`p*` 是它自己的下标槽位，`p₀` 是它的孩子 0 里前缀 `tw 1` 的下标槽位。两者的分支类型都是 `Tr zero`，读法都只有 0（`rd-zero`）。朝 `h₁ 1` 折（路径 `ink self`，实际证据 `oᴱ`）时 `p₀` 保留，`p*` 走链；目标下标 ν = 1 时记号在两处都保留。`p*` 上链在第 0 层，没有更高的读法，所以 `Above` 为空。

```agda
one : Tr zero
one = suc zero

z* : Tr (h₁ one)
z* = proj₁ (Ωt (h₁ one))

p* p₀ : Pos (a₁ (suc one))
p* = inj₂ (z* , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))
p₀ = inj₂ (z* , inj₂ (inj₂ (tt , inj₂ (inj₂ (zero , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))))))

IsNothing IsJust : ∀ {j X x₀} → Keep j X x₀ → Set
IsNothing nothing = ⊤
IsNothing (just _) = ⊥
IsJust nothing = ⊥
IsJust (just _) = ⊤

kp* : IsNothing (kp (a₁ (suc one)) (proj₂ oᴱ (suc one)) p* (ink self))
kp* = tt

kp₀ : IsJust (kp (a₁ (suc one)) (proj₂ oᴱ (suc one)) p₀ (ink self))
kp₀ = tt

nu* : GR.Nu (a₁ (suc one)) p* []
nu* = GR.c0 refl

nu₀ : GR.Nu (a₁ (suc one)) p₀ []
nu₀ = GR.c0 refl

no-above : ∀ κ → Above (a₁ (suc one)) p* κ → ⊥
no-above κ (κ″ , nu , le) with rd-zero nu
no-above [] (.[] , nu , inj₁ ()) | refl
no-above [] (.[] , nu , inj₂ ()) | refl
no-above (_ ∷ _) (.[] , nu , inj₁ ()) | refl
no-above (_ ∷ _) (.[] , nu , inj₂ ()) | refl

no-spec* : KeepSpec′ (a₁ (suc one)) (h₁ one) (𝟏 ∷ []) p* [] (kp (a₁ (suc one)) (proj₂ oᴱ (suc one)) p* (ink self)) → ⊥
no-spec* (inj₁ ())
no-spec* (inj₂ ab) = no-above [] ab

spec-hh₁ : ∀ z (o : Ok (hh one z)) (w : h₁ one ≤ hh one z) κ
  → KeepSpec′ (hh one z) (h₁ one) (𝟏 ∷ []) (inj₂ (tt , inj₁ tt)) κ (kp (hh one z) o (inj₂ (tt , inj₁ tt)) w)
spec-hh₁ z o w κ = spec-hh one z o w (𝟏 ∷ []) one≤Ω₁ κ
```

## `TightStep 1` 在一个具体点上的结论

取 t = 0、κ = 1、a = Ω_{Ω₂}、n = 0、z = `z*`、g 为 Ω 树的实际分支 `g*`。两条关系前提成立（`hyp₁`、`hyp₂`，都来自读回域 `YiGLDom.Dom`）；结论的参照 ψ₁(Ω_{Ω₁}) 共尾度是 Ω₁（`goal-cof`），而回灌出来的树是 ℕ 极限（`feed-lim`，有限测试）。所以 `TightStep 1` 连同底的两条前提推出 `Cand`（`tight-at`）。`Cand` 本身未判定：极限树上的推导只能经 `mw`、`mc` 两条。

```agda
g* : Tr (h₁ one) → Tr (a₁ (suc one))
g* z = proj₁ (upz {s = sΩ (h₁ one)} {h = hh one} z (Ωt (hh one z)))

a* κ* s* : E.T
κ* = 𝟏 ∷ []
a* = E.Ωt (E.Ωt (𝟏 ∷ 𝟏 ∷ []))
s* = E.sucT (E.Ωt κ*)

cof-a* : cof a* ≡ cΩ κ*
cof-a* = refl

nu-top : GR.Nu (a₁ (suc one)) (inj₁ (inj₁ tt)) κ*
nu-top = GR.ca (inj₂ (refl , GR.c0 refl))

goal-term : E.γT ([] ++ a*) κ* 1 ≡ E.ψ κ* (E.Ωt (E.Ωt κ*)) ∷ []
goal-term = refl

goal-cof : cof (E.γT ([] ++ a*) κ* 1) ≡ cΩ []
goal-cof = refl

IsLim : ∀ {S} → T S → Set
IsLim (lim _ _) = ⊤
IsLim _ = ⊥

feed-lim : IsLim (feed (a₁ (suc one)) (proj₂ oᴱ (suc one)) (rbᶻ (a₁ (suc one))) (D.dn Bᴱ (suc one)) (inj₁ (inj₁ tt)) g* z*)
feed-lim = tt

hyp₁ : GR.R (h₁ one) (E.Ωt κ*) z*
hyp₁ = dom-top (dC (prefix zero) zero {t = []} {ν = κ*} {y = one} (dz zero) (H.m1 refl H.mz))

y₂ : Tr (tw 1)
y₂ = proj₁ (upz {s = sΩ zero} {h = h₁} (suc one) (upz {s = sS} {h = λ _ → h₁ one} tt (suc z* , z◃ z* ◃s)))

top-hh : Top (hh one z*) s*
top-hh = dom-top (dC (prefix (tw 1)) (tw 1) {t = []} {ν = s*} {y = y₂} (dz (tw 1))
  (H.mU {t = []} H.mz (H.mU {t = []} H.mz (H.m1 refl hyp₁))))

le* : E.Ωt (E.Ωt κ*) ≤ᵀ E.Ωt s*
le* = inj₁ (E.hd< (E.lv< (<-sucT (E.Ωt κ*))))

hyp₂ : GR.R (a₁ (suc one)) (fsT a* (E.Ωt κ*)) (g* z*)
hyp₂ = H.mU {t = []} H.mz (closeᴿ (hh one z*) le* top-hh)

Cand : Set
Cand = GR.R (h₁ one) (E.ψ κ* (E.Ωt (E.Ωt κ*)) ∷ [])
  (feed (a₁ (suc one)) (proj₂ oᴱ (suc one)) (rbᶻ (a₁ (suc one))) (D.dn Bᴱ (suc one)) (inj₁ (inj₁ tt)) g* z*)

tight-at : TightStep one → OK (D.dn Bᴱ (suc one)) → PrefixU (D.dn Bᴱ (suc one)) [] → Cand
tight-at ts gb pf = ts gb [] pf a* κ* nu-top cof-a* g* 0 z* hyp₁ hyp₂
```
