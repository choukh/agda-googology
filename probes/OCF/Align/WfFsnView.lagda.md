# WfFsnView: 共尾度的视图与基本列的展开式

> **记号侧验收工作**, 不是最终定义, 不进成品. [WfFsn](WfFsn.lagda.md) 的第二段.
>
> EBO 的 `fsT`/`fsn` 按 `cof` 的**计算值**分派 (辅助函数 `fsT0`/`fsT₊`/`fsTc`, `fsn↓0`/`fsn↓₊`/`fsn↓c`), 证明里直接对它们做 `with` 会碰到归档记下的坑 (重建的项失去结构序). 这里换成两个归纳的视图:
>
> - `VΩ a μ`: $a$ 的共尾度是 $\Omega_{\mu+1}$ ($a$ 的 Ω-脊). 四种: 和 (`ωs`), 正规叶 $\Omega_u$, $u$ 后继 (`ωr`), 奇异叶 $\Omega_u$, $u$ 的共尾度为 $\Omega_{\mu+1}$ (`ωl`), 穿透 $\psi_u(b)$, $\mu+1\le u$ (`ωp`, 规则 5Ω).
> - `Vω t`: $t$ 的共尾度是 $\omega$. 五种: 和 (`ws`), 叶 $\Omega_u$, $u$ 的共尾度 $\omega$ (`wl`), 规则 4 (`w4`), 规则 5ω (`w5`), 规则 6 (`w6`, $\mu+1>u$, γ-链).
>
> 视图由 `cof` 的等式造出 (`vΩ`, `vω`), 沿视图结构递归定义基本列 (`fΩ`, `fω`, γ-链 `γ`), 并证明与 EBO 原定义逐点相等 (`fΩ-eq`, `fω-eq`, `γ-eq`). 以后的证明都沿视图递归, 末了一次改写回 `fsT`/`fsn`. 另有基本列的单调 (`fΩ-mono`, Lean `fs_mono`), γ-链上升 (`γ-mono`, Lean `tower_lt`), 以及标准形给出的两条: $\mu$ 标准 (`nf-ν`), $\mu+1<a$ (`dom<`).
>
> `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfFsnView where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open E using (T; PT; ψ; 𝟏; _<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<; Cmp; lt; eq; gt; cmpᵀ;
              cof; cofP; cofA; cofψ0; cofψ₊; c0; c1; cω; cΩ; pred; sucT; Ωt; Ωs;
              fsT; fsT0; fsT₊; fsTc; fsn; fsn↓; fsn↓0; fsn↓₊; fsn↓c; γT; γ↓; fsT↓; trm; dec;
              fsT↓-trm; γ↓-trm; fsn₊-eq; fsn0-eq; rep-trm; pred-suc; pred-<; <-sucT)
open import OCF.Align.Closure using (<ᵀ-trans; Pen; fsTc-pen)
open import OCF.Align.WfFsnBase
```

## §1 Ω-视图

```agda
data NE : T → Set where
  ne : ∀ {x xs} → NE (x ∷ xs)

data VΩ : T → T → Set where
  ωs : ∀ {x y ys μ} → VΩ (y ∷ ys) μ → VΩ (x ∷ y ∷ ys) μ
  ωr : ∀ {u} → cof u ≡ c1 → VΩ (ψ u [] ∷ []) (pred u)
  ωl : ∀ {u μ} → cof u ≡ cΩ μ → VΩ u μ → VΩ (ψ u [] ∷ []) μ
  ωp : ∀ {u b μ} → cof b ≡ cΩ μ → Pen (cmpᵀ (sucT μ) u) → VΩ b μ → VΩ (ψ u b ∷ []) μ

vΩ  : ∀ a {μ} → cof a ≡ cΩ μ → VΩ a μ
vΩ0 : ∀ u c → cof u ≡ c → ∀ {μ} → cofψ0 u c ≡ cΩ μ → VΩ (ψ u [] ∷ []) μ
vΩ₊ : ∀ u b c → cof b ≡ c → ∀ {μ} → cofA u c ≡ cΩ μ → VΩ (ψ u b ∷ []) μ
vΩc : ∀ u b ν → cof b ≡ cΩ ν → ∀ m → cmpᵀ (sucT ν) u ≡ m → ∀ {μ} → cofψ₊ u ν m ≡ cΩ μ →
      VΩ (ψ u b ∷ []) μ

vΩ [] ()
vΩ (x ∷ xs@(_ ∷ _)) e = ωs (vΩ xs e)
vΩ (ψ u b@(_ ∷ _) ∷ []) e = vΩ₊ u b (cof b) refl e
vΩ (ψ u@(_ ∷ _) [] ∷ []) e = vΩ0 u (cof u) refl e
vΩ (𝟏 ∷ []) ()

vΩ0 u c0 ue ()
vΩ0 u c1 ue refl = ωr ue
vΩ0 u cω ue ()
vΩ0 u (cΩ ν) ue refl = ωl ue (vΩ u ue)

vΩ₊ u b c0 be ()
vΩ₊ u b c1 be ()
vΩ₊ u b cω be ()
vΩ₊ u b (cΩ ν) be e = vΩc u b ν be (cmpᵀ (sucT ν) u) refl e

vΩc u b ν be lt m refl = ωp be (inj₁ m) (vΩ b be)
vΩc u b ν be eq m refl = ωp be (inj₂ m) (vΩ b be)
vΩc u b ν be gt m ()
```

沿视图的 Ω-基本列 $a[\eta]$, 与 EBO 的 `fsT` 逐点相等.

```agda
fΩ : ∀ {a μ} → VΩ a μ → T → T
fΩ (ωs {x = x} v) η     = x ∷ fΩ v η
fΩ (ωr _) η             = η
fΩ (ωl _ v) η           = ψ (fΩ v η) [] ∷ []
fΩ (ωp {u = u} _ _ v) η = ψ u (fΩ v η) ∷ []

fΩ-eq : ∀ {a μ} (v : VΩ a μ) η → fsT a η ≡ fΩ v η
fΩ-eq (ωs {x = x} v) η = cong (x ∷_) (fΩ-eq v η)
fΩ-eq (ωr {u = []} ()) η
fΩ-eq (ωr {u = w ∷ ws} e) η = cong (λ c → fsT0 (w ∷ ws) c η) e
fΩ-eq (ωl {u = []} _ ()) η
fΩ-eq (ωl {u = w ∷ ws} e v) η =
  trans (cong (λ c → fsT0 (w ∷ ws) c η) e) (cong (λ z → ψ z [] ∷ []) (fΩ-eq v η))
fΩ-eq (ωp {b = []} () _ _) η
fΩ-eq (ωp {u = u} {b = y ∷ ys} {μ = μ} be pen v) η =
  trans (cong (λ c → fsT₊ u (y ∷ ys) c η) be)
    (trans (fsTc-pen u (y ∷ ys) μ (cmpᵀ (sucT μ) u) pen η) (cong (λ z → ψ u z ∷ []) (fΩ-eq v η)))
```

**单调与非零** (对一切项, 不要标准形). $\eta_1<\eta_2\Rightarrow a[\eta_1]<a[\eta_2]$ (Lean `fs_mono`, Buchholz 3.2(b)); $\eta\ne0\Rightarrow a[\eta]\ne0$.

```agda
fΩ-mono : ∀ {a μ} (v : VΩ a μ) {η₁ η₂} → η₁ <ᵀ η₂ → fΩ v η₁ <ᵀ fΩ v η₂
fΩ-mono (ωs v) p     = tl< (fΩ-mono v p)
fΩ-mono (ωr _) p     = p
fΩ-mono (ωl _ v) p   = hd< (lv< (fΩ-mono v p))
fΩ-mono (ωp _ _ v) p = hd< (ar< (fΩ-mono v p))

fΩ-pos : ∀ {a μ} (v : VΩ a μ) {η} → [] <ᵀ η → [] <ᵀ fΩ v η
fΩ-pos (ωs v) p     = []<
fΩ-pos (ωr _) p     = p
fΩ-pos (ωl _ v) p   = []<
fΩ-pos (ωp _ _ v) p = []<
```

**γ-链** (Lean `tower`): $\gamma_0=\Omega_\mu$, $\gamma_{k+1}=\psi_\mu(b[\gamma_k])$. 与 EBO 的 `γT` 逐点相等; 每一级 $<\Omega_{\mu+1}$; 严格上升; 于是 $b[\gamma_k]$ 也严格上升.

```agda
γ : ∀ {b ν} → VΩ b ν → ℕ → T
γ {ν = ν} w zero    = Ωt ν
γ {ν = ν} w (suc k) = ψ ν (fΩ w (γ w k)) ∷ []

γ-eq : ∀ {b ν} (w : VΩ b ν) k → γT b ν k ≡ γ w k
γ-eq w zero = refl
γ-eq {b} {ν} w (suc k) =
  cong (λ z → ψ ν z ∷ []) (trans (cong (fsT b) (γ-eq w k)) (fΩ-eq w (γ w k)))

γ< : ∀ {b ν} (w : VΩ b ν) k → γ w k <ᵀ Ωs ν
γ< {ν = ν} w zero    = hd< (lv< (<-sucT ν))
γ< {ν = ν} w (suc k) = hd< (lv< (<-sucT ν))

γ-mono : ∀ {b ν} (w : VΩ b ν) k → γ w k <ᵀ γ w (suc k)
γ-mono w zero    = hd< (ar< (fΩ-pos w []<))
γ-mono w (suc k) = hd< (ar< (fΩ-mono w (γ-mono w k)))

val-mono : ∀ {b ν} (w : VΩ b ν) k → fΩ w (γ w k) <ᵀ fΩ w (γ w (suc k))
val-mono w k = fΩ-mono w (γ-mono w k)

val-le0 : ∀ {b ν} (w : VΩ b ν) k → fΩ w (γ w zero) ≤ᵀ fΩ w (γ w k)
val-le0 w zero    = inj₂ refl
val-le0 w (suc k) = ≤-trans′ (val-le0 w k) (inj₁ (val-mono w k))
```

**下标非零.** 视图里叶与穿透结点的下标非空 (Bachmann 一段的大小论证要它).

```agda
cof0  : ∀ b → NE b → cof b ≡ c0 → ⊥
cof0P : ∀ x → cofP x ≡ c0 → ⊥
cofA0 : ∀ u c → cofA u c ≡ c0 → ⊥
ψ0-0  : ∀ {u} c → cofψ0 u c ≡ c0 → c ≡ c0
cof0 (x ∷ []) ne e = cof0P x e
cof0 (x ∷ xs@(_ ∷ _)) ne e = cof0 xs ne e
cof0P (ψ u b@(_ ∷ _)) e = cofA0 u (cof b) e
cof0P (ψ u@(_ ∷ _) []) e = cof0 u ne (ψ0-0 (cof u) e)
cof0P (ψ [] []) ()
cofA0 u c0 ()
cofA0 u c1 ()
cofA0 u cω ()
cofA0 u (cΩ μ) e = go (cmpᵀ (sucT μ) u) e where
  go : ∀ m → cofψ₊ u μ m ≡ c0 → ⊥
  go lt ()
  go eq ()
  go gt ()
ψ0-0 c0 _ = refl
ψ0-0 c1 ()
ψ0-0 cω ()
ψ0-0 (cΩ _) ()

pen-ne : ∀ μ u → Pen (cmpᵀ (sucT μ) u) → NE u
pen-ne μ (_ ∷ _) _ = ne
pen-ne [] [] (inj₁ ())
pen-ne [] [] (inj₂ ())
pen-ne (_ ∷ _) [] (inj₁ ())
pen-ne (_ ∷ _) [] (inj₂ ())

reg-eq : ∀ {u} → cof u ≡ c1 → Ωs (pred u) ≡ ψ u [] ∷ []
reg-eq {u} e = cong (λ z → ψ z [] ∷ []) (pred-suc u e)

Ωs≤ : ∀ μ u → Pen (cmpᵀ (sucT μ) u) → Ωs μ ≤ᵀ (ψ u [] ∷ [])
Ωs≤ μ u pen with Pen→≤ (sucT μ) u pen
... | inj₁ p    = inj₁ (hd< (lv< p))
... | inj₂ refl = inj₂ refl
```

**标准形给出的两条.** $a$ 标准且共尾度 $\Omega_{\mu+1}$ 时, $\mu$ 标准 (Lean `OT_subOf_dom` 加上 `pred` 保标准形), $\mu+1<a$ (Lean `dom_le`).

```agda
nf-ν : ∀ {a μ} → NF a → VΩ a μ → NF μ
nf-ν n (ωs v)     = nf-ν (nf-tl n) v
nf-ν n (ωr _)     = nf-pred (nfp-u (nf-hd n))
nf-ν n (ωl _ v)   = nf-ν (nfp-u (nf-hd n)) v
nf-ν n (ωp _ _ v) = nf-ν (nfp-a (nf-hd n)) v

dom< : ∀ {a μ} → NF a → VΩ a μ → sucT μ <ᵀ a
dom< n (ωs {x = x} {y} {ys} v) = <ᵀ-trans (dom< (nf-tl n) v) (tail< x (y ∷ ys) (nf-le n) (nf-tl n))
dom< n (ωr {u = u} e) = subst (λ z → z <ᵀ (ψ u [] ∷ [])) (sym (pred-suc u e)) (idx< u [] [])
dom< n (ωl {u = u} e v) = <ᵀ-trans (dom< (nfp-u (nf-hd n)) v) (idx< u [] [])
dom< n (ωp {u = u} {b} {μ} be pen v) = ≤-< (Pen→≤ (sucT μ) u pen) (idx< u b [])
```

## §2 ω-视图

```agda
data Vω : T → Set where
  ws : ∀ {x y ys} → Vω (y ∷ ys) → Vω (x ∷ y ∷ ys)
  wl : ∀ {u} → cof u ≡ cω → Vω u → Vω (ψ u [] ∷ [])
  w4 : ∀ {u b} → cof b ≡ c1 → Vω (ψ u b ∷ [])
  w5 : ∀ {u b} → cof b ≡ cω → Vω b → Vω (ψ u b ∷ [])
  w6 : ∀ {u b ν} → cof b ≡ cΩ ν → cmpᵀ (sucT ν) u ≡ gt → VΩ b ν → Vω (ψ u b ∷ [])

vω  : ∀ t → cof t ≡ cω → Vω t
vω0 : ∀ u c → cof u ≡ c → cofψ0 u c ≡ cω → Vω (ψ u [] ∷ [])
vω₊ : ∀ u b → NE b → ∀ c → cof b ≡ c → cofA u c ≡ cω → Vω (ψ u b ∷ [])
vωc : ∀ u b ν → cof b ≡ cΩ ν → ∀ m → cmpᵀ (sucT ν) u ≡ m → cofψ₊ u ν m ≡ cω → Vω (ψ u b ∷ [])

vω [] ()
vω (x ∷ xs@(_ ∷ _)) e = ws (vω xs e)
vω (ψ u b@(_ ∷ _) ∷ []) e = vω₊ u b ne (cof b) refl e
vω (ψ u@(_ ∷ _) [] ∷ []) e = vω0 u (cof u) refl e
vω (𝟏 ∷ []) ()

vω0 u c0 ue ()
vω0 u c1 ue ()
vω0 u cω ue _ = wl ue (vω u ue)
vω0 u (cΩ μ) ue ()

vω₊ u b nb c0 be _ = ⊥-elim (cof0 b nb be)
vω₊ u b nb c1 be _ = w4 be
vω₊ u b nb cω be _ = w5 be (vω b be)
vω₊ u b nb (cΩ ν) be e = vωc u b ν be (cmpᵀ (sucT ν) u) refl e

vωc u b ν be lt m ()
vωc u b ν be eq m ()
vωc u b ν be gt m _ = w6 be m (vΩ b be)
```

沿视图的 ω-基本列 $t[n]$, 与 EBO 的 `fsn` 逐点相等. 规则 6 的 `fsn↓c` 走带证书的 `fsT↓`/`γ↓`, 由 EBO §6 的 `fsT↓-trm`, `γ↓-trm` 换成裸值, 再由 `γ-eq`, `fΩ-eq` 换成视图上的值.

```agda
fω : ∀ {t} → Vω t → ℕ → T
fω (ws {x = x} v) n       = x ∷ fω v n
fω (wl _ v) n             = ψ (fω v n) [] ∷ []
fω (w4 {u = u} {b} _) n   = replicate n (ψ u (pred b))
fω (w5 {u = u} _ v) n     = ψ u (fω v n) ∷ []
fω (w6 {u = u} _ _ w) n   = ψ u (fΩ w (γ w n)) ∷ []

fsn↓c-gt : ∀ u y ys ν (be : cof (y ∷ ys) ≡ cΩ ν) m → m ≡ gt → ∀ n →
           trm (fsn↓c u y ys ν be m n) ≡ ψ u (fsT (y ∷ ys) (γT (y ∷ ys) ν n)) ∷ []
fsn↓c-gt u y ys ν be .gt refl n =
  cong (λ z → ψ u z ∷ [])
       (trans (fsT↓-trm (y ∷ ys) be (dec (γ↓ (y ∷ ys) ν be n))) (cong (fsT (y ∷ ys)) (γ↓-trm (y ∷ ys) ν be n)))

fω-eq : ∀ {t} (v : Vω t) n → fsn t n ≡ fω v n
fω-eq (ws {x = x} v) n = cong (x ∷_) (fω-eq v n)
fω-eq (wl {u = []} () v) n
fω-eq (wl {u = w ∷ ws′} e v) n = trans (fsn0-eq w ws′ n e) (cong (λ z → ψ z [] ∷ []) (fω-eq v n))
fω-eq (w4 {b = []} ()) n
fω-eq (w4 {u = u} {b = y ∷ ys} e) n = trans (fsn₊-eq u y ys n e) (rep-trm u (pred-< (y ∷ ys) e) n)
fω-eq (w5 {b = []} () v) n
fω-eq (w5 {u = u} {b = y ∷ ys} e v) n =
  trans (fsn₊-eq u y ys n e) (cong (λ z → ψ u z ∷ []) (fω-eq v n))
fω-eq (w6 {b = []} () _ _) n
fω-eq (w6 {u = u} {b = y ∷ ys} {ν} be g w) n =
  trans (fsn₊-eq u y ys n be)
    (trans (fsn↓c-gt u y ys ν be (cmpᵀ (sucT ν) u) g n)
      (cong (λ z → ψ u z ∷ []) (trans (cong (fsT (y ∷ ys)) (γ-eq w n)) (fΩ-eq w (γ w n)))))
```
