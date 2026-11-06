# WfScoutTau: EBO 到 OT_I 的翻译 τ, 严格保序与端点之下

> 侦察实验 (报告在 [NotationWF](../../Survey/NotationWF.md)). 记号侧, 读记号, 不进成品.
>
> 1. **τ 严格保序, 对全部项, 不要标准形 (`τ-mono`).** $s<^\mathsf T t\Rightarrow\tau s\prec\tau t$, 其中 $\prec$ 是归档 Setzer OT_I 的 `lt`. 证明只用归档里已证的序论 (Lemma 2.4 的线性、传递, `Lex` 的 $+1$ 引理), 对 `_<ᵀ_` 的推导结构递归. 这是手册 §6.1 的义务 2.
> 2. **可数项在端点之下 (`τ-bd`).** 每个项 $\tau t\prec I$ (`τ≺I`), 所以可数项 (`Ctbl`) 满足 $\tau t\prec\psi_{\Omega_1}(\Omega_{I+1})$ = `endpt 1`. 这是义务 5.
> 3. **没有做的: 义务 3 (τ 保标准形, `isOTᵉ t → OT (τ t)`).** 只有有限测试 (§3).
>
> 归档文件是 `--safe --cubical-compatible`, 要 `--hidden-argument-puns`; 编译本文件要把归档 (或其拷贝) 加进 `-i`, 见报告. 本文件 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WfScoutTau where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import OCF.Align.EBO as E
open E using (_<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.EBOI using (isOTᵉ)

open import Mahlo.Inacc.Syntax using (Tm; PTm; zer; _▹_; ⟨_⟩; phi; psi; Om; I; ΩR; one; eqT; eqP; toList; NZ)
open import Mahlo.Inacc.Order using (lt; le; _≺_; lt!)
open import Mahlo.Inacc.Closure using (isOT; OT; ot!)
open import Mahlo.Inacc.BoolLemmas using (∨-true; ∨-introˡ; ∨-introʳ; ∧-intro; if-true; eqP-refl; eqR-refl; eqT-sound)
open import Mahlo.Inacc.OrderProps using (ltLx; lt-list)
open import Mahlo.Inacc.Unfold using (ltP′; lt-unfold≠)
open import Mahlo.Inacc.Linear using (AT-all; lin″; ≺⇒eqT-false)
open import Mahlo.Inacc.Trans using (lt-trans)
open import Mahlo.Inacc.Lex using (fromL; toList-fromL; fromL-NZ; ltLx-sing⁻; ≺-▹; +1-least′; +one; one≺P;
  ≺-sing-▹; lt-zer; leˡ; leʳ)
open import Mahlo.Inacc.Theorem using (endpt)
open import Mahlo.Inacc.FactsImpl using (facts)
import Mahlo.Inacc.WO.Main facts as M
```

## §1 τ

手册 §3 的映射, 与 `probes/Survey/scripts/eboi/SetzerTest.agda` 的 `τP` 相同 (那里还有 $\psi_I$, $I$): $\tau(\mathbf 1)=\varphi'_00$, $\tau(\psi_u(0))=\Omega'_{\tau u}$ ($u\ne0$), $\tau(\psi_u(a))=\psi_{\Omega'_{\tau u+1}}(\tau a)$ ($a\ne0$). 和逐项翻译; Setzer 的和是 snoc 表, 经 `fromL`. 子句先按参数分 (第一行), 这样 $\tau(\psi_v(a))$ 在 $a\ne0$ 时对未知的 $v$ 也能归约.

```agda
φ1 : PTm
φ1 = phi zer zer

τL : E.T → List PTm
τP : E.PT → PTm
τ  : E.T → Tm
τ t = fromL (τL t)
τL [] = []
τL (x ∷ xs) = τP x ∷ τL xs
τP (E.ψ u (y ∷ ys)) = psi (ΩR (τ u ▹ φ1)) (τ (y ∷ ys))
τP (E.ψ [] []) = φ1
τP (E.ψ (w ∷ ws) []) = Om (τ (w ∷ ws))

lt-τ : ∀ s t → lt (τ s) (τ t) ≡ ltLx (τL s) (τL t)
lt-τ s t = trans (lt-list (τ s) (τ t)) (subst (λ z → ltLx z (toList (τ t)) ≡ ltLx (τL s) (τL t)) (sym (toList-fromL (τL s)))
                                         (cong (ltLx (τL s)) (toList-fromL (τL t))))
```

## §2 严格保序

小引理, 全在 Setzer 的序上: $\Omega'$ 保序, $x<y\Rightarrow x+1\le y$, $x<y\Rightarrow x+1<y+1$.

```agda
notle : ∀ s t → lt s t ≡ true → le t s ≡ false
notle s t h = trans (lin″ s t (AT-all s t)) (cong not h)

Ωlt : ∀ a c → lt a c ≡ true → lt ⟨ Om a ⟩ ⟨ Om c ⟩ ≡ true
Ωlt a c h = trans (lt-unfold≠ (Om a) (Om c) (≺⇒eqT-false a c (AT-all a c) h)) h

Ωle : ∀ a c → le a c ≡ true → le ⟨ Om a ⟩ ⟨ Om c ⟩ ≡ true
Ωle a c h with ∨-true h
... | inj₁ l = leˡ ⟨ Om a ⟩ ⟨ Om c ⟩ (Ωlt a c l)
... | inj₂ e = leʳ ⟨ Om a ⟩ ⟨ Om c ⟩ e

s1≤ : ∀ x y → lt x y ≡ true → le (x ▹ φ1) y ≡ true
s1≤ x y h = subst (λ z → le z y ≡ true) (+one x) (+1-least′ x y h)

le-lt : ∀ a b c → le a b ≡ true → lt b c ≡ true → lt a c ≡ true
le-lt a b c h g with ∨-true h
... | inj₁ l = lt-trans a b c l g
... | inj₂ e = subst (λ z → lt z c ≡ true) (sym (eqT-sound a b e)) g

s1< : ∀ x y → lt x y ≡ true → lt (x ▹ φ1) (y ▹ φ1) ≡ true
s1< x y h = le-lt (x ▹ φ1) y (y ▹ φ1) (s1≤ x y h) (≺-▹ y φ1)

eqT-ne : ∀ a c → lt a c ≡ true → eqT a c ≡ false
eqT-ne a c h = ≺⇒eqT-false a c (AT-all a c) h
```

主定理. `monoP` 按两端的形状 (下标、参数是否为空) 分情形, 每支落到 (≺′4)–(≺′11) 的一条.

```agda
τ-lt  : ∀ {s t} → s <ᵀ t → lt (τ s) (τ t) ≡ true
mono  : ∀ {s t} → s <ᵀ t → ltLx (τL s) (τL t) ≡ true
monoP : ∀ {x y} → x <ᴾ y → lt ⟨ τP x ⟩ ⟨ τP y ⟩ ≡ true

τ-lt {s} {t} q = trans (lt-τ s t) (mono q)

mono []< = refl
mono (hd< {x} {y} {xs} {ys} p) = ltLx-sing⁻ (τP x) (τL xs) (τP y) (τL ys) (monoP p)
mono (tl< {x} q) = trans (if-true (eqP-refl (τP x))) (mono q)

-- 下标严格增
monoP {E.ψ [] []} {E.ψ (w ∷ ws) []} (lv< []<) = one≺P (Om (τ (w ∷ ws))) refl
monoP {E.ψ [] []} {E.ψ (w ∷ ws) (y ∷ ys)} (lv< []<) = one≺P (psi (ΩR (τ (w ∷ ws) ▹ φ1)) (τ (y ∷ ys))) refl
monoP {E.ψ (u ∷ us) []} {E.ψ (v ∷ vs) []} (lv< q) = Ωlt (τ (u ∷ us)) (τ (v ∷ vs)) (τ-lt q)
monoP {E.ψ (u ∷ us) []} {E.ψ v (y ∷ ys)} (lv< q) =
  trans (lt-unfold≠ (Om U) (psi (ΩR (V ▹ φ1)) (τ (y ∷ ys))) refl)
        (cong not (notle ⟨ Om U ⟩ ⟨ Om (V ▹ φ1) ⟩ (Ωlt U (V ▹ φ1) (lt-trans U V (V ▹ φ1) (τ-lt q) (≺-▹ V φ1)))))
  where U = τ (u ∷ us); V = τ v
monoP {E.ψ u (a ∷ as)} {E.ψ (v ∷ vs) []} (lv< q) =
  trans (lt-unfold≠ (psi (ΩR (τ u ▹ φ1)) (τ (a ∷ as))) (Om (τ (v ∷ vs))) refl)
        (Ωle (τ u ▹ φ1) (τ (v ∷ vs)) (s1≤ (τ u) (τ (v ∷ vs)) (τ-lt q)))
monoP {E.ψ u (a ∷ as)} {E.ψ v (y ∷ ys)} (lv< q) =
  trans (lt-unfold≠ (psi π A) (psi κ B) e)
        (∨-introʳ {x = eqT (τ u ▹ φ1) (τ v ▹ φ1) ∧ lt A B} (∨-introˡ (Ωlt (τ u ▹ φ1) (τ v ▹ φ1) (s1< (τ u) (τ v) (τ-lt q)))))
  where
    π = ΩR (τ u ▹ φ1); κ = ΩR (τ v ▹ φ1); A = τ (a ∷ as); B = τ (y ∷ ys)
    e : eqP (psi π A) (psi κ B) ≡ false
    e = cong (λ z → (z ∧ eqP φ1 φ1) ∧ eqT A B) (eqT-ne (τ u) (τ v) (τ-lt q))
-- 下标相同, 参数严格增
monoP {E.ψ [] []} {E.ψ [] (y ∷ ys)} (ar< q) = one≺P (psi (ΩR (zer ▹ φ1)) (τ (y ∷ ys))) refl
monoP {E.ψ (u ∷ us) []} {E.ψ _ (y ∷ ys)} (ar< q) =
  trans (lt-unfold≠ (Om U) (psi (ΩR (U ▹ φ1)) (τ (y ∷ ys))) refl)
        (cong not (notle ⟨ Om U ⟩ ⟨ Om (U ▹ φ1) ⟩ (Ωlt U (U ▹ φ1) (≺-▹ U φ1))))
  where U = τ (u ∷ us)
monoP {E.ψ u (a ∷ as)} {E.ψ _ (y ∷ ys)} (ar< q) =
  trans (lt-unfold≠ (psi π A) (psi π B) e) (∨-introˡ (∧-intro (eqR-refl π) (τ-lt q)))
  where
    π = ΩR (τ u ▹ φ1); A = τ (a ∷ as); B = τ (y ∷ ys)
    e : eqP (psi π A) (psi π B) ≡ false
    e = trans (cong (λ z → z ∧ eqT A B) (eqR-refl π)) (eqT-ne A B (τ-lt q))

τ-mono : ∀ {s t} → s <ᵀ t → τ s ≺ τ t
τ-mono q = lt! (τ-lt q)
```

**可数项在端点之下.** 先证一切 $\tau t\prec I$: 和看首项, $\varphi'_00\prec I$, $\Omega'_x\prec I\Leftarrow x\prec I$, $\psi_{\Omega'_{x+1}}(\cdot)\prec I\Leftarrow x+1\prec I$. 再用 $I\prec\Omega'_{I+1}$ (闭项, `refl`).

```agda
τ≺I  : ∀ t → lt (τ t) ⟨ I ⟩ ≡ true
τP≺I : ∀ x → lt ⟨ τP x ⟩ ⟨ I ⟩ ≡ true
s1≺I : ∀ u → lt (τ u ▹ φ1) ⟨ I ⟩ ≡ true
τ≺I [] = lt-zer zer I
τ≺I (x ∷ xs) = trans (lt-list (τ (x ∷ xs)) ⟨ I ⟩)
  (trans (cong (λ z → ltLx z (I ∷ [])) (toList-fromL (τL (x ∷ xs)))) (ltLx-sing⁻ (τP x) (τL xs) I [] (τP≺I x)))
τP≺I (E.ψ [] []) = one≺P I refl
τP≺I (E.ψ (w ∷ ws) []) = trans (lt-unfold≠ (Om (τ (w ∷ ws))) I refl) (τ≺I (w ∷ ws))
τP≺I (E.ψ u (y ∷ ys)) =
  trans (lt-unfold≠ (psi (ΩR (τ u ▹ φ1)) (τ (y ∷ ys))) I refl)
        (leˡ ⟨ Om (τ u ▹ φ1) ⟩ ⟨ I ⟩ (trans (lt-unfold≠ (Om (τ u ▹ φ1)) I refl) (s1≺I u)))
s1≺I [] = one≺P I refl
s1≺I (w ∷ ws) = ≺-sing-▹ (τ (w ∷ ws)) φ1 I (fromL-NZ (τP w) (τL ws)) (τ≺I (w ∷ ws))

Ω* : Tm
Ω* = M.ΩI+ 1

I≺Ω* : lt ⟨ I ⟩ Ω* ≡ true
I≺Ω* = refl

τ-bdᵇ : ∀ {t} → Ctbl t → lt (τ t) (endpt 1) ≡ true
τ-bdᵇ c[] = lt-zer zer (psi (ΩR one) Ω*)
τ-bdᵇ (c∷ {a} {xs} c) = trans (lt-list (τ (E.ψ [] a ∷ xs)) (endpt 1))
  (trans (cong (λ z → ltLx z (psi (ΩR one) Ω* ∷ [])) (toList-fromL (τL (E.ψ [] a ∷ xs))))
         (ltLx-sing⁻ (τP (E.ψ [] a)) (τL xs) (psi (ΩR one) Ω*) [] (h a)))
  where
    h : ∀ a → lt ⟨ τP (E.ψ [] a) ⟩ ⟨ psi (ΩR one) Ω* ⟩ ≡ true
    h [] = one≺P (psi (ΩR one) Ω*) refl
    h (y ∷ ys) = trans (lt-unfold≠ (psi (ΩR one) A) (psi (ΩR one) Ω*) e) (∨-introˡ (∧-intro (eqR-refl (ΩR one)) l))
      where
        A = τ (y ∷ ys)
        l : lt A Ω* ≡ true
        l = lt-trans A ⟨ I ⟩ Ω* (τ≺I (y ∷ ys)) I≺Ω*
        e : eqP (psi (ΩR one) A) (psi (ΩR one) Ω*) ≡ false
        e = trans (cong (λ z → z ∧ eqT A Ω*) (eqR-refl (ΩR one))) (eqT-ne A Ω* l)

τ-bd : ∀ {t} → Ctbl t → τ t ≺ endpt 1
τ-bd c = lt! (τ-bdᵇ c)
```

## §3 有限测试 (不是证明)

义务 3 只有测试: Ω-塔 `EBOψ k` 是 EBO 标准形, 其 τ-像在 OT 里; 链的 τ-像递增, 在端点之下.

```agda
_ : isOTᵉ (E.EBOψ 3) ≡ true
_ = refl

_ : isOT (τ (E.EBOψ 3)) ≡ true
_ = refl

_ : lt (τ (E.EBOψ 2)) (τ (E.EBOψ 3)) ≡ true
_ = refl

_ : lt (τ (E.EBOψ 3)) (endpt 1) ≡ true
_ = refl
```
