# 极限高度 (二): 一切不含 Ω-极限的高度上严格增长

> 入口 [MonoPort7](MonoPort7.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 两种一步都是 $\Omega_k$ 在两个世界里的两次折叠的比较, 都由 `MonoPort7Node.ΩdObs` 给出:
>
> - **后继** `HtCrossVInst.Hs.MonoStep Λ`: 左边 $\Omega_\Lambda$ 在世界 $0$ 里经 `z⊲ one` 进入, 状态 `Y₀`; 右边 $\Omega_\Lambda$ 在世界 $1$ 里, 状态 `(Y₀ ⊕ Step Y₀) ⊕ 0`; 两边动作 `Act`, 良基证明 `accᴸ`. 层 $k = \Lambda$ (`monoS`). 这一步不再经 `MonoPortStep` 的外层链: 那条链就是 `ΩdObs` 里节点上升时的子层链.
> - **ℕ-极限** `HtCrossVInst.Hl.N.MonoL n`: 左边同上 (层 $f(n)$); 右边在世界 $1$ 里, 动作 `A²`, 良基证明 `accL (f n)`, 状态 `Rp n ⊕ 0`. 右边状态自洽 (`gRp`) 由 `nodeSelf` 对 `Rp` 的各段归纳; 底 $1\le\beta$ (`oneβ`).
>
> 两边的动作不看上下文的前提都是 `hSt` (`Act`, `A²` 在作用点上定义性地化成 `Step Y`).
>
> 结论: 对一切不含 Ω-极限的 $\Lambda$, $T_\Lambda < T_{\Lambda+1}$ (`Suc.growS`); 对一切 `hl f` (各 $f(n)$ 不含 Ω-极限), $T_{f(n)} < T_{\mathrm{hl}\,f}$ (`Lim.growL`). 于是在一切可数高度上 (`emb : A → H`) 沿严格序 $\ll$ 严格增长 (`grow≪`). 特例: $\omega$, $\omega+1$, $\omega\cdot 2$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort7Lim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; z⊲; Lg; _≪_)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (H; LgH; hz; hs; hl; hΩ; hself; hsuc; sl; z⊲ᴴ; accᴸ; _⊲[_]_; n0; n1; _⨾_; nl; nw; sum)
open import OCF.Align.HtFeedClosed using (one; TΛ)
open import OCF.Align.HtFeedHt using (emb; Lg-emb)
open import OCF.Align.MonoPort6Chain using (N; lgN; grow₀; _+ᴬ_)
import OCF.Align.HtCrossVInst as CV
open import OCF.Align.HtCrossVSim using (Free)
import OCF.Align.MonoPort7Rel as Rl
import OCF.Align.MonoPort7Node as Nd
```

## 1 后继一步, 一切不含 Ω-极限的高度

```agda
module Suc (Λ : H) (fΛ : Free Λ) (l : LgH Λ) where
  t₀ : hz ⊲[ one ] Λ
  t₀ = z⊲ᴴ Λ
  open Rl Λ l {one} tt t₀
  open Nd Λ l {one} tt t₀

  fH : ∀ k → Free k → Fin k
  fH hz _ = tt
  fH (hs b) x = fH b x
  fH (hl g) x = λ n → fH (g n) (x n)
  fH (hΩ _) ()

  z≼ : ∀ Δ → P.zeroD ≼ Δ
  z≼ Δ {t} tm = r0 t

  g0 : Good P.Y₀
  g0 = z≼ P.zeroD

  gL : Good (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀))
  gL = ⨾≼ {P.d P.Y₀} {P.Step P.Y₀} {P.d P.Y₀} {P.Step P.Y₀} g0 g0 g0
         (proj₂ (hSt Λ n0 n0 azero azero P.Y₀ P.Y₀ g0 g0 (≤-refl _ , g0) z≤))

  Yʳ₀ : P.St one
  Yʳ₀ = P._⊕⟨_⟩_ (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀)) tt P.zeroD

  gR₀ : Good Yʳ₀
  gR₀ = ⨾≼ {P.d (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀))} {P.zeroD} {P.d (P._⊕⟨_⟩_ P.Y₀ tt (P.Step P.Y₀))} {P.zeroD} gL gL gL (z≼ P.zeroD)

  monoS : CV.Hs.MonoStep Λ l
  monoS = proj₁ (ΩdObs Λ (fH Λ fΛ) hself aᴸ aᴸ (z⊲ one) C.self P.Act P.Act (hSt Λ) (hSt Λ) (hSt Λ)
                   n0 (n0 ⨾ nw C.self n0) one CV.b₀ P.Y₀ Yʳ₀ g0 gR₀ (z≤ , z≼ (P.d Yʳ₀)) (CV.sum≥ one (nl (λ _ → n1 ⨾ n0))))

  growS : asuc (TΛ Λ l) ≤ TΛ (hs Λ) l
  growS = CV.HsS.hs-reduce<′ Λ l fΛ monoS
```

## 2 ℕ-极限, 各项不含 Ω-极限

```agda
module Lim (f : ℕ → H) (l : LgH (hl f)) (ff : Free (hl f)) where
  Λ : H
  Λ = hl f
  t₀ : hz ⊲[ one ] Λ
  t₀ = z⊲ᴴ Λ
  open Rl Λ l {one} tt t₀
  open Nd Λ l {one} tt t₀
  module HL = CV.Hl f l
  open Suc Λ ff l using (fH; z≼; g0; gL)

  -- Rp 的状态都自洽: 每一步是层 hl f 上一个常数分支的节点
  gRp : ∀ m → Good (proj₂ (HL.Rp m))
  gRp zero = gL
  gRp (suc m) =
    ⨾≼ {P.d (proj₂ (HL.Rp m))} {P.Run accᴸ (HL.Fi m) (z⊲ one) tt hself P.Act (proj₁ (HL.Rp m)) (proj₂ (HL.Rp m))}
       {P.d (proj₂ (HL.Rp m))} {P.Run accᴸ (HL.Fi m) (z⊲ one) tt hself P.Act (proj₁ (HL.Rp m)) (proj₂ (HL.Rp m))}
       (gRp m) (gRp m) (gRp m)
       (nodeSelf (sl m hself) (fH (f m) (ff m)) (z⊲ one) hself P.Act (hSt Λ) (proj₁ (HL.Rp m)) (proj₂ (HL.Rp m)) (gRp m))

  oneβ : ∀ n → one ≤ HL.N.β n
  oneβ zero = CV.sum≥ one (nl (λ _ → n1 ⨾ n0))
  oneβ (suc n) = ≤-trans (oneβ n) (CV.sum≥ (HL.N.β n) (HL.d n))

  module M (n : ℕ) where
    Yʳ : P.St one
    Yʳ = P._⊕⟨_⟩_ (proj₂ (HL.Rp n)) tt P.zeroD

    gR : Good Yʳ
    gR = ⨾≼ {P.d (proj₂ (HL.Rp n))} {P.zeroD} {P.d (proj₂ (HL.Rp n))} {P.zeroD} (gRp n) (gRp n) (gRp n) (z≼ P.zeroD)

    monoL : HL.N.MonoL n
    monoL = proj₁ (ΩdObs (f n) (fH (f n) (ff n)) (HL.N.hk n) aᴸ aᴷ (z⊲ one) C.self P.Act (HL.N.A² n) (hSt (f n)) (hSt (f n)) (hSt (f n))
                     n0 (n0 ⨾ nw C.self n0) one (HL.N.β n) P.Y₀ Yʳ g0 gR (z≤ , z≼ (P.d Yʳ)) (oneβ n))

  monoL : ∀ n → HL.N.MonoL n
  monoL n = M.monoL n

  growL : ∀ n → asuc (TΛ (f n) (proj₂ l n)) ≤ TΛ (hl f) l
  growL n = CV.HlS.hl-reduce<′ f l n (ff n) (monoL n)
```

## 3 一切可数高度: 沿 $\ll$ 严格增长

`emb : A → H` 把树换成高度 (`HtFeedHt`), 不含 Ω-极限 (`free-emb`). $a \ll b$ 是 $A$ 上的严格序 (`CumReadCF`). 不同的合法性证明给出相同的值 (`lg-irr-emb`), 所以陈述对两边各取一个.

```agda
TE : ∀ a → Lg a → A
TE a la = TΛ (emb a) (Lg-emb a la)

le-s : ∀ a → a ≤ asuc a
le-s a = ⊲→≤ (C.suc C.self)

grow≪ : ∀ {a b} → a ≪ b → (lb : Lg b) (la : Lg a) → asuc (TE a la) ≤ TE b lb
grow≪ {a} C.zero lb la =
  ≤-trans (s≤ (proj₁ (CV.lg-irr-emb a (Lg-emb a la) (Lg-emb a lb)))) (Suc.growS (emb a) (CV.free-emb a) (Lg-emb a lb))
grow≪ {a} {asuc b} (C.suc r) lb la =
  ≤-trans (grow≪ r lb la) (≤-trans (le-s (TE b lb)) (Suc.growS (emb b) (CV.free-emb b) (Lg-emb b lb)))
grow≪ {a} {alim g} (C.lim n r) (st , lg) la =
  ≤-trans (grow≪ r (lg n) la)
    (≤-trans (le-s (TE (g n) (lg n)))
       (Lim.growL (λ m → emb (g m)) (Lg-emb (alim g) (st , lg)) (λ m → CV.free-emb (g m)) n))
```

## 4 特例: $\omega$, $\omega+1$, $\omega\cdot2$

```agda
finN : ∀ n → Free (N n)
finN zero = tt
finN (suc n) = finN n

lgω : LgH (hl N)
lgω = (λ n → hsuc hself) , lgN

-- 高度 ω 严格高于一切有限高度
growω : ∀ n → asuc (TΛ (N n) (lgN n)) ≤ TΛ (hl N) lgω
growω = Lim.growL N lgω finN

growω₀ : ∀ n → asuc (TΛ hz tt +ᴬ n) ≤ TΛ (hl N) lgω
growω₀ n = ≤-trans (s≤ (grow₀ n)) (growω n)

-- ω 到 ω+1
growω1 : asuc (TΛ (hl N) lgω) ≤ TΛ (hs (hl N)) lgω
growω1 = Suc.growS (hl N) finN lgω

-- ω+n 到 ω·2
ωp : ℕ → H
ωp zero = hl N
ωp (suc n) = hs (ωp n)

lgωp : ∀ n → LgH (ωp n)
lgωp zero = lgω
lgωp (suc n) = lgωp n

freeωp : ∀ n → Free (ωp n)
freeωp zero = finN
freeωp (suc n) = freeωp n

lgω2 : LgH (hl ωp)
lgω2 = (λ n → hsuc hself) , lgωp

growω2 : ∀ n → asuc (TΛ (ωp n) (lgωp n)) ≤ TΛ (hl ωp) lgω2
growω2 = Lim.growL ωp lgω2 freeωp
```
