# 结构关系, 第九轮 (二): 树世界处也带领先量的语义, 带前段对齐的 `nw`

> 入口见 [StrRel9](StrRel9.lagda.md). 不读记号.
>
> `StrRel8Neg.¬nwˡ` 说: 不带底部前段对齐的 `nw` 规则不可靠. `cv` 产生的 `nw` 两边的前段是 `sum-fst U z` 与 `sum-fst U′ z′`, $z\sqsubseteq^{\mathsf P}z'$, 这正是 `StrRel4Pr.genᴾ` 能生成对齐的形状, 但 `genᴾ` 要领先量 $\mathrm{Adm}(\Sigma U z,\Sigma U' z';L,L')$, 而 `SemS` 不带它. 本文:
>
> 1. 语义 `SemL lV lV′ x x′` = `StrRel7Snd.SemS` 加三条前提: **树世界处的领先量** $\mathrm{Adm}(V,V';W,W')$ ($V,V'$ 树世界, $W,W'$ 运行世界), 与两条 **`Lg` 等式** `lV ≡ lg⊲ q lW` (树世界处的极限结构就是运行路径带下来的那个; 拼接 `cat` 要它).
> 2. 关系 `Le lV lV′ x x′` = $\sqsubseteq^{+}$ 的九个构造子 (按 `Lg` 下标) + **`nwΣᴸ`**: $U\le U'$, $z\sqsubseteq^{\mathsf P}z'$, `Le lU lU′ x x′` ⇒ `Le (Lg-sum U z lU) (Lg-sum U′ z′ lU′) (nw (sum-fst U z) x) (nw (sum-fst U′ z′) x′)`.
> 3. **`sndᴸ`**: `Le lV lV′ x x′ → SemL lV lV′ x x′`, 对推导归纳一个证明, 无参数, 含嵌套 `nκ`, 对一切深度. 新前提在每个递归调用处都由折叠的字面给出: `nκ` 的格里由对齐的 `aP` 所带的领先量与走法的 `Lg` 等式 (`StrRel9Walk`), `ni` 的分支在 `self` 上 (`adm-self`, `refl`), `tr` 的左左比较由 `split`, 右边 `nw` 由领先量对右树世界反单调 (`adm-lo`).
> 4. `emb⁺`: 旧关系 $\sqsubseteq^{+}$ 在一切下标处嵌入 `Le`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel9Snd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl; ≤-trans; ⊲→≤; ⊞-mono)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; sum; sum-fst; Lg-sum; kk)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁; toV0)
open import OCF.Align.KNestAdm using (Adm; adm-tr; split)
open import OCF.Align.KNestSound using (adv-sum)
open import OCF.Align.StrRel4Walk using (Al; aS)
open import OCF.Align.StrRel4Gen using (Al-map; lg-tr; lgsf; cat; adm-self)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; sq; lm; tr; pr; vsᴾ; alSuccᴾ; alZeroᴾ; genᴾ)
open import OCF.Align.StrRel5Walk using (Env)
open import OCF.Align.StrRel5Suf using (rfx)
open import OCF.Align.StrRel5Nest using (stepA; E; OA; R∀; advA; cvR; stepR; drpR)
open import OCF.Align.StrRel7Coh using (Ch; coh₁; cA-step; alR)
open import OCF.Align.StrRel7Walk using (cohWlk)
open import OCF.Align.StrRel7Zero using (AR; cohᴬ; snd0)
open import OCF.Align.StrRel7Snd using (_⊑⁺_; n0⁺; n1⁺; ⨾⁺; nl⁺; nwʳ⁺; pr⁺; κ⁺; ni⁺; tr⁺)
open import OCF.Align.StrRel9Walk using (module GoD)
```

## 1 关系

下标 `lV`, `lV′` 是两边树世界处的极限结构. 除 `nwʳᴸ` (内层下标是 `lg⊲ p lV′`), `κᴸ`, `niᴸ` (分支的下标是分支自己的 `lc`), `nwΣᴸ` 外, 构造子不动下标.

```agda
data Le : ∀ {V V′} → Lg V → Lg V′ → D one V → D one V′ → Set where
  n0ᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D one V′} → Le lV lV′ n0 x
  n1ᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} → Le lV lV′ n1 n1
  ⨾ᴸ   : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D one V} {x′ y′ : D one V′} →
         Le lV lV′ x x′ → Le lV lV′ y y′ → Le lV lV′ (x ⨾ y) (x′ ⨾ y′)
  nlᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} →
         (∀ n → Le lV lV′ (d n) (d′ n)) → Le lV lV′ (nl d) (nl d′)
  nwʳᴸ : ∀ {V₀ V V′} {lV : Lg V} {lV′ : Lg V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} →
         Le lV (lg⊲ p lV′) x x′ → Le lV lV′ x (nw p x′)
  prᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D one V} {x′ y′ : D one V′} → Le lV lV′ x x′ → Le lV lV′ x (x′ ⨾ y′)
  κᴸ   : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {zz zz′} {u : ∀ {c} → V ⊲ c → Lg c → D one c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D one c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → Le lc lc′ (u p lc) (u′ p′ lc′)) →
         Le lV lV′ (nκ zz u) (nκ zz′ u′)
  niᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {u : ∀ {c} → V ⊲ c → Lg c → D azero c → D one c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D azero c → D one c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → ∀ {z z′} → z ⊑ᴾ z′ → Le lc lc′ (u p lc z) (u′ p′ lc′ z′)) →
         (∀ {c} (p : V ⊲ c) (lc : Lg c) → ∀ {z z″} → z ⊑ᴾ z″ → Le lc lc (u p lc z) (u p lc z″)) →
         Le lV lV′ (ni (C.ss C.self) u) (ni (C.ss C.self) u′)
  trᴸ  : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x y : D one V} {z : D one V′} → Le lV lV x y → Le lV lV′ y z → Le lV lV′ x z
  -- 新: 两边都由 cv 形状的前段包住
  nwΣᴸ : ∀ {U U′ Z Z′} {lU : Lg U} {lU′ : Lg U′} {z : D azero Z} {z′ : D azero Z′} {x : D one U} {x′ : D one U′} →
         U ≤ U′ → z ⊑ᴾ z′ → Le lU lU′ x x′ →
         Le (Lg-sum U z lU) (Lg-sum U′ z′ lU′) (nw (sum-fst U z) x) (nw (sum-fst U′ z′) x′)

SemL : ∀ {V V′} → Lg V → Lg V′ → D one V → D one V′ → Set
SemL {V} {V′} lV lV′ x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (l₁ : one ⊲ W) (l₁′ : one ⊲ W′) → W ≤ W′ →
  ∀ (q : V ⊲ W) (q′ : V′ ⊲ W′) → Al W W′ q lW q′ lW′ → lV ≡ lg⊲ q lW → lV′ ≡ lg⊲ q′ lW′ → Adm V V′ W W′ →
  ∀ w w′ (Y : F.St W) (Y′ : F.St W′) → Ch Y → R∀ Y Y′ →
  OA (F.Run ac₁ x q lW l₁ stepA w Y) (F.Run ac₁ x′ q′ lW′ l₁′ stepA w′ Y′)
```

## 2 两条小引理

右边树世界降低, 领先量仍在 (`Adm` 对右边的起点反单调). 前段拼上运行路径后, 内层树世界处的 `Lg` 等式由 `lgsf` 给出.

```agda
adm-lo : ∀ {V V₀ V′ W W′} → V₀ ⊲ V′ → Adm V V′ W W′ → Adm V V₀ W W′
adm-lo p (δ , h , h′) = δ , h , ≤-trans (⊞-mono (⊲→≤ p) (≤-refl δ)) h′

eq-nw : ∀ {U Z W} (z : D azero Z) (lU : Lg U) (q : sum U z ⊲ W) (lW : Lg W) →
        Lg-sum U z lU ≡ lg⊲ q lW → lU ≡ lg⊲ (⊲-tr (sum-fst U z) q) lW
eq-nw {U} z lU q lW e =
  trans (sym (lgsf U z lU)) (trans (cong (lg⊲ (sum-fst U z)) e) (sym (lg-tr (sum-fst U z) q lW)))

eq-r : ∀ {V₀ V′ W′} (p : V₀ ⊲ V′) (q′ : V′ ⊲ W′) (lV′ : Lg V′) (lW′ : Lg W′) →
       lV′ ≡ lg⊲ q′ lW′ → lg⊲ p lV′ ≡ lg⊲ (⊲-tr p q′) lW′
eq-r p q′ lV′ lW′ e = trans (cong (lg⊲ p) e) (sym (lg-tr p q′ lW′))
```

## 3 可靠性

与 `StrRel7Snd.snd⁺` 逐句对应; 多出的三条前提原样往下传, 或在调用处由折叠的字面给出. 新的一句是 `nwΣᴸ`.

```agda
sndᴸ : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D one V} {x′ : D one V′} → Le lV lV′ x x′ → SemL lV lV′ x x′
sndᴸ n0ᴸ lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′ = z0
sndᴸ n1ᴸ lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r = stepR {Y = Y} {Y′ = Y′} r
sndᴸ (⨾ᴸ {x = x} {x′ = x′} hx hy) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′ =
  sq (Ox τ τ′) (sndᴸ hy lW lW′ l₁ l₁′ le q q′ hq e e′ ad (w ⨾ nw q x) (w′ ⨾ nw q′ x′) _ _
                     (advA {Y = Y} {Y′ = Y} Δ Δ c (coh₁ ac₁ x q lW l₁ stepA cA-step w Y c))
                     (advA {Y = Y} {Y′ = Y′} Δ Δ′ r Ox) τ τ′)
  where
  Δ = F.Run ac₁ x q lW l₁ stepA w Y
  Δ′ = F.Run ac₁ x′ q′ lW′ l₁′ stepA w′ Y′
  Ox = sndᴸ hx lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r
sndᴸ (nlᴸ {d = d} {d′} hd) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′ = lm (λ n → proj₁ (go n) τ τ′)
  where
  P = λ n → F.Rpt ac₁ d q lW l₁ stepA w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ lW′ l₁′ stepA w′ Y′ n
  Δ = λ n → F.Run ac₁ (d n) q lW l₁ stepA (proj₁ (P n)) (proj₂ (P n))
  Δ′ = λ n → F.Run ac₁ (d′ n) q′ lW′ l₁′ stepA (proj₁ (P′ n)) (proj₂ (P′ n))
  st : ∀ n → Ch (proj₂ (P n)) × R∀ (proj₂ (P n)) (proj₂ (P′ n))
  go : ∀ n → OA (Δ n) (Δ′ n) × Ch (proj₂ (P n)) × R∀ (proj₂ (P n)) (proj₂ (P′ n))
  go n = sndᴸ (hd n) lW lW′ l₁ l₁′ le q q′ hq e e′ ad _ _ _ _ (proj₁ (st n)) (proj₂ (st n)) , st n
  st zero = c , r
  st (suc n) =
    advA {Y = proj₂ (P n)} {Y′ = proj₂ (P n)} (Δ n) (Δ n) (proj₁ (st n)) (coh₁ ac₁ (d n) q lW l₁ stepA cA-step _ _ (proj₁ (st n))) ,
    advA {Y = proj₂ (P n)} {Y′ = proj₂ (P′ n)} (Δ n) (Δ′ n) (proj₂ (st n)) (proj₁ (go n))
sndᴸ (nwʳᴸ {lV′ = lV′} {p = p} h) lW lW′ l₁ l₁′ le q q′ hq e e′ ad =
  sndᴸ h lW lW′ l₁ l₁′ le q (⊲-tr p q′) (rfx p hq) e (eq-r p q′ lV′ lW′ e′) (adm-lo p ad)
sndᴸ (prᴸ h) lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′ =
  pr (sndᴸ h lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′)
sndᴸ (trᴸ hxy hyz) {W} lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′ =
  tr (sndᴸ hxy lW lW l₁ l₁ (≤-refl W) q q (alR lW W q lW C.self) e e (split q lW) w w Y Y c c τ τ)
     (sndᴸ hyz lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′)
sndᴸ (nwΣᴸ {U} {U′} {lU = lU} {lU′} {z} {z′} hU hz h) lW lW′ l₁ l₁′ le q q′ hq e e′ ad =
  sndᴸ h lW lW′ l₁ l₁′ le (⊲-tr (sum-fst U z) q) (⊲-tr (sum-fst U′ z′) q′)
       (cat (genᴾ hz lU lU′ hU ad) hq e e′) (eq-nw z lU q lW e) (eq-nw z′ lU′ q′ lW′ e′)
       (adm-tr (adv-sum z z′ (adm-self U U′) (toV0 z z′ (vsᴾ hz z≤))) ad)
sndᴸ {V} {V′} (κᴸ {u = u} {u′} h) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′ = lm (λ n → drpR (cell n))
  where
  cL : ℕ → F.Cl W V (cnt one)
  cL = F.κc ac₁ u q lW l₁ stepA w Y
  cR : ℕ → F.Cl W′ V′ (cnt one)
  cR = F.κc ac₁ u′ q′ lW′ l₁′ stepA w′ Y′
  eL : ℕ → Env
  eL n = E (F.v (cL n)) (F.lv (cL n)) (⊲-tr l₁ (F.wv (cL n)))
  eR : ℕ → Env
  eR n = E (F.v (cR n)) (F.lv (cR n)) (⊲-tr l₁′ (F.wv (cR n)))
  ΔL : ∀ n → F.Df (F.v (cL n))
  ΔL n = F.κΔ ac₁ u l₁ stepA (cL n)
  ΔR : ∀ n → F.Df (F.v (cR n))
  ΔR n = F.κΔ ac₁ u′ l₁′ stepA (cR n)

  St : ℕ → Set
  St n = (F.v (cL n) ≤ F.v (cR n)) × Al (F.v (cL n)) (F.v (cR n)) (F.av (cL n)) (F.lv (cL n)) (F.av (cR n)) (F.lv (cR n)) ×
         Ch (F.Sv (cL n)) × R∀ (F.Sv (cL n)) (F.Sv (cR n))

  out : ∀ n → St n → OA (ΔL n) (ΔR n)
  out n (vle , H , cs , rs) =
    GoD.cellᵈ (eL n) (eR n) cA-step u u′ (λ Y₂ Y₂′ → Ch Y₂ × R∀ Y₂ Y₂′) proj₁
      (λ {Y₂} {Y₂′} Δ Δ′ cr O Os → advA {Y = Y₂} {Y′ = Y₂} Δ Δ (proj₁ cr) Os , advA {Y = Y₂} {Y′ = Y₂′} Δ Δ′ (proj₂ cr) O)
      (λ p p′ lc lc′ c≤ ad₁ q₁ q₁′ hq₁ e₁ e₁′ w₁ w₁′ Y₁ Y₁′ cr →
         sndᴸ (h p p′ lc lc′ c≤) (F.lv (cL n)) (F.lv (cR n)) (⊲-tr l₁ (F.wv (cL n))) (⊲-tr l₁′ (F.wv (cR n))) vle
              q₁ q₁′ hq₁ e₁ e₁′ ad₁ w₁ w₁′ Y₁ Y₁′ (proj₁ cr) (proj₂ cr))
      H (F.ap (cL n)) (F.ap (cR n)) (F.co (cL n)) (F.co (cR n)) (F.Sv (cL n)) (F.Sv (cR n)) (cs , rs)

  st0 : St zero
  st0 = vsᴾ (proj₂ r) le ,
        alZeroᴾ lW lW′ (Al-map (λ ad₂ → adv-sum (F.z Y) (F.z Y′) ad₂ (toV0 (F.z Y) (F.z Y′) (vsᴾ (proj₂ r) z≤))) hq) (proj₂ r) le ,
        cvR (sum-fst W (F.z Y)) (F.lv (cL zero)) (sum-fst W (F.z Y)) (F.lv (cL zero)) Y Y c ,
        cvR (sum-fst W (F.z Y)) (F.lv (cL zero)) (sum-fst W′ (F.z Y′)) (F.lv (cR zero)) Y Y′ r

  stS : ∀ n → St n → St (suc n)
  stS n st@(vle , H , cs , rs) =
    vsᴾ dr vle , alSuccᴾ dr (F.lv (cL n)) (F.lv (cR n)) vle ,
    cvR qL (F.lv (cL (suc n))) qL (F.lv (cL (suc n))) (F.Sv (cL n) F.⊕ ΔL n) (F.Sv (cL n) F.⊕ ΔL n)
        (advA {Y = F.Sv (cL n)} {Y′ = F.Sv (cL n)} (ΔL n) (ΔL n) cs
              (cohWlk (eL n) cA-step u (F.v (cL n)) (F.av (cL n)) (F.ap (cL n)) (F.lv (cL n)) C.self (F.co (cL n)) (F.Sv (cL n)) cs)) ,
    cvR qL (F.lv (cL (suc n))) (sum-fst (F.v (cR n)) (F.yc (ΔR n) (inj₁ (z⊲ (F.v (cR n)))) tt)) (F.lv (cR (suc n)))
        (F.Sv (cL n) F.⊕ ΔL n) (F.Sv (cR n) F.⊕ ΔR n) (advA {Y = F.Sv (cL n)} {Y′ = F.Sv (cR n)} (ΔL n) (ΔR n) rs O)
    where
    O = out n st
    dr = O (inj₁ (z⊲ (F.v (cL n)))) (inj₁ (z⊲ (F.v (cR n))))
    qL = sum-fst (F.v (cL n)) (F.yc (ΔL n) (inj₁ (z⊲ (F.v (cL n)))) tt)

  go : ∀ n → St n
  go zero = st0
  go (suc n) = stS n (go n)

  cell : ∀ n → F.yc (ΔL n) (inj₁ (z⊲ (F.v (cL n)))) tt ⊑ᴾ F.yc (ΔR n) (inj₁ (z⊲ (F.v (cR n)))) tt
  cell n = out n (go n) (inj₁ (z⊲ _)) (inj₁ (z⊲ _))
sndᴸ {V} {V′} (niᴸ {u = u} {u′} h hs) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq e e′ ad w w′ Y Y′ c r τ τ′ =
  go (F.rkT kW τ lW) (F.rkT kW′ τ′ lW′)
  where
  Rr = C.ss C.self
  a₀ = F.accCn azero
  kW = kk (cnt one) Rr q l₁
  kW′ = kk (cnt one) Rr q′ l₁′
  AL = F.Ai ac₁ Rr u q kW l₁ stepA w
  AR′ = F.Ai ac₁ Rr u′ q′ kW′ l₁′ stepA w′
  aa : AR lW lW AL AL
  aa z z″ Y₁ Y₂ hz c₁ r₁ =
    sndᴸ (hs q lW hz) lW lW l₁ l₁ (≤-refl W) C.self C.self (aS C.self lW) refl refl (adm-self W W) _ _ Y₁ Y₂ c₁ r₁
  a : AR lW lW′ AL AR′
  a z z′ Y₁ Y₁′ hz c₁ r₁ =
    sndᴸ (h q q′ lW lW′ le hz) lW lW′ l₁ l₁′ le C.self C.self (aS C.self lW′) refl refl (adm-self W W′) _ _ Y₁ Y₁′ c₁ r₁
  CL = F.Chn a₀ kW lW (C.lg⊲ kW lW) AL Y
  CR = F.Chn a₀ kW′ lW′ (C.lg⊲ kW′ lW′) AR′ Y′
  St : ℕ → Set
  St n = (proj₁ (proj₂ (CL n)) ⊑ᴾ proj₁ (proj₂ (CR n))) × (proj₁ (CL n) ⊑ᴾ proj₁ (CR n)) ×
         Ch (proj₂ (proj₂ (CL n))) × R∀ (proj₂ (proj₂ (CL n))) (proj₂ (proj₂ (CR n)))
  O : ∀ n → St n → OA (F.Run a₀ (proj₁ (proj₂ (CL n))) C.self lW kW AL (proj₁ (CL n)) (proj₂ (proj₂ (CL n))))
                      (F.Run a₀ (proj₁ (proj₂ (CR n))) C.self lW′ kW′ AR′ (proj₁ (CR n)) (proj₂ (proj₂ (CR n))))
  O n (hc , hw , cs , rs) = snd0 hc a₀ a₀ C.self C.self lW lW′ kW kW′ AL AR′ aa a _ _ hw _ _ cs rs
  st : ∀ n → St n
  st zero = proj₁ r (inj₁ kW) (inj₁ kW′) , z0 , c , r
  st (suc n) = let s@(hc , hw , cs , rs) = st n in
    O n s (inj₁ kW) (inj₁ kW′) , sq hw hc ,
    advA {Y = proj₂ (proj₂ (CL n))} {Y′ = proj₂ (proj₂ (CL n))} ΔL ΔL cs
         (cohᴬ a₀ (proj₁ (proj₂ (CL n))) C.self lW kW AL aa (proj₁ (CL n)) (proj₂ (proj₂ (CL n))) cs) ,
    advA {Y = proj₂ (proj₂ (CL n))} {Y′ = proj₂ (proj₂ (CR n))} ΔL ΔR rs (O n s)
    where
    ΔL = F.Run a₀ (proj₁ (proj₂ (CL n))) C.self lW kW AL (proj₁ (CL n)) (proj₂ (proj₂ (CL n)))
    ΔR = F.Run a₀ (proj₁ (proj₂ (CR n))) C.self lW′ kW′ AR′ (proj₁ (CR n)) (proj₂ (proj₂ (CR n)))
  go : (x : F.Rk′ azero azero) (y : F.Rk′ azero azero) →
       F.RKi ac₁ a₀ Rr u q lW l₁ stepA w Y τ tt x ⊑ᴾ F.RKi ac₁ a₀ Rr u′ q′ lW′ l₁′ stepA w′ Y′ τ′ tt y
  go (F.keep ()) y
  go (F.rise _) (F.keep ())
  go (F.rise _) (F.rise _) = lm (λ n → O n (st n) τ τ′)
```

## 4 旧关系嵌入, 顶层

旧关系 $\sqsubseteq^{+}$ 在一切下标处嵌入 `Le`. 顶层 (树在自己的世界上跑, 路径 `self`) 新前提都成立: `aS`, `refl`, `adm-self`; 所以 `SemL` 的前提可满足, 与 `SemS` 在顶层给出同样的结论.

```agda
emb⁺ : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑⁺ x′ → ∀ {lV : Lg V} {lV′ : Lg V′} → Le lV lV′ x x′
emb⁺ n0⁺ = n0ᴸ
emb⁺ n1⁺ = n1ᴸ
emb⁺ (⨾⁺ h h′) = ⨾ᴸ (emb⁺ h) (emb⁺ h′)
emb⁺ (nl⁺ h) = nlᴸ (λ n → emb⁺ (h n))
emb⁺ (nwʳ⁺ h) = nwʳᴸ (emb⁺ h)
emb⁺ (pr⁺ h) = prᴸ (emb⁺ h)
emb⁺ (κ⁺ h) = κᴸ (λ p p′ lc lc′ c≤ → emb⁺ (h p p′ lc lc′ c≤))
emb⁺ (ni⁺ h hs) = niᴸ (λ p p′ lc lc′ c≤ hz → emb⁺ (h p p′ lc lc′ c≤ hz)) (λ p lc hz → emb⁺ (hs p lc hz))
emb⁺ (tr⁺ h h′) = trᴸ (emb⁺ h) (emb⁺ h′)

top : ∀ {V V′} {lV : Lg V} {lV′ : Lg V′} {x : D one V} {x′ : D one V′} → Le lV lV′ x x′ →
      (l₁ : one ⊲ V) (l₁′ : one ⊲ V′) → V ≤ V′ → ∀ w w′ (Y : F.St V) (Y′ : F.St V′) → Ch Y → R∀ Y Y′ →
      OA (F.Run ac₁ x C.self lV l₁ stepA w Y) (F.Run ac₁ x′ C.self lV′ l₁′ stepA w′ Y′)
top {V} {V′} {lV} {lV′} h l₁ l₁′ le = sndᴸ h lV lV′ l₁ l₁′ le C.self C.self (aS C.self lV′) refl refl (adm-self V V′)
```
