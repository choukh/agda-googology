# 结构关系, 第七轮: 加上传递与 `ni` 的关系 $\sqsubseteq^{+}$

> 入口见 [StrRel7](StrRel7.lagda.md). `StrRel6` 的七个构造子之外加两个: **`tr⁺`** (传递, 中间一棵与左边同一树世界) 与 **`ni⁺`** (`ni` 节点, 分支对坐标单调). 语义 `SemS` 是 `StrRel6.SemT` 加一条前提: **左边状态自洽** (`Ch Y`). 对推导归纳一个证明 `snd⁺`, 无参数, 含嵌套 `nκ`, 对一切深度.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel7Snd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; cnt; sum; sum-fst; kk)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁; toV0)
open import OCF.Align.KNestSound using (adv-sum)
open import OCF.Align.StrRel4Walk using (Al; aS)
open import OCF.Align.StrRel4Gen using (Al-map)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; sq; lm; tr; pr; vsᴾ; alSuccᴾ; alZeroᴾ)
open import OCF.Align.StrRel5Walk using (Env)
open import OCF.Align.StrRel5Suf using (rfx)
open import OCF.Align.StrRel5Nest using (stepA; E; OA; R∀; advA; cvR; stepR; drpR)
open import OCF.Align.StrRel6 using (_⊑ˢ_; n0ˢ; n1ˢ; ⨾ˢ; nlˢ; nwʳˢ; prˢ; κˢ; SemT)
open import OCF.Align.StrRel7Coh using (Ch; coh₁; cA-step; alR)
open import OCF.Align.StrRel7Walk using (cohWlk; module GoC)
open import OCF.Align.StrRel7Zero using (AR; cohᴬ; snd0)
```

## 1 关系

`ni⁺` 的两条前提: 两边分支在 $c\le c'$ 的位置上、坐标 $z\sqsubseteq^{\mathsf P}z'$ 时相关; 左边分支在同一位置上对坐标单调 (`tr` 的中间一棵在左边跑, 要它). `ni` 的层号固定为 `ss self` (第 1 层树的 `ni` 只有这一种).

```agda
infix 4 _⊑⁺_
data _⊑⁺_ : ∀ {V V′} → D one V → D one V′ → Set where
  n0⁺  : ∀ {V V′} {x : D one V′} → n0 {W = V} ⊑⁺ x
  n1⁺  : ∀ {V V′} → n1 {W = V} ⊑⁺ n1 {W = V′}
  ⨾⁺   : ∀ {V V′} {x y : D one V} {x′ y′ : D one V′} → x ⊑⁺ x′ → y ⊑⁺ y′ → (x ⨾ y) ⊑⁺ (x′ ⨾ y′)
  nl⁺  : ∀ {V V′} {d : ℕ → D one V} {d′ : ℕ → D one V′} → (∀ n → d n ⊑⁺ d′ n) → nl d ⊑⁺ nl d′
  nwʳ⁺ : ∀ {V₀ V V′} {p : V₀ ⊲ V′} {x : D one V} {x′ : D one V₀} → x ⊑⁺ x′ → x ⊑⁺ nw p x′
  pr⁺  : ∀ {V V′} {x : D one V} {x′ y′ : D one V′} → x ⊑⁺ x′ → x ⊑⁺ (x′ ⨾ y′)
  κ⁺   : ∀ {V V′ zz zz′} {u : ∀ {c} → V ⊲ c → Lg c → D one c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D one c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → u p lc ⊑⁺ u′ p′ lc′) →
         nκ zz u ⊑⁺ nκ zz′ u′
  ni⁺  : ∀ {V V′} {u : ∀ {c} → V ⊲ c → Lg c → D azero c → D one c} {u′ : ∀ {c} → V′ ⊲ c → Lg c → D azero c → D one c} →
         (∀ {c c′} (p : V ⊲ c) (p′ : V′ ⊲ c′) (lc : Lg c) (lc′ : Lg c′) → c ≤ c′ → ∀ {z z′} → z ⊑ᴾ z′ → u p lc z ⊑⁺ u′ p′ lc′ z′) →
         (∀ {c} (p : V ⊲ c) (lc : Lg c) → ∀ {z z″} → z ⊑ᴾ z″ → u p lc z ⊑⁺ u p lc z″) →
         ni (C.ss C.self) u ⊑⁺ ni (C.ss C.self) u′
  tr⁺  : ∀ {V V′} {x y : D one V} {z : D one V′} → x ⊑⁺ y → y ⊑⁺ z → x ⊑⁺ z

SemS : ∀ {V V′} → D one V → D one V′ → Set
SemS {V} {V′} x x′ =
  ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (l₁ : one ⊲ W) (l₁′ : one ⊲ W′) → W ≤ W′ →
  ∀ (q : V ⊲ W) (q′ : V′ ⊲ W′) → Al W W′ q lW q′ lW′ → ∀ w w′ (Y : F.St W) (Y′ : F.St W′) → Ch Y → R∀ Y Y′ →
  OA (F.Run ac₁ x q lW l₁ stepA w Y) (F.Run ac₁ x′ q′ lW′ l₁′ stepA w′ Y′)
```

## 2 可靠性

```agda
snd⁺ : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑⁺ x′ → SemS x x′
snd⁺ n0⁺ lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′ = z0
snd⁺ n1⁺ lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r = stepR {Y = Y} {Y′ = Y′} r
snd⁺ (⨾⁺ {x = x} {x′ = x′} hx hy) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′ =
  sq (Ox τ τ′) (snd⁺ hy lW lW′ l₁ l₁′ le q q′ hq (w ⨾ nw q x) (w′ ⨾ nw q′ x′) _ _
                     (advA {Y = Y} {Y′ = Y} Δ Δ c (coh₁ ac₁ x q lW l₁ stepA cA-step w Y c))
                     (advA {Y = Y} {Y′ = Y′} Δ Δ′ r Ox) τ τ′)
  where
  Δ = F.Run ac₁ x q lW l₁ stepA w Y
  Δ′ = F.Run ac₁ x′ q′ lW′ l₁′ stepA w′ Y′
  Ox = snd⁺ hx lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r
snd⁺ (nl⁺ {d = d} {d′} hd) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′ = lm (λ n → proj₁ (go n) τ τ′)
  where
  P = λ n → F.Rpt ac₁ d q lW l₁ stepA w Y n
  P′ = λ n → F.Rpt ac₁ d′ q′ lW′ l₁′ stepA w′ Y′ n
  Δ = λ n → F.Run ac₁ (d n) q lW l₁ stepA (proj₁ (P n)) (proj₂ (P n))
  Δ′ = λ n → F.Run ac₁ (d′ n) q′ lW′ l₁′ stepA (proj₁ (P′ n)) (proj₂ (P′ n))
  st : ∀ n → Ch (proj₂ (P n)) × R∀ (proj₂ (P n)) (proj₂ (P′ n))
  go : ∀ n → OA (Δ n) (Δ′ n) × Ch (proj₂ (P n)) × R∀ (proj₂ (P n)) (proj₂ (P′ n))
  go n = snd⁺ (hd n) lW lW′ l₁ l₁′ le q q′ hq _ _ _ _ (proj₁ (st n)) (proj₂ (st n)) , st n
  st zero = c , r
  st (suc n) =
    advA {Y = proj₂ (P n)} {Y′ = proj₂ (P n)} (Δ n) (Δ n) (proj₁ (st n)) (coh₁ ac₁ (d n) q lW l₁ stepA cA-step _ _ (proj₁ (st n))) ,
    advA {Y = proj₂ (P n)} {Y′ = proj₂ (P′ n)} (Δ n) (Δ′ n) (proj₂ (st n)) (proj₁ (go n))
snd⁺ (nwʳ⁺ {p = p} h) lW lW′ l₁ l₁′ le q q′ hq = snd⁺ h lW lW′ l₁ l₁′ le q (⊲-tr p q′) (rfx p hq)
snd⁺ (pr⁺ h) lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′ = pr (snd⁺ h lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′)
snd⁺ (tr⁺ hxy hyz) {W} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′ =
  tr (snd⁺ hxy lW lW l₁ l₁ (≤-refl W) q q (alR lW W q lW C.self) w w Y Y c c τ τ)
     (snd⁺ hyz lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′)
snd⁺ {V} {V′} (κ⁺ {u = u} {u′} h) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′ = lm (λ n → drpR (cell n))
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
    GoC.cellᶜ (eL n) (eR n) cA-step u u′ (λ Y₂ Y₂′ → Ch Y₂ × R∀ Y₂ Y₂′) proj₁
      (λ {Y₂} {Y₂′} Δ Δ′ cr O Os → advA {Y = Y₂} {Y′ = Y₂} Δ Δ (proj₁ cr) Os , advA {Y = Y₂} {Y′ = Y₂′} Δ Δ′ (proj₂ cr) O)
      (λ p p′ lc lc′ c≤ ad q₁ q₁′ hq₁ w₁ w₁′ Y₁ Y₁′ cr →
         snd⁺ (h p p′ lc lc′ c≤) (F.lv (cL n)) (F.lv (cR n)) (⊲-tr l₁ (F.wv (cL n))) (⊲-tr l₁′ (F.wv (cR n))) vle
              q₁ q₁′ hq₁ w₁ w₁′ Y₁ Y₁′ (proj₁ cr) (proj₂ cr))
      H (F.ap (cL n)) (F.ap (cR n)) (F.co (cL n)) (F.co (cR n)) (F.Sv (cL n)) (F.Sv (cR n)) (cs , rs)

  st0 : St zero
  st0 = vsᴾ (proj₂ r) le ,
        alZeroᴾ lW lW′ (Al-map (λ ad → adv-sum (F.z Y) (F.z Y′) ad (toV0 (F.z Y) (F.z Y′) (vsᴾ (proj₂ r) z≤))) hq) (proj₂ r) le ,
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
snd⁺ {V} {V′} (ni⁺ {u = u} {u′} h hs) {W} {W′} lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r τ τ′ =
  go (F.rkT kW τ lW) (F.rkT kW′ τ′ lW′)
  where
  Rr = C.ss C.self
  a₀ = F.accCn azero
  kW = kk (cnt one) Rr q l₁
  kW′ = kk (cnt one) Rr q′ l₁′
  AL = F.Ai ac₁ Rr u q kW l₁ stepA w
  AR′ = F.Ai ac₁ Rr u′ q′ kW′ l₁′ stepA w′
  aa : AR lW lW AL AL
  aa z z″ Y₁ Y₂ hz c₁ r₁ = snd⁺ (hs q lW hz) lW lW l₁ l₁ (≤-refl W) C.self C.self (aS C.self lW) _ _ Y₁ Y₂ c₁ r₁
  a : AR lW lW′ AL AR′
  a z z′ Y₁ Y₁′ hz c₁ r₁ = snd⁺ (h q q′ lW lW′ le hz) lW lW′ l₁ l₁′ le C.self C.self (aS C.self lW′) _ _ Y₁ Y₁′ c₁ r₁
  CL = F.Chn a₀ kW lW (lg⊲ kW lW) AL Y
  CR = F.Chn a₀ kW′ lW′ (lg⊲ kW′ lW′) AR′ Y′
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

## 3 推论

旧关系嵌入新关系; `SemT` 推出 `SemS`. 于是 `StrRel6` 的全部推导 (含 `nest-rel`, `diff`) 在新关系里, 并可以与 `tr⁺`, `ni⁺` 自由组合.

```agda
emb : ∀ {V V′} {x : D one V} {x′ : D one V′} → x ⊑ˢ x′ → x ⊑⁺ x′
emb n0ˢ = n0⁺
emb n1ˢ = n1⁺
emb (⨾ˢ h h′) = ⨾⁺ (emb h) (emb h′)
emb (nlˢ h) = nl⁺ (λ n → emb (h n))
emb (nwʳˢ h) = nwʳ⁺ (emb h)
emb (prˢ h) = pr⁺ (emb h)
emb (κˢ h) = κ⁺ (λ p p′ lc lc′ c≤ → emb (h p p′ lc lc′ c≤))

T→S : ∀ {V V′} {x : D one V} {x′ : D one V′} → SemT x x′ → SemS x x′
T→S s lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ c r = s lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r
```
