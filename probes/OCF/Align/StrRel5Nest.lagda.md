# 结构关系, 第五轮 (四): 嵌套族对一切深度结构可靠

> 不含记号. 入口 [StrRel5](StrRel5.lagda.md).
>
> 主线的嵌套族 $\mathrm{nest}_0=1$, $\mathrm{nest}_{k+1}=\mathrm{n}\kappa(\_\mapsto\mathrm{nest}_k)$ (`KNestSound.nest`), 动作取 `Step` (主线的动作, 对一切抬升都是它). 语义 `Sem k`:
>
> - 两边运行世界 $W\le W'$;
> - 从树世界到运行世界的两条路径 $q,q'$ **对齐** (`Al`, 领先量量到 $W,W'$), 不是 "一切 $q,q'$";
> - 两边状态结构相关 `R∀`: 状态的差对**一切**读数路径对 $\sqsubseteq^{\mathsf P}$ 相关, 第 0 层累计 $z$ 也相关;
>
> 结论: 两边输出对一切读数路径对 $\sqsubseteq^{\mathsf P}$ 相关.
>
> **定理 `sem : ∀ k → Sem k`**, 对 $k$ 归纳, 无参数. `nκ` 一步对格号归纳:
>
> - 第 0 格: 路径 `⊲-tr q (sum-fst W z)` 由 `alZeroᴾ` 对齐 ($q$ 的对齐经 `Al-map` 换到格世界, 用 $z\sqsubseteq^{\mathsf P}z'$ 的值);
> - 第 $n+1$ 格: 路径 `sum-fst v d` 由 `alSuccᴾ` 对齐, $d\sqsubseteq^{\mathsf P}d'$ 是上一格的输出;
> - 格内: `StrRel5All.cellᴬ`, 分支前提就是归纳假设 (剩下的路径的对齐由 `walkᴬ` 给);
> - 换世界: `cvR` (结构版的路径一致: `cmpF` 两边算出的读数路径不同, 由 `R∀` 对一切路径对成立接住).
>
> **推论 `sem-val`**: 值可比 (`vsᴾ`). 不要领先量 `Adm`, 不要 "树世界可比", 不要 `CellStep`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel5Nest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; z⊲; Tg; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤)
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; nw; cnt; sum; sum-fst; drp)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KValSem using (ac₁; toV0)
open import OCF.Align.KNestSound using (nest; adv-sum)
open import OCF.Align.StrRel4Walk using (Al)
open import OCF.Align.StrRel4Gen using (Al-map)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0; o1; sq; lm; wl; wr; tr; pr; vsᴾ; alSuccᴾ; alZeroᴾ)
open import OCF.Align.StrRel5Walk using (Env; env; Rn)
open import OCF.Align.StrRel5All using (module GoA)
```

## §1 环境与状态关系

```agda
stepA : ∀ {W} → F.Ig (cnt one) W
stepA _ _ _ Y = F.Step Y

E : ∀ W → Lg W → one ⊲ W → Env
E W lW l₁ = env W lW l₁ stepA (z⊲ W)

OA : ∀ {W W′} → F.Df W → F.Df W′ → Set
OA {W} {W′} Δ Δ′ = ∀ (τ : Tg azero W) (τ′ : Tg azero W′) → F.yc Δ τ tt ⊑ᴾ F.yc Δ′ τ′ tt

R∀ : ∀ {W W′} → F.St W → F.St W′ → Set
R∀ {W} {W′} Y Y′ = (∀ (τ : Tg azero W) (τ′ : Tg azero W′) → F.yc (F.d Y) τ tt ⊑ᴾ F.yc (F.d Y′) τ′ tt) × (F.z Y ⊑ᴾ F.z Y′)

advA : ∀ {W W′} {Y : F.St W} {Y′ : F.St W′} (Δ : F.Df W) (Δ′ : F.Df W′) → R∀ Y Y′ → OA Δ Δ′ → R∀ (Y F.⊕ Δ) (Y′ F.⊕ Δ′)
advA {W} {W′} Δ Δ′ (r , rz) O = (λ τ τ′ → sq (r τ τ′) (O τ τ′)) , sq rz (O (inj₁ (z⊲ W)) (inj₁ (z⊲ W′)))

-- 换世界: 读数路径由 cmpF 算出, 两边不同; R∀ 对一切路径对成立, 所以接得住
cvR : ∀ {W₁ W₂ W₁′ W₂′} (q : W₁ ⊲ W₂) (l : Lg W₂) (q′ : W₁′ ⊲ W₂′) (l′ : Lg W₂′) (Y : F.St W₁) (Y′ : F.St W₁′) →
      R∀ Y Y′ → R∀ (F.cv q l Y) (F.cv q′ l′ Y′)
cvR q l q′ l′ Y Y′ (r , rz) = h , z0
  where
  h : ∀ τ τ′ → F.yc (F.d (F.cv q l Y)) τ tt ⊑ᴾ F.yc (F.d (F.cv q′ l′ Y′)) τ′ tt
  h (inj₁ τ₁) (inj₁ τ₁′) with cmpF q τ₁ l | cmpF q′ τ₁′ l′
  ... | inj₁ a | inj₁ b = wl (wr (r (inj₁ a) (inj₁ b)))
  ... | inj₁ a | inj₂ b = wl (wr (r (inj₁ a) (inj₂ b)))
  ... | inj₂ a | inj₁ b = wl (wr (r (inj₂ a) (inj₁ b)))
  ... | inj₂ a | inj₂ b = wl (wr (r (inj₂ a) (inj₂ b)))
  h (inj₁ τ₁) (inj₂ τ₂′) with cmpF q τ₁ l
  ... | inj₁ a = wl (r (inj₁ a) (inj₂ (⊲-tr q′ τ₂′)))
  ... | inj₂ a = wl (r (inj₂ a) (inj₂ (⊲-tr q′ τ₂′)))
  h (inj₂ τ₂) (inj₁ τ₁′) with cmpF q′ τ₁′ l′
  ... | inj₁ b = wr (r (inj₂ (⊲-tr q τ₂)) (inj₁ b))
  ... | inj₂ b = wr (r (inj₂ (⊲-tr q τ₂)) (inj₂ b))
  h (inj₂ τ₂) (inj₂ τ₂′) = r (inj₂ (⊲-tr q τ₂)) (inj₂ (⊲-tr q′ τ₂′))

-- 动作 Step: 第 0 层是 ω·(1⨾0⨾读数)
stepR : ∀ {W W′} {Y : F.St W} {Y′ : F.St W′} → R∀ Y Y′ → OA (F.Step Y) (F.Step Y′)
stepR (r , rz) τ τ′ = lm (λ _ → sq (sq o1 z0) (r τ τ′))

drpR : ∀ {V V′ U U′} {x : D azero V} {x′ : D azero V′} → x ⊑ᴾ x′ → drp {W′ = U} x ⊑ᴾ drp {W′ = U′} x′
drpR z0 = z0
drpR o1 = o1
drpR (sq h h′) = sq (drpR h) (drpR h′)
drpR (lm h) = lm (λ n → drpR (h n))
drpR {U = U} {U′} (wl {x = x} {x′} h) = drpR {U = U} {U′} {x} {x′} h
drpR {U = U} {U′} (wr {x = x} {x′} h) = drpR {U = U} {U′} {x} {x′} h
drpR {U = U} {U′} (tr {x = x} {y} {z} h h′) = tr (drpR {U = U} {U} {x} {y} h) (drpR {U = U} {U′} {y} {z} h′)
drpR (pr h) = pr (drpR h)
```

## §2 定理

```agda
Sem : ℕ → Set
Sem k = ∀ {W W′} (lW : Lg W) (lW′ : Lg W′) (l₁ : one ⊲ W) (l₁′ : one ⊲ W′) → W ≤ W′ →
        ∀ {V V′} (q : V ⊲ W) (q′ : V′ ⊲ W′) → Al W W′ q lW q′ lW′ → ∀ w w′ (Y : F.St W) (Y′ : F.St W′) → R∀ Y Y′ →
        OA (Rn (E W lW l₁) (nest k) q w Y) (Rn (E W′ lW′ l₁′) (nest k) q′ w′ Y′)

sem : ∀ k → Sem k
sem zero lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r = stepR {Y = Y} {Y′ = Y′} r
sem (suc k) {W} {W′} lW lW′ l₁ l₁′ le {V} {V′} q q′ hq w w′ Y Y′ r τ τ′ = lm (λ n → drpR (cell n))
  where
  u : ∀ {c} → V ⊲ c → Lg c → D one c
  u _ _ = nest k
  u′ : ∀ {c} → V′ ⊲ c → Lg c → D one c
  u′ _ _ = nest k
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
         R∀ (F.Sv (cL n)) (F.Sv (cR n))

  out : ∀ n → St n → OA (ΔL n) (ΔR n)
  out n (vle , H , rs) =
    GoA.cellᴬ (eL n) (eR n) u u′ R∀ (λ {Y₂} {Y₂′} Δ Δ′ → advA {Y = Y₂} {Y′ = Y₂′} Δ Δ′)
      (λ p p′ lc lc′ c≤ ad q₁ q₁′ hq₁ w₁ w₁′ Y₁ Y₁′ r₁ →
         sem k (F.lv (cL n)) (F.lv (cR n)) (⊲-tr l₁ (F.wv (cL n))) (⊲-tr l₁′ (F.wv (cR n))) vle q₁ q₁′ hq₁ w₁ w₁′ Y₁ Y₁′ r₁)
      H (F.ap (cL n)) (F.ap (cR n)) (F.co (cL n)) (F.co (cR n)) (F.Sv (cL n)) (F.Sv (cR n)) rs

  st0 : St zero
  st0 = vsᴾ (proj₂ r) le ,
        alZeroᴾ lW lW′ (Al-map (λ ad → adv-sum (F.z Y) (F.z Y′) ad (toV0 (F.z Y) (F.z Y′) (vsᴾ (proj₂ r) z≤))) hq) (proj₂ r) le ,
        cvR (sum-fst W (F.z Y)) (F.lv (cL zero)) (sum-fst W′ (F.z Y′)) (F.lv (cR zero)) Y Y′ r

  stS : ∀ n → St n → St (suc n)
  stS n st@(vle , H , rs) =
    vsᴾ dr vle , alSuccᴾ dr (F.lv (cL n)) (F.lv (cR n)) vle ,
    cvR (sum-fst (F.v (cL n)) (F.yc (ΔL n) (inj₁ (z⊲ (F.v (cL n)))) tt)) (F.lv (cL (suc n))) (sum-fst (F.v (cR n)) (F.yc (ΔR n) (inj₁ (z⊲ (F.v (cR n)))) tt)) (F.lv (cR (suc n))) (F.Sv (cL n) F.⊕ ΔL n) (F.Sv (cR n) F.⊕ ΔR n) (advA {Y = F.Sv (cL n)} {Y′ = F.Sv (cR n)} (ΔL n) (ΔR n) rs O)
    where
    O = out n st
    dr = O (inj₁ (z⊲ (F.v (cL n)))) (inj₁ (z⊲ (F.v (cR n))))

  go : ∀ n → St n
  go zero = st0
  go (suc n) = stS n (go n)

  cell : ∀ n → F.yc (ΔL n) (inj₁ (z⊲ (F.v (cL n)))) tt ⊑ᴾ F.yc (ΔR n) (inj₁ (z⊲ (F.v (cR n)))) tt
  cell n = out n (go n) (inj₁ (z⊲ _)) (inj₁ (z⊲ _))

-- 值的推论
sem-val : ∀ k {W W′} (lW : Lg W) (lW′ : Lg W′) (l₁ : one ⊲ W) (l₁′ : one ⊲ W′) → W ≤ W′ →
          ∀ {V V′} (q : V ⊲ W) (q′ : V′ ⊲ W′) → Al W W′ q lW q′ lW′ → ∀ w w′ (Y : F.St W) (Y′ : F.St W′) → R∀ Y Y′ →
          ∀ τ τ′ e e′ → e ≤ e′ → sum e (F.yc (Rn (E W lW l₁) (nest k) q w Y) τ tt) ≤ sum e′ (F.yc (Rn (E W′ lW′ l₁′) (nest k) q′ w′ Y′) τ′ tt)
sem-val k lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′ e e′ h = vsᴾ (sem k lW lW′ l₁ l₁′ le q q′ hq w w′ Y Y′ r τ τ′) h
```
