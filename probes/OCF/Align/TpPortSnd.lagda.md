# 两种种类的单调 (十一): 节点一步与对层的归纳

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort7Snd](MonoPort7Snd.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 节点坐标动作的前提里, 内层 `Int` 多 `NZ₁-S r` (`zL₁`), 与两种种类的 `Ai` 字面一致.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)
module OCF.Align.TpPortSnd (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtTowerTy using (hl; hΩ; ⊲ᴮ↑)
open import OCF.Align.HtTowerFTree using (ss; sl; sL; StH; Vs; acc; mkOf; inS; outS; NZ-S; NZ₁-S; n0; n1; _⨾_; nl; ni; nw; ≤rf) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.TpPortDef using (_⊑₀_; refl₀) renaming (preL to preLˢ)
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortInt Λ lΛ oΛ lW t₀ using (IntMK; cx00; module CxS; cxLN; cxRN; finS; toN; fromN)
open import OCF.Align.TpPortLay Λ lΛ oΛ lW t₀ using (module L; HAKN)
open import OCF.Align.TpPortRelM lW using (module RelM)
import OCF.Align.TpPortZero as Z


module B₀ (ac : AccY hz) (ll : hz ⊲[ W ] Λ) = Z.B Λ lΛ oΛ lW t₀ O preO ac ll (λ h → h ll)

preL≡ : ∀ {ly V} (d : ℕ → D ly V) k → preLˢ d k ≡ G.preL d k
preL≡ d zero = refl
preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)
```
```agda
toHA₀ : ∀ ac ll (i j : P.Ig hz W) → HAK hz i j → B₀.HA ac ll i j
toHA₀ ac ll i j h w w′ c c′ Y Y′ (B₀.cx cw) = h w w′ c c′ Y Y′ cw

SemK : ∀ k → AccY k → k ⊲[ W ] Λ → D k W → D k W → Set
SemK hz ac ll x x′ = ∀ (Aᵢ Aⱼ : P.Ig hz W) → HAK hz Aᵢ Aᵢ → HAK hz Aⱼ Aⱼ → HAK hz Aᵢ Aⱼ → B₀.Sem ac ll Aᵢ Aⱼ x x′
SemK (hs b) ac ll = L.SemS (hs b) ac ll
SemK (hl f) ac ll = L.SemS (hl f) ac ll
SemK (hΩ _ g) _ _ _ _ = ⊤

SndArg : ∀ k → AccY k → Set
SndArg k ac = ∀ pos {x x′} → Rel k x x′ → SemK k ac pos x x′

OutsK : ∀ {k} → AccY k → k ⊲[ W ] Λ → P.Ig k W → P.St W → ℕ → P.Df W
OutsK ac pos A₂ Y n =
  P.Run ac (proj₁ (proj₂ (P.Chn ac pos lW A₂ Y n))) ≤rf lW pos A₂ (proj₁ (P.Chn ac pos lW A₂ Y n)) (proj₂ (proj₂ (P.Chn ac pos lW A₂ Y n)))

chainK : ∀ k → Fin k → (ac : AccY k) (pos : k ⊲[ W ] Λ) → SndArg k ac → (i j : P.Ig k W) → HAK k i i → HAK k j j → HAK k i j →
         ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ n → OutsK ac pos i Y n ≼ OutsK ac pos j Y′ n
chainK hz fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (B₀.Chain.chain₀ ac pos i j (toHA₀ ac pos i i hi) (toHA₀ ac pos j j hj) (toHA₀ ac pos i j hij) Y Y′ azero azero g g′ s z≤)
chainK (hs b) fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (L.Ch.chainG (hs b) ac pos (sk pos) (λ h → h) i j hi hj hij Y Y′ azero azero g g′ s z≤)
chainK (hl f) fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (L.Ch.chainG (hl f) ac pos (sk pos) (λ h → h) i j hi hj hij Y Y′ azero azero g g′ s z≤)

SvK : ∀ {k} → AccY k → k ⊲[ W ] Λ → P.Ig k W → P.St W → D k W → P.St W
SvK ac pos i Y z = P.cv ≤rf Y G.⊕ P.Run ac z ≤rf lW pos (P.Ig↾ ≤rf i) n0 (P.cv ≤rf Y)

brnK : ∀ k → Fin k → (ac : AccY k) (pos : k ⊲[ W ] Λ) → SndArg k ac → (i j : P.Ig k W) → HAK k i i → HAK k j j → HAK k i j →
       ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ {z z′} → Ctx k z z′ → i ≤rf lW z (SvK ac pos i Y z) ≼ j ≤rf lW z′ (SvK ac pos j Y′ z′)
brnK hz fk ac pos sk i j hi hj hij Y Y′ g g′ s {z} {z′} cz = proj₂ (hij z z′ azero azero S S′ cz gS gS′ sS z≤)
  where
  module B = B₀ ac pos
  i′ = P.Ig↾ ≤rf i
  j′ = P.Ig↾ ≤rf j
  Y₁ = P.cv ≤rf Y
  Y₁′ = P.cv ≤rf Y′
  Δ = B.Run i′ z ≤rf n0 Y₁
  Δ′ = B.Run j′ z′ ≤rf n0 Y₁′
  S = Y₁ G.⊕ Δ
  S′ = Y₁′ G.⊕ Δ′
  c00 = B.cx (refl₀ n0)
  o = sk pos cz i′ j′ hi hj hij ≤rf ≤rf n0 n0 (G.vY Y) (G.vY Y′) Y₁ Y₁′ c00 g g′ s (proj₁ s)
  rΔ = proj₂ (sk pos (refl₀ z) i′ i′ hi hi hi ≤rf ≤rf n0 n0 azero azero Y₁ Y₁ c00 g g (B.sr {Y₁} g) z≤)
  rΔ′ = proj₂ (sk pos (refl₀ z′) j′ j′ hj hj hj ≤rf ≤rf n0 n0 azero azero Y₁′ Y₁′ c00 g′ g′ (B.sr {Y₁′} g′) z≤)
  gS = B.G⊕ {Y₁} {Δ} g rΔ
  gS′ = B.G⊕ {Y₁′} {Δ′} g′ rΔ′
  sS = B.S⊕ {Y₁} {Y₁′} {Δ} {Δ′} g g′ s o
brnK (hs b) fk ac pos sk i j hi hj hij Y Y′ g g′ s cz =
  L.brn (hs b) ac pos i j hi hj hij Y Y′ g g′ s (sk pos (cxRel (hs b) cz)) (sk pos (proj₁ (cxL (hs b) cz))) (sk pos (proj₁ (cxR (hs b) cz))) cz
brnK (hl f) fk ac pos sk i j hi hj hij Y Y′ g g′ s cz =
  L.brn (hl f) ac pos i j hi hj hij Y Y′ g g′ s (sk pos (cxRel (hl f) cz)) (sk pos (proj₁ (cxL (hl f) cz))) (sk pos (proj₁ (cxR (hl f) cz))) cz

module Node (Lv : Ht) (fb : Fin Lv) (f : ∀ {W₁ k} → StH W₁ k Lv → AccY k) (ll : Lv ⊲[ W ] Λ)
  {k : Ht} (r : StH W k Lv) (u u′ : ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → Vs Lv r W′ → D Lv W′)
  (sk : SndArg k (f r))
  (mu  : ∀ z z′ → LowT Lv r z z′ → RelN Lv (u ≤rf lW z) (u ≤rf lW z′))
  (mu′ : ∀ z z′ → LowT Lv r z z′ → RelN Lv (u′ ≤rf lW z) (u′ ≤rf lW z′))
  (cr  : ∀ z z′ → LowT Lv r z z′ → RelN Lv (u ≤rf lW z) (u′ ≤rf lW z′))
  (su  : ∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴮ↑ ≤rf ll) (u ≤rf lW z) (u ≤rf lW z′))
  (su′ : ∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴮ↑ ≤rf ll) (u′ ≤rf lW z) (u′ ≤rf lW z′))
  (sc  : ∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴮ↑ ≤rf ll) (u ≤rf lW z) (u′ ≤rf lW z′))
  (Aᵢ Aⱼ : P.Ig Lv W) (hi : HAKN Lv Aᵢ Aᵢ) (hj : HAKN Lv Aⱼ Aⱼ) (hij : HAKN Lv Aᵢ Aⱼ)
  (w w′ : D Lv W) (Y Y′ : P.St W) (cw : CxN Lv w w′) (g : Good Y) (g′ : Good Y′) (s : SRel Y Y′) where

  zL = NZ-S r
  zL₁ = NZ₁-S r
  fk = finS r fb
  ac′ = f r
  kpos = P.kk r ≤rf ll
  Ub = ∀ {W′} → W ≤ʷ W′ → LgW₂ W′ → Vs Lv r W′ → D Lv W′
  module LK = L.K Lv (acc f) (⊲ᴮ↑ ≤rf ll)

  AiA : Ub → P.Ig Lv W → D Lv W → P.Ig k W
  AiA u₁ A₁ w₁ = P.Ai (acc f) ac′ r u₁ ≤rf kpos ll A₁ w₁

  -- 坐标层的动作前提 = 分支的语义 + 上下文相关 (要 Int 单调)
  hAi : ∀ {u₁ u₂ : Ub} (A₁ A₂ : P.Ig Lv W) {w₁ w₂} →
        (∀ z z′ → LowT Lv r z z′ → RelN Lv (u₁ ≤rf lW z) (u₁ ≤rf lW z′)) →
        (∀ z z′ → LowT Lv r z z′ → RelN Lv (u₂ ≤rf lW z) (u₂ ≤rf lW z′)) →
        (∀ z z′ → LowT Lv r z z′ → RelN Lv (u₁ ≤rf lW z) (u₂ ≤rf lW z′)) →
        (∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴮ↑ ≤rf ll) (u₁ ≤rf lW z) (u₂ ≤rf lW z′)) →
        HAKN Lv A₁ A₁ → HAKN Lv A₂ A₂ → HAKN Lv A₁ A₂ → CxN Lv w₁ w₂ → HAK k (AiA u₁ A₁ w₁) (AiA u₂ A₂ w₂)
  hAi {u₁} {u₂} A₁ A₂ m₁₁ m₂₂ m₁₂ s₁₂ h₁ h₂ h₁₂ cw₁ z z′ c c′ Y₁ Y₂ cz g₁ g₂ s₁ cb =
    s₁₂ (inS r z) (inS r z′) (lowIn Lv r cz) (P.Ig↾ ≤rf A₁) (P.Ig↾ ≤rf A₂) h₁ h₂ h₁₂ tt tt _ _ c c′ Y₁ Y₂ (LK.cx ctx) g₁ g₂ s₁ cb
    where
    mo : ∀ {v₁ v₂ : Ub} → (∀ z z′ → LowT Lv r z z′ → RelN Lv (v₁ ≤rf lW z) (v₂ ≤rf lW z′)) → ∀ (y y′ : D k W) → Ctx k y y′ →
         Rel Lv (v₁ ≤rf lW (inS r y)) (v₂ ≤rf lW (inS r y′))
    mo m y y′ cy = fromN Lv zL fb (m (inS r y) (inS r y′) (lowIn Lv r cy))
    ctx = CxS.ctxN Lv cw₁
            (toN Lv zL fb (IntMK k fk ac′ zL zL₁ (mkOf r ≤rf) (mo {u₁} {u₁} m₁₁) (mo {u₂} {u₂} m₂₂) (mo {u₁} {u₂} m₁₂) cz (cx00 k)))
            (toN Lv zL fb (IntMK k fk ac′ zL zL₁ (mkOf r ≤rf) (mo {u₁} {u₁} m₁₁) (mo {u₁} {u₁} m₁₁) (mo {u₁} {u₁} m₁₁) (cxL k cz) (cx00 k)))
            (toN Lv zL fb (IntMK k fk ac′ zL zL₁ (mkOf r ≤rf) (mo {u₂} {u₂} m₂₂) (mo {u₂} {u₂} m₂₂) (mo {u₂} {u₂} m₂₂) (cxR k cz) (cx00 k)))

  i = AiA u Aᵢ w
  j = AiA u′ Aⱼ w′
  hii = hAi {u} {u} Aᵢ Aᵢ mu mu mu su hi hi hi (cxLN Lv cw)
  hjj = hAi {u′} {u′} Aⱼ Aⱼ mu′ mu′ mu′ su′ hj hj hj (cxRN Lv cw)
  hx  = hAi {u} {u′} Aᵢ Aⱼ mu mu′ cr sc hi hj hij cw

  -- 对 Rk 的值分情形: 上升用链, 保留用分支一步 (目标 hs 与 hl 两种)
  rkRel : ∀ {t} (tm : t ⊲[ W ] Λ) (rk : P.Rk k t W) →
          Rel t (P.RKi (acc f) ac′ r u ≤rf lW ll Aᵢ w Y (Tt tm) rk) (P.RKi (acc f) ac′ r u′ ≤rf lW ll Aⱼ w′ Y′ (Tt tm) rk)
  rkRel {t} tm P.rise =
    rnl t (λ n → chainK k fk ac′ kpos sk i i hii hii hii Y Y g g (≤-refl _ , g) n tm)
          (λ n → chainK k fk ac′ kpos sk j j hjj hjj hjj Y′ Y′ g′ g′ (≤-refl _ , g′) n tm)
          (λ n → chainK k fk ac′ kpos sk i j hii hjj hx Y Y′ g g′ s n tm)
  rkRel {hs b₁} tm (P.keep (ss p)) =
    rni (hs b₁) (ss p)
      (λ y y′ l → brnK k fk ac′ (⊲ᴮ↑ ≤rf kpos) sk i i hii hii hii Y Y g g (≤-refl _ , g) (lowOut (hs b₁) (ss p) l) (⊲ᴮ↑ ≤rf tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴮ↑ ≤rf kpos) sk j j hjj hjj hjj Y′ Y′ g′ g′ (≤-refl _ , g′) (lowOut (hs b₁) (ss p) l) (⊲ᴮ↑ ≤rf tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴮ↑ ≤rf kpos) sk i j hii hjj hx Y Y′ g g′ s (lowOut (hs b₁) (ss p) l) (⊲ᴮ↑ ≤rf tm))
  rkRel {hl f₁} tm (P.keep (sl n p)) =
    rni (hl f₁) (sl n p)
      (λ y y′ l → brnK k fk ac′ (⊲ᴮ↑ ≤rf kpos) sk i i hii hii hii Y Y g g (≤-refl _ , g) (lowOut (hl f₁) (sl n p) l) (⊲ᴮ↑ ≤rf tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴮ↑ ≤rf kpos) sk j j hjj hjj hjj Y′ Y′ g′ g′ (≤-refl _ , g′) (lowOut (hl f₁) (sl n p) l) (⊲ᴮ↑ ≤rf tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴮ↑ ≤rf kpos) sk i j hii hjj hx Y Y′ g g′ s (lowOut (hl f₁) (sl n p) l) (⊲ᴮ↑ ≤rf tm))
  rkRel {hΩ _ g₁} tm (P.keep (sL e p)) = tt

  step : P.Run (acc f) (ni r u) ≤rf lW ll Aᵢ w Y ≼ P.Run (acc f) (ni r u′) ≤rf lW ll Aⱼ w′ Y′
  step tm = rkRel tm (P.rkT (⊲ᴮ↑ ≤rf kpos) tm lW)

sndS : ∀ b → Fin b → (ac : AccY b) (ll : b ⊲[ W ] Λ) {x x′ : D b W} → RelN b x x′ → L.SemS b ac ll x x′
sndArg : ∀ k → Fin k → (ac : AccY k) → SndArg k ac

sndArg hz fk ac pos h Aᵢ Aⱼ hi hj hij = B₀.snd₀ ac pos h Aᵢ Aⱼ (toHA₀ ac pos Aᵢ Aᵢ hi) (toHA₀ ac pos Aⱼ Aⱼ hj) (toHA₀ ac pos Aᵢ Aⱼ hij)
sndArg (hs b) fk ac pos h = sndS (hs b) fk ac pos h
sndArg (hl f) fk ac pos h = sndS (hl f) fk ac pos h

sndS b fb ac ll RelM.n0⊑ Aᵢ Aⱼ hi hj hij = L.n0S b ac ll
sndS b fb ac ll RelM.n1⊑ Aᵢ Aⱼ hi hj hij = L.n1S b ac ll (L.toHA b ac ll Aᵢ Aⱼ hij)
sndS b fb ac ll (RelM.⨾⊑ rx rx′ hx hy) Aᵢ Aⱼ hi hj hij =
  L.⨾S b ac ll (sndS b fb ac ll rx Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll rx′ Aⱼ Aⱼ hj hj hj) (sndS b fb ac ll hx Aᵢ Aⱼ hi hj hij)
    (L.K.inn (hx , (rx , rx′))) (sndS b fb ac ll hy Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.nl⊑ rd rd′ hd) Aᵢ Aⱼ hi hj hij =
  L.nlS b ac ll (λ n → sndS b fb ac ll (rd n) Aᵢ Aᵢ hi hi hi) (λ n → sndS b fb ac ll (rd′ n) Aⱼ Aⱼ hj hj hj)
    (λ n → sndS b fb ac ll (hd n) Aᵢ Aⱼ hi hj hij) (λ n → L.K.inn (hd n , (rd n , rd′ n)))
sndS b fb (acc f) ll (RelM.ni⊑ {k = k} r {u = u} {u′ = u′} mu mu′ cr) Aᵢ Aⱼ hi hj hij tt tt w w′ c c′ Y Y′ (L.K.cx cw) g g′ s cb =
  obs cb (Node.step b fb f ll r u u′ (sndArg k (finS r fb) (f r)) mu mu′ cr
            (λ z z′ l → sndS b fb (acc f) (⊲ᴮ↑ ≤rf ll) (mu z z′ l))
            (λ z z′ l → sndS b fb (acc f) (⊲ᴮ↑ ≤rf ll) (mu′ z z′ l))
            (λ z z′ l → sndS b fb (acc f) (⊲ᴮ↑ ≤rf ll) (cr z z′ l))
            Aᵢ Aⱼ hi hj hij w w′ Y Y′ cw g g′ s)
sndS b fb ac ll (RelM.nwˡ h) = sndS b fb ac ll h
sndS b fb ac ll (RelM.nwʳ h) = sndS b fb ac ll h
sndS b fb ac ll (RelM.nwᵉ h) = sndS b fb ac ll h
sndS b fb ac ll (RelM.tr h h′) Aᵢ Aⱼ hi hj hij = L.trS b ac ll (sndS b fb ac ll h Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll h′ Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.u0ˡ h) Aᵢ Aⱼ hi hj hij = L.u0ˡS b ac ll (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.u0ʳ h) Aᵢ Aⱼ hi hj hij = L.u0ʳS b ac ll (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.u1ˡ h) Aᵢ Aⱼ hi hj hij = L.u1ˡS b ac ll (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.u1ʳ h) Aᵢ Aⱼ hi hj hij = L.u1ʳS b ac ll (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.asˡ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  L.asˡS b ac ll (sndS b fb ac ll rx Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll ry Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll rz Aᵢ Aᵢ hi hi hi)
    (L.K.inn (rx , (rx , rx))) (L.K.inn (ry , (ry , ry))) (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.asˡ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  L.asˡ′S b ac ll (sndS b fb ac ll rx Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll ry Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll rz Aᵢ Aᵢ hi hi hi)
    (L.K.inn (rx , (rx , rx))) (L.K.inn (ry , (ry , ry))) (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.asʳ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  L.asʳS b ac ll (sndS b fb ac ll rx Aⱼ Aⱼ hj hj hj) (sndS b fb ac ll ry Aⱼ Aⱼ hj hj hj) (sndS b fb ac ll rz Aⱼ Aⱼ hj hj hj)
    (L.K.inn (rx , (rx , rx))) (L.K.inn (ry , (ry , ry))) (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.asʳ′ rx ry rz h) Aᵢ Aⱼ hi hj hij =
  L.asʳ′S b ac ll (sndS b fb ac ll rx Aⱼ Aⱼ hj hj hj) (sndS b fb ac ll ry Aⱼ Aⱼ hj hj hj) (sndS b fb ac ll rz Aⱼ Aⱼ hj hj hj)
    (L.K.inn (rx , (rx , rx))) (L.K.inn (ry , (ry , ry))) (sndS b fb ac ll h Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.pre⊑ {x} {x′} {d} {d′} rx rx′ rd rd′ hx hd k) Aᵢ Aⱼ hi hj hij =
  subst (λ t → L.K.Sem b ac ll Aᵢ Aⱼ {tt} {tt} (x ⨾ t) (x′ ⨾ nl d′)) (sym (preL≡ d k))
    (L.preS b ac ll preO (sndS b fb ac ll rx Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll rx′ Aⱼ Aⱼ hj hj hj)
       (λ n → sndS b fb ac ll (rd n) Aᵢ Aᵢ hi hi hi) (λ n → sndS b fb ac ll (rd′ n) Aⱼ Aⱼ hj hj hj)
       (sndS b fb ac ll hx Aᵢ Aⱼ hi hj hij) (L.K.inn (hx , (rx , rx′))) (λ n → sndS b fb ac ll (hd n) Aᵢ Aⱼ hi hj hij)
       (λ n → L.K.inn (hd n , (rd n , rd′ n))) k)
```
