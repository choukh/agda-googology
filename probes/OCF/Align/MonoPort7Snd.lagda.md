# 极限高度 (六): 节点一步与对层的归纳, 对一切不含 Ω-极限的层

> 入口 [MonoPort7](MonoPort7.lagda.md). 不含记号. 由 `probes/Survey/scripts/monoport7/mk_snd.py` 生成: `SemK` 到 `Node` 照 [MonoPort6Snd](MonoPort6Snd.lagda.md) 手写 (对层 `hl` 加一句), `sndS` 的子句逐字取自 `MonoPort6Snd`, 只换节点那一句. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.
>
> 与 `MonoPort6Snd` 的差: `Node` 对节点层 $L$ 与任意节点 `r : StH W k L` 写一次 (原来是 `hs b` 与 `ss Pk`); 分支的关系是 `RelN L`; 坐标动作的前提里, 内层 `Int` 在层 $L$ 上的输出经 `toN`/`fromN` 在 `Rel L` 与 `RelN L` 之间换写 (对 `hs`, `hl` 两者定义性相同); `rkRel` 多一句目标 `hl` 的保留; `SemK`, `chainK`, `brnK`, `sndArg` 多一句 `hl f`. `sndS` 对一切 `Fin` 层 (不含 Ω-极限).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; _⊲[_]_)
module OCF.Align.MonoPort7Snd (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtFeedTree using (hs; hl; hΩ; ss; sl; sL; StH; Vs; D; AccY; acc; mkOf; inS; outS; ⊲ᴴ↑; NZ-S;
  n0; n1; _⨾_; nl; ni; nw)
open import OCF.Align.StrRelDef lW using (_⊑₀_; refl₀) renaming (preL to preLˢ)
open import OCF.Align.MonoPort7Rel Λ lΛ lW t₀
open import OCF.Align.MonoPort7Int Λ lΛ lW t₀ using (IntMK; cx00; module CxS; cxLN; cxRN; finS; toN; fromN)
open import OCF.Align.MonoPort7Lay Λ lΛ lW t₀ using (module L; HAKN)
open import OCF.Align.MonoPort5Rel lW using (module RelM)
import OCF.Align.MonoPort6Zero as Z

module B₀ (ac : AccY hz) (ll : hz ⊲[ W ] Λ) = Z.B Λ lΛ lW t₀ O preO ac ll (λ h → h ll)

preL≡ : ∀ {ly V} (d : ℕ → D ly V) k → preLˢ d k ≡ G.preL d k
preL≡ d zero = refl
preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)
```

## 1 各层的语义, 链, 分支一步 (对层分三种: 第 0 层, `hs b`, `hl f`)

```agda
toHA₀ : ∀ ac ll (i j : P.Ig hz W) → HAK hz i j → B₀.HA ac ll i j
toHA₀ ac ll i j h w w′ c c′ Y Y′ (B₀.cx cw) = h w w′ c c′ Y Y′ cw

SemK : ∀ k → AccY k → k ⊲[ W ] Λ → D k W → D k W → Set
SemK hz ac ll x x′ = ∀ (Aᵢ Aⱼ : P.Ig hz W) → HAK hz Aᵢ Aᵢ → HAK hz Aⱼ Aⱼ → HAK hz Aᵢ Aⱼ → B₀.Sem ac ll Aᵢ Aⱼ x x′
SemK (hs b) ac ll = L.SemS (hs b) ac ll
SemK (hl f) ac ll = L.SemS (hl f) ac ll
SemK (hΩ g) _ _ _ _ = ⊤

SndArg : ∀ k → AccY k → Set
SndArg k ac = ∀ pos {x x′} → Rel k x x′ → SemK k ac pos x x′

OutsK : ∀ {k} → AccY k → k ⊲[ W ] Λ → P.Ig k W → P.St W → ℕ → P.Df W
OutsK ac pos A₂ Y n =
  P.Run ac (proj₁ (proj₂ (P.Chn ac pos lW A₂ Y n))) C.self lW pos A₂ (proj₁ (P.Chn ac pos lW A₂ Y n)) (proj₂ (proj₂ (P.Chn ac pos lW A₂ Y n)))

chainK : ∀ k → Fin k → (ac : AccY k) (pos : k ⊲[ W ] Λ) → SndArg k ac → (i j : P.Ig k W) → HAK k i i → HAK k j j → HAK k i j →
         ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ n → OutsK ac pos i Y n ≼ OutsK ac pos j Y′ n
chainK hz fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (B₀.Chain.chain₀ ac pos i j (toHA₀ ac pos i i hi) (toHA₀ ac pos j j hj) (toHA₀ ac pos i j hij) Y Y′ azero azero g g′ s z≤)
chainK (hs b) fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (L.Ch.chainG (hs b) ac pos (sk pos) (λ h → h) i j hi hj hij Y Y′ azero azero g g′ s z≤)
chainK (hl f) fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (L.Ch.chainG (hl f) ac pos (sk pos) (λ h → h) i j hi hj hij Y Y′ azero azero g g′ s z≤)

SvK : ∀ {k} → AccY k → k ⊲[ W ] Λ → P.Ig k W → P.St W → D k W → P.St W
SvK ac pos i Y z = P.cv C.self Y G.⊕ P.Run ac z C.self lW pos (P.Ig↾ C.self i) n0 (P.cv C.self Y)

brnK : ∀ k → Fin k → (ac : AccY k) (pos : k ⊲[ W ] Λ) → SndArg k ac → (i j : P.Ig k W) → HAK k i i → HAK k j j → HAK k i j →
       ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ {z z′} → Ctx k z z′ → i C.self lW z (SvK ac pos i Y z) ≼ j C.self lW z′ (SvK ac pos j Y′ z′)
brnK hz fk ac pos sk i j hi hj hij Y Y′ g g′ s {z} {z′} cz = proj₂ (hij z z′ azero azero S S′ cz gS gS′ sS z≤)
  where
  module B = B₀ ac pos
  i′ = P.Ig↾ C.self i
  j′ = P.Ig↾ C.self j
  Y₁ = P.cv C.self Y
  Y₁′ = P.cv C.self Y′
  Δ = B.Run i′ z C.self n0 Y₁
  Δ′ = B.Run j′ z′ C.self n0 Y₁′
  S = Y₁ G.⊕ Δ
  S′ = Y₁′ G.⊕ Δ′
  c00 = B.cx (refl₀ n0)
  o = sk pos cz i′ j′ hi hj hij C.self C.self n0 n0 (G.vY Y) (G.vY Y′) Y₁ Y₁′ c00 g g′ s (proj₁ s)
  rΔ = proj₂ (sk pos (refl₀ z) i′ i′ hi hi hi C.self C.self n0 n0 azero azero Y₁ Y₁ c00 g g (B.sr {Y₁} g) z≤)
  rΔ′ = proj₂ (sk pos (refl₀ z′) j′ j′ hj hj hj C.self C.self n0 n0 azero azero Y₁′ Y₁′ c00 g′ g′ (B.sr {Y₁′} g′) z≤)
  gS = B.G⊕ {Y₁} {Δ} g rΔ
  gS′ = B.G⊕ {Y₁′} {Δ′} g′ rΔ′
  sS = B.S⊕ {Y₁} {Y₁′} {Δ} {Δ′} g g′ s o
brnK (hs b) fk ac pos sk i j hi hj hij Y Y′ g g′ s cz =
  L.brn (hs b) ac pos i j hi hj hij Y Y′ g g′ s (sk pos (cxRel (hs b) cz)) (sk pos (proj₁ (cxL (hs b) cz))) (sk pos (proj₁ (cxR (hs b) cz))) cz
brnK (hl f) fk ac pos sk i j hi hj hij Y Y′ g g′ s cz =
  L.brn (hl f) ac pos i j hi hj hij Y Y′ g g′ s (sk pos (cxRel (hl f) cz)) (sk pos (proj₁ (cxL (hl f) cz))) (sk pos (proj₁ (cxR (hl f) cz))) cz

module Node (Lv : H) (fb : Fin Lv) (f : ∀ {W₁ k} → StH W₁ k Lv → AccY k) (ll : Lv ⊲[ W ] Λ)
  {k : H} (r : StH W k Lv) (u u′ : ∀ {W′} → W ⊲ W′ → Lg W′ → Vs Lv r W′ → D Lv W′)
  (sk : SndArg k (f r))
  (mu  : ∀ z z′ → LowT Lv r z z′ → RelN Lv (u C.self lW z) (u C.self lW z′))
  (mu′ : ∀ z z′ → LowT Lv r z z′ → RelN Lv (u′ C.self lW z) (u′ C.self lW z′))
  (cr  : ∀ z z′ → LowT Lv r z z′ → RelN Lv (u C.self lW z) (u′ C.self lW z′))
  (su  : ∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴴ↑ C.self ll) (u C.self lW z) (u C.self lW z′))
  (su′ : ∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴴ↑ C.self ll) (u′ C.self lW z) (u′ C.self lW z′))
  (sc  : ∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴴ↑ C.self ll) (u C.self lW z) (u′ C.self lW z′))
  (Aᵢ Aⱼ : P.Ig Lv W) (hi : HAKN Lv Aᵢ Aᵢ) (hj : HAKN Lv Aⱼ Aⱼ) (hij : HAKN Lv Aᵢ Aⱼ)
  (w w′ : D Lv W) (Y Y′ : P.St W) (cw : CxN Lv w w′) (g : Good Y) (g′ : Good Y′) (s : SRel Y Y′) where

  zL = NZ-S r
  fk = finS r fb
  ac′ = f r
  kpos = P.kk r C.self ll
  Ub = ∀ {W′} → W ⊲ W′ → Lg W′ → Vs Lv r W′ → D Lv W′
  module LK = L.K Lv (acc f) (⊲ᴴ↑ C.self ll)

  AiA : Ub → P.Ig Lv W → D Lv W → P.Ig k W
  AiA u₁ A₁ w₁ = P.Ai (acc f) ac′ r u₁ C.self kpos ll A₁ w₁

  -- 坐标层的动作前提 = 分支的语义 + 上下文相关 (要 Int 单调)
  hAi : ∀ {u₁ u₂ : Ub} (A₁ A₂ : P.Ig Lv W) {w₁ w₂} →
        (∀ z z′ → LowT Lv r z z′ → RelN Lv (u₁ C.self lW z) (u₁ C.self lW z′)) →
        (∀ z z′ → LowT Lv r z z′ → RelN Lv (u₂ C.self lW z) (u₂ C.self lW z′)) →
        (∀ z z′ → LowT Lv r z z′ → RelN Lv (u₁ C.self lW z) (u₂ C.self lW z′)) →
        (∀ z z′ → LowT Lv r z z′ → L.SemS Lv (acc f) (⊲ᴴ↑ C.self ll) (u₁ C.self lW z) (u₂ C.self lW z′)) →
        HAKN Lv A₁ A₁ → HAKN Lv A₂ A₂ → HAKN Lv A₁ A₂ → CxN Lv w₁ w₂ → HAK k (AiA u₁ A₁ w₁) (AiA u₂ A₂ w₂)
  hAi {u₁} {u₂} A₁ A₂ m₁₁ m₂₂ m₁₂ s₁₂ h₁ h₂ h₁₂ cw₁ z z′ c c′ Y₁ Y₂ cz g₁ g₂ s₁ cb =
    s₁₂ (inS r z) (inS r z′) (lowIn Lv r cz) (P.Ig↾ C.self A₁) (P.Ig↾ C.self A₂) h₁ h₂ h₁₂ tt tt _ _ c c′ Y₁ Y₂ (LK.cx ctx) g₁ g₂ s₁ cb
    where
    mo : ∀ {v₁ v₂ : Ub} → (∀ z z′ → LowT Lv r z z′ → RelN Lv (v₁ C.self lW z) (v₂ C.self lW z′)) → ∀ (y y′ : D k W) → Ctx k y y′ →
         Rel Lv (v₁ C.self lW (inS r y)) (v₂ C.self lW (inS r y′))
    mo m y y′ cy = fromN Lv zL fb (m (inS r y) (inS r y′) (lowIn Lv r cy))
    ctx = CxS.ctxN Lv cw₁
            (toN Lv zL fb (IntMK k fk ac′ zL (mkOf r C.self) (mo {u₁} {u₁} m₁₁) (mo {u₂} {u₂} m₂₂) (mo {u₁} {u₂} m₁₂) cz (cx00 k)))
            (toN Lv zL fb (IntMK k fk ac′ zL (mkOf r C.self) (mo {u₁} {u₁} m₁₁) (mo {u₁} {u₁} m₁₁) (mo {u₁} {u₁} m₁₁) (cxL k cz) (cx00 k)))
            (toN Lv zL fb (IntMK k fk ac′ zL (mkOf r C.self) (mo {u₂} {u₂} m₂₂) (mo {u₂} {u₂} m₂₂) (mo {u₂} {u₂} m₂₂) (cxR k cz) (cx00 k)))

  i = AiA u Aᵢ w
  j = AiA u′ Aⱼ w′
  hii = hAi {u} {u} Aᵢ Aᵢ mu mu mu su hi hi hi (cxLN Lv cw)
  hjj = hAi {u′} {u′} Aⱼ Aⱼ mu′ mu′ mu′ su′ hj hj hj (cxRN Lv cw)
  hx  = hAi {u} {u′} Aᵢ Aⱼ mu mu′ cr sc hi hj hij cw

  -- 对 Rk 的值分情形: 上升用链, 保留用分支一步 (目标 hs 与 hl 两种)
  rkRel : ∀ {t} (tm : t ⊲[ W ] Λ) (rk : P.Rk k t W) →
          Rel t (P.RKi (acc f) ac′ r u C.self lW ll Aᵢ w Y (Tt tm) rk) (P.RKi (acc f) ac′ r u′ C.self lW ll Aⱼ w′ Y′ (Tt tm) rk)
  rkRel {t} tm P.rise =
    rnl t (λ n → chainK k fk ac′ kpos sk i i hii hii hii Y Y g g (≤-refl _ , g) n tm)
          (λ n → chainK k fk ac′ kpos sk j j hjj hjj hjj Y′ Y′ g′ g′ (≤-refl _ , g′) n tm)
          (λ n → chainK k fk ac′ kpos sk i j hii hjj hx Y Y′ g g′ s n tm)
  rkRel {hs b₁} tm (P.keep (ss p)) =
    rni (hs b₁) (ss p)
      (λ y y′ l → brnK k fk ac′ (⊲ᴴ↑ C.self kpos) sk i i hii hii hii Y Y g g (≤-refl _ , g) (lowOut (hs b₁) (ss p) l) (⊲ᴴ↑ C.self tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴴ↑ C.self kpos) sk j j hjj hjj hjj Y′ Y′ g′ g′ (≤-refl _ , g′) (lowOut (hs b₁) (ss p) l) (⊲ᴴ↑ C.self tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴴ↑ C.self kpos) sk i j hii hjj hx Y Y′ g g′ s (lowOut (hs b₁) (ss p) l) (⊲ᴴ↑ C.self tm))
  rkRel {hl f₁} tm (P.keep (sl n p)) =
    rni (hl f₁) (sl n p)
      (λ y y′ l → brnK k fk ac′ (⊲ᴴ↑ C.self kpos) sk i i hii hii hii Y Y g g (≤-refl _ , g) (lowOut (hl f₁) (sl n p) l) (⊲ᴴ↑ C.self tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴴ↑ C.self kpos) sk j j hjj hjj hjj Y′ Y′ g′ g′ (≤-refl _ , g′) (lowOut (hl f₁) (sl n p) l) (⊲ᴴ↑ C.self tm))
      (λ y y′ l → brnK k fk ac′ (⊲ᴴ↑ C.self kpos) sk i j hii hjj hx Y Y′ g g′ s (lowOut (hl f₁) (sl n p) l) (⊲ᴴ↑ C.self tm))
  rkRel {hΩ g₁} tm (P.keep (sL e p)) = tt

  step : P.Run (acc f) (ni r u) C.self lW ll Aᵢ w Y ≼ P.Run (acc f) (ni r u′) C.self lW ll Aⱼ w′ Y′
  step tm = rkRel tm (P.rkT (⊲ᴴ↑ C.self kpos) tm lW)

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
            (λ z z′ l → sndS b fb (acc f) (⊲ᴴ↑ C.self ll) (mu z z′ l))
            (λ z z′ l → sndS b fb (acc f) (⊲ᴴ↑ C.self ll) (mu′ z z′ l))
            (λ z z′ l → sndS b fb (acc f) (⊲ᴴ↑ C.self ll) (cr z z′ l))
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
