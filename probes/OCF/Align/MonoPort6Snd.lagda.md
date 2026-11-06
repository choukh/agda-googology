# 一步对一切有限高度 (五): 节点一步与对层的归纳

> 入口 [MonoPort6](MonoPort6.lagda.md). 不含记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> 一句话: **"坐标层 $k$ 的 `snd` (两个动作, 一切目标) ⇒ 层 `hs b` 的节点一步"** (`Node.step`), 再对 (良基证明, 推导) 归纳一次 (`sndS`, `sndArg`). 节点一步不看层号: 输出在目标 `tm` 上的读数是 `RKi … (rkT …)`, 我们对 `Rk` 的**值**分情形 (`rkRel`), 不计算 `rkT`: `rise` 时用层 $k$ 的链 (`chainK`), `keep (ss p)` 时用层 $k$ 的分支一步 (`brnK`). 于是上一组的障碍 (i) (`rkT` 的取值引理) 不出现; 障碍 (ii) (位置等式与 `subst`) 也不出现, 因为一切陈述对位置全称, 递归调用时直接取折叠给出的位置 (`kk r …`, `⊲ᴴ↑ C.self …`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtFeedTree using (H; LgH; hz; _⊲[_]_)
module OCF.Align.MonoPort6Snd (Λ : H) (lΛ : LgH Λ) {W : A} (lW : Lg W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtFeedTree using (hs; hl; hΩ; ss; sl; sL; StH; Vs; D; AccY; acc; mkOf; inS; outS; ⊲ᴴ↑;
  n0; n1; _⨾_; nl; ni; nw)
open import OCF.Align.StrRelDef lW using (_⊑₀_; refl₀) renaming (preL to preLˢ)
open import OCF.Align.MonoPort6Rel Λ lΛ lW t₀
open import OCF.Align.MonoPort6Int Λ lΛ lW t₀ using (IntMK; cx00; module CxS)
open import OCF.Align.MonoPort6Lay Λ lΛ lW t₀ using (module L)
open import OCF.Align.MonoPort5Rel lW using (module RelM)
import OCF.Align.MonoPort6Zero as Z

module B₀ (ac : AccY hz) (ll : hz ⊲[ W ] Λ) = Z.B Λ lΛ lW t₀ O preO ac ll (λ h → h ll)

preL≡ : ∀ {ly V} (d : ℕ → D ly V) k → preLˢ d k ≡ G.preL d k
preL≡ d zero = refl
preL≡ d (suc k) = cong (λ t → t ⨾ d k) (preL≡ d k)
```

## 1 各层的语义, 链, 分支一步 (对层分两种: 第 0 层与 `hs b`)

```agda
toHA₀ : ∀ ac ll (i j : P.Ig hz W) → HAK hz i j → B₀.HA ac ll i j
toHA₀ ac ll i j h w w′ c c′ Y Y′ (B₀.cx cw) = h w w′ c c′ Y Y′ cw

SemK : ∀ k → AccY k → k ⊲[ W ] Λ → D k W → D k W → Set
SemK hz ac ll x x′ = ∀ (Aᵢ Aⱼ : P.Ig hz W) → HAK hz Aᵢ Aᵢ → HAK hz Aⱼ Aⱼ → HAK hz Aᵢ Aⱼ → B₀.Sem ac ll Aᵢ Aⱼ x x′
SemK (hs b) ac ll = L.SemS b ac ll
SemK (hl f) _ _ _ _ = ⊤
SemK (hΩ g) _ _ _ _ = ⊤

SndArg : ∀ k → AccY k → Set
SndArg k ac = ∀ pos {x x′} → Rel k x x′ → SemK k ac pos x x′

-- 链的第 n 段输出 (对一切层, 字面就是折叠的 Chn)
OutsK : ∀ {k} → AccY k → k ⊲[ W ] Λ → P.Ig k W → P.St W → ℕ → P.Df W
OutsK ac pos A₂ Y n =
  P.Run ac (proj₁ (proj₂ (P.Chn ac pos lW A₂ Y n))) C.self lW pos A₂ (proj₁ (P.Chn ac pos lW A₂ Y n)) (proj₂ (proj₂ (P.Chn ac pos lW A₂ Y n)))

chainK : ∀ k → Fin k → (ac : AccY k) (pos : k ⊲[ W ] Λ) → SndArg k ac → (i j : P.Ig k W) → HAK k i i → HAK k j j → HAK k i j →
         ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ n → OutsK ac pos i Y n ≼ OutsK ac pos j Y′ n
chainK hz fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (B₀.Chain.chain₀ ac pos i j (toHA₀ ac pos i i hi) (toHA₀ ac pos j j hj) (toHA₀ ac pos i j hij) Y Y′ azero azero g g′ s z≤)
chainK (hs b) fk ac pos sk i j hi hj hij Y Y′ g g′ s =
  proj₂ (L.Ch.chainG b ac pos (sk pos) i j hi hj hij Y Y′ azero azero g g′ s z≤)

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
  L.brn b ac pos i j hi hj hij Y Y′ g g′ s (sk pos (cxRel (hs b) cz)) (sk pos (proj₁ (cxL (hs b) cz))) (sk pos (proj₁ (cxR (hs b) cz))) cz
```

## 2 节点一步: 一句话, 对一切节点层、坐标层与目标层

```agda
module Node (b : H) (fb : Fin b) (f : ∀ {W₁ k} → StH W₁ k (hs b) → AccY k) (ll : hs b ⊲[ W ] Λ)
  {k : H} (Pk : k ⊲[ W ] b) (u u′ : ∀ {W′} → W ⊲ W′ → Lg W′ → Vs (hs b) (ss Pk) W′ → D (hs b) W′)
  (sk : SndArg k (f (ss Pk)))
  (mu  : ∀ z z′ → LowT (hs b) (ss Pk) z z′ → Rel (hs b) (u C.self lW z) (u C.self lW z′))
  (mu′ : ∀ z z′ → LowT (hs b) (ss Pk) z z′ → Rel (hs b) (u′ C.self lW z) (u′ C.self lW z′))
  (cr  : ∀ z z′ → LowT (hs b) (ss Pk) z z′ → Rel (hs b) (u C.self lW z) (u′ C.self lW z′))
  (su  : ∀ z z′ → LowT (hs b) (ss Pk) z z′ → L.SemS b (acc f) (⊲ᴴ↑ C.self ll) (u C.self lW z) (u C.self lW z′))
  (su′ : ∀ z z′ → LowT (hs b) (ss Pk) z z′ → L.SemS b (acc f) (⊲ᴴ↑ C.self ll) (u′ C.self lW z) (u′ C.self lW z′))
  (sc  : ∀ z z′ → LowT (hs b) (ss Pk) z z′ → L.SemS b (acc f) (⊲ᴴ↑ C.self ll) (u C.self lW z) (u′ C.self lW z′))
  (Aᵢ Aⱼ : P.Ig (hs b) W) (hi : HAK (hs b) Aᵢ Aᵢ) (hj : HAK (hs b) Aⱼ Aⱼ) (hij : HAK (hs b) Aᵢ Aⱼ)
  (w w′ : D (hs b) W) (Y Y′ : P.St W) (cw : Ctx (hs b) w w′) (g : Good Y) (g′ : Good Y′) (s : SRel Y Y′) where

  r = ss Pk
  fk = fin⊲ Pk fb
  ac′ = f r
  kpos = P.kk r C.self ll
  Ub = ∀ {W′} → W ⊲ W′ → Lg W′ → Vs (hs b) r W′ → D (hs b) W′
  module LK = L.K b (acc f) (⊲ᴴ↑ C.self ll)

  AiA : Ub → P.Ig (hs b) W → D (hs b) W → P.Ig k W
  AiA u₁ A₁ w₁ = P.Ai (acc f) ac′ r u₁ C.self kpos ll A₁ w₁

  -- 坐标层的动作前提 = 分支的语义 + 上下文相关 (要 Int 单调)
  hAi : ∀ {u₁ u₂ : Ub} (A₁ A₂ : P.Ig (hs b) W) {w₁ w₂} →
        (∀ z z′ → LowT (hs b) r z z′ → Rel (hs b) (u₁ C.self lW z) (u₁ C.self lW z′)) →
        (∀ z z′ → LowT (hs b) r z z′ → Rel (hs b) (u₂ C.self lW z) (u₂ C.self lW z′)) →
        (∀ z z′ → LowT (hs b) r z z′ → Rel (hs b) (u₁ C.self lW z) (u₂ C.self lW z′)) →
        (∀ z z′ → LowT (hs b) r z z′ → L.SemS b (acc f) (⊲ᴴ↑ C.self ll) (u₁ C.self lW z) (u₂ C.self lW z′)) →
        HAK (hs b) A₁ A₁ → HAK (hs b) A₂ A₂ → HAK (hs b) A₁ A₂ → Ctx (hs b) w₁ w₂ → HAK k (AiA u₁ A₁ w₁) (AiA u₂ A₂ w₂)
  hAi {u₁} {u₂} A₁ A₂ m₁₁ m₂₂ m₁₂ s₁₂ h₁ h₂ h₁₂ cw₁ z z′ c c′ Y₁ Y₂ cz g₁ g₂ s₁ cb =
    s₁₂ (inS r z) (inS r z′) (lowIn (hs b) r cz) (P.Ig↾ C.self A₁) (P.Ig↾ C.self A₂) h₁ h₂ h₁₂ tt tt _ _ c c′ Y₁ Y₂ (LK.cx ctx) g₁ g₂ s₁ cb
    where
    mo : ∀ {v₁ v₂ : Ub} → (∀ z z′ → LowT (hs b) r z z′ → Rel (hs b) (v₁ C.self lW z) (v₂ C.self lW z′)) → ∀ (y y′ : D k W) → Ctx k y y′ →
         Rel (hs b) (v₁ C.self lW (inS r y)) (v₂ C.self lW (inS r y′))
    mo m y y′ cy = m (inS r y) (inS r y′) (lowIn (hs b) r cy)
    ctx = CxS.ctxN b cw₁
            (IntMK k fk ac′ tt (mkOf r C.self) (mo {u₁} {u₁} m₁₁) (mo {u₂} {u₂} m₂₂) (mo {u₁} {u₂} m₁₂) cz (cx00 k))
            (IntMK k fk ac′ tt (mkOf r C.self) (mo {u₁} {u₁} m₁₁) (mo {u₁} {u₁} m₁₁) (mo {u₁} {u₁} m₁₁) (cxL k cz) (cx00 k))
            (IntMK k fk ac′ tt (mkOf r C.self) (mo {u₂} {u₂} m₂₂) (mo {u₂} {u₂} m₂₂) (mo {u₂} {u₂} m₂₂) (cxR k cz) (cx00 k))

  i = AiA u Aᵢ w
  j = AiA u′ Aⱼ w′
  hii = hAi {u} {u} Aᵢ Aᵢ mu mu mu su hi hi hi (cxL (hs b) cw)
  hjj = hAi {u′} {u′} Aⱼ Aⱼ mu′ mu′ mu′ su′ hj hj hj (cxR (hs b) cw)
  hx  = hAi {u} {u′} Aᵢ Aⱼ mu mu′ cr sc hi hj hij cw

  -- 对 Rk 的值分情形: 上升用链, 保留用分支一步
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
  rkRel {hl f₁} tm (P.keep (sl n p)) = tt
  rkRel {hΩ g₁} tm (P.keep (sL e p)) = tt

  step : P.Run (acc f) (ni r u) C.self lW ll Aᵢ w Y ≼ P.Run (acc f) (ni r u′) C.self lW ll Aⱼ w′ Y′
  step tm = rkRel tm (P.rkT (⊲ᴴ↑ C.self kpos) tm lW)
```

## 3 对 (良基证明, 推导) 的一次归纳

`sndS` 对层 `hs b` 的推导归纳, 节点句调用 `Node.step`: 坐标层 $k$ 的 `snd` 取在更小的良基证明 `f (ss P)` 上 (`sndArg`), 分支的 `snd` 取在同一个良基证明、更小的推导上, 位置换成折叠给出的 `⊲ᴴ↑ C.self ll`. 第 0 层由 `MonoPort6Zero` 给出, 不递归.

```agda
sndS : ∀ b → Fin b → (ac : AccY (hs b)) (ll : hs b ⊲[ W ] Λ) {x x′ : D (hs b) W} → Rel (hs b) x x′ → L.SemS b ac ll x x′
sndArg : ∀ k → Fin k → (ac : AccY k) → SndArg k ac

sndArg hz fk ac pos h Aᵢ Aⱼ hi hj hij = B₀.snd₀ ac pos h Aᵢ Aⱼ (toHA₀ ac pos Aᵢ Aᵢ hi) (toHA₀ ac pos Aⱼ Aⱼ hj) (toHA₀ ac pos Aᵢ Aⱼ hij)
sndArg (hs b) fk ac pos h = sndS b fk ac pos h

sndS b fb ac ll RelM.n0⊑ Aᵢ Aⱼ hi hj hij = L.n0S b ac ll
sndS b fb ac ll RelM.n1⊑ Aᵢ Aⱼ hi hj hij = L.n1S b ac ll (L.toHA b ac ll Aᵢ Aⱼ hij)
sndS b fb ac ll (RelM.⨾⊑ rx rx′ hx hy) Aᵢ Aⱼ hi hj hij =
  L.⨾S b ac ll (sndS b fb ac ll rx Aᵢ Aᵢ hi hi hi) (sndS b fb ac ll rx′ Aⱼ Aⱼ hj hj hj) (sndS b fb ac ll hx Aᵢ Aⱼ hi hj hij)
    (L.K.inn (hx , (rx , rx′))) (sndS b fb ac ll hy Aᵢ Aⱼ hi hj hij)
sndS b fb ac ll (RelM.nl⊑ rd rd′ hd) Aᵢ Aⱼ hi hj hij =
  L.nlS b ac ll (λ n → sndS b fb ac ll (rd n) Aᵢ Aᵢ hi hi hi) (λ n → sndS b fb ac ll (rd′ n) Aⱼ Aⱼ hj hj hj)
    (λ n → sndS b fb ac ll (hd n) Aᵢ Aⱼ hi hj hij) (λ n → L.K.inn (hd n , (rd n , rd′ n)))
sndS b fb (acc f) ll (RelM.ni⊑ {k = k} (ss Pk) {u = u} {u′ = u′} mu mu′ cr) Aᵢ Aⱼ hi hj hij tt tt w w′ c c′ Y Y′ (L.K.cx cw) g g′ s cb =
  obs cb (Node.step b fb f ll Pk u u′ (sndArg k (fin⊲ Pk fb) (f (ss Pk))) mu mu′ cr
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
