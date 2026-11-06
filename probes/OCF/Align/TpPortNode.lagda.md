# 两种种类的单调 (十二): 常数分支的节点, 两边世界与嵌入不同; $\Omega_k$ 的观测

> 入口 [TpPort](TpPort.lagda.md). 不含记号. **生成文件**: 由 `probes/Survey/scripts/tpport/mk_tpport.py` 从 [MonoPort7Node](MonoPort7Node.lagda.md) 逐字节可重生成 (公共变换在同目录的 `tpgen.py`). 公共变换只改: 世界的类型与序 (`A`, `_⊲_` 换成两种种类的 `Wd₂`, `_≤ʷ_`; `C.self`, `C.⊲-tr` 换成 `≤rf`, `≤tr`; `Lg` 换成 `LgW₂`), 高度的类型 (`H` 换成 `Ht`, `LgH` 换成 `LgB`, `hΩ g` 换成 `hΩ κ g`), 模块参数多一个 `oΛ` (第 1 层是实例在一切世界里的第一位置, 两种种类的折叠要它), 数据树多一个构造子 `nμ` (每个 `nκ` 的空子句后加一句), `Step` 换名 `Stp`. 证明逐句不变. 
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`, 不改树、折叠、合法性.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
open import OCF.Align.HtTowerTy using (HB; hz; hs; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; AccY; D)
module OCF.Align.TpPortNode (Λ : Ht) (lΛ : LgB Λ) (oΛ : ∀ {w} → hs hz ⊲[ w ] Λ) {W : Wd₂} (lW : LgW₂ W) (t₀ : hz ⊲[ W ] Λ) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; ≤-refl)
open import OCF.Align.HtTowerTy using (hl; hΩ; hself; ⊲ᴮ↑)
open import OCF.Align.HtTowerFTree using (ss; sl; sL; StH; Vs; acc; accᴸ; accK; accL; outS; n0; n1; _⨾_; nl; ni; nw; Ωd; sum; ≤rf; ≤tr) renaming (_≤_ to _≤ʷ_)
open import OCF.Align.TpPortDef using (val₀)
open import OCF.Align.TpPortRel Λ lΛ oΛ lW t₀
open import OCF.Align.TpPortSnd Λ lΛ oΛ lW t₀ using (chainK; brnK; sndArg; OutsK)

```
```agda
HAKb : ∀ k → P.Ig k W → P.Ig k W → Set
HAKb k A₀ A₁ = ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ → Obs c c′ (A₀ ≤rf lW w Y) (A₁ ≤rf lW w′ Y′)

StepA : ∀ {k} → P.Ig k W
StepA p lW′ z Y = P.Stp Y

hSt : ∀ k → HAKb k StepA StepA
hSt k w w′ c c′ Y Y′ g g′ s cb =
  obs cb (λ {t} tm → rnl t (λ _ → r⨾ t (rΩ t) (rΩ t) (rΩ t) (g tm)) (λ _ → r⨾ t (rΩ t) (rΩ t) (rΩ t) (g′ tm))
                           (λ _ → r⨾ t (rΩ t) (rΩ t) (rΩ t) (proj₂ s tm)))

-- 分支是常数 n1 的节点: 坐标动作 Ai 在作用点上就是外层动作 (上下文被丢掉), 两边的节点、世界、嵌入可以不同
hAi : ∀ {ly k W₁ W₂} (ac₁ ac₂ : AccY ly) (ac′ : AccY k) (r₁ : StH W₁ k ly) (r₂ : StH W₂ k ly) (q₁ : W₁ ≤ʷ W) (q₂ : W₂ ≤ʷ W)
      (pos : k ⊲[ W ] Λ) (ll₁ ll₂ : ly ⊲[ W ] Λ) (A₁ A₂ : P.Ig ly W) (w₁ w₂ : D ly W) → HAKb ly A₁ A₂ →
      HAK k (P.Ai ac₁ ac′ r₁ (λ _ _ _ → n1) q₁ pos ll₁ A₁ w₁) (P.Ai ac₂ ac′ r₂ (λ _ _ _ → n1) q₂ pos ll₂ A₂ w₂)
hAi ac₁ ac₂ ac′ r₁ r₂ q₁ q₂ pos ll₁ ll₂ A₁ A₂ w₁ w₂ h z z′ c c′ Y Y′ _ g g′ s cb = h _ _ c c′ Y Y′ g g′ s cb
```
```agda
RKb : ∀ {k t m} → AccY k → k ⊲[ W ] Λ → P.Ig k W → P.St W → P.Tg W t m → P.Rk k t m → D t m
RKb ac pos i Y T (P.keep R′) =
  ni R′ (λ {W′} p lW′ y →
    P.yc (i (≤tr (P.wm T) p) lW′ (outS R′ y)
            (P._⊕⟨_⟩_ (P.cv (≤tr (P.wm T) p) Y) lW′
               (P.Run ac (outS R′ y) ≤rf lW′ (⊲ᴮ↑ (≤tr (P.wm T) p) pos) (P.Ig↾ (≤tr (P.wm T) p) i) n0 (P.cv (≤tr (P.wm T) p) Y))))
         (P.tg ≤rf (⊲ᴮ↑ p (P.tm T)) lW′))
RKb ac pos i Y T P.rise = nl (λ n → P.yc (OutsK ac pos i Y n) T)

conv : ∀ {ly W₀ k t m} (ac : AccY ly) (ac′ : AccY k) (r : StH W₀ k ly) (u : ∀ {W′} → W₀ ≤ʷ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) (q₀ : W₀ ≤ʷ W) (ll : ly ⊲[ W ] Λ) (A₀ : P.Ig ly W) w Y
       (T : P.Tg W t m) (rk : P.Rk k t m) →
       P.RKi ac ac′ r u q₀ lW ll A₀ w Y T rk ≡ RKb ac′ (P.kk r q₀ ll) (P.Ai ac ac′ r u q₀ (P.kk r q₀ ll) ll A₀ w) Y T rk
conv ac ac′ r u q₀ ll A₀ w Y T (P.keep R′) = refl
conv ac ac′ r u q₀ ll A₀ w Y T P.rise = refl
```
```agda
relB : ∀ k → Fin k → (ac : AccY k) (pos : k ⊲[ W ] Λ) (i j : P.Ig k W) → HAK k i i → HAK k j j → HAK k i j →
       ∀ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → ∀ {t} (tm : t ⊲[ W ] Λ) (rk : P.Rk k t W) →
       Rel t (RKb ac pos i Y (Tt tm) rk) (RKb ac pos j Y′ (Tt tm) rk)
relB k fk ac pos i j hi hj hij Y Y′ g g′ s {t} tm P.rise =
  rnl t (λ n → chainK k fk ac pos (sndArg k fk ac) i i hi hi hi Y Y g g (≤-refl _ , g) n tm)
        (λ n → chainK k fk ac pos (sndArg k fk ac) j j hj hj hj Y′ Y′ g′ g′ (≤-refl _ , g′) n tm)
        (λ n → chainK k fk ac pos (sndArg k fk ac) i j hi hj hij Y Y′ g g′ s n tm)
relB k fk ac pos i j hi hj hij Y Y′ g g′ s {t = hz} tm (P.keep ())
relB k fk ac pos i j hi hj hij Y Y′ g g′ s {t = hs b₁} tm (P.keep (ss p)) =
  rni (hs b₁) (ss p)
    (λ y y′ l → brnK k fk ac (⊲ᴮ↑ ≤rf pos) (sndArg k fk ac) i i hi hi hi Y Y g g (≤-refl _ , g) (lowOut (hs b₁) (ss p) l) (⊲ᴮ↑ ≤rf tm))
    (λ y y′ l → brnK k fk ac (⊲ᴮ↑ ≤rf pos) (sndArg k fk ac) j j hj hj hj Y′ Y′ g′ g′ (≤-refl _ , g′) (lowOut (hs b₁) (ss p) l) (⊲ᴮ↑ ≤rf tm))
    (λ y y′ l → brnK k fk ac (⊲ᴮ↑ ≤rf pos) (sndArg k fk ac) i j hi hj hij Y Y′ g g′ s (lowOut (hs b₁) (ss p) l) (⊲ᴮ↑ ≤rf tm))
relB k fk ac pos i j hi hj hij Y Y′ g g′ s {t = hl f₁} tm (P.keep (sl n p)) =
  rni (hl f₁) (sl n p)
    (λ y y′ l → brnK k fk ac (⊲ᴮ↑ ≤rf pos) (sndArg k fk ac) i i hi hi hi Y Y g g (≤-refl _ , g) (lowOut (hl f₁) (sl n p) l) (⊲ᴮ↑ ≤rf tm))
    (λ y y′ l → brnK k fk ac (⊲ᴮ↑ ≤rf pos) (sndArg k fk ac) j j hj hj hj Y′ Y′ g′ g′ (≤-refl _ , g′) (lowOut (hl f₁) (sl n p) l) (⊲ᴮ↑ ≤rf tm))
    (λ y y′ l → brnK k fk ac (⊲ᴮ↑ ≤rf pos) (sndArg k fk ac) i j hi hj hij Y Y′ g g′ s (lowOut (hl f₁) (sl n p) l) (⊲ᴮ↑ ≤rf tm))
relB k fk ac pos i j hi hj hij Y Y′ g g′ s {t = hΩ _ g₁} tm (P.keep (sL e p)) = tt
```
```agda
nodeSelf : ∀ {ly W₀ k} (r : StH W₀ k ly) → Fin k → (q₀ : W₀ ≤ʷ W) (ll : ly ⊲[ W ] Λ) (A₀ : P.Ig ly W) → HAKb ly A₀ A₀ →
           ∀ w Y → Good Y → P.Run accᴸ (ni r (λ _ _ _ → n1)) q₀ lW ll A₀ w Y ≼ P.Run accᴸ (ni r (λ _ _ _ → n1)) q₀ lW ll A₀ w Y
nodeSelf {k = k} r fk q₀ ll A₀ h w Y g {t} tm =
  subst₂ (Rel t) (sym (conv accᴸ (accK r) r (λ _ _ _ → n1) q₀ ll A₀ w Y (Tt tm) (P.rkT (⊲ᴮ↑ ≤rf (P.kk r q₀ ll)) tm lW)))
                 (sym (conv accᴸ (accK r) r (λ _ _ _ → n1) q₀ ll A₀ w Y (Tt tm) (P.rkT (⊲ᴮ↑ ≤rf (P.kk r q₀ ll)) tm lW)))
    (relB k fk (accK r) (P.kk r q₀ ll) i i hii hii hii Y Y g g (≤-refl _ , g) tm (P.rkT (⊲ᴮ↑ ≤rf (P.kk r q₀ ll)) tm lW))
  where
  i = P.Ai accᴸ (accK r) r (λ _ _ _ → n1) q₀ (P.kk r q₀ ll) ll A₀ w
  hii = hAi accᴸ accᴸ (accK r) r r q₀ q₀ (P.kk r q₀ ll) ll ll A₀ A₀ w w h
```
```agda
data Ac : Set where
  aᴸ aᴷ : Ac

acS : Ac → ∀ k → AccY k
acS aᴸ k = accᴸ
acS aᴷ k = accL k

toBs : ∀ s b {W₀} (q : W₀ ≤ʷ W) (ll : hs b ⊲[ W ] Λ) (A₀ : P.Ig (hs b) W) w Y {t} (tm : t ⊲[ W ] Λ) →
       P.yc (P.Run (acS s (hs b)) (ni (ss {W = W₀} hself) (λ _ _ _ → n1)) q lW ll A₀ w Y) (Tt tm) ≡
       RKb (accL b) (P.kk (ss {W = W₀} hself) q ll) (P.Ai (acS s (hs b)) (accL b) (ss hself) (λ _ _ _ → n1) q (P.kk (ss {W = W₀} hself) q ll) ll A₀ w) Y (Tt tm)
           (P.rkT (⊲ᴮ↑ ≤rf (P.kk (ss {W = W₀} hself) q ll)) tm lW)
toBs aᴸ b q ll A₀ w Y tm = conv accᴸ (accL b) (ss hself) (λ _ _ _ → n1) q ll A₀ w Y (Tt tm) _
toBs aᴷ b q ll A₀ w Y tm = conv (accL (hs b)) (accL b) (ss hself) (λ _ _ _ → n1) q ll A₀ w Y (Tt tm) _

toBl : ∀ s (g : ℕ → Ht) m {W₀} (q : W₀ ≤ʷ W) (ll : hl g ⊲[ W ] Λ) (A₀ : P.Ig (hl g) W) w Y {t} (tm : t ⊲[ W ] Λ) →
       P.yc (P.Run (acS s (hl g)) (ni (sl {W = W₀} m hself) (λ _ _ _ → n1)) q lW ll A₀ w Y) (Tt tm) ≡
       RKb (accL (g m)) (P.kk (sl {W = W₀} m hself) q ll) (P.Ai (acS s (hl g)) (accL (g m)) (sl m hself) (λ _ _ _ → n1) q (P.kk (sl {W = W₀} m hself) q ll) ll A₀ w) Y (Tt tm)
           (P.rkT (⊲ᴮ↑ ≤rf (P.kk (sl {W = W₀} m hself) q ll)) tm lW)
toBl aᴸ g m q ll A₀ w Y tm = conv accᴸ (accL (g m)) (sl m hself) (λ _ _ _ → n1) q ll A₀ w Y (Tt tm) _
toBl aᴷ g m q ll A₀ w Y tm = conv (accL (hl g)) (accL (g m)) (sl m hself) (λ _ _ _ → n1) q ll A₀ w Y (Tt tm) _

-- 两边的常数分支节点 ss hself: 输出相关
ndS : ∀ b → Fin b → (hk : hs b ⊲[ W ] Λ) (s₁ s₂ : Ac) → ∀ {W₁ W₂} (q₁ : W₁ ≤ʷ W) (q₂ : W₂ ≤ʷ W) (A₁ A₂ : P.Ig (hs b) W) →
      HAKb (hs b) A₁ A₁ → HAKb (hs b) A₂ A₂ → HAKb (hs b) A₁ A₂ → ∀ w₁ w₂ Y₁ Y₂ → Good Y₁ → Good Y₂ → SRel Y₁ Y₂ →
      P.Run (acS s₁ (hs b)) (ni (ss {W = W₁} hself) (λ _ _ _ → n1)) q₁ lW hk A₁ w₁ Y₁ ≼ P.Run (acS s₂ (hs b)) (ni (ss {W = W₂} hself) (λ _ _ _ → n1)) q₂ lW hk A₂ w₂ Y₂
ndS b fb hk s₁ s₂ {W₁} q₁ q₂ A₁ A₂ h₁ h₂ h₁₂ w₁ w₂ Y₁ Y₂ g₁ g₂ sr {t} tm =
  subst₂ (Rel t) (sym (toBs s₁ b q₁ hk A₁ w₁ Y₁ tm)) (sym (toBs s₂ b q₂ hk A₂ w₂ Y₂ tm))
    (relB b fb (accL b) pos i j hii hjj hij Y₁ Y₂ g₁ g₂ sr tm (P.rkT (⊲ᴮ↑ ≤rf pos) tm lW))
  where
  pos = P.kk (ss {W = W₁} hself) q₁ hk
  i = P.Ai (acS s₁ (hs b)) (accL b) (ss hself) (λ _ _ _ → n1) q₁ pos hk A₁ w₁
  j = P.Ai (acS s₂ (hs b)) (accL b) (ss hself) (λ _ _ _ → n1) q₂ pos hk A₂ w₂
  hii = hAi (acS s₁ (hs b)) (acS s₁ (hs b)) (accL b) (ss hself) (ss hself) q₁ q₁ pos hk hk A₁ A₁ w₁ w₁ h₁
  hjj = hAi (acS s₂ (hs b)) (acS s₂ (hs b)) (accL b) (ss hself) (ss hself) q₂ q₂ pos hk hk A₂ A₂ w₂ w₂ h₂
  hij = hAi (acS s₁ (hs b)) (acS s₂ (hs b)) (accL b) (ss hself) (ss hself) q₁ q₂ pos hk hk A₁ A₂ w₁ w₂ h₁₂

-- 两边的常数分支节点 sl m hself
ndL : ∀ (g : ℕ → Ht) m → Fin (g m) → (hk : hl g ⊲[ W ] Λ) (s₁ s₂ : Ac) → ∀ {W₁ W₂} (q₁ : W₁ ≤ʷ W) (q₂ : W₂ ≤ʷ W) (A₁ A₂ : P.Ig (hl g) W) →
      HAKb (hl g) A₁ A₁ → HAKb (hl g) A₂ A₂ → HAKb (hl g) A₁ A₂ → ∀ w₁ w₂ Y₁ Y₂ → Good Y₁ → Good Y₂ → SRel Y₁ Y₂ →
      P.Run (acS s₁ (hl g)) (ni (sl {W = W₁} m hself) (λ _ _ _ → n1)) q₁ lW hk A₁ w₁ Y₁ ≼
      P.Run (acS s₂ (hl g)) (ni (sl {W = W₂} m hself) (λ _ _ _ → n1)) q₂ lW hk A₂ w₂ Y₂
ndL g m fm hk s₁ s₂ {W₁} q₁ q₂ A₁ A₂ h₁ h₂ h₁₂ w₁ w₂ Y₁ Y₂ g₁ g₂ sr {t} tm =
  subst₂ (Rel t) (sym (toBl s₁ g m q₁ hk A₁ w₁ Y₁ tm)) (sym (toBl s₂ g m q₂ hk A₂ w₂ Y₂ tm))
    (relB (g m) fm (accL (g m)) pos i j hii hjj hij Y₁ Y₂ g₁ g₂ sr tm (P.rkT (⊲ᴮ↑ ≤rf pos) tm lW))
  where
  pos = P.kk (sl {W = W₁} m hself) q₁ hk
  i = P.Ai (acS s₁ (hl g)) (accL (g m)) (sl m hself) (λ _ _ _ → n1) q₁ pos hk A₁ w₁
  j = P.Ai (acS s₂ (hl g)) (accL (g m)) (sl m hself) (λ _ _ _ → n1) q₂ pos hk A₂ w₂
  hii = hAi (acS s₁ (hl g)) (acS s₁ (hl g)) (accL (g m)) (sl m hself) (sl m hself) q₁ q₁ pos hk hk A₁ A₁ w₁ w₁ h₁
  hjj = hAi (acS s₂ (hl g)) (acS s₂ (hl g)) (accL (g m)) (sl m hself) (sl m hself) q₂ q₂ pos hk hk A₂ A₂ w₂ w₂ h₂
  hij = hAi (acS s₁ (hl g)) (acS s₂ (hl g)) (accL (g m)) (sl m hself) (sl m hself) q₁ q₂ pos hk hk A₁ A₂ w₁ w₂ h₁₂
```
```agda
-- 第一段之后的状态
module Fst {k : Ht} (A₁ A₂ : P.Ig k W) (h₁ : HAKb k A₁ A₁) (h₂ : HAKb k A₂ A₂) (h₁₂ : HAKb k A₁ A₂)
  (w w′ : D k W) (Y Y′ : P.St W) (g : Good Y) (g′ : Good Y′) (s : SRel Y Y′) where
  D₁ = A₁ ≤rf lW w Y
  D₂ = A₂ ≤rf lW w′ Y′
  r₁ : D₁ ≼ D₁
  r₁ = proj₂ (h₁ w w azero azero Y Y g g (≤-refl _ , g) z≤)
  r₂ : D₂ ≼ D₂
  r₂ = proj₂ (h₂ w′ w′ azero azero Y′ Y′ g′ g′ (≤-refl _ , g′) z≤)
  Y₁ = P._⊕⟨_⟩_ Y lW D₁
  Y₂ = P._⊕⟨_⟩_ Y′ lW D₂
  g₁ : Good Y₁
  g₁ = ⨾≼ {P.d Y} {D₁} {P.d Y} {D₁} g g g r₁
  g₂ : Good Y₂
  g₂ = ⨾≼ {P.d Y′} {D₂} {P.d Y′} {D₂} g′ g′ g′ r₂
  o′ = h₁₂ w w′ (G.vY Y) (G.vY Y′) Y Y′ g g′ s (proj₁ s)
  s₁ : SRel Y₁ Y₂
  s₁ = proj₁ o′ , ⨾≼ {P.d Y} {D₁} {P.d Y′} {D₂} g g′ (proj₂ s) (proj₂ o′)

-- 状态加上一段相关的输出, 仍自洽且相关
step⊕ : ∀ {Y Y′ N N′} → Good Y → Good Y′ → SRel Y Y′ → N ≼ N → N′ ≼ N′ → N ≼ N′ →
        Good (P._⊕⟨_⟩_ Y lW N) × (Good (P._⊕⟨_⟩_ Y′ lW N′) × SRel (P._⊕⟨_⟩_ Y lW N) (P._⊕⟨_⟩_ Y′ lW N′))
step⊕ {Y} {Y′} {N} {N′} g g′ s r r′ h =
  ⨾≼ {P.d Y} {N} {P.d Y} {N} g g g r , (⨾≼ {P.d Y′} {N′} {P.d Y′} {N′} g′ g′ g′ r′ ,
  (val₀ (h t₀) (proj₁ s) , ⨾≼ {P.d Y} {N} {P.d Y′} {N′} g g′ (proj₂ s) h))

module Lm (g : ℕ → Ht) (fg : ∀ m → Fin (g m)) (hk : hl g ⊲[ W ] Λ) (s₁ s₂ : Ac) {W₁ W₂} (q₁ : W₁ ≤ʷ W) (q₂ : W₂ ≤ʷ W)
  (A₁ A₂ : P.Ig (hl g) W) (h₁ : HAKb (hl g) A₁ A₁) (h₂ : HAKb (hl g) A₂ A₂) (h₁₂ : HAKb (hl g) A₁ A₂)
  (w₁ w₂ : D (hl g) W) (Y₁ Y₂ : P.St W) (g₁ : Good Y₁) (g₂ : Good Y₂) (sr : SRel Y₁ Y₂) where
  F₁ : ℕ → D (hl g) W₁
  F₁ m = ni (sl m hself) (λ _ _ _ → n1)
  F₂ : ℕ → D (hl g) W₂
  F₂ m = ni (sl m hself) (λ _ _ _ → n1)
  R₁ R₂ : ℕ → D (hl g) W × P.St W
  R₁ = P.Rpt (acS s₁ (hl g)) F₁ q₁ lW hk A₁ w₁ Y₁
  R₂ = P.Rpt (acS s₂ (hl g)) F₂ q₂ lW hk A₂ w₂ Y₂
  N₁ N₂ : ℕ → P.Df W
  N₁ m = P.Run (acS s₁ (hl g)) (F₁ m) q₁ lW hk A₁ (proj₁ (R₁ m)) (proj₂ (R₁ m))
  N₂ m = P.Run (acS s₂ (hl g)) (F₂ m) q₂ lW hk A₂ (proj₁ (R₂ m)) (proj₂ (R₂ m))

  Inv : ℕ → Set
  Inv m = Good (proj₂ (R₁ m)) × (Good (proj₂ (R₂ m)) × SRel (proj₂ (R₁ m)) (proj₂ (R₂ m)))

  nd : ∀ m → Inv m → (N₁ m ≼ N₁ m) × ((N₂ m ≼ N₂ m) × (N₁ m ≼ N₂ m))
  nd m (a , (b , c)) =
    ndL g m (fg m) hk s₁ s₁ q₁ q₁ A₁ A₁ h₁ h₁ h₁ _ _ _ _ a a (≤-refl _ , a) ,
    (ndL g m (fg m) hk s₂ s₂ q₂ q₂ A₂ A₂ h₂ h₂ h₂ _ _ _ _ b b (≤-refl _ , b) ,
     ndL g m (fg m) hk s₁ s₂ q₁ q₂ A₁ A₂ h₁ h₂ h₁₂ _ _ _ _ a b c)

  inv : ∀ m → Inv m
  inv zero = g₁ , (g₂ , sr)
  inv (suc m) = step⊕ (proj₁ (inv m)) (proj₁ (proj₂ (inv m))) (proj₂ (proj₂ (inv m)))
                  (proj₁ (nd m (inv m))) (proj₁ (proj₂ (nd m (inv m)))) (proj₂ (proj₂ (nd m (inv m))))

  out : P.nlᴰ N₁ ≼ P.nlᴰ N₂
  out = nl≼ {N₁} {N₂} (λ m → proj₁ (nd m (inv m))) (λ m → proj₁ (proj₂ (nd m (inv m)))) (λ m → proj₂ (proj₂ (nd m (inv m))))

ΩdObs : ∀ k → Fin k → (hk : k ⊲[ W ] Λ) (s₁ s₂ : Ac) → ∀ {W₀ W₀′} (q₀ : W₀ ≤ʷ W) (q₀′ : W₀′ ≤ʷ W) (A₁ A₂ : P.Ig k W) →
        HAKb k A₁ A₁ → HAKb k A₂ A₂ → HAKb k A₁ A₂ →
        ∀ w w′ c c′ Y Y′ → Good Y → Good Y′ → SRel Y Y′ → c ≤ c′ →
        Obs c c′ (P.Run (acS s₁ k) (Ωd k {W₀}) q₀ lW hk A₁ w Y) (P.Run (acS s₂ k) (Ωd k {W₀′}) q₀′ lW hk A₂ w′ Y′)
ΩdObs hz fk hk s₁ s₂ q₀ q₀′ A₁ A₂ h₁ h₂ h₁₂ w w′ c c′ Y Y′ g g′ s cb = h₁₂ w w′ c c′ Y Y′ g g′ s cb
ΩdObs (hs b) fk hk s₁ s₂ {W₀} {W₀′} q₀ q₀′ A₁ A₂ h₁ h₂ h₁₂ w w′ c c′ Y Y′ g g′ s cb =
  val₀ (hN t₀) (proj₁ o) , ⨾≼ {F.D₁} {N₁} {F.D₂} {N₂} F.r₁ F.r₂ (proj₂ o) hN
  where
  module F = Fst A₁ A₂ h₁ h₂ h₁₂ w w′ Y Y′ g g′ s
  o = h₁₂ w w′ c c′ Y Y′ g g′ s cb
  N₁ = P.Run (acS s₁ (hs b)) (ni (ss {W = W₀} hself) (λ _ _ _ → n1)) q₀ lW hk A₁ (w ⨾ nw q₀ (n1 {W = W₀})) F.Y₁
  N₂ = P.Run (acS s₂ (hs b)) (ni (ss {W = W₀′} hself) (λ _ _ _ → n1)) q₀′ lW hk A₂ (w′ ⨾ nw q₀′ (n1 {W = W₀′})) F.Y₂
  hN : N₁ ≼ N₂
  hN = ndS b fk hk s₁ s₂ q₀ q₀′ A₁ A₂ h₁ h₂ h₁₂ _ _ F.Y₁ F.Y₂ F.g₁ F.g₂ F.s₁
ΩdObs (hl g₀) fk hk s₁ s₂ {W₀} {W₀′} q₀ q₀′ A₁ A₂ h₁ h₂ h₁₂ w w′ c c′ Y Y′ g g′ s cb =
  val₀ (M.out t₀) (proj₁ o) , ⨾≼ {F.D₁} {P.nlᴰ M.N₁} {F.D₂} {P.nlᴰ M.N₂} F.r₁ F.r₂ (proj₂ o) M.out
  where
  module F = Fst A₁ A₂ h₁ h₂ h₁₂ w w′ Y Y′ g g′ s
  o = h₁₂ w w′ c c′ Y Y′ g g′ s cb
  module M = Lm g₀ fk hk s₁ s₂ q₀ q₀′ A₁ A₂ h₁ h₂ h₁₂ (w ⨾ nw q₀ (n1 {W = W₀})) (w′ ⨾ nw q₀′ (n1 {W = W₀′})) F.Y₁ F.Y₂ F.g₁ F.g₂ F.s₁
ΩdObs (hΩ _ f) () hk s₁ s₂ q₀ q₀′ A₁ A₂ h₁ h₂ h₁₂ w w′ c c′ Y Y′ g g′ s cb
```
