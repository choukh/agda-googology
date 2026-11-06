# 链从 0 起 (一): 第 1 层回灌的链从底起的折叠

> 不含记号. 入口 [ChainZ](ChainZ.lagda.md). 审查 D2 的第一条引理: 在 [HtTowerFFold](HtTowerFFold.lagda.md) 的新种类闭包 (`RunM`) 里, 链从底起, 不读界.
>
> - 原折叠: 第 $n$ 格的世界是 $(a, v_n)$, $v_0=\mathrm{rd}(\beta, z_1)$ ($\beta$ 是世界的高度界, $z_1$ 是当前世界以来第 1 层的输出), $v_{n+1}=\mathrm{rd}(v_n,\Delta_n)$. 链的第 0 格**读界** $\beta$.
> - 这里: 链 $x_0=\mathrm{hz}$, $x_{n+1}=\mathrm{rd}(x_n,\Delta_n)$ (`rd` 以链自己的上一格为底, 即 $x_n\boxplus$ 读回), **链的值从不读界**; 第 $n$ 格的世界是 $(a,\beta\boxplus x_n)$, 即 `step S₀` 上只增长的世界操作 "高度界接上 $x_n$" (`DiagK3Grow.growW` 在这一级的样子: 一个分量, 不判定). 格有界就是 `hself`; 世界变大由 `⊞-fst`, 相邻格由 `⊞-⊲` 加 `rd-fst`.
> - 记录 `ClZ` 存链的值 $x_n$ 与它的合法; 格的界 $\beta\boxplus x_n$ 是算出来的 (`toCl`), 不存. 别的一切 (`Cl₁`, `KG`, 状态, 目标) 从 `HtTowerFFold` 以同样的模块参数导入.
> - 第 0 格的值由模块参数 `sd` 从状态里的 `z₁` 算出 (`sd` 的两个实例都不看界). `sd = hz` 时链会停在底: 第 0 格的界就是当前世界, 若节点就在当前世界造的, 从节点的界走到它是空的, $\Delta_0$ 空, $x_1=\mathrm{rd}(\mathrm{hz},\Delta_0)=\mathrm{hz}$, 以后各格同理 (见 `ChainZTest`).
>
> **复制的说明.** `Run` 与 `RunM` 在同一个互递归块里, 换掉 `κc₁` 就要重写整块; 块里除 `κc₁` 的两条子句与它的类型、`RKμ` 里五处 `toCl` 外, 逐字取自 `HtTowerFFold` §5 (由脚本按行号抽取, 不手抄). 这是这一篇唯一的复制, 计入翻译账与行数.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (D₊; Ht; Wd₂; LgW₂; H₀)
open import OCF.Align.HtTowerFRead using (D₁)
module OCF.Align.ChainZFold
  (S : ∀ {Kd : Wd₂ → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wd₂ → Set} {Z₀ Z₁ : Set} {W} → D₊ Kd V′ Z₀ Z₁ W → D₊ Kd V′ Z₀ Z₁ W)
  (Λ : Ht) (lΛ : LgB Λ) (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ)
  (sd : ∀ {W} → LgW₂ W → D₁ W → H₀) (lsd : ∀ {W} (lW : LgW₂ W) t → LgB (sd lW t)) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy hiding (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerTy using (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFRead using (D₁; rd; rd-fst; Lg-rd; drp₁)
open import OCF.Align.HtTowerFFold S Λ lΛ one⊲
  hiding (Run; Rpt; RunNi; Ai; Chn; RKi; BNi; Walk₁; WRp₁; RunM; RKμ; RKμk; Kp₁; Kb₁; κc₁; κΔ₁)
```

## §1 链的一格

```agda
record ClZ (W W₀ : Wd₂) (ly : Ht) : Set where
  constructor mkZ
  field
    xz   : H₀
    lxz  : LgB xz
    a₁z  : H₀
    ap₁z : proj₂ W₀ ⊲[ proj₁ W ] a₁z
    av₁z : a₁z ⊲[ proj₁ W ] proj₂ W ⊞ xz
    Svz  : St (proj₁ W , proj₂ W ⊞ xz)
    coz  : D ly (proj₁ W , proj₂ W ⊞ xz)
open ClZ public

-- 格的界是算出来的: 世界的高度界接上链的值
toCl : ∀ {W W₀ ly} → LgW₂ W → ClZ W W₀ ly → Cl₁ W W₀ ly
toCl {W} lW c =
  mkCl₁ (proj₂ W ⊞ xz c) (Lg-⊞ (proj₂ W) (xz c) (proj₂ lW) (lxz c)) (⊞-fst (proj₂ W) (xz c))
    (a₁z c) (ap₁z c) (av₁z c) (Svz c) (coz c)
```

## §2 折叠 (互递归块; 只有 `κc₁` 变了)

```agda
Run   : ∀ {ly W₀ W} → AccY ly → D ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Df W
Rpt   : ∀ {ly W₀ W} → AccY ly → (ℕ → D ly W₀) → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → ℕ → D ly W × St W
RunNi : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Df W
Ai    : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW k W → LW ly W → Ig ly W → D ly W → Ig k W
Chn   : ∀ {k W} → AccY k → LW k W → LgW₂ W → Ig k W → St W → ℕ → D k W × (D k W × St W)
RKi   : ∀ {ly W₀ W k t m} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → Rk k t m → D t m
BNi   : ∀ {ly W₀ W k W′} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → LW k W → W ≤ W′ → LgW₂ W′ → D k W′ → Df W′
Walk₁ : ∀ {ly W₀ V₁} → AccY ly → NZ ly → Bu ly W₀ → (b : H₀) {a : H₀} → a ⊲[ proj₁ V₁ ] b → proj₂ W₀ ⊲[ proj₁ V₁ ] a → LgB b → b ⊲[ proj₁ V₁ ] proj₂ V₁ →
        proj₁ W₀ ⊲ proj₁ V₁ → LgW₂ V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → Df V₁
WRp₁  : ∀ {ly W₀ V₁ a n} → AccY ly → NZ ly → Bu ly W₀ → (f : ℕ → H₀) (stp : ∀ {w} n → f n ⊲[ w ] f (suc n)) (lf : ∀ n → LgB (f n)) →
        a ⊲[ proj₁ V₁ ] f n → proj₂ W₀ ⊲[ proj₁ V₁ ] a → (∀ m → f m ⊲[ proj₁ V₁ ] proj₂ V₁) → proj₁ W₀ ⊲ proj₁ V₁ →
        LgW₂ V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → ℕ → D ly V₁ × St V₁
RunM  : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Df W
RKμ   : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → ∀ t {m} → Tg W t m → D t m
RKμk  : ∀ {ly W₀ W t m} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → NZ₁ t → D t m
Kp₁   : ∀ {ly W₀ W W⁺} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → W ≤ W⁺ → LgW₂ W⁺ → Df W⁺
Kb₁   : ∀ {ly W₀ W W⁺ W′} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → W ≤ W⁺ → LgW₂ W⁺ → W⁺ ≤ W′ → LgW₂ W′ → Df W′
κc₁   : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → ℕ → ClZ W W₀ ly
κΔ₁   : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → (c : Cl₁ W W₀ ly) → Df (proj₁ W , v₁ c)

Run ac n0 q₀ lW ll A₀ w Y = zeroD
Run ac n1 q₀ lW ll A₀ w Y = A₀ ≤rf lW w Y
Run ac (x ⨾ y) q₀ lW ll A₀ w Y =
  Run ac x q₀ lW ll A₀ w Y ⨾ᴰ Run ac y q₀ lW ll A₀ (w ⨾ nw q₀ x) (Y ⊕⟨ lW ⟩ Run ac x q₀ lW ll A₀ w Y)
Run ac (nl F) q₀ lW ll A₀ w Y =
  nlᴰ (λ n → Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))
Run ac (nw p x) q₀ lW ll A₀ w Y = Run ac x (≤tr p q₀) lW ll A₀ w Y
Run (acc f) (ni r u) q₀ lW ll A₀ w Y = RunNi (acc f) (f r) r u q₀ lW ll A₀ w Y
Run ac (nκ zz u) q₀ lW ll A₀ w Y =
  KG.KR.RunK u (λ p lc q lV ll′ A′ co′ Y′ → Run ac (u p lc) q lV ll′ A′ co′ Y′) q₀ lW ll A₀ w Y
Run {ly} ac (nμ zz u) q₀ lW ll A₀ w Y = RunM ac (nz₁→nz ly zz) u q₀ lW ll A₀ w Y

Rpt ac F q₀ lW ll A₀ w Y zero = w , Y
Rpt ac F q₀ lW ll A₀ w Y (suc n) =
  (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n) ⨾ nw q₀ (F n)) ,
  (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n) ⊕⟨ lW ⟩ Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))

RunNi ac ac′ r u q₀ lW ll A₀ w Y =
  df (λ T → RKi ac ac′ r u q₀ lW ll A₀ w Y T (rkT (⊲ᴮ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T)))

Ai ac ac′ r u q₀ hk ll A₀ w {W′} p lW′ z Y′ =
  Run ac (u (≤tr q₀ p) lW′ (inS r z)) ≤rf lW′ (⊲ᴮ↑ p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac′ z ≤rf lW′ (NZ-S r) (NZ₁-S r) (mkOf r (≤tr q₀ p)) (λ p′ l′ z′ → u (≤tr (≤tr q₀ p) p′) l′ (inS r z′)) n0) Y′

BNi ac ac′ r u q₀ ll A₀ w Y hk p lW′ z =
  Ai ac ac′ r u q₀ hk ll A₀ w p lW′ z
    (cv p Y ⊕⟨ lW′ ⟩ Run ac′ z ≤rf lW′ (⊲ᴮ↑ p hk) (Ig↾ p (Ai ac ac′ r u q₀ hk ll A₀ w)) n0 (cv p Y))

Chn ac′ hk lW A² Y zero = n0 , (yc (d Y) (tg ≤rf hk lW) , Y)
Chn ac′ hk lW A² Y (suc n) =
  (proj₁ (Chn ac′ hk lW A² Y n) ⨾ proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ,
  (yc (Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
      (tg ≤rf hk lW) ,
   (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)) ⊕⟨ lW ⟩
      Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))))

RKi ac ac′ r u q₀ lW ll A₀ w Y T (keep R′) =
  ni R′ (λ {W′} p lW′ y →
    yc (BNi ac ac′ r u q₀ ll A₀ w Y (kk r q₀ ll) (≤tr (wm T) p) lW′ (outS R′ y))
       (tg ≤rf (⊲ᴮ↑ p (tm T)) lW′))
RKi ac ac′ r u q₀ lW ll A₀ w Y T rise =
  nl (λ n →
    yc (Run ac′ (proj₁ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))) ≤rf lW (kk r q₀ ll)
              (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w)
              (proj₁ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))
              (proj₂ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n)))) T)
```

**沿高度坐标走** (`Walk₁`, 原样).

```agda
Walk₁ ac zy u b hself ap lb bV q lV ll A₀ co Y = zeroD
Walk₁ ac zy u (hs b) (hsuc P) ap lb bV q lV ll A₀ co Y =
  Walk₁ ac zy u b P ap lb (⊲ᴮ-tr (hsuc hself) bV) q lV ll A₀ co Y ⨾ᴰ
  Run ac (u (q , ⊲ᴮ-tr ap P) (proj₁ lV , lb)) (C.self , ⊲ᴮ-tr (hsuc hself) bV) lV ll A₀
    (co ⨾ Cut₁ zy u b P ap lb (⊲ᴮ-tr (hsuc hself) bV) q (proj₁ lV))
    (Y ⊕⟨ lV ⟩ Walk₁ ac zy u b P ap lb (⊲ᴮ-tr (hsuc hself) bV) q lV ll A₀ co Y)
Walk₁ ac zy u (hl f) (hlim n P) ap (stp , lf) bV q lV ll A₀ co Y =
  Walk₁ ac zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q lV ll A₀ co Y ⨾ᴰ
  nlᴰ (λ m → Walk₁ ac zy u (f (suc (m + n))) (stp (m + n)) (⊲ᴮ-tr ap (tailᴮ f stp P m)) (lf (suc (m + n))) (⊲ᴮ-tr (hlim (suc (m + n)) hself) bV) q lV ll A₀
        (proj₁ (WRp₁ ac zy u f stp lf P ap (λ m₁ → ⊲ᴮ-tr (hlim m₁ hself) bV) q lV ll A₀
                  (co ⨾ Cut₁ zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q (proj₁ lV))
                  (Y ⊕⟨ lV ⟩ Walk₁ ac zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q lV ll A₀ co Y) m))
        (proj₂ (WRp₁ ac zy u f stp lf P ap (λ m₁ → ⊲ᴮ-tr (hlim m₁ hself) bV) q lV ll A₀
                  (co ⨾ Cut₁ zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q (proj₁ lV))
                  (Y ⊕⟨ lV ⟩ Walk₁ ac zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q lV ll A₀ co Y) m)))
Walk₁ {ly} {W₀} {V₁} ac zy u (hΩ tt h) (hLim {c = c₀} e P) ap (mo , lh) bV q lV ll A₀ co Y =
  Walk₁ ac zy u (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lV))) (⊲ᴮ-tr (hLim e hself) bV) q lV ll A₀ co Y ⨾ᴰ
  KG.KR.RunK {ly} {proj₁ V₁} {proj₂ V₁}
    (λ {c} p lc → Cut₁ zy u (h c) (mo lc (⊲-tr e p) C.self (⊲-tr e p)) (⊲ᴮ↑ {S₀} p (⊲ᴮ-tr ap P)) (lh c lc)
                       (⊲ᴮ-tr {S₀} (hLim C.self hself) (⊲ᴮ↑ {S₀} p bV)) (⊲-tr q p) lc)
    (λ {c} p lc {V} qV lV′ ll′ A′ co′ Y′ →
       Walk₁ ac zy u (h c) (⊲ᴮ↑ {S₀} (proj₁ qV) (mo lc (⊲-tr e p) C.self (⊲-tr e p))) (⊲ᴮ↑ {S₀} (⊲-tr p (proj₁ qV)) (⊲ᴮ-tr ap P)) (lh c lc)
             (⊲ᴮ-tr {S₀} (⊲ᴮ↑ {S₀} (proj₁ qV) (⊲ᴮ-tr {S₀} (hLim C.self hself) (⊲ᴮ↑ {S₀} p bV))) (proj₂ qV)) (⊲-tr (⊲-tr q p) (proj₁ qV)) lV′ ll′ A′ co′ Y′)
    ≤rf lV ll A₀
    (co ⨾ Cut₁ zy u (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lV))) (⊲ᴮ-tr (hLim e hself) bV) q (proj₁ lV))
    (Y ⊕⟨ lV ⟩ Walk₁ ac zy u (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lV))) (⊲ᴮ-tr (hLim e hself) bV) q lV ll A₀ co Y)

WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y zero = co , Y
WRp₁ {n = n} ac zy u f stp lf p ap fV q lV ll A₀ co Y (suc m) =
  (proj₁ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m) ⨾
     Cut₁ zy u (f (suc (m + n))) (stp (m + n)) (⊲ᴮ-tr ap (tailᴮ f stp p m)) (lf (suc (m + n))) (fV (suc (m + n))) q (proj₁ lV)) ,
  (proj₂ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m) ⊕⟨ lV ⟩
     Walk₁ ac zy u (f (suc (m + n))) (stp (m + n)) (⊲ᴮ-tr ap (tailᴮ f stp p m)) (lf (suc (m + n))) (fV (suc (m + n))) q lV ll A₀
       (proj₁ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m)) (proj₂ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m)))
```

**新种类的闭包** (`RunM`, `RKμ`, `RKμk`, `Kp₁`, `Kb₁` 原样, 只把格经 `toCl` 取出).

```agda
RunM ac zy u q₀ lW ll A₀ w Y = df (λ {t} T → RKμ ac zy u q₀ lW ll A₀ w Y t T)

RKμ ac zy u q₀ lW ll A₀ w Y hz T =
  nl (λ n → drp (yc (κΔ₁ ac zy u q₀ lW ll A₀ (toCl lW (κc₁ ac zy u q₀ lW ll A₀ w Y n)))
                    (τ₀ (proj₁ lW , lv₁ (toCl lW (κc₁ ac zy u q₀ lW ll A₀ w Y n))))))
RKμ ac zy u q₀ lW ll A₀ w Y (hs hz) T =
  nl (λ n → nw (proj₁ (wm T) , hself)
              (drp₁ (proj₁ lW , lv₁ (toCl lW (κc₁ ac zy u q₀ lW ll A₀ w Y n)))
                 (yc (κΔ₁ ac zy u q₀ lW ll A₀ (toCl lW (κc₁ ac zy u q₀ lW ll A₀ w Y n)))
                     (τ₁ (proj₁ lW , lv₁ (toCl lW (κc₁ ac zy u q₀ lW ll A₀ w Y n)))))))
RKμ ac zy u q₀ lW ll A₀ w Y (hs (hs b)) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hs (hl f)) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hs (hΩ κ g)) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hl f) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hΩ κ g) T = RKμk ac zy u q₀ ll A₀ w Y T tt

RKμk ac zy u q₀ ll A₀ w Y T zz₁ =
  yc (Kp₁ ac zy u q₀ ll A₀ w Y (wm T) (lm T)) (tg ≤rf (tm T) (lm T)) ⨾
  nμ zz₁ (λ {W′} q lW′ → yc (Kb₁ ac zy u q₀ ll A₀ w Y (wm T) (lm T) q lW′) (tg ≤rf (⊲ᴮ↑ q (tm T)) lW′))

Kp₁ {W⁺ = W⁺} ac zy u q₀ ll A₀ w Y wu lW⁺ =
  Walk₁ ac zy u (proj₂ W⁺) (proj₂ (≤tr q₀ wu)) hself (proj₂ lW⁺) hself (proj₁ (≤tr q₀ wu)) lW⁺ (⊲ᴮ↑ wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu Y)

Kb₁ {W⁺ = W⁺} {W′} ac zy u q₀ ll A₀ w Y wu lW⁺ q lW′ =
  Run ac (u (≤tr (≤tr q₀ wu) q) lW′) ≤rf lW′ (⊲ᴮ↑ (≤tr wu q) ll) (Ig↾ (≤tr wu q) A₀)
    (nw q (nw wu w ⨾ Cut₁ zy u (proj₂ W⁺) (proj₂ (≤tr q₀ wu)) hself (proj₂ lW⁺) hself (proj₁ (≤tr q₀ wu)) (proj₁ lW⁺)) ⨾
       Cut₁ zy u (proj₂ W′) (proj₂ q) (⊲ᴮ↑ {S₀} (proj₁ q) (proj₂ (≤tr q₀ wu))) (proj₂ lW′) hself (proj₁ (≤tr (≤tr q₀ wu) q)) (proj₁ lW′))
    (cv q (cv wu Y ⊕⟨ lW⁺ ⟩ Kp₁ ac zy u q₀ ll A₀ w Y wu lW⁺) ⊕⟨ lW′ ⟩
       Walk₁ ac zy u (proj₂ W′) (proj₂ q) (⊲ᴮ↑ {S₀} (proj₁ q) (proj₂ (≤tr q₀ wu))) (proj₂ lW′) hself (proj₁ (≤tr (≤tr q₀ wu) q)) lW′
         (⊲ᴮ↑ (≤tr wu q) ll) (Ig↾ (≤tr wu q) A₀)
         (nw q (nw wu w ⨾ Cut₁ zy u (proj₂ W⁺) (proj₂ (≤tr q₀ wu)) hself (proj₂ lW⁺) hself (proj₁ (≤tr q₀ wu)) (proj₁ lW⁺)))
         (cv q (cv wu Y ⊕⟨ lW⁺ ⟩ Kp₁ ac zy u q₀ ll A₀ w Y wu lW⁺)))

```

**链从底起** (这一篇唯一的新子句). 第 0 格: $x_0=\mathrm{sd}(z_1)$, 由模块参数 `sd` 给出, 只看状态里第 1 层的输出 $z_1$; 两个实例 (`ChainZClosed`): `sd = hz` (审查 D2 的原文 $x_0=\mathrm{bot}$) 与 `sd = rd(hz, z₁)` (种子取输出, 不取界). 界是 $\beta\boxplus x_0$. 第 $n+1$ 格: $x_{n+1}=\mathrm{rd}(x_n,\Delta_n)$, 界 $\beta\boxplus x_{n+1}$; 相邻格的第一位置是 `⊞-⊲ β (rd-fst …)`. 链的值从不引用 $\beta$; $\beta$ 只经世界操作 "接上" 出现.

```agda
κc₁ {W₀ = W₀} {W} ac zy u q₀ lW ll A₀ w Y zero =
  mkZ (sd lW (z₁ Y)) (lsd lW (z₁ Y)) (proj₂ W₀) hself (⊲ᴮ-tr (proj₂ q₀) (⊞-fst (proj₂ W) (sd lW (z₁ Y))))
    (cv (C.self , ⊞-fst (proj₂ W) (sd lW (z₁ Y))) Y) (nw (C.self , ⊞-fst (proj₂ W) (sd lW (z₁ Y))) w)
κc₁ {W₀ = W₀} {W} ac zy u q₀ lW ll A₀ w Y (suc n) =
  mkZ x′ lx′ (v₁ c₀) (⊲ᴮ-tr (ap₁ c₀) (av₁ c₀)) stp
    (cv (C.self , stp) (Sv₁ c₀ ⊕⟨ (proj₁ lW , lv₁ c₀) ⟩ κΔ₁ ac zy u q₀ lW ll A₀ c₀))
    (nw (C.self , stp) (co₁ c₀ ⨾ Cut₁ zy u (v₁ c₀) (av₁ c₀) (ap₁ c₀) (lv₁ c₀) hself (proj₁ q₀) (proj₁ lW)))
  where
  z₀ : ClZ W W₀ _
  z₀ = κc₁ ac zy u q₀ lW ll A₀ w Y n
  c₀ : Cl₁ W W₀ _
  c₀ = toCl lW z₀
  Δ₁ : D₁ (proj₁ W , v₁ c₀)
  Δ₁ = yc (κΔ₁ ac zy u q₀ lW ll A₀ c₀) (τ₁ (proj₁ lW , lv₁ c₀))
  x′ : H₀
  x′ = rd (proj₁ lW , lv₁ c₀) (xz z₀) Δ₁
  lx′ : LgB x′
  lx′ = Lg-rd (proj₁ lW , lv₁ c₀) (xz z₀) Δ₁ (lxz z₀)
  stp : v₁ c₀ ⊲[ proj₁ W ] proj₂ W ⊞ x′
  stp = ⊞-⊲ (proj₂ W) (rd-fst (proj₁ lW , lv₁ c₀) (xz z₀) Δ₁)

κΔ₁ ac zy u q₀ lW ll A₀ c =
  Walk₁ ac zy u (v₁ c) (av₁ c) (ap₁ c) (lv₁ c) hself (proj₁ q₀) (proj₁ lW , lv₁ c) (⊲ᴮ↑ (C.self , wv₁ c) ll) (Ig↾ (C.self , wv₁ c) A₀) (co₁ c) (Sv₁ c)
```
