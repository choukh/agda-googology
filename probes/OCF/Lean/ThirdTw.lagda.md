# Third (一): 高度是值的塔: 分类, 嵌入, 决定; 底对 $n$ 递归, 地板

> 不含记号. 入口 [Third](Third.lagda.md), 接口 [ThirdIf](ThirdIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只导入 stdlib, [CRwBase](CRwBase.lagda.md), [ThirdIf](ThirdIf.lagda.md).
>
> **与 RecB 的差.** RecB 的塔高度是可数树, 种类的位置与世界无关. 这里高度 $m$ 是 `HB U` 的值, 塔 `Tw U m` 穿过 $\Omega$-结点时分量由坐标编号, 所以**分类要世界**: `cl` 从 `Pos` 读出 (留底种类 / 第 $j$ 层的新种类, 位置 $j+1\lhd_w m$); `along` 沿 $w$ 里的字面第一位置走到第 $i$ 层的新种类. 决定 `dcl` 用 `cmpB`, 公共上界是 $m$ (世界 $w$ 里).
>
> **底.** `Sb 0 = S⊥`, `Sb (n+1)` 的分量: 指标分量 `step (Sb n)` 与第 $c$ 个分量 `Tw (Sb n) (hs c)`, $c$ 是第 $n$ 个底的**值**. $n=0$ 时 $c$ 是可数树, 形状同 RecB 的第 1 个底.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdTw where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf
```

## §1 分类

```agda
module _ {U : KS} {w : Wd U} where
  data Cl (m : HB U) (κ : K (Tw U m)) : Set where
    bas : (κ₀ : K U) → (E U κ₀ → E (Tw U m) κ) → Cl m κ
    nw  : (j : HB U) → hs j ⊲[ w ] m → (HB (Tw U j) → E (Tw U m) κ) → Cl m κ

  cS : ∀ {x κ} → Cl x κ → Cl (hs x) (inj₁ κ)
  cS (bas κ₀ to) = bas κ₀ to
  cS (nw j p to) = nw j (hsuc p) to

  cL : ∀ {f} n {κ} → Cl (f n) κ → Cl (hl f) (n , κ)
  cL n (bas κ₀ to) = bas κ₀ to
  cL n (nw j p to) = nw j (hlim n p) to

  cO : ∀ {κ₀ g} e {κ} → Bd U κ₀ e w → Cl (g e) κ → Cl (hΩ κ₀ g) (e , κ)
  cO e b (bas κ₁ to) = bas κ₁ to
  cO e b (nw j p to) = nw j (hLim b p) to

  cl : ∀ m κ → Pos U w m κ → Cl m κ
  cl hz κ _ = bas κ (λ e → e)
  cl (hs x) (inj₁ κ) p = cS (cl x κ p)
  cl (hs x) (inj₂ _) _ = nw x hself (λ c → c)
  cl (hl f) (n , κ) p = cL n (cl (f n) κ p)
  cl (hΩ κ₀ g) (e , κ) (b , p) = cO e b (cl (g e) κ p)
```

## §2 留下的种类: 底种类的嵌入, 沿第一位置的新种类

底种类嵌进塔时穿过 $\Omega$-结点走 `bot` 分量, 证据是 `botBd` (与世界无关). `along q`: 沿字面第一位置 $q : i+1\lhd_w t$ 走到第 $i$ 层的新种类, 坐标字面是第 $i$ 层的值.

```agda
module _ {U : KS} where
  emb : ∀ t → K U → K (Tw U t)
  emb hz κ = κ
  emb (hs x) κ = inj₁ (emb x κ)
  emb (hl f) κ = 0 , emb (f 0) κ
  emb (hΩ κ₀ g) κ = bot U κ₀ , emb (g (bot U κ₀)) κ

  frE : ∀ t κ → E (Tw U t) (emb t κ) → E U κ
  frE hz κ c = c
  frE (hs x) κ c = frE x κ c
  frE (hl f) κ c = frE (f 0) κ c
  frE (hΩ κ₀ g) κ c = frE (g (bot U κ₀)) κ c

  posE : ∀ {w} t κ → Pos U w t (emb t κ)
  posE hz κ = tt
  posE (hs x) κ = posE x κ
  posE (hl f) κ = posE (f 0) κ
  posE {w} (hΩ κ₀ g) κ = botBd U κ₀ w , posE (g (bot U κ₀)) κ

  along : ∀ {w i t} → hs i ⊲[ w ] t → K (Tw U t)
  along hself = inj₂ tt
  along (hsuc q) = inj₁ (along q)
  along (hlim n q) = n , along q
  along (hLim {c = e} _ q) = e , along q

  frA : ∀ {w i t} (q : hs i ⊲[ w ] t) → E (Tw U t) (along q) → HB (Tw U i)
  frA hself c = c
  frA (hsuc q) c = frA q c
  frA (hlim n q) c = frA q c
  frA (hLim _ q) c = frA q c

  posA : ∀ {w i t} (q : hs i ⊲[ w ] t) → Pos U w t (along q)
  posA hself = tt
  posA (hsuc q) = posA q
  posA (hlim n q) = posA q
  posA (hLim b q) = b , posA q
```

## §3 决定

与 `CRwFold.Dc` 同形, 世界 $w$ 是参数: 公共上界 $X$ 是世界 $w$ 里的合法值.

```agda
module _ {U : KS} {w : Wd U} where
  data Dc (X t : HB U) (A : Set) : Set where
    keep  : (κ′ : K (Tw U t)) → Pos U w t κ′ → (E (Tw U t) κ′ → A) → Dc X t A
    same  : (HB (Tw U t) → A) → Dc X t A
    above : (i : HB U) → hs i ⊲[ w ] X → t ⊲[ w ] i → (HB (Tw U i) → A) → Dc X t A

  pick : ∀ {X t i A} → (HB (Tw U i) → A) → hs i ⊲[ w ] X → (t ⊲[ w ] hs i) ⊎ (hs i ⊲[ w ] t) → Dc X t A
  pick to u (inj₂ q) = keep (along q) (posA q) (λ c → to (frA q c))
  pick to u (inj₁ hself) = keep (inj₂ tt) tt to
  pick to u (inj₁ (hsuc q)) = above-or-same to u q
    where
    above-or-same : ∀ {X t i A} → (HB (Tw U i) → A) → hs i ⊲[ w ] X → t ⊲[ w ] i → Dc X t A
    above-or-same to u hself = same to
    above-or-same to u q@(hsuc _) = above _ u q to
    above-or-same to u q@(hlim _ _) = above _ u q to
    above-or-same to u q@(hLim _ _) = above _ u q to

  dcl : ∀ {m t κ} → t ⊲[ w ] m → LgW U w → LgB m → Cl {U} {w} m κ → Dc m t (E (Tw U m) κ)
  dcl {t = t} pt lw lm (bas κ₀ to) = keep (emb t κ₀) (posE t κ₀) (λ c → to (frE t κ₀ c))
  dcl pt lw lm (nw j pj to) = pick to pj (cmpB pj pt lw lm)
```

## §4 底对 $n$ 递归, 塔的地板, 底的地板

`topT U fb m`: 第 $m$ 层的地板. 穿过高度的 $\Omega$-结点时取**逐坐标**的第 $e$ 个分量的地板: 结点的种类是底种类 $\kappa$ 的 `bot` 拷贝, 分支 $e\mapsto\iota_e$ (第 $g\,e$ 层的地板). 这里不累加 (累加要对坐标递归, 一般的 `E U κ` 没有结构); 中间层合法性不要它 (形状证书只读第 $0$ 层).

```agda
topT : ∀ U → HB U → ∀ m → HB (Tw U m)
ΣT : ∀ U → HB U → (f : ℕ → HB U) → ℕ → HB (Tw U (hl f))
topT U b hz = b
topT U b (hs x) = hΩ (inj₂ tt) up
topT U b (hl f) = hl (ΣT U b f)
topT U b (hΩ κ g) = hΩ (bot U κ , emb (g (bot U κ)) κ)
  (λ c → ι {E U κ} {λ e → Tw U (g e)} (frE (g (bot U κ)) κ c) (topT U b (g (frE (g (bot U κ)) κ c))))
ΣT U b f zero = ι 0 (topT U b (f 0))
ΣT U b f (suc n) = ΣT U b f n ⊞ ι (suc n) (topT U b (f (suc n)))

Ix : KS → Set
Ix U = ⊤ ⊎ HB U

FX : (U : KS) → Ix U → KS
FX U (inj₁ _) = step U
FX U (inj₂ c) = Tw U (hs c)

XSof : KS → KS
XSof U = sup (Ix U) (FX U)

Sb : ℕ → KS
Sb zero = S⊥
Sb (suc n) = XSof (Sb n)

-- 这一层的指标种类
ιK : ∀ {U} → K (XSof U)
ιK = inj₁ tt , inj₂ tt

gtX : ∀ U (fb : HB U) → HB U → HB (XSof U)
gtX U fb hz = hz
gtX U fb (hs c) = gtX U fb c ⊞ ι {Ix U} {FX U} (inj₂ c) (topT U fb (hs c))
gtX U fb (hl f) = hl (λ k → gtX U fb (f k))
gtX U fb (hΩ κ h) = hΩ (inj₁ tt , inj₁ κ) (λ e → gtX U fb (h e))

fl : ∀ n → HB (Sb n)
fl zero = hz
fl (suc n) = hΩ ιK (gtX (Sb n) (fl n))

-- Λ 层: 底的并, 地板取部分和
SΛ : KS
SΛ = sup ℕ Sb

ΣΛ : ℕ → HB SΛ
ΣΛ zero = ι {ℕ} {Sb} 0 (fl 0)
ΣΛ (suc n) = ΣΛ n ⊞ ι {ℕ} {Sb} (suc n) (fl (suc n))

flΛ : HB SΛ
flΛ = hl ΣΛ
```
