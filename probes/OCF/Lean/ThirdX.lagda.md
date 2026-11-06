# Third (六): 跨底折叠, 把上抬的路径带下来

> 不含记号. 入口 [Third](Third.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 对任一底 $U$, 固定的合法世界 $w$, 洗法, 合法化, 代表坐标.
>
> **`ΦX t B …`**: 把 `XSof U` 的高度折到 $U$ 上的第 $t$ 层; 世界的界 $B$ (第 $U$ 层的合法值, $t\lhd_w B$) 是一切比较的字面公共上界. 三种结点:
>
> - **指标种类** $\iota$ (坐标是 $U$ 的值, 读 $\Omega_{x+1}$): 当作第 $0$ 层的新种类, 用 `pickG` 与 $t$ 比较 (RecB 的 $n=0$ 情形, 这里对一切底一条, 没有 "$n\ge1$ 时一律留"). 分支先回灌 $B\boxplus\mathrm{leg}\,c$, 进入后界换成 (回灌后的坐标)$+1$.
> - **指标分量的旧种类** (地板里坐标的 $\Omega$-结点): 不留, 在代表坐标 `pk κ` 处取分支. 地板带路径时这一步在固定世界里是第一位置 (`Bd` 证据 `pk-bd`).
> - **第 $c$ 个分量的种类**: 底种类留; 新种类以 $B$ 为公共上界比较.
>
> `PH-ΦX↓`: 输入带上抬的路径 `lift Q` (指标分量平凡), 输出带 `PSL Q t` (对一切 `Q`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdPS
open import OCF.Lean.ThirdTw using (XSof; Ix; FX; ιK)
import OCF.Lean.ThirdFold as TF
module OCF.Lean.ThirdX (U : KS) (w : Wd U) (lw : LgW U w) (Sn : TF.San U w lw)
  (leg : HB U → HB U) (Lg-leg : ∀ a → LgB (leg a))
  (pk : (κ : K U) → E U κ) (pk-bd : ∀ κ → Bd U κ (pk κ) w) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.ThirdIf
open import OCF.Lean.ThirdTw using (emb; frE; posE)
open TF U w lw
open F Sn
open San Sn

X = XSof U
⊲tr : ∀ {a b c} → a ⊲ᵘ b → b ⊲ᵘ c → a ⊲ᵘ c
⊲tr = ⊲ᴮ-tr {U}
```

## §1 自己的路径

```agda
PoU : Po
PoU = record { W = HB U ; _≤_ = _⊲ᵘ_ ; rf = hself ; tr = ⊲tr }

sh₀ : HB U → HB U → HB U
sh₀ B c = B ⊞ leg c

Adm₀ : HB U → HB U → Set
Adm₀ B e = (B ⊲ᵘ e) × LgB e

EvX : HB U → K X → Set
EvX B (inj₁ _ , inj₂ _) = hs hz ⊲ᵘ B
EvX B (inj₁ _ , inj₁ κ) = ⊤
EvX B (inj₂ c , κ) = (hs c ⊲ᵘ B) × Pos U w (hs c) κ

AdX : HB U → (κ : K X) → E X κ → Set
AdX B (inj₁ _ , inj₂ _) e = Adm₀ B e
AdX B (inj₁ _ , inj₁ κ) e = Bd U κ e w
AdX B (inj₂ c , κ) e = AdT (hs c) κ e

nxX : (B : HB U) (κ : K X) (e : E X κ) → AdX B κ e → HB U
nxX B (inj₁ _ , inj₂ _) e a = hs e
nxX B (inj₁ _ , inj₁ κ) e a = B
nxX B (inj₂ c , κ) e a = B

PSX : PS PoU X
PSX = record { Ev = EvX ; Ad = AdX ; nx = nxX ; ev↑ = ev↑′ ; ad↓ = ad↓′ ; nx↑ = nx↑′ }
  where
  ev↑′ : ∀ {B B′} → B ⊲ᵘ B′ → ∀ {κ} → EvX B κ → EvX B′ κ
  ev↑′ q {inj₁ _ , inj₂ _} ev = ⊲tr ev q
  ev↑′ q {inj₁ _ , inj₁ κ} ev = tt
  ev↑′ q {inj₂ c , κ} (p , o) = ⊲tr p q , o
  ad↓′ : ∀ {B B′} → B ⊲ᵘ B′ → ∀ {κ e} (a′ : AdX B′ κ e) → Σ (AdX B κ e) (λ a → nxX B κ e a ⊲ᵘ nxX B′ κ e a′)
  ad↓′ q {inj₁ _ , inj₂ _} (p , l) = (⊲tr q p , l) , hself
  ad↓′ q {inj₁ _ , inj₁ κ} a = a , q
  ad↓′ q {inj₂ c , κ} a = a , q
  nx↑′ : ∀ {B κ e} (a : AdX B κ e) → B ⊲ᵘ nxX B κ e a
  nx↑′ {κ = inj₁ _ , inj₂ _} (p , l) = hsuc p
  nx↑′ {κ = inj₁ _ , inj₁ κ} a = hself
  nx↑′ {κ = inj₂ c , κ} a = hself
```

## §2 决定与折叠

```agda
⊤̂ : HB U → Set
⊤̂ _ = ⊤

-- 指标种类的决定: 第 0 层的新种类, 公共上界 B
dcI : ∀ {B t} → LgB B → t ⊲ᵘ B → hs hz ⊲ᵘ B → Dg B t (HB U) ⊤̂
dcI lB pt o = pickG {i = hz} (λ c → c) (λ c _ → tt) o (cmpB {U} o pt lw lB)

-- 第 c 个分量的种类的决定
dcx : ∀ {B t c κ} → LgB B → t ⊲ᵘ B → hs c ⊲ᵘ B → Cg (hs c) κ → Dg B t (E (T (hs c)) κ) (AdT (hs c) κ)
dcx {t = t} lB pt ev (bas κ₀ to ad) = keep (emb t κ₀) (posE t κ₀) (λ c′ → to (frE t κ₀ c′)) (λ c′ → ad (frE t κ₀ c′))
dcx lB pt ev (nw j pj to ad) = pickG to ad (⊲tr pj ev) (cmpB {U} (⊲tr pj ev) pt lw lB)

aS : ∀ {B} e → LgB B → Adm₀ B (sh₀ B e)
aS {B} e lB = ⊞-fst {U} B (leg e) , Lg-⊞ B (leg e) lB (Lg-leg e)

↑S : ∀ {B} e → B ⊲ᵘ hs (sh₀ B e)
↑S {B} e = hsuc (⊞-fst {U} B (leg e))

ΦX : ∀ t B → LgB B → t ⊲ᵘ B → GT t → (h : HB X) → PH PSX B h → GT t
ΦX t B lB pt b hz nd = hs hz , tt
ΦX t B lB pt b (hs h) nd = limG (mulG (ΦX t B lB pt b h nd))
ΦX t B lB pt b (hl f) nd = limG (ΣG (λ k → ΦX t B lB pt b (f k) (nd k)))
ΦX t B lB pt b (hΩ (inj₁ _ , inj₂ _) g) (o , pg) = nodeG (dcI lB pt o) pt b
  (λ t′ pt′ b′ c _ → ΦX t′ (hs (sh₀ B c)) (proj₂ (aS c lB)) (⊲tr pt′ (↑S c)) b′ (g (sh₀ B c)) (pg _ (aS c lB)))
  (λ i u q x → Φ i (wfC i) (lg↓ u lB) t q b (proj₁ x) (proj₂ x))
ΦX t B lB pt b (hΩ (inj₁ _ , inj₁ κ) g) (_ , pg) = ΦX t B lB pt b (g (pk κ)) (pg _ (pk-bd κ))
ΦX t B lB pt b (hΩ (inj₂ c , κ) g) ((ev , pos) , pg) = nodeG (dcx lB pt ev (cg (hs c) κ pos)) pt b
  (λ t′ pt′ b′ e pe → ΦX t′ B lB pt′ b′ (g e) (pg e pe))
  (λ i u q x → Φ i (wfC i) (lg↓ u lB) t q b (proj₁ x) (proj₂ x))

Sh-ΦX : ∀ t B lB pt b h nd → ShG (ΦX t B lB pt b h nd)
Sh-ΦX t B lB pt b hz nd = tt
Sh-ΦX t B lB pt b (hs h) nd = Sh-mul _ (Sh-ΦX t B lB pt b h nd)
Sh-ΦX t B lB pt b (hl f) nd = Sh-Σ _ (λ k → Sh-ΦX t B lB pt b (f k) (nd k))
Sh-ΦX t B lB pt b (hΩ (inj₁ _ , inj₂ _) g) (o , pg) = Sh-node (dcI lB pt o) pt b _ _
  (λ t′ pt′ b′ c _ → Sh-ΦX t′ (hs (sh₀ B c)) (proj₂ (aS c lB)) (⊲tr pt′ (↑S c)) b′ (g (sh₀ B c)) (pg _ (aS c lB)))
  (λ i u q x → Sh-Φ i (wfC i) (lg↓ u lB) t q b (proj₁ x) (proj₂ x))
Sh-ΦX t B lB pt b (hΩ (inj₁ _ , inj₁ κ) g) (_ , pg) = Sh-ΦX t B lB pt b (g (pk κ)) (pg _ (pk-bd κ))
Sh-ΦX t B lB pt b (hΩ (inj₂ c , κ) g) ((ev , pos) , pg) = Sh-node (dcx lB pt ev (cg (hs c) κ pos)) pt b _ _
  (λ t′ pt′ b′ e pe → Sh-ΦX t′ B lB pt′ b′ (g e) (pg e pe))
  (λ i u q x → Sh-Φ i (wfC i) (lg↓ u lB) t q b (proj₁ x) (proj₂ x))
```

## §3 定理: 跨底折叠把上抬的路径带下来 (对一切 `Q`)

```agda
module Down {P : Po} (Q : PS P U) (O : Po.W P → Set) (o↑ : ∀ {a b} → Po._≤_ P a b → O a → O b)
  (ph-san : ∀ j {V} c → PH (PSL Q j) V c → PH (PSL Q j) V (san j c))
  (ph-tp : ∀ j V → O V → PH (PSL Q j) V (tp j)) where
  open Po P
  open import OCF.Lean.ThirdPath U w lw Sn Q O o↑
  open Node ph-san ph-tp
  LQ = lift Q

  PH-ΦX↓ : ∀ t B lB pt b h nd V → O V → PH (L t) V (proj₁ b) → PH LQ V h →
           PH (L t) V (proj₁ (ΦX t B lB pt b h nd))
  PH-ΦX↓ t B lB pt b hz nd V o pb ph = tt
  PH-ΦX↓ t B lB pt b (hs h) nd V o pb ph = PH-mulG (ΦX t B lB pt b h nd) (PH-ΦX↓ t B lB pt b h nd V o pb ph)
  PH-ΦX↓ t B lB pt b (hl f) nd V o pb ph =
    PH-ΣG (λ k → ΦX t B lB pt b (f k) (nd k)) (λ k → PH-ΦX↓ t B lB pt b (f k) (nd k) V o pb (ph k))
  PH-ΦX↓ t B lB pt b (hΩ (inj₁ _ , inj₂ _) g) (oB , pg) V o pb (_ , pgL) =
    PH-node {R = ⊤̂} (λ V′ c → PH LQ V′ (g (sh₀ B c))) (dcI lB pt oB) pt b _ _ V o pb
      (okP {X = B} {t = t} {i = hz} {R = ⊤̂} (λ V′ c → PH LQ V′ (g (sh₀ B c))) (λ le p → PH-mono LQ le _ p) V
        (λ c → c) (λ c _ → tt) oB (λ c V′ le _ → PH-mono LQ le _ (pgL _ tt)) (cmpB {U} oB pt lw lB))
      (λ t′ pt′ b′ c _ V′ oV pb′ pin → PH-ΦX↓ t′ (hs (sh₀ B c)) (proj₂ (aS c lB)) (⊲tr pt′ (↑S c)) b′ (g (sh₀ B c)) (pg _ (aS c lB)) V′ oV pb′ pin)
      (λ i u q x V′ oV px pb′ → PH-Φ i (wfC i) (lg↓ u lB) t q b (proj₁ x) (proj₂ x) V′ oV pb′ px)
  PH-ΦX↓ t B lB pt b (hΩ (inj₁ _ , inj₁ κ) g) (_ , pg) V o pb (_ , pgL) =
    PH-ΦX↓ t B lB pt b (g (pk κ)) (pg _ (pk-bd κ)) V o pb (pgL _ tt)
  PH-ΦX↓ t B lB pt b (hΩ (inj₂ c , κ) g) ((ev , pos) , pg) V o pb (evL , pgL) =
    PH-node {R = AdT (hs c) κ} Pm′ (dcx lB pt ev (cg (hs c) κ pos)) pt b _ _ V o pb
      (okX (cg (hs c) κ pos) (clP (hs c) κ pos))
      (λ t′ pt′ b′ e pe V′ oV pb′ pin → PH-ΦX↓ t′ B lB pt′ b′ (g e) (pg e pe) V′ oV pb′ pin)
      (λ i u q x V′ oV px pb′ → PH-Φ i (wfC i) (lg↓ u lB) t q b (proj₁ x) (proj₂ x) V′ oV pb′ px)
    where
    Pm′ : W → E (T (hs c)) κ → Set
    Pm′ V′ e = PH LQ V′ (g e)
    okX : (cc : Cg (hs c) κ) → ClP (hs c) κ cc → Ok Pm′ V (dcx lB pt ev cc)
    okX (bas κ₀ to ad) (evd , pk′) =
      okB {X = B} {t = t} {R = AdT (hs c) κ} Pm′ (λ le p → PH-mono LQ le _ p) V κ₀ to ad (evd evL) (λ e a →
        PH-mono LQ (proj₂ (pk′ e a)) _ (pgL (to e) (proj₁ (pk′ e a))))
    okX (nw j pj to ad) pk′ =
      okP {X = B} {t = t} {R = AdT (hs c) κ} Pm′ (λ le p → PH-mono LQ le _ p) V to ad (⊲tr pj ev)
        (λ c′ V′ le p → PH-mono LQ (proj₂ (pk′ c′ V′ le p)) _ (pgL (to c′) (proj₁ (pk′ c′ V′ le p))))
        (cmpB {U} (⊲tr pj ev) pt lw lB)
```
