# CRw (二): 层号, 种类, 一份折叠

> 不含记号. 入口 [CRw](CRw.lagda.md), 接口 [CRwIf](CRwIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 对任一满足接口的 `I` 一条定义.
>
> **重写, 不是拷贝删减.** 参考 `TySupFold` (`Φ`), `PathOutFold` (`Ψ`), `X1UpFold` (`ΦU`) 与 `TySupC`, `PathOutX1` (只作参考). 原来是三个折叠, 各有自己的层号类型与决定; 这里是**一个**折叠 `Φ`, 对层号递归:
>
> - **层号** 是一对 (底, 高度): 底 `b⊥` (空结构 `S⊥`) 或 `bX` ($\Omega_1$ 这一层的种类结构 `XS`), 高度 $m$ 是可数树. 第 $(s, m)$ 层的种类结构是底上的塔 `Tw (bS s) m` (后继给 `step`, ℕ-极限给 `sup ℕ`). `(b⊥, c)` 是可数层号 $c$, `(bX, hz)` 是 $\Omega_1$ (PathOut 的 $X_1$), `(bX, m)` 是 $\Omega_1\oplus m$ (X1Up 的叠层). 塔、种类分类、嵌入、`along` 对两种底**一份定义**.
> - **目标** `Tg`: 同底 (`sm`, $t\lhd m$, 公共上界是 $m$), 或从 $\Omega_1$ 到可数层号 (`cx`, 带世界的界 $B$, $t\lhd B$).
> - **决定.** 同底: 底种类一律留 (嵌入), 塔的新种类 (第 $j$ 层) 用 `cmpB` 比较 $j+1$ 与 $t$, 公共上界 $m$ (`dcl`). 跨底: `XS` 的种类 $(c,\kappa)$ 带证据 $c+1\lhd B$, 它的层号与 $t$ 用 `cmpB` 比较, 公共上界 $B$ (`dcx`). 两者共用一个 `pick` (留 / 同层 / 在上).
> - **世界移动** 只在跨底时发生: 进入种类 $(c,\kappa)$ 的分支时坐标先回灌, 世界换新 (按种类的策略 `pX`: $\Omega_1$ 种类用接口的 `Adm₀`/`nxt₀`/`sh₀`, 其余种类不动世界).
> - **带路径** `PH` 只在跨底时要求 (`Nd`). 同底的折叠不要路径.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.CRwIf
module OCF.Lean.CRwFold (I : CRwIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Lean.CRwBase
open CRwIf I
```

## §1 塔与层号

```agda
Tw : KS → Cd → KS
Tw S hz = S
Tw S (hs x) = step (Tw S x)
Tw S (hl f) = sup ℕ (λ n → Tw S (f n))
Tw S (hΩ () _)

-- Ω₁ 这一层: 坐标 c 处是第 c+1 层的种类
XS : KS
XS = sup Cd (λ c → Tw S⊥ (hs c))

data Bs : Set where
  b⊥ bX : Bs

bS : Bs → KS
bS b⊥ = S⊥
bS bX = XS

Lev : Bs → Cd → KS
Lev s m = Tw (bS s) m
```

## §2 种类: 分类, 嵌入, `along` (对一切底一份)

塔的种类分两类: 底种类 (来自 `S`) 与新种类 (第 $j$ 层的 $\Omega$, 位置 $j+1\lhd m$).

```agda
module _ {S : KS} where
  data Cl (m : Cd) (κ : K (Tw S m)) : Set where
    bas : (κ₀ : K S) → (E S κ₀ → E (Tw S m) κ) → Cl m κ
    nw  : (j : Cd) → hs j ⊲ m → (HB (Tw S j) → E (Tw S m) κ) → Cl m κ

  cS : ∀ {x κ} → Cl x κ → Cl (hs x) (inj₁ κ)
  cS (bas κ₀ to) = bas κ₀ to
  cS (nw j p to) = nw j (hsuc p) to

  cL : ∀ {f} n {κ} → Cl (f n) κ → Cl (hl f) (n , κ)
  cL n (bas κ₀ to) = bas κ₀ to
  cL n (nw j p to) = nw j (hlim n p) to

  cl : ∀ m κ → Cl m κ
  cl hz κ = bas κ (λ e → e)
  cl (hs x) (inj₁ κ) = cS (cl x κ)
  cl (hs x) (inj₂ _) = nw x hself (λ c → c)
  cl (hl f) (n , κ) = cL n (cl (f n) κ)
  cl (hΩ () _) _

  emb : ∀ t → K S → K (Tw S t)
  emb hz κ = κ
  emb (hs x) κ = inj₁ (emb x κ)
  emb (hl f) κ = 0 , emb (f 0) κ
  emb (hΩ () _) _

  frE : ∀ t κ → E (Tw S t) (emb t κ) → E S κ
  frE hz κ c = c
  frE (hs x) κ c = frE x κ c
  frE (hl f) κ c = frE (f 0) κ c
  frE (hΩ () _) _ _

  along : ∀ {i t} → hs i ⊲ t → K (Tw S t)
  along hself = inj₂ tt
  along (hsuc q) = inj₁ (along q)
  along (hlim n q) = n , along q
  along (hLim {κ = ()} _ _)

  frA : ∀ {i t} (q : hs i ⊲ t) → E (Tw S t) (along q) → HB (Tw S i)
  frA hself c = c
  frA (hsuc q) c = frA q c
  frA (hlim n q) c = frA q c
  frA (hLim {κ = ()} _ _) _
```

## §3 决定

`Dc L X t A`: 坐标类型 $A$ 的种类对目标层 $t$ 留 (`keep`), 同层 (`same`), 或在上 (`above`, 先坍缩到第 $i$ 层, $i+1\lhd X$, $t\lhd i$). `pick`: 由 `cmpB` 的结果 ($j+1$ 与 $t$ 在公共上界 $X$ 之下) 读出三种之一.

```agda
data Dc (L : Cd → KS) (X t : Cd) (A : Set) : Set where
  keep  : (κ′ : K (L t)) → (E (L t) κ′ → A) → Dc L X t A
  same  : (HB (L t) → A) → Dc L X t A
  above : (i : Cd) → hs i ⊲ X → t ⊲ i → (HB (L i) → A) → Dc L X t A

caseDc : ∀ {L X t A} {R : Set} → Dc L X t A →
         ((κ′ : K (L t)) → (E (L t) κ′ → A) → R) → ((HB (L t) → A) → R) →
         ((i : Cd) → hs i ⊲ X → t ⊲ i → (HB (L i) → A) → R) → R
caseDc (keep κ′ fr) k s ab = k κ′ fr
caseDc (same to) k s ab = s to
caseDc (above i u q to) k s ab = ab i u q to

pick : ∀ S {X t i A} → (HB (Tw S i) → A) → hs i ⊲ X → (t ⊲ hs i) ⊎ (hs i ⊲ t) → Dc (Tw S) X t A
pick S to u (inj₂ q) = keep (along q) (λ c → to (frA q c))
pick S to u (inj₁ hself) = keep (inj₂ tt) to
pick S to u (inj₁ (hsuc hself)) = same to
pick S to u (inj₁ (hsuc q)) = above _ u q to

-- 同底: 底种类一律留, 新种类以 m 为公共上界比较
dcl : ∀ {S m t κ} → t ⊲ m → LgB m → Cl {S} m κ → Dc (Tw S) m t (E (Tw S m) κ)
dcl {t = t} pt lm (bas κ₀ to) = keep (emb t κ₀) (λ c → to (frE t κ₀ c))
dcl {S} pt lm (nw j pj to) = pick S to pj (cmpB pj pt tt lm)

-- 跨底: XS 的种类 (c , κ) 带 c+1 ⊲ B, 以世界的界 B 为公共上界比较
dcx : ∀ {B t c} {κ : K (Tw S⊥ (hs c))} → LgB B → t ⊲ B → hs c ⊲ B →
      Cl {S⊥} (hs c) κ → Dc (Tw S⊥) B t (E (Tw S⊥ (hs c)) κ)
dcx lB pt ev (bas () _)
dcx lB pt ev (nw j pj to) = pick S⊥ to (⊲ᴮ-tr pj ev) (cmpB (⊲ᴮ-tr pj ev) pt tt lB)
```

## §4 世界的策略与带路径

进入一个种类的分支: 可入 `pAd`, 新世界 `pnx`, 回灌 `psh`, 与接口同样的律. $\Omega_1$ 这一层的种类 $(c,\kappa)$ 里只有 $\Omega_1$ 本身 ($c=0$ 处的新种类, 坐标是可数树) 用接口; 其余 (包括各分量里 $\Omega_1$ 的拷贝) 不动世界 (`poF`, 同 PathOut 的 `Adm₁`). `pX`: 每个种类的策略.

```agda
record Po (A : Set) : Set₁ where
  field
    pAd   : Cd → A → Set
    pnx   : (B : Cd) (e : A) → pAd B e → Cd
    psh   : Cd → A → A
    pad-sh : ∀ {B} e → LgB B → pAd B (psh B e)
    pnx↑  : ∀ {B e} (a : pAd B e) → B ⊲ pnx B e a
    plg   : ∀ {B e} (a : pAd B e) → LgB B → LgB (pnx B e a)
    pad↓  : ∀ {B B′} → B ⊲ B′ → ∀ {e} (a′ : pAd B′ e) → Σ (pAd B e) (λ a → pnx B e a ⊲ pnx B′ e a′)
open Po

poΩ : Po Cd
poΩ = record { pAd = Adm₀ ; pnx = nxt₀ ; psh = sh₀ ; pad-sh = adm-sh ; pnx↑ = nx-up ; plg = lg-nx ; pad↓ = adm↓ }

poF : ∀ {A} → Po A
poF = record { pAd = λ _ _ → ⊤ ; pnx = λ B _ _ → B ; psh = λ _ e → e ; pad-sh = λ _ _ → tt
             ; pnx↑ = λ _ → hself ; plg = λ _ l → l ; pad↓ = λ q _ → tt , q }

-- XS 的种类 (c , κ): 只有 Ω₁ 这一种 (c = 0 处的新种类) 移动世界
pX : ∀ c (κ : K (Tw S⊥ (hs c))) → Po (E (Tw S⊥ (hs c)) κ)
pX c (inj₁ κ) = poF
pX hz (inj₂ _) = poΩ
pX (hs _) (inj₂ _) = poF
pX (hl _) (inj₂ _) = poF
pX (hΩ () _) (inj₂ _)
```

**带路径的结构** `PS T` (同 `X1UpIf.PS`, 不带证据参数的 `nxt`): 证据 `Ev`, 可入 `Ad`, 新世界 `nx`, 三条律. `PH Q B h`: $h$ 的每个结点的种类在世界 $B$ 里带证据, 每个可入的分支在新世界里递归地带路径. `PSX`: $\Omega_1$ 这一层, 种类 $(c,\kappa)$ 的证据是 $c+1\lhd B$.

```agda
record PS (T : KS) : Set₁ where
  field
    Ev  : Cd → K T → Set
    Ad  : Cd → (κ : K T) → E T κ → Set
    nx  : (B : Cd) (κ : K T) (e : E T κ) → Ad B κ e → Cd
    ev↑ : ∀ {B B′} → B ⊲ B′ → ∀ {κ} → Ev B κ → Ev B′ κ
    ad↓ : ∀ {B B′} → B ⊲ B′ → ∀ {κ e} (a′ : Ad B′ κ e) → Σ (Ad B κ e) (λ a → nx B κ e a ⊲ nx B′ κ e a′)
    nx↑ : ∀ {B κ e} (a : Ad B κ e) → B ⊲ nx B κ e a

module _ {T : KS} (Q : PS T) where
  open PS Q
  PH : Cd → HB T → Set
  PH B hz = ⊤
  PH B (hs h) = PH B h
  PH B (hl f) = ∀ n → PH B (f n)
  PH B (hΩ κ g) = Ev B κ × (∀ e (a : Ad B κ e) → PH (nx B κ e a) (g e))

PSX : PS XS
PSX = record
  { Ev = λ B κ → hs (proj₁ κ) ⊲ B
  ; Ad = λ B κ → pAd (pX (proj₁ κ) (proj₂ κ)) B
  ; nx = λ B κ → pnx (pX (proj₁ κ) (proj₂ κ)) B
  ; ev↑ = λ q ev → ⊲ᴮ-tr ev q
  ; ad↓ = λ q {κ} → pad↓ (pX (proj₁ κ) (proj₂ κ)) q
  ; nx↑ = λ {B} {κ} → pnx↑ (pX (proj₁ κ) (proj₂ κ)) }
```

## §5 地板

`topT S b m`: 第 $m$ 层的地板 (底上取 $b$, 后继取新种类的 $\Omega$, ℕ-极限取部分和). $\Omega_1$ 这一层的地板 `topL` 是 $\Omega_1$ 种类的结点, 分支 $g\,0=0$, $g\,(c+1)=g\,c\boxplus\iota_c\,\Omega_{c+1}$ (同 `PathOut.topL`).

```agda
topT : ∀ S → HB S → ∀ m → HB (Tw S m)
ΣT : ∀ S → HB S → (f : ℕ → Cd) → ℕ → HB (Tw S (hl f))
topT S b hz = b
topT S b (hs x) = hΩ (inj₂ tt) up
topT S b (hl f) = hl (ΣT S b f)
topT S b (hΩ () _)
ΣT S b f zero = ι 0 (topT S b (f 0))
ΣT S b f (suc n) = ΣT S b f n ⊞ ι (suc n) (topT S b (f (suc n)))

gt : Cd → HB XS
gt hz = hz
gt (hs c) = gt c ⊞ ι c (topT S⊥ hz (hs c))
gt (hl f) = hl (λ n → gt (f n))
gt (hΩ () _)

topL : HB XS
topL = hΩ (hz , inj₂ tt) gt

top : ∀ s m → HB (Lev s m)
top b⊥ = topT S⊥ hz
top bX = topT XS topL
```

## §6 折叠

可达性: 同底时 $i+1\lhd m$; 可数层号在 $\Omega_1$ 之下 (`lx`).

```agda
data Lt : Bs → Cd → Bs → Cd → Set where
  lt : ∀ {s i m} → hs i ⊲ m → Lt s i s m
  lx : ∀ {i m} → Lt b⊥ i bX m

data Acc (s : Bs) (m : Cd) : Set where
  acc : (∀ s′ i → Lt s′ i s m → Acc s′ i) → Acc s m

wf⊥ : ∀ m → Acc b⊥ m
g⊥ : ∀ m i → hs i ⊲ m → Acc b⊥ i
wf⊥ m = acc (λ { _ i (lt p) → g⊥ m i p })
g⊥ (hs x) .x hself = wf⊥ x
g⊥ (hs x) i (hsuc p) = g⊥ x i p
g⊥ (hl f) i (hlim n p) = g⊥ (f n) i p
g⊥ (hΩ () _) i _

wfX : ∀ m → Acc bX m
gX : ∀ m i → hs i ⊲ m → Acc bX i
wfX m = acc (λ { _ i (lt p) → gX m i p ; _ i lx → wf⊥ i })
gX (hs x) .x hself = wfX x
gX (hs x) i (hsuc p) = gX x i p
gX (hl f) i (hlim n p) = gX (f n) i p
gX (hΩ () _) i _

wf : ∀ s m → Acc s m
wf b⊥ = wf⊥
wf bX = wfX
```

目标, 与路径的要求 (只在跨底时).

```agda
data Tg : Bs → Cd → Bs → Cd → Set where
  sm : ∀ {s m t} → t ⊲ m → Tg s m s t
  cx : ∀ {t} B → LgB B → t ⊲ B → Tg bX hz b⊥ t

Nd : ∀ {s m s′ t} → Tg s m s′ t → HB (Lev s m) → Set
Nd (sm _) h = ⊤
Nd (cx B _ _) h = PH PSX B h

ndS : ∀ {s m s′ t} (tg : Tg s m s′ t) h → Nd tg (hs h) → Nd tg h
ndS (sm _) h p = tt
ndS (cx _ _ _) h p = p

ndL : ∀ {s m s′ t} (tg : Tg s m s′ t) f → Nd tg (hl f) → ∀ n → Nd tg (f n)
ndL (sm _) f p n = tt
ndL (cx _ _ _) f p n = p n
```

累加 (同 `TySupFold`): 后继取 $x\cdot\omega$ 的部分积, ℕ-极限取部分和, 坍缩取回灌链.

```agda
module _ {S : KS} where
  mul : HB S → ℕ → HB S
  mul x zero = x
  mul x (suc n) = mul x n ⊞ x

  chain : HB S → (HB S → HB S) → ℕ → HB S
  chain b k zero = k b
  chain b k (suc n) = chain b k n ⊞ k (b ⊞ chain b k n)

  Σ⁺ : (ℕ → HB S) → ℕ → HB S
  Σ⁺ f zero = f 0
  Σ⁺ f (suc n) = Σ⁺ f n ⊞ f (suc n)

lg↓ : ∀ {i X} → hs i ⊲ X → LgB X → LgB i
lg↓ p l = lgB⊲ (⊲ᴮ-tr (hsuc hself) p) tt l

⊏⊑ : ∀ {i X} → hs i ⊲ X → i ⊲ X
⊏⊑ p = ⊲ᴮ-tr (hsuc hself) p
```

**折叠** `Φ s m a lm s′ t tg b h nd`: 把第 $(s,m)$ 层的高度 $h$ 折到第 $(s',t)$ 层, 当前界 $b$. 同底 (`sm`) 与跨底 (`cx`) 只在 $\Omega$-结点处不同.

```agda
Φ : ∀ s m → Acc s m → LgB m → ∀ s′ t (tg : Tg s m s′ t) → HB (Lev s′ t) → (h : HB (Lev s m)) → Nd tg h → HB (Lev s′ t)
Φ s m a lm s′ t tg b hz nd = hs hz
Φ s m a lm s′ t tg b (hs h) nd = hl (mul (Φ s m a lm s′ t tg b h (ndS tg h nd)))
Φ s m a lm s′ t tg b (hl f) nd = hl (Σ⁺ (λ n → Φ s m a lm s′ t tg b (f n) (ndL tg f nd n)))
Φ s m (acc rs) lm _ t (sm pt) b (hΩ κ g) nd = caseDc (dcl pt lm (cl m κ))
  (λ κ′ fr → hΩ κ′ (λ c → Φ s m (acc rs) lm s t (sm pt) b (g (fr c)) tt))
  (λ to → hl (chain b (λ b′ → Φ s m (acc rs) lm s t (sm pt) b′ (g (to b′)) tt)))
  (λ i pi q to → Φ s i (rs s i (lt pi)) (lg↓ pi lm) s t (sm q) b
     (hl (chain (top s i) (λ b′ → Φ s m (acc rs) lm s i (sm (⊏⊑ pi)) b′ (g (to b′)) tt))) tt)
Φ _ _ (acc rs) lm _ t (cx B lB pt) b (hΩ (c , κ) g) (ev , pg) = caseDc (dcx lB pt ev (cl (hs c) κ))
  (λ κ′ fr → hΩ κ′ (λ c′ →
     Φ bX hz (acc rs) tt b⊥ t
       (cx (pnx P B (psh P B (fr c′)) (pad-sh P (fr c′) lB)) (plg P (pad-sh P (fr c′) lB) lB)
           (⊲ᴮ-tr pt (pnx↑ P (pad-sh P (fr c′) lB))))
       b (g (psh P B (fr c′))) (pg (psh P B (fr c′)) (pad-sh P (fr c′) lB))))
  (λ to → hl (chain b (λ b′ →
     Φ bX hz (acc rs) tt b⊥ t
       (cx (pnx P B (psh P B (to b′)) (pad-sh P (to b′) lB)) (plg P (pad-sh P (to b′) lB) lB)
           (⊲ᴮ-tr pt (pnx↑ P (pad-sh P (to b′) lB))))
       b′ (g (psh P B (to b′))) (pg (psh P B (to b′)) (pad-sh P (to b′) lB)))))
  (λ i pi q to → Φ b⊥ i (rs b⊥ i lx) (lg↓ pi lB) b⊥ t (sm q) b
     (hl (chain (top b⊥ i) (λ b′ →
        Φ bX hz (acc rs) tt b⊥ i
          (cx (pnx P B (psh P B (to b′)) (pad-sh P (to b′) lB)) (plg P (pad-sh P (to b′) lB) lB)
              (⊲ᴮ-tr (⊏⊑ pi) (pnx↑ P (pad-sh P (to b′) lB))))
          b′ (g (psh P B (to b′))) (pg (psh P B (to b′)) (pad-sh P (to b′) lB))))) tt)
  where P = pX c κ
```

## §7 形状给出的合法

`Sh`: ℕ-极限的相邻项在一切世界里是第一位置, 遗传; $\Omega$-结点只要分支遗传. 对一切输入 (不读输入合法, 不读路径).

```agda
module _ {S : KS} where
  Sh : HB S → Set
  Sh hz = ⊤
  Sh (hs h) = Sh h
  Sh (hl f) = (∀ {w : Wd S} n → f n ⊲[ w ] f (suc n)) × (∀ n → Sh (f n))
  Sh (hΩ κ g) = ∀ c → Sh (g c)

  Sh-⊞ : ∀ a b → Sh a → Sh b → Sh (a ⊞ b)
  Sh-⊞ a hz sa sb = sa
  Sh-⊞ a (hs b) sa sb = Sh-⊞ a b sa sb
  Sh-⊞ a (hl f) sa (st , sf) = (λ n → ⊞-⊲ a (st n)) , (λ n → Sh-⊞ a (f n) sa (sf n))
  Sh-⊞ a (hΩ κ g) sa sg = λ c → Sh-⊞ a (g c) sa (sg c)

  Sh-mul : ∀ x → Sh x → Sh (hl (mul x))
  Sh-mul x s = (λ n → ⊞-fst (mul x n) x) , go
    where go : ∀ n → Sh (mul x n)
          go zero = s
          go (suc n) = Sh-⊞ _ x (go n) s

  Sh-chain : ∀ b k → (∀ b′ → Sh (k b′)) → Sh (hl (chain b k))
  Sh-chain b k sk = (λ n → ⊞-fst (chain b k n) (k (b ⊞ chain b k n))) , go
    where go : ∀ n → Sh (chain b k n)
          go zero = sk b
          go (suc n) = Sh-⊞ _ _ (go n) (sk _)

  Sh-Σ : ∀ f → (∀ n → Sh (f n)) → Sh (hl (Σ⁺ f))
  Sh-Σ f sf = (λ n → ⊞-fst (Σ⁺ f n) (f (suc n))) , go
    where go : ∀ n → Sh (Σ⁺ f n)
          go zero = sf 0
          go (suc n) = Sh-⊞ _ _ (go n) (sf (suc n))

Sh-case : ∀ {L X t A} {S : KS} (d : Dc L X t A) {k s ab} →
          (∀ κ′ fr → Sh {S} (k κ′ fr)) → (∀ to → Sh {S} (s to)) → (∀ i u q to → Sh {S} (ab i u q to)) →
          Sh (caseDc d k s ab)
Sh-case (keep κ′ fr) sk ss sa = sk κ′ fr
Sh-case (same to) sk ss sa = ss to
Sh-case (above i u q to) sk ss sa = sa i u q to

Sh-Φ : ∀ s m a lm s′ t tg b h nd → Sh (Φ s m a lm s′ t tg b h nd)
Sh-Φ s m a lm s′ t tg b hz nd = tt
Sh-Φ s m a lm s′ t tg b (hs h) nd = Sh-mul _ (Sh-Φ s m a lm s′ t tg b h (ndS tg h nd))
Sh-Φ s m a lm s′ t tg b (hl f) nd = Sh-Σ _ (λ n → Sh-Φ s m a lm s′ t tg b (f n) (ndL tg f nd n))
Sh-Φ s m (acc rs) lm _ t (sm pt) b (hΩ κ g) nd = Sh-case (dcl pt lm (cl m κ))
  (λ κ′ fr c → Sh-Φ s m (acc rs) lm s t (sm pt) b (g (fr c)) tt)
  (λ to → Sh-chain b _ (λ b′ → Sh-Φ s m (acc rs) lm s t (sm pt) b′ (g (to b′)) tt))
  (λ i pi q to → Sh-Φ s i (rs s i (lt pi)) (lg↓ pi lm) s t (sm q) b _ tt)
Sh-Φ _ _ (acc rs) lm _ t (cx B lB pt) b (hΩ (c , κ) g) (ev , pg) = Sh-case (dcx lB pt ev (cl (hs c) κ))
  (λ κ′ fr c′ → Sh-Φ bX hz (acc rs) tt b⊥ t _ b _ _)
  (λ to → Sh-chain b _ (λ b′ → Sh-Φ bX hz (acc rs) tt b⊥ t _ b′ _ _))
  (λ i pi q to → Sh-Φ b⊥ i (rs b⊥ i lx) (lg↓ pi lB) b⊥ t (sm q) b _ tt)

-- 第 0 层没有种类: 形状就是合法
sh→lg : ∀ (h : Cd) → Sh h → LgB h
sh→lg hz s = tt
sh→lg (hs h) s = sh→lg h s
sh→lg (hl f) (st , s) = (λ {w} n → st {w} n) , (λ n → sh→lg (f n) (s n))
sh→lg (hΩ () _) s
```
