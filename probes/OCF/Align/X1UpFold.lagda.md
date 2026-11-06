# 在 $X_1$ 上叠层: 上层折叠与它的路径

> 不含记号. 入口 [X1Up](X1Up.lagda.md), 接口 [X1UpIf](X1UpIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 对任一满足接口的 `U` 一条定义. 底层是 `PathOutIf` 的种类结构 `XS` (实例: $X_1$ 层). 叠层层号是可数层号 $m$ (`Cd`, 第 0 层的值), 第 $X_1\oplus m$ 层的种类结构 `LS m` 是 `XS` 上的 `step`/`sup` 塔 (与 `LFReTy.Lv` 同式: `LS hz` 字面就是 `XS`, 后继给 `step`, ℕ-极限给 `sup ℕ`).
>
> - **种类分两类** (`clD`): 底种类 (来自 `XS`) 与新种类 (第 $j$ 层的 $\Omega$, 位置 $j+1\lhd m$).
> - **上层折叠** `ΦU m a lm t pt b h`: 把第 $X_1\oplus m$ 层的高度折到第 $X_1\oplus t$ 层, 与 [TySupFold](TySupFold.lagda.md) 的 `Φ` 逐子句相同, 只有决定 `decU` 不同: **底种类一律留** (嵌入 `emb t κ₀`), 新种类按层号与目标比较 (`cmpB`, 公共上界 $m$), 照 `TySupC.pick` 留/同层/在上. 在上时链从第 $i$ 层的地板 `topU i` 起步; `topU hz` 是底层的地板 `topX`.
> - **折到 $X_1$** `ΦX m lm h`: 目标 $t=0$ (第 $X_1$ 层), 当前界取地板 `topX` (否定一路的提醒: 从 $0$ 起步则 "同层" 的链里没有 $\Omega$-结点).
> - **路径** (`PSL m`): 第 $X_1\oplus m$ 层的带路径结构逐层搭出: 旧种类原样; 新种类无证据, 分支只对 "在某个更大的世界 $V$ 里带路径" 的坐标要求在 $V$ 里带路径 (进入后的世界就是 $V$). **定理** `PH-ΦU`: 输入与当前界带路径, 则输出带路径 (对一切世界). `PH-ΦX`: 折到 $X_1$ 的输出满足 `PathOutFold.PH`, 可交给 `Ψ`.
>
> **底种类沿嵌入搬运证据 (PathOut 接手清单第 1 条的卡点).** 留下的底种类在目标层里是 `emb t κ₀`, 输入里是 `κ` (`clD m κ = bas κ₀ to`), 两边的证据、可入与进入后的世界都要沿各自的递归归到 `XS` 的 $\kappa_0$, 对变量层号不是 `refl`. 本篇的写法: 不证两边的世界相等, 只证**有序** (`upkE`: 目标侧的世界在 $\kappa_0$ 的世界之上; `clP`: 输入侧的世界在 $\kappa_0$ 的世界之下), 再用 "带路径对世界单调" (`PH-mono`, 由接口的三条律) 搬过去. 每条搬运引理对层号递归, 每一步类型字面对上, 不用 `subst`. 新种类同样 (`upkA`, `clP`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.X1UpIf
module OCF.Align.X1UpFold (U : X1UpIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.HtTowerTy
open import OCF.Align.TySupIf using (AccR; acc; Dc; keep; same; above)
open import OCF.Align.TySupC using (Cd; _⊑ᶜ_; _⊏ᶜ_; wfC; ⊏→⊑ᶜ; lgC↓ᶜ)
open import OCF.Align.TySupSum using (ICdΣ)
import OCF.Align.TySupFold as F
open F ICdΣ using (mul; chain; Σ⁺)
open import OCF.Align.PathOutIf using (module PathOutIf)
import OCF.Align.PathOutFold as PF
open X1UpIf U using (P; _≼_; ≼-rf; ≼-tr; topX; Lg-topX; PH-topX)
module I = X1UpIf U
open PathOutIf P using (XS; Wo)
module O = PathOutIf P
```

## §1 叠层与地板

```agda
LS : Cd → KS
LS hz = XS
LS (hs x) = step (LS x)
LS (hl f) = sup ℕ (λ n → LS (f n))
LS (hΩ () _)

topU : ∀ m → HB (LS m)
ΣU : (f : ℕ → Cd) → ℕ → HB (LS (hl f))
topU hz = topX
topU (hs x) = hΩ (inj₂ tt) up
topU (hl f) = hl (ΣU f)
topU (hΩ () _)
ΣU f zero = ι 0 (topU (f 0))
ΣU f (suc n) = ΣU f n ⊞ ι (suc n) (topU (f (suc n)))
```

## §2 种类的两类, 嵌入, 决定

```agda
data ClD (m : Cd) (κ : K (LS m)) : Set where
  bas : (κ₀ : K XS) → (E XS κ₀ → E (LS m) κ) → ClD m κ
  nw  : (j : Cd) → j ⊏ᶜ m → (HB (LS j) → E (LS m) κ) → ClD m κ

cS : ∀ {x κ} → ClD x κ → ClD (hs x) (inj₁ κ)
cS (bas κ₀ to) = bas κ₀ to
cS (nw j p to) = nw j (hsuc p) to

cL : ∀ {f} n {κ} → ClD (f n) κ → ClD (hl f) (n , κ)
cL n (bas κ₀ to) = bas κ₀ to
cL n (nw j p to) = nw j (hlim n p) to

clD : ∀ m κ → ClD m κ
clD hz κ = bas κ (λ e → e)
clD (hs x) (inj₁ κ) = cS (clD x κ)
clD (hs x) (inj₂ _) = nw x hself (λ c → c)
clD (hl f) (n , κ) = cL n (clD (f n) κ)
clD (hΩ () _) _
```

底种类嵌进第 $t$ 层 (ℕ-极限层取分量 $0$); 新种类沿路径 $j+1\lhd t$ 嵌进第 $t$ 层 (同 `TySupC.along`).

```agda
emb : ∀ t → K XS → K (LS t)
emb hz κ = κ
emb (hs x) κ = inj₁ (emb x κ)
emb (hl f) κ = 0 , emb (f 0) κ
emb (hΩ () _) _

frE : ∀ t κ → E (LS t) (emb t κ) → E XS κ
frE hz κ c = c
frE (hs x) κ c = frE x κ c
frE (hl f) κ c = frE (f 0) κ c
frE (hΩ () _) _ _

along : ∀ {i t} → i ⊏ᶜ t → K (LS t)
along hself = inj₂ tt
along (hsuc q) = inj₁ (along q)
along (hlim n q) = n , along q
along (hLim {κ = ()} _ _)

frA : ∀ {i t} (q : i ⊏ᶜ t) → E (LS t) (along q) → HB (LS i)
frA hself c = c
frA (hsuc q) c = frA q c
frA (hlim n q) c = frA q c
frA (hLim {κ = ()} _ _) _

pickU : ∀ {m t i} {κ : K (LS m)} → (HB (LS i) → E (LS m) κ) → i ⊏ᶜ m →
        (t ⊲[ tt ] hs i) ⊎ (hs i ⊲[ tt ] t) → Dc LS _⊏ᶜ_ _⊑ᶜ_ m t κ
pickU to pi (inj₂ q) = keep (along q) (λ c → to (frA q c))
pickU to pi (inj₁ hself) = keep (inj₂ tt) to
pickU to pi (inj₁ (hsuc hself)) = same to
pickU to pi (inj₁ (hsuc (hsuc q))) = above _ pi (hsuc q) to
pickU to pi (inj₁ (hsuc (hlim n q))) = above _ pi (hlim n q) to
pickU to pi (inj₁ (hsuc (hLim {κ = ()} _ _)))

-- 决定: 底种类一律留; 新种类的位置 j+1 与目标 t 都在 m 之下, m 合法
decU : ∀ m t → t ⊑ᶜ m → LgB m → (κ : K (LS m)) → ClD m κ → Dc LS _⊏ᶜ_ _⊑ᶜ_ m t κ
decU m t pt lm κ (bas κ₀ to) = keep (emb t κ₀) (λ c → to (frE t κ₀ c))
decU m t pt lm κ (nw j pj to) = pickU to pj (cmpB pj pt tt lm)
```

## §3 上层折叠

```agda
caseU : ∀ {m t κ} {B : Set} → Dc LS _⊏ᶜ_ _⊑ᶜ_ m t κ →
        ((κ′ : K (LS t)) → (E (LS t) κ′ → E (LS m) κ) → B) →
        ((HB (LS t) → E (LS m) κ) → B) →
        ((i : Cd) → i ⊏ᶜ m → t ⊑ᶜ i → (HB (LS i) → E (LS m) κ) → B) → B
caseU (keep κ′ fr) k s ab = k κ′ fr
caseU (same to) k s ab = s to
caseU (above i pi q to) k s ab = ab i pi q to

ΦU : ∀ m → AccR _⊏ᶜ_ m → LgB m → ∀ t → t ⊑ᶜ m → HB (LS t) → HB (LS m) → HB (LS t)
ΦU m (acc rs) lm t pt b hz = hs hz
ΦU m (acc rs) lm t pt b (hs h) = hl (mul (ΦU m (acc rs) lm t pt b h))
ΦU m (acc rs) lm t pt b (hl f) = hl (Σ⁺ (λ n → ΦU m (acc rs) lm t pt b (f n)))
ΦU m (acc rs) lm t pt b (hΩ κ g) = caseU (decU m t pt lm κ (clD m κ))
  (λ κ′ fr → hΩ κ′ (λ c → ΦU m (acc rs) lm t pt b (g (fr c))))
  (λ to → hl (chain b (λ b′ → ΦU m (acc rs) lm t pt b′ (g (to b′)))))
  (λ i pi q to → ΦU i (rs i pi) (lgC↓ᶜ pi lm) t q b
     (hl (chain (topU i) (λ b′ → ΦU m (acc rs) lm i (⊏→⊑ᶜ pi) b′ (g (to b′))))))

-- 折到第 X₁ 层, 当前界是底层的地板
ΦX : ∀ m → LgB m → HB (LS m) → HB XS
ΦX m lm h = ΦU m (wfC m) lm hz (z⊲ᴮ m) topX h
```

## §4 地板合法 (同 `TySupSum.Lg-topΣ`)

```agda
Lg-topU : ∀ m → LgB (topU m)
Lg-ΣU : ∀ f n → LgB (ΣU f n)
Lg-topU hz = Lg-topX
Lg-topU (hs x) = (λ lw e e′ p → up-⊲ p) , (λ c lc → Lg-up c lc)
Lg-topU (hl f) = (λ n → ⊞-fst (ΣU f n) (ι (suc n) (topU (f (suc n))))) , Lg-ΣU f
Lg-topU (hΩ () _)
Lg-ΣU f zero = Lg-ι 0 (topU (f 0)) (Lg-topU (f 0))
Lg-ΣU f (suc n) = Lg-⊞ (ΣU f n) (ι (suc n) (topU (f (suc n)))) (Lg-ΣU f n) (Lg-ι (suc n) (topU (f (suc n))) (Lg-topU (f (suc n))))
```

## §5 叠层的带路径结构

`step` 一步: 旧种类原样; 新种类 (坐标是下一层的值 $c$) 无证据, 可入 = "有更大的世界 $V$, $c$ 在 $V$ 里带路径", 进入后的世界是 $V$. `sup` 逐分量.

```agda
module StepPS {T : KS} (Q : PS _≼_ T) where
  open PS Q
  Ev⁺ : Wo → K (step T) → Set
  Ev⁺ W (inj₁ κ) = Ev W κ
  Ev⁺ W (inj₂ _) = ⊤

  Adm⁺ : (W : Wo) (κ : K (step T)) → E (step T) κ → Set
  Adm⁺ W (inj₁ κ) e = Adm W κ e
  Adm⁺ W (inj₂ _) c = Σ Wo (λ V → (W ≼ V) × PHg Q V c)

  nxt⁺ : (W : Wo) (κ : K (step T)) → Ev⁺ W κ → (e : E (step T) κ) → Adm⁺ W κ e → Wo
  nxt⁺ W (inj₁ κ) ev e a = nxt W κ ev e a
  nxt⁺ W (inj₂ _) _ _ a = proj₁ a

  ev↑⁺ : ∀ {W W′} → W ≼ W′ → ∀ {κ} → Ev⁺ W κ → Ev⁺ W′ κ
  ev↑⁺ q {inj₁ κ} ev = ev↑ q ev
  ev↑⁺ q {inj₂ _} ev = tt

  adm↓⁺ : ∀ {W W′} (q : W ≼ W′) {κ} (ev : Ev⁺ W κ) {e} (a′ : Adm⁺ W′ κ e) →
          Σ (Adm⁺ W κ e) (λ a → nxt⁺ W κ ev e a ≼ nxt⁺ W′ κ (ev↑⁺ q {κ} ev) e a′)
  adm↓⁺ q {inj₁ κ} ev a′ = adm↓ q ev a′
  adm↓⁺ q {inj₂ _} ev (V , w , p) = (V , ≼-tr q w , p) , ≼-rf

  ≼nx⁺ : ∀ {W κ} (ev : Ev⁺ W κ) e (a : Adm⁺ W κ e) → W ≼ nxt⁺ W κ ev e a
  ≼nx⁺ {κ = inj₁ κ} ev e a = ≼nx ev e a
  ≼nx⁺ {κ = inj₂ _} ev e (V , w , p) = w

psStep : ∀ {T} → PS _≼_ T → PS _≼_ (step T)
psStep Q = record { Ev = Ev⁺ ; Adm = Adm⁺ ; nxt = nxt⁺ ; ev↑ = ev↑⁺ ; adm↓ = adm↓⁺ ; ≼nx = ≼nx⁺ }
  where open StepPS Q

module SupPS {I : Set} {G : I → KS} (Q : (i : I) → PS _≼_ (G i)) where
  Evˢ : Wo → K (sup I G) → Set
  Evˢ W (i , κ) = PS.Ev (Q i) W κ

  Admˢ : (W : Wo) (κ : K (sup I G)) → E (sup I G) κ → Set
  Admˢ W (i , κ) e = PS.Adm (Q i) W κ e

  nxtˢ : (W : Wo) (κ : K (sup I G)) → Evˢ W κ → (e : E (sup I G) κ) → Admˢ W κ e → Wo
  nxtˢ W (i , κ) ev e a = PS.nxt (Q i) W κ ev e a

  ev↑ˢ : ∀ {W W′} → W ≼ W′ → ∀ {κ} → Evˢ W κ → Evˢ W′ κ
  ev↑ˢ q {i , κ} ev = PS.ev↑ (Q i) q ev

  adm↓ˢ : ∀ {W W′} (q : W ≼ W′) {κ} (ev : Evˢ W κ) {e} (a′ : Admˢ W′ κ e) →
          Σ (Admˢ W κ e) (λ a → nxtˢ W κ ev e a ≼ nxtˢ W′ κ (ev↑ˢ q {κ} ev) e a′)
  adm↓ˢ q {i , κ} ev a′ = PS.adm↓ (Q i) q ev a′

  ≼nxˢ : ∀ {W κ} (ev : Evˢ W κ) e (a : Admˢ W κ e) → W ≼ nxtˢ W κ ev e a
  ≼nxˢ {κ = i , κ} ev e a = PS.≼nx (Q i) ev e a

psSup : ∀ {I G} → ((i : I) → PS _≼_ (G i)) → PS _≼_ (sup I G)
psSup Q = record { Ev = Evˢ ; Adm = Admˢ ; nxt = nxtˢ ; ev↑ = ev↑ˢ ; adm↓ = adm↓ˢ ; ≼nx = ≼nxˢ }
  where open SupPS Q

base : PS _≼_ XS
base = record { Ev = O.Ev ; Adm = O.Adm ; nxt = O.nxt ; ev↑ = I.ev↑ ; adm↓ = I.adm↓ ; ≼nx = I.≼-nxt }

PSL : ∀ m → PS _≼_ (LS m)
PSL hz = base
PSL (hs x) = psStep (PSL x)
PSL (hl f) = psSup (λ n → PSL (f n))
PSL (hΩ () _)

PHU : ∀ m → Wo → HB (LS m) → Set
PHU m = PHg (PSL m)

-- 底层: PHg base 与 PathOutFold.PH 同式
PH→g : ∀ {W} h → PF.PH P W h → PHg base W h
PH→g hz p = tt
PH→g (hs h) p = PH→g h p
PH→g (hl f) p = λ n → PH→g (f n) (p n)
PH→g (hΩ κ g) (ev , p) = ev , λ e a → PH→g (g e) (p e a)

g→PH : ∀ {W} h → PHg base W h → PF.PH P W h
g→PH hz p = tt
g→PH (hs h) p = g→PH h p
g→PH (hl f) p = λ n → g→PH (f n) (p n)
g→PH (hΩ κ g) (ev , p) = ev , λ e a → g→PH (g e) (p e a)
```

## §6 带路径对世界单调, 对加法封闭

对任一带路径结构. 单调用 `ev↑`, `adm↓`; 加法 $a\boxplus h$ 把 $a$ 放进 $h$ 的每个分支, 分支的世界是 `nxt`, 用 `≼nx` 与单调搬过去.

```agda
module _ {T : KS} (Q : PS _≼_ T) where
  open PS Q
  PH-mono : ∀ {W W′} → W ≼ W′ → ∀ h → PHg Q W h → PHg Q W′ h
  PH-mono q hz p = tt
  PH-mono q (hs h) p = PH-mono q h p
  PH-mono q (hl f) p = λ n → PH-mono q (f n) (p n)
  PH-mono q (hΩ κ g) (ev , p) =
    ev↑ q ev , λ e a′ → PH-mono (proj₂ (adm↓ q ev a′)) (g e) (p e (proj₁ (adm↓ q ev a′)))

  PH-⊞ : ∀ {W} a h → PHg Q W a → PHg Q W h → PHg Q W (a ⊞ h)
  PH-⊞ a hz pa ph = pa
  PH-⊞ a (hs h) pa ph = PH-⊞ a h pa ph
  PH-⊞ a (hl f) pa ph = λ n → PH-⊞ a (f n) pa (ph n)
  PH-⊞ a (hΩ κ g) pa (ev , ph) = ev , λ e x → PH-⊞ a (g e) (PH-mono (≼nx ev e x) a pa) (ph e x)

  PH-mul : ∀ {W} x → PHg Q W x → ∀ n → PHg Q W (mul x n)
  PH-mul x p zero = p
  PH-mul x p (suc n) = PH-⊞ (mul x n) x (PH-mul x p n) p

  PH-Σ : ∀ {W} f → (∀ n → PHg Q W (f n)) → ∀ n → PHg Q W (Σ⁺ f n)
  PH-Σ f p zero = p 0
  PH-Σ f p (suc n) = PH-⊞ (Σ⁺ f n) (f (suc n)) (PH-Σ f p n) (p (suc n))

  PH-chain : ∀ {W} b k → PHg Q W b → (∀ b′ → PHg Q W b′ → PHg Q W (k b′)) → ∀ n → PHg Q W (chain b k n)
  PH-chain b k pb pk zero = pk b pb
  PH-chain b k pb pk (suc n) =
    PH-⊞ (chain b k n) (k (b ⊞ chain b k n)) (PH-chain b k pb pk n)
      (pk (b ⊞ chain b k n) (PH-⊞ b (chain b k n) pb (PH-chain b k pb pk n)))
```

## §7 地板带路径

```agda
PH-up : ∀ x {W} c → PHU x W c → PHU (hs x) W (up c)
PH-up x hz p = tt
PH-up x (hs c) p = PH-up x c p
PH-up x (hl f) p = λ n → PH-up x (f n) (p n)
PH-up x (hΩ κ g) (ev , p) = ev , λ e a → PH-up x (g e) (p e a)

PH-ι : ∀ f n {W} c → PHU (f n) W c → PHU (hl f) W (ι n c)
PH-ι f n hz p = tt
PH-ι f n (hs c) p = PH-ι f n c p
PH-ι f n (hl g) p = λ k → PH-ι f n (g k) (p k)
PH-ι f n (hΩ κ g) (ev , p) = ev , λ e a → PH-ι f n (g e) (p e a)

PH-topU : ∀ m W → PHU m W (topU m)
PH-ΣU : ∀ f W n → PHU (hl f) W (ΣU f n)
PH-topU hz W = PH→g topX (PH-topX W)
PH-topU (hs x) W = tt , λ c a → PH-up x c (proj₂ (proj₂ a))
PH-topU (hl f) W = PH-ΣU f W
PH-topU (hΩ () _) W
PH-ΣU f W zero = PH-ι f 0 (topU (f 0)) (PH-topU (f 0) W)
PH-ΣU f W (suc n) = PH-⊞ (PSL (hl f)) (ΣU f n) (ι (suc n) (topU (f (suc n))))
  (PH-ΣU f W n) (PH-ι f (suc n) (topU (f (suc n))) (PH-topU (f (suc n)) W))
```

## §8 搬运引理

**输入侧** (`clP`): 对 `clD m κ` 的两类. 底种类: 证据读回 $\kappa_0$ 的证据 (`evd`); $\kappa_0$ 的可入给出 $\kappa$ 的可入, 进入后的世界在 $\kappa_0$ 的之下. 新种类 (第 $j$ 层): 在更大世界 $V$ 里带路径的坐标可入, 进入后的世界在 $V$ 之下. 对层号递归, 每一步字面对上.

```agda
ClP : ∀ m κ → ClD m κ → Set
ClP m κ (bas κ₀ to) =
  Σ (∀ {W} → PS.Ev (PSL m) W κ → O.Ev W κ₀) (λ evd →
    ∀ {W} (ev : PS.Ev (PSL m) W κ) e (a : O.Adm W κ₀ e) →
      Σ (PS.Adm (PSL m) W κ (to e)) (λ a′ → PS.nxt (PSL m) W κ ev (to e) a′ ≼ O.nxt W κ₀ (evd ev) e a))
ClP m κ (nw j p to) =
  ∀ {W} (ev : PS.Ev (PSL m) W κ) c V → W ≼ V → PHU j V c →
    Σ (PS.Adm (PSL m) W κ (to c)) (λ a′ → PS.nxt (PSL m) W κ ev (to c) a′ ≼ V)

pS : ∀ {x κ} (c : ClD x κ) → ClP x κ c → ClP (hs x) (inj₁ κ) (cS c)
pS (bas κ₀ to) p = p
pS (nw j q to) p = p

pL : ∀ {f} n {κ} (c : ClD (f n) κ) → ClP (f n) κ c → ClP (hl f) (n , κ) (cL n c)
pL n (bas κ₀ to) p = p
pL n (nw j q to) p = p

clP : ∀ m κ → ClP m κ (clD m κ)
clP hz κ = (λ ev → ev) , (λ ev e a → a , ≼-rf)
clP (hs x) (inj₁ κ) = pS (clD x κ) (clP x κ)
clP (hs x) (inj₂ _) = λ ev c V w p → (V , w , p) , ≼-rf
clP (hl f) (n , κ) = pL n (clD (f n) κ) (clP (f n) κ)
clP (hΩ () _) _
```

**输出侧**: 留下的底种类 `emb t κ₀` 的证据由 $\kappa_0$ 的给出 (`evE`); 它的可入读回 $\kappa_0$ 的可入, 进入后的世界在 $\kappa_0$ 的之上 (`upkE`). 留下的新种类 `along q` 无证据 (`evA`); 可入读出 "更大世界 $V$ 与路径", 进入后的世界在 $V$ 之上 (`upkA`).

```agda
evE : ∀ t {W} κ → O.Ev W κ → PS.Ev (PSL t) W (emb t κ)
evE hz κ ev = ev
evE (hs x) κ ev = evE x κ ev
evE (hl f) κ ev = evE (f 0) κ ev
evE (hΩ () _) κ ev

upkE : ∀ t {W} κ (ev : O.Ev W κ) c (a : PS.Adm (PSL t) W (emb t κ) c) →
       Σ (O.Adm W κ (frE t κ c)) (λ a₀ → O.nxt W κ ev (frE t κ c) a₀ ≼ PS.nxt (PSL t) W (emb t κ) (evE t κ ev) c a)
upkE hz κ ev c a = a , ≼-rf
upkE (hs x) κ ev c a = upkE x κ ev c a
upkE (hl f) κ ev c a = upkE (f 0) κ ev c a
upkE (hΩ () _) κ ev c a

evA : ∀ {i t} (q : i ⊏ᶜ t) {W} → PS.Ev (PSL t) W (along q)
evA hself = tt
evA (hsuc q) = evA q
evA (hlim n q) = evA q
evA (hLim {κ = ()} _ _)

upkA : ∀ {i t} (q : i ⊏ᶜ t) {W} (ev : PS.Ev (PSL t) W (along q)) c (a : PS.Adm (PSL t) W (along q) c) →
       Σ Wo (λ V → (W ≼ V) × PHU i V (frA q c) × (V ≼ PS.nxt (PSL t) W (along q) ev c a))
upkA hself ev c (V , w , p) = V , w , p , ≼-rf
upkA (hsuc q) ev c a = upkA q ev c a
upkA (hlim n q) ev c a = upkA q ev c a
upkA (hLim {κ = ()} _ _) ev c a
```

## §9 定理: 上层折叠的输出带路径

归纳假设写成两个函数类型: `IH₁` (同一层号 $m$, 分支上, 任意目标), `IH₂` (在上之后从第 $i$ 层折到 $t$).

```agda
IH₁ : ∀ m → (∀ i → i ⊏ᶜ m → AccR _⊏ᶜ_ i) → LgB m → (κ : K (LS m)) → (E (LS m) κ → HB (LS m)) → Set
IH₁ m rs lm κ g = ∀ t′ (pt′ : t′ ⊑ᶜ m) b′ e V → PHU t′ V b′ → PHU m V (g e) →
                  PHU t′ V (ΦU m (acc rs) lm t′ pt′ b′ (g e))

IH₂ : ∀ m → (∀ i → i ⊏ᶜ m → AccR _⊏ᶜ_ i) → LgB m → ∀ t → HB (LS t) → Set
IH₂ m rs lm t b = ∀ i (pi : i ⊏ᶜ m) (q : t ⊑ᶜ i) x V → PHU t V b → PHU i V x →
                  PHU t V (ΦU i (rs i pi) (lgC↓ᶜ pi lm) t q b x)

module Nd (m : Cd) (rs : ∀ i → i ⊏ᶜ m → AccR _⊏ᶜ_ i) (lm : LgB m) (t : Cd) (pt : t ⊑ᶜ m)
          (b : HB (LS t)) (κ : K (LS m)) (g : E (LS m) κ → HB (LS m)) where
  Kc : (κ′ : K (LS t)) → (E (LS t) κ′ → E (LS m) κ) → HB (LS t)
  Kc κ′ fr = hΩ κ′ (λ c → ΦU m (acc rs) lm t pt b (g (fr c)))
  Sc : (HB (LS t) → E (LS m) κ) → HB (LS t)
  Sc to = hl (chain b (λ b′ → ΦU m (acc rs) lm t pt b′ (g (to b′))))
  Ac : (i : Cd) → i ⊏ᶜ m → t ⊑ᶜ i → (HB (LS i) → E (LS m) κ) → HB (LS t)
  Ac i pi q to = ΦU i (rs i pi) (lgC↓ᶜ pi lm) t q b
    (hl (chain (topU i) (λ b′ → ΦU m (acc rs) lm i (⊏→⊑ᶜ pi) b′ (g (to b′)))))
```

链: 新种类 (第 $j$ 层) 的结点坍缩到第 $j$ 层, 起点 $b_0$ 带路径则链的每一项带路径.

```agda
PH-ch : ∀ m rs lm κ (g : E (LS m) κ → HB (LS m)) {W} j pj (to : HB (LS j) → E (LS m) κ) →
        ClP m κ (nw j pj to) → PHU m W (hΩ κ g) → IH₁ m rs lm κ g →
        ∀ (pj′ : j ⊑ᶜ m) b₀ → PHU j W b₀ →
        PHU j W (hl (chain b₀ (λ b′ → ΦU m (acc rs) lm j pj′ b′ (g (to b′)))))
PH-ch m rs lm κ g {W} j pj to pk (ev , pg) ih pj′ b₀ p₀ =
  PH-chain (PSL j) b₀ _ p₀ (λ b′ pb′ →
    PH-mono (PSL j) (proj₂ (pk ev b′ W ≼-rf pb′)) _
      (ih j pj′ b′ (to b′) _ (PH-mono (PSL j) (PS.≼nx (PSL m) ev (to b′) (proj₁ (pk ev b′ W ≼-rf pb′))) b′ pb′)
        (pg (to b′) (proj₁ (pk ev b′ W ≼-rf pb′)))))

PH-pk : ∀ m rs lm t pt b κ (g : E (LS m) κ → HB (LS m)) W j pj (to : HB (LS j) → E (LS m) κ) →
        ClP m κ (nw j pj to) → PHU t W b → PHU m W (hΩ κ g) → IH₁ m rs lm κ g → IH₂ m rs lm t b →
        (r : (t ⊲[ tt ] hs j) ⊎ (hs j ⊲[ tt ] t)) →
        PHU t W (caseU (pickU to pj r) (Nd.Kc m rs lm t pt b κ g) (Nd.Sc m rs lm t pt b κ g) (Nd.Ac m rs lm t pt b κ g))
PH-pk m rs lm t pt b κ g W j pj to pk pb (ev , pg) ih₁ ih₂ (inj₂ q) =
  evA q , λ c a →
    let u = upkA q (evA q) c a
        V = proj₁ u ; w = proj₁ (proj₂ u) ; pc = proj₁ (proj₂ (proj₂ u)) ; w′ = proj₂ (proj₂ (proj₂ u))
        a′ = proj₁ (pk ev (frA q c) V w pc)
    in PH-mono (PSL t) (≼-tr (proj₂ (pk ev (frA q c) V w pc)) w′) _
         (ih₁ t pt b (to (frA q c)) _ (PH-mono (PSL t) (PS.≼nx (PSL m) ev (to (frA q c)) a′) b pb) (pg _ a′))
PH-pk m rs lm t pt b κ g W j pj to pk pb (ev , pg) ih₁ ih₂ (inj₁ hself) =
  tt , λ c a →
    let a′ = proj₁ (pk ev c (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a)))
    in PH-mono (PSL t) (proj₂ (pk ev c (proj₁ a) (proj₁ (proj₂ a)) (proj₂ (proj₂ a)))) _
         (ih₁ t pt b (to c) _ (PH-mono (PSL t) (PS.≼nx (PSL m) ev (to c) a′) b pb) (pg _ a′))
PH-pk m rs lm t pt b κ g W j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc hself)) =
  PH-ch m rs lm κ g j pj to pk ph ih₁ pt b pb
PH-pk m rs lm t pt b κ g W j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hsuc q))) =
  ih₂ j pj (hsuc q) _ W pb (PH-ch m rs lm κ g j pj to pk ph ih₁ (⊏→⊑ᶜ pj) (topU j) (PH-topU j W))
PH-pk m rs lm t pt b κ g W j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hlim n q))) =
  ih₂ j pj (hlim n q) _ W pb (PH-ch m rs lm κ g j pj to pk ph ih₁ (⊏→⊑ᶜ pj) (topU j) (PH-topU j W))
PH-pk m rs lm t pt b κ g W j pj to pk pb ph ih₁ ih₂ (inj₁ (hsuc (hLim {κ = ()} _ _)))

PH-nd : ∀ m rs lm t pt b κ (g : E (LS m) κ → HB (LS m)) W (c : ClD m κ) → ClP m κ c →
        PHU t W b → PHU m W (hΩ κ g) → IH₁ m rs lm κ g → IH₂ m rs lm t b →
        PHU t W (caseU (decU m t pt lm κ c) (Nd.Kc m rs lm t pt b κ g) (Nd.Sc m rs lm t pt b κ g) (Nd.Ac m rs lm t pt b κ g))
PH-nd m rs lm t pt b κ g W (bas κ₀ to) (evd , pk) pb (ev , pg) ih₁ ih₂ =
  evE t κ₀ (evd ev) , λ c a →
    let u = upkE t κ₀ (evd ev) c a
        a′ = proj₁ (pk ev (frE t κ₀ c) (proj₁ u))
    in PH-mono (PSL t) (≼-tr (proj₂ (pk ev (frE t κ₀ c) (proj₁ u))) (proj₂ u)) _
         (ih₁ t pt b (to (frE t κ₀ c)) _ (PH-mono (PSL t) (PS.≼nx (PSL m) ev (to (frE t κ₀ c)) a′) b pb) (pg _ a′))
PH-nd m rs lm t pt b κ g W (nw j pj to) pk pb ph ih₁ ih₂ =
  PH-pk m rs lm t pt b κ g W j pj to pk pb ph ih₁ ih₂ (cmpB pj pt tt lm)
```

**定理 (对一切 `U`, 一切输入).** 当前界与输入在世界 $W$ 里带路径, 则输出在 $W$ 里带路径. 递归与 `ΦU` 相同.

```agda
PH-ΦU : ∀ m a lm t pt b h W → PHU t W b → PHU m W h → PHU t W (ΦU m a lm t pt b h)
PH-ΦU m (acc rs) lm t pt b hz W pb ph = tt
PH-ΦU m (acc rs) lm t pt b (hs h) W pb ph =
  PH-mul (PSL t) _ (PH-ΦU m (acc rs) lm t pt b h W pb ph)
PH-ΦU m (acc rs) lm t pt b (hl f) W pb ph =
  PH-Σ (PSL t) _ (λ n → PH-ΦU m (acc rs) lm t pt b (f n) W pb (ph n))
PH-ΦU m (acc rs) lm t pt b (hΩ κ g) W pb ph =
  PH-nd m rs lm t pt b κ g W (clD m κ) (clP m κ) pb ph
    (λ t′ pt′ b′ e V pb′ pe → PH-ΦU m (acc rs) lm t′ pt′ b′ (g e) V pb′ pe)
    (λ i pi q x V pbx px → PH-ΦU i (rs i pi) (lgC↓ᶜ pi lm) t q b x V pbx px)

PH-ΦX : ∀ m lm h W → PHU m W h → PF.PH P W (ΦX m lm h)
PH-ΦX m lm h W ph = g→PH (ΦX m lm h)
  (PH-ΦU m (wfC m) lm hz (z⊲ᴮ m) topX h W (PH→g topX (PH-topX W)) ph)
```
