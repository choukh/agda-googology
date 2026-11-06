
# 种类塔上的一级折叠, 否定一路 (一): 公共上界之下的可入判定是定理

> 不含记号. 入口 [NegKcFold](NegKcFold.lagda.md). 对着接口 [KcFoldIf](KcFoldIf.lagda.md) ("接口定稿 2026-11-05 15:44 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 UIP; 函数外延 `FE₀` (`ColimWNeg`) 只在 §4 作前提, 用到它的结论标 "条件".
>
> 嫌疑 (i): 高度坐标的可入判定是否只能在公共上界之下, 外层世界长高后旧证据弱化是否仍可判定. **结论: 可判定, 是构造 (定理), 不是否定.**
>
> 1. **顶坐标 (`TopK`).** 每个种类在每个世界里有一个顶坐标: 底 `S₀` 是世界本身, `step` 的新种类是世界的界, 并逐分量. 律 `bdTop`: 界之下的坐标都是顶坐标的第一位置. 对一切站 `Kc s`, 一切 `Lev c`, 极限 `KΛc` 一行一个构造子 (`topKc`, `topLev`, `topΛ`).
> 2. **缩世界的判定 (`Shr.shr`).** 外层世界 $w$ 在合法世界 $W$ 之下 ($w\le W$, 二者合法), 高度 $b$ 合法, $x\lhd_{[W]}b$, 则 $x\lhd_{[w]}b$ 可判定. 对 $b$ 结构递归: 后继与 ℕ-极限处用 `cmpB` 与良基 (`StallDxBdec.toLt`, `irr`) 排除别的路径; $\Omega$-结点处**只看顶坐标那一支** (合法的 $g$ 单调, 小世界里一切可入支都在顶坐标那一支之下), 在 $W$ 里用 `cmpK` 把 $x$ 送到顶坐标那一支之下或排除, 不搜索坐标.
> 3. **种类的可入判定 (`DecK`, `admKc`).** `S₀` 用 `LvOmLev.dec⊲`; `step` 的新种类 (坐标是高度) 先在大世界里 `cmpB`, 再用 `shr`; 并逐分量. 一切站, 一切 `Lev c`, 极限.
> 4. **对照 (否定): 不带公共上界撞分离子** (`bare-sep`, 条件 `FE₀` 到 `bare→WLPO`): 对裸的合法高度 $x$ 判定 $x\lhd_{[0]}\omega$.
> 5. **接口的 `BDecTower` 是定理** (`bdecTower`, `bdecΛ`, `bdecLev`): 接口的 `BDecK` 不要外层世界合法, 合法沿 `≤w` 往下传 (`LgDown`).
>
> 外层世界长高 $a\le a'$ 之后, 旧证据 (在 $a$ 里可入) 弱化成在 $a'$ 里可入 (`Bd↑`); 判定 "在 $a$ 里是否可入" 就是以 $a'$ (或任一更大的合法读世界) 为公共上界的同一条 `admKc`. 判定给出的是**某个**证据, 不一定是原来那个 (拷贝问题, 见入口的判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKcFoldDec where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; toLt; irr; wf; <s₀; <s; <l₀; <l; <Ω₀; <Ω)
open import OCF.Align.LvOmLev using (dec⊲)
open import OCF.Align.LvKtIf using (FN; nxt; Kc; KΛc)
open import OCF.Align.KcFoldIf using (BDecK; BDecTower)
open import OCF.Align.CumReadCF using (lg⊲)
open import Data.Bool using (Bool; true; false)
open import OCF.Align.ColimWIf using (finH; ω₀)
open import OCF.Align.ColimWNeg using (yα; Lg-yα; ne₁; FE₀; yα≡; WLPO)
```

## §1 顶坐标

```agda
record TopK (S : KS) : Set where
  field
    top   : (κ : K S) → Wd S → E S κ
    topBd : ∀ κ w → Bd S κ (top κ w) w
    bdTop : ∀ {κ c w} → Bd S κ c w → Pr S κ w c (top κ w)
open TopK public

topS₀ : TopK S₀
topS₀ = record { top = λ _ w → w ; topBd = λ _ w → C.self ; bdTop = λ e → e }

module _ {S : KS} (T : TopK S) where
  topK⁺ : (κ : K (step S)) → Wd (step S) → E (step S) κ
  topK⁺ (inj₁ κ) w = top T κ (proj₁ w)
  topK⁺ (inj₂ _) w = proj₂ w

  topBd⁺ : ∀ κ w → Bd (step S) κ (topK⁺ κ w) w
  topBd⁺ (inj₁ κ) w = topBd T κ (proj₁ w)
  topBd⁺ (inj₂ _) w = hself

  bdTop⁺ : ∀ {κ c w} → Bd (step S) κ c w → Pr (step S) κ w c (topK⁺ κ w)
  bdTop⁺ {inj₁ κ} e = bdTop T e
  bdTop⁺ {inj₂ _} e = e

  topStep : TopK (step S)
  topStep = record { top = topK⁺ ; topBd = topBd⁺ ; bdTop = λ {κ} → bdTop⁺ {κ} }

topSup : (I : Set) (F : I → KS) → ((i : I) → TopK (F i)) → TopK (sup I F)
topSup I F T = record
  { top = λ κ w → top (T (proj₁ κ)) (proj₂ κ) (w (proj₁ κ))
  ; topBd = λ κ w → topBd (T (proj₁ κ)) (proj₂ κ) (w (proj₁ κ))
  ; bdTop = λ {κ} e → bdTop (T (proj₁ κ)) e }

topLev : ∀ {S} (x : HB S) → TopK (Lev x)
topLev hz = topS₀
topLev (hs x) = topStep (topLev x)
topLev (hl f) = topSup ℕ (λ n → Lev (f n)) (λ n → topLev (f n))
topLev {S} (hΩ κ g) = topSup (E S κ) (λ c → Lev (g c)) (λ c → topLev (g c))

topFN : ∀ {K} → TopK K → (i : ⊤ ⊎ HB K) → TopK (FN K i)
topFN T (inj₁ _) = T
topFN T (inj₂ c) = topLev c

topNxt : ∀ {K} → TopK K → TopK (nxt K)
topNxt {K} T = topSup (⊤ ⊎ HB K) (FN K) (topFN T)

topKc : ∀ s → TopK (Kc s)
topKc zero = topS₀
topKc (suc s) = topNxt (topKc s)

topΛ : TopK KΛc
topΛ = topSup ℕ Kc topKc
```

## §2 环的否定与缩世界的判定

```agda
module _ {S : KS} where
  <-⊲ : ∀ {a b c : HB S} {w} → a <ᴮ b → b ⊲[ w ] c → a <ᴮ c
  <-⊲ q hself = q
  <-⊲ q (hsuc p) = <s (<-⊲ q p)
  <-⊲ q (hlim n p) = <l n (<-⊲ q p)
  <-⊲ q (hLim {c = c} e p) = <Ω c (<-⊲ q p)

  cyc : ∀ {y z : HB S} {w} → y ⊲[ w ] z → z <ᴮ y → ⊥
  cyc {z = z} p q = irr (wf z) (<-⊲ q p)

module Shr {S : KS} (T : TopK S) where
  noS : ∀ {x b : HB S} {w W} → ¬ (x ⊲[ w ] b) → x ⊲[ W ] b → ¬ (x ⊲[ w ] hs b)
  noS nr p hself = cyc p <s₀
  noS nr p (hsuc r) = nr r

  noL2 : ∀ {x w W n m} {f : ℕ → HB S} → LgB (hl f) → LgW S w → ¬ (x ⊲[ w ] f n) → x ⊲[ W ] f n → x ⊲[ w ] f m →
         (f m ⊲[ w ] f n) ⊎ (f n ⊲[ w ] f m) → ⊥
  noL2 lb lw nr p r (inj₁ mn) = nr (⊲ᴮ-tr r mn)
  noL2 {n = n} {m} {f} lb lw nr p r (inj₂ nm) with cmpB r nm lw (proj₂ lb m)
  ... | inj₂ xn = nr xn
  ... | inj₁ nx with toLt nx
  ...   | inj₁ e = nr (subst (λ z → z ⊲[ _ ] f n) e hself)
  ...   | inj₂ lt = cyc p lt

  noL : ∀ {x w W n} {f : ℕ → HB S} → LgB (hl f) → LgW S w → ¬ (x ⊲[ w ] f n) → x ⊲[ W ] f n → ¬ (x ⊲[ w ] hl f)
  noL {n = n} lb lw nr p hself = cyc p (<l₀ n)
  noL {n = n} {f} lb lw nr p (hlim m r) = noL2 lb lw nr p r (cmpB {L = hl f} (hlim n hself) (hlim m hself) lw lb)

  -- 外层世界 w 在读的世界 W 之下; 在 W 里的第一位置, 在 w 里是否仍是: 可判定
  shr : ∀ {x w W} (b : HB S) → _≤w_ S w W → LgW S W → LgW S w → LgB b → x ⊲[ W ] b → Dec (x ⊲[ w ] b)
  shrΩ : ∀ {x w W} κ (g : E S κ → HB S) {c} → _≤w_ S w W → LgW S W → LgW S w → LgB (hΩ κ g) →
         Bd S κ c W → x ⊲[ W ] g c → Pr S κ W (top T κ w) c ⊎ Pr S κ W c (top T κ w) → Dec (x ⊲[ w ] hΩ κ g)
  goΩ : ∀ {x w W} κ (g : E S κ → HB S) → _≤w_ S w W → LgW S W → LgW S w → LgB (hΩ κ g) →
        x ⊲[ W ] g (top T κ w) → Dec (x ⊲[ w ] hΩ κ g)

  shr b q lW lw lb hself = yes hself
  shr (hs b) q lW lw lb (hsuc p) with shr b q lW lw lb p
  ... | yes r = yes (hsuc r)
  ... | no nr = no (noS nr p)
  shr (hl f) q lW lw lb (hlim n p) with shr (f n) q lW lw (proj₂ lb n) p
  ... | yes r = yes (hlim n r)
  ... | no nr = no (noL lb lw nr p)
  shr {w = w} (hΩ κ g) q lW lw lb (hLim e p) = shrΩ κ g q lW lw lb e p (cmpK S e (Bd↑ S q (topBd T κ w)) lW)

  goΩ {x} {w} {W} κ g q lW lw lb xt with shr (g (top T κ w)) q lW lw (proj₂ lb (top T κ w) (lgBd S (topBd T κ w) lw)) xt
  ... | yes r = yes (hLim (topBd T κ w) r)
  ... | no nr = no noΩ
    where
    noΩ : ¬ (x ⊲[ w ] hΩ κ g)
    noΩ hself = cyc xt (<Ω₀ (top T κ w))
    noΩ (hLim e″ r) = nr (⊲ᴮ-tr r (proj₁ lb lw e″ (topBd T κ w) (bdTop T e″)))

  shrΩ {x} {w} {W} κ g {c} q lW lw lb e p (inj₂ ct) = goΩ κ g q lW lw lb (⊲ᴮ-tr p (proj₁ lb lW e (Bd↑ S q (topBd T κ w)) ct))
  shrΩ {x} {w} {W} κ g {c} q lW lw lb e p (inj₁ tc)
    with cmpB p (proj₁ lb lW (Bd↑ S q (topBd T κ w)) e tc) lW (proj₂ lb c (lgBd S e lW))
  ... | inj₂ xt = goΩ κ g q lW lw lb xt
  ... | inj₁ tx with toLt tx
  ...   | inj₁ eq = yes (hLim (topBd T κ w) (subst (λ z → z ⊲[ w ] g (top T κ w)) eq hself))
  ...   | inj₂ lt = no noΩ′
    where
    noΩ′ : ¬ (x ⊲[ w ] hΩ κ g)
    noΩ′ hself = cyc p (<Ω₀ c)
    noΩ′ (hLim e″ r) = cyc (⊲ᴮ↑ q (⊲ᴮ-tr r (proj₁ lb lw e″ (topBd T κ w) (bdTop T e″)))) lt
```

## §3 种类的可入判定 (一切 `Kc s`, `Lev c`, `KΛc`)

```agda
record DecK (S : KS) : Set where
  field
    decBd : ∀ {κ c w W} → _≤w_ S w W → LgW S W → LgW S w → Bd S κ c W → Dec (Bd S κ c w)
open DecK public

decS₀ : DecK S₀
decS₀ = record { decBd = λ q lW lw e → dec⊲ e q lW }

module _ {S : KS} (T : TopK S) (D : DecK S) where
  decBd⁺ : ∀ {κ c w W} → _≤w_ (step S) w W → LgW (step S) W → LgW (step S) w → Bd (step S) κ c W → Dec (Bd (step S) κ c w)
  decBd⁺ {inj₁ κ} q lW lw e = decBd D (proj₁ q) (proj₁ lW) (proj₁ lw) e
  decBd⁺ {inj₂ _} {c} {w , b} {W , B} (q₁ , q₂) (lW , lB) (lw , lb) e with cmpB e q₂ lW lB
  ... | inj₂ cb = Shr.shr T b q₁ lW lw lb cb
  ... | inj₁ bc with toLt bc
  ...   | inj₁ eq = yes (subst (λ z → z ⊲[ w ] b) eq hself)
  ...   | inj₂ lt = no (λ r → cyc (⊲ᴮ↑ q₁ r) lt)

  decStep : DecK (step S)
  decStep = record { decBd = λ {κ} → decBd⁺ {κ} }

decSup : (I : Set) (F : I → KS) → ((i : I) → DecK (F i)) → DecK (sup I F)
decSup I F D = record { decBd = λ {κ} q lW lw e → decBd (D (proj₁ κ)) (q (proj₁ κ)) (lW (proj₁ κ)) (lw (proj₁ κ)) e }

decLev : ∀ {S} (x : HB S) → DecK (Lev x)
decLev hz = decS₀
decLev (hs x) = decStep (topLev x) (decLev x)
decLev (hl f) = decSup ℕ (λ n → Lev (f n)) (λ n → decLev (f n))
decLev {S} (hΩ κ g) = decSup (E S κ) (λ c → Lev (g c)) (λ c → decLev (g c))

decFN : ∀ {K} → DecK K → (i : ⊤ ⊎ HB K) → DecK (FN K i)
decFN D (inj₁ _) = D
decFN D (inj₂ c) = decLev c

decNxt : ∀ {K} → DecK K → DecK (nxt K)
decNxt {K} D = decSup (⊤ ⊎ HB K) (FN K) (decFN D)

decKc : ∀ s → DecK (Kc s)
decKc zero = decS₀
decKc (suc s) = decNxt (decKc s)

decΛ : DecK KΛc
decΛ = decSup ℕ Kc decKc
```

**主定理 (对一切站与极限).**

```agda
admKc : ∀ s {κ c a W} → _≤w_ (Kc s) a W → LgW (Kc s) W → LgW (Kc s) a → Bd (Kc s) κ c W → Dec (Bd (Kc s) κ c a)
admKc s = decBd (decKc s)

admΛ : ∀ {κ c a W} → _≤w_ KΛc a W → LgW KΛc W → LgW KΛc a → Bd KΛc κ c W → Dec (Bd KΛc κ c a)
admΛ = decBd decΛ

admLev : ∀ {S} (x : HB S) {κ c a W} → _≤w_ (Lev x) a W → LgW (Lev x) W → LgW (Lev x) a → Bd (Lev x) κ c W → Dec (Bd (Lev x) κ c a)
admLev x = decBd (decLev x)

shrKc : ∀ s {x a W} (b : HB (Kc s)) → _≤w_ (Kc s) a W → LgW (Kc s) W → LgW (Kc s) a → LgB b → x ⊲[ W ] b → Dec (x ⊲[ a ] b)
shrKc s = Shr.shr (topKc s)

shrΛ : ∀ {x a W} (b : HB KΛc) → _≤w_ KΛc a W → LgW KΛc W → LgW KΛc a → LgB b → x ⊲[ W ] b → Dec (x ⊲[ a ] b)
shrΛ = Shr.shr topΛ
```

## §4 对照: 不带公共上界, 判定撞分离子

```agda
noLimFin : ∀ {f : ℕ → HB S₀} {w} n → ¬ (hl f ⊲[ w ] finH n)
noLimFin zero ()
noLimFin (suc n) (hsuc p) = noLimFin n p

allFα : ∀ α → yα α ≡ ω₀ → ∀ n → α n ≡ false
allFα α e n = h (α n) refl
  where
  h : ∀ b → α n ≡ b → α n ≡ false
  h false q = q
  h true q = ⊥-elim (ne₁ α n q (cong up e))

bare-sep : (∀ x → LgB x → Dec (x ⊲[ azero ] ω₀)) → ∀ α → (∀ n → α n ≡ false) ⊎ ¬ (yα α ≡ ω₀)
bare-sep D α with D (yα α) (Lg-yα α)
... | yes p = inj₁ (allFα α (atω p))
  where
  atω : ∀ {f : ℕ → HB S₀} → hl f ⊲[ azero ] ω₀ → hl f ≡ ω₀
  atω hself = refl
  atω (hlim n p) = ⊥-elim (noLimFin n p)
... | no np = inj₂ (λ e → np (subst (λ z → z ⊲[ azero ] ω₀) (sym e) hself))

bare→WLPO : FE₀ → (∀ x → LgB x → Dec (x ⊲[ azero ] ω₀)) → WLPO
bare→WLPO fe D α with bare-sep D α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (yα≡ fe α h))
```

## §5 接口的 `BDecK`: 对一切站与极限是定理

接口的 `BDecK` 不要外层世界 $a$ 合法; 合法沿 `≤w` 往下传 (`LgDown`, 各构造子一行), 所以 `DecK` 给出 `BDecK`.

```agda
LgDown : KS → Set
LgDown S = ∀ {a W} → _≤w_ S a W → LgW S W → LgW S a

dwS₀ : LgDown S₀
dwS₀ q lW = lg⊲ q lW

dwStep : ∀ {S} → LgDown S → LgDown (step S)
dwStep d (q₁ , q₂) (lW , lB) = d q₁ lW , lgB⊲ q₂ lW lB

dwSup : (I : Set) (F : I → KS) → ((i : I) → LgDown (F i)) → LgDown (sup I F)
dwSup I F d q lW i = d i (q i) (lW i)

dwLev : ∀ {S} (x : HB S) → LgDown (Lev x)
dwLev hz = dwS₀
dwLev (hs x) = dwStep (dwLev x)
dwLev (hl f) = dwSup ℕ (λ n → Lev (f n)) (λ n → dwLev (f n))
dwLev {S} (hΩ κ g) = dwSup (E S κ) (λ c → Lev (g c)) (λ c → dwLev (g c))

dwFN : ∀ {K} → LgDown K → (i : ⊤ ⊎ HB K) → LgDown (FN K i)
dwFN d (inj₁ _) = d
dwFN d (inj₂ c) = dwLev c

dwKc : ∀ s → LgDown (Kc s)
dwKc zero = dwS₀
dwKc (suc s) = dwSup (⊤ ⊎ HB (Kc s)) (FN (Kc s)) (dwFN (dwKc s))

dwΛ : LgDown KΛc
dwΛ = dwSup ℕ Kc dwKc

toBDec : ∀ {S} → DecK S → LgDown S → BDecK S
toBDec D d e q lW = decBd D q lW (d q lW) e

bdecTower : BDecTower
bdecTower s = toBDec (decKc s) (dwKc s)

bdecΛ : BDecK KΛc
bdecΛ = toBDec decΛ dwΛ

bdecLev : ∀ {S} (x : HB S) → BDecK (Lev x)
bdecLev x = toBDec (decLev x) (dwLev x)
```
