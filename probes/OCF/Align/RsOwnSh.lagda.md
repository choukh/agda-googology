# 积世界上的升界 (一): 底拷贝的共享界, 对种类结构的构造子递归

> 不含记号. 入口 [RsOwn](RsOwn.lagda.md), 接口 [RsOwnIf](RsOwnIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 一个种类结构 $T$ 的**底拷贝**: 沿 `step` 的旧种类, 并的任一分量 (下标可以是坐标), 一直走到某个 `S₀` 的那个种类 (坐标 `A`, 界是 `A`). 本篇对 `S₀`, `step`, `sup` 各写一行, 给出记录 `ShB T tp w0`:
>
> - `Bot κ`: $\kappa$ 是底拷贝 (可判定 `bot?`: 对种类的构造子递归; 不判定下标相等, 只看种类这一份数据的形状).
> - `Al P w`: 世界 $w$ 里**每一份**底拷贝的界满足 $P$ (对世界的结构递归, 并的分量全称).
> - `rB v w`: 把每一份底拷贝的界换成 $v$, 别的界 (`step` 的新种类的高度界) 不动. **对世界的结构递归, 不判定任何下标**.
> - 律: `rB-al` (换后每份 $\equiv v$), `rB-≤` (每份都 $\lhd v$ 时世界变大), `rB-lg`, `rB-least` (比 $w$ 大且每份都 $\unrhd v$ 的世界都比 `rB v w` 大), `tp-al`, `tp-rB` (一个底拷贝的顶就是它在世界里的界), `prA`, `lgA`, `frPr`, `lgFr` (坐标与 `A` 互译), `al0` (基世界每份是 $0$); `rM` 与它的四条律 (逐份带 `Al` 的证据地换, 有界升界用).
>
> 然后对 `Lev c` (一切 $c$), `Kc s` (一切站), `KΛc` 组装 (`shLev`, `shKc`, `shΛ`), 顶坐标与基世界逐字是 [GenFoldInst](GenFoldInst.lagda.md) 的 `genLev`, `genKc`, `GΛ` 的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RsOwnSh where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; topBd; GenK; tpK; w₀)
open import OCF.Align.GenFoldTree using (topStepG)
open import OCF.Align.GenFoldInst using (genLev; genKc; topSupG; genS₀)
open import OCF.Align.LvKtIf using (FN; nxt; Kc; KΛc)
open import OCF.Align.NewTwrColl using (GΛ)
```

## §1 记录

```agda
record ShB (T : KS) (tp : TopG T) (w0 : Wd T) : Set₁ where
  field
    Bot   : K T → Set
    bot?  : (κ : K T) → Dec (Bot κ)
    κb    : K T
    b₀    : Bot κb
    toA   : ∀ {κ} → Bot κ → E T κ → A
    frA   : ∀ {κ} → Bot κ → A → E T κ
    to-fr : ∀ {κ} (b : Bot κ) a → toA b (frA b a) ≡ a
    fr-to : ∀ {κ} (b : Bot κ) x → frA b (toA b x) ≡ x
    prA   : ∀ {κ} (b : Bot κ) {w x y} → Pr T κ w x y → toA b x ⊲ toA b y
    frPr  : ∀ {κ} (b : Bot κ) {w a a′} → a ⊲ a′ → Pr T κ w (frA b a) (frA b a′)
    lgA   : ∀ {κ} (b : Bot κ) {x} → LgE T κ x → Lg (toA b x)
    lgFr  : ∀ {κ} (b : Bot κ) {a} → Lg a → LgE T κ (frA b a)
    Al    : (A → Set) → Wd T → Set
    al-map : ∀ {P Q : A → Set} → (∀ {x} → P x → Q x) → ∀ {w} → Al P w → Al Q w
    rB    : A → Wd T → Wd T
    rB-al : ∀ v w → Al (λ x → x ≡ v) (rB v w)
    rB-≤  : ∀ {v w} → Al (λ x → x ⊲ v) w → _≤w_ T w (rB v w)
    rB-lg : ∀ {v w} → LgW T w → Lg v → LgW T (rB v w)
    rB-least : ∀ {v w w′} → _≤w_ T w w′ → Al (λ x → v ⊲ x) w′ → _≤w_ T (rB v w) w′
    tp-al : ∀ {κ} (b : Bot κ) {P : A → Set} {w} → Al P w → P (toA b (top tp κ w))
    al0   : Al (λ x → x ≡ azero) w0
    -- 逐份带证据地换 (有界升界用)
    rM    : ∀ {P : A → Set} → (∀ a → P a → A) → (w : Wd T) → Al P w → Wd T
    rM-≤  : ∀ {P : A → Set} {φ : ∀ a → P a → A} → (∀ a p → a ⊲ φ a p) → ∀ {w} (al : Al P w) → _≤w_ T w (rM φ w al)
    rM-lg : ∀ {P : A → Set} {φ : ∀ a → P a → A} → (∀ a p → Lg (φ a p)) → ∀ {w} (al : Al P w) → LgW T w → LgW T (rM φ w al)
    rM-al : ∀ {P : A → Set} {φ : ∀ a → P a → A} {Q : A → Set} → (∀ a p → Q (φ a p)) → ∀ {w} (al : Al P w) → Al Q (rM φ w al)
    rM-tp : ∀ {κ} (b : Bot κ) {P : A → Set} {φ : ∀ a → P a → A} {w} (al : Al P w) →
            toA b (top tp κ (rM φ w al)) ≡ φ _ (tp-al b al)
open ShB public
```

## §2 三个构造

**底.**

```agda
shS₀ : ShB S₀ (tpK genS₀) azero
shS₀ = record
  { Bot = λ _ → ⊤ ; bot? = λ _ → yes tt ; κb = tt ; b₀ = tt
  ; toA = λ _ x → x ; frA = λ _ a → a ; to-fr = λ _ a → refl ; fr-to = λ _ x → refl
  ; prA = λ _ p → p ; frPr = λ _ p → p ; lgA = λ _ l → l ; lgFr = λ _ l → l
  ; Al = λ P w → P w ; al-map = λ f p → f p
  ; rB = λ v w → v ; rB-al = λ v w → refl ; rB-≤ = λ p → p ; rB-lg = λ lw lv → lv
  ; rB-least = λ q p → p
  ; tp-al = λ _ p → p ; al0 = refl
  ; rM = λ φ w al → φ w al ; rM-≤ = λ h al → h _ al ; rM-lg = λ h al lw → h _ al
  ; rM-al = λ h al → h _ al ; rM-tp = λ _ al → refl }
```

**一步.** 旧种类沿用, 新种类 (坐标是高度) 不是底拷贝; 世界的高度分量不动.

```agda
module _ {T : KS} {tp : TopG T} {w0 : Wd T} (Sh : ShB T tp w0) where
  private
    BotS : K (step T) → Set
    BotS (inj₁ κ) = Bot Sh κ
    BotS (inj₂ _) = ⊥

    botS? : (κ : K (step T)) → Dec (BotS κ)
    botS? (inj₁ κ) = bot? Sh κ
    botS? (inj₂ _) = no (λ ())

    toS : ∀ {κ} → BotS κ → E (step T) κ → A
    toS {inj₁ κ} b x = toA Sh b x

    frS : ∀ {κ} → BotS κ → A → E (step T) κ
    frS {inj₁ κ} b a = frA Sh b a

    to-frS : ∀ {κ} (b : BotS κ) a → toS b (frS b a) ≡ a
    to-frS {inj₁ κ} b a = to-fr Sh b a

    fr-toS : ∀ {κ} (b : BotS κ) x → frS b (toS b x) ≡ x
    fr-toS {inj₁ κ} b x = fr-to Sh b x

    prS : ∀ {κ} (b : BotS κ) {w x y} → Pr (step T) κ w x y → toS b x ⊲ toS b y
    prS {inj₁ κ} b p = prA Sh b p

    frPrS : ∀ {κ} (b : BotS κ) {w a a′} → a ⊲ a′ → Pr (step T) κ w (frS b a) (frS b a′)
    frPrS {inj₁ κ} b p = frPr Sh b p

    lgS : ∀ {κ} (b : BotS κ) {x} → LgE (step T) κ x → Lg (toS b x)
    lgS {inj₁ κ} b l = lgA Sh b l

    lgFrS : ∀ {κ} (b : BotS κ) {a} → Lg a → LgE (step T) κ (frS b a)
    lgFrS {inj₁ κ} b l = lgFr Sh b l

    tpS : ∀ {κ} (b : BotS κ) {P : A → Set} {w} → Al Sh P (proj₁ w) → P (toS b (top (topStepG tp) κ w))
    tpS {inj₁ κ} b p = tp-al Sh b p

    rMS : ∀ {P : A → Set} → (∀ a → P a → A) → (w : Wd (step T)) → Al Sh P (proj₁ w) → Wd (step T)
    rMS φ w al = rM Sh φ (proj₁ w) al , proj₂ w

    rM-tpS : ∀ {κ} (b : BotS κ) {P : A → Set} {φ : ∀ a → P a → A} {w} (al : Al Sh P (proj₁ w)) →
             toS b (top (topStepG tp) κ (rMS φ w al)) ≡ φ _ (tpS b {P} {w} al)
    rM-tpS {inj₁ κ} b {P} {φ} al = rM-tp Sh b {P} {φ} al

  shStep : ShB (step T) (topStepG tp) (w0 , hz)
  shStep = record
    { Bot = BotS ; bot? = botS? ; κb = inj₁ (κb Sh) ; b₀ = b₀ Sh
    ; toA = toS ; frA = frS ; to-fr = to-frS ; fr-to = fr-toS
    ; prA = prS ; frPr = frPrS ; lgA = lgS ; lgFr = lgFrS
    ; Al = λ P w → Al Sh P (proj₁ w) ; al-map = λ f p → al-map Sh f p
    ; rB = λ v w → rB Sh v (proj₁ w) , proj₂ w
    ; rB-al = λ v w → rB-al Sh v (proj₁ w)
    ; rB-≤ = λ p → rB-≤ Sh p , hself
    ; rB-lg = λ lw lv → rB-lg Sh (proj₁ lw) lv , proj₂ lw
    ; rB-least = λ q p → rB-least Sh (proj₁ q) p , proj₂ q
    ; tp-al = tpS ; al0 = al0 Sh
    ; rM = rMS
    ; rM-≤ = λ {P} {φ} h al → rM-≤ Sh {P} {φ} h al , hself
    ; rM-lg = λ {P} {φ} h al lw → rM-lg Sh {P} {φ} h al (proj₁ lw) , proj₂ lw
    ; rM-al = λ {P} {φ} {Q} h al → rM-al Sh {P} {φ} {Q} h al
    ; rM-tp = rM-tpS }
```

**并.** 下标 $I$ 任意 (可以是坐标): `Al` 对一切分量全称, `rB` 逐分量, 都不判定下标. `i₀` 只用来给出一份底拷贝 `κb`.

```agda
module _ (I : Set) (F : I → KS) (i₀ : I) {tps : (i : I) → TopG (F i)} {w0s : (i : I) → Wd (F i)}
         (Sh : (i : I) → ShB (F i) (tps i) (w0s i)) where
  private
    T = sup I F

    BotU : K T → Set
    BotU (i , κ) = Bot (Sh i) κ

    toU : ∀ {κ} → BotU κ → E T κ → A
    toU {i , κ} b x = toA (Sh i) b x

    frU : ∀ {κ} → BotU κ → A → E T κ
    frU {i , κ} b a = frA (Sh i) b a

  shSup : ShB (sup I F) (topSupG I F tps) (λ i → w0s i)
  shSup = record
    { Bot = BotU ; bot? = λ κ → bot? (Sh (proj₁ κ)) (proj₂ κ)
    ; κb = i₀ , κb (Sh i₀) ; b₀ = b₀ (Sh i₀)
    ; toA = λ {κ} → toU {κ} ; frA = λ {κ} → frU {κ}
    ; to-fr = λ {κ} b a → to-fr (Sh (proj₁ κ)) b a
    ; fr-to = λ {κ} b x → fr-to (Sh (proj₁ κ)) b x
    ; prA = λ {κ} b p → prA (Sh (proj₁ κ)) b p
    ; frPr = λ {κ} b p → frPr (Sh (proj₁ κ)) b p
    ; lgA = λ {κ} b l → lgA (Sh (proj₁ κ)) b l
    ; lgFr = λ {κ} b l → lgFr (Sh (proj₁ κ)) b l
    ; Al = λ P w → ∀ i → Al (Sh i) P (w i)
    ; al-map = λ f p i → al-map (Sh i) f (p i)
    ; rB = λ v w i → rB (Sh i) v (w i)
    ; rB-al = λ v w i → rB-al (Sh i) v (w i)
    ; rB-≤ = λ p i → rB-≤ (Sh i) (p i)
    ; rB-lg = λ lw lv i → rB-lg (Sh i) (lw i) lv
    ; rB-least = λ q p i → rB-least (Sh i) (q i) (p i)
    ; tp-al = λ {κ} b p → tp-al (Sh (proj₁ κ)) b (p (proj₁ κ))
    ; al0 = λ i → al0 (Sh i)
    ; rM = λ φ w al i → rM (Sh i) φ (w i) (al i)
    ; rM-≤ = λ {P} {φ} h al i → rM-≤ (Sh i) {P} {φ} h (al i)
    ; rM-lg = λ {P} {φ} h al lw i → rM-lg (Sh i) {P} {φ} h (al i) (lw i)
    ; rM-al = λ {P} {φ} {Q} h al i → rM-al (Sh i) {P} {φ} {Q} h (al i)
    ; rM-tp = λ {κ} b {P} {φ} al → rM-tp (Sh (proj₁ κ)) b {P} {φ} (al (proj₁ κ)) }
```

## §3 组装: 层号, 站, 极限站

```agda
shLev : ∀ {S} (c : HB S) → ShB (Lev c) (tpK (genLev c)) (w₀ (genLev c))
shLev hz = shS₀
shLev (hs c) = shStep (shLev c)
shLev (hl f) = shSup ℕ (λ n → Lev (f n)) 0 (λ n → shLev (f n))
shLev {S} (hΩ κ g) = shSup (E S κ) (λ e → Lev (g e)) (bot S κ) (λ e → shLev (g e))

shFN : ∀ {Q : KS} (G : GenK Q) → ShB Q (tpK G) (w₀ G) → (i : ⊤ ⊎ HB Q) →
       ShB (FN Q i) (tpK (OCF.Align.GenFoldInst.genFN G i)) (w₀ (OCF.Align.GenFoldInst.genFN G i))
shFN G Sh (inj₁ _) = Sh
shFN G Sh (inj₂ c) = shLev c

shKc : ∀ s → ShB (Kc s) (tpK (genKc s)) (w₀ (genKc s))
shKc zero = shS₀
shKc (suc s) = shSup (⊤ ⊎ HB (Kc s)) (FN (Kc s)) (inj₁ tt) (shFN (genKc s) (shKc s))

shΛ : ShB KΛc (tpK GΛ) (w₀ GΛ)
shΛ = shSup ℕ Kc 0 shKc
```

## §4 结论 (按档)

- **[定理/构造]** `ShB` 对 `S₀`, `step`, `sup` (任意下标, 含坐标下标) 各有一行 (`shS₀`, `shStep`, `shSup`); 对一切 `Lev c`, 一切站 `Kc s`, 极限站 `KΛc` 有实例 (`shLev`, `shKc`, `shΛ`), 顶坐标与基世界逐字是 `GenFoldInst` 的.
- **[判断]** `rB` 是 "同一个 $R$ 一起升" 里 $R\,a\,v=v$ 那一个 (`NegKindLvRaise.half-top`); 单独用它撞 `rs≤` (`no-upAllR` 的世界 `w′`). 下一篇在世界上加证据 "每份底拷贝的界相等", 让 `rs≤` 的前提变成对每份拷贝的字面公共上界.
