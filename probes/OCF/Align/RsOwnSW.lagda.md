# 积世界上的升界 (二): 世界带 "底拷贝同界" 的证据; 一切底拷贝的 `KLv`

> 不含记号. 入口 [RsOwn](RsOwn.lagda.md), 接口 [RsOwnIf](RsOwnIf.lagda.md) (`subW`, `topSub`, `RsInv`, `RsK`), 工具 [RsOwnSh](RsOwnSh.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 对任一带 `ShB` 的种类结构 $T$ (例: `KΛc`, `Kc s`, `Lev c`):
>
> - **不变式 `Uf w`**: 存在 $a$, 世界 $w$ 里每一份底拷贝的界都 $\equiv a$. $a$ 就是一切底拷贝的**字面公共上界** (也是下界). `TU = subW T Uf`: 种类, 坐标, 界, 第一位置, 比较都沿用 $T$, 世界带这份证据.
> - **`invB κ b : RsInv T Uf tp κ`** (对每个底拷贝 $\kappa$, 下标可以含函数): 升界 = 把**每一份**底拷贝的界置成 $v$ (`rB`). `rs-top` 无前提 (自己的顶恰为 $v$); `rs≤` 的前提 "旧顶 $\lhd v$" 经证据传到每一份拷贝 (旧界都 $\equiv$ 旧顶), 所以世界变大; 证据保持 (换后每份 $\equiv v$). **不判定任何下标.**
> - **`rsB κ b : RsK TU tpU κ`** (接口 §1, 即 `KLv` 的三条升界律), 由 `inv→RsK`.
> - **`genU : GenK TU`**, `ldU`, `flU`: 基世界的证据 ($a=0$, `al0`); A-回灌 `fbA` 对一切底拷贝给出同一个 `FBA` (读证据里的 $a$, 置一切底拷贝), 其余有损. `tpA-bound`: 它读出的就是该底拷贝自己的顶.
> - **`KLvB Λ κ b : KLv TU tpU Λ κ`** (接口 `KindLvIf` §3), 级层 $0$, 读回 `sum` (同 `FBA` 的读法); `lvU Λ : LvFb TU tpU Λ`: 底拷贝给 `KLvB`, 其余有损.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RsOwnSW where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top; topBd; GenK; tpK; w₀; lw₀; aK; frE; frE-lg; frE-mono; fbA;
                                       FBA; tpA; rsA; LgDn; lgDn; FbLg; FbLgAt; DK)
open import OCF.Align.GenFoldTree using (module Tree)
open import OCF.Align.KindLvIf using (KLv; LvFb)
open import OCF.Align.RsOwnIf
open import OCF.Align.RsOwnSh
```

## §1 从 `RsInv` 到 `RsK` (对一切 $T$, $P$)

```agda
inv→RsK : ∀ {T : KS} {P : Wd T → Set} {tp : TopG T} {κ} → RsInv T P tp κ → RsK (subW T P) (topSub tp) κ
inv→RsK R = record
  { rs = λ w v → rsᴵ R (proj₁ w) (proj₂ w) v , rsᴵ-P R (proj₂ w) v
  ; rs≤ = λ {w} q → rsᴵ≤ R (proj₂ w) q
  ; rsLg = λ {w} lw lv → rsᴵLg R (proj₂ w) lw lv
  ; rs-top = λ {w} → rsᴵ-top R (proj₂ w) }
```

## §2 不变式与每个底拷贝的升界

```agda
module SW {T : KS} (G : GenK T) (Sh : ShB T (tpK G) (w₀ G)) where
  Uf : Wd T → Set
  Uf w = Σ A (λ a → Al Sh (λ x → x ≡ a) w)

  TU : KS
  TU = subW T Uf

  tpU : TopG TU
  tpU = topSub (tpK G)

  -- 一个底拷贝的顶就是共享的界
  tp≡a : ∀ {κ} (b : Bot Sh κ) {w} (u : Uf w) → toA Sh b (top (tpK G) κ w) ≡ proj₁ u
  tp≡a b (a , al) = tp-al Sh b al

  lg-a : ∀ {w} (u : Uf w) → LgW T w → Lg (proj₁ u)
  lg-a {w} u lw = subst Lg (tp≡a (b₀ Sh) u) (lgA Sh (b₀ Sh) (lgBd T (topBd (tpK G) (κb Sh) w) lw))

  al≤ : ∀ {w a v} → Al Sh (λ x → x ≡ a) w → a ⊲ v → Al Sh (λ x → x ⊲ v) w
  al≤ {v = v} al p = al-map Sh (λ e → subst (_⊲ v) (sym e) p) al

  invB : ∀ κ (b : Bot Sh κ) → RsInv T Uf (tpK G) κ
  invB κ b = record
    { rsᴵ = λ w p v → rB Sh (toA Sh b v) w
    ; rsᴵ-P = λ {w} p v → toA Sh b v , rB-al Sh (toA Sh b v) w
    ; rsᴵ≤ = λ {w} {v} p q → rB-≤ Sh (al≤ (proj₂ p) (subst (_⊲ toA Sh b v) (tp≡a b p) (prA Sh b q)))
    ; rsᴵLg = λ p lw lv → rB-lg Sh lw (lgA Sh b lv)
    ; rsᴵ-top = λ {w} {v} p → top-eq w v }
    where
    top-eq : ∀ w v → top (tpK G) κ (rB Sh (toA Sh b v) w) ≡ v
    top-eq w v = trans (sym (fr-to Sh b _))
                   (trans (cong (frA Sh b) (tp-al Sh b (rB-al Sh (toA Sh b v) w))) (fr-to Sh b v))

  rsB : ∀ κ (b : Bot Sh κ) → RsK TU tpU κ
  rsB κ b = inv→RsK (invB κ b)
```

## §3 坍缩用的结构: `GenK`, `LgDn`, `FbLg`

A-回灌: 读证据里的共享界, 置一切底拷贝.

```agda
  shF : ∀ {κ} → FBA TU κ
  shF = record
    { tpA = λ w → proj₁ (proj₂ w)
    ; rsA = λ w v → rB Sh v (proj₁ w) , (v , rB-al Sh v (proj₁ w))
    ; rs≤ = λ {w} p → rB-≤ Sh (al≤ (proj₂ (proj₂ w)) p)
    ; rsLg = λ lw lv → rB-lg Sh lw lv
    ; tp-rs = C.self }

  fbAt : ∀ κ → Dec (Bot Sh κ) → FBA TU κ ⊎ ⊤
  fbAt κ (yes b) = inj₁ shF
  fbAt κ (no _) = inj₂ tt

  genU : GenK TU
  genU = record
    { tpK = tpU ; w₀ = w₀ G , (azero , al0 Sh) ; lw₀ = lw₀ G
    ; aK = aK G ; frE = frE G ; frE-lg = frE-lg G
    ; frE-mono = λ lw e e′ p → frE-mono G lw e e′ p
    ; fbA = λ κ → fbAt κ (bot? Sh κ) }

  ldU : LgDn T → LgDn TU
  ldU Ld = record { lgDn = λ p l → lgDn Ld p l }

  flAt : ∀ κ (d : Dec (Bot Sh κ)) → FbLgAt {TU} {κ} (fbAt κ d)
  flAt κ (yes b) {w} lw = lg-a (proj₂ w) lw
  flAt κ (no _) = tt

  flU : FbLg genU
  flU κ = flAt κ (bot? Sh κ)

  -- A-回灌读出的就是这个底拷贝自己的顶 (FBA 绑在种类上)
  tpA-bound : ∀ {κ} (b : Bot Sh κ) w → toA Sh b (top tpU κ w) ≡ tpA (shF {κ}) w
  tpA-bound b w = tp≡a b (proj₂ w)
```

## §4 每个底拷贝的 `KLv` (级层 $0$, 读回 `sum`)

```agda
  open Tree TU using (sum; sum-fst; Lg-sum)

  KLvB : (Λ : HB (step TU)) → ∀ κ (b : Bot Sh κ) → KLv TU tpU Λ κ
  KLvB Λ κ b = record
    { ℓ = hz ; ℓ⊲ = z⊲ᴮ Λ
    ; rd = λ lW e x → frA Sh b (sum (toA Sh b e) x)
    ; rd-fst = λ {W} lW e x → subst (λ e′ → Pr T κ (proj₁ (proj₁ W)) e′ (frA Sh b (sum (toA Sh b e) x)))
                                     (fr-to Sh b e) (frPr Sh b (sum-fst (toA Sh b e) x))
    ; rd-lg = λ lW e x le → lgFr Sh b (Lg-sum (toA Sh b e) x (lgA Sh b le))
    ; rs = rs (rsB κ b) ; rs≤ = rs≤ (rsB κ b) ; rsLg = rsLg (rsB κ b) ; rs-top = rs-top (rsB κ b) }

  lvAt : (Λ : HB (step TU)) → ∀ κ → Dec (Bot Sh κ) → KLv TU tpU Λ κ ⊎ ⊤
  lvAt Λ κ (yes b) = inj₁ (KLvB Λ κ b)
  lvAt Λ κ (no _) = inj₂ tt

  lvU : (Λ : HB (step TU)) → LvFb TU tpU Λ
  lvU Λ κ = lvAt Λ κ (bot? Sh κ)

  -- 每个底拷贝都有级回灌
  lv-bot : ∀ Λ κ → Bot Sh κ → Σ (KLv TU tpU Λ κ) (λ L → lvU Λ κ ≡ inj₁ L)
  lv-bot Λ κ b with bot? Sh κ
  ... | yes b′ = KLvB Λ κ b′ , refl
  ... | no nb = ⊥-elim (nb b)
```

## §5 升后世界的大小 (值)

`rs` 之后每一份底拷贝的界恰是 $v$ (`rs-all`); 它是比原世界大, 且每份底拷贝都 $\unrhd v$ 的世界里最小的 (`rs-least`); 非底拷贝的界 (`step` 的高度分量) 不动 (由 `rB` 的定义; 在世界序里体现为 `rs-least` 只要求 $w\le w'$).

```agda
  rs-all : ∀ κ (b : Bot Sh κ) w v → Al Sh (λ x → x ≡ toA Sh b v) (proj₁ (rs (rsB κ b) w v))
  rs-all κ b w v = rB-al Sh (toA Sh b v) (proj₁ w)

  rs-least : ∀ κ (b : Bot Sh κ) w v (w′ : Wd TU) → _≤w_ TU w w′ → Al Sh (λ x → toA Sh b v ⊲ x) (proj₁ w′) →
             _≤w_ TU (rs (rsB κ b) w v) w′
  rs-least κ b w v w′ q p = rB-least Sh q p
```

## §6 结论 (按档)

- **[构造]** `invB`, `rsB`: 对**一切**底拷贝 (含下标是坐标或含函数的高度的分量里的拷贝), 在带证据 `Uf` 的世界上, `RsInv`/`RsK` (即 `KLv` 的 `rs≤`, `rsLg`, `rs-top`) 成立, 不判定下标. `KLvB`, `lvU`: `KLv` 与 `LvFb`. `genU`, `ldU`, `flU`: 坍缩所需的 `GenK`, `LgDn`, `FbLg`.
- **[定理]** `tp≡a`, `tpA-bound` (A-回灌读的是该拷贝自己的顶), `lv-bot` (每个底拷贝有级回灌), `rs-all`, `rs-least` (升后世界的大小).
- **[判断]** 这是 "一起升" ($R\,a\,v=v$) 加世界证据; 它避开 `NegKindLvRaise.no-upAllR` 的方式是让那里的世界 `w′` (两份拷贝界不同) 不在 `TU` 里 (`RsOwnTm.w′-not-Uf`, 定理). 代价: 升一个底拷贝就升了一切底拷贝 (语义上与 "精确置自己, 别处不动" 不同; 值上的影响没有定理).
