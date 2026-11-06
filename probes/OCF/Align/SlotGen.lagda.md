# 高度坐标的共享槽 (一): 对一切 `Slot` 的一起升; 必要条件

> 不含记号. 入口 [Slot](Slot.lagda.md), 接口 [SlotIf](SlotIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 一起升 (构造).** 给一个共享槽 `S : Slot T tp J κJ Q tq κ₀` 与共享种类上的一个升界 `R₀ : RsK Q tq κ₀`. 世界证据 `ShW S` (每一份共享世界都是同一个 $\omega$). 成员 $j$ 的升界: $\mathrm{rs}\,w\,v = \mathrm{wset}\,(R_0.\mathrm{rs}\ \omega\ (\mathrm{cE}_j\,v))\ w$, 即先在共享槽里升, 再把**一切**成员所在的共享世界置成升后的那一个. 新槽依赖旧槽 $\omega$ (不是 "忘" 的一起升; 对照否定一路 `NegSlotPre.no-forget`). `invS j : RsInv T (ShW S) tp (κJ j)`, `rsS j : RsK (subW T (ShW S)) (topSub tp) (κJ j)`. **对一切 $j$, 不判定下标.**
> - **§2 值 (定理).** `rs-same`: 升成员 $j$ 到 $v$ 之后, 每个成员 $j'$ 的顶经搬运都是 $\mathrm{cE}_j\,v$ (一切成员一起到 $v$). `rs-least`: 升后的世界是 "比原世界大, 且每份共享世界都 $\ge$ 升后的共享世界" 的世界里最小的. `share-no-loss`: 带证据的世界与 "把每份共享世界置成证据里的 $\omega$" 互相 $\le$ (共享不丢世界序里的信息). `cE-inj`: 搬运是单射 (读回不丢).
> - **§3 必要条件 (定理).** `rsFam→Dg`: 任一对一切成员的 `RsK` 族 (任一种类结构, 任一世界类型) 给出对角解码 `Dg`; `slot→Dg`: 共享槽给出的对角解码就是 $\mathrm{cE}^{-}_{j'}\circ\mathrm{cE}_j$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SlotGen where

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top)
open import OCF.Align.RsOwnIf using (RsK; rs; rs≤; rsLg; rs-top; RsInv; subW; topSub; rsᴵ)
open import OCF.Align.RsOwnSW using (inv→RsK)
open import OCF.Align.SlotIf
```

## §1 一起升

```agda
module Gen {T : KS} {tp : TopG T} {J : Set} {κJ : J → K T} {Q : KS} {tq : TopG Q} {κ₀ : K Q}
           (S : Slot T tp J κJ Q tq κ₀) (R₀ : RsK Q tq κ₀) where

  Ev : Wd T → Set
  Ev = ShW S

  ω≡ : ∀ j {w} (p : Ev w) → wpr S j w ≡ proj₁ p
  ω≡ j (ω , al) = al-pr S j al

  cE-inj : ∀ j {x y} → cE S j x ≡ cE S j y → x ≡ y
  cE-inj j {x} {y} e = trans (sym (cE⁻-cE S j x)) (trans (cong (cE⁻ S j) e) (cE⁻-cE S j y))

  -- 升后的共享世界
  ω⁺ : ∀ j {w} → Ev w → E T (κJ j) → Wd Q
  ω⁺ j p v = rs R₀ (proj₁ p) (cE S j v)

  rsW : ∀ j (w : Wd T) → Ev w → E T (κJ j) → Wd T
  rsW j w p v = wset S (ω⁺ j p v) w

  -- 前提沿搬运落到共享槽
  pre : ∀ j {w v} (p : Ev w) → Pr T (κJ j) w (top tp (κJ j) w) v →
        Pr Q κ₀ (proj₁ p) (top tq κ₀ (proj₁ p)) (cE S j v)
  pre j {w} {v} p q =
    subst (λ ω → Pr Q κ₀ ω (top tq κ₀ ω) (cE S j v)) (ω≡ j p)
      (subst (λ x → Pr Q κ₀ (wpr S j w) x (cE S j v)) (top-cp S j w) (pr→ S j q))

  rsW≤ : ∀ j {w v} (p : Ev w) → Pr T (κJ j) w (top tp (κJ j) w) v → _≤w_ T w (rsW j w p v)
  rsW≤ j {w} {v} p q =
    set-≤ S (al-map S (λ {x} e → subst (λ y → _≤w_ Q y (ω⁺ j p v)) (sym e) (rs≤ R₀ (pre j p q))) (proj₂ p))

  lgω : ∀ j {w} (p : Ev w) → LgW T w → LgW Q (proj₁ p)
  lgω j {w} p lw = subst (LgW Q) (ω≡ j p) (lgπ S j lw)

  rsW-top : ∀ j w (p : Ev w) v → top tp (κJ j) (rsW j w p v) ≡ v
  rsW-top j w p v = cE-inj j
    (trans (top-cp S j (rsW j w p v))
      (trans (cong (top tq κ₀) (al-pr S j (al-set S (ω⁺ j p v) w))) (rs-top R₀)))

  invS : ∀ j → RsInv T Ev tp (κJ j)
  invS j = record
    { rsᴵ = rsW j
    ; rsᴵ-P = λ {w} p v → ω⁺ j p v , al-set S (ω⁺ j p v) w
    ; rsᴵ≤ = λ p q → rsW≤ j p q
    ; rsᴵLg = λ p lw lv → set-lg S lw (rsLg R₀ (lgω j p lw) (lgE→ S j lv))
    ; rsᴵ-top = λ {w} {v} p → rsW-top j w p v }

  rsS : ∀ j → RsK (subW T Ev) (topSub tp) (κJ j)
  rsS j = inv→RsK (invS j)

  -- 接口 §3 的形状: 对一切成员
  famS : RsFam (subW T Ev) (topSub tp) J κJ
  famS = rsS
```

## §2 值

```agda
  -- 升 j 之后, 每个成员 j′ 的顶经搬运都是 cE j v
  rs-same : ∀ j j′ (w : Wd T) (p : Ev w) v → cE S j′ (top tp (κJ j′) (rsW j w p v)) ≡ cE S j v
  rs-same j j′ w p v =
    trans (top-cp S j′ (rsW j w p v))
      (trans (cong (top tq κ₀) (al-pr S j′ (al-set S (ω⁺ j p v) w))) (rs-top R₀))

  -- 于是 j′ 的顶就是 v 读回到 j′
  rs-other : ∀ j j′ (w : Wd T) (p : Ev w) v → top tp (κJ j′) (rsW j w p v) ≡ cE⁻ S j′ (cE S j v)
  rs-other j j′ w p v = trans (sym (cE⁻-cE S j′ _)) (cong (cE⁻ S j′) (rs-same j j′ w p v))

  rs-least : ∀ j (w : Wd T) (p : Ev w) v (w′ : Wd T) → _≤w_ T w w′ →
             Al S (λ x → _≤w_ Q (ω⁺ j p v) x) w′ → _≤w_ T (rsW j w p v) w′
  rs-least j w p v w′ q al = set-least S q al

  share-no-loss : ∀ {w} (p : Ev w) → _≤w_ T w (wset S (proj₁ p) w) × _≤w_ T (wset S (proj₁ p) w) w
  share-no-loss {w} p =
    set-≤ S (al-map S (λ {x} e → subst (λ y → _≤w_ Q y (proj₁ p)) (sym e) (≤w-rf Q)) (proj₂ p)) ,
    set-least S (≤w-rf T) (al-map S (λ {x} e → subst (λ y → _≤w_ Q (proj₁ p) y) (sym e) (≤w-rf Q)) (proj₂ p))
```

## §3 必要条件

任一对一切成员一致的 `RsK` 族 (这里 $T$ 任意, 所以也包括 `subW` 带任意证据的世界) 在任一世界 $w$ 上给出对角解码: $\mathrm{dc}\,j\,j'\,v = $ 升 $j$ 到 $v$ 之后 $j'$ 的顶. 对角律就是 `rs-top`.

```agda
rsFam→Dg : ∀ {T : KS} {tp : TopG T} {J : Set} {κJ : J → K T} →
           RsFam T tp J κJ → Wd T → Dg J (λ j → E T (κJ j))
rsFam→Dg {tp = tp} {κJ = κJ} R w = record
  { dc = λ j j′ v → top tp (κJ j′) (rs (R j) w v)
  ; dc-d = λ j v → rs-top (R j) }

slot→Dg : ∀ {T tp J κJ Q tq κ₀} → Slot T tp J κJ Q tq κ₀ → Dg J (λ j → E T (κJ j))
slot→Dg S = record { dc = λ j j′ x → cE⁻ S j′ (cE S j x) ; dc-d = λ j x → cE⁻-cE S j x }
```

## §4 结论 (按档)

- **[构造]** `Gen.invS`, `Gen.rsS`, `Gen.famS`: 对一切共享槽与共享种类上的一个升界, 一族成员 (下标任意, 可以含函数) 在带证据 `ShW` 的世界上都有 `RsInv`/`RsK` (`KLv` 的三条升界律), 不判定下标.
- **[定理]** `rs-same`, `rs-other`, `rs-least`, `share-no-loss`, `cE-inj`; `rsFam→Dg`, `slot→Dg`.
- **[判断]** 一起升的代价与 [RsOwnSW](RsOwnSW.lagda.md) 相同: 升一个成员就把一切成员升到同一个 (搬运后的) $v$ (`rs-other`). 证据只约束共享世界, 共享槽以外的界由 `set-≤`, `set-least` 约束 (实例里不动).
