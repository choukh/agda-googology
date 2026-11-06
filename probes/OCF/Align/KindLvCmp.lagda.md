# 按级回灌 (五): 与 `rd₁`, `toD₁`, `rd₂` 的对照; 实例的形状定理

> 不含记号. 入口 [KindLv](KindLv.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提. 第 4 层: 只加关系与定理, 不改前 3 层.
>
> - **§1 结构等价 `_≈_`**: 两棵树逐构造子相同, 函数分支逐点 (有函数外延时就是 `≡`; 这里不用函数外延).
> - **§2 级 $0$ (`Lev 0 = S₀`) 与 `rd₁` 对照 [定理].** $T=S_0$ 时, `readL 0` (级层第 1 层的数据读进 `HB S₀`) 与 `GenFoldRd.rd₁` (`G = genS₀`) 对一切数据结构等价 (`rdL0≈rd₁`). `wrL 0` 与 `toD₁` 的四行同形 (`wr0-*`, `toD₁-*`, `refl`).
> - **§3 级 $1$ (`Lev 1 = step S₀`) 与 `rd₂` 对照 [定理, 逐行].** `readL 1` 读第 2 层的数据: 过第 1 层的结点读成新种类 `inj₂ tt` 的 $\Omega$-结点 (`rdL1-new`), 分支是沿 `stepE` 的连续分支, 它与 `HtTowerCont.nbᴮ` 结构等价 (`nbJ≈nbᴮ`); 过第 0 层的结点读成旧种类 `inj₁ tt` 的 $\Omega$-结点 (`rdL1-old`); 这两行与 `rd₂` 的两行同形. 新种类的闭包结点有损 (`rdL1-nc`), `rd₂` 那一行经 `encH` 读成 κH 结点: 这是两者的差.
> - **§4 与 `onlyA-rd₁` 的对照 [定理].** `rd₁` 的输出只含底种类的结点 (`NewTwrObs.onlyA-rd₁`, 对一切 $T$); 级读回不是: `readL 1` 在过第 1 层的结点上输出新种类的结点 (`rdL1-notA`).
> - **§5 实例 `lvΛ` 的形状 [定理, `refl`]** (否定一路 `NegKindLvBlind.relevel` 说 "按自己的级" 不是接口的律, 所以写成实例上的定理): $\kappa_1$ 在对角的第 1 项里是头种类 (`κ₁-in-Bᴧ`); 它的级回灌的级层是第 2 层 (`K1-ℓ`), 读回就是 `readL 1` (`K1-rd`), 升界被看见 (`K1-seen`); 对照 `NewTwrK.lossy-rd 0 2 (inj₂ tt)`: 同一个种类在 `GΛ` 的 `fbA` 下有损 (`κ₁-was-lossy`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KindLvCmp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (nbᴮ)
open import OCF.Align.GenFoldIf using (GenK; fbA; tpK; top; LgDn; n0; n1; _⨾_; nl; ni; nc; nw; ss)
open import OCF.Align.GenFoldTree using (module Tree)
open import OCF.Align.GenFoldInst using (genS₀; ldS₀)
open import OCF.Align.LvKtIf using (KΛc)
open import OCF.Align.NewTwrColl using (GΛ; LdΛ)
open import OCF.Align.NewTwrEv using (two)
open import OCF.Align.NewTwrK using (lossy-rd)
open import OCF.Align.NewTwrObs using (OnlyA; oΩ)
open import OCF.Align.KindLvIf
open import OCF.Align.KindLvEmb
import OCF.Align.KindLvRd as KRd
import OCF.Align.GenFoldRd as GRd
open import OCF.Align.KindLvTw using (Bᴧ; κ₁; K1; lvΛ; Λ)
```

## §1 结构等价

```agda
module _ {S : KS} where
  infix 4 _≈_
  data _≈_ : HB S → HB S → Set where
    ≈z : hz ≈ hz
    ≈s : ∀ {x y} → x ≈ y → hs x ≈ hs y
    ≈l : ∀ {f g} → (∀ n → f n ≈ g n) → hl f ≈ hl g
    ≈Ω : ∀ {κ f g} → (∀ e → f e ≈ g e) → hΩ κ f ≈ hΩ κ g
```

## §2 级 0 与 `rd₁`, `toD₁`

```agda
module L0 where
  open Tree S₀
  open KRd S₀ ldS₀ using (readL; readLp; wrL)
  open GRd S₀ genS₀ ldS₀ using (rd₁; rdp₁; toD₁; module NbA)
  open NbA

  nbA-cong : ∀ {b b′ : HB S₀} {s s′ : A → HB S₀ → HB S₀} → b ≈ b′ → (∀ a {h h′} → h ≈ h′ → s a h ≈ s′ a h′) →
             ∀ e → nbA b s e ≈ nbA b′ s′ e
  nbA-cong q qs azero = q
  nbA-cong q qs (OCF.Align.CumReadCF.asuc e) = qs e (nbA-cong q qs e)
  nbA-cong q qs (OCF.Align.CumReadCF.alim f) = ≈l (λ n → nbA-cong q qs (f n))

  rdL0≈rd₁  : ∀ {W} (lW : LgW L₀ W) {b b′} → b ≈ b′ → (x : D (hs hz) W) → readL hz lW b x ≈ rd₁ lW b′ x
  rdpL0≈rd₁ : ∀ {W} (lW : LgW L₀ W) {b b′} → b ≈ b′ → (d : ℕ → D (hs hz) W) → ∀ n → readLp hz lW b d n ≈ rdp₁ lW b′ d n
  rdL0≈rd₁ lW q n0 = q
  rdL0≈rd₁ lW q n1 = ≈s q
  rdL0≈rd₁ lW q (x ⨾ y) = rdL0≈rd₁ lW (rdL0≈rd₁ lW q x) y
  rdL0≈rd₁ lW q (nl d) = ≈l (rdpL0≈rd₁ lW q d)
  rdL0≈rd₁ lW q (ni (ss hself) u) = ≈Ω (nbA-cong q (λ a q′ → rdL0≈rd₁ lW q′ (u (≤rf) lW (toD₀ a))))
  rdL0≈rd₁ lW q (nc (inj₁ κ) z u) = rdL0≈rd₁ lW q (u ≤rf lW)
  rdL0≈rd₁ lW q (nc (inj₂ _) () u)
  rdL0≈rd₁ lW q (nw p x) = rdL0≈rd₁ _ q x
  rdpL0≈rd₁ lW q d zero = q
  rdpL0≈rd₁ lW q d (suc n) = rdL0≈rd₁ lW (rdpL0≈rd₁ lW q d n) (d n)

  -- 写入: wrL 0 与 toD₁ 的四行同形
  wr0-z : ∀ {W} → wrL hz {W} hz ≡ n0
  wr0-z = refl
  toD₁-z : ∀ {W} → toD₁ {W} hz ≡ n0
  toD₁-z = refl
  wr0-s : ∀ {W} y → wrL hz {W} (hs y) ≡ wrL hz y ⨾ n1
  wr0-s y = refl
  toD₁-s : ∀ {W} y → toD₁ {W} (hs y) ≡ toD₁ y ⨾ n1
  toD₁-s y = refl
  wr0-l : ∀ {W} f → wrL hz {W} (hl f) ≡ nl (λ n → wrL hz (f n))
  wr0-l f = refl
  toD₁-l : ∀ {W} f → toD₁ {W} (hl f) ≡ nl (λ n → toD₁ (f n))
  toD₁-l f = refl
  wr0-Ω : ∀ {W} h → wrL hz {W} (hΩ tt h) ≡ ni (ss hself) (λ q lW′ x → wrL hz (h (sum azero x)))
  wr0-Ω h = refl
  toD₁-Ω : ∀ {W} h → toD₁ {W} (hΩ tt h) ≡ ni (ss hself) (λ q lW′ x → toD₁ (h (sum azero x)))
  toD₁-Ω h = refl
```

## §3 级 1 与 `rd₂`

```agda
≈-rf : ∀ {S : KS} (x : HB S) → x ≈ x
≈-rf hz = ≈z
≈-rf (hs x) = ≈s (≈-rf x)
≈-rf (hl f) = ≈l (λ n → ≈-rf (f n))
≈-rf (hΩ κ g) = ≈Ω (λ e → ≈-rf (g e))

-- 沿 stepE 的连续分支就是 nbᴮ (分支函数保持 ≈ 时)
nbJ≈nbᴮ : ∀ {S : KS} {b : HB (step S)} {s : HB S → HB (step S) → HB (step S)} →
          (∀ y {h h′} → h ≈ h′ → s y h ≈ s y h′) → ∀ y → nbJ (stepE {S}) b s y ≈ nbᴮ b s y
nbJ≈nbᴮ {b = b} sc hz = ≈-rf b
nbJ≈nbᴮ sc (hs y) = sc y (nbJ≈nbᴮ sc y)
nbJ≈nbᴮ sc (hl f) = ≈l (λ n → nbJ≈nbᴮ sc (f n))
nbJ≈nbᴮ sc (hΩ κ h) = ≈Ω (λ e → nbJ≈nbᴮ sc (h e))

module L1 (T : KS) (Ld : LgDn T) where
  open Tree T
  open KRd T Ld using (readL; Br)

  -- 过第 1 层: 新种类 (同 rd₂ 的 κH 行)
  rdL1-new : ∀ {W} (lW : LgW L₀ W) b (u : Br (hs hz) {W} hself) →
             Σ (HB S₀ → HB (Lev {T} (hs hz))) (λ g → readL (hs hz) lW b (ni (ss hself) u) ≡ hΩ (inj₂ tt) g)
  rdL1-new lW b u = _ , refl

  -- 过第 0 层: 旧种类 (同 rd₂ 的 κA 行)
  rdL1-old : ∀ {W} (lW : LgW L₀ W) b (u : Br (hs hz) {W} (hsuc hself)) →
             Σ (A → HB (Lev {T} (hs hz))) (λ g → readL (hs hz) lW b (ni (ss (hsuc hself)) u) ≡ hΩ (inj₁ tt) g)
  rdL1-old lW b u = _ , refl

  -- 新种类的闭包结点: 有损 (rd₂ 经 encH 读成 κH 结点)
  rdL1-nc : ∀ {W} (lW : LgW L₀ W) b z (u : ∀ {W′} → W ≤ W′ → LgW L₀ W′ → D (hs (hs hz)) W′) →
            readL (hs hz) lW b (nc (inj₂ tt) z u) ≡ readL (hs hz) lW b (u ≤rf lW)
  rdL1-nc lW b z u = refl
```

## §4 与 `onlyA-rd₁` 的对照

`rd₁` 的输出只含底种类 (`NewTwrObs.onlyA-rd₁`). 级读回在第 1 级输出新种类的结点:

```agda
  rdL1-notA : ∀ {W} (lW : LgW L₀ W) b (u : Br (hs hz) {W} hself) →
              ¬ OnlyA {Lev {T} (hs hz)} (inj₁ tt) (readL (hs hz) lW b (ni (ss hself) u))
  rdL1-notA lW b u ()
```

## §5 实例 `lvΛ` 的形状

```agda
-- κ₁ 是对角第 1 项的头种类
κ₁-in-Bᴧ : Σ (_ → HB KΛc) (λ g → Bᴧ 1 ≡ hs (hΩ κ₁ g))
κ₁-in-Bᴧ = _ , refl

lv-κ₁ : lvΛ κ₁ ≡ inj₁ K1
lv-κ₁ = refl

-- 按自己的级: 级层是第 2 层 (= lyL 1), 读回是 readL 1
K1-ℓ : ℓ K1 ≡ lyL {KΛc} (hs hz)
K1-ℓ = refl

K1-rd : ∀ {W} lW b x → rd K1 {W} lW b x ≡ KRd.readL KΛc LdΛ (hs hz) lW b x
K1-rd lW b x = refl

-- 升界被看见
K1-seen : ∀ {w v} → top (tpK GΛ) κ₁ (rs K1 w v) ≡ v
K1-seen = rs-top K1

-- 对照: 同一个种类在 NewTwr 的最终坍缩里有损
κ₁-was-lossy : fbA GΛ κ₁ ≡ inj₂ tt
κ₁-was-lossy = lossy-rd 0 two (inj₂ tt)
```
