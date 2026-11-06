# 共享槽, 否定一路 (二): 共享槽让成员的坐标互为收缩; 相邻两级不能同在一个槽里

> 不含记号. 入口 [NegSlot](NegSlot.lagda.md). 对着接口 [SlotIf](SlotIf.lagda.md) ("接口定稿 2026-11-05 20:03 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **结果.**
>
> 1. **`sh-read` (定理, 盲; 对一切 `T`).** 在带证据 `ShW` 的世界上, 成员 $j'$ 的顶由成员 $j$ 的顶决定: $\mathrm{top}_{j'}\,w\equiv \mathrm{cE}^{-}_{j'}(\mathrm{cE}_j(\mathrm{top}_j\,w))$. 共享槽把一切成员认成 "同一个值经不同的读回".
> 2. **`img`, `slot-ret` (定理; 对一切 `T`, 只用 `top-cp`, `cE⁻-cE`, `wset`, `al-set`, `al-pr`).** 任一成员 $j$ 的任一顶值, 都在任一别的成员 $j'$ 的搬运 `cE j′` 的像里 (`img`: 把 $j$ 读到的那份共享世界经 `wset` 写给一切成员). 若成员 $j$ 的每个坐标值都是某个世界的顶 ("可达", `Reach`), 则 **$j$ 的坐标类型是 $j'$ 的坐标类型的收缩** (`slot-ret`, 映射 $\mathrm{cE}^-_{j'}\circ\mathrm{cE}_j$ 与 $\mathrm{cE}^-_{j}\circ\mathrm{cE}_{j'}$). 共享槽不是 "一个大类型装下各级": 它逼每一对成员的坐标类型互为收缩.
> 3. **`no-slot-adj` (定理, 否定; 对一切 `T`).** 若成员 $j_H$ 的坐标是 `HB S′`, `S′` 有一个种类的坐标是成员 $j_L$ 的坐标 (相邻两级), 且 $j_H$ 可达, 则矛盾 (`no-retract`).
> 4. **`K₁` 上 (定理, 否定).**
>    - **`no-slot-κHc`**: 接口 §4 的一族 `κHc` ($J=$ `H₀`) **没有任何 `Slot`** (任意 $Q$, `tq`, $\kappa_0$). 无别的前提: 可达性在闭的下标 `hs hz` 处由点更新给出 (`NegSlotPre.updO`, 下标不含函数, 按构造子判定).
>    - **`no-slot-pair`**: 任一族 ($J$, `κJ` 任意) 只要含相邻两级的成员 `κHc c`, `κHc (hs c)` ($c$ 任意, 可含函数), 且高的那份有 `RsK` (只用 `rs-top`) 与一个世界, 就没有 `Slot`.
>    - **`no-slot-κH`**: 原卡点的一族 `κH f = κHc (jx f)` ($J=\mathbb N\to$ `H₀`): 对任一 $f$, 若 $f^+$ ($n\mapsto$ `hs (jx f)`) 那份有 `RsK` 与一个世界, 就没有 `Slot`. 这一族里没有一对下标能按构造子判定, 所以用 `RsK` 的 `rs-top` 给可达性.
> 5. **前提实例与边界 (定理).** `slot-one`: 任一种类自己构成一个单成员的 `Slot` ($Q=T$); `slot-copies`: 一族成员若是同一个种类 (坐标同一类型), 也有 `Slot`. 所以 `Slot` 本身可满足, 否定只落在 "坐标类型不同, 且相邻" 的族上. `ShW` 可满足 (`sh-wset`: 任一世界经 `wset` 写成带证据的世界). `RsK` 前提: `NegSlotPre.RLz`, `RHz` (相邻两级 `κHc hz`, `κHc (hs hz)` 同时有 `RsK`). `no-slot-pair`/`no-slot-κH` 的 `Slot` 前提与 `RsK` 前提合起来是否可满足, 正是被否定的; 各自可满足见上.
>
> **只否定什么.** 只否定: 一个 `Slot` (接口 §2 的整个记录, 特别是 `wset` + `al-set` + `top-cp` + `cE⁻-cE`) 的成员里同时有相邻两级 (高的那份坐标是一棵高度树, 树的某个种类的坐标是低的那份的坐标), 且高的那份可达. **不否定**: 成员坐标类型相同的族 (构造一路的 `Lev (a ⊞ b)` 里同一种类的拷贝; `slot-copies`); 成员互不相邻的族 (例如只含 `κHc c` 一个 $c$); 不经 `wset` 的升界 (例如 `NegSlotPre` 已讨论的形状); `Dg` (接口 §1; 非对角无律, 本篇没有关于它的否定). 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegSlotWall where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.NegKindLvLev using (no-desc-step)
open import OCF.Align.GenFoldIf using (K₁; TopG; top; w₀)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.NegGenFoldUpd using (jx)
open import OCF.Align.RsOwnIf using (RsK; rs; rs-top; subW; topSub)
open import OCF.Align.SlotIf
open import OCF.Align.NegSlotPre using (_◁_; s; p; ps; updO)
```

## §1 对一切 `T`: 盲, 像, 收缩

```agda
module SL {T : KS} {tp : TopG T} {J : Set} {κJ : J → K T} {Q : KS} {tq : TopG Q} {κ₀ : K Q}
          (S : Slot T tp J κJ Q tq κ₀) where

  tj : ∀ j → Wd T → E T (κJ j)
  tj j w = top tp (κJ j) w

  -- 盲: 带证据的世界上, 一切成员的顶由任一成员的顶决定
  sh-read : ∀ j j′ w → ShW S w → tj j′ w ≡ cE⁻ S j′ (cE S j (tj j w))
  sh-read j j′ w (ω , al) =
    trans (sym (cE⁻-cE S j′ (tj j′ w)))
      (cong (cE⁻ S j′)
        (trans (top-cp S j′ w)
          (trans (cong (top tq κ₀) (trans (al-pr S j′ al) (sym (al-pr S j al))))
            (sym (top-cp S j w)))))

  -- 写: 任一世界经 wset 成为带证据的世界
  sh-wset : ∀ ω w → ShW S (wset S ω w)
  sh-wset ω w = ω , al-set S ω w

  -- 像: j 的顶在 cE j′ 的像里 (把 j 读到的共享世界写给一切成员)
  img : ∀ j j′ w → cE S j′ (tj j′ (wset S (wpr S j w) w)) ≡ cE S j (tj j w)
  img j j′ w =
    trans (top-cp S j′ (wset S (wpr S j w) w))
      (trans (cong (top tq κ₀) (al-pr S j′ (al-set S (wpr S j w) w))) (sym (top-cp S j w)))

  Reach : J → Set
  Reach j = ∀ e → Σ (Wd T) (λ w → tj j w ≡ e)

  slot-ret : ∀ j j′ → Reach j → E T (κJ j) ◁ E T (κJ j′)
  slot-ret j j′ R = record { s = λ e → cE⁻ S j′ (cE S j e) ; p = λ e′ → cE⁻ S j (cE S j′ e′) ; ps = pf }
    where
    pf : ∀ e → cE⁻ S j (cE S j′ (cE⁻ S j′ (cE S j e))) ≡ e
    pf e = trans (cong (λ z → cE⁻ S j (cE S j′ (cE⁻ S j′ z))) ζ)
             (trans (cong (λ z → cE⁻ S j (cE S j′ z)) (cE⁻-cE S j′ e₁))
               (trans (cong (cE⁻ S j) (sym ζ)) (cE⁻-cE S j e)))
      where
      w = proj₁ (R e)
      e₁ = tj j′ (wset S (wpr S j w) w)
      ζ : cE S j e ≡ cE S j′ e₁
      ζ = trans (cong (cE S j) (sym (proj₂ (R e)))) (sym (img j j′ w))
```

**相邻两级.** 高的那份的坐标是 `HB S′`, `S′` 的种类 $\kappa$ 的坐标是低的那份的坐标 (两个类型等式, 实例里都是 `refl`).

```agda
  ≡◁ : ∀ {X Y Z : Set} → X ≡ Y → Y ◁ Z → X ◁ Z
  ≡◁ refl R = R

  ◁≡ : ∀ {X Y Z : Set} → X ◁ Y → Y ≡ Z → X ◁ Z
  ◁≡ R refl = R

  no-slot-adj : ∀ jL jH {S′ : KS} (κ : K S′) → E T (κJ jH) ≡ HB S′ → E S′ κ ≡ E T (κJ jL) → Reach jH → ⊥
  no-slot-adj jL jH κ eH eL R = no-retract κ (s R′) (p R′) (ps R′)
    where
    R′ = ◁≡ (≡◁ (sym eH) (slot-ret jH jL R)) (sym eL)
```

## §2 前提实例: 单成员与同种类的拷贝

$Q=T$, 搬运是恒等, `wset ω w = ω`. 一族成员若都是同一个种类 $\kappa$, 同一个记录也成立 (`slot-copies`, $J$ 任意).

```agda
slot-copies : ∀ {T : KS} (tp : TopG T) (J : Set) (κ : K T) → Slot T tp J (λ _ → κ) T tp κ
slot-copies {T} tp J κ = record
  { cE = λ j e → e ; cE⁻ = λ j e → e ; cE⁻-cE = λ j e → refl
  ; wpr = λ j w → w ; lgπ = λ j l → l ; pr→ = λ j q → q ; pr← = λ j q → q
  ; lgE→ = λ j l → l ; lgE← = λ j l → l ; top-cp = λ j w → refl
  ; Al = λ P w → P w ; al-map = λ f q → f q ; al-pr = λ j q → q
  ; wset = λ ω w → ω ; al-set = λ ω w → refl
  ; set-≤ = λ q → q ; set-least = λ q r → r ; set-lg = λ lw lω → lω }

slot-one : ∀ {T : KS} (tp : TopG T) (κ : K T) → Slot T tp ⊤ (λ _ → κ) T tp κ
slot-one tp κ = slot-copies tp ⊤ κ

-- 例: K₁ 的 κHc c 单独成一个 Slot (任一 c, 可含函数)
slot-κHc-one : ∀ c → Slot K₁ tp₁ ⊤ (λ _ → κHc c) K₁ tp₁ (κHc c)
slot-κHc-one c = slot-one tp₁ (κHc c)
```

## §3 `K₁`

**整族 `κHc` 没有 `Slot`.** 低的成员 `hz` (坐标 `HB S₀`), 高的成员 `hs hz` (坐标 `HB (step S₀)`, 新种类的坐标 `HB S₀`). 高的那份的可达: `updO` 把分量 `hs (hs hz)` 的界置成任意值 (下标按构造子判定).

```agda
reach-hz1 : ∀ {Q tq κ₀} (S : Slot K₁ tp₁ H₀ κHc Q tq κ₀) → SL.Reach S (hs hz)
reach-hz1 S e = updO (w₀ (genKc 1)) e , refl

no-slot-κHc : ∀ {Q tq κ₀} → ¬ Slot K₁ tp₁ H₀ κHc Q tq κ₀
no-slot-κHc S = SL.no-slot-adj S hz (hs hz) {S′ = step S₀} (inj₂ tt) refl refl (reach-hz1 S)
```

**任一族, 含相邻两级 `κHc c`, `κHc (hs c)` ($c$ 任意).** 成员的种类经等式给出; 高的那份的可达由 `RsK` 的 `rs-top` 与一个世界给出 (世界可带任意证据 $P$).

```agda
reach-rs : ∀ {J κJ Q tq κ₀} (S : Slot K₁ tp₁ J κJ Q tq κ₀) j (P : Wd K₁ → Set) →
  RsK (subW K₁ P) (topSub tp₁) (κJ j) → Σ (Wd K₁) P → SL.Reach S j
reach-rs S j P R w e = proj₁ (rs R w e) , rs-top R

-- 坐标等式随种类等式
Eκ : ∀ {k k′ : K K₁} → k ≡ k′ → E K₁ k ≡ E K₁ k′
Eκ refl = refl

no-slot-pair : ∀ {J κJ Q tq κ₀} (S : Slot K₁ tp₁ J κJ Q tq κ₀) c jL jH →
  κJ jL ≡ κHc c → κJ jH ≡ κHc (hs c) →
  (P : Wd K₁ → Set) → RsK (subW K₁ P) (topSub tp₁) (κJ jH) → Σ (Wd K₁) P → ⊥
no-slot-pair S c jL jH eL eH P R w =
  SL.no-slot-adj S jL jH {S′ = Lev (hs c)} (inj₂ tt) (Eκ eH) (sym (Eκ eL)) (reach-rs S jH P R w)
```

**原卡点的一族 `κH f = κHc (jx f)`.** 低的成员 $f$, 高的成员 $f^+$: `Lev (jx f⁺)` 的第 1 个分量是 `step (Lev (jx f))`, 种类 `(1 , inj₂ tt)` 的坐标是 `HB (Lev (jx f))` (定义相等).

```agda
f⁺ : (ℕ → H₀) → ℕ → H₀
f⁺ f _ = hs (jx f)

no-slot-κH : ∀ {Q tq κ₀} (S : Slot K₁ tp₁ (ℕ → H₀) (λ f → κHc (jx f)) Q tq κ₀) f →
  (P : Wd K₁ → Set) → RsK (subW K₁ P) (topSub tp₁) (κHc (jx (f⁺ f))) → Σ (Wd K₁) P → ⊥
no-slot-κH S f P R w =
  SL.no-slot-adj S f (f⁺ f) {S′ = Lev (jx (f⁺ f))} (1 , inj₂ tt) refl refl (reach-rs S (f⁺ f) P R w)
```

## §4 结论 (按档)

- **[定理]** `SL.sh-read` (盲: 带证据的世界上一切成员的顶由一个成员的顶决定), `SL.sh-wset`, `SL.img`, **`SL.slot-ret`** (可达的成员的坐标是任一别的成员的坐标的收缩).
- **[定理, 否定]** **`SL.no-slot-adj`** (一切 `T`); **`no-slot-κHc`** (无别的前提); **`no-slot-pair`**, **`no-slot-κH`** (前提: 高的那份的 `RsK` 与一个世界).
- **[定理, 前提实例]** `slot-copies`, `slot-one`, `slot-κHc-one` (`Slot` 可满足); `SL.sh-wset` (`ShW` 可满足); `reach-hz1`; `NegSlotPre.RLz`, `RHz`, `w0⊤` (`RsK` 与世界可满足).
- **[判断]** (1) 共享槽的代价不是 "槽要大", 是 "成员要两两互为收缩" (`slot-ret`); 坐标类型随级严格变大的族 (相邻级) 因此进不了同一个槽. 能进同一个槽的, 是坐标类型可以互相无损搬运的成员, 例如同一种类在不同位置的拷贝 (构造一路的 `SlotCp` 方向). (2) `κH f` 一族原卡点里 "坐标是高度, 坐标类型随级变" 的种类, 若要按级回灌, 槽只能按 "坐标类型的同构类" 分组, 每组一个槽; 组之间仍是原来的问题 (相邻级之间的升界). 这是判断, 没有编译成定理. (3) 穷尽是判断.
