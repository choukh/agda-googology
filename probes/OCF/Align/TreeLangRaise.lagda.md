# 树的语言 (二): 由判据推出升界的形状 (C6 的下标)

> 不含记号. 入口 [TreeLang](TreeLang.lagda.md), 接口 [TreeLangIf](TreeLangIf.lagda.md) ("接口定稿 2026-11-05 20:27 (首次编译通过)", 变更记录: 无). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **问题.** C6: 一族种类 (例如 `Lev (hΩ κ g)` 里以坐标 $c$ 为下标的深种类) 要各自升界: 升一份, 别的不动. 什么样的下标与世界允许这样的升界? 本篇只从接口的律 (`Raise`: `set`, `keep`, 定义域 `Ev`) 出发.
>
> **结果 (都是定理).**
>
> 1. **`ev→wdec` (一般形, 对一切框架).** 一对带证据的成员 $j, j'$, 只要读数有一个可判定的 "基值" $v_0$ 与一个别的值 $v_1$, 合法的升界就给出键的弱判定: $\neg(\mathrm{key}\,j'\equiv\mathrm{key}\,j)\ \vee\ \neg\neg(\mathrm{key}\,j'\equiv\mathrm{key}\,j)$. **判据推出: 律的定义域里的一对成员, 它们的键必须 (弱) 可判定相等.** 裸下标 (`Bare`) 时对一切键成立 (`bare→wdec`).
> 2. **`shape` (形状定理), `unique`, `unique¬¬`.** 定义域里键可判定时, 合法的升界在读数上**唯一**, 就是按判定的点更新 (`pick`: 同键取 $v$, 异键取旧值). 不可判定时任意两个合法升界 "不能不一致" (`unique¬¬`). 判据在定义域里定死了升界, 自由只剩定义域之外.
> 3. **`sup-bare→Sep` (对照 `Lev` 的形状).** 以裸坐标为下标的积世界 (`Lev` 的 `sup` 的形状: 第 $c$ 个分量是 `Wd (Lev c)`, $c$ 取遍 `H₀`), 读每个分量里第一份底拷贝的界: 合法的裸升界推出分离子 `NegGenFoldUpd.Sep`. 这是分离子一族 (`upd₁-sep`, `updD-sep`) 作为 `ev→wdec` 的一个实例.
> 4. **`posR` (实例), `pos-unique`.** 下标取 "同一合法高度 $L$ 在同一合法世界 $\omega$ 里的字面第一位置" (`Pos`), 世界只对这些位置给分量, 键是高度: 判定由 `StallDxBdec.bdec` 给出, 点更新 `rsP` 满足 `set`, `keep` (对一切成员对, 证据在下标里); 而且任一合法升界在读数上都等于它.
>
> **推出的形状.** 由 1–4: 要逐个升界的种类族, 其下标 (键) 在律的定义域里必须可判定相等; `Lev` 的 Ω-并以裸坐标为下标, 不行 (3); 以 "共同合法界之下的字面位置" 为下标, 行, 且唯一 (4). 这就是 "Ω-并只取有界坐标". 对照: [ColimAIf](ColimAIf.lagda.md) 的 `LevA w` 与 `GWA` 正是这个形状 (那里是先设计后验证; 判断, 没有写成两者的同构定理).
>
> **剩下的自由度 (判断, 依据已有定理).** 判据不决定: (i) 证据放在种类里 (`LevA`: 同一层号经两条路径成两个种类, 拷贝要相干, `ColimA` 的 `noCrossA`) 还是放在世界里 (`AdmWIf.SupB`: 不是 `KS`, 缺 `botBd`); (ii) 读数随成员变类型 (跨级) 时, 同键取 $v$ 要沿判定给的相等证明搬运 (`ColimARaise.uip→raiseA1` 只是 UIP 条件下的定理; 族增量绕开). 本篇的框架读数类型 $V$ 不随成员变, 所以不碰 (ii). 这两处是 "需要新判据" 的信号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLangRaise where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.StallDxBdec using (bdec)
open import OCF.Align.NegGenFoldUpd using (jx; Sep; WDec; wdec→sep)
open import OCF.Align.TreeLangIf
```

## §1 律推出键的弱判定

```agda
module _ {F : RaiseFrame} (R : Raise F) where
  ev→wdec : ∀ {w j j′} → Ev F w j j′ → ∀ {v₀} → obs F j′ w ≡ v₀ → (v₁ : V F) → ¬ (v₁ ≡ v₀) →
            (∀ x → (x ≡ v₀) ⊎ ¬ (x ≡ v₀)) → ¬ (key F j′ ≡ key F j) ⊎ ¬ ¬ (key F j′ ≡ key F j)
  ev→wdec {w} {j} {j′} ev e0 v₁ ne z? with z? (obs F j′ (rs R w j v₁))
  ... | inj₁ e = inj₁ (λ k → ne (trans (sym (set R v₁ ev k)) e))
  ... | inj₂ ne′ = inj₂ (λ nk → ne′ (trans (keep R v₁ ev nk) e0))

  bare→wdec : Bare F → ∀ (w₀ : W F) {v₀} → (∀ j → obs F j w₀ ≡ v₀) → (v₁ : V F) → ¬ (v₁ ≡ v₀) →
              (∀ x → (x ≡ v₀) ⊎ ¬ (x ≡ v₀)) → ∀ j j′ → ¬ (key F j′ ≡ key F j) ⊎ ¬ ¬ (key F j′ ≡ key F j)
  bare→wdec b w₀ z0 v₁ ne z? j j′ = ev→wdec (b w₀ j j′) (z0 j′) v₁ ne z?
```

## §2 定义域里唯一: 就是按判定的点更新

```agda
pick : ∀ {X : Set} {Y : Set} → X ⊎ ¬ X → Y → Y → Y
pick (inj₁ _) a b = a
pick (inj₂ _) a b = b

module _ {F : RaiseFrame} (R : Raise F) where
  shape : ∀ {w j j′} v → Ev F w j j′ → (d : (key F j′ ≡ key F j) ⊎ ¬ (key F j′ ≡ key F j)) →
          obs F j′ (rs R w j v) ≡ pick d v (obs F j′ w)
  shape v ev (inj₁ k) = set R v ev k
  shape v ev (inj₂ nk) = keep R v ev nk

module _ {F : RaiseFrame} (R R′ : Raise F) where
  unique : ∀ {w j j′} v → Ev F w j j′ → (key F j′ ≡ key F j) ⊎ ¬ (key F j′ ≡ key F j) →
           obs F j′ (rs R w j v) ≡ obs F j′ (rs R′ w j v)
  unique v ev d = trans (shape R v ev d) (sym (shape R′ v ev d))

  unique¬¬ : ∀ {w j j′} v → Ev F w j j′ → ¬ ¬ (obs F j′ (rs R w j v) ≡ obs F j′ (rs R′ w j v))
  unique¬¬ v ev nq = (λ nk → nq (unique v ev (inj₂ nk))) (λ k → nq (unique v ev (inj₁ k)))
```

## §3 `Lev` 的形状: 裸坐标为下标的积世界, 推出分离子

先把框架层的弱判定搬到 `H₀` 上: 只要成员族里有一份以 `H₀` 为键的单射拷贝.

```agda
module _ {F : RaiseFrame} (R : Raise F) where
  bare→Sep : Bare F → ∀ (w₀ : W F) {v₀} → (∀ j → obs F j w₀ ≡ v₀) → (v₁ : V F) → ¬ (v₁ ≡ v₀) →
             (∀ x → (x ≡ v₀) ⊎ ¬ (x ≡ v₀)) →
             (ιJ : H₀ → J F) → (∀ a b → key F (ιJ a) ≡ key F (ιJ b) → a ≡ b) → Sep
  bare→Sep b w₀ z0 v₁ ne z? ιJ inj = wdec→sep wd
    where
    wd : WDec
    wd f f′ with bare→wdec R b w₀ z0 v₁ ne z? (ιJ (jx f)) (ιJ (jx f′))
    ... | inj₁ nk = inj₁ (λ e → nk (cong (λ a → key F (ιJ a)) e))
    ... | inj₂ nnk = inj₂ (λ ne′ → nnk (λ k → ne′ (inj (jx f′) (jx f) k)))
```

**`Lev` 的 Ω-并的世界**: 对每个坐标 $c$ (这里 $c$ 取遍 `H₀`) 有一个分量 `Wd (Lev c)`. 读数: 分量 $c$ 里第一份底拷贝的界 (`baseBd`, 沿 $c$ 的第 0 支 / 最小坐标支). 律的定义域是裸的 (`Ev` 恒为 `⊤`).

```agda
baseBd : ∀ {S : KS} (c : HB S) → Wd (Lev c) → A
baseBd hz w = w
baseBd (hs x) w = baseBd x (proj₁ w)
baseBd (hl f) w = baseBd (f 0) (w 0)
baseBd {S} (hΩ κ g) w = baseBd (g (bot S κ)) (w (bot S κ))

zW : ∀ {S : KS} (c : HB S) → Wd (Lev c)
zW hz = azero
zW (hs x) = zW x , hz
zW (hl f) n = zW (f n)
zW (hΩ κ g) e = zW (g e)

zW-base : ∀ {S : KS} (c : HB S) → baseBd c (zW c) ≡ azero
zW-base hz = refl
zW-base (hs x) = zW-base x
zW-base (hl f) = zW-base (f 0)
zW-base {S} (hΩ κ g) = zW-base (g (bot S κ))

isZ : ∀ x → (x ≡ azero) ⊎ ¬ (x ≡ azero)
isZ azero = inj₁ refl
isZ (asuc x) = inj₂ (λ ())
isZ (alim f) = inj₂ (λ ())

supF : RaiseFrame
supF = record
  { W = (c : H₀) → Wd (Lev c) ; J = H₀ ; Key = H₀ ; V = A
  ; key = λ c → c ; obs = λ c w → baseBd c (w c) ; Ev = λ _ _ _ → ⊤ }

sup-bare→Sep : Raise supF → Sep
sup-bare→Sep R = bare→Sep R (λ _ _ _ → tt) zW (λ c → zW-base c) (asuc azero) (λ ()) isZ (λ a → a) (λ a b e → e)
```

**前提可满足的部分.** `set`, `keep` 各自可满足 (只升: 一切分量一起升; 只留: 世界不动) 是 `NegGenFoldUpd.half₁R`, `half₁K` 在 `K₁` 上的同一件事, 本篇不重写. 两条同时成立的实例在 §4 (下标换成位置).

## §4 字面位置为下标: 合法升界存在且唯一

固定合法世界 $\omega$ 与合法高度 $L$. 成员是 $L$ 在 $\omega$ 里的字面第一位置 $(a, p)$, 键是高度 $a$, 世界只对位置给分量 (分量以证据为参数), 读数是那个分量. 律的定义域取一切成员对 (`Ev = ⊤`): 证据已经在下标里.

```agda
module Pos {S : KS} {ω : Wd S} {L : HB S} (lω : LgW S ω) (lL : LgB L) (Vp : Set) where
  PJ : Set
  PJ = Σ (HB S) (λ a → a ⊲[ ω ] L)

  posF : RaiseFrame
  posF = record
    { W = (a : HB S) → a ⊲[ ω ] L → Vp ; J = PJ ; Key = HB S ; V = Vp
    ; key = proj₁ ; obs = λ j w → w (proj₁ j) (proj₂ j) ; Ev = λ _ _ _ → ⊤ }

  posBare : Bare posF
  posBare w j j′ = tt

  -- 键在定义域里可判定 (bdec)
  pos-dec : ∀ (j j′ : PJ) → (proj₁ j′ ≡ proj₁ j) ⊎ ¬ (proj₁ j′ ≡ proj₁ j)
  pos-dec (a , p) (b , q) = bdec q p lω lL

  rsP : W posF → PJ → Vp → W posF
  rsP w (a , p) v b q = pick (bdec q p lω lL) v (w b q)

  setP : ∀ {w : W posF} (j j′ : PJ) v → proj₁ j′ ≡ proj₁ j → rsP w j v (proj₁ j′) (proj₂ j′) ≡ v
  setP (a , p) (b , q) v k with bdec q p lω lL
  ... | inj₁ _ = refl
  ... | inj₂ ne = ⊥-elim (ne k)

  keepP : ∀ {w : W posF} (j j′ : PJ) v → ¬ (proj₁ j′ ≡ proj₁ j) → rsP w j v (proj₁ j′) (proj₂ j′) ≡ w (proj₁ j′) (proj₂ j′)
  keepP (a , p) (b , q) v nk with bdec q p lω lL
  ... | inj₁ e = ⊥-elim (nk e)
  ... | inj₂ _ = refl

  posR : Raise posF
  posR = record
    { rs = rsP
    ; set = λ {w} {j} {j′} v _ k → setP {w} j j′ v k
    ; keep = λ {w} {j} {j′} v _ nk → keepP {w} j j′ v nk }

  -- 任一合法升界在读数上等于 posR
  pos-unique : (R : Raise posF) → ∀ w j j′ v → obs posF j′ (rs R w j v) ≡ rsP w j v (proj₁ j′) (proj₂ j′)
  pos-unique R w j j′ v = unique R posR v tt (pos-dec j j′)
```

**实例可满足.** `Pos` 的前提: 任一 `S`, 合法世界与合法高度. 例: `S₀`, 世界 `azero` (合法: `CumReadCF.Lg azero = ⊤`), $L = 0$.

```agda
posInst : Raise (Pos.posF {S₀} {azero} {hz} tt tt ℕ)
posInst = Pos.posR tt tt ℕ
```

## §5 结论 (按档)

- **[定理]** `ev→wdec`, `bare→wdec` (律推出键的弱判定, 对一切框架); `shape`, `unique`, `unique¬¬` (定义域里升界唯一, 是按判定的点更新); `bare→Sep`, **`sup-bare→Sep`** (`Lev` 的裸坐标积世界上的升界推出分离子); **`Pos.posR`**, `Pos.pos-dec`, **`Pos.pos-unique`**, `posInst` (字面位置为下标: 合法升界存在, 唯一).
- **[判断]** 推出的形状与 `ColimAIf.LevA`/`GWA` 相同; 剩下的自由度 (证据放种类还是世界; 跨级读数的搬运) 是需要新判据的地方.
