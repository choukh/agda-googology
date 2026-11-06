# 分层互递归塔, 否定一路 (四): 深种类上的边界, 级的拷贝不被认成同一个

> 不含记号. 入口 [NegStratTw](NegStratTw.lagda.md). 只读导入构造一路的 [StratTwTw](StratTwTw.lagda.md) (19:20 版). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` 只在一条条件定理 (`updD→WLPO`) 里作前提.
>
> **§1 对一切 `S` 的引理: 级的和里的拷贝.** `Lev (a ⊞ b)` 里有 `Lev a` 的每个种类的一份拷贝 (`kup a b κ`), 坐标来回 (`cE`, `cE⁻`, `cE-cE⁻`), 世界投影 (`wpr`) 与插入 (`wins`, `wpr-wins`), 界双向搬 (`bd→`, `bd←`), 基世界投到基世界 (`w₀-pr`). 都对 $b$ 的构造子递归, 不判定.
>
> **§2 实例里的拷贝.** 构造一路的级 $X_1=\mathrm{h\Omega}\,(\mathrm{r},\mathrm{new})\,(c\mapsto a_1\boxplus b_1\,c)$ (`X1≡`, `refl`), $a_1=\mathrm{hs}(\iota_{\mathrm l}\,1)$, 下标 $c$ 取遍 `HB (Lev X₀) = HB (step S₀)`. 于是分量 2 里有一族深种类 `κd c = (2 , inj₁ (c , kup a₁ (b₁ c) new))`, **每个 $c$ 一份**, 坐标都转成 `HB (step S₀)`, 与头种类 `hd 0 = (1 , new)` 的坐标同一类型: 它们是第 1 站的级 ($X_0=1$) 的新种类在第 2 站的级里的拷贝 (第 2 站的级读回经它们看第 1 级的高度).
>
> 1. **`no-wmatch-cp` (定理).** 对任一 $c$: 没有世界映射 `wm : Wd U → Wd (C 1)` 同时把 `κd c` 的界送进头种类的界, 又把头种类的界送回 `hd 0` 的界 (对照 `HtTowerNStage.no-wmatch`, `NegKindLvW.no-wmatchΛH`). 两个前提各自可满足 (`sat-hd`, `sat-cp`). 读法: `KT 0` 升 `hd 0` 的界, 这一份回灌不被拷贝 `κd c` 看见; 拷贝的界由世界的第 2 个分量单独给.
> 2. **`updD-sep` (定理, 否定) / `updD→WLPO` (条件 `FE₀`).** 把 `KT s` 的点更新推广到这一族拷贝: 对一切世界与一切 $c$ 一致地 "把 `κd c` 的界升到 $1$ 以上, 不动 `κd c′` ($c'\ne c$) 的界", 推出分离子 `Sep` (同 `NegGenFoldUpd.upd₁-sep`; 下标 $c$ 含函数, 用 `up (jx f)` 编码). 两半各自可满足 (`halfR`: 一次升整族; `halfK`: 不动).
>
> **只否定什么.** 只否定: 在 `StratTwTw` 的总结构 `U` 的分量 2 里, 以 `HB (step S₀)` 的坐标为下标的这一族拷贝上, 一致的 "升一份留别份" (分离子), 与一个同时双向保 `κd c` 与 `hd 0` 的界的世界映射. **不否定**: 构造一路的 `KT` (ℕ 下标点更新, 可判定); 只升不留 (`halfR`, 它把整族一起升); 别的回灌方式 (例如折叠自己的读回升深种类的界; 未构造, 未否定). 推广到一切 $s$ (分量 $s+2$ 里第 $s+1$ 站级的拷贝) 是判断: 同一论证要 $X_{s+1}$ 的头 (`X-head`, 已是定理) 与 `kup`, 写法相同, 没写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegStratTwDeep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.GenFoldIf using (GenK; w₀)
open import OCF.Align.GenFoldInst using (genLev; upd)
open import OCF.Align.ColimWNeg using (WLPO; FE₀)
open import OCF.Align.NegGenFoldUpd using (jx; Sep; sep→WLPO; fα; fω; bit)
open import OCF.Align.NegKindLvUpd using (one⊀z)
open import OCF.Align.KindLvEv using (evK)
open import OCF.Align.StratTwTw using (P; X; C; U; QF; st; hd; GU)
```

## §1 级的和里的拷贝 (对一切 `S`)

```agda
module Cp {S : KS} (a : HB S) where
  kup : ∀ b → K (Lev a) → K (Lev (a ⊞ b))
  kup hz κ = κ
  kup (hs b) κ = inj₁ (kup b κ)
  kup (hl f) κ = 0 , kup (f 0) κ
  kup (hΩ κ′ g) κ = bot S κ′ , kup (g (bot S κ′)) κ

  cE : ∀ b κ → E (Lev (a ⊞ b)) (kup b κ) → E (Lev a) κ
  cE hz κ e = e
  cE (hs b) κ e = cE b κ e
  cE (hl f) κ e = cE (f 0) κ e
  cE (hΩ κ′ g) κ e = cE (g (bot S κ′)) κ e

  cE⁻ : ∀ b κ → E (Lev a) κ → E (Lev (a ⊞ b)) (kup b κ)
  cE⁻ hz κ x = x
  cE⁻ (hs b) κ x = cE⁻ b κ x
  cE⁻ (hl f) κ x = cE⁻ (f 0) κ x
  cE⁻ (hΩ κ′ g) κ x = cE⁻ (g (bot S κ′)) κ x

  cE-cE⁻ : ∀ b κ x → cE b κ (cE⁻ b κ x) ≡ x
  cE-cE⁻ hz κ x = refl
  cE-cE⁻ (hs b) κ x = cE-cE⁻ b κ x
  cE-cE⁻ (hl f) κ x = cE-cE⁻ (f 0) κ x
  cE-cE⁻ (hΩ κ′ g) κ x = cE-cE⁻ (g (bot S κ′)) κ x

  wpr : ∀ b → Wd (Lev (a ⊞ b)) → Wd (Lev a)
  wpr hz w = w
  wpr (hs b) w = wpr b (proj₁ w)
  wpr (hl f) w = wpr (f 0) (w 0)
  wpr (hΩ κ′ g) w = wpr (g (bot S κ′)) (w (bot S κ′))

  wins : ∀ b → Wd (Lev a) → Wd (Lev (a ⊞ b))
  wins hz w = w
  wins (hs b) w = wins b w , hz
  wins (hl f) w = λ n → wins (f n) w
  wins (hΩ κ′ g) w = λ c → wins (g c) w

  wpr-wins : ∀ b w → wpr b (wins b w) ≡ w
  wpr-wins hz w = refl
  wpr-wins (hs b) w = wpr-wins b w
  wpr-wins (hl f) w = wpr-wins (f 0) w
  wpr-wins (hΩ κ′ g) w = wpr-wins (g (bot S κ′)) w

  bd→ : ∀ b κ {e w} → Bd (Lev (a ⊞ b)) (kup b κ) e w → Bd (Lev a) κ (cE b κ e) (wpr b w)
  bd→ hz κ p = p
  bd→ (hs b) κ p = bd→ b κ p
  bd→ (hl f) κ p = bd→ (f 0) κ p
  bd→ (hΩ κ′ g) κ p = bd→ (g (bot S κ′)) κ p

  bd← : ∀ b κ {x w} → Bd (Lev a) κ x (wpr b w) → Bd (Lev (a ⊞ b)) (kup b κ) (cE⁻ b κ x) w
  bd← hz κ p = p
  bd← (hs b) κ p = bd← b κ p
  bd← (hl f) κ p = bd← (f 0) κ p
  bd← (hΩ κ′ g) κ p = bd← (g (bot S κ′)) κ p

  w₀-pr : ∀ b → wpr b (w₀ (genLev (a ⊞ b))) ≡ w₀ (genLev a)
  w₀-pr hz = refl
  w₀-pr (hs b) = w₀-pr b
  w₀-pr (hl f) = w₀-pr (f 0)
  w₀-pr (hΩ κ′ g) = w₀-pr (g (bot S κ′))
```

## §2 实例里的一族拷贝

```agda
a₁ : HB (P 1)
a₁ = hs (ι {⊤ ⊎ ⊤} {QF (st 0)} (inj₁ tt) (hs hz))

unΩ : ∀ {T : KS} → HB (step T) → HB T → HB (step T)
unΩ (hΩ (inj₂ _) h) = h
unΩ _ = λ _ → hz

b₁ : HB (step S₀) → HB (P 1)
b₁ c = ι {⊤ ⊎ ⊤} {QF (st 0)} (inj₂ tt) (unΩ (evK (X 0)) c)

X1≡ : X 1 ≡ hΩ (inj₂ tt , inj₂ tt) (λ c → a₁ ⊞ b₁ c)
X1≡ = refl

open Cp a₁

κd : HB (step S₀) → K U
κd c = 2 , inj₁ (c , kup (b₁ c) (inj₂ tt))

-- 拷贝的界所在的槽
slot : Wd U → HB (step S₀) → HB (step S₀)
slot w c = proj₂ (wpr (b₁ c) (proj₁ (w 2) c))

w0 : Wd U
w0 = w₀ GU

slot0 : ∀ c → slot w0 c ≡ hz
slot0 c = cong proj₂ (w₀-pr (b₁ c))

one : ∀ c → E U (κd c)
one c = cE⁻ (b₁ c) (inj₂ tt) (hs hz)
```

## §3 一致的 "升一份留别份" ⇒ 分离子

```agda
record PtUpdD : Set where
  field
    updD   : Wd U → HB (step S₀) → Wd U
    raiseD : ∀ w c → Bd U (κd c) (one c) (updD w c)
    keepD  : ∀ w c c′ → ¬ (c′ ≡ c) → ∀ {e} → Bd U (κd c′) e (updD w c) → Bd U (κd c′) e w
open PtUpdD public

isZ : ∀ {T : KS} (x : HB T) → (x ≡ hz) ⊎ ¬ (x ≡ hz)
isZ hz = inj₁ refl
isZ (hs x) = inj₂ (λ ())
isZ (hl f) = inj₂ (λ ())
isZ (hΩ κ g) = inj₂ (λ ())

⊲hz : ∀ {T : KS} {x : HB T} {w} → x ⊲[ w ] hz → x ≡ hz
⊲hz hself = refl

wv : Wd U → HB (step S₀) → Wd (Lev a₁)
wv w c = wpr (b₁ c) (proj₁ (w 2) c)

wdecD : PtUpdD → ∀ c c′ → ¬ (c′ ≡ c) ⊎ ¬ ¬ (c′ ≡ c)
wdecD Pu c c′ with isZ (slot (updD Pu w0 c) c′)
... | inj₁ z = inj₁ λ eq → one⊀z (subst (λ y → hs hz ⊲[ proj₁ (wv W c′) ] y) z (t′ eq))
  where
  W = updD Pu w0 c
  r : c′ ≡ c → Bd U (κd c′) (one c′) W
  r eq = subst (λ y → Bd U (κd y) (one y) W) (sym eq) (raiseD Pu w0 c)
  t : c′ ≡ c → cE (b₁ c′) (inj₂ tt) (one c′) ⊲[ proj₁ (wv W c′) ] slot W c′
  t eq = bd→ (b₁ c′) (inj₂ tt) {e = one c′} {w = proj₁ (W 2) c′} (r eq)
  t′ : c′ ≡ c → hs hz ⊲[ proj₁ (wv W c′) ] slot W c′
  t′ eq = subst (λ x → x ⊲[ proj₁ (wv W c′) ] slot W c′) (cE-cE⁻ (b₁ c′) (inj₂ tt) (hs hz)) (t eq)
... | inj₂ nz = inj₂ λ ne → nz (⊲hz (subst (λ y → x ⊲[ proj₁ (wv w0 c′) ] y) (slot0 c′) (t′ ne)))
  where
  W = updD Pu w0 c
  x = slot W c′
  q : Bd U (κd c′) (cE⁻ (b₁ c′) (inj₂ tt) x) W
  q = bd← (b₁ c′) (inj₂ tt) {x = x} {w = proj₁ (W 2) c′} hself
  t : ¬ (c′ ≡ c) → cE (b₁ c′) (inj₂ tt) (cE⁻ (b₁ c′) (inj₂ tt) x) ⊲[ proj₁ (wv w0 c′) ] slot w0 c′
  t ne = bd→ (b₁ c′) (inj₂ tt) {e = cE⁻ (b₁ c′) (inj₂ tt) x} {w = proj₁ (w0 2) c′} (keepD Pu w0 c c′ ne q)
  t′ : ¬ (c′ ≡ c) → x ⊲[ proj₁ (wv w0 c′) ] slot w0 c′
  t′ ne = subst (λ y → y ⊲[ proj₁ (wv w0 c′) ] slot w0 c′) (cE-cE⁻ (b₁ c′) (inj₂ tt) x) (t ne)
```

编码: $c=\mathrm{up}(\mathrm{jx}\,f)$ (`HB (step S₀)` 里).

```agda
atU : HB (step S₀) → ℕ → HB (step S₀)
atU (hl F) n = F n
atU _ n = hz

lemB : ∀ b → up {S₀} (bit b) ≡ hz → b ≡ false
lemB false _ = refl
lemB true ()

nnB : ∀ b → ¬ ¬ (b ≡ false) → b ≡ false
nnB false _ = refl
nnB true nn = ⊥-elim (nn (λ ()))

updD-sep : PtUpdD → Sep
updD-sep Pu α with wdecD Pu (up (jx fω)) (up (jx (fα α)))
... | inj₁ ne = inj₂ (λ e → ne (cong up e))
... | inj₂ nn = inj₁ (λ n → nnB (α n) (λ k → nn (λ e → k (lemB (α n) (cong (λ x → atU x (suc n)) e)))))

updD→WLPO : FE₀ → PtUpdD → WLPO
updD→WLPO fe Pu = sep→WLPO fe (updD-sep Pu)
```

两半各自可满足. 只留: 世界不动. 只升: 把分量 2 整个换成 "每个 $c$ 的拷贝的界都是 $1$" (`wins`).

```agda
halfK : Σ (Wd U → HB (step S₀) → Wd U) (λ u → ∀ w c c′ → ¬ (c′ ≡ c) → ∀ {e} → Bd U (κd c′) e (u w c) → Bd U (κd c′) e w)
halfK = (λ w c → w) , (λ w c c′ ne b → b)

wsel : Wd (Lev (ι {⊤ ⊎ ⊤} {QF (st 0)} (inj₁ tt) (hs hz)))
wsel = azero , hz

raised : Wd (C 2)
raised = (λ c → wins (b₁ c) (wsel , hs hz)) , hz

updR : Wd U → HB (step S₀) → Wd U
updR w c = upd {λ m → Wd (C m)} w 2 raised

halfR : ∀ w c → Bd U (κd c) (one c) (updR w c)
halfR w c = bd← (b₁ c) (inj₂ tt) (subst (λ v → Bd (Lev a₁) (inj₂ tt) (hs hz) v) (sym (wpr-wins (b₁ c) (wsel , hs hz))) hself)

-- 只升的一半把别的拷贝也升了
halfR-moves : ∀ w c c′ → Bd U (κd c′) (one c′) (updR w c)
halfR-moves w c c′ = halfR w c′
```

## §4 拷贝与头种类: 没有同时保两份界的世界映射

`hd 0 = (1 , inj₂ tt)` 的坐标 `HB (Lev X₀) = HB (step S₀)`, 世界 `Wd (C 1) = Wd (step (step S₀))`, 与 `Lev a₁` 的世界同一类型.

```agda
w⋆ : HB (step S₀) → Wd U
w⋆ c = updR w0 c

no-wmatch-cp : ∀ c (wm : Wd U → Wd (C 1)) →
  (∀ {e w} → Bd U (κd c) e w → Bd (C 1) (inj₂ tt) (cE (b₁ c) (inj₂ tt) e) (wm w)) →
  (∀ {x w} → Bd (C 1) (inj₂ tt) x (wm w) → Bd U (hd 0) x w) → ⊥
no-wmatch-cp c wm h1 h0 =
  one⊀z (h0 (subst (λ x → Bd (C 1) (inj₂ tt) x (wm (w⋆ c))) (cE-cE⁻ (b₁ c) (inj₂ tt) (hs hz)) (h1 (halfR w0 c))))

sat-hd : Σ (Wd U → Wd (C 1)) (λ wm →
  (∀ {x w} → Bd U (hd 0) x w → Bd (C 1) (inj₂ tt) x (wm w)) × (∀ {x w} → Bd (C 1) (inj₂ tt) x (wm w) → Bd U (hd 0) x w))
sat-hd = (λ w → w 1) , (λ b → b) , (λ b → b)

sat-cp : ∀ c → Σ (Wd U → Wd (C 1)) (λ wm →
  (∀ {e w} → Bd U (κd c) e w → Bd (C 1) (inj₂ tt) (cE (b₁ c) (inj₂ tt) e) (wm w)) ×
  (∀ {x w} → Bd (C 1) (inj₂ tt) x (wm w) → Bd U (κd c) (cE⁻ (b₁ c) (inj₂ tt) x) w))
sat-cp c = (λ w → wpr (b₁ c) (proj₁ (w 2) c)) , (λ b → bd→ (b₁ c) (inj₂ tt) b) , (λ b → bd← (b₁ c) (inj₂ tt) b)
```

## §5 结论 (按档)

- **[定理]** §1 的引理 (对一切 `S`); `X1≡`, `slot0`.
- **[定理, 否定]** **`updD-sep`**; **`no-wmatch-cp`**. **[条件 `FE₀`]** `updD→WLPO`.
- **[定理, 前提实例]** `halfK`, `halfR`, `halfR-moves`; `sat-hd`, `sat-cp`.
- **[判断]** 分层塔每站的级里, 低一站的级以 "每个坐标一份" 的拷贝出现 (以含函数的高度为下标). 头种类的回灌 (`KT`) 只升分量 $s+1$ 的第二分量; 拷贝的界在别的分量里, 不被认成同一个 (`no-wmatch-cp`); 逐份去升撞分离子 (`updD-sep`), 一起升 (`halfR`) 未被否定也未构造. 这与 KindLv 的墙同型 (`NegKindLvInst.updHΛ-sep`), 位置从 "后面各站的头" 移到了 "每站的级里的深种类".
