# 一般种类结构的折叠, 否定一路 (一): 并的世界里只升一个分量的界, 是分离子

> 不含记号. 入口 [NegGenFold](NegGenFold.lagda.md). 对着接口 [GenFoldIf](GenFoldIf.lagda.md) ("接口定稿 2026-11-05 16:59 (首次编译通过)", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP; 函数外延 `FE₀` (只对 $\mathbb N\to$ `H₀`, 来自 `ColimWNeg`) 只在两条条件定理里作前提, 标 "条件".
>
> 接口文件头 "为什么不撞 `no-wmatch`" 一段写了构造一路的第一个障碍 (判断): "并的世界是逐分量的积, 升高分量 $i$ 的界要对下标 $i$ 判定 '是不是这个分量' (函数更新); 下标是坐标 (`A`, `HB _`) 时判定不了, 这些种类只能有损地回灌 (`fbA κ = inj₂ tt`)". 本篇把它写成定理, 并划出它的范围.
>
> - **对象.** 接口的决定性实验对象 `K₁ = Kc 1` (§1), 与第 1 站下降的层所在的种类结构 `T₀ = Lev X₀` (§2; `Lev (B 1) = step T₀`, 所以第 1 站的 `DK` 取 $K=T_0$). 两者都是以高度 (`H₀`) 为下标的并. 下标取形如 `jx f = hl (0, f 0, f 1, …)` 的高度, 这一分量里有一份底种类 (坐标 `A`) 的拷贝 `κ₁ f` / `κj f`.
> - **点更新 `PtUpd`**: 给世界 $w$, 下标 $i$, 分量 $i$ 的新世界 $x$, 得到新世界; **升** (`raise`): 分量 $i$ 的种类在新世界里的界是 $x$ 给的; **留** (`keep`): 别的分量 $k\neq i$ 的种类的界不升 ($k$ 的界在新世界里 ⇒ 在旧世界里). 这就是 `HtTowerFTree.nκ` 的 "$A$ 升高, 高度分量 `proj₂ W` 不动" 推广到并.
> - **`upd₁-sep`, `updT-sep` (定理)**: `PtUpd` ⇒ 分离子 (对一切 $\alpha:\mathbb N\to$ `Bool`, $\alpha$ 全假, 或两个下标 `jx (fα α)`, `jx fω` 不相等). **`upd₁→WLPO`, `updT→WLPO` (条件 `FE₀`)**. 证明只用到更弱的 `PtUpdB` (只对 `jx f` 分量的那一份底拷贝, 新界是一个 `A` 值): 在全 $0$ 的世界里把分量 `jx f` 的底界升到 $1$, 看分量 `jx f′` 的底界是不是 $0$ (`A` 的构造子, 可判定): 是 $0$ 则两下标不等 (由 "升"), 不是 $0$ 则两下标不能不等 (由 "留").
> - **两半各自可满足 (`half₁R`, `half₁K`, `halfTR`, `halfTK`)**: 只要 "升", 取 "把每个分量里的每份底拷贝都换成新界" (对层号结构递归, 不判定下标); 只要 "留", 取世界不动. **下标可判定时两半同时成立 (`upd∘`, `raise∘`, `keep∘`)**: `K₁` 的分量 `inj₁ tt` (旧站) 是模式, 点更新就是按模式写的函数.
>
> **为什么构造一路需要这条律.** 接口的回灌只有 `FBA` (`rs≤`, `rsLg`, `tp-rs`), 不含 "留"; 但接口文件头说有内容的回灌要 "升高分量 $i$ 的界" 而对 $i$ 判定, 即本篇的 `PtUpd`; `HtTowerFTree` 的两种种类的闭包 (`nκ` 只升 `A`, `nμ` 只升高度分量) 都是 "升一个, 留其余" 的形状, 两种种类时世界是积 `A × H₀`, 留其余是配对, 不判定. 推广到并, 留其余就要点更新.
>
> **只否定什么.** 只否定: 在 `K₁` (与 `T₀`) 的世界上, 一个**对一切**世界, 一切形如 `jx f` 的下标一致的操作同时满足 "升" 与 "留" (那份底拷贝). **不否定**: 接口的 `FBA` 与 `GenK` (它们不要 "留", 有实例, 见 [NegGenFoldBlind](NegGenFoldBlind.lagda.md)); 下标可判定的分量上的点更新 (`upd∘`); 只升不留的回灌 (`half₁R`: 一切底拷贝一起升); 有损回灌 (`fbA κ = inj₂ tt`). 路线状态: 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegGenFoldUpd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.HtTowerNStage using (dWLev)
open import OCF.Align.ColimWNeg using (WLPO; FE₀)
open import OCF.Align.LvKtIf using (Kc; FN; injL)
open import OCF.Align.NegDnFoldCopy using (X₀; T₀)
open import OCF.Align.GenFoldIf using (K₁)
```

## §0 下标的形状与分离子的输入

`jx f` 是第 0 项为 $0$ 的 ℕ-极限; 它的 `Lev` 的第 0 个分量是 `Lev hz = S₀`, 那里的种类 `tt` 就是一份底种类 (坐标 `A`). `jx` 是单射 (`jx-inj`, 不用外延: 从 `hl g` 取回 `g`, 再去掉第 0 项).

```agda
jx : (ℕ → H₀) → H₀
jx f = hl (λ { zero → hz ; (suc n) → f n })

unhl : H₀ → ℕ → H₀
unhl (hl g) = g
unhl _ = λ _ → hz

jx-inj : ∀ {f f′} → jx f′ ≡ jx f → f′ ≡ f
jx-inj e = cong (λ x n → unhl x (suc n)) e

bit : Bool → H₀
bit true = hs hz
bit false = hz

fα : (ℕ → Bool) → ℕ → H₀
fα α n = bit (α n)

fω : ℕ → H₀
fω _ = hz

bit≡ : ∀ b → bit b ≡ hz → b ≡ false
bit≡ false _ = refl
bit≡ true ()

eq→F : ∀ α → jx (fα α) ≡ jx fω → ∀ n → α n ≡ false
eq→F α e n = bit≡ (α n) (cong (λ f → f n) (jx-inj e))

F→eq : FE₀ → ∀ α → (∀ n → α n ≡ false) → jx (fα α) ≡ jx fω
F→eq fe α h = cong jx (fe (fα α) fω (λ n → cong bit (h n)))

Sep : Set
Sep = ∀ (α : ℕ → Bool) → (∀ n → α n ≡ false) ⊎ ¬ (jx (fα α) ≡ jx fω)

-- 弱判定 ⇒ 分离子
WDec : Set
WDec = ∀ f f′ → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)

wdec→sep : WDec → Sep
wdec→sep D α with D fω (fα α)
... | inj₁ ne = inj₂ ne
... | inj₂ nn = inj₁ nnF
  where
  nnF : ∀ n → α n ≡ false
  nnF n with α n in eq
  ... | false = refl
  ... | true = ⊥-elim (nn (λ e → t≢f (trans (sym eq) (eq→F α e n))))
    where t≢f : ¬ (true ≡ false)
          t≢f ()

sep→WLPO : FE₀ → Sep → WLPO
sep→WLPO fe S α with S α
... | inj₁ h = inj₁ h
... | inj₂ ne = inj₂ (λ h → ne (F→eq fe α h))

-- A 的构造子: 是不是 0 可判定; 1 不在 0 之下
not⊲0 : ∀ {v} → (v ≡ azero → ⊥) → ¬ (v ⊲ azero)
not⊲0 nz C.self = nz refl
```

## §1 `K₁ = Kc 1`: 读回分量 `inj₂ c` 的下标是高度

`Wd K₁` 是对下标 `⊤ ⊎ H₀` 的依赖函数; 分量 `inj₂ c` 的世界是 `Wd (Lev c)`. `κ₁ f` 是分量 `inj₂ (jx f)` 里第 0 个子分量的底种类.

```agda
κ₁ : (ℕ → H₀) → K K₁
κ₁ f = inj₂ (jx f) , (0 , tt)

E-κ₁ : ∀ f → E K₁ (κ₁ f) ≡ A
E-κ₁ f = refl

record PtUpd₁ : Set where
  field
    upd   : Wd K₁ → (i : ⊤ ⊎ H₀) → Wd (FN S₀ i) → Wd K₁
    raise : ∀ w i x (κ : K (FN S₀ i)) {c} → Bd (FN S₀ i) κ c x → Bd K₁ (i , κ) c (upd w i x)
    keep  : ∀ w i x k (κ : K (FN S₀ k)) → ¬ (k ≡ i) → ∀ {c} → Bd K₁ (k , κ) c (upd w i x) → Bd K₁ (k , κ) c w

-- 只对 jx f 分量的那一份底拷贝 (更弱的前提)
record PtUpdB₁ : Set where
  field
    updB   : Wd K₁ → (ℕ → H₀) → A → Wd K₁
    raiseB : ∀ w f x {c} → c ⊲ x → Bd K₁ (κ₁ f) c (updB w f x)
    keepB  : ∀ w f x f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd K₁ (κ₁ f′) c (updB w f x) → Bd K₁ (κ₁ f′) c w

z₁ : Wd K₁
z₁ (inj₁ tt) = azero
z₁ (inj₂ c) = dWLev c

xA₁ : ∀ f → A → Wd (Lev (jx f))
xA₁ f x zero = x
xA₁ f x (suc n) = dWLev (f n)

inj₂-inj : ∀ {c c′ : H₀} → _≡_ {A = ⊤ ⊎ H₀} (inj₂ c′) (inj₂ c) → c′ ≡ c
inj₂-inj refl = refl

full→B₁ : PtUpd₁ → PtUpdB₁
full→B₁ P = record
  { updB = λ w f x → upd w (inj₂ (jx f)) (xA₁ f x)
  ; raiseB = λ w f x p → raise w (inj₂ (jx f)) (xA₁ f x) (0 , tt) p
  ; keepB = λ w f x f′ ne b → keep w (inj₂ (jx f)) (xA₁ f x) (inj₂ (jx f′)) (0 , tt) (λ e → ne (inj₂-inj e)) b }
  where open PtUpd₁ P

wdec₁ : PtUpdB₁ → WDec
wdec₁ P f f′ = go (updB z₁ f (asuc azero) (inj₂ (jx f′)) 0) refl
  where
  open PtUpdB₁ P
  r1 : Bd K₁ (κ₁ f) (asuc azero) (updB z₁ f (asuc azero))
  r1 = raiseB z₁ f (asuc azero) C.self
  go : ∀ v → updB z₁ f (asuc azero) (inj₂ (jx f′)) 0 ≡ v → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
  go azero eq = inj₁ (λ e → h₀ (subst (asuc azero ⊲_) eq (h e)))
    where
    h₀ : ¬ (asuc azero ⊲ azero)
    h₀ ()
    h : jx f′ ≡ jx f → asuc azero ⊲ updB z₁ f (asuc azero) (inj₂ (jx f′)) 0
    h e = subst (λ g → Bd K₁ (κ₁ g) (asuc azero) (updB z₁ f (asuc azero))) (sym (jx-inj e)) r1
  go (asuc v) eq = inj₂ (λ ne → not⊲0 (λ ()) (keepB z₁ f (asuc azero) f′ ne (subst (asuc v ⊲_) (sym eq) C.self)))
  go (alim g) eq = inj₂ (λ ne → not⊲0 (λ ()) (keepB z₁ f (asuc azero) f′ ne (subst (alim g ⊲_) (sym eq) C.self)))

updB₁-sep : PtUpdB₁ → Sep
updB₁-sep P = wdec→sep (wdec₁ P)

upd₁-sep : PtUpd₁ → Sep
upd₁-sep P = updB₁-sep (full→B₁ P)

upd₁→WLPO : FE₀ → PtUpd₁ → WLPO
upd₁→WLPO fe P = sep→WLPO fe (upd₁-sep P)
```

**两半各自可满足.** 只升: 每个读回分量里的每一份底拷贝都换成新界 $x$ (`rB`, 对层号结构递归, 不看下标是哪一个). 只留: 世界不动.

```agda
rB : ∀ {S : KS} (c : HB S) → A → Wd (Lev c) → Wd (Lev c)
rB hz x w = x
rB (hs c) x (w , β) = rB c x w , β
rB (hl f) x w = λ n → rB (f n) x (w n)
rB (hΩ κ g) x w = λ e → rB (g e) x (w e)

upAll₁ : Wd K₁ → (ℕ → H₀) → A → Wd K₁
upAll₁ w f x (inj₁ tt) = w (inj₁ tt)
upAll₁ w f x (inj₂ c) = rB c x (w (inj₂ c))

half₁R : ∀ w f x {c} → c ⊲ x → Bd K₁ (κ₁ f) c (upAll₁ w f x)
half₁R w f x p = p

stay₁ : Wd K₁ → (ℕ → H₀) → A → Wd K₁
stay₁ w f x = w

half₁K : ∀ w f x f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd K₁ (κ₁ f′) c (stay₁ w f x) → Bd K₁ (κ₁ f′) c w
half₁K w f x f′ ne b = b

-- 只升的那一半把别的分量也升了: 换一个下标, 底拷贝同样在新界之下
upAll₁-moves : ∀ w f x f′ {c} → c ⊲ x → Bd K₁ (κ₁ f′) c (upAll₁ w f x)
upAll₁-moves w f x f′ p = p
```

**下标可判定时两半同时成立.** 分量 `inj₁ tt` (旧站 `S₀`) 是模式: 升它, 留一切读回分量.

```agda
upd∘ : Wd K₁ → A → Wd K₁
upd∘ w x (inj₁ tt) = x
upd∘ w x (inj₂ c) = w (inj₂ c)

raise∘ : ∀ w x {c} → c ⊲ x → Bd K₁ (inj₁ tt , tt) c (upd∘ w x)
raise∘ w x p = p

keep∘ : ∀ w x c (κ : K (Lev c)) {e} → Bd K₁ (inj₂ c , κ) e (upd∘ w x) → Bd K₁ (inj₂ c , κ) e w
keep∘ w x c κ b = b
```

## §2 `T₀ = Lev X₀`: 第 1 站下降的层所在的种类结构

`X₀ = One.X₁` (`NegDnFoldCopy`), `Lev X₀` 是对坐标 $y$ : `H₀` 的并, 分量 $y$ 是 `Fc y = Lev (1 ⊞ injL 1 (up y))`. 分量 `jx f` 是对 ℕ 的并, 它的第 0 个子分量是 `Lev 1 = step S₀`, 其旧种类 `inj₁ tt` 是一份底拷贝 (`κj f`, 坐标 `A`, 界是世界的 `A`-分量).

```agda
Fc : H₀ → KS
Fc y = Lev (hs hz ⊞ injL {S₀} (hs hz) (up {S₀} y))

Wd-T₀ : Wd T₀ ≡ ((y : H₀) → Wd (Fc y))
Wd-T₀ = refl

κj : (ℕ → H₀) → K T₀
κj f = jx f , (0 , inj₁ tt)

E-κj : ∀ f → E T₀ (κj f) ≡ A
E-κj f = refl

record PtUpdT : Set where
  field
    upd   : Wd T₀ → (i : H₀) → Wd (Fc i) → Wd T₀
    raise : ∀ w i x (κ : K (Fc i)) {c} → Bd (Fc i) κ c x → Bd T₀ (i , κ) c (upd w i x)
    keep  : ∀ w i x k (κ : K (Fc k)) → ¬ (k ≡ i) → ∀ {c} → Bd T₀ (k , κ) c (upd w i x) → Bd T₀ (k , κ) c w

record PtUpdBT : Set where
  field
    updB   : Wd T₀ → (ℕ → H₀) → A → Wd T₀
    raiseB : ∀ w f x {c} → c ⊲ x → Bd T₀ (κj f) c (updB w f x)
    keepB  : ∀ w f x f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd T₀ (κj f′) c (updB w f x) → Bd T₀ (κj f′) c w

zT : Wd T₀
zT y = dWLev (hs hz ⊞ injL {S₀} (hs hz) (up {S₀} y))

xAT : ∀ f → A → Wd (Fc (jx f))
xAT f x zero = x , hz
xAT f x (suc n) = zT (jx f) (suc n)

full→BT : PtUpdT → PtUpdBT
full→BT P = record
  { updB = λ w f x → upd w (jx f) (xAT f x)
  ; raiseB = λ w f x p → raise w (jx f) (xAT f x) (0 , inj₁ tt) p
  ; keepB = λ w f x f′ ne b → keep w (jx f) (xAT f x) (jx f′) (0 , inj₁ tt) ne b }
  where open PtUpdT P

wdecT : PtUpdBT → WDec
wdecT P f f′ = go (proj₁ (updB zT f (asuc azero) (jx f′) 0)) refl
  where
  open PtUpdBT P
  r1 : Bd T₀ (κj f) (asuc azero) (updB zT f (asuc azero))
  r1 = raiseB zT f (asuc azero) C.self
  go : ∀ v → proj₁ (updB zT f (asuc azero) (jx f′) 0) ≡ v → ¬ (jx f′ ≡ jx f) ⊎ ¬ ¬ (jx f′ ≡ jx f)
  go azero eq = inj₁ (λ e → h₀ (subst (asuc azero ⊲_) eq (h e)))
    where
    h₀ : ¬ (asuc azero ⊲ azero)
    h₀ ()
    h : jx f′ ≡ jx f → asuc azero ⊲ proj₁ (updB zT f (asuc azero) (jx f′) 0)
    h e = subst (λ g → Bd T₀ (κj g) (asuc azero) (updB zT f (asuc azero))) (sym (jx-inj e)) r1
  go (asuc v) eq = inj₂ (λ ne → not⊲0 (λ ()) (keepB zT f (asuc azero) f′ ne (subst (asuc v ⊲_) (sym eq) C.self)))
  go (alim g) eq = inj₂ (λ ne → not⊲0 (λ ()) (keepB zT f (asuc azero) f′ ne (subst (alim g ⊲_) (sym eq) C.self)))

updT-sep : PtUpdT → Sep
updT-sep P = wdec→sep (wdecT (full→BT P))

updT→WLPO : FE₀ → PtUpdT → WLPO
updT→WLPO fe P = sep→WLPO fe (updT-sep P)

-- 两半各自可满足
upAllT : Wd T₀ → (ℕ → H₀) → A → Wd T₀
upAllT w f x y = rB (hs hz ⊞ injL {S₀} (hs hz) (up {S₀} y)) x (w y)

halfTR : ∀ w f x {c} → c ⊲ x → Bd T₀ (κj f) c (upAllT w f x)
halfTR w f x p = p

stayT : Wd T₀ → (ℕ → H₀) → A → Wd T₀
stayT w f x = w

halfTK : ∀ w f x f′ → ¬ (jx f′ ≡ jx f) → ∀ {c} → Bd T₀ (κj f′) c (stayT w f x) → Bd T₀ (κj f′) c w
halfTK w f x f′ ne b = b
```

## §3 结论 (按档)

- **[定理]** `jx-inj`, `eq→F`, `wdec→sep` (弱判定 ⇒ 分离子); **[条件 `FE₀`]** `F→eq`, `sep→WLPO`.
- **[定理]** **`upd₁-sep`**, `updB₁-sep`, `full→B₁` (`K₁`); **`updT-sep`**, `full→BT` (`T₀`): 点更新 (升 + 留) ⇒ 分离子. **[条件 `FE₀`]** **`upd₁→WLPO`**, `updT→WLPO`.
- **[定理, 前提实例]** `half₁R`, `half₁K`, `halfTR`, `halfTK` (两半各自可满足; 只升的那一半 `upAll₁` 把别的分量的底拷贝也升了, `upAll₁-moves`); `upd∘`, `raise∘`, `keep∘` (下标可判定的分量上两半同时成立). 分离子 `Sep` 本身经典地成立 (判断), `FE₀` 在 Agda 里证不出也否证不了 (与 `ColimWNeg`, `NegDnFoldAdm` 同档).
- **[判断]** 这条定理落在**律的定义域**上 (手册 §3.1): "留" 比较的是两个**裸下标** $k$, $i$ (`¬ (k ≡ i)`), 没有公共上界. 接口的 `FBA` 不比较下标, 所以不撞它. 出路 (判断): 回灌升高时连同别的分量一起升 (`upAll₁` 的形状), 或者只在可判定的分量上点更新 (`upd∘`), 或者有损.
