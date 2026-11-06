# 可入下标比较式更新的否定 (二): 四条更新律本身不推出禁忌

> 不含记号. 入口 [AdmWNeg](AdmWNeg.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 问题: 诊断 §5.1 第一条引理的四条律 (在 $(c_0,p_0)$ 处恰好接长 `at`; 严格在 $c_0$ 之下的分量不动 `below`; 世界只增 `≤w`; 保合法 `lg`) 本身是否已经推出相等的判定或别的禁忌?
>
> 回答: **在可数下标的实例上有反模型, 在诊断最小实例的下标 `HB S₀` 上也有.** 下标是 `A` 的层 (只有 $0$, 后继, ℕ-极限; 可数分支), 世界的分量以 (坐标, 可入证据) 为下标, 逐分量独立 (拷贝不认同, 正是 [AdmWNegCopy](AdmWNegCopy.lagda.md) 里 `copy→⊥` 杀掉的形状), 分量族是 `Lev` 形的 `G c = Lev (toH c)`, 增量沿路径用 `UniTrNeg.emb⊲` 嵌入. 更新 `raiseA` 用 `cmpF q p₀` 选择. 四条律都是定理 (`at`, `below`, `raise-≤`, `raise-lg`), `at` 对**一切**证据 $p_0$ 成立 (不只字面 `self`), 是命题相等, 证明用 `cmpF-diag` ($\mathrm{cmpF}\,p\,p \equiv \mathrm{inj}_1\,\mathrm{self}$, 对 $p$ 归纳, ℕ-极限处用 `tri-refl`).
>
> 所以 (定理档): 四条律与 "分量以证据为下标、逐分量独立" 同时可满足, 且有拷贝 (重复项的 ℕ-极限, `two-ev`). 拷贝墙不在更新律里, 在 `cmpK` 里 (`AdmWNegCopy.copy→⊥`).
>
> **两个下标.** §3–§5 下标是 `A` (只有 $0$, 后继, ℕ-极限; 可数分支). §6 换成诊断最小实例的下标 `HB S₀` (带 $\Omega$-节点), 分量族 `step (Lev (up c))` (接口 `AdmWIf` 的 `Slot`); 入口用它构造接口的 `RaiseIf.RaiseB`. `HB S₀` 上直接用 `cmpB` 时, `at` 卡在合法性证据里的 `mo` 在自反处给出的环 $g\,c\lhd g\,c$; §6 的 `cmpB₀` 在 $\Omega$-节点处 `cmpF` 返回字面 `self` 时不调用 `mo`, 所以 `at` 不需要 "环的证明唯一" (诊断 §3.3 义务 2 在 `at` 处由定义的写法绕开). §7 是有限测试.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmWNegLaws where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using ()
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; cmpF; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.UniTrNeg using (emb⊲; Lg-emb⊲)
open import OCF.Align.HtTowerNStage using (dWLev)
open import OCF.Align.AdmWNegCopy using (toH; toH-⊲; Lg-toH)
```

## §1 `cmpF` 在对角上给 `self`

```agda
tri-refl : ∀ n → <ᴺ-dec n n ≡ injᶜ refl
tri-refl zero = refl
tri-refl (suc n) rewrite tri-refl n = refl

cmpF-diag : ∀ {c b} (p : c ⊲ b) (lb : Lg b) → cmpF p p lb ≡ inj₁ C.self
cmpF-diag C.self lb = refl
cmpF-diag (C.suc p) lb = cmpF-diag p lb
cmpF-diag (C.lim n p) (st , w) rewrite tri-refl n = cmpF-diag p (w n)
```

## §2 `A` 上的严格子项, 反对称

```agda
infix 4 _<ᴬ_
data _<ᴬ_ : A → A → Set where
  <s₀ : ∀ {b} → b <ᴬ asuc b
  <s  : ∀ {a b} → a <ᴬ b → a <ᴬ asuc b
  <l₀ : ∀ {f} n → f n <ᴬ alim f
  <l  : ∀ {a f} n → a <ᴬ f n → a <ᴬ alim f

data Acc (x : A) : Set where
  acc : (∀ {y} → y <ᴬ x → Acc y) → Acc x

down : ∀ {x y} → Acc x → y <ᴬ x → Acc y
down (acc r) p = r p

wf : ∀ x → Acc x
wf azero = acc (λ ())
wf (asuc x) = acc (λ { <s₀ → wf x ; (<s p) → down (wf x) p })
wf (alim f) = acc (λ { (<l₀ n) → wf (f n) ; (<l n p) → down (wf (f n)) p })

irr : ∀ {x} → Acc x → ¬ (x <ᴬ x)
irr (acc r) p = irr (r p) p

<-tr : ∀ {a b c} → a <ᴬ b → b <ᴬ c → a <ᴬ c
<-tr p <s₀ = <s p
<-tr p (<s q) = <s (<-tr p q)
<-tr p (<l₀ n) = <l n p
<-tr p (<l n q) = <l n (<-tr p q)

toLt : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (a <ᴬ b)
toLt C.self = inj₁ refl
toLt (C.suc p) with toLt p
... | inj₁ refl = inj₂ <s₀
... | inj₂ q = inj₂ (<s q)
toLt (C.lim n p) with toLt p
... | inj₁ refl = inj₂ (<l₀ n)
... | inj₂ q = inj₂ (<l n q)

antisym : ∀ {a b} → a ⊲ b → b ⊲ a → a ≡ b
antisym p q with toLt p | toLt q
... | inj₁ e | _ = e
... | inj₂ _ | inj₁ e = sym e
... | inj₂ s | inj₂ t = ⊥-elim (irr (wf _) (<-tr s t))
```

## §3 世界: 分量以 (坐标, 证据) 为下标

分量族 `G c = Lev (toH c)`; 每个分量是 `step (G c)`, 被升高的槽是新种类的界 (类型 `HB (G c)`). 增量沿路径 $c_0\lhd c$ 用 `emb⊲ (toH-⊲ r)` 嵌入; 路径是 `self` 时定义上是恒等.

```agda
G : A → KS
G c = Lev {S₀} (toH c)

emb : ∀ {c₀ c} → c₀ ⊲ c → HB (G c₀) → HB (G c)
emb r x = emb⊲ {S₀} {w = azero} (toH-⊲ r) x

emb-self : ∀ {c} (x : HB (G c)) → emb C.self x ≡ x
emb-self x = refl

Lg-emb : ∀ {c₀ c} (r : c₀ ⊲ c) x → LgB x → LgB (emb r x)
Lg-emb r x l = Lg-emb⊲ {S₀} {w = azero} (toH-⊲ r) x l

Wd⋆ : Set
Wd⋆ = Σ A (λ b → (c : A) → c ⊲ b → Wd (step (G c)))

LgW⋆ : Wd⋆ → Set
LgW⋆ (b , v) = Lg b × (∀ c q → LgW (step (G c)) (v c q))

-- 世界序: 外层界只增, 分量逐个只增 (证据沿外层的增长搬运)
_≤⋆_ : Wd⋆ → Wd⋆ → Set
(b , v) ≤⋆ (b′ , v′) = Σ (b ⊲ b′) (λ s → ∀ c q → _≤w_ (step (G c)) (v c q) (v′ c (⊲-tr q s)))
```

## §4 比较式更新

`raiseA c₀ p₀ δ lb W`: 对每个分量 $(c, q)$ 看 `cmpF q p₀ lb`: $c_0 \lhd c$ 则沿返回的路径嵌入 $\delta$ 接长; $c\lhd c_0$ 则不动. 外层界不变.

```agda
upd : ∀ {c₀ b} (p₀ : c₀ ⊲ b) (δ : HB (G c₀)) (lb : Lg b) (c : A) (q : c ⊲ b) →
      Wd (step (G c)) → (c₀ ⊲ c) ⊎ (c ⊲ c₀) → Wd (step (G c))
upd p₀ δ lb c q u (inj₁ r) = proj₁ u , (proj₂ u ⊞ emb r δ)
upd p₀ δ lb c q u (inj₂ r) = u

raiseA : ∀ {c₀ b} (p₀ : c₀ ⊲ b) (δ : HB (G c₀)) (lb : Lg b) →
         ((c : A) → c ⊲ b → Wd (step (G c))) → (c : A) → c ⊲ b → Wd (step (G c))
raiseA p₀ δ lb v c q = upd p₀ δ lb c q (v c q) (cmpF q p₀ lb)
```

**`at`**: 在 $(c_0, p_0)$ 处, 槽恰好是 "旧界 ⊞ δ", 对一切证据 $p_0$.

```agda
at : ∀ {c₀ b} (p₀ : c₀ ⊲ b) δ lb v →
     raiseA p₀ δ lb v c₀ p₀ ≡ (proj₁ (v c₀ p₀) , (proj₂ (v c₀ p₀) ⊞ δ))
at p₀ δ lb v rewrite cmpF-diag p₀ lb = refl
```

**`below`**: 严格在 $c_0$ 之下 ($c\lhd c_0$, $c\not\equiv c_0$) 的分量不动, 对一切证据.

```agda
below-upd : ∀ {c₀ b} (p₀ : c₀ ⊲ b) δ lb c q u → c ⊲ c₀ → ¬ (c ≡ c₀) →
            (s : (c₀ ⊲ c) ⊎ (c ⊲ c₀)) → upd p₀ δ lb c q u s ≡ u
below-upd p₀ δ lb c q u r ne (inj₁ r′) = ⊥-elim (ne (antisym r r′))
below-upd p₀ δ lb c q u r ne (inj₂ _) = refl

below : ∀ {c₀ b} (p₀ : c₀ ⊲ b) δ lb v c q → c ⊲ c₀ → ¬ (c ≡ c₀) → raiseA p₀ δ lb v c q ≡ v c q
below p₀ δ lb v c q r ne = below-upd p₀ δ lb c q (v c q) r ne (cmpF q p₀ lb)
```

**`raise-≤`** 与 **`raise-lg`**: 世界只增, 保合法 ($\delta$ 合法时).

```agda
upd-≤ : ∀ {c₀ b} (p₀ : c₀ ⊲ b) δ lb c q u s → _≤w_ (step (G c)) u (upd p₀ δ lb c q u s)
upd-≤ p₀ δ lb c q u (inj₁ r) = ≤w-rf (G c) , ⊞-fst (proj₂ u) (emb r δ)
upd-≤ p₀ δ lb c q u (inj₂ r) = ≤w-rf (step (G c))

raise-≤ : ∀ {c₀ b} (p₀ : c₀ ⊲ b) δ lb v → (b , v) ≤⋆ (b , raiseA p₀ δ lb v)
raise-≤ p₀ δ lb v = C.self , (λ c q → upd-≤ p₀ δ lb c q (v c q) (cmpF q p₀ lb))

upd-lg : ∀ {c₀ b} (p₀ : c₀ ⊲ b) δ lb c q u s → LgB δ → LgW (step (G c)) u → LgW (step (G c)) (upd p₀ δ lb c q u s)
upd-lg p₀ δ lb c q u (inj₁ r) lδ (lw , lu) = lw , Lg-⊞ (proj₂ u) (emb r δ) lu (Lg-emb r δ lδ)
upd-lg p₀ δ lb c q u (inj₂ r) lδ l = l

raise-lg : ∀ {c₀ b} (p₀ : c₀ ⊲ b) δ (lb : Lg b) v → LgB δ → LgW⋆ (b , v) → LgW⋆ (b , raiseA p₀ δ lb v)
raise-lg p₀ δ lb v lδ (_ , lv) = lb , (λ c q → upd-lg p₀ δ lb c q (v c q) (cmpF q p₀ lb) lδ (lv c q))
```

## §5 这个实例里确有拷贝

界 $\lim_n 0$ 之下, 坐标 $0$ 有两个不同的证据; 它们是两个独立的分量 (`raiseA` 可以给它们不同的值, 世界类型不认同它们). 不同: 第一个构造子的 ℕ-下标不同.

```agda
b₀ : A
b₀ = alim (λ _ → azero)

lgb₀ : Lg b₀
lgb₀ = (λ n → C.self) , (λ n → tt)

ev₀ ev₁ : azero ⊲ b₀
ev₀ = C.lim 0 C.self
ev₁ = C.lim 1 C.self

idx : ∀ {c} → c ⊲ b₀ → ℕ
idx C.self = 0
idx (C.lim n _) = n

two-ev : ¬ (ev₀ ≡ ev₁)
two-ev e with cong idx e
... | ()

-- 世界里两个拷贝的分量可以不同: 一个合法世界, 分量按证据的下标取
vᵢ : (c : A) → c ⊲ b₀ → Wd (step (G c))
vᵢ c q = w (idx q)
  where
  wz : Wd (G c)
  wz = dWLev (toH {S₀} c)
  w : ℕ → Wd (step (G c))
  w zero = wz , hz
  w (suc _) = wz , hs hz
```

## §6 换成 `HB S₀` 下标: 同样的四条律

诊断最小实例的坐标是 `HB S₀` (外层 `step S₀`, 界 $c\lhd_{[a]} b$). 直接用 `cmpB` 时, `at` 要 `cmpB p p ≡ inj₁ hself`, 经 $\Omega$-节点时卡在 `mo lw e e r` (界的合法性证据里的函数). 出路: 选择用的比较 `cmpB₀` 只在 `S₀` 上写 (坐标是 `A`, 第一位置是 `A` 的 $\lhd$), 在 $\Omega$-节点处 `cmpF e e′` 返回字面 `self` 时**不调用** `mo`, 直接比较同一个分支里的两条路径. 它与 `cmpB` 同型, 一样停机. 于是对角上给 `hself` (`cmpB₀-diag`, 对路径归纳, 用 `tri-refl` 与 `cmpF-diag`), 不需要 "$t\lhd t$ 的证明唯一". 我起草时的判断 (`at` 要 `HB` 的 UIP) 由此作废: 义务 2 在 `at` 处由定义的写法绕开.

```agda
cmpB₀ : ∀ {a b L : HB S₀} {w} → a ⊲[ w ] L → b ⊲[ w ] L → Lg w → LgB L → (b ⊲[ w ] a) ⊎ (a ⊲[ w ] b)
cmpB₀ hself q lw l = inj₁ q
cmpB₀ p hself lw l = inj₂ p
cmpB₀ (hsuc p) (hsuc q) lw l = cmpB₀ p q lw l
cmpB₀ (hlim n p) (hlim m q) lw (st , l) with <ᴺ-dec n m
... | injᵃ n<m = cmpB₀ (⊲ᴮ-tr p (stepsᴮ st n<m)) q lw (l m)
... | injᵇ m<n = cmpB₀ p (⊲ᴮ-tr q (stepsᴮ st m<n)) lw (l n)
... | injᶜ refl = cmpB₀ p q lw (l n)
cmpB₀ (hLim {c = c} e p) (hLim {c = c′} e′ q) lw (mo , l) with cmpF e e′ lw
... | inj₁ C.self = cmpB₀ p q lw (l c (C.lg⊲ e lw))
... | inj₁ (C.suc r) = cmpB₀ p (⊲ᴮ-tr q (mo lw e′ e (C.suc r))) lw (l c (C.lg⊲ e lw))
... | inj₁ (C.lim k r) = cmpB₀ p (⊲ᴮ-tr q (mo lw e′ e (C.lim k r))) lw (l c (C.lg⊲ e lw))
... | inj₂ r = cmpB₀ (⊲ᴮ-tr p (mo lw e e′ r)) q lw (l c′ (C.lg⊲ e′ lw))

cmpB₀-diag : ∀ {a L : HB S₀} {w} (p : a ⊲[ w ] L) (lw : Lg w) (l : LgB L) → cmpB₀ p p lw l ≡ inj₁ hself
cmpB₀-diag hself lw l = refl
cmpB₀-diag (hsuc p) lw l = cmpB₀-diag p lw l
cmpB₀-diag (hlim n p) lw (st , l) rewrite tri-refl n = cmpB₀-diag p lw (l n)
cmpB₀-diag (hLim {c = c} e p) lw (mo , l) rewrite cmpF-diag e lw = cmpB₀-diag p lw (l c (C.lg⊲ e lw))
```

`HB S₀` 上的反对称 (严格子项与良基取自 `StallDxBdec`).

```agda
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω) renaming (wf to wfᴮ; irr to irrᴮ; toLt to toLtᴮ)

<ᴮ-tr : ∀ {a b c : HB S₀} → a <ᴮ b → b <ᴮ c → a <ᴮ c
<ᴮ-tr p <s₀ = <s p
<ᴮ-tr p (<s q) = <s (<ᴮ-tr p q)
<ᴮ-tr p (<l₀ n) = <l n p
<ᴮ-tr p (<l n q) = <l n (<ᴮ-tr p q)
<ᴮ-tr p (<Ω₀ c) = <Ω c p
<ᴮ-tr p (<Ω c q) = <Ω c (<ᴮ-tr p q)

antisymᴮ : ∀ {a b : HB S₀} {w w′} → a ⊲[ w ] b → b ⊲[ w′ ] a → a ≡ b
antisymᴮ p q with toLtᴮ p | toLtᴮ q
... | inj₁ e | _ = e
... | inj₂ _ | inj₁ e = sym e
... | inj₂ s | inj₂ t = ⊥-elim (irrᴮ (wfᴮ _) (<ᴮ-tr s t))
```

世界: 外层 $(a, b)$ ($a$ 是 `A` 的世界, $b$ 是 `HB S₀` 的界), 分量以 $(c, q : c\lhd_{[a]} b)$ 为下标, 第 $c$ 个分量是 `step (Lev (up c))` (诊断的 `Lev (Ωtop S₀)` 的分量族, 多一个新种类作槽). 增量沿路径 $c_0\lhd c$ 用 `emb⊲ (up-⊲ r)` 嵌入.

```agda
Gᴮ : HB S₀ → KS
Gᴮ c = Lev (up c)

embᴮ : ∀ {c₀ c : HB S₀} {a} → c₀ ⊲[ a ] c → HB (Gᴮ c₀) → HB (Gᴮ c)
embᴮ {a = a} r x = emb⊲ {step S₀} {w = (a , hz)} (up-⊲ r) x

Lg-embᴮ : ∀ {c₀ c : HB S₀} {a} (r : c₀ ⊲[ a ] c) x → LgB x → LgB (embᴮ r x)
Lg-embᴮ {a = a} r x l = Lg-emb⊲ {step S₀} {w = (a , hz)} (up-⊲ r) x l

Vᴮ : A → HB S₀ → Set
Vᴮ a b = (c : HB S₀) → c ⊲[ a ] b → Wd (step (Gᴮ c))

LgWᴮ : (a : A) (b : HB S₀) → Vᴮ a b → Set
LgWᴮ a b v = Lg a × LgB b × (∀ c q → LgW (step (Gᴮ c)) (v c q))

updᴮ : ∀ {c₀ b : HB S₀} {a} (δ : HB (Gᴮ c₀)) (c : HB S₀) →
       Wd (step (Gᴮ c)) → (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀) → Wd (step (Gᴮ c))
updᴮ δ c u (inj₁ r) = proj₁ u , (proj₂ u ⊞ embᴮ r δ)
updᴮ δ c u (inj₂ r) = u

raiseB : ∀ {c₀ b : HB S₀} {a} (p₀ : c₀ ⊲[ a ] b) (δ : HB (Gᴮ c₀)) (la : Lg a) (lb : LgB b) → Vᴮ a b → Vᴮ a b
raiseB {c₀} {b} {a} p₀ δ la lb v c q = updᴮ {c₀} {b} {a} δ c (v c q) (cmpB₀ q p₀ la lb)

atᴮ : ∀ {c₀ b : HB S₀} {a} (p₀ : c₀ ⊲[ a ] b) δ la lb v →
      raiseB p₀ δ la lb v c₀ p₀ ≡ (proj₁ (v c₀ p₀) , (proj₂ (v c₀ p₀) ⊞ δ))
atᴮ p₀ δ la lb v rewrite cmpB₀-diag p₀ la lb = refl

belowᴮ : ∀ {c₀ b : HB S₀} {a} (p₀ : c₀ ⊲[ a ] b) δ la lb v c q → c ⊲[ a ] c₀ → ¬ (c ≡ c₀) →
         raiseB p₀ δ la lb v c q ≡ v c q
belowᴮ {c₀} {b} {a} p₀ δ la lb v c q r ne = go (cmpB₀ q p₀ la lb)
  where
  go : (s : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) → updᴮ {c₀} {b} {a} δ c (v c q) s ≡ v c q
  go (inj₁ r′) = ⊥-elim (ne (antisymᴮ r r′))
  go (inj₂ _) = refl

raise-≤ᴮ : ∀ {c₀ b : HB S₀} {a} (p₀ : c₀ ⊲[ a ] b) δ la lb v c q →
           _≤w_ (step (Gᴮ c)) (v c q) (raiseB p₀ δ la lb v c q)
raise-≤ᴮ {c₀} {b} {a} p₀ δ la lb v c q = go (cmpB₀ q p₀ la lb)
  where
  go : (s : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) → _≤w_ (step (Gᴮ c)) (v c q) (updᴮ {c₀} {b} {a} δ c (v c q) s)
  go (inj₁ r) = ≤w-rf (Gᴮ c) , ⊞-fst (proj₂ (v c q)) (embᴮ r δ)
  go (inj₂ r) = ≤w-rf (step (Gᴮ c))

raise-lgᴮ : ∀ {c₀ b : HB S₀} {a} (p₀ : c₀ ⊲[ a ] b) δ la lb v → LgB δ → LgWᴮ a b v → LgWᴮ a b (raiseB p₀ δ la lb v)
raise-lgᴮ {c₀} {b} {a} p₀ δ la lb v lδ (_ , _ , lv) = la , lb , (λ c q → go c q (cmpB₀ q p₀ la lb))
  where
  go : ∀ c q (s : (c₀ ⊲[ a ] c) ⊎ (c ⊲[ a ] c₀)) → LgW (step (Gᴮ c)) (updᴮ {c₀} {b} {a} δ c (v c q) s)
  go c q (inj₁ r) = proj₁ (lv c q) , Lg-⊞ (proj₂ (v c q)) (embᴮ r δ) (proj₂ (lv c q)) (Lg-embᴮ r δ lδ)
  go c q (inj₂ r) = lv c q
```

**这一节的结论 (定理档).** 在诊断最小实例的下标 (`HB S₀`, 带 $\Omega$-节点) 上, 分量以 (坐标, 证据) 为下标、逐分量独立的世界, 比较式更新 `raiseB` 满足四条律: `atᴮ` (对一切证据 $p_0$, 命题相等), `belowᴮ`, `raise-≤ᴮ` (逐分量), `raise-lgᴮ`. 没有 `off`, 没有坐标相等的判定, 没有 K, 没有函数外延. 与 [AdmWNegCopy](AdmWNegCopy.lagda.md) 合起来: 这个世界形状上**更新写得出**, **`cmpK` 写不出** (`copy→⊥`).

## §7 有限测试: 拷贝在更新里拿到同一条路径

**测试, 不是证明.** 坐标 $c=\lim_n 0$ 在界 $b=\lim_n c$ 之下有两个拷贝 (`q₀ = hlim 0 hself`, `q₁ = hlim 1 hself`); 升高点 $c_0 = 0$, 证据 $p_0$ 经 $c$ 的第 1 项. `cmpB₀` 给两个拷贝的路径字面相同 (`refl`), 所以 `raiseB` 在两个拷贝上嵌入同一个 $\delta$ 的像. 合法性证据取 "环上是 `hself`" 的那一个 (闭项); 一般的合法性证据在环上给什么, 这里不说.

```agda
module CopyTest where
  c₁ : HB S₀
  c₁ = hl (λ _ → hz)

  bc : HB S₀
  bc = hl (λ _ → c₁)

  lc₁ : LgB c₁
  lc₁ = (λ n → hself) , (λ n → tt)

  lbc : LgB bc
  lbc = (λ n → hself) , (λ n → lc₁)

  p₀ : hz ⊲[ azero ] bc
  p₀ = hlim 0 (hlim 1 hself)

  q₀ q₁ : c₁ ⊲[ azero ] bc
  q₀ = hlim 0 hself
  q₁ = hlim 1 hself

  same-path : cmpB₀ q₀ p₀ tt lbc ≡ cmpB₀ q₁ p₀ tt lbc
  same-path = refl

  path-is : cmpB₀ q₀ p₀ tt lbc ≡ inj₁ (hlim 1 hself)
  path-is = refl
```
