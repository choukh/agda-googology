# 差树按层互译 (二): 第 1 层的翻译

> 不含记号. 入口 [LayerTr](LayerTr.lagda.md). 第 1 层的差树 `D one W` ([SumOneTree](SumOneTree.lagda.md)) 与第 1 层的布劳威尔树 `B₁ W` ([LayerTrBase](LayerTrBase.lagda.md)) 之间:
>
> - `S q l b x`: 从 $b$ 接着走 $x$, 即 $b+x$. `toB l x = S _ l 0 x`. 归纳假设 (第 0 层) 用在两处: `ni` 的坐标 $y$ 是合法的第 0 层布劳威尔树, 用 `BrwMidZero.dif` 读成第 0 层的差树再喂给分支; 读回时用 `BrwMidZero.toA`.
> - `ni R u` $=\sum_z u(z)$ 译成 `bi`: 坐标 $y$ 上的分支是 $b+\sum_{w<\mathrm{dif}\,y}u(w)$, 由 `I` 沿 `dif y` 积出 (坐标的记法同 `SumOneTree.Int`: 走过 $x$ 之后坐标是 $w ⨾ x$).
> - `nκ _ u` $=\sum_{c\ge W}u(c)$ 译成 `bκ`: 世界 $c$ 上的分支是 $b+\sum_{W\le c'\le c}u(c')$, 前一段由 `K` 沿路径 $W\lhd c$ 走出 (同 `SumOneTree.Cut`).
> - **合法性由形状给**: `S-fst` ($b\lhd b+x$) 与 `Lg-S` (前提只在加数上, 形如 `Ok`). `toB` 的输出总是 `LgB yes`; 没有 `nκ` 的差树 (`Ok no`) 的输出是 `LgB no`.
> - `dif₁`: 一条 `no` 的第一位置路径到差树. `bi` 读回 `ni`: 坐标 $z$ 上的差是分支从 $\mathrm{toA}\,z$ 到 $\mathrm{toA}\,z+1$ 的那一段, 由合法性里的后继步进给出. **`bκ` 读不回** (见 [LayerTr](LayerTr.lagda.md) §3).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LayerTrOne where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Strict; ss; sl; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw; Pre; tailP)
open import OCF.Align.BrwMidZero using (dif; toA)
open import OCF.Align.LayerTrBase

one : A
one = asuc azero
```

## §1 第 0 层坐标上的积分

`I e z q w b`: 从 $b$ 起, 沿坐标树 $z$ 的每个位置做一次 $e$; $w$ 是当前坐标. 第 0 层没有节点, 所以只有和的结构.

```agda
I  : ∀ {W₀ W} → (D azero W → B₁ W → B₁ W) → D azero W₀ → W₀ ⊲ W → D azero W → B₁ W → B₁ W
Ip : ∀ {W₀ W} → (D azero W → B₁ W → B₁ W) → (ℕ → D azero W₀) → W₀ ⊲ W → D azero W → B₁ W → ℕ → B₁ W
I e n0 q w b = b
I e n1 q w b = e w b
I e (x ⨾ y) q w b = I e y q (w ⨾ nw q x) (I e x q w b)
I e (nl d) q w b = bl (Ip e d q w b)
I e (ni () u) q w b
I e (nκ () u) q w b
I e (nw p x) q w b = I e x (⊲-tr p q) w b
Ip e d q w b zero = b
Ip e d q w b (suc n) = I e (d n) q (w ⨾ Pre q d n) (Ip e d q w b n)
```

## §2 和

```agda
S  : ∀ {W₀ W} → W₀ ⊲ W → Lg W → B₁ W → D one W₀ → B₁ W
Sp : ∀ {W₀ W} → W₀ ⊲ W → Lg W → B₁ W → (ℕ → D one W₀) → ℕ → B₁ W
K  : ∀ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) b {a} → a ⊲ b → W₀ ⊲ a → Lg b → B₁ a → B₁ b
KR : ∀ {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n))
     {a n} → a ⊲ f n → W₀ ⊲ a → B₁ a → ∀ m → B₁ (f (m + n))

S q l b n0 = b
S q l b n1 = bs b
S q l b (x ⨾ y) = S q l (S q l b x) y
S q l b (nl d) = bl (Sp q l b d)
S q l b (ni (ss C.self) u) =
  bi (λ {W′} p l′ y ly → I (λ w b′ → S C.self l′ b′ (u (⊲-tr q p) l′ w)) (dif {W′} y (z⊲ y) ly) C.self n0 (bw p b))
S q l b (nκ zz u) = bκ (λ {c} p lc → S C.self lc (K u c p q lc b) (u (⊲-tr q p) lc))
S q l b (nw p x) = S (⊲-tr p q) l b x
Sp q l b d zero = b
Sp q l b d (suc n) = S q l (Sp q l b d n) (d n)
K u b C.self aW lb x = x
K u (asuc c) (C.suc p) aW lb x = bw (C.suc C.self) (S C.self lb (K u c p aW lb x) (u (⊲-tr aW p) lb))
K u (alim f) (C.lim n p) aW (st , wl) x = bl (λ m → bw (C.lim (m + n) C.self) (KR u f st wl p aW x m))
KR u f st wl p aW x zero = K u (f _) p aW (wl _) x
KR u f st wl {n = n} p aW x (suc m) =
  K u (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (KR u f st wl p aW x m)

toB : ∀ {W} → Lg W → D one W → B₁ W
toB l x = S C.self l bz x
```

## §3 合法性由形状给

`Ok no x`: $x$ 里没有 `nκ` (遗传). `Ok yes` 对一切差树成立 (`ok-yes`).

```agda
Al : Fl → Set
Al yes = ⊤
Al no = ⊥

Ok : ∀ {W} → Fl → D one W → Set
Ok fl n0 = ⊤
Ok fl n1 = ⊤
Ok fl (x ⨾ y) = Ok fl x × Ok fl y
Ok fl (nl d) = ∀ n → Ok fl (d n)
Ok fl (ni r u) = ∀ {W′} p l w → Ok fl (u {W′} p l w)
Ok fl (nκ zz u) = Al fl × (∀ {c} p l → Ok fl (u {c} p l))
Ok fl (nw p x) = Ok fl x

ok-yes : ∀ {W} (x : D one W) → Ok yes x
ok-yes n0 = tt
ok-yes n1 = tt
ok-yes (x ⨾ y) = ok-yes x , ok-yes y
ok-yes (nl d) = λ n → ok-yes (d n)
ok-yes (ni r u) = λ p l w → ok-yes (u p l w)
ok-yes (nκ zz u) = tt , (λ p l → ok-yes (u p l))
ok-yes (nw p x) = ok-yes x

I-fst : ∀ {fl W₀ W} (e : D azero W → B₁ W → B₁ W) → (∀ w b → b ⊲⟨ fl ⟩ e w b) →
        (z : D azero W₀) (q : W₀ ⊲ W) → ∀ w b → b ⊲⟨ fl ⟩ I e z q w b
I-fst e fe n0 q w b = self
I-fst e fe n1 q w b = fe w b
I-fst e fe (x ⨾ y) q w b = ⊲ᴮ-tr (I-fst e fe x q w b) (I-fst e fe y q (w ⨾ nw q x) (I e x q w b))
I-fst e fe (nl d) q w b = lim 0 self
I-fst e fe (ni () u) q w b
I-fst e fe (nκ () u) q w b
I-fst e fe (nw p x) q w b = I-fst e fe x (⊲-tr p q) w b

Lg-I  : ∀ {fl W₀ W} (e : D azero W → B₁ W → B₁ W) → (∀ w b → b ⊲⟨ fl ⟩ e w b) → (∀ w b → LgB fl b → LgB fl (e w b)) →
        (z : D azero W₀) (q : W₀ ⊲ W) → ∀ w b → LgB fl b → LgB fl (I e z q w b)
Lg-Ip : ∀ {fl W₀ W} (e : D azero W → B₁ W → B₁ W) → (∀ w b → b ⊲⟨ fl ⟩ e w b) → (∀ w b → LgB fl b → LgB fl (e w b)) →
        (d : ℕ → D azero W₀) (q : W₀ ⊲ W) → ∀ w b → LgB fl b → ∀ n → LgB fl (Ip e d q w b n)
Lg-I e fe le n0 q w b lb = lb
Lg-I e fe le n1 q w b lb = le w b lb
Lg-I e fe le (x ⨾ y) q w b lb = Lg-I e fe le y q _ _ (Lg-I e fe le x q w b lb)
Lg-I e fe le (nl d) q w b lb = (λ n → I-fst e fe (d n) q (w ⨾ Pre q d n) (Ip e d q w b n)) , Lg-Ip e fe le d q w b lb
Lg-I e fe le (ni () u) q w b lb
Lg-I e fe le (nκ () u) q w b lb
Lg-I e fe le (nw p x) q w b lb = Lg-I e fe le x (⊲-tr p q) w b lb
Lg-Ip e fe le d q w b lb zero = lb
Lg-Ip e fe le d q w b lb (suc n) = Lg-I e fe le (d n) q _ _ (Lg-Ip e fe le d q w b lb n)
```

**第一位置.** `ni` 经世界自身上坐标 $0$ 的分支: 那一支是 `I` 沿 `dif 0 = n0` 走, 就是 `bw self b`. `nκ` 经世界自身那一支: `K` 沿 `self` 什么都不走.

```agda
-- 累积的形式: 从一条到 b 的路径接着走 x. 不用 ⊲ᴮ-tr, 读回 (§4) 沿它逐段走
S-fstᵃ : ∀ fl {W₀ W W′} (q : W₀ ⊲ W) (l : Lg W) {a : B₁ W′} (b : B₁ W) (x : D one W₀) → Ok fl x → a ⊲⟨ fl ⟩ b → a ⊲⟨ fl ⟩ S q l b x
S-fstᵃ fl q l b n0 o P = P
S-fstᵃ fl q l b n1 o P = suc P
S-fstᵃ fl q l b (x ⨾ y) (o , o′) P = S-fstᵃ fl q l (S q l b x) y o′ (S-fstᵃ fl q l b x o P)
S-fstᵃ fl q l b (nl d) o P = lim 0 P
S-fstᵃ fl q l b (ni (ss C.self) u) o P = ini l (wR P)
S-fstᵃ yes q l b (nκ zz u) (a , o) P = inκ l (S-fstᵃ yes C.self l b (u q l) (o q l) P)
S-fstᵃ no q l b (nκ zz u) (() , o) P
S-fstᵃ fl q l b (nw p x) o P = S-fstᵃ fl (⊲-tr p q) l b x o P

S-fst : ∀ fl {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (x : D one W₀) → Ok fl x → b ⊲⟨ fl ⟩ S q l b x
S-fst fl q l b x o = S-fstᵃ fl q l b x o self

K-fst : ∀ fl {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) → (∀ {c} p l → Ok fl (u {c} p l)) →
        ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) (x : B₁ a) → x ⊲⟨ fl ⟩ K u b p aW lb x
K-fst fl u o b C.self aW lb x = self
K-fst fl u o (asuc c) (C.suc p) aW lb x =
  wR (⊲ᴮ-tr (K-fst fl u o c p aW lb x) (S-fst fl C.self lb (K u c p aW lb x) (u (⊲-tr aW p) lb) (o (⊲-tr aW p) lb)))
K-fst fl u o (alim f) (C.lim n p) aW (st , wl) x = lim 0 (wR (K-fst fl u o (f n) p aW (wl n) x))
```

**合法.** `ni` 的后继步进: 坐标 `asuc y` 的 `dif` 字面是 `dif y ⨾ n1`, 所以分支多走一格, 那一格是 `S-fst`. `nκ` 的后继步进: `K` 沿 `C.suc p` 字面是 `bw _ (前一支)`.

```agda
Lg-S  : ∀ fl {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (x : D one W₀) → Ok fl x → LgB fl b → LgB fl (S q l b x)
Lg-Sp : ∀ fl {W₀ W} (q : W₀ ⊲ W) (l : Lg W) (b : B₁ W) (d : ℕ → D one W₀) → (∀ n → Ok fl (d n)) → LgB fl b →
        ∀ n → LgB fl (Sp q l b d n)
Lg-K  : ∀ fl {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) → (∀ {c} p l → Ok fl (u {c} p l)) →
        ∀ b {a} (p : a ⊲ b) (aW : W₀ ⊲ a) (lb : Lg b) (x : B₁ a) → LgB fl x → LgB fl (K u b p aW lb x)
Lg-KR : ∀ fl {W₀} (u : ∀ {c} → W₀ ⊲ c → Lg c → D one c) → (∀ {c} p l → Ok fl (u {c} p l)) →
        (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) → ∀ {a n} (p : a ⊲ f n) (aW : W₀ ⊲ a) (x : B₁ a) →
        LgB fl x → ∀ m → LgB fl (KR u f st wl p aW x m)

Lg-S fl q l b n0 o lb = lb
Lg-S fl q l b n1 o lb = lb
Lg-S fl q l b (x ⨾ y) (o , o′) lb = Lg-S fl q l (S q l b x) y o′ (Lg-S fl q l b x o lb)
Lg-S fl q l b (nl d) o lb = (λ n → S-fst fl q l (Sp q l b d n) (d n) (o n)) , Lg-Sp fl q l b d o lb
Lg-S fl q l b (ni (ss C.self) u) o lb = λ p l′ y ly →
  Lg-I (λ w b′ → S C.self l′ b′ (u (⊲-tr q p) l′ w))
       (λ w b′ → S-fst fl C.self l′ b′ (u (⊲-tr q p) l′ w) (o (⊲-tr q p) l′ w))
       (λ w b′ lb′ → Lg-S fl C.self l′ b′ (u (⊲-tr q p) l′ w) (o (⊲-tr q p) l′ w) lb′)
       (dif y (z⊲ y) ly) C.self n0 (bw p b) lb ,
  S-fst fl C.self l′ (I (λ w b′ → S C.self l′ b′ (u (⊲-tr q p) l′ w)) (dif y (z⊲ y) ly) C.self n0 (bw p b))
        (u (⊲-tr q p) l′ (n0 ⨾ nw C.self (dif y (z⊲ y) ly))) (o (⊲-tr q p) l′ _)
Lg-S fl q l b (nκ zz u) (a , o) lb = λ p lc →
  Lg-S fl C.self lc (K u _ p q lc b) (u (⊲-tr q p) lc) (o (⊲-tr q p) lc) (Lg-K fl u o _ p q lc b lb) ,
  ⊲ᴮ-tr (wR self) (S-fst fl {asuc _} {asuc _} C.self lc (bw (C.suc C.self) (S C.self lc (K u _ p q lc b) (u (⊲-tr q p) lc)))
                                    (u (C.suc (⊲-tr q p)) lc) (o (C.suc (⊲-tr q p)) lc))
Lg-S fl q l b (nw p x) o lb = Lg-S fl (⊲-tr p q) l b x o lb
Lg-Sp fl q l b d o lb zero = lb
Lg-Sp fl q l b d o lb (suc n) = Lg-S fl q l (Sp q l b d n) (d n) (o n) (Lg-Sp fl q l b d o lb n)
Lg-K fl u o b C.self aW lb x lx = lx
Lg-K fl u o (asuc c) (C.suc p) aW lb x lx =
  Lg-S fl C.self lb (K u c p aW lb x) (u (⊲-tr aW p) lb) (o (⊲-tr aW p) lb) (Lg-K fl u o c p aW lb x lx)
Lg-K fl u o (alim f) (C.lim n p) aW (st , wl) x lx =
  (λ m → wL (wR (K-fst fl u o (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (KR u f st wl p aW x m)))) ,
  Lg-KR fl u o f st wl p aW x lx
Lg-KR fl u o f st wl p aW x lx zero = Lg-K fl u o (f _) p aW (wl _) x lx
Lg-KR fl u o f st wl {n = n} p aW x lx (suc m) =
  Lg-K fl u o (f (suc (m + n))) (st (m + n)) (⊲-tr aW (tailP f st p m)) (wl (suc (m + n))) (KR u f st wl p aW x m) (Lg-KR fl u o f st wl p aW x lx m)

toB-fst : ∀ fl {W} (l : Lg W) (x : D one W) → Ok fl x → bz ⊲⟨ fl ⟩ toB l x
toB-fst fl l x o = S-fst fl C.self l bz x o

Lg-toB : ∀ fl {W} (l : Lg W) (x : D one W) → Ok fl x → LgB fl (toB l x)
Lg-toB fl l x o = Lg-S fl C.self l bz x o tt
```

## §4 读回差

`dif₁ b p w`: 沿第一位置路径 $p:a\lhd b$ 读出 $b-a$. 同 `BrwMidZero.dif`, 多三种路径: 抬升 (`wR`, `wL`) 与进 `bi` (`ini`). 进 `bi` 之后, 剩下的是 `ni`: 坐标 $z$ 上放分支从 $\mathrm{toA}\,z$ 到 $\mathrm{toA}\,z+1$ 的那一段, 那一段的路径就是合法性里的后继步进. 路径没有 `inκ` (标记 `no`).

```agda
dif₁ : ∀ {W W′} (b : B₁ W) {a : B₁ W′} → a ⊲⟨ no ⟩ b → LgB no b → D one W
dif₁ b self w = n0
dif₁ (bs b) (suc p) w = dif₁ b p w ⨾ n1
dif₁ (bl f) (lim n p) (st , w) = dif₁ (f n) p (w n) ⨾ nl (λ m → dif₁ (f (suc (m + n))) (st (m + n)) (w (suc (m + n))))
dif₁ (bw r b) (wR p) w = nw r (dif₁ b p w)
dif₁ b (wL p) w = dif₁ b p w
dif₁ (bi f) (ini l p) w =
  dif₁ (f C.self l azero tt) p (proj₁ (w C.self l azero tt)) ⨾
  ni (ss C.self) (λ {W′} p′ l′ z →
    dif₁ (f p′ l′ (asuc (proj₁ (toA z))) (proj₂ (toA z)))
         (proj₂ (w p′ l′ (proj₁ (toA z)) (proj₂ (toA z))))
         (proj₁ (w p′ l′ (asuc (proj₁ (toA z))) (proj₂ (toA z)))))

-- 差 → 树 → 差
difT : ∀ {W} (l : Lg W) (x : D one W) → Ok no x → D one W
difT l x o = dif₁ (toB l x) (toB-fst no l x o) (Lg-toB no l x o)
```
