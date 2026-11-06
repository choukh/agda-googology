# 去累加, 否定一路 (四): 跨底折叠里留下的结点在不同世界里折分支

> 不含记号. 入口 [NegNoAcc](NegNoAcc.lagda.md). 只读导入构造一路的 [NoAccFold](NoAccFold.lagda.md) (01:55 版, `Φᴾ`), 与 [CRwBase](CRwBase.lagda.md), [CRwIf](CRwIf.lagda.md), [CRwFold](CRwFold.lagda.md), [CRw](CRw.lagda.md) (实例 `I₁`), 不改它们. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路已找到同底 "在上" 的卡点 (它的 `NoAccStuck`), 跨底部分只写了判断, 留给本路. 跨底折叠 (从 $\Omega_1$ 层折到可数层号 $t$) 留下一个 $\Omega_1$ 结点时, 输出分支在坐标 $c'$ 处是 "在世界 $\mathrm{nxt}_0\,B\,(\mathrm{sh}_0\,B\,c')$ 里折 $g(\mathrm{sh}_0\,B\,c')$". 相邻坐标的分支在**不同的世界**里折; 里面再留下的 $\Omega_1$ 结点经回灌 $W\boxplus d$ 读到各自的世界 $W$. 证书读输入合法时, 后一段折叠 (例如 "在上" 的第二段) 要前一段的输出合法, 所以这里问: 留下的结点合法吗?
>
> 1. **`⊞-not-monoˡ` (定理).** 回灌对世界不保第一位置: $1\lhd2$, 但 $1\boxplus\omega\not\lhd2\boxplus\omega$. (接口 `NoAccIf.sh-⊲` 只要求对坐标单调; `CRwIf` 的 `I₁` 的回灌 $B\boxplus\mathrm{leg}\,c$ 同样只对坐标.)
> 2. **`kept-world` (定理, 核心, 只看几个值).** 第 1 层 (`step S⊥`) 的结点 $\sup G$, 若 $c_0\lhd c_1$ (在合法世界的界之下) 处的分支是同一种类的结点 $\sup X$, $\sup Y$, 且 $X\,d\neq Y\,d$ (某个 $d$), $Y$ 的分支都不含 $\Omega$-结点, 则 $\sup G$ **不** `LgB`.
> 3. **`kept-world-Φᴾ` (定理, 对构造一路的 `Φᴾ`, 实例 `I₁`).** $\Omega_1$ 层一个合法的输入 `In` ($\Omega_1$ 结点, 分支恒为 $K$; $K$ 是 $\Omega_1$ 结点, 分支在 $e$ 处是 $e$ 自己), 世界 $B=2$ 合法且输入带路径 (`PH-In`), 经逐点折叠 `Φᴾ` 跨底折到第 1 层: 两个 $\Omega_1$ 结点都留下, 输出**不 `LgB`**. 分支 $c'=0, 1$ 的世界是 $3, 4$; 里面的结点在 $d=0$ 处折的是 $3$ 与 $4$, 输出不同.
> 4. **`kept-world-Φ` (定理, 对照).** 同一输入在 CRw 的累加折叠 `CRwFold.Φ` 下同样不 `LgB`. 所以这一条与 ℕ-极限子句是否累加无关; CRw 不受影响, 因为它的证书 (`Sh-Φ`) 不要中间层合法.
>
> 5. **`leg-not-pt`, `no-CRwIf-⊞` (定理).** `NoAccFold` 的跨底部分仍用 `CRwIf` 的 `I₁`, 回灌里的 `leg` 是部分和 (`leg-not-pt`). 这不是疏忽: 若 `CRwIf` 的进入保留坐标合法的信息 (`I₁` 满足), 回灌就不能是不累加的 $1\boxplus c$ (`no-CRwIf-⊞`). 所以 `Φᴾ` 只去掉了 ℕ-极限子句的累加; 后继 (`mul`), 坍缩链 (`chain`), 跨底回灌 (`leg`) 三处的 `⊞` 都还在 (前两处是 `refl` 可读的定义, 判断不算 "累加子句" 由作者定).
>
> **前提实例.** 输入合法 (`Lg-In`), 带路径 (`PH-In`), 世界 $B=2$ 合法, $1\lhd B$; 违反 `LgB` 的世界 $(\mathrm{tt},1)$ 合法, $0\lhd1$, $1\lhd1$, $0\lhd1$.
>
> **只否定什么.** 只否定: `CRwIf` (加进入保留合法) 配不累加的回灌; 跨底折叠 (`Φᴾ` 与 `Φ`, 实例 `I₁`) 在留下 $\Omega_1$ 结点时输出合法 (对合法且带路径的输入). **不否定**: 闭项 `TX`, `TU` 的证书 (它们折到第 0 层, 不留 $\Omega_1$; 若用形状证书, 不要中间层合法); 换一种世界移动 (例如分支不读世界, 或回灌对世界单调) 的跨底折叠; 用别的合法性 (只在相容世界里) 验收中间层. 本篇没有关闭任何路线.
>
> **对纲领与目标.** 去累加之后, 证书读输入合法要求中间层的输出合法; 跨底的世界移动 (分支的世界随坐标变, 回灌读世界) 让留下的结点在分支之间不单调. 这是树侧的信息: 去累加的下一步要的不是改 ℕ-极限子句, 而是让留下结点的分支在 "同一个世界" 里折, 或者回灌对世界单调 (判断, 未写).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegNoAccX where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf
open import OCF.Lean.NegCRwInst using (num; at; lim-not-fin; hs-inj)
open import OCF.Lean.CRw using (I₁)
import OCF.Lean.CRwFold as CF
import OCF.Lean.NoAccFold as NF
```

## §1 回灌对世界不单调

```agda
open import Data.Nat using (_+_)

ω̂ : Cd
ω̂ = hl num

addN : ∀ a n → num {S⊥} a ⊞ num n ≡ num (n + a)
addN a zero = refl
addN a (suc n) = cong hs (addN a n)

one≢two : ¬ (num {S⊥} 1 ≡ num 2)
one≢two e = h (hs-inj e)
  where h : ¬ (hz ≡ num {S⊥} 1)
        h ()

⊞-not-monoˡ : (num 1 ⊲ num 2) × ¬ (num 1 ⊞ ω̂ ⊲ num 2 ⊞ ω̂)
⊞-not-monoˡ = hsuc hself , (λ p → go p refl)
  where
  go : ∀ {b} → num 1 ⊞ ω̂ ⊲ b → b ≡ num 2 ⊞ ω̂ → ⊥
  go hself e = one≢two (cong (λ h → at h 0) e)
  go (hsuc p) ()
  go (hlim n q) refl = lim-not-fin (n + 2) (subst (λ z → num 1 ⊞ ω̂ ⊲ z) (addN 2 n) q)
```

## §2 核心: 留下的结点, 分支是同种类而不同的结点

```agda
module _ {S : KS} where
  NoΩ : HB S → Set
  NoΩ hz = ⊤
  NoΩ (hs h) = NoΩ h
  NoΩ (hl f) = ∀ n → NoΩ (f n)
  NoΩ (hΩ _ _) = ⊥

  noΩ⊲ : ∀ {w κ g y} → NoΩ y → ¬ (hΩ κ g ⊲[ w ] y)
  noΩ⊲ ny hself = ny
  noΩ⊲ ny (hsuc p) = noΩ⊲ ny p
  noΩ⊲ ny (hlim n p) = noΩ⊲ (ny n) p
  noΩ⊲ ny (hLim e p) = ny

  NoΩ-⊞ : ∀ a b → NoΩ a → NoΩ b → NoΩ (a ⊞ b)
  NoΩ-⊞ a hz na nb = na
  NoΩ-⊞ a (hs b) na nb = NoΩ-⊞ a b na nb
  NoΩ-⊞ a (hl f) na nb = λ n → NoΩ-⊞ a (f n) na (nb n)
  NoΩ-⊞ a (hΩ κ g) na ()

S₁ : KS
S₁ = step S⊥

br : HB S₁ → Cd → HB S₁
br hz = λ _ → hz
br (hs _) = λ _ → hz
br (hl _) = λ _ → hz
br (hΩ (inj₁ ()) _)
br (hΩ (inj₂ _) g) = g

module KeptW (G X Y : Cd → HB S₁) (c₀ c₁ b : Cd) (lb : LgB b) (e₀ : c₀ ⊲ b) (e₁ : c₁ ⊲ b) (p : c₀ ⊲ c₁)
  (eX : G c₀ ≡ hΩ (inj₂ tt) X) (eY : G c₁ ≡ hΩ (inj₂ tt) Y)
  (d : Cd) (dif : ¬ (X d ≡ Y d)) (noΩ : ∀ d′ → NoΩ (Y d′)) where

  W : Wd S₁
  W = tt , b

  kept-world : ¬ LgB {S₁} (hΩ (inj₂ tt) G)
  kept-world (mo , _) = go (mo {w = W} (tt , lb) e₀ e₁ p) eX eY
    where
    go : ∀ {a y} → a ⊲[ W ] y → a ≡ hΩ (inj₂ tt) X → y ≡ hΩ (inj₂ tt) Y → ⊥
    go hself ea eb = dif (cong (λ F → F d) (cong br (trans (sym ea) eb)))
    go (hsuc q) ea ()
    go (hlim n q) ea ()
    go {a} (hLim {c = c} e q) ea refl = noΩ⊲ (noΩ c) (subst (λ z → z ⊲[ W ] Y c) ea q)
```

## §3 实例: 构造一路的逐点折叠 `Φᴾ` 与 CRw 的 `Φ`

```agda
open CF I₁
open NF I₁ using (Φᴾ)

κΩ : K XS
κΩ = hz , inj₂ tt

liftX : Cd → HB XS
liftX hz = hz
liftX (hs c) = hs (liftX c)
liftX (hl f) = hl (λ n → liftX (f n))
liftX (hΩ () _)

liftX-⊲ : ∀ {c c′ : Cd} {x : ⊤} {w} → c ⊲[ x ] c′ → liftX c ⊲[ w ] liftX c′
liftX-⊲ hself = hself
liftX-⊲ (hsuc p) = hsuc (liftX-⊲ p)
liftX-⊲ (hlim n p) = hlim n (liftX-⊲ p)

Lg-liftX : ∀ c → LgB c → LgB (liftX c)
Lg-liftX hz l = tt
Lg-liftX (hs c) l = Lg-liftX c l
Lg-liftX (hl f) (st , l) = (λ n → liftX-⊲ (st {tt} n)) , (λ n → Lg-liftX (f n) (l n))
Lg-liftX (hΩ () _) l

Kn In : HB XS
Kn = hΩ κΩ liftX
In = hΩ κΩ (λ _ → Kn)

Lg-Kn : LgB Kn
Lg-Kn = (λ lw e e′ p → liftX-⊲ p) , (λ {w} {c} lw e → Lg-liftX c (lgB⊲ e tt (proj₂ (lw hz))))

Lg-In : LgB In
Lg-In = (λ lw e e′ p → hself) , (λ lw e → Lg-Kn)

PH-lift : ∀ V x → PH PSX V (liftX x)
PH-lift V hz = tt
PH-lift V (hs x) = PH-lift V x
PH-lift V (hl f) = λ n → PH-lift V (f n)
PH-lift V (hΩ () _)

PH-Kn : ∀ V → hs hz ⊲ V → PH PSX V Kn
PH-Kn V o = o , (λ e a → PH-lift (hs e) e)

B₂ : Cd
B₂ = num 2

PH-In : PH PSX B₂ In
PH-In = hsuc hself , (λ e a → PH-Kn (hs e) (⊲ᴮ-tr (⊲ᴮ-tr (hsuc hself) (proj₁ a)) (hsuc hself)))

tg₁ : Tg bX hz b⊥ (num 1)
tg₁ = cx B₂ tt (hsuc hself)
```

**逐点折叠 `Φᴾ`.** 输出 $O$; 它的分支 $G=\mathrm{br}\,O$, $X=\mathrm{br}(G\,0)$, $Y=\mathrm{br}(G\,1)$. 结构等式都是 `refl`.

```agda
NoΩ-mul : ∀ {S : KS} (x : HB S) → NoΩ x → ∀ n → NoΩ (mul x n)
NoΩ-mul x nx zero = nx
NoΩ-mul x nx (suc n) = NoΩ-⊞ (mul x n) x (NoΩ-mul x nx n) nx

NoΩ-Φᴾ : ∀ {t} a lm (tg : Tg bX hz b⊥ t) b x nd → NoΩ (Φᴾ bX hz a lm b⊥ t tg b (liftX x) nd)
NoΩ-Φᴾ a lm tg b hz nd = tt
NoΩ-Φᴾ a lm tg b (hs x) nd = NoΩ-mul _ (NoΩ-Φᴾ a lm tg b x (ndS tg (liftX x) nd))
NoΩ-Φᴾ a lm tg b (hl f) nd = λ n → NoΩ-Φᴾ a lm tg b (f n) (ndL tg (λ n → liftX (f n)) nd n)
NoΩ-Φᴾ a lm tg b (hΩ () _) nd

Oᴾ : HB S₁
Oᴾ = Φᴾ bX hz (wf bX hz) tt b⊥ (num 1) tg₁ hz In PH-In

module Pᴾ where
  G X Y : Cd → HB S₁
  G = br Oᴾ
  X = br (G hz)
  Y = br (G (hs hz))

  eO : Oᴾ ≡ hΩ (inj₂ tt) G
  eO = refl

  dif : ¬ (X hz ≡ Y hz)
  dif e = h (cong (λ z → at (at (at z 0) 0) 0) e)
    where h : ∀ {f : ℕ → HB S₁} → ¬ (hs hz ≡ hl f)
          h ()

  noΩ : ∀ d → NoΩ (Y d)
  noΩ d = NoΩ-Φᴾ _ _ _ _ _ _

  ¬Lg : ¬ LgB Oᴾ
  ¬Lg = KeptW.kept-world G X Y hz (hs hz) (hs hz) tt (hsuc hself) hself (hsuc hself) refl refl hz dif noΩ

kept-world-Φᴾ : LgB In × PH PSX B₂ In × LgB B₂ × ¬ LgB Oᴾ
kept-world-Φᴾ = Lg-In , PH-In , tt , Pᴾ.¬Lg
```

**对照: CRw 的累加折叠 `Φ`.** 同一输入.

```agda
NoΩ-Σ : ∀ {S : KS} (f : ℕ → HB S) → (∀ n → NoΩ (f n)) → ∀ n → NoΩ (Σ⁺ f n)
NoΩ-Σ f nf zero = nf 0
NoΩ-Σ f nf (suc n) = NoΩ-⊞ (Σ⁺ f n) (f (suc n)) (NoΩ-Σ f nf n) (nf (suc n))

NoΩ-Φ : ∀ {t} a lm (tg : Tg bX hz b⊥ t) b x nd → NoΩ (Φ bX hz a lm b⊥ t tg b (liftX x) nd)
NoΩ-Φ a lm tg b hz nd = tt
NoΩ-Φ a lm tg b (hs x) nd = NoΩ-mul _ (NoΩ-Φ a lm tg b x (ndS tg (liftX x) nd))
NoΩ-Φ a lm tg b (hl f) nd = NoΩ-Σ _ (λ n → NoΩ-Φ a lm tg b (f n) (ndL tg (λ n → liftX (f n)) nd n))
NoΩ-Φ a lm tg b (hΩ () _) nd

Oᶜ : HB S₁
Oᶜ = Φ bX hz (wf bX hz) tt b⊥ (num 1) tg₁ hz In PH-In

module Pᶜ where
  G X Y : Cd → HB S₁
  G = br Oᶜ
  X = br (G hz)
  Y = br (G (hs hz))

  eO : Oᶜ ≡ hΩ (inj₂ tt) G
  eO = refl

  dif : ¬ (X hz ≡ Y hz)
  dif e = h (cong (λ z → at (at (at z 0) 0) 0) e)
    where h : ∀ {f : ℕ → HB S₁} → ¬ (hs hz ≡ hl f)
          h ()

  noΩ : ∀ d → NoΩ (Y d)
  noΩ d = NoΩ-Φ _ _ _ _ _ _

  ¬Lg : ¬ LgB Oᶜ
  ¬Lg = KeptW.kept-world G X Y hz (hs hz) (hs hz) tt (hsuc hself) hself (hsuc hself) refl refl hz dif noΩ

kept-world-Φ : ¬ LgB Oᶜ
kept-world-Φ = Pᶜ.¬Lg
```

## §4 构造一路的 `Φᴾ` 哪里还累加; `CRwIf` 逼出累加的回灌

`NoAccFold` 的跨底部分沿用 `CRwIf` (实例 `I₁`, 回灌 $B\boxplus\mathrm{leg}\,c$). `leg` 是部分和, 不逐点 (`leg-not-pt`). 构造一路的判断 "在 `NoAccIf` 上写不出 `dcx`" 的一个形式: **`no-CRwIf-⊞`** (定理): 若 `CRwIf` 的进入保留坐标合法的信息 (`LgB (nxt₀ B e a) → LgB e`, `I₁` 满足: `nxt-I₁`), 则回灌不能是 $1\boxplus c$ (对一切 $c$). 因为 `adm-sh` 与 `lg-nx` 对一切坐标给出合法的新世界, 而 $1\boxplus\lim(\lim(0,0,\dots),0,0,\dots)$ 不合法 (`no-up`). 两个前提各自可满足: 前者 `I₁`, 后者 `stay⊞` (回灌 $B\boxplus c$, 世界不动).

```agda
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.NegNoAccPt using (no-up; two)

leg-not-pt : ¬ (leg (hl (λ n → num n)) ≡ hl (λ n → leg (num n)))
leg-not-pt e = h (cong (λ z → at z 2) e)
  where h : ¬ (num {S⊥} 3 ≡ num 2)
        h e′ = h₂ (hs-inj (hs-inj e′))
          where h₂ : ¬ (num {S⊥} 1 ≡ hz)
                h₂ ()

nxt-I₁ : ∀ {B e} (a : CRwIf.Adm₀ I₁ B e) → LgB (CRwIf.nxt₀ I₁ B e a) → LgB e
nxt-I₁ a l = l

stay⊞ : CRwIf
stay⊞ = record
  { Adm₀ = λ B e → ⊤ ; nxt₀ = λ B e a → B ; sh₀ = λ B c → B ⊞ c
  ; adm-sh = λ c lB → tt ; nx-up = λ a → hself ; lg-nx = λ a lB → lB ; adm↓ = λ q a′ → tt , q }

stay⊞-sh : ∀ c → CRwIf.sh₀ stay⊞ (hs hz) c ≡ hs hz ⊞ c
stay⊞-sh c = refl

no-CRwIf-⊞ : ∀ (J : CRwIf) → (∀ {B e} (a : CRwIf.Adm₀ J B e) → LgB (CRwIf.nxt₀ J B e a) → LgB e) →
             ¬ (∀ c → CRwIf.sh₀ J (hs hz) c ≡ hs hz ⊞ c)
no-CRwIf-⊞ J refl-lg sh-eq = no-up {w = tt} (hs hz) (proj₁ lgc {tt} 0)
  where
  open CRwIf J
  c⋆ : Cd
  c⋆ = hl (two (hl (λ _ → hz)) hz)
  a⋆ = adm-sh {B = hs hz} c⋆ tt
  lgc : LgB (hs hz ⊞ c⋆)
  lgc = subst LgB (sh-eq c⋆) (refl-lg a⋆ (lg-nx a⋆ tt))
```

## 结论 (按档)

- **[定理]** `addN`, **`⊞-not-monoˡ`**; `NoΩ`, `noΩ⊲`, `NoΩ-⊞`, `br`, **`KeptW.kept-world`** (核心, 只看几个值); 实例 `Kn`, `In`, `Lg-Kn`, **`Lg-In`**, `PH-lift`, `PH-Kn`, **`PH-In`**, `tg₁`; `NoΩ-mul`, `NoΩ-Φᴾ`, `Pᴾ.eO` (refl), `Pᴾ.dif`, **`kept-world-Φᴾ`** (构造一路的逐点折叠: 合法带路径的输入, 输出不 `LgB`); `NoΩ-Σ`, `NoΩ-Φ`, **`kept-world-Φ`** (CRw 的累加折叠同样); **`leg-not-pt`**, `nxt-I₁`, `stay⊞`, `stay⊞-sh`, **`no-CRwIf-⊞`** (`CRwIf` 加 "进入保留坐标合法" 逼出回灌累加).
- **[判断]** 出路的方向 (分支在同一世界里折, 或回灌对世界单调) 未写, 未否定.
