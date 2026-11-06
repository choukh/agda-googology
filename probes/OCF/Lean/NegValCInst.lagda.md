# NegValC (一): 累加的折叠在值关系下的三个实例 (不依赖接口)

> 不含记号. 入口 [NegValC](NegValC.lagda.md). 本篇**不依赖**构造一路 ValC 的接口 ([ValCIf](ValCIf.lagda.md)), 只导入 [CRwBase](CRwBase.lagda.md), [CRwIf](CRwIf.lagda.md), [CRwFold](CRwFold.lagda.md), [CRw](CRw.lagda.md) (实例 `I₁`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有). 第 4 层: 只新增关系与定理, 不改树, 折叠, 合法性.
>
> **问题.** 作者本轮选定 "值: Fab5 的路线引理搬到 CRw". Fab5 的值关系 (`Fab5ValRel._≤[_]_`) 有 "ℕ-极限在左边" 的规则 `l≤` ($\forall n.\,f_n\le b\Rightarrow\lim f\le b$), 没有 "Ω-极限在左边"; 它的值单调 `Ψ-mono≤` 是对 Fab3Typed 的**逐点**折叠证的 ($\Psi(\lim f)=\lim(\Psi\circ f)$). CRw 的折叠 `Φ` 在 ℕ-极限处取**部分和** (`Σ⁺`), 后继处取部分积 (`mul`). 本篇问: Fab5 的关系与值合法原样搬到 CRw 上, 哪几处断.
>
> 1. **`acc-not-mono≤` (定理, 对一切层号, 一切目标, 一切界, 一切坐标关系 `cr`).** $\lim(1,1,1,\dots)$ 与 $1$ 在值关系下互相 $\le$ (`l11≤one`, `one≤l11`, 对一切种类结构与 `cr`), 两者都合法 (`LgB`) 且形状合法 (`Sh`); 但 CRw 的折叠把前者送到 $\hat\omega\boxplus\hat\omega\boxplus\cdots$, 后者送到 $\hat\omega$, 且 $\hat\omega+1\le\Phi(\lim(1,1,\dots))$, 所以 $\Phi(\lim(1,1,\dots))\not\le\Phi(1)$. 同底 (`sm`) 与跨底 (`cx`) 都成立; 只用到 `Φ` 的 $0$, 后继, ℕ-极限三个子句 (定义上的等式). 这是**值关系成立而折叠后的值序反向**的例子: 输入 $x\le y$ (还互相 $\le$), 输出 $\Phi\,y+1\le\Phi\,x$.
> 2. **`mo-not-pres` (定理).** Fab5 的值合法 `Mo` 原样搬过来, 不被 CRw 的折叠保持: 第 2 层的 `N = up (top b⊥ 1)` (地板 `top b⊥ 2` 在坐标 `top b⊥ 1` 处的分支, `N-branch`) 值合法且 `LgB`; 折到第 1 层 (`keep`, 留下 $\Omega_1$ 结点) 后不值合法, 因为留下的结点在坐标 $\lim(1,1,\dots)\le 1$ 处的分支就是 1 的情形. `N-in-floor` (定理, `refl`): 第 2 层地板折到第 0 层时, 回灌链的第 0 点正是 $\Phi_{2\to1,\,\mathrm{top}\,1}\,N$.
> 3. **`sh-not-mono≤` (定理, 实例 `I₁`).** 回灌 $\mathrm{sh}_0\,B\,c=B\boxplus\mathrm{leg}\,c$ 对坐标不保值关系: $\lim(1,1,\dots)\le 1$, 但 $\mathrm{sh}_0\,B\,\lim(1,1,\dots)\not\le\mathrm{sh}_0\,B\,1$, 对一切 $B$. `leg` 本身同样 (`leg-not-mono≤`). `leg` 也是部分和.
>
> **前提实例.** 1: 输入 $\lim(1,1,\dots)$, $1$ 对一切种类结构合法 (`Lg-l11`, `Sh-l11`), 对一切 `cr`, 一切世界互相 $\le$; `cr` 的实例: `cr⊥`, `cr⁺ cr⊥` (§1). 2: `N` 的 `Mo` (`Mo-N`) 与 `LgB` (`Lg-N`) 都是定理; 世界任取. 3: 对一切 $B$.
>
> **只否定什么.** 1 只否定: 一个含 `l≤` 与自反的关系 (Fab5 的关系就是) 在 CRw 的折叠下单调, 对一切值合法的输入 (Fab5 的 `Mo` 在不含 $\Omega$-结点的树上恒真). **不否定**: 对**值严格**的 ℕ-极限 (相邻项严格增长) 单调; 去掉或限制 `l≤` 的关系; CRw 闭项实际折到的输入 (地板与折叠的输出, ℕ-极限都是部分和, 相邻项至少多 $1$; 回灌坐标经 `leg` 也是部分和) 上的单调. 2 只否定 "Fab5 的 `Mo` 原样搬过来是 CRw 折叠的不变量" (Fab5 的 `Mo-Ψ` 的直接移植); 不否定把第 0 层坐标的值合法收窄 (例如只取值严格的树) 之后的版本. 3 只否定 `I₁` 的回灌对坐标值单调 (对一切坐标); 不说跨底折叠的闭项 `TX`, `TU` 的值, 因为闭项的跨底目标是第 0 层, $\Omega_1$ 结点在那里是 "同层" (链), 链的坐标是折叠的输出.
>
> **对纲领与目标.** 纲领 1: 这三条都是对布劳威尔树 (`HB`) 与它上面的值关系的陈述; 1 说明 CRw 的折叠**不是输入的值的函数**: 值相同 (互相 $\le$) 的两个合法输入折出值不同的树. 纲领 2, 4: 无公理, 不读记号. 目标 "树侧的合法性标准": Fab5 的 `Mo` 是为值而设的合法性, 本篇说明在累加的折叠上它不够, 还要一条约束 ℕ-极限 (与第 0 层坐标) 的值的合法性, 而 `LgB` (允许相邻项相同, `hself`) 不给它. 这是由树逼出的 (累加的折叠的三个子句), 不是由记号逼出的.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValCInst where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRwIf
import OCF.Lean.CRwFold as CF
```

## §1 Fab5 的值关系, 搬到 CRw 的高度上

定义逐字取自 [Fab5ValRel](../Align/Fab5ValRel.lagda.md) (`CR`, `Rel._≤[_]_`, `Rel.Mo`, `≤-refl`, `≤-trans`, `cr⁺`, `up-mono≤`, `Mo-up`), 只把类型换成 `CRwBase` 的 `KS`, `HB`, `step`, `up` (两边是不同的类型, 不能直接导入). 新增 `¬s≤`: 对一切种类结构, $x+1\not\le x$.

```agda
record CR (S : KS) : Set₁ where
  field
    _≤ᴱ[_]_ : ∀ {κ} → E S κ → Wd S → E S κ → Set
    Moᴱ     : ∀ {κ} → Wd S → E S κ → Set
    Bdᵛ     : ∀ {κ} → E S κ → Wd S → Set
    moᴱ-bot : ∀ κ w → Moᴱ {κ} w (bot S κ)
    botBdᵛ  : ∀ κ w → Bdᵛ {κ} (bot S κ) w
open CR public

module Rel {S : KS} (cr : CR S) where
  infix 4 _≤[_]_
  data _≤[_]_ : HB S → Wd S → HB S → Set where
    z≤  : ∀ {w b} → hz ≤[ w ] b
    s≤s : ∀ {w a b} → a ≤[ w ] b → hs a ≤[ w ] hs b
    ≤s  : ∀ {w a b} → a ≤[ w ] b → a ≤[ w ] hs b
    l≤  : ∀ {w f b} → (∀ n → f n ≤[ w ] b) → hl f ≤[ w ] b
    ≤l  : ∀ {w a f} n → a ≤[ w ] f n → a ≤[ w ] hl f
    ≤Ω  : ∀ {w a κ g c} → Bdᵛ cr c w → Moᴱ cr w c → a ≤[ w ] g c → a ≤[ w ] hΩ κ g
    Ω≤Ω : ∀ {w κ g g′} → (∀ c → Moᴱ cr w c → g c ≤[ w ] g′ c) → hΩ κ g ≤[ w ] hΩ κ g′

  Mo : Wd S → HB S → Set
  Mo w hz = ⊤
  Mo w (hs h) = Mo w h
  Mo w (hl f) = ∀ n → Mo w (f n)
  Mo w (hΩ κ g) =
    (∀ c c′ → Moᴱ cr w c → Moᴱ cr w c′ → _≤ᴱ[_]_ cr c w c′ → g c ≤[ w ] g c′) ×
    (∀ c → Moᴱ cr w c → Mo w (g c))

  ≤-refl : ∀ {w} a → a ≤[ w ] a
  ≤-refl hz = z≤
  ≤-refl (hs a) = s≤s (≤-refl a)
  ≤-refl (hl f) = l≤ (λ n → ≤l n (≤-refl (f n)))
  ≤-refl (hΩ κ g) = Ω≤Ω (λ c _ → ≤-refl (g c))

  ≤-trans : ∀ {w a b c} → a ≤[ w ] b → b ≤[ w ] c → a ≤[ w ] c
  ≤-trans z≤ q = z≤
  ≤-trans (l≤ h) q = l≤ (λ n → ≤-trans (h n) q)
  ≤-trans p (≤l n q) = ≤l n (≤-trans p q)
  ≤-trans p (≤Ω e m q) = ≤Ω e m (≤-trans p q)
  ≤-trans p (≤s q) = ≤s (≤-trans p q)
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
  ≤-trans (≤s p) (s≤s q) = ≤s (≤-trans p q)
  ≤-trans (≤l n p) (l≤ h) = ≤-trans p (h n)
  ≤-trans (≤Ω e m p) (Ω≤Ω H) = ≤Ω e m (≤-trans p (H _ m))
  ≤-trans (Ω≤Ω H) (Ω≤Ω H′) = Ω≤Ω (λ c mc → ≤-trans (H c mc) (H′ c mc))

  -- 新增: 后继严格 (对一切种类结构, 一切世界)
  ¬s≤ : ∀ {w} x → ¬ (hs x ≤[ w ] x)
  ¬s≤ hz ()
  ¬s≤ (hs x) (s≤s p) = ¬s≤ x p
  ¬s≤ (hs x) (≤s p) = ¬s≤ x (≤-trans (≤s (≤-refl (hs x))) p)
  ¬s≤ (hl f) (≤l n p) = ¬s≤ (f n) (≤-trans (s≤s (≤l n (≤-refl (f n)))) p)
  ¬s≤ (hΩ κ g) (≤Ω e m p) = ¬s≤ (g _) (≤-trans (s≤s (≤Ω e m (≤-refl (g _)))) p)
```

底与一步 (同 Fab5: 新种类的坐标用下一层的关系本身, 坐标的值合法是下一层的 `Mo`).

```agda
module CR⊥ where
  ≤ᴱ⊥ : ∀ {κ : K S⊥} → E S⊥ κ → ⊤ → E S⊥ κ → Set
  ≤ᴱ⊥ {()}
  Moᴱ⊥ : ∀ {κ : K S⊥} → ⊤ → E S⊥ κ → Set
  Moᴱ⊥ {()}
  Bdᵛ⊥ : ∀ {κ : K S⊥} → E S⊥ κ → ⊤ → Set
  Bdᵛ⊥ {()}
  bot⊥ : ∀ (κ : K S⊥) w → Moᴱ⊥ {κ} w (bot S⊥ κ)
  bot⊥ ()
  bbot⊥ : ∀ (κ : K S⊥) w → Bdᵛ⊥ {κ} (bot S⊥ κ) w
  bbot⊥ ()

cr⊥ : CR S⊥
cr⊥ = record { _≤ᴱ[_]_ = ≤ᴱ⊥ ; Moᴱ = Moᴱ⊥ ; Bdᵛ = Bdᵛ⊥ ; moᴱ-bot = bot⊥ ; botBdᵛ = bbot⊥ }
  where open CR⊥

module _ {T : KS} (cr : CR T) where
  open Rel cr

  ≤ᴱ⁺ : ∀ {κ} → E (step T) κ → Wd (step T) → E (step T) κ → Set
  ≤ᴱ⁺ {inj₁ κ} c w c′ = _≤ᴱ[_]_ cr c (proj₁ w) c′
  ≤ᴱ⁺ {inj₂ _} a w a′ = a ≤[ proj₁ w ] a′

  Moᴱ⁺ : ∀ {κ} → Wd (step T) → E (step T) κ → Set
  Moᴱ⁺ {inj₁ κ} w c = Moᴱ cr (proj₁ w) c
  Moᴱ⁺ {inj₂ _} w a = Mo (proj₁ w) a

  Bdᵛ⁺ : ∀ {κ} → E (step T) κ → Wd (step T) → Set
  Bdᵛ⁺ {inj₁ κ} c w = Bdᵛ cr c (proj₁ w)
  Bdᵛ⁺ {inj₂ _} a w = a ≤[ proj₁ w ] proj₂ w

  moᴱ-bot⁺ : ∀ κ w → Moᴱ⁺ {κ} w (bot (step T) κ)
  moᴱ-bot⁺ (inj₁ κ) w = moᴱ-bot cr κ (proj₁ w)
  moᴱ-bot⁺ (inj₂ _) w = tt

  botBdᵛ⁺ : ∀ κ w → Bdᵛ⁺ {κ} (bot (step T) κ) w
  botBdᵛ⁺ (inj₁ κ) w = botBdᵛ cr κ (proj₁ w)
  botBdᵛ⁺ (inj₂ _) w = z≤

cr⁺ : ∀ {T} → CR T → CR (step T)
cr⁺ cr = record { _≤ᴱ[_]_ = ≤ᴱ⁺ cr ; Moᴱ = Moᴱ⁺ cr ; Bdᵛ = Bdᵛ⁺ cr ; moᴱ-bot = moᴱ-bot⁺ cr ; botBdᵛ = botBdᵛ⁺ cr }

module _ {T : KS} (cr : CR T) where
  private
    module V = Rel cr
    module V⁺ = Rel (cr⁺ cr)

  up-mono≤ : ∀ {w β a b} → a V.≤[ w ] b → up a V⁺.≤[ (w , β) ] up b
  up-mono≤ V.z≤ = V⁺.z≤
  up-mono≤ (V.s≤s p) = V⁺.s≤s (up-mono≤ p)
  up-mono≤ (V.≤s p) = V⁺.≤s (up-mono≤ p)
  up-mono≤ (V.l≤ h) = V⁺.l≤ (λ n → up-mono≤ (h n))
  up-mono≤ (V.≤l n p) = V⁺.≤l n (up-mono≤ p)
  up-mono≤ (V.≤Ω e m p) = V⁺.≤Ω e m (up-mono≤ p)
  up-mono≤ (V.Ω≤Ω H) = V⁺.Ω≤Ω (λ c mc → up-mono≤ (H c mc))

  Mo-up : ∀ {w β} a → V.Mo w a → V⁺.Mo (w , β) (up a)
  Mo-up hz m = tt
  Mo-up (hs a) m = Mo-up a m
  Mo-up (hl f) m = λ n → Mo-up (f n) (m n)
  Mo-up (hΩ κ g) (mo , mh) =
    (λ c c′ mc mc′ p → up-mono≤ (mo c c′ mc mc′ p)) , (λ c mc → Mo-up (g c) (mh c mc))

private
  module R₀ = Rel cr⊥

-- 第 0 层: 一切树值合法 (没有结点)
Mo⊥ : ∀ c → R₀.Mo tt c
Mo⊥ hz = tt
Mo⊥ (hs c) = Mo⊥ c
Mo⊥ (hl f) = λ n → Mo⊥ (f n)
Mo⊥ (hΩ () _)
```

## §2 两个输入: $1$ 与 $\lim(1,1,\dots)$

对一切种类结构: 两者合法 (`LgB`: 相邻项是 `hself`), 对一切 `cr` 与世界互相 $\le$ (形状合法 `Sh-l11` 在 §3).

```agda
one : ∀ {S} → HB S
one = hs hz

l11 : ∀ {S} → HB S
l11 = hl (λ _ → hs hz)

module _ {S : KS} where
  Lg-l11 : LgB {S} l11
  Lg-l11 = (λ n → hself) , (λ n → tt)

  module _ (cr : CR S) where
    open Rel cr
    l11≤one : ∀ {w} → l11 ≤[ w ] one
    l11≤one = l≤ (λ n → ≤-refl (hs hz))

    one≤l11 : ∀ {w} → one ≤[ w ] l11
    one≤l11 = ≤l 0 (≤-refl (hs hz))
```

## §3 累加的折叠不保值关系 (`acc-not-mono≤`)

对一切满足接口的 `I`, 一切层号 $(s,m)$, 可达性证明, 合法证据, 目标 (同底 `sm` 或跨底 `cx`), 界 $b$, 目标层上的一切坐标关系 `cr`, 一切世界. 路径 (`Nd`) 对这两个输入是平凡的 (`nd1`, `ndl`). 折叠的值是定义上的等式: $\Phi\,1=\hat\omega=\lim(1,2,3,\dots)$ (`Φ1≡`), $\Phi\,\lim(1,1,\dots)=\lim(\hat\omega,\ \hat\omega\boxplus\hat\omega,\ \dots)$, 第 1 项的第 0 项字面是 $\hat\omega+1$.

```agda
module G (I : CRwIf) where
  open CF I

  Sh-l11 : ∀ {S} → Sh {S} l11
  Sh-l11 = (λ n → hself) , (λ n → tt)

  nd1 : ∀ {s m s′ t} (tg : Tg s m s′ t) → Nd tg one
  nd1 (sm _) = tt
  nd1 (cx _ _ _) = tt

  ndl : ∀ {s m s′ t} (tg : Tg s m s′ t) → Nd tg l11
  ndl (sm _) = tt
  ndl (cx _ _ _) = λ n → tt

  ω̂ : ∀ {S} → HB S
  ω̂ = hl (mul (hs hz))

  module AccV (s : Bs) (m : Cd) (a : Acc s m) (lm : LgB m) (s′ : Bs) (t : Cd)
              (tg : Tg s m s′ t) (b : HB (Lev s′ t)) where
    Φ1 ΦL : HB (Lev s′ t)
    Φ1 = Φ s m a lm s′ t tg b one (nd1 tg)
    ΦL = Φ s m a lm s′ t tg b l11 (ndl tg)

    Φ1≡ : Φ1 ≡ ω̂
    Φ1≡ = refl

    module _ (cr : CR (Lev s′ t)) where
      open Rel cr

      -- 值序反向: Φ 1 + 1 ≤ Φ lim(1,1,…)
      rev : ∀ {w} → hs Φ1 ≤[ w ] ΦL
      rev = ≤l 1 (≤l 0 (≤-refl (hs ω̂)))

      acc-not-mono≤ : ∀ {w} → ¬ (ΦL ≤[ w ] Φ1)
      acc-not-mono≤ p = ¬s≤ ω̂ (≤-trans rev p)
```

## §4 Fab5 的值合法不被保持 (`mo-not-pres`)

第 1, 2 层 (`Lev b⊥ 1 = step S⊥`, `Lev b⊥ 2 = step (step S⊥)`) 的坐标关系取 Fab5 的那一组 (`cr⁺`). `N` 是第 2 层的 $\Omega_1$ 结点 (种类 `inj₁ (inj₂ tt)`), 分支 $c\mapsto\mathrm{up}\,(\mathrm{up}\,c)$; 它就是地板 `top b⊥ 2` (第 2 层的 $\Omega_2$ 结点, 分支 `up`) 在坐标 `top b⊥ 1` 处的分支. 折到第 1 层: $\Omega_1$ 的层号 $1$ 就是目标, `pick` 给 `keep`, 输出是第 1 层的 $\Omega_1$ 结点, 分支 $c\mapsto\Phi(\mathrm{up}\,(\mathrm{up}\,c))$ (`FN≡`, `refl`).

```agda
  two : Cd
  two = hs (hs hz)

  cr₁ : CR (Lev b⊥ one)
  cr₁ = cr⁺ cr⊥

  cr₂ : CR (Lev b⊥ two)
  cr₂ = cr⁺ cr₁

  N : HB (Lev b⊥ two)
  N = up (top b⊥ one)

  N-branch : top b⊥ two ≡ hΩ (inj₂ tt) (λ c → up c)
  N-branch = refl

  N≡ : N ≡ hΩ (inj₁ (inj₂ tt)) (λ c → up (up c))
  N≡ = refl

  -- N 值合法 (Fab5 的 Mo, 对一切世界)
  Mo-top₁ : ∀ {w} → Rel.Mo cr₁ w (top b⊥ one)
  Mo-top₁ = (λ c c′ _ _ p → up-mono≤ cr⊥ p) , (λ c _ → Mo-up cr⊥ c (Mo⊥ c))

  Mo-N : ∀ {w} → Rel.Mo cr₂ w N
  Mo-N {w , β} = Mo-up cr₁ (top b⊥ one) Mo-top₁

  -- N 字面合法
  up⊲ : ∀ {T : KS} {w β} {a b : HB T} → a ⊲[ w ] b → up a ⊲[ (w , β) ] up b
  up⊲ hself = hself
  up⊲ (hsuc p) = hsuc (up⊲ p)
  up⊲ (hlim n p) = hlim n (up⊲ p)
  up⊲ (hLim e p) = hLim e (up⊲ p)

  Lg-up : ∀ {T : KS} (a : HB T) → LgB a → LgB (up a)
  Lg-up hz l = tt
  Lg-up (hs a) l = Lg-up a l
  Lg-up (hl f) (st , l) = (λ n → up⊲ (st n)) , (λ n → Lg-up (f n) (l n))
  Lg-up (hΩ κ g) (mo , l) = (λ lw e e′ p → up⊲ (mo (proj₁ lw) e e′ p)) , (λ {w} {c} lw e → Lg-up (g c) (l (proj₁ lw) e))

  Lg-N : LgB N
  Lg-N = (λ lw e e′ p → up⊲ (up⊲ p)) ,
         (λ {w} {c} lw e → Lg-up (up c) (Lg-up c (lgB⊲ e tt (proj₂ (proj₁ lw)))))

  FN : HB (Lev b⊥ one) → HB (Lev b⊥ one)
  FN b = Φ b⊥ two (wf b⊥ two) tt b⊥ one (sm (hsuc hself)) b N tt

  FN≡ : ∀ b → FN b ≡ hΩ (inj₂ tt) (λ c → Φ b⊥ two (wf b⊥ two) tt b⊥ one (sm (hsuc hself)) b (up (up c)) tt)
  FN≡ b = refl

  ¬Mo-FN : ∀ b {w} → ¬ Rel.Mo cr₁ w (FN b)
  ¬Mo-FN b (mo , _) =
    AccV.acc-not-mono≤ b⊥ two (wf b⊥ two) tt b⊥ one (sm (hsuc hself)) b cr₁
      (mo l11 one (Mo⊥ l11) (Mo⊥ one) (l11≤one cr⊥))

  mo-not-pres : LgB N × (∀ {w} → Rel.Mo cr₂ w N) × (∀ b {w} → ¬ Rel.Mo cr₁ w (FN b))
  mo-not-pres = Lg-N , Mo-N , ¬Mo-FN
```

**`FN` 出现在地板的折叠里.** 第 2 层地板折到第 0 层: $\Omega_2$ 的层号 $1$ 在目标 $0$ 之上, `pick` 给 `above` (先以 `top b⊥ 1` 为界坍缩到第 1 层, 再折到第 0 层); 回灌链的第 0 点是 `FN (top b⊥ 1)` (两条都是 `refl`).

```agda
  kN : HB (Lev b⊥ one) → HB (Lev b⊥ one)
  kN b′ = Φ b⊥ two (wf b⊥ two) tt b⊥ one (sm (hsuc hself)) b′ (up b′) tt

  N-in-floor : ∀ b → Φ b⊥ two (wf b⊥ two) tt b⊥ hz (sm (z⊲ᴮ two)) b (top b⊥ two) tt
                   ≡ Φ b⊥ one (wf b⊥ one) tt b⊥ hz (sm (hsuc hself)) b (hl (chain (top b⊥ one) kN)) tt
  N-in-floor b = refl

  N-chain0 : chain (top b⊥ one) kN 0 ≡ FN (top b⊥ one)
  N-chain0 = refl
```

## §5 回灌对坐标不保值关系 (实例 `I₁`)

`I₁` 的回灌是 $\mathrm{sh}_0\,B\,c=B\boxplus\mathrm{leg}\,c$, `leg` 把 ℕ-极限换成部分和. $\mathrm{leg}\,\lim(1,1,\dots)=\lim(1,2,3,\dots)$, 第 1 项字面是 $2$.

```agda
open import OCF.Lean.CRw using (I₁; leg)

leg-not-mono≤ : (l11 R₀.≤[ tt ] one) × ¬ (leg l11 R₀.≤[ tt ] leg one)
leg-not-mono≤ = l11≤one cr⊥ , λ p → R₀.¬s≤ (hs hz) (R₀.≤-trans (R₀.≤l 1 (R₀.≤-refl (hs (hs hz)))) p)

sh-not-mono≤ : ∀ B → (l11 R₀.≤[ tt ] one) × ¬ (CRwIf.sh₀ I₁ B l11 R₀.≤[ tt ] CRwIf.sh₀ I₁ B one)
sh-not-mono≤ B = l11≤one cr⊥ , λ p → R₀.¬s≤ (hs B) (R₀.≤-trans (R₀.≤l 1 (R₀.≤-refl (hs (hs B)))) p)
```

## 结论 (按档)

- **[定理, 对一切 `I`, 一切层号, 目标, 界, `cr`, 世界]** `G.AccV.acc-not-mono≤`: $\Phi\,\lim(1,1,\dots)\not\le\Phi\,1$; `G.AccV.rev`: $\Phi\,1+1\le\Phi\,\lim(1,1,\dots)$; 而输入互相 $\le$ (`l11≤one`, `one≤l11`), 合法 (`Lg-l11`, `G.Sh-l11`).
- **[定理, 对一切 `I`]** `G.mo-not-pres`: `N` 合法且 (Fab5 的) 值合法, 折到第 1 层后不值合法, 对一切界与世界. `G.N-in-floor`, `G.N-chain0`: 这个折叠出现在第 2 层地板折到第 0 层的回灌链的第 0 点.
- **[定理, 实例 `I₁`]** `leg-not-mono≤`, `sh-not-mono≤` (对一切 $B$).
- **[定理]** `Rel.¬s≤`: 对一切种类结构, $x+1\not\le x$ (Fab5 的关系).
- **[判断]** 这三处的共同来源是累加 (部分和, 部分积): 输入里相邻项相同的 ℕ-极限 ($\lim(1,1,\dots)$, `LgB` 允许) 被累加放大. 收窄到值严格的 ℕ-极限后单调是否成立, 本篇不证也不否定.
