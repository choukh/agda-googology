# 高度上的值关系: 对一切种类结构一条定义, 与 "值合法" `Mo`

> 不含记号. Fable 5.1, 2026-11-06 (第五轮自选: 摆脱侧). 入口 [Fab5Val](Fab5Val.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP. 不改任何已有文件. 只导入 [HtTowerTy](HtTowerTy.lagda.md).
>
> **这一篇做什么.** C 线 (带类型折叠) 至今没有值的定理; 主审把值的一侧的障碍归到 "折叠对层单调" 一条. 字面第一位置 `_⊲[_]_` 是前缀关系, 不是值关系: 它没有 "极限在左边" 的规则 ($\forall n.\,f_n\le b\Rightarrow\lim f\le b$), 所以累加的折叠不保它 (`NegTySupMono.Φ-not-mono`), 而 "第 $n$ 层的塔项低于第 $n+1$ 层的塔项" 这样的值陈述在 `⊲` 下根本写不出 (两棵树不互为前缀). 本篇把**值关系** `_≤[_]_` 写在 `HB S` 上, 对一切种类结构 `S` 一条定义, 它就是第 0 层的标准前序 (`TLRuleSpec._≤_`: `z≤`, `s≤`, `≤l`, `l≤`; 这里把那边可推出的 `≤-suc` 写成规则 `≤s`, 因为没有 "$\Omega$-极限在左边" 时它推不出) 加上 $\Omega$-结点的两条:
>
> - `≤Ω`: 值界之下 (`Bdᵛ`, 新种类是 $c\le b$)、**值合法** (`Moᴱ`) 的坐标 $c$ 处, $a\le g\,c\Rightarrow a\le\sup g$ (右边取一支);
> - `Ω≤Ω`: 同一种类的两个结点在值合法的坐标上逐支比较.
>
> 界用值关系 (`Bdᵛ`) 而不用字面的 `Bd`: 这样整个值的一侧不碰字面第一位置, 也不要 `LgB` 作前提 (入口的 `Ψ-mono≤` 只要 `Mo`). 坐标限于值合法: 折叠的值单调要对右边的结点分支作归纳, 归纳假设要分支值合法, 而 "一切坐标处的分支都值合法" 塔的 $\Omega_n$ 不满足 (坐标是任意的树). 这是 Kripke 式的写法, 与 `X1UpIf` 的可入同一形状.
>
> 没有 "$\Omega$-极限在左边" 的规则 ($\forall c.\,g\,c\le b\Rightarrow\sup g\le b$): 折叠把 $\Omega$-结点坍缩成可数链, 这条规则对坍缩不可靠 (判断, 不证). 坐标上的值关系与值合法由一个记录 `CR S` 给出, `step` 一步 (`cr⁺`): 新种类的坐标是 `HB T`, 用 `T` 上的关系本身.
>
> **值合法 `Mo`.** `≤` 有 "极限在左边", 所以 `⊲`-合法 (`LgB`, 分支保第一位置) 的结点**不保证**分支保 `≤` (入口 `lgB-not-mo`, 定理). 值的定理需要的分支单调是对 `≤` 的, 本篇把它写成谓词 `Mo w h`: 每个 $\Omega$-结点的分支在值合法的坐标上保 `≤`, 并遗传到值合法坐标处的分支. 这是树侧的一条合法性判据 (目标里的 "树侧的合法性标准"), 与 `LgB` 不同: `LgB` 为了比较 (`cmpB`, 要字面第一位置), `Mo` 为了值. 两者都不读记号.
>
> **定理 (对一切 `S`, `CR S`).** 自反 `≤-refl` (对一切树, 不要 `Mo`), 传递 `≤-trans`, 加法两边单调 (`⊞-monoˡ`, `⊞-monoʳ`), `≤⊞`, `≤⊞ˡ`, `Mo-⊞`; `step` 的嵌入 `up` 保 `≤` 与 `Mo` (`up-mono≤`, `Mo-up`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Fab5ValRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.HtTowerTy
```

## §1 坐标上的值关系与值合法

```agda
record CR (S : KS) : Set₁ where
  field
    _≤ᴱ[_]_ : ∀ {κ} → E S κ → Wd S → E S κ → Set
    Moᴱ     : ∀ {κ} → Wd S → E S κ → Set
    Bdᵛ     : ∀ {κ} → E S κ → Wd S → Set
    moᴱ-bot : ∀ κ w → Moᴱ {κ} w (bot S κ)
    botBdᵛ  : ∀ κ w → Bdᵛ {κ} (bot S κ) w
open CR public
```

## §2 值关系与 `Mo`

```agda
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
```

**基本性质.** 自反对一切树 (逐支); 传递对两个推导的字典序归纳. 没有 `⊲→≤`: 沿 `hLim` 走要经过任意坐标, 那里没有值合法; 值的一侧不从字面第一位置出发.

```agda
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

```

**加法.** 右边逐构造子, 所以 `a ⊞ x` 对 `a` 单调是对 `x` 的归纳, 对 `x` 单调是对推导的归纳.

```agda
  ≤⊞ : ∀ {w} a b → a ≤[ w ] a ⊞ b
  ≤⊞ a hz = ≤-refl a
  ≤⊞ a (hs b) = ≤s (≤⊞ a b)
  ≤⊞ a (hl f) = ≤l 0 (≤⊞ a (f 0))
  ≤⊞ {w} a (hΩ κ g) = ≤Ω (botBdᵛ cr κ w) (moᴱ-bot cr κ w) (≤⊞ a (g (bot S κ)))

  ≤⊞ˡ : ∀ {w} a x → x ≤[ w ] a ⊞ x
  ≤⊞ˡ a hz = z≤
  ≤⊞ˡ a (hs x) = s≤s (≤⊞ˡ a x)
  ≤⊞ˡ a (hl f) = l≤ (λ n → ≤l n (≤⊞ˡ a (f n)))
  ≤⊞ˡ a (hΩ κ g) = Ω≤Ω (λ c _ → ≤⊞ˡ a (g c))

  ⊞-monoˡ : ∀ {w a a′} x → a ≤[ w ] a′ → a ⊞ x ≤[ w ] a′ ⊞ x
  ⊞-monoˡ hz p = p
  ⊞-monoˡ (hs x) p = s≤s (⊞-monoˡ x p)
  ⊞-monoˡ (hl f) p = l≤ (λ n → ≤l n (⊞-monoˡ (f n) p))
  ⊞-monoˡ (hΩ κ g) p = Ω≤Ω (λ c _ → ⊞-monoˡ (g c) p)

  ⊞-monoʳ : ∀ {w} a {x y} → x ≤[ w ] y → a ⊞ x ≤[ w ] a ⊞ y
  ⊞-monoʳ a (z≤ {b = y}) = ≤⊞ a y
  ⊞-monoʳ a (s≤s p) = s≤s (⊞-monoʳ a p)
  ⊞-monoʳ a (≤s p) = ≤s (⊞-monoʳ a p)
  ⊞-monoʳ a (l≤ h) = l≤ (λ n → ⊞-monoʳ a (h n))
  ⊞-monoʳ a (≤l n p) = ≤l n (⊞-monoʳ a p)
  ⊞-monoʳ a (≤Ω e m p) = ≤Ω e m (⊞-monoʳ a p)
  ⊞-monoʳ a (Ω≤Ω H) = Ω≤Ω (λ c mc → ⊞-monoʳ a (H c mc))

  ⊞-mono : ∀ {w a a′ x y} → a ≤[ w ] a′ → x ≤[ w ] y → a ⊞ x ≤[ w ] a′ ⊞ y
  ⊞-mono {x = x} p q = ≤-trans (⊞-monoˡ x p) (⊞-monoʳ _ q)

  Mo-⊞ : ∀ {w} a b → Mo w a → Mo w b → Mo w (a ⊞ b)
  Mo-⊞ a hz ma mb = ma
  Mo-⊞ a (hs b) ma mb = Mo-⊞ a b ma mb
  Mo-⊞ a (hl f) ma mb = λ n → Mo-⊞ a (f n) ma (mb n)
  Mo-⊞ a (hΩ κ g) ma (mo , mh) =
    (λ c c′ mc mc′ p → ⊞-monoʳ a (mo c c′ mc mc′ p)) , (λ c mc → Mo-⊞ a (g c) ma (mh c mc))
```

## §3 一步: 新种类的坐标用 `T` 上的关系本身

```agda
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
```

**嵌入 `up` 保 `≤` 与 `Mo`.** 旧种类的界与坐标的值合法在新世界里就是旧世界里的 (字面).

```agda
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
```

## 结论 (按档)

- **[定理]** `CR`, `Rel._≤[_]_`, `Rel.Mo`, `≤-refl`, `≤-trans`, `≤⊞`, `≤⊞ˡ`, `⊞-monoˡ`, `⊞-monoʳ`, `⊞-mono`, `Mo-⊞`, `cr⁺`, `up-mono≤`, `Mo-up`.
- **[判断]** `≤` 是值关系的一个可靠子关系: 没有 "$\Omega$-极限在左边" 的规则, 因为折叠坍缩 $\Omega$-结点为可数链; 第 0 层上它与 `TLRuleSpec._≤_` 相同 (入口 `≤→≤ᴬ`, 定理).
