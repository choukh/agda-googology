# 路径记在折叠输出上, 否定一路 (五): 合法的输入把低坐标的种类带进每个分支

> 不含记号. 入口 [NegPathOut](NegPathOut.lagda.md). 本篇不依赖构造一路的实例 (只用 [NegPathOutWorld](NegPathOutWorld.lagda.md) 的 `LOm`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 构造一路的设计 (PathOut 的消息, 待实例验证): 折叠的输入带一个谓词, 说 "输入里种类的坐标都在界之上" ($B\lhd y$), 于是目标 ($t\lhd B$) 与种类经 $B$ 有公共上界; 留下的结点进入分支时坐标先接在界后 ($B\boxplus e$). 本篇问: **合法的** (`LgB`) 输入满足这样的谓词吗?
>
> **结果.**
>
> 1. **`ment⊲` (定理).** 第一位置保 "提到坐标 $c$ 的种类": $a\lhd b$ 且 $a$ 提到 $c$, 则 $b$ 提到 $c$.
> 2. **`spread` (定理).** 层号 `lΩ lz G` 上, 合法的 $\Omega_1$-结点 $\mathrm{h\Omega}\,\Omega_1\,g$, 若分支 $g\,c$ 提到坐标 $c$, 则对一切合法的 $c'\rhd c$, 分支 $g\,c'$ 也提到 $c$. 特别地 $g\,0$ 提到 $0$ 时, 一切合法分支都提到 $0$ (`spread-0`). 合法性 (Ω-单调) 把低坐标的种类带进每个高分支.
> 3. **`above-fails` (定理).** 谓词 "高度里一切以坐标为下标的种类, 坐标都在 $b$ 之上" (`AbV b`) 在提到 $0$ 的高度上只对 $b=0$ 成立 (`AbV b h → b ≡ hz`). 所以对 2 里的合法结点, 任何非零界 $b$ 下, **没有一个合法分支**满足 `AbV b` (`no-AbV-branch`).
> 4. **实例 `Dᶜ` (构造).** `Dᶜ` 的分支 $g\,c$ 按 $c$ 的结构累加: $g\,0$ 是种类 $0$ 的结点, $g\,(c+1)$ 是种类 $c+1$ 的结点, 分支取 $g\,c$; $g\,(\lim f)=\lim g\circ f$. 它**合法** (`Lg-Dᶜ`, 在一切世界里单调), 分支 $g\,0$ 提到 $0$. 读法 (判断): $\sup_c\Omega_{c+1}$ 的一个合法写法.
>
> **前提实例.** 2, 3: `Dᶜ` (`Lg-Dᶜ`, `ment-g0`). $b=1$ 非零.
>
> **只否定什么.** 只否定: 对合法输入要求 "一切以坐标为下标的种类坐标都在当前界之上" (`AbV`, 在非零界下). **不否定**: 只对**部分**种类 (例如刚进入的坐标对应的那一个) 要求在界之上; 对在界之下的种类另给证据 ($y\lhd B$ 与 $t\lhd B$ 同样有公共上界 $B$); 不按这个谓词组织的折叠. 构造一路的谓词 `PH` 是哪一种, 要对实例查. 本篇没有关闭任何路线.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegPathOutLg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; [_,_])
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥; LH; lz; ls; ll; lΩ; Lv)
open import OCF.Align.LFReBr using (w₀; Lg-w₀)
open import OCF.Align.NegPathOutWorld using (module LOm; G₁; κ₁)
```

## §1 第一位置保 "提到坐标"

```agda
module Spread (G : HB S⊥ → LH) where
  open LOm G using (X; SX; Ω₁; Ment)

  ment⊲ : ∀ {w a b c} → a ⊲[ w ] b → Ment c a → Ment c b
  ment⊲ hself m = m
  ment⊲ (hsuc p) m = ment⊲ p m
  ment⊲ (hlim n p) m = n , ment⊲ p m
  ment⊲ (hLim {κ = inj₁ _ , inj₁ ()} _ _) m
  ment⊲ (hLim {κ = inj₁ _ , inj₂ _} {c = e} _ p) m = e , ment⊲ p m
  ment⊲ (hLim {κ = inj₂ c′ , κ} {c = e} _ p) m = inj₂ (e , ment⊲ p m)
```

## §2 合法的 $\Omega_1$-结点把低坐标带进高分支

世界 `wB B`: $\Omega_1$ 分量的界是 $B$, 其余分量取 `LFReBr.w₀` (最小合法世界).

```agda
  F : ⊤ ⊎ HB S⊥ → KS
  F = [ (λ _ → step (Lv lz)) , (λ c → Lv (G c)) ]′

  wB : HB S⊥ → Wd SX
  wB B = [_,_] {C = λ i → Wd (F i)} (λ _ → tt , B) (λ c → w₀ (G c))

  lgwB : ∀ B → LgB B → LgW SX (wB B)
  lgwB B lB (inj₁ _) = tt , lB
  lgwB B lB (inj₂ c) = Lg-w₀ (G c)

  spread : ∀ (g : HB S⊥ → HB SX) → LgB (hΩ Ω₁ g) → ∀ c c′ → LgB c′ → c ⊲[ tt ] c′ → Ment c (g c) → Ment c (g c′)
  spread g (mo , _) c c′ lc′ p m = ment⊲ (mo {wB c′} (lgwB c′ lc′) p hself p) m

  spread-0 : ∀ (g : HB S⊥ → HB SX) → LgB (hΩ Ω₁ g) → Ment hz (g hz) → ∀ c′ → LgB c′ → Ment hz (g c′)
  spread-0 g lg m c′ lc′ = spread g lg hz c′ lc′ (z⊲ᴮ c′) m
```

## §3 "种类都在界之上" 只对界 $0$ 成立

```agda
  AbV : HB S⊥ → HB SX → Set
  AbV b hz = ⊤
  AbV b (hs h) = AbV b h
  AbV b (hl f) = ∀ n → AbV b (f n)
  AbV b (hΩ (inj₁ _ , inj₁ ()) g)
  AbV b (hΩ (inj₁ _ , inj₂ _) g) = ∀ e → AbV b (g e)
  AbV b (hΩ (inj₂ c′ , κ) g) = (b ⊲[ tt ] c′) × (∀ e → AbV b (g e))

  mentAb : ∀ {b c} h → Ment c h → AbV b h → b ⊲[ tt ] c
  mentAb hz () a
  mentAb (hs h) m a = mentAb h m a
  mentAb (hl f) (n , m) a = mentAb (f n) m (a n)
  mentAb (hΩ (inj₁ _ , inj₁ ()) g) m a
  mentAb (hΩ (inj₁ _ , inj₂ _) g) (e , m) a = mentAb (g e) m (a e)
  mentAb (hΩ (inj₂ c′ , κ) g) (inj₁ refl) a = proj₁ a
  mentAb (hΩ (inj₂ c′ , κ) g) (inj₂ (e , m)) a = mentAb (g e) m (proj₂ a e)

  ⊲hz : ∀ {b : HB S⊥} → b ⊲[ tt ] hz → b ≡ hz
  ⊲hz hself = refl

  above-fails : ∀ {b} h → Ment hz h → AbV b h → b ≡ hz
  above-fails h m a = ⊲hz (mentAb h m a)

  s≢z : ¬ (hs {S⊥} hz ≡ hz)
  s≢z ()

  no-AbV-branch : ∀ (g : HB S⊥ → HB SX) → LgB (hΩ Ω₁ g) → Ment hz (g hz) →
                  ∀ c′ → LgB c′ → ¬ AbV (hs hz) (g c′)
  no-AbV-branch g lg m c′ lc′ a = s≢z (above-fails (g c′) (spread-0 g lg m c′ lc′) a)
```

## §4 实例: 累加的合法结点

在 `G₁ c = c+1` 上 (Fab4LOm 的 `G`), 种类 $c$ 是第 $c$ 个分量的新种类 `κ₁ c`, 坐标是第 `ofC c` 层的值, 最小坐标是 $0$.

```agda
open Spread G₁ public using (ment⊲; spread; spread-0; AbV; no-AbV-branch)
open LOm G₁ using (SX; Ω₁; Ment)

kc : HB S⊥ → K SX
kc c = inj₂ c , κ₁ c

gᶜ : HB S⊥ → HB SX
gᶜ hz = hΩ (kc hz) (λ _ → hz)
gᶜ (hs c) = hΩ (kc (hs c)) (λ _ → gᶜ c)
gᶜ (hl f) = hl (λ n → gᶜ (f n))
gᶜ (hΩ () _)

Dᶜ : HB SX
Dᶜ = hΩ Ω₁ gᶜ

-- 单调, 对一切世界
gᶜ-mono : ∀ {w} {c c′ : HB S⊥} → c ⊲[ tt ] c′ → gᶜ c ⊲[ w ] gᶜ c′
gᶜ-mono hself = hself
gᶜ-mono {w} {c′ = hs c″} (hsuc p) = hLim {c = hz} (botBd SX (kc (hs c″)) w) (gᶜ-mono p)
gᶜ-mono (hlim n p) = hlim n (gᶜ-mono p)
gᶜ-mono (hLim {κ = ()} _ _)

Lg-gᶜ : ∀ c → LgB c → LgB (gᶜ c)
Lg-gᶜ hz _ = (λ _ _ _ _ → hself) , (λ _ _ → tt)
Lg-gᶜ (hs c) l = (λ _ _ _ _ → hself) , (λ _ _ → Lg-gᶜ c l)
Lg-gᶜ (hl f) (st , l) = (λ {w} n → gᶜ-mono {w} (st {tt} n)) , (λ n → Lg-gᶜ (f n) (l n))
Lg-gᶜ (hΩ () _) _

Lg-Dᶜ : LgB Dᶜ
Lg-Dᶜ = (λ lw e e′ p → gᶜ-mono p) , (λ c lc → Lg-gᶜ c lc)

ment-g0 : Ment hz (gᶜ hz)
ment-g0 = inj₁ refl

-- 结论的实例: 界 1 下, Dᶜ 没有一个合法分支满足 AbV
inst-no-AbV : ∀ c′ → LgB c′ → ¬ AbV (hs hz) (gᶜ c′)
inst-no-AbV = no-AbV-branch gᶜ Lg-Dᶜ ment-g0
```

## 结论 (按档)

- **[定理]** `Spread.ment⊲`, `wB`, `lgwB`, **`spread`**, `spread-0`, `AbV`, `mentAb`, **`above-fails`**, **`no-AbV-branch`**; 实例 `gᶜ`, `Dᶜ`, `gᶜ-mono`, `Lg-gᶜ`, **`Lg-Dᶜ`**, `ment-g0`, `inst-no-AbV`.
- **[判断]** `Dᶜ` 读 $\sup_c\Omega_{c+1}$; 构造一路的 `PH` 是否是 `AbV` 一类, 待实例.
