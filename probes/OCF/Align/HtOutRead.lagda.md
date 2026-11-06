# 高度来自折叠的输出 (一): 连续的分支, 第 1 层的读法

> 不含记号. 入口 [HtOut](HtOut.lagda.md). 高度 `H` 与 `LgH` 照搬 [HtFeedTree](HtFeedTree.lagda.md), 不改.
>
> - `Cont g`: $\Omega$-分支 $g:A\to H$ 的两条字段: **极限坐标处字面连续** ($g(\lim f)\equiv\mathrm{hl}(g\circ f)$) 与**后继坐标处步进** ($g\,c\lhd_{[0]} g(c+1)$), 加上起点与后继保合法. `cont→LgH`: 有这两条就 `LgH (hΩ g)`. 一步定理, 参数是任意的 $g$. 沿坐标的**一切**第一位置单调是对路径归纳得到的, 不要坐标合法.
> - `nb b s`: 对坐标结构递归的分支 ($g(0)=b$, $g(c+1)=s\,c\,(g\,c)$, $g(\lim f)=\mathrm{hl}(g\circ f)$). 连续是定义性的 (`refl`). [HtFeedHt](HtFeedHt.lagda.md) 的 `it F x` 是它的特例 (`it-cont`).
> - `rd b x`: 第 1 层的差树 $x$ (`D (hs hz) W`, 折叠在第 1 层目标上的输出类型) 接在高度 $b$ 后面读成高度. `ni` 与 `nκ` 都读成 `hΩ (nb …)`: 坐标 $c$ 上的增量是差树在坐标 $c$ 上的分支. **`Lg-rd`: 读出来一律合法, 前提只有底合法.** `rd-fst`: 底是读出的第一位置 (世界 $0$).
>
> 与已有结果的关系: [HtFeedNeg](HtFeedNeg.lagda.md) 的 `no-weak` 说只有后继步进不够; 这里说**再加极限处的字面连续就够了**, 而 [HtOutNeg](HtOutNeg.lagda.md) 说两条字段各自去掉都有不合法的反例. [BrwHigh](BrwHigh.lagda.md) 判断坐标要改成差树 (`D₀`), 才能沿前缀单调; 在 `H` 里不必: 坐标仍是 `A`, 分支在极限坐标上取 `hl`, 单调对路径归纳. 差树的坐标只在增量里出现一次 (`toD`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtOutRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedHt using (Good; lf; fst; it; it⊲)
```

## §1 高度的加法

只用来让 "第 1 层" 字面地是一个高度的第一位置 (§4 的 `top⁺`).

```agda
infixl 6 _⊞ᴴ_
_⊞ᴴ_ : H → H → H
a ⊞ᴴ hz = a
a ⊞ᴴ hs b = hs (a ⊞ᴴ b)
a ⊞ᴴ hl f = hl (λ n → a ⊞ᴴ f n)
a ⊞ᴴ hΩ g = hΩ (λ c → a ⊞ᴴ g c)

⊞ᴴ-fst : ∀ {W} a b → a ⊲[ W ] a ⊞ᴴ b
⊞ᴴ-fst a hz = hself
⊞ᴴ-fst a (hs b) = hsuc (⊞ᴴ-fst a b)
⊞ᴴ-fst a (hl f) = hlim 0 (⊞ᴴ-fst a (f 0))
⊞ᴴ-fst {W} a (hΩ g) = hLim (z⊲ W) (⊞ᴴ-fst a (g azero))

⊞ᴴ-⊲ : ∀ {W} a {x y} → x ⊲[ W ] y → a ⊞ᴴ x ⊲[ W ] a ⊞ᴴ y
⊞ᴴ-⊲ a hself = hself
⊞ᴴ-⊲ a (hsuc p) = hsuc (⊞ᴴ-⊲ a p)
⊞ᴴ-⊲ a (hlim n p) = hlim n (⊞ᴴ-⊲ a p)
⊞ᴴ-⊲ a (hLim e p) = hLim e (⊞ᴴ-⊲ a p)

Lg-⊞ᴴ : ∀ a b → LgH a → LgH b → LgH (a ⊞ᴴ b)
Lg-⊞ᴴ a hz la lb = la
Lg-⊞ᴴ a (hs b) la lb = Lg-⊞ᴴ a b la lb
Lg-⊞ᴴ a (hl f) la (st , l) = (λ n → ⊞ᴴ-⊲ a (st n)) , (λ n → Lg-⊞ᴴ a (f n) la (l n))
Lg-⊞ᴴ a (hΩ g) la (mo , l) = (λ lc′ p → ⊞ᴴ-⊲ a (mo lc′ p)) , (λ c lc → Lg-⊞ᴴ a (g c) la (l c lc))
```

## §2 连续的分支: 一步定理

`Cont g` 的字段只说 $g$ 在坐标的三个构造子上怎样, 不提折叠, 不提记号. 单调沿坐标的一切第一位置, 对路径归纳: 自身; 后继 (用步进); 极限 (用连续, 再进 `hl` 的第 $n$ 项). 不要坐标合法, 世界是 $0$, 所以搬到一切世界.

```agda
record Cont (g : A → H) : Set where
  constructor ct
  field
    c-lim : ∀ f → g (alim f) ≡ hl (λ n → g (f n))
    c-suc : ∀ c → g c ⊲[ azero ] g (asuc c)
    c-lgz : LgH (g azero)
    c-lgs : ∀ c → LgH (g c) → LgH (g (asuc c))
open Cont public

cont-mono : ∀ {g} → Cont g → ∀ {c c′} → c ⊲ c′ → g c ⊲[ azero ] g c′
cont-mono K C.self = hself
cont-mono K (C.suc p) = ⊲ᴴ-tr (cont-mono K p) (c-suc K _)
cont-mono {g} K {c} (C.lim {f = f} n p) = subst (λ h → g c ⊲[ azero ] h) (sym (c-lim K f)) (hlim n (cont-mono K p))

cont-lg : ∀ {g} → Cont g → ∀ c → Lg c → LgH (g c)
cont-lg K azero _ = c-lgz K
cont-lg K (asuc c) l = c-lgs K c (cont-lg K c l)
cont-lg K (alim f) (st , l) = subst LgH (sym (c-lim K f)) ((λ n → cont-mono K (st n)) , (λ n → cont-lg K (f n) (l n)))

cont→LgH : ∀ {g} → Cont g → LgH (hΩ g)
cont→LgH K = (λ _ p → ⊲ᴴ0 (cont-mono K p)) , cont-lg K
```

## §3 对坐标递归的分支

```agda
nb : H → (A → H → H) → A → H
nb b s azero = b
nb b s (asuc c) = s c (nb b s c)
nb b s (alim f) = hl (λ n → nb b s (f n))

nb-cont : ∀ {b s} → LgH b → (∀ c h → h ⊲[ azero ] s c h) → (∀ c h → LgH h → LgH (s c h)) → Cont (nb b s)
nb-cont {b} {s} lb fs ls = ct (λ f → refl) (λ c → fs c (nb b s c)) lb (λ c → ls c (nb b s c))

-- HtFeedHt 的迭代是特例
it-cont : ∀ {F} → Good F → ∀ x → LgH x → Cont (it F x)
it-cont gF x lx = ct (λ f → refl) (λ c → fst gF _) lx (λ c → lf gF _)
```

## §4 第 1 层的差树读成高度

差树的 `ni` 分支吃第 0 层的差树坐标 (`D₀`), 高度的 $\Omega$-分支吃 `A`. 坐标 $c$ 上要喂一棵 `D₀`, 取 `toD c`: 后继接 `n1`, 极限取 `nl`. **这是选择**: `A` 的极限 $\lim f$ 写成差要相邻项的路径 (`BrwMidZero.dif` 要 `Lg`), 分支是全函数, 拿不到; 所以 `toD` 在极限处取部分和, 值不忠实 (读法里的坐标会变大). 合法性不受影响.

`nκ` 的分支吃世界: 坐标 $c$ 上取世界 $W$ 接 `toD c` (`sum`), 世界的合法与路径都由 `Lg-sum`, `sum-fst` 给出.

```agda
toD : ∀ {W} → A → D₀ W
toD azero = n0
toD (asuc c) = toD c ⨾ n1
toD (alim f) = nl (λ n → toD (f n))

D₁ : A → Set
D₁ = D (hs hz)

rd  : ∀ {W} → Lg W → H → D₁ W → H
rdp : ∀ {W} → Lg W → H → (ℕ → D₁ W) → ℕ → H
rd lW b n0 = b
rd lW b n1 = hs b
rd lW b (x ⨾ y) = rd lW (rd lW b x) y
rd lW b (nl d) = hl (rdp lW b d)
rd lW b (ni (ss hself) u) = hΩ (nb b (λ c h → rd lW h (u C.self lW (toD c))))
rd {W} lW b (nκ _ u) = hΩ (nb b (λ c h → rd (Lg-sum W (toD {azero} c) lW) h (u (sum-fst W (toD {azero} c)) (Lg-sum W (toD {azero} c) lW))))
rd lW b (nw p x) = rd (lg⊲ p lW) b x
rdp lW b d zero = b
rdp lW b d (suc n) = rd lW (rdp lW b d n) (d n)

rd-fst : ∀ {W} (lW : Lg W) b (x : D₁ W) → b ⊲[ azero ] rd lW b x
rd-fst lW b n0 = hself
rd-fst lW b n1 = hsuc hself
rd-fst lW b (x ⨾ y) = ⊲ᴴ-tr (rd-fst lW b x) (rd-fst lW (rd lW b x) y)
rd-fst lW b (nl d) = hlim 0 hself
rd-fst lW b (ni (ss hself) u) = hLim C.self hself
rd-fst lW b (nκ _ u) = hLim C.self hself
rd-fst lW b (nw p x) = rd-fst (lg⊲ p lW) b x
```

**合法性.** 无前提 (只要底合法); 每个 $\Omega$-节点是 `nb-cont` 的一次调用, 再递归到分支.

```agda
Lg-rd  : ∀ {W} (lW : Lg W) b (x : D₁ W) → LgH b → LgH (rd lW b x)
Lg-rdp : ∀ {W} (lW : Lg W) b (d : ℕ → D₁ W) → LgH b → ∀ n → LgH (rdp lW b d n)
Lg-rd lW b n0 l = l
Lg-rd lW b n1 l = l
Lg-rd lW b (x ⨾ y) l = Lg-rd lW (rd lW b x) y (Lg-rd lW b x l)
Lg-rd lW b (nl d) l = (λ n → rd-fst lW (rdp lW b d n) (d n)) , Lg-rdp lW b d l
Lg-rd lW b (ni (ss hself) u) l =
  cont→LgH (nb-cont l (λ c h → rd-fst lW h (u C.self lW (toD c))) (λ c h lh → Lg-rd lW h (u C.self lW (toD c)) lh))
Lg-rd {W} lW b (nκ _ u) l =
  cont→LgH (nb-cont l (λ c h → rd-fst (Lg-sum W (toD {azero} c) lW) h (u (sum-fst W (toD {azero} c)) (Lg-sum W (toD {azero} c) lW)))
                      (λ c h lh → Lg-rd (Lg-sum W (toD {azero} c) lW) h (u (sum-fst W (toD {azero} c)) (Lg-sum W (toD {azero} c) lW)) lh))
Lg-rd lW b (nw p x) l = Lg-rd (lg⊲ p lW) b x l
Lg-rdp lW b d l zero = l
Lg-rdp lW b d l (suc n) = Lg-rd lW (rdp lW b d n) (d n) (Lg-rdp lW b d l n)
```
