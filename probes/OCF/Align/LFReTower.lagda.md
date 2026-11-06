# 层号一次封闭: $\Omega$, 塔, 不动点 (合法性由形状给出)

> 不含记号. 入口 [LFRe](LFRe.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> `Ω̂ : HB SL → HB SL` 是层号的 $x\mapsto\Omega_x$. 后继处 $\Omega_{h+1}=\sup_c(\Omega_h\boxplus c)$, $c$ 过第 $h$ 层的值; 两种极限处字面连续. **合法性是一步定理** `Lg-Ω̂ : ∀ h → LgB h → LgB (Ω̂ h)`: 后继处用 `⊞-fst`, `⊞-⊲`, `Lg-⊞` (和的形状), 极限处用单调 `Ω̂-⊲` (连续的形状, 同 `HtTowerCont.cont-mono`). 不按层写, 不按阶段写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LFReTower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy
```

## §1 $\Omega$

```agda
Ω̂ : HB SL → HB SL
Ω̂ hz = hs hz
Ω̂ (hs h) = hΩ (νL (ofHB h)) (λ c → Ω̂ h ⊞ ιL (ofHB h) (up c))
Ω̂ (hl f) = hl (λ n → Ω̂ (f n))
Ω̂ (hΩ κ g) = hΩ κ (λ c → Ω̂ (g c))

Ω̂-suc : ∀ {W} h → Ω̂ h ⊲[ W ] Ω̂ (hs h)
Ω̂-suc {W} h = hLim (botBd SL (νL (ofHB h)) W) (⊞-fst (Ω̂ h) hz)

Ω̂-⊲ : ∀ {x y W} → x ⊲[ W ] y → Ω̂ x ⊲[ W ] Ω̂ y
Ω̂-⊲ hself = hself
Ω̂-⊲ (hsuc {b = b} p) = ⊲ᴮ-tr (Ω̂-⊲ p) (Ω̂-suc b)
Ω̂-⊲ (hlim n p) = hlim n (Ω̂-⊲ p)
Ω̂-⊲ (hLim e p) = hLim e (Ω̂-⊲ p)
```

后继处的分支: 坐标 $c$ 经 `up` 放进第 `ofHB h` 个分量, 再接在 $\Omega_h$ 后面. 这与 `HtTowerU.Lg-θs` 是同一个证明.

```agda
Lg-Ω̂ : ∀ h → LgB h → LgB (Ω̂ h)
Lg-Ω̂ hz l = tt
Lg-Ω̂ (hs h) l =
  (λ {W} lw e e′ p → ⊞-⊲ (Ω̂ h) (ι-⊲ {LH} {FL} {ofHB h} {w = W} (up-⊲ p))) ,
  (λ c lc → Lg-⊞ (Ω̂ h) (ιL (ofHB h) (up c)) (Lg-Ω̂ h l) (Lg-ι (ofHB h) (up c) (Lg-up c lc)))
Lg-Ω̂ (hl f) (st , l) = (λ n → Ω̂-⊲ (st n)) , (λ n → Lg-Ω̂ (f n) (l n))
Lg-Ω̂ (hΩ κ g) (mo , l) = (λ lw e e′ p → Ω̂-⊲ (mo lw e e′ p)) , (λ c lc → Lg-Ω̂ (g c) (l c lc))
```

## §2 塔与 $\Lambda$

旧文件的 `tw` 原样: $t_0=0$, $t_{n+1}=\Omega_{t_n}$. 相邻项是第一位置由 `Ω̂-⊲` 一步归纳给出 (旧文件靠 `fst`, 这里靠单调). 不需要 `HtTowerU.θ` 那样接在上一项后面: 一切层的新种类在同一个 `SL` 里, `no-naive-diag` 的那种 "各级落在不同的种类结构" 不出现.

```agda
tw : ℕ → HB SL
tw zero = hz
tw (suc n) = Ω̂ (tw n)

tw-st : ∀ {W} n → tw n ⊲[ W ] tw (suc n)
tw-st zero = z⊲ᴮ (hs hz)
tw-st (suc n) = Ω̂-⊲ (tw-st n)

Lg-tw : ∀ n → LgB (tw n)
Lg-tw zero = tt
Lg-tw (suc n) = Lg-Ω̂ (tw n) (Lg-tw n)

Λ : HB SL
Λ = hl tw

Lg-Λ : LgB Λ
Lg-Λ = (λ n → tw-st n) , Lg-tw
```

**不动点的形状.** `Ω̂ Λ` 就是 `hl (tw ∘ suc)`, 是 `refl` (同旧文件 `fix-form`).

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

fix-form : Ω̂ Λ ≡ hl (λ n → tw (suc n))
fix-form = refl
```

## §3 $\Lambda$ 之上

$\Omega_{\Lambda+1}$ 是一个种类 (读回层 `ofHB Λ`), 合法. 下一个不动点: 从合法的 $b$ 出发, $x_{n+1}=x_n\boxplus\Omega_{x_n}$, 取 ℕ-对角 (`fix`). 值上 $x\boxplus\Omega_x=\Omega_x$ 当 $x<\Omega_x$ (判断, 纸面的序数算术); 这里用 ⊞ 是因为 $b$ 不一定是 $\Omega_b$ 的字面第一位置 ($\Lambda+1$ 不是 $\Omega_\Lambda=\Lambda$ 之下的). `Lg-fix` 对一切合法 $b$ 一步.

```agda
ΩΛ+1 : HB SL
ΩΛ+1 = Ω̂ (hs Λ)

Lg-ΩΛ+1 : LgB ΩΛ+1
Lg-ΩΛ+1 = Lg-Ω̂ (hs Λ) Lg-Λ

it : HB SL → ℕ → HB SL
it b zero = b
it b (suc n) = it b n ⊞ Ω̂ (it b n)

Lg-it : ∀ b → LgB b → ∀ n → LgB (it b n)
Lg-it b l zero = l
Lg-it b l (suc n) = Lg-⊞ (it b n) (Ω̂ (it b n)) (Lg-it b l n) (Lg-Ω̂ (it b n) (Lg-it b l n))

fix : HB SL → HB SL
fix b = hl (it b)

Lg-fix : ∀ b → LgB b → LgB (fix b)
Lg-fix b l = (λ n → ⊞-fst (it b n) (Ω̂ (it b n))) , Lg-it b l

-- 第二个不动点, 第 n 个不动点
Λ₂ : HB SL
Λ₂ = fix (hs Λ)

Lg-Λ₂ : LgB Λ₂
Lg-Λ₂ = Lg-fix (hs Λ) Lg-Λ

Λn : ℕ → HB SL
Λn zero = Λ
Λn (suc n) = fix (hs (Λn n))

Lg-Λn : ∀ n → LgB (Λn n)
Lg-Λn zero = Lg-Λ
Lg-Λn (suc n) = Lg-fix (hs (Λn n)) (Lg-Λn n)
```

## §4 旧守卫的反例在这里是第一位置

旧文件 `LevelFixNeg.no-cp-Ω3-Ω2`: $\Omega+3$ 不是 $\Omega\cdot2$ 的字面第一位置, 因为旧的第一位置进 `lc` 只走第一支. 这里进 $\Omega$-节点走世界的界之下的任一坐标: 只要世界在第 0 层的界不小于 $2$, $\Omega+3$ 就是 $\Omega\cdot2=\Omega\boxplus\Omega$ 的第一位置, 坐标就是 $2$ (分支 $\Omega\boxplus(1\boxplus2)$ 字面是 $\Omega+3$). 这正是 `chain-stuck` 要的东西: 链点 (这里是 $\Omega+3$) 在下一个闭包的第一路径上, 由世界给出, 不由守卫给出.

```agda
Ω₁ : HB SL
Ω₁ = tw 2

two : HB (Lv lz)
two = hs (hs hz)

cp-Ω3-Ω2 : ∀ {W} → two ⊲[ proj₁ (W lz) ] proj₂ (W lz) → hs (hs (hs Ω₁)) ⊲[ W ] Ω₁ ⊞ Ω₁
cp-Ω3-Ω2 e = hLim {c = two} e hself
```

**比较.** `cmpB {SL}` (HtTowerTy, 对一切 `S`) 就是这里一切层号的比较, 一条定理, 不按层. 它在 $\Omega$-节点处调用的 `cmpK` 是 `sup`, `step` 的字段, 最终是各层值上的 `cmpB {Lv k}`.

```agda
cmpL : ∀ {a b L W} → a ⊲[ W ] L → b ⊲[ W ] L → LgW SL W → LgB L → (b ⊲[ W ] a) ⊎ (a ⊲[ W ] b)
cmpL = cmpB {SL}
```
