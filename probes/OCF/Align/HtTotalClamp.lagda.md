# 折叠对一切高度有定义 (二): 夹成合法, 回灌成全函数

> 不含记号. 入口 [HtTotal](HtTotal.lagda.md). [HtTotalNeg](HtTotalNeg.lagda.md) 说: 夹法在合法处是恒等推出 LPO (`no-clamp`), 不要合法性的比较在合法坐标上有效也推出 LPO (`no-valid`, `no-agree`). 所以全有定义的折叠不能在一切合法高度上与原来的相同 (否则 LPO). 这里取第一种: 夹法 `cl` 在合法处也挪动, 挪动的方式只用树上现成的第一位置运算.
>
> - `cl`: 对高度结构递归. $0$, 后继原样; $\mathbb N$-极限 $\lim f$ 换成部分和 $\lim_n(\mathrm{cl}\,f_0\boxplus\cdots\boxplus\mathrm{cl}\,f_n)$; $\Omega$-极限 $\mathrm{h\Omega}\,g$ 换成沿坐标的部分和 `nb (cl (g 0)) (λ c h → h ⊞ cl (g (c+1)))` (极限坐标处连续). `⊞ᴴ` 是现成的保证 "$a$ 是 $a\boxplus b$ 的第一位置" 的运算 (`⊞ᴴ-fst`; 这里没有现成的第一位置的并), 所以单调由形状给出.
> - **`Lg-cl`: 对一切高度, `cl h` 合法.** 无前提. 极限处是 `⊞ᴴ-fst`, $\Omega$-极限处是 `cont→LgH` 的一次调用.
> - `TΛᶜ h = TΛ (cl h) _`: 闭项对一切高度有定义. `Fbᶜ h = rd (h+1) (out₁ (cl h) _)`: 回灌对一切高度有定义; 底仍是 $h+1$, 只有折叠的最高层被夹.
> - **`Good-rd`**: 底取 $h+1$ 的任何读法都满足 `HtFeedHt.Good` (合法性只要底合法, 第一位置由 `rd-fst`), 所以 `Fbᶜ` 是 `Good` (`Good-Fbᶜ`), `HtFeedHt` 的 $\Omega$-迭代与一切变换都能用在它上面 ([HtTotalIter](HtTotalIter.lagda.md)). `rd-n0`: 输出取空树时就是后继, 所以 `Good` 本身不带强度.
> - 一致: **`cl-fin`, `TΛᶜ-fin`, `agree-fin`**: 在有限高度上 `cl` 是恒等, `TΛᶜ`, `Fbᶜ` 与 `TΛ`, `Fb` 相等 (`≡`, 不用 `Funext`). 不一致: **`cl-moves`**: 合法的 $\omega$ 被挪动 (第 2 支 $3\ne2$).
>
> 累加的账 (判断, 两边都记): 好处是全有定义而不另写折叠, 比较仍是合法最高层上的 `cmpH`, 判定有效. 代价是值: 部分和在可加主数的上升列上不改上确界, 别处会变大 (例: $\lim_n(\Omega+n)$ 的部分和极限是 $\Omega\cdot\omega$, 不是 $\Omega+\omega$; $\Omega$-分支 $c\mapsto\Omega+c$ 的部分和是 $\Omega^2$ 那一档, 不是 $\Omega\cdot2$). 所以 `Fbᶜ` 在合法高度上读 $h\mapsto\psi_1(\Omega_{1+\mathrm{cl}\,h})$, 不低于 `Fb` 的读法 $\psi_1(\Omega_{1+h})$, 两者的差没有定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTotalClamp where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; ⊲ᴴ-tr; LgH; D; n0)
open import OCF.Align.HtFeedHt using (Good; gd)
open import OCF.Align.HtFeedClosed using (TΛ; Lg-TΛ; one)
open import OCF.Align.HtOutRead using (_⊞ᴴ_; ⊞ᴴ-fst; Lg-⊞ᴴ; nb; nb-cont; cont→LgH; D₁; rd; rd-fst; Lg-rd)
open import OCF.Align.HtOutFeed using (out₁; Fb)
```

## §1 夹法

```agda
cl  : H → H
clp : (ℕ → H) → ℕ → H
cl hz = hz
cl (hs h) = hs (cl h)
cl (hl f) = hl (clp f)
cl (hΩ g) = hΩ (nb (cl (g azero)) (λ c h → h ⊞ᴴ cl (g (asuc c))))
clp f zero = cl (f zero)
clp f (suc n) = clp f n ⊞ᴴ cl (f (suc n))

Lg-cl  : ∀ h → LgH (cl h)
Lg-clp : ∀ f n → LgH (clp f n)
Lg-cl hz = tt
Lg-cl (hs h) = Lg-cl h
Lg-cl (hl f) = (λ n → ⊞ᴴ-fst (clp f n) (cl (f (suc n)))) , Lg-clp f
Lg-cl (hΩ g) =
  cont→LgH (nb-cont (Lg-cl (g azero)) (λ c h → ⊞ᴴ-fst h (cl (g (asuc c))))
                    (λ c h lh → Lg-⊞ᴴ h (cl (g (asuc c))) lh (Lg-cl (g (asuc c)))))
Lg-clp f zero = Lg-cl (f zero)
Lg-clp f (suc n) = Lg-⊞ᴴ (clp f n) (cl (f (suc n))) (Lg-clp f n) (Lg-cl (f (suc n)))
```

**有限高度上是恒等; 合法的 $\omega$ 被挪动.**

```agda
fin : ℕ → H
fin zero = hz
fin (suc n) = hs (fin n)

cl-fin : ∀ n → cl (fin n) ≡ fin n
cl-fin zero = refl
cl-fin (suc n) = cong hs (cl-fin n)

Lg-fin : ∀ n → LgH (fin n)
Lg-fin zero = tt
Lg-fin (suc n) = Lg-fin n

-- 有限高度的合法性证明只有一个
Lg-fin-prop : ∀ n (a b : LgH (fin n)) → a ≡ b
Lg-fin-prop zero a b = refl
Lg-fin-prop (suc n) a b = Lg-fin-prop n a b

ωᴴ : H
ωᴴ = hl fin

Lg-ωᴴ : LgH ωᴴ
Lg-ωᴴ = (λ n → hsuc hself) , Lg-fin

br2 : H → H
br2 (hl f) = f 2
br2 _ = hz

cl-moves : ¬ (cl ωᴴ ≡ ωᴴ)
cl-moves e with cong br2 e
... | ()
```

## §2 对一切高度的闭项与回灌

```agda
TΛᶜ : H → A
TΛᶜ h = TΛ (cl h) (Lg-cl h)

Lg-TΛᶜ : ∀ h → Lg (TΛᶜ h)
Lg-TΛᶜ h = Lg-TΛ (cl h) (Lg-cl h)

Fbᶜ : H → H
Fbᶜ h = rd tt (hs h) (out₁ (cl h) (Lg-cl h))
```

**合法性不看折叠.** 底取 $h+1$, 读什么差树都 `Good`.

```agda
Good-rd : (x : H → D₁ one) → Good (λ h → rd tt (hs h) (x h))
Good-rd x = gd (λ h lh → Lg-rd tt (hs h) (x h) lh) (λ h → ⊲ᴴ-tr (hsuc hself) (rd-fst tt (hs h) (x h)))

-- 输出取空树: 回灌就是后继; Good 不带强度
rd-n0 : ∀ h → rd {one} tt (hs h) n0 ≡ hs h
rd-n0 h = refl

Good-Fbᶜ : Good Fbᶜ
Good-Fbᶜ = Good-rd (λ h → out₁ (cl h) (Lg-cl h))

fbᶜ-fst : ∀ h → hs h ⊲[ azero ] Fbᶜ h
fbᶜ-fst h = rd-fst tt (hs h) (out₁ (cl h) (Lg-cl h))
```

## §3 在有限高度上与原来相等

```agda
ap-Lg : ∀ {B : Set} (F : (h : H) → LgH h → B) {x y} (e : x ≡ y) (lx : LgH x) (ly : LgH y) → subst LgH e lx ≡ ly → F x lx ≡ F y ly
ap-Lg F refl lx ly p = cong (F _) p

TΛᶜ-fin : ∀ n (l : LgH (fin n)) → TΛᶜ (fin n) ≡ TΛ (fin n) l
TΛᶜ-fin n l = ap-Lg TΛ (cl-fin n) (Lg-cl (fin n)) l (Lg-fin-prop n _ l)

agree-fin : ∀ n (l : LgH (fin n)) → Fbᶜ (fin n) ≡ proj₁ (Fb (fin n , l))
agree-fin n l = ap-Lg (λ h lh → rd tt (hs (fin n)) (out₁ h lh)) (cl-fin n) (Lg-cl (fin n)) l (Lg-fin-prop n _ l)
```
