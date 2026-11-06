# 带类型折叠的 sup 层: 折叠与形状给出的合法

> 不含记号. 入口 [TySup](TySup.lagda.md), 接口 [TySupIf](TySupIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 对任一满足接口的 `R` 一条定义. `Φ X a lX t pt b h`: 把层号 $X$ 的高度 $h$ 折到目标层 $t$ (`pt : t ⊑ X`), 当前界 $b$ 是第 $t$ 层的值. 输出的类型就是第 $t$ 层的值 `HB (L t)`. 对 $\Omega$-结点按 `dec` 分三种:
>
> - **留**: 结点原样, 种类换成 $t$ 层里的种类, 分支递归.
> - **同层**: 坍缩成链的 ℕ-极限, 与 [Fab3Typed](Fab3Typed.lagda.md) 的 `chain` 同式: $d_0=k\,b$, $d_{n+1}=d_n\boxplus k\,(b\boxplus d_n)$, $k\,b'=\Phi_{t,b'}(g\,b')$. 链点就是输出, 回灌是恒等 (实例里 `to` 是恒等, `TySup.feed-id`).
> - **在上**: 种类的层号 $i$ 高于 $t$. 先在第 $i$ 层坍缩: 链从第 $i$ 层的地板 `top i` 起, 分支折到目标 $i$; 得到第 $i$ 层的值, 再整个从 $i$ 折到 $t$ (对可达性递归, $i\sqsubset X$).
>
> 这是 Fab3Typed 的 "折叠复合 `fold n = Ψ ∘ … ∘ Ψ`" 在没有顶种类时的写法: 复合的次序改为**每个结点就地**先折到自己的层再往下.
>
> **ℕ-极限改为累加 (代价, 如实).** `Φ (hl f) = hl (Σ (Φ ∘ f))`, 部分和 $\Phi f_0, \Phi f_0\boxplus\Phi f_1, \dots$. 于是输出的每个 ℕ-极限的相邻项字面是第一位置 (`⊞-fst`), 合法由形状给出, 对一切输入 (`Sh-Φ`, 不要输入合法, 不要单调). 不累加时需要的单调 $a\lhd h\Rightarrow\Phi\,a\lhd\Phi\,h$ 在 "在上" 处要比较 "直接折到 $t$" 与 "先折到 $i$ 再折到 $t$" 两种折法的输出, 那是字面不同的两棵树; 这一条本篇**未找到**证明 (判断, 不是否定). 累加改变值: 对相邻项值相等的 ℕ-极限, 累加得到 $x\cdot\omega$ 而不是 $x$; 对按值递增且加法主项的序列两者相同 (判断, 纸面). 累加会给基本列带来毛刺 (作者 11-04), 这里记账, 不称更自然.
>
> 层号的合法 `LgC X` 只在 `dec` 里用 (比较的公共上界), 高度的合法一处也不用.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.TySupIf
module OCF.Align.TySupFold (R : TySupIf) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)
open import OCF.Align.HtTowerTy using (KS; K; E; HB; hz; hs; hl; hΩ; Wd; _⊲[_]_; _⊞_; ⊞-fst; ⊞-⊲)
open TySupIf R
```

## §1 链, 累加, 乘 ω

对一切种类结构 `S`. `chain b k` 即 Fab3Typed 的 `chain`, 只是世界只剩界 $b$ (其余世界分量折叠不读).

```agda
module _ {S : KS} where
  mul : HB S → ℕ → HB S
  mul x zero = x
  mul x (suc n) = mul x n ⊞ x

  chain : HB S → (HB S → HB S) → ℕ → HB S
  chain b k zero = k b
  chain b k (suc n) = chain b k n ⊞ k (b ⊞ chain b k n)

  Σ⁺ : (ℕ → HB S) → ℕ → HB S
  Σ⁺ f zero = f 0
  Σ⁺ f (suc n) = Σ⁺ f n ⊞ f (suc n)
```

## §2 折叠

对可达性 `a` 与高度字典序递归: 留与同层对高度的子项 (`g c`) 递归, 在上对可达性的子项 (`rs i pi`) 递归. 三种情形写成 `caseDc` 的三个延续, 递归调用留在 `Φ` 自己的子句里 (同 Fab3Typed 的延续写法), 检查器看得见子项.

```agda
caseDc : ∀ {X t κ} {B : Set} → Dc L _⊏_ _⊑_ X t κ →
         ((κ′ : K (L t)) → (E (L t) κ′ → E (L X) κ) → B) →
         ((HB (L t) → E (L X) κ) → B) →
         ((i : C) → i ⊏ X → t ⊑ i → (HB (L i) → E (L X) κ) → B) → B
caseDc (keep κ′ fr) k s ab = k κ′ fr
caseDc (same to) k s ab = s to
caseDc (above i pi q to) k s ab = ab i pi q to

Φ : ∀ X → AccR _⊏_ X → LgC X → ∀ t → t ⊑ X → HB (L t) → HB (L X) → HB (L t)
Φ X (acc rs) lX t pt b hz = hs hz
Φ X (acc rs) lX t pt b (hs h) = hl (mul (Φ X (acc rs) lX t pt b h))
Φ X (acc rs) lX t pt b (hl f) = hl (Σ⁺ (λ n → Φ X (acc rs) lX t pt b (f n)))
Φ X (acc rs) lX t pt b (hΩ κ g) = caseDc (dec X t pt lX κ)
  (λ κ′ fr → hΩ κ′ (λ c → Φ X (acc rs) lX t pt b (g (fr c))))
  (λ to → hl (chain b (λ b′ → Φ X (acc rs) lX t pt b′ (g (to b′)))))
  (λ i pi q to → Φ i (rs i pi) (lgC↓ pi lX) t q b
     (hl (chain (top i) (λ b′ → Φ X (acc rs) lX i (⊏→⊑ pi) b′ (g (to b′))))))
```

## §3 形状给出的合法

`Sh`: ℕ-极限的相邻项在一切世界里是第一位置, 遗传; $\Omega$-结点只要求分支遗传 (不要单调). 在没有种类的层上它就是 `LgB` (`TySup.sh→lgB`).

```agda
module _ {S : KS} where
  Sh : HB S → Set
  Sh hz = ⊤
  Sh (hs h) = Sh h
  Sh (hl f) = (∀ {w : Wd S} n → f n ⊲[ w ] f (suc n)) × (∀ n → Sh (f n))
  Sh (hΩ κ g) = ∀ c → Sh (g c)

  Sh-⊞ : ∀ a b → Sh a → Sh b → Sh (a ⊞ b)
  Sh-⊞ a hz sa sb = sa
  Sh-⊞ a (hs b) sa sb = Sh-⊞ a b sa sb
  Sh-⊞ a (hl f) sa (st , sf) = (λ n → ⊞-⊲ a (st n)) , (λ n → Sh-⊞ a (f n) sa (sf n))
  Sh-⊞ a (hΩ κ g) sa sg = λ c → Sh-⊞ a (g c) sa (sg c)

  Sh-mul : ∀ x → Sh x → ∀ n → Sh (mul x n)
  Sh-mul x s zero = s
  Sh-mul x s (suc n) = Sh-⊞ (mul x n) x (Sh-mul x s n) s

  Sh-mulL : ∀ x → Sh x → Sh (hl (mul x))
  Sh-mulL x s = (λ n → ⊞-fst (mul x n) x) , Sh-mul x s

  Sh-chain : ∀ b k → (∀ b′ → Sh (k b′)) → Sh (hl (chain b k))
  Sh-chain b k sk = (λ n → ⊞-fst (chain b k n) (k (b ⊞ chain b k n))) , go
    where
    go : ∀ n → Sh (chain b k n)
    go zero = sk b
    go (suc n) = Sh-⊞ _ _ (go n) (sk _)

  Sh-Σ : ∀ f → (∀ n → Sh (f n)) → Sh (hl (Σ⁺ f))
  Sh-Σ f sf = (λ n → ⊞-fst (Σ⁺ f n) (f (suc n))) , go
    where
    go : ∀ n → Sh (Σ⁺ f n)
    go zero = sf 0
    go (suc n) = Sh-⊞ _ _ (go n) (sf (suc n))
```

**定理 (一步, 对一切 `R`, 一切输入).** 折叠的输出由形状合法. 证明的递归与 `Φ` 的递归相同.

```agda
Sh-case : ∀ {X t κ} {S : KS} (d : Dc L _⊏_ _⊑_ X t κ) {k s ab} →
          (∀ κ′ fr → Sh {S} (k κ′ fr)) → (∀ to → Sh {S} (s to)) → (∀ i pi q to → Sh {S} (ab i pi q to)) →
          Sh (caseDc d k s ab)
Sh-case (keep κ′ fr) sk ss sa = sk κ′ fr
Sh-case (same to) sk ss sa = ss to
Sh-case (above i pi q to) sk ss sa = sa i pi q to

Sh-Φ : ∀ X a lX t pt b h → Sh (Φ X a lX t pt b h)
Sh-Φ X (acc rs) lX t pt b hz = tt
Sh-Φ X (acc rs) lX t pt b (hs h) = Sh-mulL _ (Sh-Φ X (acc rs) lX t pt b h)
Sh-Φ X (acc rs) lX t pt b (hl f) = Sh-Σ _ (λ n → Sh-Φ X (acc rs) lX t pt b (f n))
Sh-Φ X (acc rs) lX t pt b (hΩ κ g) = Sh-case (dec X t pt lX κ)
  (λ κ′ fr c → Sh-Φ X (acc rs) lX t pt b (g (fr c)))
  (λ to → Sh-chain b _ (λ b′ → Sh-Φ X (acc rs) lX t pt b′ (g (to b′))))
  (λ i pi q to → Sh-Φ i (rs i pi) (lgC↓ pi lX) t q b
     (hl (chain (top i) (λ b′ → Φ X (acc rs) lX i (⊏→⊑ pi) b′ (g (to b′))))))
```
