# 序数高度: 编译过的否定

> **判决: 六条否定都编译过, 只否定写明的陈述.** 结论写在 [LadderOrd](LadderOrd.lagda.md).
>
> | 定理 | 陈述 | 只否定什么 | 前提可满足吗 |
> | --- | --- | --- | --- |
> | `viewE→LPO` | 若每个 `m : Ordᴵ` 都有写法 (`ViewE`: 下面没有东西, 闭包, 或链), 则 LPO | 不带证书的 `Ordᴵ` 字面作高度, **改 `View` 加一个 "空" 情形也不行**. 这更正了上一轮 "修 `View` 就能绕开" 的判断 | `viewE-val`: 码的值 `val M` 都有写法. 带证书的子类型上成立 |
> | `no-tri-code` | 码的全局三歧是假的 (按值比较, 相等是 $\equiv$) | 跨 $M$ 的比较 (`¬tri` 在码上的同形). 不否定固定 $M$ 内的 `<ᴾ-tri` | 固定 $M$ 时成立 |
> | `no-step²` | `view-step` 对 `HB ω²ᶜ` 的顶的链是假的 | `HtS` 的这个字段, 不否定 $\omega^2$ 作高度 (`Gω²`) | 不适用 |
> | `no-all-Ord` | 一个 `HtB` 不能字面忠实地含全部 `Ordᴵ` (推出 $\bot$) | 单一的高度类型. 不否定 `HB M` | 前提 `emb` 不可满足, 这就是结论 |
> | `all-Ord→LPO` | 一个 `HtB` 含全部 `Ordᴵ`, 只要求忠实到值, 也推出 LPO | 同上, 值的版本 | 同上 |
> | `no-cofinal` | 没有 $M$ 使位置的秩穷尽 `Ordᴵ` | `HB M` 的秩穷尽 `Ordᴵ`. 定理到此为止; "所以 `HB M` 没有 Ω-共尾元, 壁垒定理的前提不被触发" 是由此作的判断 (壁垒说的是 `Ordᴰ`) | 不适用 |
>
> LPO 不是矛盾, 所以 `viewE→LPO`, `all-Ord→LPO` 说的是: 这条路线不能无公理地写出, 与壁垒定理同一个意义.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _≅ᴵ_; _≺ᴵ_; via; _⊑ᴵ_; z⊑; s⊑; z≅; l≅; ≺ᴵ-irrefl; ≺ᴵ-trans; ≅ᴵ-refl; <-≅)
open import OCF.Align.LadderOrdBase using (HtB; Tri; tlt; teq; tgt; clos)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ωᶜ; ω²ᶜ; _≼_; l≼; l≼ʳ)
open import OCF.Align.LadderInfOrd using (ωᴼ; ω′ᴼ; nl)
```

## §1 不带证书的 `Ordᴵ`: 写法推出 LPO

```agda
LPO : Set
LPO = (h : ℕ → Bool) → (Σ ℕ λ n → h n ≡ true) ⊎ (∀ n → h n ≡ false)

data ViewE (m : Ordᴵ) : Set where
  emp   : (∀ c → c <ᴵ m → ⊥) → ViewE m
  clos  : ∀ {n} → n <ᴵ m → ViewE m
  chain : (F : ℕ → Ordᴵ) → (∀ i → F i <ᴵ m) → ViewE m

any : (ℕ → Bool) → ℕ → Bool
any h zero = h 0
any h (suc n) = any h n ∨ h (suc n)

b2o : Bool → Ordᴵ
b2o false = zero
b2o true = suc zero

b-step : ∀ x y → b2o x ⊑ᴵ b2o (x ∨ y)
b-step false y = z⊑
b-step true y = s⊑ z≅ zero

𝕋 : (ℕ → Bool) → Ordᴵ
𝕋 h = lim (λ n → b2o (any h n)) (λ n → b-step (any h n) (h (suc n)))

any-true : ∀ h n → any h n ≡ true → Σ ℕ λ j → h j ≡ true
any-true h zero e = 0 , e
any-true h (suc n) e with any h n in x | h (suc n) in y
... | true | _ = any-true h n x
... | false | true = suc n , y

true-any : ∀ h n → h n ≡ true → any h n ≡ true
true-any h zero e = e
true-any h (suc n) e rewrite e with any h n
... | true = refl
... | false = refl

b-below : ∀ x {c} → c <ᴵ b2o x → x ≡ true
b-below true q = refl

viewE→LPO : (∀ m → ViewE m) → LPO
viewE→LPO v h = go (has (v (𝕋 h)))
  where
  has : ViewE (𝕋 h) → (Σ Ordᴵ λ c → c <ᴵ 𝕋 h) ⊎ (∀ c → c <ᴵ 𝕋 h → ⊥)
  has (emp x) = inj₂ x
  has (clos {n} q) = inj₁ (n , q)
  has (chain F qs) = inj₁ (F 0 , qs 0)
  go : (Σ Ordᴵ λ c → c <ᴵ 𝕋 h) ⊎ (∀ c → c <ᴵ 𝕋 h → ⊥) → (Σ ℕ λ n → h n ≡ true) ⊎ (∀ n → h n ≡ false)
  go (inj₁ (c , lim n q)) = inj₁ (any-true h n (b-below (any h n) q))
  go (inj₂ no) = inj₂ fls
    where
    pos : ∀ n x → any h n ≡ x → b2o x ≡ b2o (any h n)
    pos n x refl = refl
    fls : ∀ n → h n ≡ false
    fls n with h n in e
    ... | false = refl
    ... | true = ⊥-elim (no zero (lim n (subst (λ x → zero <ᴵ b2o x) (sym′ (true-any h n e)) zero)))
      where
      sym′ : ∀ {a b : Bool} → a ≡ b → b ≡ a
      sym′ refl = refl

-- 前提在码的值上成立: 这才是带证书的子类型
viewE-val : ∀ M → ViewE (val M)
viewE-val cz = emp (λ c ())
viewE-val (cs M) = clos zero
viewE-val (cl g) = chain (Sb zero g) (λ i → lim (suc i) (le< (Sb zero g i) (g i)))
```

## §2 码的全局三歧

`ωᶜ` 与 `ω′` 的值相同 (判断), 但都是极限, 彼此下面只有有限数, 而且字面不等.

```agda
g′ : ℕ → Code
g′ zero = cs cz
g′ (suc j) = cz

ω′ : Code
ω′ = cl g′

data Fin′ : Ordᴵ → Set where
  fz′ : Fin′ zero
  fs′ : ∀ {a} → Fin′ a → Fin′ (suc a)

no-lim : ∀ {x f s} → Fin′ x → lim f s <ᴵ x → ⊥
no-lim (fs′ h) (suc q) = no-lim h q
no-lim (fs′ ()) zero

Fin-Sbω : ∀ i → Fin′ (Sb zero (λ _ → cz) i)
Fin-Sbω zero = fz′
Fin-Sbω (suc i) = fs′ (Fin-Sbω i)

Fin-Sbω′ : ∀ i → Fin′ (Sb zero g′ i)
Fin-Sbω′ zero = fz′
Fin-Sbω′ (suc zero) = fs′ (fs′ fz′)
Fin-Sbω′ (suc (suc i)) = fs′ (Fin-Sbω′ (suc i))

_<ᶜ_ : Code → Code → Set
a <ᶜ b = val a <ᴵ val b

no-tri-code : (∀ a b → Tri _<ᶜ_ a b) → ⊥
no-tri-code t with t ωᶜ ω′
... | tlt (lim n q) = no-lim (Fin-Sbω′ n) q
... | tgt (lim n q) = no-lim (Fin-Sbω n) q
... | teq e with cong (λ { (cl g) → g 0 ; _ → cz }) e
...   | ()
```

## §3 壁垒的前提不被触发

位置的秩都低于 `suc (val M)`, 所以 `HB M` 不穷尽 `Ordᴵ`. 判断: 里面没有 Ω-共尾元, 也不以 `Ordᴰ` 为精确初始段.

```agda
rk-bound : ∀ M (p : Pos (cs M)) → rkP zero p <ᴵ suc (val M)
rk-bound M p = rkP<plus zero p

no-cofinal : ∀ M → (∀ η → Σ (Pos (cs M)) λ p → η ≅ᴵ rkP zero p) → ⊥
no-cofinal M f with f (suc (val M))
... | p , e = ≺ᴵ-irrefl (via e (rk-bound M p))
```

## §4 `view-step` 在 $\omega^2$ 上是假的

`HtS` 的字段 `view-step` 要链的下一项是上一项的闭包. 码 `ω²ᶜ` 的顶的链, 第 1 项自己是链. 所以 `HB ω²ᶜ` 不是 `HtS`, 也说明克隆里只改 `mono-rowL` 是必需的.

```agda
P₀ P₁ : Pos (cs ω²ᶜ)
P₀ = low (blk 0 end)
P₁ = low (blk 1 end)

no-step² : (Σ (P₀ <ᴾ P₁) λ r → HtB.view (HB ω²ᶜ) P₁ ≡ clos {n = P₀} r) → ⊥
no-step² (r , ())
```

## §5 一个 `HtB` 装不下全部 `Ordᴵ`

这是目标 4 的编译过的部分. 把全部 `Ordᴵ` 放进同一个高度结构, 三歧就直接打架: 忠实到字面是矛盾 (`no-all-Ord`), 只忠实到值是 LPO (`all-Ord→LPO`). 不需要 Ω-共尾元. 所以每个 `HB M` 只是 $M$ 之下的段, 不同 $M$ 之间不比较, 这是必须的. 这两条不否定 "按 $M$ 分段", 也不否定用链逐段走到更高的办法; 它们只否定单一的高度类型.

```agda
no-all-Ord : (𝔹 : HtB) (emb : Ordᴵ → HtB.Ht 𝔹) →
             (∀ {a b} → HtB._<ᴸ_ 𝔹 (emb a) (emb b) → a ≺ᴵ b) → (∀ {a b} → emb a ≡ emb b → a ≅ᴵ b) → ⊥
no-all-Ord 𝔹 emb rl re with HtB.tri 𝔹 (emb ωᴼ) (emb ω′ᴼ)
... | tlt x with rl x
...   | via (l≅ h) (lim n q) = nl (suc n) q
no-all-Ord 𝔹 emb rl re | teq x with re x
...   | l≅ h with h 0
...     | ()
no-all-Ord 𝔹 emb rl re | tgt x with rl x
...   | via (l≅ h) (lim n q) = nl n q

all-Ord→LPO : (𝔹 : HtB) (emb : Ordᴵ → HtB.Ht 𝔹) →
              (∀ {a b} → HtB._<ᴸ_ 𝔹 (emb a) (emb b) → suc a ≼ b) → (∀ {a b} → emb a ≡ emb b → a ≼ b) → LPO
all-Ord→LPO 𝔹 emb rl re h with HtB.tri 𝔹 (emb (𝕋 h)) (emb zero)
... | tlt x = ⊥-elim (s≼0 (rl x))
  where
  s≼0 : ∀ {a} → suc a ≼ zero → ⊥
  s≼0 ()
... | teq x = inj₂ (fls (re x))
  where
  o≼0 : suc zero ≼ zero → ⊥
  o≼0 ()
  fls : 𝕋 h ≼ zero → ∀ n → h n ≡ false
  fls (l≼ k) n with h n in e
  ... | false = refl
  ... | true = ⊥-elim (o≼0 (subst (λ x → b2o x ≼ zero) (true-any h n e) (k n)))
... | tgt x = inj₁ (ex (rl x))
  where
  o≼0 : suc zero ≼ zero → ⊥
  o≼0 ()
  ex : suc zero ≼ 𝕋 h → Σ ℕ λ j → h j ≡ true
  ex (l≼ʳ n y) with any h n in e
  ... | true = any-true h n e
  ... | false = ⊥-elim (o≼0 y)
```
