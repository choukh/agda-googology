# 严格列 (六): 序数值验收

> 入口 [TLCode](TLCode.lagda.md). **判决: PARTIAL (编译过的部分无条件).** 这是验收文件, 导入 `LadderOrdPos`, `LadderOrdCode`, `LadderOrdClosed`, 不读记号. 比较的是同一高度上的树, 结果都比 "互相 `≼`" 强: 计值 $\cong$, FGH 逐点相等.
>
> | 定理 | 陈述 |
> | --- | --- |
> | `Lω·k~`, `Lω²~`, `acc-ω·2`, `acc-ω²` | 字面的列 `ω·2ᴸ`, `ω²ᴸ` 与码 `ω·ᶜ 1`, `ω²ᶜ` 逐块同形, 对一切位置, 一切 $\alpha$ 计值 $\cong$ |
> | `lv-shape M`, `acc M p α`, `lv-exact M` | **一切旧码进新世界:** `Lv M : Lit (lv₀ M)`, 块形同形, 树 $\cong$, 高度的值与 `val M` 互相 `≼` |
> | `acc-ω^ω`, `acc-ε₀`, `acc-feed` | 上一条在 `ω^ωᶜ`, `ε₀ᶜ`, `η*` 上的实例, 对象是已有的 `Tω^ω`, `Tε₀`, `T-feed` |
> | `sh~`, `new⊂old`, `Lit-val` | **一切新码进旧世界:** 块形读成码, 树 $\cong$, 码的值与 $t$ 互相 `≼` |
> | `Str→Lit`, `Str→Lit-val` | 带证书 `Str` 的 $\eta$ 有 `Lit` 的码, 值互相 `≼`. 所以 `Lit` 不比 `Str` 窄 |
> | `no-~ω^ω` | 字面的列 `ω^ωᴸ` (`E ωᴵ`) 与码 `ω^ωᶜ` **不**同形: 那个码的块带 `+1` |
>
> **没有的.** `Tω^ωᴸ`, `Tε₀ᴸ` 与已有的 `Tω^ω`, `Tε₀` 的比较. `no-~ω^ω` 说明这座桥过不去, 它只否定逐块同形这个办法. 要比较得处理基本列错位 (块末的行错开), 这正是 [EmbVV](EmbVV.lagda.md) 第一个障碍的第 2 条. 未走通, 不是否定. `acc-ω^ω`, `acc-ε₀` 用的是 `Lv`, 列里带分隔符 `suc`, 这是为了对上旧码的基本列, 不是证书的要求.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeAccept where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level hiding (up; sim; acc)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.TLCodeShape using (Sh; sz; ss; sl; end)
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeLe
open import OCF.Align.TLCodeArith
open import OCF.Align.TLCodeCert
open import OCF.Align.TLCodeBridge
open import OCF.Align.LadderOrdPos using (Code; cz; cs; cl; plus; Sb; val)
open import OCF.Align.LadderOrdCode using (ωᶜ; ω·ᶜ; ω²ᶜ; ω^ᶜ; ω^ωᶜ; ε₀ᶜ; _ᶜ+_) renaming (_≼_ to _≼ᵒ_; z≼ to z≼ᵒ; s≼ to s≼ᵒ; s≼ʳ to s≼ʳᵒ; l≼ to l≼ᵒ; l≼ʳ to l≼ʳᵒ)
open import OCF.Align.LadderOrdStr using (Str; code; code-val)
open import OCF.Align.LadderOrdCert using (Gᵖ)
open import OCF.Align.LadderOrdClosed using (Tω·2; Tω²; Tω^ω; Tε₀; T-feed; η*)
```

## §1 字面的列 $\omega\cdot k$, $\omega^2$

```agda
Lω~ : shape Lω ~ ωᶜ
Lω~ = ~l (λ { zero → ~z ; (suc i) → ~z })

+ω~ : ∀ {a M} (h : Lit a) → shape h ~ M → shape (L+ω h) ~ M ᶜ+ ωᶜ
+ω~ h r = ~l (λ { zero → r ; (suc i) → ~z })

Lω·k~ : ∀ k → shape (Lω· k) ~ ω·ᶜ k
Lω·k~ zero = Lω~
Lω·k~ (suc k) = +ω~ (Lω· k) (Lω·k~ k)

abv+ω~ : ∀ {a} (h : Lit a) → above (L+ω h) (lim 1 zero) ~ ωᶜ
abv+ω~ h = ~l (λ { zero → ~z ; (suc i) → ~z })

Lω²~ : shape Lω² ~ ω²ᶜ
Lω²~ = ~l (λ { zero → Lω~ ; (suc i) → abv+ω~ (Lω· (i + 0)) })

module B·2 = Br Lω·2 (Lω·k~ 1)
module B²  = Br Lω² Lω²~

acc-ω·2 : Tω·2ᴸ ≅ Tω·2
acc-ω·2 = B·2.val≅ end zero

acc-ω² : Tω²ᴸ ≅ Tω²
acc-ω² = B².val≅ end zero
```

## §2 旧码进新世界

`lv b c` 是 $b+c$, 列取块的结束点 $P_j$. 这里有分隔符 `suc`: $P_{j+1}=(P_j+1)+g_{j+1}$, 这是旧码的 $\sum_j(g_j+1)$, 只在这个文件里.

```agda
lv : Ordᴵ → Code → Ordᴵ
Pv : Ordᴵ → (ℕ → Code) → ℕ → Ordᴵ
<lv : ∀ b c {x} → x <ᴵ b → x <ᴵ lv b c
Pv< : ∀ b g j → Pv b g j <ᴵ Pv b g (suc j)
lv b cz = b
lv b (cs c) = suc (lv b c)
lv b (cl g) = limᴸ (Pv b g) (Pv< b g)
Pv b g zero = lv b (g 0)
Pv b g (suc j) = lv (suc (Pv b g j)) (g (suc j))
<lv b cz q = q
<lv b (cs c) q = suc (<lv b c q)
<lv b (cl g) q = lim 0 (<lv b (g 0) q)
Pv< b g j = <lv (suc (Pv b g j)) (g (suc j)) zero

Lvb : ∀ {b} → Lit b → ∀ c → Lit (lv b c)
LPv : ∀ {b} → Lit b → ∀ g j → Lit (Pv b g j)
Lvb hb cz = hb
Lvb hb (cs c) = ls (Lvb hb c)
Lvb {b} hb (cl g) = ll (LPv hb g) (Pv< b g)
LPv hb g zero = Lvb hb (g 0)
LPv hb g (suc j) = Lvb (ls (LPv hb g j)) (g (suc j))

lv₀ : Code → Ordᴵ
lv₀ = lv zero

Lv : ∀ M → Lit (lv₀ M)
Lv = Lvb lz

above~ : ∀ {x} (hx : Lit x) c → above (Lvb (ls hx) c) (<lv (suc x) c zero) ~ c
tail~ : ∀ {b} (hb : Lit b) g k i → k ≡ i → above (LPv hb g (suc k)) (Pv< b g k) ~ g (suc i)
above~ hx cz = ~z
above~ hx (cs c) = ~s (above~ hx c)
above~ hx (cl g) = ~l (λ { zero → above~ hx (g 0) ; (suc i) → tail~ (ls hx) g (i + 0) i (+-identityʳ i) })
tail~ hb g k .k refl = above~ (LPv hb g k) (g (suc k))

lv-shape : ∀ M → shape (Lv M) ~ M
lv-shape cz = ~z
lv-shape (cs c) = ~s (lv-shape c)
lv-shape (cl g) = ~l (λ { zero → lv-shape (g 0) ; (suc i) → tail~ lz g (i + 0) i (+-identityʳ i) })

module BL (M : Code) = Br (Lv M) (lv-shape M)

acc : ∀ M (p : Ptᴸ (Lv M)) (α : Ordᴵ) → forceᴺ _ (Gᴸ (Lv M) p α) ≅ forceᴺ _ (Gᵖ M (BL.u M p) α)
acc M = BL.val≅ M

acc-ω^ω : forceᴺ _ (Gᴸ (Lv ω^ωᶜ) end zero) ≅ Tω^ω
acc-ω^ω = acc ω^ωᶜ end zero

acc-ε₀ : forceᴺ _ (Gᴸ (Lv ε₀ᶜ) end zero) ≅ Tε₀
acc-ε₀ = acc ε₀ᶜ end zero

acc-feed : forceᴺ _ (Gᴸ (Lv η*) end zero) ≅ T-feed
acc-feed = acc η* end zero
```

## §3 值

```agda
plus-mono : ∀ c {b b′} → b ≼ b′ → plus b c ≼ plus b′ c
Sb-mono : ∀ g j {b b′} → b ≼ b′ → Sb b g j ≼ Sb b′ g j
plus-mono cz x = x
plus-mono (cs c) x = s≼ (plus-mono c x)
plus-mono (cl g) x = l≼ (λ n → l≼ʳ n (Sb-mono g n x))
Sb-mono g zero x = x
Sb-mono g (suc j) x = s≼ (plus-mono (g j) (Sb-mono g j x))

≼-lv : ∀ b c → b ≼ lv b c
≼-lv b cz = ≼-refl b
≼-lv b (cs c) = s≼ʳ (≼-lv b c)
≼-lv b (cl g) = l≼ʳ 0 (≼-lv b (g 0))

lv-val : ∀ b c → Eqv (lv b c) (plus b c)
Pv-val : ∀ b g j → Eqv (Pv b g j) (plus (Sb b g j) (g j))
lv-val b cz = ≼-refl b , ≼-refl b
lv-val b (cs c) = s≼ (proj₁ (lv-val b c)) , s≼ (proj₂ (lv-val b c))
lv-val b (cl g) = l≼ up , l≼ dn
  where
  up : ∀ n → Pv b g n ≼ plus b (cl g)
  up n = l≼ʳ (suc n) (s≼ʳ (proj₁ (Pv-val b g n)))
  dn : ∀ n → Sb b g n ≼ lv b (cl g)
  dn zero = l≼ʳ 0 (≼-lv b (g 0))
  dn (suc n) = l≼ʳ (suc n) (≼-trans (s≼ (proj₂ (Pv-val b g n))) (<→s≼ (Pv< b g n)))
Pv-val b g zero = lv-val b (g 0)
Pv-val b g (suc j) =
  ≼-trans (proj₁ (lv-val (suc (Pv b g j)) (g (suc j)))) (plus-mono (g (suc j)) (s≼ (proj₁ (Pv-val b g j))))
  , ≼-trans (plus-mono (g (suc j)) (s≼ (proj₂ (Pv-val b g j)))) (proj₂ (lv-val (suc (Pv b g j)) (g (suc j))))

lv-exact : ∀ M → Eqv (lv₀ M) (val M)
lv-exact = lv-val zero
```

## §4 新码进旧世界

```agda
toC : Sh → Code
toC sz = cz
toC (ss s) = cs (toC s)
toC (sl g) = cl (λ i → toC (g i))

sh~ : ∀ s → s ~ toC s
sh~ sz = ~z
sh~ (ss s) = ~s (sh~ s)
sh~ (sl g) = ~l (λ i → sh~ (g i))

module new⊂old {t} (h : Lit t) = Br h (sh~ (shape h))

st≼0 : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n ≼ f (suc n)) → ∀ j → f 0 ≼ f j
st≼0 st zero = ≼-refl _
st≼0 st (suc j) = ≼-trans (st≼0 st j) (st j)

f≼+ : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n ≼ f (suc n)) → ∀ j n → f n ≼ f (n + j)
f≼+ st j zero = st≼0 st j
f≼+ {f} st j (suc n) = f≼+ {λ i → f (suc i)} (λ i → st (suc i)) j n

-- 块形读成码, 值就是 t
above-val : ∀ {a t} (h : Lit t) (q : a <ᴵ t) → Eqv (plus (suc a) (toC (above h q))) t
tail-val : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} (hf : ∀ n → Lit (f n)) (hr : ∀ n → f n <ᴵ f (suc n)) j c₀ b → b ≼ f j → Eqv (plus b (toC c₀)) (f j) →
           Eqv (plus b (toC (sl (tailb hf hr j c₀)))) (lim f s)
above-val (ls h) zero = ≼-refl _ , ≼-refl _
above-val (ls h) (suc q) = s≼ (proj₁ (above-val h q)) , s≼ (proj₂ (above-val h q))
above-val (ll hf hr) (lim j q) = tail-val hf hr j (above (hf j) q) (suc _) (<→s≼ q) (above-val (hf j) q)
tail-val {f} {s} hf hr j c₀ b bj e₀ = l≼ up , l≼ dn
  where
  G : ℕ → Code
  G i = toC (tailb hf hr j c₀ i)
  S : ℕ → Ordᴵ
  S = Sb b G
  st : ∀ n → f n ≼ f (suc n)
  st n = ≼-trans (s≼ʳ (≼-refl _)) (<→s≼ (hr n))
  -- 第 i+1 项就是 f (i+j) 的后继
  Si : ∀ i → Eqv (S (suc i)) (suc (f (i + j)))
  Si zero = s≼ (proj₁ e₀) , s≼ (proj₂ e₀)
  Si (suc i) =
    let A = above-val (hf (suc i + j)) (hr (i + j))
    in s≼ (≼-trans (plus-mono _ (proj₁ (Si i))) (proj₁ A))
     , s≼ (≼-trans (proj₂ A) (plus-mono _ (proj₂ (Si i))))
  up : ∀ n → S n ≼ lim f s
  up zero = l≼ʳ j bj
  up (suc n) = ≼-trans (proj₁ (Si n)) (l≼ʳ (suc (n + j)) (<→s≼ (hr (n + j))))
  dn : ∀ n → f n ≼ plus b (toC (sl (tailb hf hr j c₀)))
  dn n = l≼ʳ (suc n) (≼-trans (≼-trans (f≼+ st j n) (s≼ʳ (≼-refl _))) (proj₂ (Si n)))

Lit-val : ∀ {t} (h : Lit t) → Eqv (val (toC (shape h))) t
Lit-val lz = z≼ , z≼
Lit-val (ls h) = s≼ (proj₁ (Lit-val h)) , s≼ (proj₂ (Lit-val h))
Lit-val (ll hf hr) = tail-val hf hr 0 (shape (hf 0)) zero z≼ (Lit-val (hf 0))
```

## §5 `Str` 不比 `Lit` 宽

```agda
old→new : ∀ {a b} → a ≼ᵒ b → a ≼ b
old→new z≼ᵒ = z≼
old→new (s≼ᵒ x) = s≼ (old→new x)
old→new (s≼ʳᵒ x) = s≼ʳ (old→new x)
old→new (l≼ᵒ h) = l≼ (λ n → old→new (h n))
old→new (l≼ʳᵒ n x) = l≼ʳ n (old→new x)

Str→Lit : ∀ {η} (h : Str η) → Lit (lv₀ (code h))
Str→Lit h = Lv (code h)

Str→Lit-val : ∀ {η} (h : Str η) → Eqv (lv₀ (code h)) η
Str→Lit-val h =
  ≼-trans (proj₁ (lv-exact (code h))) (old→new (proj₁ (code-val h)))
  , ≼-trans (old→new (proj₂ (code-val h))) (proj₂ (lv-exact (code h)))
```

## §6 字面的 $\omega^\omega$ 与旧码不同形

`ω^ᶜ 1` 的块是 `cs cz` (每块两个点), 列是 $1,3,5,\dots$; `E 1` 的列是 $1,2,3,\dots$, 块 $1$ 高于切点的部分是空的. 只否定逐块同形这个办法.

```agda
no-~ω^ω : shape Lω^ω ~ ω^ωᶜ → ⊥
no-~ω^ω (~l R) with R 1
... | ~l Q with Q 0
...   | ()
```
