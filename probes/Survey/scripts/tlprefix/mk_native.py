import sys
SP=sys.argv[1]
s=open(SP+'/n/N1.agda',encoding='utf8').read()
a=s.index('data A : Set')
b=s.index('-- 骨架: 折叠与单调互递归')
body=s[a:b]
head='''# 前缀 (五): 合法性做进定义, 到哪一步

> 入口 [TLPrefix](TLPrefix.lagda.md). **判决: PARTIAL.** 不含记号, 不读证书. 这是作者的理想形态的探针: 不累加, 没有单独的合法性证明, 证据就在树的 `lim` 里.
>
> **编译过的.**
>
> - `A`, `_⊲_`: 下标的极限自带字面第一位置, 没有 `Lg`. `from`, `Lg-from`: 读成带 `Lg` 的下标.
> - `Str`, `O`: 数据树分层定义, `ol` 带 `⊴`, `oi` 带分支单调和分支同余. 过了正性和停机检查. 朴素的写法过不了, 报错在 [TLPrefix](TLPrefix.lagda.md).
> - `Ω̇`, `Ω⊴`, `Ω≈`: 证据和树一起造, 互递归. `Ω̇ (alim f st)` 的步进就是 `Ω⊴ (st n)`. 对照 `Certified.Ω-not-step`: 那里相邻两项不 `⊑`, 这里是 `⊴`, 不是同一个关系.
> - `ord`, `HS-ord`: **第 0 层的 `HS` 不要 `WF`.** 证据就在 `ol` 里.
>
> **没有的: 折叠 `ψ`.** 骨架的停机报错在 [TLPrefix](TLPrefix.lagda.md). 未走通, 不是否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLPrefixNative where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Free.Level as FL
open FL using (HS; hz; hs; hl; _⊑⁰_; _≅_; ≺s; ≺l; z≅; s≅; l≅; ≅→⊑; Ordᶜ)
import OCF.Align.CumReadCF as C
```

## §1 下标

```agda
'''
body=body.replace("module Str (L : A)","```\n\n## §2 分层的数据树\n\n证据的关系是参数, 所以正性检查只看到参数, 看不到低层的 `O` 在箭头左边.\n\n```agda\nmodule Str (L : A)")
body=body.replace("O : A → Set\nVs : ∀ L","```\n\n## §3 层, 关系, $\\Omega$\n\n```agda\nO : A → Set\nVs : ∀ L")
tail=r'''```

## §4 第 0 层: 合法由定义保证

`O azero` 只有 `o0`, `os`, `ol`. 它就是证据在 `lim` 里的第 0 层树.

```agda
Ord₀ : Set
Ord₀ = Ordᶜ FL.zero

ord : O azero → Ord₀
ord o0 = FL.zero
ord (os x) = FL.suc (ord x)
ord (ol F st) = FL.lim (λ n → ord (F n))
ord (oi () h m c)
ord (oe () x)

≈→≅ : (x y : O azero) → x ≈ y → ord x ≅ ord y
≈→≅ o0 o0 e = z≅
≈→≅ (os x) (os y) e = s≅ (≈→≅ x y e)
≈→≅ (ol F st) (ol G st′) e = l≅ (λ n → ≈→≅ (F n) (G n) (e n))
≈→≅ (oi () h m c) y e
≈→≅ (oe () x) y e
≈→≅ o0 (oi () h m c) e
≈→≅ o0 (oe () y) e
≈→≅ (os x) (oi () h m c) e
≈→≅ (os x) (oe () y) e
≈→≅ (ol F st) (oi () h m c) e
≈→≅ (ol F st) (oe () y) e

⊴→⊑⁰ : {x y : O azero} → x ⊴ y → ord x ⊑⁰ ord y
⊴→⊑⁰ {x} {y} (rf e) = ≅→⊑ (≈→≅ x y e)
⊴→⊑⁰ (s d) c = ≺s (⊴→⊑⁰ d c)
⊴→⊑⁰ (l n d) c = ≺l n (⊴→⊑⁰ d c)
⊴→⊑⁰ (nd {r = ()} d)
⊴→⊑⁰ (ee {R = ()} d)

-- 没有 WF: 证据就在树里
HS-ord : (x : O azero) → HS (ord x)
HS-ord o0 = hz
HS-ord (os x) = hs (HS-ord x)
HS-ord (ol F st) = hl (λ n → HS-ord (F n)) (λ n → ⊴→⊑⁰ (st n))
HS-ord (oi () h m c)
HS-ord (oe () x)
```

## §5 读成带 `Lg` 的下标

```agda
from : A → C.A
from⊲ : ∀ {a b} → a ⊲ b → from a C.⊲ from b
from azero = C.azero
from (asuc a) = C.asuc (from a)
from (alim f st) = C.alim (λ n → from (f n))
from⊲ self = C.self
from⊲ (suc P) = C.suc (from⊲ P)
from⊲ (lim n P) = C.lim n (from⊲ P)

Lg-from : ∀ a → C.Lg (from a)
Lg-from azero = tt
Lg-from (asuc a) = Lg-from a
Lg-from (alim f st) = (λ n → from⊲ (st n)) , (λ n → Lg-from (f n))
```
'''
open('TLPrefixNative.lagda.md','w',encoding='utf8').write(head+body+tail)
