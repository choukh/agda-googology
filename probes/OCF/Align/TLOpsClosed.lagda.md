# 树的算子语言 (十一): 闭项

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 全部无参数, 无假设. 下面的读法都是判断, 只有 `T₀`, `TΩ` 在 [TLOpsAccept](TLOpsAccept.lagda.md) 有定理. 世界前缀在 `Tᵖ` 里, 见 [TLOpsPre](TLOpsPre.lagda.md); `Top`, `Feed` 的最外层闭包没有前缀.
>
> **生成原则**: 高度与层都是 $A$. 字面合法的 $A$ 由 `azero`, `asuc`, `alim` 写出, 也可以读回折叠的输出 (`lit`). 新一站不需要新构造子, 不需要新的闭包定理.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
import OCF.Free.Level as FL
open FL using (HS; FGH)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg; _⊲_; z⊲; lg⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (Ord₀; Lit₀; lit; g; lg; rd; El)
open import OCF.Align.TLOpsW using (one; g₀; Gw; gw)
open import OCF.Align.TLOpsPre using (Tᵖ; HS-Tᵖ; Lit-Tᵖ)
open import OCF.Align.TLOpsClo using (module Top; module Feed)
```

## §1 三条旧定理在这里的位置

一条定理: `HS-Tᵖ` (`ψW` 加 `C′`). `Ω̇-inst` 对应 `OCF/Free/Main.GᴺΩ̇` ($p=1$), `Tᵠ-inst` 对应 `LadderOrdMain.GᴺTᵠ` (高度任意). `Gν` 对应 `Feed` ([TLOpsAbs](TLOpsAbs.lagda.md) 给出它们共用的迭代). 树不是旧树, 差在世界前缀和基本列的第 0 项, 见 [TLOpsTest](TLOpsTest.lagda.md).

```agda
-- ψ₀(Ω_{Ω+η})
Ω̇-inst : ∀ η (g : Gw η) → HS (Tᵖ one η η tt g C.self)
Ω̇-inst η g = HS-Tᵖ one η η tt g C.self

-- ψ₀(Ω_{Ω·p+α})
Tᵠ-inst : ∀ p α (lp : Lg p) (g : Gw α) → HS (Tᵖ p α α lp g C.self)
Tᵠ-inst p α lp g = HS-Tᵖ p α α lp g C.self

-- ψ₀(Ω_{Ω·p})
Tp : ∀ p → Lg p → Ord₀
Tp p lp = Tᵖ p azero one lp g₀ (z⊲ one)

HS-Tp : ∀ p (lp : Lg p) → HS (Tp p lp)
HS-Tp p lp = HS-Tᵖ p azero one lp g₀ (z⊲ one)
```

## §2 闭项

```agda
two : A
two = asuc one

nat : ℕ → A
nat zero = azero
nat (suc n) = asuc (nat n)

lnat : ∀ n → Lg (nat n)
lnat zero = tt
lnat (suc n) = lnat n

ωA : A
ωA = alim nat

lω : Lg ωA
lω = (λ n → C.suc C.self) , lnat

-- ω + n, ω·2, ...
ω+ : A → ℕ → A
ω+ a zero = a
ω+ a (suc n) = asuc (ω+ a n)

lω+ : ∀ {a} → Lg a → ∀ n → Lg (ω+ a n)
lω+ l zero = l
lω+ l (suc n) = lω+ l n

ω·2 : A
ω·2 = alim (ω+ ωA)

lω·2 : Lg ω·2
lω·2 = (λ n → C.suc C.self) , lω+ lω

-- ψ₀(Ω_{Ω·2}), ψ₀(Ω_{Ω·ω}), ψ₀(Ω_{Ω·ω·2})
T·2 T·ω T·ω2 : Ord₀
T·2 = Tp two tt
T·ω = Tp ωA lω
T·ω2 = Tp ω·2 lω·2

HS·2 : HS T·2
HS·2 = HS-Tp two tt

HS·ω : HS T·ω
HS·ω = HS-Tp ωA lω

HS·ω2 : HS T·ω2
HS·ω2 = HS-Tp ω·2 lω·2

-- 把输出读回作高度: 这里没有新东西, 只是 lit
T-fed : (y : Ord₀) → Lit₀ y → Ord₀
T-fed y ly = Tp (g (lit y ly)) (lg (lit y ly))

HS-fed : (y : Ord₀) (ly : Lit₀ y) → HS (T-fed y ly)
HS-fed y ly = HS-Tp (g (lit y ly)) (lg (lit y ly))

T₀₁ : Ord₀
T₀₁ = Tᵖ azero one one tt g₀ C.self

-- ψ₀(Ω_{Ω·ε₀}): 高度是 ψ₀(Ω₁) 的读出
T·ε₀ : Ord₀
T·ε₀ = T-fed T₀₁ (Lit-Tᵖ azero one one tt g₀ C.self)

-- ψ₀(Ω_Ω), 顶层闭包, 没有前缀
TΩ : Ord₀
TΩ = Top.T azero tt

-- ψ₀(Ω_{Ω²}), 回灌作高度, 最外层没有前缀
T⊤′ : Ord₀
T⊤′ = Feed.T

HS⊤′ : HS T⊤′
HS⊤′ = Feed.HS-T

lv⊤′ : FL.Ordᴵ
lv⊤′ = Feed.lv

fgh⊤′ : ℕ → ℕ
fgh⊤′ = FGH T⊤′
```
