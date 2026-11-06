# 结构关系, 第十八轮 (五): 第 $0$ 层的 `RelX⁺` 是传递的

> 不读记号. 入口 [StrRel18](StrRel18.lagda.md). 接口 [StrRel18If](StrRel18If.lagda.md) §3 的 `Trans00`. `StrRel17` 接手清单第 2 项.
>
> 1. **(定理) `canc`**: 布劳威尔树的加法左消去: $c\oplus a\le c\oplus b\Rightarrow a\le b$ (对 $a$, $b$ 的字典序归纳; $a$ 后继而 $b=0$ 的情形由 `irr` 排除).
> 2. **(定理) `admH`**: 领先量 (`Adm`) 横向复合: $\mathrm{Adm}(V_0,V_0';V,V')$ 与 $\mathrm{Adm}(V_0',V_0'';V',V'')$ ⇒ $\mathrm{Adm}(V_0,V_0'';V,V'')$. 两个领先量 $\delta_1\le\delta_2$ 由 `canc` 得到.
> 3. **(定理) `alH`**: 对齐 (`StrRel4Walk.Al`) 横向复合, 中间的路径相同. 对两个推导归纳; 中间路径的形状 (`self`/后继/极限) 排除了不匹配的情形.
> 4. **(定理) `aph`: `StrRel18Up.APH` 成立; 推论 `trans00⁺ : Trans00`** (接口 §3): 第 $0$ 层的 `RelX⁺` 对一切世界传递.
>
> **读法 (判断).** `Up` 的可靠性的一个来源 (`StrRel17` 入口 §3) 现在有了. 它不解决第一个障碍: `Up` 仍要 "上升输出的再折叠 $\le$ 保留输出的再折叠" (`StrRel18Up.UpStep`), 传递性只把两段接起来.
>
> **前提可满足.** 定理都没有前提 (`canc`, `admH`, `alH` 的前提是被复合的数据).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel18Tr where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ≤lim⁻; irr; _⊞_; ≤⊞; ⊞-mono)
open import OCF.Align.KNestAdm using (Adm)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
open import OCF.Align.StrRel12Al using (AP)
open import OCF.Align.StrRel13Val using (Λ₂)
open import OCF.Align.StrRel18Up using (APH; trans00)
open import OCF.Align.StrRel18If Λ₂ tt using (Trans00)
```

## 1 左消去

```agda
canc : ∀ c {a b} → c ⊞ a ≤ c ⊞ b → a ≤ b
canc c {a = azero} h = z≤
canc c {a = alim f} h = l≤ (λ n → canc c (≤-trans (≤l n (≤-refl (c ⊞ f n))) h))
canc c {a = asuc a} {b = azero} h = ⊥-elim (irr c (≤-trans (s≤ (≤⊞ c a)) h))
canc c {a = asuc a} {b = asuc b} (s≤ h) = s≤ (canc c h)
canc c {a = asuc a} {b = alim g} h with ≤lim⁻ h
... | n , h′ = ≤l n (canc c {a = asuc a} {b = g n} h′)
```

## 2 领先量的横向复合

```agda
admH : ∀ {V₀ V₀′ V₀″ V V′ V″} → Adm V₀ V₀′ V V′ → Adm V₀′ V₀″ V′ V″ → Adm V₀ V₀″ V V″
admH {V₀′ = V₀′} {V₀″ = V₀″} (δ₁ , a , a′) (δ₂ , b , b′) =
  δ₁ , a , ≤-trans (⊞-mono (≤-refl V₀″) (canc V₀′ (≤-trans a′ b))) b′
```

## 3 对齐的横向复合

```agda
alH : ∀ {L L′ L″ a b a′ b′ a″ b″} {p : a ⊲ b} {lb : Lg b} {p′ : a′ ⊲ b′} {lb′ : Lg b′} {p″ : a″ ⊲ b″} {lb″ : Lg b″} →
      Al L L′ p lb p′ lb′ → Al L′ L″ p′ lb′ p″ lb″ → Al L L″ p lb p″ lb″
alH (aS p′ lb′) H₂ = aS _ _
alH H₁ (aR H′) = aR (alH H₁ H′)
alH H₁ (aRL H′) = aRL (alH H₁ H′)
alH (aP H c≤ ad) (aP H′ c≤′ ad′) = aP (alH H H′) (≤-trans c≤ c≤′) (admH ad ad′)
alH (aR H) (aP H′ c≤ ad) = aR (alH H H′)
alH (aRL H) (aL H′ G′) = aRL (alH H H′)
alH (aL H G) (aL H′ G′) = aL (alH H H′) (λ m → alH (G m) (G′ m))
```

## 4 `APH` 与传递性

```agda
aph : APH
aph {V′ = V′} {V″ = V″} {l″ = l″} {p′ = p′} {p″ = p″} (H , ad , e₀ , e₀′) (H′ , ad′ , f₀′ , f₀″) e =
  alH H (subst (λ k → Al V′ V″ p′ k p″ l″) (sym e) H′) , admH ad ad′ , e₀ , f₀″

trans00⁺ : Trans00
trans00⁺ = trans00 aph
```
