# `T⁺` 对输入单调, 否定一路 (三): 互模拟的输入与函数外延; 合法性证明不是命题

> 不含记号. 入口 [NegTpMono](NegTpMono.lagda.md). 接口 [TpMonoIf](TpMonoIf.lagda.md) 的 (a) `SimInv` 与一步律里的 `LgIrr`.
>
> 1. **`l₁≢l₂`** (定理): 合法性 `LgB` 不是命题. 同一个高度 $h_2=\mathrm{hl}\,f_2$ ($f_2(0)=0$, $f_2(n+1)=\mathrm{hl}(\lambda\_.0)$) 有两个合法性证明, 第 0 步的路径分别走极限的第 0 项与第 1 项. `T⁺` 的类型 `(h : Ht) → LgB h → A` 读合法性证明 (折叠里 `rkT` 经 `cmpB … lΛ` 用它), 所以 `LgIrr` 不是平凡的.
> 2. **`sim→irr`** (定理): `SimInv F → LgIrr F` (取 $b=a$, 互模拟取自反).
> 3. **`fe-irr→sim`** (**条件**: 前提 `Funext`): `Funext → LgIrr F → SimInv F`. 证明: 有外延时互模拟推出相等 (`≈→≡`), 剩下的正是 `LgIrr`. 合起来: **有 `Funext` 时 (a) 恰好等价于 `LgIrr`; 外延只能消掉 "输入不同" 那一半, 消不掉 "合法性证明不同" 那一半** (第 1 条: 即使有外延, `LgB` 也不是命题, 所以 `LgIrr` 仍要对折叠证). 没有 `Funext` 时 (a) 能否不经外延证出: 本路没有否定, 判断能 (要的是两个实例上折叠的互模拟, 与 `MonoPort8Sim.Two` 同形; `TpMonoToy` 与 `NegTpMonoBlind` 的模型都不用外延就满足 (a)), 所以**不需要外延** 是判断, 不是定理.
> 4. **`collapse`, `collapse₀`** (条件定理, 前提 `SimInv T⁺`): 接口的 (a) 对 `T⁺` 成立时, `Tᴰ₊` 的每一项 $t_k$ 与 `T-Ω₂` 在值上互相 $\le$ (由 `TdPlusVal.in-suc`, `DiagK3Zero.pr₀-top` 的互模拟). 这把 `TdPlusVal` 里 "若互模拟输入上 `T⁺` 的值相等, 则每个 $t_k$ 读 $\psi_0(\Omega_{\Omega_2})$" 的判断变成以 (a) 为前提的定理: 构造一路要证的 (a) 一旦证出, `Tᴰ₊` 就在值上逐项退成 `T-Ω₂`. 不是否定, 是 (a) 的一个后果.
>
> `Funext` 只作前提出现 (`fe-irr→sim`, `≈→≡`), 标 "条件".
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegTpMonoSim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂)
open import OCF.Align.HtTowerFClosed using (Ω₂ᴴ; lΩ₂; T-Ω₂)
open import OCF.Align.TpMonoIf
open import OCF.Align.DiagK3Zero using (≈z; ≈s; ≈l; ≈Ω; t₀; pr₀; pr₀-top; lλ₀; Lg-pr₀)
open import OCF.Align.DiagKTop using (λh; Lg-λh)
open import OCF.Align.TdPlusFold using (prL; Lg-prL)
open import OCF.Align.TdPlusVal using (t₊; in-suc)
```

## §1 合法性证明不是命题

```agda
f₂ : ℕ → Ht
f₂ zero = hz
f₂ (suc n) = hl (λ _ → hz)

h₂ : Ht
h₂ = hl f₂

st₁ st₂ : ∀ {w} n → f₂ n ⊲[ w ] f₂ (suc n)
st₁ zero = hlim 0 hself
st₁ (suc n) = hself
st₂ zero = hlim 1 hself
st₂ (suc n) = hself

lf₂ : ∀ n → LgB (f₂ n)
lf₂ zero = tt
lf₂ (suc n) = (λ m → hself) , (λ m → tt)

l₁ l₂ : LgB h₂
l₁ = st₁ , lf₂
l₂ = st₂ , lf₂

w₀ : Wd₂
w₀ = azero , hz

l₁≢l₂ : ¬ (l₁ ≡ l₂)
l₁≢l₂ e with cong (λ l → proj₁ l {w₀} 0) e
... | ()
```

## §2 (a) 与 `LgIrr`

```agda
≈-refl : ∀ {S} (x : HB S) → x ≈ x
≈-refl hz = ≈z
≈-refl (hs x) = ≈s (≈-refl x)
≈-refl (hl f) = ≈l (λ n → ≈-refl (f n))
≈-refl (hΩ κ g) = ≈Ω (λ c → ≈-refl (g c))

≈-sym : ∀ {S} {x y : HB S} → x ≈ y → y ≈ x
≈-sym ≈z = ≈z
≈-sym (≈s p) = ≈s (≈-sym p)
≈-sym (≈l p) = ≈l (λ n → ≈-sym (p n))
≈-sym (≈Ω p) = ≈Ω (λ c → ≈-sym (p c))

sim→irr : ∀ {F : Fn} → SimInv F → LgIrr F
sim→irr s a la la′ = s a la a la′ (≈-refl a)

-- 条件: 函数外延 (只作前提)
Funext : Set₁
Funext = ∀ {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g

≈→≡ : Funext → ∀ {S} {x y : HB S} → x ≈ y → x ≡ y
≈→≡ fe ≈z = refl
≈→≡ fe (≈s p) = cong hs (≈→≡ fe p)
≈→≡ fe (≈l p) = cong hl (fe (λ n → ≈→≡ fe (p n)))
≈→≡ fe (≈Ω {κ = κ} p) = cong (hΩ κ) (fe (λ c → ≈→≡ fe (p c)))

fe-irr→sim : Funext → ∀ {F : Fn} → LgIrr F → SimInv F
fe-irr→sim fe {F} irr a la b lb e with ≈→≡ fe e
... | refl = irr a la lb
```

## §3 (a) 的一个后果: `Tᴰ₊` 逐项退成 `T-Ω₂`

```agda
collapse : SimInv T⁺ → ∀ k → (t₊ (suc k) ≤ T-Ω₂) × (T-Ω₂ ≤ t₊ (suc k))
collapse s k =
  s (prL (suc (suc k)) (λh (suc k))) (Lg-prL (suc (suc k)) (λh (suc k)) (Lg-λh (suc k))) Ω₂ᴴ lΩ₂ (in-suc k) ,
  s Ω₂ᴴ lΩ₂ (prL (suc (suc k)) (λh (suc k))) (Lg-prL (suc (suc k)) (λh (suc k)) (Lg-λh (suc k))) (≈-sym (in-suc k))

collapse₀ : SimInv T⁺ → (t₀ ≤ T-Ω₂) × (T-Ω₂ ≤ t₀)
collapse₀ s =
  s (pr₀ (λh 0)) (Lg-pr₀ (λh 0) lλ₀) Ω₂ᴴ lΩ₂ pr₀-top ,
  s Ω₂ᴴ lΩ₂ (pr₀ (λh 0)) (Lg-pr₀ (λh 0) lλ₀) (≈-sym pr₀-top)
```
