# 种类塔上的一级折叠, 否定一路 (三): 世界塔, 读回分量的世界, 极限站

> 不含记号. 入口 [NegKcFold](NegKcFold.lagda.md). 对着接口 [KcFoldIf](KcFoldIf.lagda.md) ("接口定稿 2026-11-05", 变更记录: 无) 写, 导入它, 不另造接口. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 UIP; 函数外延 `FEA` (只对 $\mathbb N\to A$, 来自 `NegLvRdLay`) 只在 §4 作前提, 用到它的结论标 "条件".
>
> 接口的 `WTower` 只管 `inj₁ tt` 分量 (旧站的种类): 后一站的这个分量在前一站的世界之上. 读回注入的分量 `inj₂ c` (`LvKtIf.injL c` 的种类就在这里) 的世界不受约束.
>
> 1. **`WTower` 不排除基世界 (定理, `baseW`, `base-only`).** 每站取码的基世界 `w0 (ckc s)` 就是 `WTower` 的实例 (`grow` 是 `≤w-rf`, 定义相等). 它上面 `LvW` 的每个 $\Omega$-结点只剩底支 (`base-only`, 由 `NegLvKtCopy.only-botK`).
> 2. **旧站分量长高, 读回分量仍可以是基世界 (定理, `mixW`, `mix-sees`, `mix-inj`, `mix-LvW`).** `mixW`: 第 0 站世界取 $1$, 以后 `inj₁ tt` 分量取上一站, `inj₂ c` 分量取基世界. 它不是基世界 (`mix-sees`: 旧站的底种类看得见坐标 $1$, `oneK s` 是 $1$ 在第 $s$ 站的写法), 但一切读回分量的种类只剩底坐标 (`mix-inj`), `LvW` 在以读回种类为头的 $\Omega$-结点上只剩底支 (`mix-LvW`). 一般形 `injBase-only`: 任一世界的 `inj₂ c` 分量是基世界, 那里的种类就只有底坐标. 所以 "不取 `w0`" 必须落在读回分量上, `WTower` 的律没有说.
> 3. **极限站的世界由世界塔相干地给出 (定理, 出口).** `limW T s = aW T s` 合法 (`lg-limW`), 嵌入拷贝的界由 `grow` 推出 (`lim-emb`). 对照 `NegLvKtCopy.no-emb→`: 那是对一切合法世界; 对世界塔造出的世界, 这一个方向成立. 所以嫌疑 (iv) "极限站撞 `code-botK`" **不是**接口的后果: 极限站的世界随世界塔, 世界塔不是基世界时极限站也不是.
> 4. **读回分量的世界 "恰好看见外层可入的分支" 撞分离子 (定理; 条件到 WLPO).** 读回分量的世界是层号 $\Omega$-结点的**裸坐标**上的函数 (`Wd (Lev (hΩ κ g)) = Π x. Wd (Lev (g x))`). `SeeExact a ρ`: 外层可入的坐标处界非零, 不可入处界为零. `seeExact-sep`: 一个世界 $\rho$ 满足 `SeeExact ωA ρ` 就推出分离子; `seeExact→WLPO` (条件 `FEA`). 两半各自可满足 (`see⁺`, `see⁻`). 这是 `ColimWNeg.raiseA-sep` / `NegLvRdLay.decAcc-sep` 的形状落在读回分量的世界上: 带公共上界的判定是定理 (`NegKcFoldDec`), 但世界的分量以裸坐标为下标, 没有公共上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NegKcFoldTower where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.LvKtCode using (CdK; cdLev; w0; lw0)
open import OCF.Align.LvKtIf
open import OCF.Align.KcFoldIf
open import OCF.Align.NegLvKtCopy using (only-botK; only-botLev)
open import OCF.Align.ColimWNeg using (WLPO; isz; t≢f)
open import OCF.Align.NegLvRdLay using (ωA; xα; lem; allF; FEA; xα≡)
open WTower
```

## §1 基世界是世界塔

```agda
baseW : WTower
baseW = record { aW = λ s → w0 (ckc s) ; laW = λ s → lw0 (ckc s) ; grow = λ s → ≤w-rf (Kc s) }

base-only : ∀ s (κ : K (Kc s)) (g : E (Kc s) κ → HB (Kc s)) (k : K (LvW (aW baseW s) (hΩ κ g))) →
  proj₁ (proj₁ k) ≡ bot (Kc s) κ
base-only s κ g ((x , e) , _) = only-botK s κ x e
```

## §2 旧站分量长高, 读回分量是基世界

```agda
wNx : ∀ {𝕂 : KS} → Wd 𝕂 → (i : ⊤ ⊎ HB 𝕂) → Wd (FN 𝕂 i)
wNx a (inj₁ _) = a
wNx a (inj₂ c) = w0 (cdLev c)

lwNx : ∀ {𝕂 : KS} {a : Wd 𝕂} → LgW 𝕂 a → (i : ⊤ ⊎ HB 𝕂) → LgW (FN 𝕂 i) (wNx a i)
lwNx la (inj₁ _) = la
lwNx la (inj₂ c) = lw0 (cdLev c)

one : A
one = asuc azero

aM : ∀ s → Wd (Kc s)
aM zero = one
aM (suc s) = wNx (aM s)

laM : ∀ s → LgW (Kc s) (aM s)
laM zero = tt
laM (suc s) = lwNx (laM s)

mixW : WTower
mixW = record { aW = aM ; laW = laM ; grow = λ s → ≤w-rf (Kc s) }

-- 不是基世界: 每一站旧的底种类看得见坐标 1
κ₀ : ∀ s → K (Kc s)
κ₀ zero = tt
κ₀ (suc s) = inj₁ tt , κ₀ s

oneK : ∀ s → E (Kc s) (κ₀ s)
oneK zero = one
oneK (suc s) = oneK s

mix-sees : ∀ s → Bd (Kc s) (κ₀ s) (oneK s) (aW mixW s)
mix-sees zero = C.self
mix-sees (suc s) = mix-sees s

-- 读回分量: 只有底坐标
injBase-only : ∀ {𝕂 : KS} (a : Wd (nxt 𝕂)) (c : HB 𝕂) → a (inj₂ c) ≡ w0 (cdLev c) →
  ∀ κ x → Bd (nxt 𝕂) (inj₂ c , κ) x a → x ≡ bot (Lev c) κ
injBase-only a c eq κ x e = only-botLev c κ x (subst (λ w → Bd (Lev c) κ x w) eq e)

mix-inj : ∀ s (c : HB (Kc s)) κ x → Bd (Kc (suc s)) (inj₂ c , κ) x (aW mixW (suc s)) → x ≡ bot (Lev c) κ
mix-inj s c κ x e = only-botLev c κ x e

mix-LvW : ∀ s (c : HB (Kc s)) κ (g : E (Lev c) κ → HB (Kc (suc s)))
  (k : K (LvW (aW mixW (suc s)) (hΩ (inj₂ c , κ) g))) → proj₁ (proj₁ k) ≡ bot (Lev c) κ
mix-LvW s c κ g ((x , e) , _) = only-botLev c κ x e
```

## §3 极限站的世界: 相干的出口

```agda
limW : WTower → Wd KΛc
limW T s = aW T s

lg-limW : ∀ T → LgW KΛc (limW T)
lg-limW T s = laW T s

lim-emb : ∀ T s (κ : K (Kc s)) x → Bd (Kc s) κ x (aW T s) → Bd KΛc (suc s , (inj₁ tt , κ)) x (limW T)
lim-emb T s κ x e = Bd↑ (Kc s) (grow T s) e
```

## §4 读回分量的世界恰好看见可入的分支: 分离子

层号 $\mathrm{h\Omega}\,\mathrm{tt}\,(x\mapsto1)$ 在 `HB S₀` 里 (合法); 它的级 `Lev` 的世界是 `A` 上的函数, 每个坐标一个 `A × HB S₀`. 界非零读作 "这一支看得见".

```agda
g1 : A → HB S₀
g1 _ = hs hz

Wρ : Set
Wρ = Wd (Lev {S₀} (hΩ tt g1))

SeeExact : A → Wρ → Set
SeeExact a ρ = (∀ x → x ⊲ a → isz (proj₂ (ρ x)) ≡ false) × (∀ x → ¬ (x ⊲ a) → isz (proj₂ (ρ x)) ≡ true)

nn-allF : ∀ α → ¬ ¬ (xα α ⊲ ωA) → ∀ n → α n ≡ false
nn-allF α nn n = h (α n) refl
  where
  h : ∀ b → α n ≡ b → α n ≡ false
  h false q = q
  h true q = ⊥-elim (nn (λ p → t≢f (trans (sym q) (allF α (lem α p refl refl) n))))

seeExact-sep : ∀ ρ → SeeExact ωA ρ → ∀ α → (∀ n → α n ≡ false) ⊎ ¬ (xα α ⊲ ωA)
seeExact-sep ρ (s⁺ , s⁻) α = look (isz (proj₂ (ρ (xα α)))) refl
  where
  look : ∀ b → isz (proj₂ (ρ (xα α))) ≡ b → (∀ n → α n ≡ false) ⊎ ¬ (xα α ⊲ ωA)
  look true eq = inj₂ (λ p → t≢f (trans (sym eq) (s⁺ (xα α) p)))
  look false eq = inj₁ (nn-allF α (λ np → t≢f (trans (sym (s⁻ (xα α) np)) eq)))

seeExact→WLPO : FEA → ∀ ρ → SeeExact ωA ρ → WLPO
seeExact→WLPO fe ρ S α with seeExact-sep ρ S α
... | inj₁ h = inj₁ h
... | inj₂ np = inj₂ (λ h → np (subst (λ t → xα α ⊲ t) (xα≡ fe α h) C.self))
```

**两半各自可满足.**

```agda
ρ⁺ ρ⁻ : Wρ
ρ⁺ x = azero , hs hz
ρ⁻ x = azero , hz

see⁺ : ∀ x → x ⊲ ωA → isz (proj₂ (ρ⁺ x)) ≡ false
see⁺ x p = refl

see⁻ : ∀ x → ¬ (x ⊲ ωA) → isz (proj₂ (ρ⁻ x)) ≡ true
see⁻ x np = refl
```

## §5 只否定什么

- **否定** (编译的): 对 `ωA` 这一个外层世界, 读回分量的世界 "可入处界非零, 不可入处界为零" (分离子; 有 `FEA` 时 WLPO).
- **定理 (不是否定, 接口的盲区)**: `WTower` 有基世界实例 (`baseW`) 与 "旧站分量长高, 读回分量为基世界" 的实例 (`mixW`); 后者在一切读回种类上只剩底支. 接口的律都满足, 读回的 $\Omega$-结构在下一站的 `LvW` 里看不见.
- **出口 (定理)**: 极限站的世界由世界塔逐站给出, 合法, 嵌入拷贝一个方向相干 (`lim-emb`).
- **不否定**: `WTower`; 读回分量取非基世界 (例如对一切坐标一致的世界, `ρ⁺` 的形状, 不判定可入); 只有正前提的 "可入处看得见" (`see⁺`).
