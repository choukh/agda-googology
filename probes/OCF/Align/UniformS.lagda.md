# 一致引理移植到符号族: 观测前序、互模拟与遗传好树 (`Ordˢ` 版)

> 接 [Prefix](Prefix.lagda.md) §8 (a). Prefix 实现了前缀栈折叠 $\psi^P$ 与证书 `Goodᶻ`/`force`, 但 `Goodᶻ` 只对无符号片段封闭; 缺的第一件是 [Uniform](Uniform.lagda.md) 在新族 `Ordˢ` 上的移植. 本文完成这件移植. 闭包定理、严格性引理与检验在 [Stage2Label](Stage2Label.lagda.md).
>
> 结论先说:
>
> 1. **互模拟 `≅ˢ` (§2–§3).** Level §5–§7 的 `Eq₊`/`R` 加两个子句: `ŝ≅` (界 $c\cong^\mathsf Ic'$, 第 0 点相关, 分支在 $\cong^\mathsf I$-相关的 $\eta$ 上相关, **外加层号种类相同** `kd ℓ ≡ kd ℓ′`) 与 `ĉ≅` (链在 `Z` 上相关, 输出相关). 对称、搬运不可见、传递性全部通过. 传递性在 `ŝ≅` 处要把 $c\sqsubseteq^\mathsf I\eta$ 换成 $c'\sqsubseteq^\mathsf I\eta$, 用的正是 $c\cong^\mathsf Ic'$: **紧的界使相关的闭包有相关的界**, 环境层号做不到 (Prefix §8 预言的第二个理由, 这里编译过). `ψᴾ` 的同余只对两种栈: 空栈 `ψ0-≅` 与单个 $\hat\Omega$ 帧 `ψ1-≅` (弹栈子句定义性展开).
> 2. **观测前序以计值为底 (§4).** `x ⊑ᵒ y` 指对一切相似观测与**一切证书** $G,G'$, `force (toZ (run O x)) G ⊑ force (toZ (run O′ y)) G′`. 观测 `ψo₀`/`ψo₁` 带栈 (相似 = 同目标层的同长纯 $\hat\Omega$ 栈). 这要求两件 Uniform 没有的东西: **计值与证书无关** (`force-≅`: `≅ᶻ`-相关的 `Z` 在任意两组证书下计值 $\cong$, 链点经 `chain≅` 逐个对上) 与**证书沿 `≅ᶻ` 搬运** (`Goodᶻ-tr`); 后者用在 `⊑ᵒ-≅ʳ`, 那里中间项需要一个证书.
> 3. **上界与链起点 (§6–§7).** `lim-r`/`lim-l`/`suc-r`/`limᵢ-r` 照 Uniform, 新增 `ŝ-r`/`ĉ-r` ($x\sqsubseteq^\mathsf o t_0\Rightarrow x\sqsubseteq^\mathsf o\hat s\,c\,t_0\,g$, 观测落到第 0 层时 `ŝ` 读作链, 第 0 项是 $t_0$). `B1` 改为假设形式 "`x ⊑ᵒ ψ^P(0)` ⟹ `x ⊑ᵒ ψ^P(z)`" (`B1₀`, `B1₁`): 有 $\hat\Omega$ 帧时 $\psi^P(0)$ 是弹栈闭包而不是 $\Omega_j$. `zero-l` 由它们得出, `Ω-monoᵒ` 照搬.
> 4. **遗传好树 (§8–§10).** `Good` 的 `ŝ` 子句: $t_0$、$g$ 好, $t_0\sqsubseteq^\mathsf o g\,\eta\,e$, $g$ 单调, 自反, 外加**支配** `Dom`: 第 0 层是 "对一切证书 $c\sqsubseteq^\mathsf I$ 链点的层号", 非零层是 $c\sqsubseteq^\mathsf I2$ (本文只处理界 $\le2$, 见 Stage2Label). `ĉᴸ` 子句存链的证书. `Good→Goodᶻ` 把第 0 层的好树变成 Prefix 的证书. `Good` 对搬运、$\Omega$、加法封闭; 加法要求 `Lv` (被加数在第 0 层时尾巴也在第 0 层), 否则退化层号上的 `ŝ` 会被加到第 0 层, 支配无法给出 (反例层号 `Z⁰`, §0).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 只导入已有模块, 不改任何已有文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformS where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Ctx; Pt; pt; lvP; Γᶜ; Mlev)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ;
  trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_; fΩ̂; ψᴾ; outs; Goodᶻ; force; force-HS)
open Restrˢ
```

## §0 层号的种类与几条 $\sqsubseteq^\mathsf I$ 小引理

`ŝ` 在第 0 层读作待计值的链 (`toZ` 把它变成 `ĉᴸ`), 在非零层读作 $\Omega_1$-共尾的符号对象; `addˢ` 与 `ψᴾ` 都按尾巴的层号分这两种情况. 互模拟要让两边落在同一种情况, 所以记下层号的**种类** `kd`. 它不能从 `Sim` 证据推出: 退化的极限层号 `Z⁰` (各项都是 `zero`) 没有前驱, `Simᴵ Z⁰ zero` 是空真的 (`vac`), 于是 `Z⁰` 层的 `ŝ` 可以被 `addˢ` 加到第 0 层的树上.

```agda
kd : Ordᴵ → Bool
kd zero      = true
kd (suc _)   = false
kd (lim _ _) = false

kd-≅ : ∀ {a b} → a ≅ᴵ b → kd a ≡ kd b
kd-≅ z≅     = refl
kd-≅ (s≅ _) = refl
kd-≅ (l≅ _) = refl

≅ᴵ→⊑ᴵ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅ᴵ→⊑ᴵ z≅     = z⊑
≅ᴵ→⊑ᴵ (s≅ e) = s⊑ e zero
≅ᴵ→⊑ᴵ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅ᴵ→⊑ᴵ (h n)) (Sim→⊑ᴵ (lim n)))

⊑ᴵ-≅ˡ : ∀ {a a′ b} → a ≅ᴵ a′ → a ⊑ᴵ b → a′ ⊑ᴵ b
⊑ᴵ-≅ˡ e h = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ (≅ᴵ-sym e)) h

⊑ᴵ-≅ʳ : ∀ {a b b′} → a ⊑ᴵ b → b ≅ᴵ b′ → a ⊑ᴵ b′
⊑ᴵ-≅ʳ h e = ⊑ᴵ-trans h (≅ᴵ→⊑ᴵ e)

Z⁰ : Ordᴵ
Z⁰ = lim (λ _ → zero) (λ _ → z⊑)

vac : Simᴵ Z⁰ zero
vac (lim n ())
```

**读法.** `≅ᴵ→⊑ᴵ` 与两条换端引理在 Level 里没有, 这里补上 (用于把 $c\sqsubseteq^\mathsf I\eta$ 搬到 $c'\cong^\mathsf Ic$). `vac` 是 §10 的 `Lv` 与 §2 的 `kd` 字段的理由.

## §1 `Z` 上的互模拟, 计值与证书无关

`Z` (第 0 层的待计值树) 上的互模拟 `≅ᶻ`: 链的界 $\cong^\mathsf I$, 第 0 点与输出相关, 分支在 $\cong^\mathsf I$-相关的 $\eta$ 上相关. 对称与传递 (传递时取中间的 $\eta'=\eta$, 支配证据经 `⊑ᴵ-≅ˡ` 搬运).

```agda
infix 4 _≅ᶻ_
data _≅ᶻ_ : Z → Z → Set where
  zᶻ : Z.zero ≅ᶻ Z.zero
  sᶻ : ∀ {x y} → x ≅ᶻ y → Z.suc x ≅ᶻ Z.suc y
  lᶻ : ∀ {f g : ℕ → Z} → (∀ n → f n ≅ᶻ g n) → Z.lim f ≅ᶻ Z.lim g
  ĉᶻ : ∀ {c c′ t₀ t₀′ o₀ o₀′} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z} →
       c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
       o₀ ≅ᶻ o₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → o η e ≅ᶻ o′ η′ e′) → ĉᴸ c t₀ g o₀ o ≅ᶻ ĉᴸ c′ t₀′ g′ o₀′ o′

≅ᶻ-sym : ∀ {x y} → x ≅ᶻ y → y ≅ᶻ x
≅ᶻ-sym zᶻ     = zᶻ
≅ᶻ-sym (sᶻ d) = sᶻ (≅ᶻ-sym d)
≅ᶻ-sym (lᶻ h) = lᶻ (λ n → ≅ᶻ-sym (h n))
≅ᶻ-sym (ĉᶻ ec dt dg dp dO) =
  ĉᶻ (≅ᴵ-sym ec) (≅ᶻ-sym dt) (λ η e η′ e′ eη → ≅ᶻ-sym (dg η′ e′ η e (≅ᴵ-sym eη)))
     (≅ᶻ-sym dp) (λ η e η′ e′ eη → ≅ᶻ-sym (dO η′ e′ η e (≅ᴵ-sym eη)))

≅ᶻ-trans : ∀ {x y w} → x ≅ᶻ y → y ≅ᶻ w → x ≅ᶻ w
≅ᶻ-trans zᶻ     zᶻ      = zᶻ
≅ᶻ-trans (sᶻ d) (sᶻ d′) = sᶻ (≅ᶻ-trans d d′)
≅ᶻ-trans (lᶻ h) (lᶻ h′) = lᶻ (λ n → ≅ᶻ-trans (h n) (h′ n))
≅ᶻ-trans (ĉᶻ ec dt dg dp dO) (ĉᶻ ec′ dt′ dg′ dp′ dO′) =
  ĉᶻ (≅ᴵ-trans ec ec′) (≅ᶻ-trans dt dt′)
     (λ η e η″ e″ eη → ≅ᶻ-trans (dg η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (dg′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
     (≅ᶻ-trans dp dp′)
     (λ η e η″ e″ eη → ≅ᶻ-trans (dO η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (dO′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
```

**计值与证书无关.** `force (ĉᴸ …) G` 的链点是 $\chi_{k+1}=E(\mathtt{lvl}\,\chi_k)$, 依赖证书 (层号 `toLevel` 吃证书). 两组证书、两条相关的链: 第 0 点 $\cong$, 其后由归纳得到 $\chi_k\cong\chi'_k$, 经 `toLevel-≅` 得层号 $\cong^\mathsf I$, 再用分支的相关性 (`chain≅`). 输出逐项同理 (`outs≅`). 递归调用都在 `≅ᶻ` 推导的子项上 (分支函数的值作为 λ 传给辅助引理), 停机检查一次通过.

```agda
chain≅ : (C C′ : Ctx) → Ctx.t₀ C ≅ Ctx.t₀ C′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → Ctx.E C η e ≅ Ctx.E C′ η′ e′) →
         ∀ k → Pt.x (Γᶜ C k) ≅ Pt.x (Γᶜ C′ k)
chain≅ C C′ h₀ hE zero    = h₀
chain≅ C C′ h₀ hE (suc k) =
  hE _ _ _ _ (toLevel-≅ (Pt.hx (Γᶜ C k)) (Pt.hx (Γᶜ C′ k)) (chain≅ C C′ h₀ hE k))

outs≅ : (C C′ : Ctx) → Ctx.t₀ C ≅ Ctx.t₀ C′ →
        (∀ η e η′ e′ → η ≅ᴵ η′ → Ctx.E C η e ≅ Ctx.E C′ η′ e′) →
        ∀ {O₀ O₀′ O O′} → O₀ ≅ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≅ O′ η′ e′) →
        ∀ n → outs C O₀ O n ≅ outs C′ O₀′ O′ n
outs≅ C C′ h₀ hE o₀ hO zero    = o₀
outs≅ C C′ h₀ hE o₀ hO (suc k) =
  hO _ _ _ _ (toLevel-≅ (Pt.hx (Γᶜ C k)) (Pt.hx (Γᶜ C′ k)) (chain≅ C C′ h₀ hE k))

force-≅ : ∀ {x y} → x ≅ᶻ y → (G : Goodᶻ x) (G′ : Goodᶻ y) → force x G ≅ force y G′
force-≅ zᶻ     Goodᶻ.gz Goodᶻ.gz = z≅
force-≅ (sᶻ d) (Goodᶻ.gs G) (Goodᶻ.gs G′) = s≅ (force-≅ d G G′)
force-≅ (lᶻ h) (Goodᶻ.gl G _) (Goodᶻ.gl G′ _) = l≅ (λ n → force-≅ (h n) (G n) (G′ n))
force-≅ (ĉᶻ {c = c} {c′ = c′} {t₀ = t₀} {t₀′ = t₀′} {o₀ = o₀} {o₀′ = o₀′} {g = g} {o = o} {g′ = g′} {o′ = o′} ec dt dg dp dO)
        (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) (Goodᶻ.gc G₀′ Gg′ d₀′ dE′ m₀′ mE′ Go₀′ Go′ mo₀′ mo′) =
  l≅ (outs≅ C C′ (force-≅ dt G₀ G₀′) (λ η e η′ e′ eη → force-≅ (dg η e η′ e′ eη) (Gg η e) (Gg′ η′ e′))
            (force-≅ dp Go₀ Go₀′) (λ η e η′ e′ eη → force-≅ (dO η e η′ e′ eη) (Go η e) (Go′ η′ e′)))
  where
  C : Ctx
  C = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
             ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
             ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  C′ : Ctx
  C′ = record { c = c′ ; t₀ = force t₀′ G₀′ ; E = λ η e → force (g′ η e) (Gg′ η e)
              ; h₀ = force-HS t₀′ G₀′ ; hE = λ η e → force-HS (g′ η e) (Gg′ η e)
              ; d₀ = d₀′ ; dE = dE′ ; m₀ = m₀′ ; mE = mE′ }
```

**读法.** `force-≅` 是 §4 观测前序良定的前提: 观测前序对**一切**证书量化, 而 Prefix 的 `force` 只对给定的证书计值.

## §2 新族的互模拟 `≅ˢ`

Level §5 的 `Eq₊`/`R` 逐字, 加两个子句. `ŝ≅`: 层号种类相同, 界 $\cong^\mathsf I$, 第 0 点相关, 分支在相关的 $\eta$ 上相关. `ĉ≅`: 链在 `Z` 上相关 (`≅ᶻ`), 输出相关; 不要求种类 (`ĉᴸ` 的读法与层号无关).

```agda
module _ (ℓ : Ordᴵ) (R : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set) where
  data Eq₊ˢ : ∀ {ℓ′} → Ordˢ ℓ → Ordˢ ℓ′ → Set where
    z≅  : ∀ {ℓ′} → Eq₊ˢ {ℓ′} Ord₊ˢ.zero Ord₊ˢ.zero
    s≅  : ∀ {ℓ′} {a : Ordˢ ℓ} {b : Ordˢ ℓ′} → Eq₊ˢ a b → Eq₊ˢ (Ord₊ˢ.suc a) (Ord₊ˢ.suc b)
    l≅  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordˢ ℓ′} → (∀ n → Eq₊ˢ (f n) (g n)) → Eq₊ˢ (Ord₊ˢ.lim f) (Ord₊ˢ.lim g)
    lᵢ≅ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} {g : Uˢ j′ (<→◃ q) → Ordˢ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordˢ j) (y : Ordˢ j′) → R j (<→◃ p) (intoˢ (<→◃ p) x) y → Eq₊ˢ (f (intoˢ (<→◃ p) x)) (g (intoˢ (<→◃ q) y))) →
          Eq₊ˢ (Ord₊ˢ.limᵢ p f) (Ord₊ˢ.limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {b : Ordˢ ℓ′} → R k (◃₁→◃ r) x b → Eq₊ˢ (Ord₊ˢ.up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : Uˢ k (◃₁→◃ r)} {a : Ordˢ ℓ} → Eq₊ˢ a (outˢ (◃₁→◃ r) y) → Eq₊ˢ a (Ord₊ˢ.up r y)
    ŝ≅  : ∀ {ℓ′ c c′} {t₀ : Ordˢ ℓ} {t₀′ : Ordˢ ℓ′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          kd ℓ ≡ kd ℓ′ → c ≅ᴵ c′ → Eq₊ˢ t₀ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eq₊ˢ (g η e) (g′ η′ e′)) →
          Eq₊ˢ (Ord₊ˢ.ŝ c t₀ g) (Ord₊ˢ.ŝ c′ t₀′ g′)
    ĉ≅  : ∀ {ℓ′ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
          {o₀ : Ordˢ ℓ} {o₀′ : Ordˢ ℓ′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} {o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Ordˢ ℓ′} →
          c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
          Eq₊ˢ o₀ o₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Eq₊ˢ (o η e) (o′ η′ e′)) →
          Eq₊ˢ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) (Ord₊ˢ.ĉᴸ c′ t₀′ g′ o₀′ o′)

Rˢ : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordˢ ℓ′ → Set
Rˢ i zero         x b = Eq₊ˢ i Rˢ x b
Rˢ i (suc r)      x b = Rˢ i r x b
Rˢ _ (self {f} n) x b = Eq₊ˢ (f n) Rˢ x b
Rˢ i (lim n r)    x b = Rˢ i r x b

infix 4 _≅ˢ_
_≅ˢ_ : ∀ {ℓ₁ ℓ₂} → Ordˢ ℓ₁ → Ordˢ ℓ₂ → Set
_≅ˢ_ {ℓ₁} = Eq₊ˢ ℓ₁ Rˢ

R→≅ˢ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → Rˢ i r (intoˢ r x) b → x ≅ˢ b
R→≅ˢ zero      e = e
R→≅ˢ (suc r)   e = R→≅ˢ r e
R→≅ˢ (self n)  e = e
R→≅ˢ (lim n r) e = R→≅ˢ r e

≅→Rˢ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordˢ ℓ′} → x ≅ˢ b → Rˢ i r (intoˢ r x) b
≅→Rˢ zero      e = e
≅→Rˢ (suc r)   e = ≅→Rˢ r e
≅→Rˢ (self n)  e = e
≅→Rˢ (lim n r) e = ≅→Rˢ r e

R-convˢ : ∀ {j ℓ₁ ℓ₂ ℓ′} (r : j ◃ ℓ₁) (r′ : j ◃ ℓ₂) {x : Ordˢ j} {b : Ordˢ ℓ′} → Rˢ j r (intoˢ r x) b → Rˢ j r′ (intoˢ r′ x) b
R-convˢ r r′ e = ≅→Rˢ r′ (R→≅ˢ r e)

≅ˢ-sym  : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ˢ b → b ≅ˢ a
R-flipˢ : ∀ {j j′ ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → Rˢ j r (intoˢ r x) y → Rˢ j′ r′ (intoˢ r′ y) x
flipRˢ  : ∀ {j j′ ℓ₂} (r′ : j′ ◃ ℓ₂) {x : Ordˢ j} {y : Ordˢ j′} → x ≅ˢ y → Rˢ j′ r′ (intoˢ r′ y) x
≅ˢ-sym z≅      = z≅
≅ˢ-sym (s≅ e)  = s≅ (≅ˢ-sym e)
≅ˢ-sym (l≅ h)  = l≅ (λ n → ≅ˢ-sym (h n))
≅ˢ-sym (lᵢ≅ {p = p} {q = q} e h) = lᵢ≅ (≅ᴵ-sym e) (λ y x d → ≅ˢ-sym (h x y (R-flipˢ (<→◃ q) (<→◃ p) d)))
≅ˢ-sym (upˡ {r = zero} e)    = upʳ (≅ˢ-sym e)
≅ˢ-sym (upˡ {r = self n} e)  = upʳ (≅ˢ-sym e)
≅ˢ-sym (upʳ {r = zero} e)    = upˡ (≅ˢ-sym e)
≅ˢ-sym (upʳ {r = self n} e)  = upˡ (≅ˢ-sym e)
≅ˢ-sym (ŝ≅ k ec et eg) = ŝ≅ (sym k) (≅ᴵ-sym ec) (≅ˢ-sym et) (λ η e η′ e′ eη → ≅ˢ-sym (eg η′ e′ η e (≅ᴵ-sym eη)))
≅ˢ-sym (ĉ≅ ec dt dg eo eO) = ĉ≅ (≅ᴵ-sym ec) (≅ᶻ-sym dt) (λ η e η′ e′ eη → ≅ᶻ-sym (dg η′ e′ η e (≅ᴵ-sym eη)))
                               (≅ˢ-sym eo) (λ η e η′ e′ eη → ≅ˢ-sym (eO η′ e′ η e (≅ᴵ-sym eη)))
R-flipˢ zero      r′ e = flipRˢ r′ e
R-flipˢ (suc r)   r′ e = R-flipˢ r r′ e
R-flipˢ (self n)  r′ e = flipRˢ r′ e
R-flipˢ (lim n r) r′ e = R-flipˢ r r′ e
flipRˢ zero       e = ≅ˢ-sym e
flipRˢ (suc r′)   e = flipRˢ r′ e
flipRˢ (self n)   e = ≅ˢ-sym e
flipRˢ (lim n r′) e = flipRˢ r′ e
```

**搬运不可见.** Level 的 `tr-≅` 组逐字, 新子句逐点 (Prefix 的 `trˢ` 对 `ŝ`/`ĉᴸ` 逐点, 链不动). `ŝ≅` 的种类字段沿 $a\cong^\mathsf Ib$ 搬运 (`kd-≅`).

```agda
trˢ-≅    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ a} {y : Ordˢ ℓ′} → x ≅ˢ y → trˢ e x ≅ˢ y
tr⁻ˢ-≅   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ b} {y : Ordˢ ℓ′} → x ≅ˢ y → tr⁻ˢ e x ≅ˢ y
backˢ-≅  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {v : Ordˢ ℓ′} → u ≅ˢ v → backˢ (resˢ q e) u ≅ˢ v
back⁻ˢ-≅ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {v : Ordˢ ℓ′} → u ≅ˢ v → backˢ (res⁻ˢ q e) u ≅ˢ v

trˢ-≅ e z≅      = z≅
trˢ-≅ e (s≅ d)  = s≅ (trˢ-≅ e d)
trˢ-≅ e (l≅ h)  = l≅ (λ n → trˢ-≅ e (h n))
trˢ-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej) λ u v d →
    subst (λ w → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ≅ˢ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
          (trˢ-≅ e (h _ v (≅→Rˢ (<→◃ q) (backˢ-≅ q e (R→≅ˢ (<→◃ (ltˢ (resˢ q e))) d)))))
trˢ-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (trˢ-≅ e d)
trˢ-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (trˢ-≅ (h n) d)
trˢ-≅ e (upʳ d) = upʳ (trˢ-≅ e d)
trˢ-≅ e (ŝ≅ k ec et eg) = ŝ≅ (trans (sym (kd-≅ e)) k) ec (trˢ-≅ e et) (λ η d η′ d′ eη → trˢ-≅ e (eg η d η′ d′ eη))
trˢ-≅ e (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (trˢ-≅ e eo) (λ η d η′ d′ eη → trˢ-≅ e (eO η d η′ d′ eη))

tr⁻ˢ-≅ e z≅      = z≅
tr⁻ˢ-≅ e (s≅ d)  = s≅ (tr⁻ˢ-≅ e d)
tr⁻ˢ-≅ e (l≅ h)  = l≅ (λ n → tr⁻ˢ-≅ e (h n))
tr⁻ˢ-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej) λ u v d →
    subst (λ w → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ≅ˢ g (intoˢ (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
          (tr⁻ˢ-≅ e (h _ v (≅→Rˢ (<→◃ q) (back⁻ˢ-≅ q e (R→≅ˢ (<→◃ (ltˢ (res⁻ˢ q e))) d)))))
tr⁻ˢ-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr⁻ˢ-≅ e d)
tr⁻ˢ-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (tr⁻ˢ-≅ (h n) d)
tr⁻ˢ-≅ e (upʳ d) = upʳ (tr⁻ˢ-≅ e d)
tr⁻ˢ-≅ e (ŝ≅ k ec et eg) = ŝ≅ (trans (kd-≅ e) k) ec (tr⁻ˢ-≅ e et) (λ η d η′ d′ eη → tr⁻ˢ-≅ e (eg η d η′ d′ eη))
tr⁻ˢ-≅ e (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (tr⁻ˢ-≅ e eo) (λ η d η′ d′ eη → tr⁻ˢ-≅ e (eO η d η′ d′ eη))

backˢ-≅ zero      (s≅ e) d = tr⁻ˢ-≅ e d
backˢ-≅ (suc q)   (s≅ e) d = backˢ-≅ q e d
backˢ-≅ (lim n q) (l≅ h) d = backˢ-≅ q (h n) d

back⁻ˢ-≅ zero      (s≅ e) d = trˢ-≅ e d
back⁻ˢ-≅ (suc q)   (s≅ e) d = back⁻ˢ-≅ q e d
back⁻ˢ-≅ (lim n q) (l≅ h) d = back⁻ˢ-≅ q (h n) d
```

**传递性.** 子句顺序照 Level (先剥两端的 `up`, 再剥中间). `ŝ≅`/`ĉ≅` 两次复合时, 第一段在 $(\eta,e)$ 与 $(\eta,e')$ 之间 ($e'$ 由 `⊑ᴵ-≅ˡ ec e` 从 $c\cong^\mathsf Ic'$ 得到), 第二段在 $(\eta,e')$ 与 $(\eta'',e'')$ 之间. 若界只满足 $c\sqsubseteq^\mathsf Ic'$ (例如一边是紧的界, 一边是膨胀后的环境层号), 中间那个闭包的定义域里没有 $\eta$ 的落脚点, 传递性不成立: 这是界必须紧的第二个理由, 在这里是编译过的形式 (`⊑ᴵ-≅ˡ ec` 是唯一的用处).

```agda
≅ˢ-trans  : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} {c : Ordˢ ℓ₃} → a ≅ˢ b → b ≅ˢ c → a ≅ˢ c
R-reflˡˢ  : ∀ {j ℓ ℓ′} (r : j ◃ ℓ) {x : Ordˢ j} {z : Ordˢ ℓ′} → Rˢ j r (intoˢ r x) z → x ≅ˢ x
≅ˢ-trans (upˡ {r = zero} e)   d = upˡ (≅ˢ-trans e d)
≅ˢ-trans (upˡ {r = self n} e) d = upˡ (≅ˢ-trans e d)
≅ˢ-trans d (upʳ {r = zero} e)   = upʳ (≅ˢ-trans d e)
≅ˢ-trans d (upʳ {r = self n} e) = upʳ (≅ˢ-trans d e)
≅ˢ-trans (upʳ {r = zero} e)   (upˡ e′) = ≅ˢ-trans e e′
≅ˢ-trans (upʳ {r = self n} e) (upˡ e′) = ≅ˢ-trans e e′
≅ˢ-trans z≅     z≅      = z≅
≅ˢ-trans (s≅ e) (s≅ e′) = s≅ (≅ˢ-trans e e′)
≅ˢ-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅ˢ-trans (h n) (h′ n))
≅ˢ-trans (lᵢ≅ {p = p} {q = q} e h) (lᵢ≅ e′ h′) =
  lᵢ≅ (≅ᴵ-trans e e′) λ x z d →
    ≅ˢ-trans (h x (trˢ e x) (≅→Rˢ (<→◃ p) (≅ˢ-sym (trˢ-≅ e (R-reflˡˢ (<→◃ p) d)))))
             (h′ (trˢ e x) z (≅→Rˢ (<→◃ q) (trˢ-≅ e (R→≅ˢ (<→◃ p) d))))
≅ˢ-trans (ŝ≅ k ec et eg) (ŝ≅ k′ ec′ et′ eg′) =
  ŝ≅ (trans k k′) (≅ᴵ-trans ec ec′) (≅ˢ-trans et et′)
     (λ η e η″ e″ eη → ≅ˢ-trans (eg η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (eg′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
≅ˢ-trans (ĉ≅ ec dt dg eo eO) (ĉ≅ ec′ dt′ dg′ eo′ eO′) =
  ĉ≅ (≅ᴵ-trans ec ec′) (≅ᶻ-trans dt dt′)
     (λ η e η″ e″ eη → ≅ᶻ-trans (dg η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (dg′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
     (≅ˢ-trans eo eo′)
     (λ η e η″ e″ eη → ≅ˢ-trans (eO η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (eO′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
R-reflˡˢ zero      e = ≅ˢ-trans e (≅ˢ-sym e)
R-reflˡˢ (suc r)   e = R-reflˡˢ r e
R-reflˡˢ (self n)  e = ≅ˢ-trans e (≅ˢ-sym e)
R-reflˡˢ (lim n r) e = R-reflˡˢ r e

≅ˢ-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ˢ b → a ≅ˢ a
≅ˢ-reflˡ e = ≅ˢ-trans e (≅ˢ-sym e)

≅ˢ-reflʳ : ∀ {ℓ₁ ℓ₂} {a : Ordˢ ℓ₁} {b : Ordˢ ℓ₂} → a ≅ˢ b → b ≅ˢ b
≅ˢ-reflʳ e = ≅ˢ-trans (≅ˢ-sym e) e

≅-trˢ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordˢ ℓ′} {x : Ordˢ a} → y ≅ˢ x → y ≅ˢ trˢ e x
≅-trˢ e d = ≅ˢ-sym (trˢ-≅ e (≅ˢ-sym d))

≅-tr⁻ˢ : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordˢ ℓ′} {x : Ordˢ b} → y ≅ˢ x → y ≅ˢ tr⁻ˢ e x
≅-tr⁻ˢ e d = ≅ˢ-sym (tr⁻ˢ-≅ e (≅ˢ-sym d))
```

## §3 $\Omega$、加法、`toZ` 与两种栈的折叠

`Ωˢ-≅` 与 Level 的 `Ω-≅` 逐字. `toZ-≅`: 第 0 层的相关树 `toZ` 后 `≅ᶻ`-相关 (`ŝ` 变成以自己为输出的 `ĉᴸ`). `addˢ-≅` 多一个前提 `kd ℓ₁ ≡ kd ℓ₂` (两个被加数的层号种类相同): 尾巴是非零层的 `ŝ` 时输出是被加数层上的 `ŝ`, 它的 `ŝ≅` 要这个字段; 尾巴的种类由 `ŝ≅` 自带, 不同种类的组合由 `tf` 排除.

```agda
Ωˢ-≅ : ∀ {a b} → a ≅ᴵ b → Ωˢ a ≅ˢ Ωˢ b
Ωˢ-≅ z≅     = s≅ z≅
Ωˢ-≅ (s≅ e) = lᵢ≅ e (λ x y d → upˡ (upʳ d))
Ωˢ-≅ (l≅ h) = l≅ (λ n → upˡ (upʳ (Ωˢ-≅ (h n))))

Ωˢ-refl : ∀ a → Ωˢ a ≅ˢ Ωˢ a
Ωˢ-refl a = Ωˢ-≅ (≅ᴵ-refl a)

toZ-≅ : ∀ {x y : Ordˢ zero} → x ≅ˢ y → toZ x ≅ᶻ toZ y
toZ-≅ z≅     = zᶻ
toZ-≅ (s≅ d) = sᶻ (toZ-≅ d)
toZ-≅ (l≅ h) = lᶻ (λ n → toZ-≅ (h n))
toZ-≅ (lᵢ≅ {p = ()} e h)
toZ-≅ (upˡ {r = ()} d)
toZ-≅ (upʳ {r = ()} d)
toZ-≅ (ŝ≅ k ec et eg) = ĉᶻ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη))
                           (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη))
toZ-≅ (ĉ≅ ec dt dg eo eO) = ĉᶻ ec dt dg (toZ-≅ eo) (λ η e η′ e′ eη → toZ-≅ (eO η e η′ e′ eη))

tf : true ≡ false → ⊥
tf ()

addˢ-≅ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ ℓ₁} {a′ : Ordˢ ℓ₂} {b : Ordˢ k₁} {b′ : Ordˢ k₂} →
         kd ℓ₁ ≡ kd ℓ₂ → a ≅ˢ a′ → b ≅ˢ b′ → addˢ a σ b ≅ˢ addˢ a′ σ′ b′
addˢ-≅ kℓ ea z≅     = ea
addˢ-≅ kℓ ea (s≅ e) = s≅ (addˢ-≅ kℓ ea e)
addˢ-≅ kℓ ea (l≅ h) = l≅ (λ n → addˢ-≅ kℓ ea (h n))
addˢ-≅ kℓ ea (upˡ {r = zero} e)   = addˢ-≅ kℓ ea e
addˢ-≅ kℓ ea (upˡ {r = self n} e) = addˢ-≅ kℓ ea e
addˢ-≅ kℓ ea (upʳ {r = zero} e)   = addˢ-≅ kℓ ea e
addˢ-≅ kℓ ea (upʳ {r = self n} e) = addˢ-≅ kℓ ea e
addˢ-≅ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} kℓ ea (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢ≅ e λ x y d →
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ≅ˢ addˢ a′ σ′ (g (intoˢ (<→◃ q′) v)))
         (sym (out-intoˢ (<→◃ (σ q)) x)) (sym (out-intoˢ (<→◃ (σ′ q′)) y))
         (addˢ-≅ kℓ ea (h x y (R-convˢ (<→◃ (σ q)) (<→◃ q) d)))
addˢ-≅ {k₁ = zero}    {k₂ = zero}    kℓ ea (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = zero}    {k₂ = suc _}   kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ {k₁ = zero}    {k₂ = lim _ _} kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf k)
addˢ-≅ {k₁ = suc _}   {k₂ = zero}    kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ {k₁ = lim _ _} {k₂ = zero}    kℓ ea (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
addˢ-≅ {k₁ = suc _}   {k₂ = suc _}   kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ kℓ ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = suc _}   {k₂ = lim _ _} kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ kℓ ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = lim _ _} {k₂ = suc _}   kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ kℓ ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ {k₁ = lim _ _} {k₂ = lim _ _} kℓ ea (ŝ≅ k ec et eg) =
  ŝ≅ kℓ ec (addˢ-≅ kℓ ea et) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eg η e η′ e′ eη))
addˢ-≅ kℓ ea (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (addˢ-≅ kℓ ea eo) (λ η e η′ e′ eη → addˢ-≅ kℓ ea (eO η e η′ e′ eη))
```

**两种栈.** 闭包理论只处理纯 $\hat\Omega$ 栈中长度 $\le1$ 的两种: 空栈 `ψ0` 与单个 $\hat\Omega$ 帧 `ψ1` (检验 1 的 $\psi_0(\Omega_\Omega+\Omega_2)$ 只用到这两种; 长度 2 的栈见 Stage2Label §11). `ψ1` 的弹栈子句定义性地展开 (`rebase p z []` 计算到 `base (suc i) zero [] _`), 所以 `ψ1-≅` 的 `z≅` 情况直接是一个 `ŝ≅`: 界 `s≅ ei` 由目标层 $i\cong^\mathsf Ii'$ 给出 (紧的界), 第 0 点与分支由 `ψ0-≅` 给出. 其余子句与 Level 的 `ψ-≅` 同形, 加 `ŝ`/`ĉᴸ` 的情况 (尾巴在第 0 层时输出 `ĉᴸ`).

```agda
ψ0 : ∀ {i k ℓ} → i <ᴵ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ i
ψ0 p σ x = ψᴾ 0 p σ [] x

ψ1 : ∀ {i k ℓ} → i <ᴵ ℓ → Simᴵ k ℓ → zero <ᴵ ℓ → Ordˢ k → Ordˢ i
ψ1 p σ z x = ψᴾ 1 p σ (fΩ̂ z ∷ []) x

ψ0-≅ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
       {a : Ordˢ k₁} {b : Ordˢ k₂} → i ≅ᴵ i′ → a ≅ˢ b → ψ0 p σ a ≅ˢ ψ0 p′ σ′ b
ψ0-≅ ei z≅ = Ωˢ-≅ ei
ψ0-≅ ei (s≅ e) = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ (kd-≅ ei) (ψ0-≅ ei e) e′) z≅)
ψ0-≅ ei (l≅ h) = l≅ (λ n → ψ0-≅ ei (h n))
ψ0-≅ ei (upˡ {r = zero} e)   = ψ0-≅ ei e
ψ0-≅ ei (upˡ {r = self n} e) = ψ0-≅ ei e
ψ0-≅ ei (upʳ {r = zero} e)   = ψ0-≅ ei e
ψ0-≅ ei (upʳ {r = self n} e) = ψ0-≅ ei e
ψ0-≅ {k₁ = zero}    {k₂ = zero}    ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψ0-≅ ei et) (λ η e η′ e′ eη → ψ0-≅ ei (eg η e η′ e′ eη))
ψ0-≅ {k₁ = zero}    {k₂ = suc _}   ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψ0-≅ {k₁ = zero}    {k₂ = lim _ _} ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψ0-≅ {k₁ = suc _}   {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψ0-≅ {k₁ = lim _ _} {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψ0-≅ {k₁ = suc _}   {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ0-≅ ei et) (λ η e η′ e′ eη → ψ0-≅ ei (eg η e η′ e′ eη))
ψ0-≅ {k₁ = suc _}   {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ0-≅ ei et) (λ η e η′ e′ eη → ψ0-≅ ei (eg η e η′ e′ eη))
ψ0-≅ {k₁ = lim _ _} {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ0-≅ ei et) (λ η e η′ e′ eη → ψ0-≅ ei (eg η e η′ e′ eη))
ψ0-≅ {k₁ = lim _ _} {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ0-≅ ei et) (λ η e η′ e′ eη → ψ0-≅ ei (eg η e η′ e′ eη))
ψ0-≅ ei (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (ψ0-≅ ei eo) (λ η e η′ e′ eη → ψ0-≅ ei (eO η e η′ e′ eη))
ψ0-≅ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h)
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ˢ ψ0 p′ σ′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (ψ0-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d))))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ n → ψ0-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ0-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)
... | injᵇ _ | injᶜ _  = l≅ (λ n → ψ0-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ0-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)
... | injᶜ _ | injᵇ _  = l≅ (λ n → ψ0-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ0-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)
... | injᶜ _ | injᶜ _  = l≅ (λ n → ψ0-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ0-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)

ψ1-≅ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
       {z : zero <ᴵ ℓ₁} {z′ : zero <ᴵ ℓ₂}
       {a : Ordˢ k₁} {b : Ordˢ k₂} → i ≅ᴵ i′ → a ≅ˢ b → ψ1 p σ z a ≅ˢ ψ1 p′ σ′ z′ b
ψ1-≅ ei z≅ = ŝ≅ (kd-≅ ei) (s≅ ei) (ψ0-≅ ei (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψ0-≅ ei (Ωˢ-≅ eη))
ψ1-≅ ei (s≅ e) = l≅ (iter-R _≅ˢ_ (λ e′ → addˢ-≅ (kd-≅ ei) (ψ1-≅ ei e) e′) z≅)
ψ1-≅ ei (l≅ h) = l≅ (λ n → ψ1-≅ ei (h n))
ψ1-≅ ei (upˡ {r = zero} e)   = ψ1-≅ ei e
ψ1-≅ ei (upˡ {r = self n} e) = ψ1-≅ ei e
ψ1-≅ ei (upʳ {r = zero} e)   = ψ1-≅ ei e
ψ1-≅ ei (upʳ {r = self n} e) = ψ1-≅ ei e
ψ1-≅ {k₁ = zero}    {k₂ = zero}    ei (ŝ≅ k ec et eg) =
  ĉ≅ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (ψ1-≅ ei et) (λ η e η′ e′ eη → ψ1-≅ ei (eg η e η′ e′ eη))
ψ1-≅ {k₁ = zero}    {k₂ = suc _}   ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψ1-≅ {k₁ = zero}    {k₂ = lim _ _} ei (ŝ≅ k ec et eg) = ⊥-elim (tf k)
ψ1-≅ {k₁ = suc _}   {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψ1-≅ {k₁ = lim _ _} {k₂ = zero}    ei (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
ψ1-≅ {k₁ = suc _}   {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ1-≅ ei et) (λ η e η′ e′ eη → ψ1-≅ ei (eg η e η′ e′ eη))
ψ1-≅ {k₁ = suc _}   {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ1-≅ ei et) (λ η e η′ e′ eη → ψ1-≅ ei (eg η e η′ e′ eη))
ψ1-≅ {k₁ = lim _ _} {k₂ = suc _}   ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ1-≅ ei et) (λ η e η′ e′ eη → ψ1-≅ ei (eg η e η′ e′ eη))
ψ1-≅ {k₁ = lim _ _} {k₂ = lim _ _} ei (ŝ≅ k ec et eg) =
  ŝ≅ (kd-≅ ei) ec (ψ1-≅ ei et) (λ η e η′ e′ eη → ψ1-≅ ei (eg η e η′ e′ eη))
ψ1-≅ ei (ĉ≅ ec dt dg eo eO) = ĉ≅ ec dt dg (ψ1-≅ ei eo) (λ η e η′ e′ eη → ψ1-≅ ei (eO η e η′ e′ eη))
ψ1-≅ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} {z = z} {z′ = z′} ei (lᵢ≅ {p = q} {q = q′} {f = f} {g = g} e h)
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ˢ ψ1 p′ σ′ z′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (ψ1-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (tr⁻ˢ-≅ e₁ (≅-tr⁻ˢ e₂ (R→≅ˢ (<→◃ r₁) d))))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l≅ (λ n → ψ1-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ1-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)
... | injᵇ _ | injᶜ _  = l≅ (λ n → ψ1-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ1-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)
... | injᶜ _ | injᵇ _  = l≅ (λ n → ψ1-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ1-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)
... | injᶜ _ | injᶜ _  = l≅ (λ n → ψ1-≅ ei (h _ _ (≅→Rˢ (<→◃ q) (chain n))))
  where chain = iter-R _≅ˢ_ (λ d → ψ1-≅ e (h _ _ (≅→Rˢ (<→◃ q) d))) (Ωˢ-≅ e)
```

## §4 观测与以计值为底的观测前序

**证书搬运.** `Goodᶻ-tr : x ≅ᶻ y → Goodᶻ x → Goodᶻ y`. `gc` 的十个字段逐个搬: 好性递归; 支配经 `force-≅` 与 `toLevel-≅` 再 `⊑ᴵ-≅ʳ`; 单调经两端的 $\cong$. 工程注记: `where` 里的字段若不写类型签名, 报

    [UnequalHiding] … ≺ force t₀′ G₀′ → … != ({ℓ : Ordᴵ} {c = c₁ : Ordᶜ ℓ} → c₁ ≺ force t₀′ G₀′ → …)
    because one is an implicit function type and the other is an explicit function type

(`_⊑_` 是隐式量化的函数类型), 加上签名即过.

```agda
Goodᶻ-tr : ∀ {x y} → x ≅ᶻ y → Goodᶻ x → Goodᶻ y
Goodᶻ-tr zᶻ     Goodᶻ.gz     = Goodᶻ.gz
Goodᶻ-tr (sᶻ d) (Goodᶻ.gs G) = Goodᶻ.gs (Goodᶻ-tr d G)
Goodᶻ-tr (lᶻ h) (Goodᶻ.gl G st) = Goodᶻ.gl (λ n → Goodᶻ-tr (h n) (G n))
  (λ n → ⊑-trans (≅→⊑ (≅-sym (force-≅ (h n) (G n) (Goodᶻ-tr (h n) (G n)))))
         (⊑-trans (st n) (≅→⊑ (force-≅ (h (suc n)) (G (suc n)) (Goodᶻ-tr (h (suc n)) (G (suc n)))))))
Goodᶻ-tr {y = ĉᴸ c′ t₀′ g′ o₀′ o′} (ĉᶻ {c = c} {t₀ = t₀} {o₀ = o₀} {g = g} {o = o} ec dt dg dp dO)
         (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  Goodᶻ.gc G₀′ Gg′ d₀′ dE′ m₀′ mE′ Go₀′ Go′ mo₀′ mo′
  where
  cv : ∀ {η} → c′ ⊑ᴵ η → c ⊑ᴵ η
  cv = ⊑ᴵ-≅ˡ (≅ᴵ-sym ec)
  G₀′ : Goodᶻ t₀′
  G₀′ = Goodᶻ-tr dt G₀
  Gg′ : ∀ η e → Goodᶻ (g′ η e)
  Gg′ η e = Goodᶻ-tr (dg η (cv e) η e (≅ᴵ-refl η)) (Gg η (cv e))
  Go₀′ : Goodᶻ o₀′
  Go₀′ = Goodᶻ-tr dp Go₀
  Go′ : ∀ η e → Goodᶻ (o′ η e)
  Go′ η e = Goodᶻ-tr (dO η (cv e) η e (≅ᴵ-refl η)) (Go η (cv e))
  ft : force t₀ G₀ ≅ force t₀′ G₀′
  ft = force-≅ dt G₀ G₀′
  fg : ∀ η e → force (g η (cv e)) (Gg η (cv e)) ≅ force (g′ η e) (Gg′ η e)
  fg η e = force-≅ (dg η (cv e) η e (≅ᴵ-refl η)) (Gg η (cv e)) (Gg′ η e)
  fo₀ : force o₀ Go₀ ≅ force o₀′ Go₀′
  fo₀ = force-≅ dp Go₀ Go₀′
  fo : ∀ η e → force (o η (cv e)) (Go η (cv e)) ≅ force (o′ η e) (Go′ η e)
  fo η e = force-≅ (dO η (cv e) η e (≅ᴵ-refl η)) (Go η (cv e)) (Go′ η e)
  d₀′ : c′ ⊑ᴵ toLevel (force t₀′ G₀′) (force-HS t₀′ G₀′)
  d₀′ = ⊑ᴵ-≅ˡ ec (⊑ᴵ-≅ʳ d₀ (toLevel-≅ (force-HS t₀ G₀) (force-HS t₀′ G₀′) ft))
  dE′ : ∀ η e → c′ ⊑ᴵ toLevel (force (g′ η e) (Gg′ η e)) (force-HS _ (Gg′ η e))
  dE′ = λ η e → ⊑ᴵ-≅ˡ ec (⊑ᴵ-≅ʳ (dE η (cv e)) (toLevel-≅ (force-HS _ (Gg η (cv e))) (force-HS _ (Gg′ η e)) (fg η e)))
  m₀′ : ∀ η e → force t₀′ G₀′ ⊑⁰ force (g′ η e) (Gg′ η e)
  m₀′ = λ η e → ⊑-trans (≅→⊑ (≅-sym ft)) (⊑-trans (m₀ η (cv e)) (≅→⊑ (fg η e)))
  mE′ : ∀ η e η′ e′ → η ⊑ᴵ η′ → force (g′ η e) (Gg′ η e) ⊑⁰ force (g′ η′ e′) (Gg′ η′ e′)
  mE′ = λ η e η′ e′ h → ⊑-trans (≅→⊑ (≅-sym (fg η e))) (⊑-trans (mE η (cv e) η′ (cv e′) h) (≅→⊑ (fg η′ e′)))
  mo₀′ : ∀ η e → force o₀′ Go₀′ ⊑⁰ force (o′ η e) (Go′ η e)
  mo₀′ = λ η e → ⊑-trans (≅→⊑ (≅-sym fo₀)) (⊑-trans (mo₀ η (cv e)) (≅→⊑ (fo η e)))
  mo′ : ∀ η e η′ e′ → η ⊑ᴵ η′ → force (o′ η e) (Go′ η e) ⊑⁰ force (o′ η′ e′) (Go′ η′ e′)
  mo′ = λ η e η′ e′ h → ⊑-trans (≅→⊑ (≅-sym (fo η e))) (⊑-trans (mo η (cv e) η′ (cv e′) h) (≅→⊑ (fo η′ e′)))
```

**观测.** Uniform 的六种去掉 `ψ⁰o` (新族的目标层 0 由带 $p:0<^\mathsf I\ell$ 的 `ψᴾ` 表达), `ψo` 分成两种栈 `ψo₀`/`ψo₁`. 相似: `ψo₀`/`ψo₁` 两侧同目标层, 层号、`Sim`、帧证据任意; `addo` 要求被加数 $\cong$ **且层号种类相同** (§3 的 `addˢ-≅` 的前提); 搬运观测同 Uniform.

```agda
data Obs : Ordᴵ → Set where
  idO  : Obs zero
  ψo₀  : ∀ {i k ℓ} → Obs i → i <ᴵ ℓ → Simᴵ k ℓ → Obs k
  ψo₁  : ∀ {i k ℓ} → Obs i → i <ᴵ ℓ → Simᴵ k ℓ → zero <ᴵ ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordˢ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

run : ∀ {k} → Obs k → Ordˢ k → Ordˢ zero
run idO           x = x
run (ψo₀ O p σ)   x = run O (ψ0 p σ x)
run (ψo₁ O p σ z) x = run O (ψ1 p σ z x)
run (addo O a σ)  x = run O (addˢ a σ x)
run (tro O e)     x = run O (trˢ e x)
run (tr⁻o O e)    x = run O (tr⁻ˢ e x)

infix 4 _≈ᵒ_ _⊑ᵒ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
  idO  : idO ≈ᵒ idO
  ψo₀  : ∀ {i k k′ ℓ ℓ′} {O O′ : Obs i} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → ψo₀ O p σ ≈ᵒ ψo₀ O′ p′ σ′
  ψo₁  : ∀ {i k k′ ℓ ℓ′} {O O′ : Obs i} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′}
         {z : zero <ᴵ ℓ} {z′ : zero <ᴵ ℓ′} → O ≈ᵒ O′ → ψo₁ O p σ z ≈ᵒ ψo₁ O′ p′ σ′ z′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → kd ℓ ≡ kd ℓ′ → a ≅ˢ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᵒ-reflˡ idO          = idO
≈ᵒ-reflˡ (ψo₀ o)      = ψo₀ (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (ψo₁ o)      = ψo₁ (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (addo o k e) = addo (≈ᵒ-reflˡ o) refl (≅ˢ-reflˡ e)
≈ᵒ-reflˡ (tro o)      = tro (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (tr⁻o o)     = tr⁻o (≈ᵒ-reflˡ o)

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᵒ-reflʳ idO          = idO
≈ᵒ-reflʳ (ψo₀ o)      = ψo₀ (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (ψo₁ o)      = ψo₁ (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (addo o k e) = addo (≈ᵒ-reflʳ o) refl (≅ˢ-reflʳ e)
≈ᵒ-reflʳ (tro o)      = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)     = tr⁻o (≈ᵒ-reflʳ o)

run-≅ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordˢ k} {x′ : Ordˢ k′} → O ≈ᵒ O′ → x ≅ˢ x′ → run O x ≅ˢ run O′ x′
run-≅ idO          d = d
run-≅ (ψo₀ o)      d = run-≅ o (ψ0-≅ (≅ᴵ-refl _) d)
run-≅ (ψo₁ o)      d = run-≅ o (ψ1-≅ (≅ᴵ-refl _) d)
run-≅ (addo o k a) d = run-≅ o (addˢ-≅ k a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (trˢ-≅ e (≅-trˢ e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d))
```

**观测前序.** 底部是**计值后的** $\sqsubseteq$, 对一切证书. `≅→⊑ᵒ` 由 `run-≅`、`toZ-≅`、`force-≅`. `⊑ᵒ-≅ʳ` (同层换右端) 在 Uniform 里是一行的传递; 这里中间项 `run O′ y` 需要一个证书才能实例化前一个 $\sqsubseteq^\mathsf o$, 它由右端的证书经 `Goodᶻ-tr` 搬来.

```agda
_⊑ᵒ_ : ∀ {k k′} → Ordˢ k → Ordˢ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ →
  (G : Goodᶻ (toZ (run O x))) (G′ : Goodᶻ (toZ (run O′ y))) → force _ G ⊑ force _ G′

≅→⊑ᵒ : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ≅ˢ y → x ⊑ᵒ y
≅→⊑ᵒ e o G G′ = ≅→⊑ (force-≅ (toZ-≅ (run-≅ o e)) G G′)

⊑ᵒ-≅ʳ : ∀ {k k′} {x : Ordˢ k} {y y′ : Ordˢ k′} → x ⊑ᵒ y → y ≅ˢ y′ → x ⊑ᵒ y′
⊑ᵒ-≅ʳ h e o G G′ = ⊑-trans (h o G Gm) (≅→⊑ (force-≅ d Gm G′))
  where
  d = toZ-≅ (run-≅ (≈ᵒ-reflʳ o) e)
  Gm = Goodᶻ-tr (≅ᶻ-sym d) G′
```

## §5 同余

`ψ0-cong`/`ψ1-cong`/`add-cong`/`tr-cong`/`tr⁻-cong` 都是一行 (观测本身). `up-l`/`up-r` 同 Uniform, 但递归调用必须写出隐式的 $x,y$: 照抄 Uniform 的 `up-l {r = zero} (λ o′ → h (tro o′)) o` 报

    [UnequalTerms] tro _O_5138 _e_5140 != O of type Obs k
    when checking that the inferred type of an application
      tro _O_5138 _e_5140 ≈ᵒ tro _O′_5139 _e′_5141
    matches the expected type O ≈ᵒ O′

(观测前序多了两个证书参数后, λ 的类型 `_⊑ᵒ_ ?x ?y` 在元变量下不再展开成隐式函数类型). 写出 `{x = trˢ e x} {y = trˢ e′ y}` 即过. §6 的上界引理同样处理.

```agda
ψ0-cong : ∀ {i k k′ ℓ ℓ′} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
          x ⊑ᵒ y → ψ0 p σ x ⊑ᵒ ψ0 p′ σ′ y
ψ0-cong h o = h (ψo₀ o)

ψ1-cong : ∀ {i k k′ ℓ ℓ′} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′}
          {z : zero <ᴵ ℓ} {z′ : zero <ᴵ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
          x ⊑ᵒ y → ψ1 p σ z x ⊑ᵒ ψ1 p′ σ′ z′ y
ψ1-cong h o = h (ψo₁ o)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordˢ k} {y : Ordˢ k′} →
           kd ℓ ≡ kd ℓ′ → a ≅ˢ a′ → x ⊑ᵒ y → addˢ a σ x ⊑ᵒ addˢ a′ σ′ y
add-cong k e h o = h (addo o k e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ a} {y : Ordˢ a′} → x ⊑ᵒ y → trˢ e x ⊑ᵒ trˢ e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordˢ b} {y : Ordˢ b′} → x ⊑ᵒ y → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ y
tr⁻-cong h o = h (tr⁻o o)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {y : Ordˢ ℓ′} → outˢ (◃₁→◃ r) x ⊑ᵒ y → Ord₊ˢ.up r x ⊑ᵒ y
up-l {r = zero}   h (ψo₀ o)      = h (ψo₀ o)
up-l {r = zero}   h (ψo₁ o)      = h (ψo₁ o)
up-l {r = zero}   h (addo o k e) = h (addo o k e)
up-l {r = zero}   {x = x} {y = y} h (tro {e = s≅ e} {e′ = e′} o)  =
  up-l {r = zero} {x = trˢ e x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = zero}   {x = x} {y = y} h (tr⁻o {e = s≅ e} {e′ = e′} o) =
  up-l {r = zero} {x = tr⁻ˢ e x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (ψo₀ o)      = h (ψo₀ o)
up-l {r = self n} h (ψo₁ o)      = h (ψo₁ o)
up-l {r = self n} h (addo o k e) = h (addo o k e)
up-l {r = self n} {x = x} {y = y} h (tro {e = l≅ f} {e′ = e′} o)  =
  up-l {r = self n} {x = trˢ (f n) x} {y = trˢ e′ y} (λ o′ → h (tro o′)) o
up-l {r = self n} {x = x} {y = y} h (tr⁻o {e = l≅ f} {e′ = e′} o) =
  up-l {r = self n} {x = tr⁻ˢ (f n) x} {y = tr⁻ˢ e′ y} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : Uˢ k (◃₁→◃ r)} {x : Ordˢ ℓ′} → x ⊑ᵒ outˢ (◃₁→◃ r) y → x ⊑ᵒ Ord₊ˢ.up r y
up-r {r = zero}   h (ψo₀ o)      = h (ψo₀ o)
up-r {r = zero}   h (ψo₁ o)      = h (ψo₁ o)
up-r {r = zero}   h (addo o k e) = h (addo o k e)
up-r {r = zero}   {y = y} {x = x} h (tro {e = e} {e′ = s≅ e′} o)  =
  up-r {r = zero} {y = trˢ e′ y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = zero}   {y = y} {x = x} h (tr⁻o {e = e} {e′ = s≅ e′} o) =
  up-r {r = zero} {y = tr⁻ˢ e′ y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (ψo₀ o)      = h (ψo₀ o)
up-r {r = self n} h (ψo₁ o)      = h (ψo₁ o)
up-r {r = self n} h (addo o k e) = h (addo o k e)
up-r {r = self n} {y = y} {x = x} h (tro {e = e} {e′ = l≅ f} o)  =
  up-r {r = self n} {y = trˢ (f n) y} {x = trˢ e x} (λ o′ → h (tro o′)) o
up-r {r = self n} {y = y} {x = x} h (tr⁻o {e = e} {e′ = l≅ f} o) =
  up-r {r = self n} {y = tr⁻ˢ (f n) y} {x = tr⁻ˢ e x} (λ o′ → h (tr⁻o o′)) o
```

## §6 反演与上界引理

**反演** 照 Uniform §0 (`i-resp` 两边对到 `trˢ e z′`). 新增: `ŝ`/`ĉᴸ` 的自反部分 (`ŝ-refl₀`, `ĉ-refl₀`, `ĉ-reflg`, `≅ᶻ-refl₀`, `≅ᶻ-reflg`, `ĉ-reflO`), 都对右端任意 (剥 `upʳ`), 以避开 "`ŝ c t₀ g ≅ ŝ c t₀ g` 两侧同变量" 在 `--without-K` 下的反演卡住.

```agda
s-invˢ : ∀ {k k′} {a : Ordˢ k} {b : Ordˢ k′} → Ord₊ˢ.suc a ≅ˢ Ord₊ˢ.suc b → a ≅ˢ b
s-invˢ (s≅ e) = e

l-invˢ : ∀ {k k′} {f : ℕ → Ordˢ k} {g : ℕ → Ordˢ k′} → Ord₊ˢ.lim f ≅ˢ Ord₊ˢ.lim g → ∀ n → f n ≅ˢ g n
l-invˢ (l≅ h) = h

i-respˢ : ∀ {k k′ j} {p : j <ᴵ k} {f : Uˢ j (<→◃ p) → Ordˢ k} {b : Ordˢ k′} → Ord₊ˢ.limᵢ p f ≅ˢ b →
          ∀ {z z′ : Ordˢ j} → z ≅ˢ z′ → f (intoˢ (<→◃ p) z) ≅ˢ f (intoˢ (<→◃ p) z′)
i-respˢ {p = p} (lᵢ≅ e h) {z} {z′} d =
  ≅ˢ-trans (h z (trˢ e z′) (≅→Rˢ (<→◃ p) (≅-trˢ e d)))
           (≅ˢ-sym (h z′ (trˢ e z′) (≅→Rˢ (<→◃ p) (≅-trˢ e (≅ˢ-reflʳ d)))))
i-respˢ (upʳ {r = zero} e)   = i-respˢ e
i-respˢ (upʳ {r = self n} e) = i-respˢ e

u-invˢ : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} {b : Ordˢ ℓ′} → Ord₊ˢ.up r x ≅ˢ b → outˢ (◃₁→◃ r) x ≅ˢ b
u-invˢ zero     (upˡ e)              = e
u-invˢ zero     (upʳ {r = zero} e)   = upʳ (u-invˢ zero e)
u-invˢ zero     (upʳ {r = self n} e) = upʳ (u-invˢ zero e)
u-invˢ (self m) (upˡ e)              = e
u-invˢ (self m) (upʳ {r = zero} e)   = upʳ (u-invˢ (self m) e)
u-invˢ (self m) (upʳ {r = self n} e) = upʳ (u-invˢ (self m) e)

u-reflˢ : ∀ {k ℓ} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} → Ord₊ˢ.up r x ≅ˢ Ord₊ˢ.up r x → outˢ (◃₁→◃ r) x ≅ˢ outˢ (◃₁→◃ r) x
u-reflˢ r e = ≅ˢ-reflˡ (u-invˢ r e)

ŝ-refl₀ : ∀ {k k′ c t₀ g} {b : Ordˢ k′} → Ord₊ˢ.ŝ {ℓ = k} c t₀ g ≅ˢ b → t₀ ≅ˢ t₀
ŝ-refl₀ (ŝ≅ _ _ et _)        = ≅ˢ-reflˡ et
ŝ-refl₀ (upʳ {r = zero} e)   = ŝ-refl₀ e
ŝ-refl₀ (upʳ {r = self n} e) = ŝ-refl₀ e

ĉ-refl₀ : ∀ {k k′ c t₀ g o₀ o} {b : Ordˢ k′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ˢ b → o₀ ≅ˢ o₀
ĉ-refl₀ (ĉ≅ _ _ _ eo _)      = ≅ˢ-reflˡ eo
ĉ-refl₀ (upʳ {r = zero} e)   = ĉ-refl₀ e
ĉ-refl₀ (upʳ {r = self n} e) = ĉ-refl₀ e

self-trˢ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} → x ≅ˢ x → trˢ e x ≅ˢ trˢ e x
self-trˢ e d = ≅ˢ-reflˡ (trˢ-≅ e (≅-trˢ e d))

self-tr⁻ˢ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} → x ≅ˢ x → tr⁻ˢ e x ≅ˢ tr⁻ˢ e x
self-tr⁻ˢ e d = ≅ˢ-reflˡ (tr⁻ˢ-≅ e (≅-tr⁻ˢ e d))

ĉ-reflg : ∀ {k k′ c t₀ g o₀ o} {b : Ordˢ k′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ˢ b → ∀ η e → o η e ≅ˢ o η e
ĉ-reflg (ĉ≅ ec _ _ _ eO) η e     = ≅ˢ-reflˡ (eO η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η))
ĉ-reflg (upʳ {r = zero} d) η e   = ĉ-reflg d η e
ĉ-reflg (upʳ {r = self n} d) η e = ĉ-reflg d η e

≅ᶻ-refl₀ : ∀ {k k′ c t₀ g o₀ o} {b : Ordˢ k′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ˢ b → t₀ ≅ᶻ t₀
≅ᶻ-refl₀ (ĉ≅ _ dt _ _ _)       = ≅ᶻ-trans dt (≅ᶻ-sym dt)
≅ᶻ-refl₀ (upʳ {r = zero} d)   = ≅ᶻ-refl₀ d
≅ᶻ-refl₀ (upʳ {r = self n} d) = ≅ᶻ-refl₀ d

≅ᶻ-reflg : ∀ {k k′ c t₀ g o₀ o} {b : Ordˢ k′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ˢ b →
           ∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g η′ e′
≅ᶻ-reflg (ĉ≅ ec _ dg _ _) η e η′ e′ eη =
  ≅ᶻ-trans (dg η e η′ (⊑ᴵ-≅ˡ ec e′) eη) (≅ᶻ-sym (dg η′ e′ η′ (⊑ᴵ-≅ˡ ec e′) (≅ᴵ-refl η′)))
≅ᶻ-reflg (upʳ {r = zero} d)   = ≅ᶻ-reflg d
≅ᶻ-reflg (upʳ {r = self n} d) = ≅ᶻ-reflg d

ĉ-reflO : ∀ {k k′ c t₀ g o₀ o} {b : Ordˢ k′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ≅ˢ b →
          ∀ η e η′ e′ → η ≅ᴵ η′ → o η e ≅ˢ o η′ e′
ĉ-reflO (ĉ≅ ec _ _ _ eO) η e η′ e′ eη =
  ≅ˢ-trans (eO η e η′ (⊑ᴵ-≅ˡ ec e′) eη) (≅ˢ-sym (eO η′ e′ η′ (⊑ᴵ-≅ˡ ec e′) (≅ᴵ-refl η′)))
ĉ-reflO (upʳ {r = zero} d)   = ĉ-reflO d
ĉ-reflO (upʳ {r = self n} d) = ĉ-reflO d
```

**上界引理.** `lim-r`/`lim-l`/`suc-r` 的 `idO` 情况先把证书匹配成 `gl`/`gs`, 计值即展开; 其余观测把运算推进两侧. 递归调用要写出隐式的树 (原因同 §5): 不写时报

    [UnequalTerms] ψᴾ 0 _p′_6193 _σ′_6194 [] (h n) != h n of type Ord₊ˢ k′ Uˢ
    when checking that the expression ψ0-cong p has type …

(高阶合一推不出 `h := λ m → ψ0 p′ σ′ (h m)`).

**`ŝ-r`/`ĉ-r` (新).** $x\sqsubseteq^\mathsf o t_0\Rightarrow x\sqsubseteq^\mathsf o\hat s\,c\,t_0\,g$. 观测到底 (`idO`) 时 `ŝ` 在第 0 层, `toZ` 后是以 $t_0$ 为第 0 项输出的链, 证书是 `gc`, 计值是 $\lim$ `outs`, 第 0 项 `outs C O₀ O 0 = O₀`, 用 `⊑-lim 0`. 其他观测: 尾巴在第 0 层时 `ψᴾ`/`addˢ` 把 `ŝ` 变成 `ĉᴸ` (转 `ĉ-r`), 否则仍是 `ŝ` (递归); 搬运逐点. 两个引理互递归, 对观测结构递归.

```agda
lim-r : ∀ {k k′} {x : Ordˢ k} {h : ℕ → Ordˢ k′} n → x ⊑ᵒ h n → x ⊑ᵒ Ord₊ˢ.lim h
lim-r n p idO G (Goodᶻ.gl G′ st) = ⊑-lim n (p idO G (G′ n))
lim-r {h = h} n p (ψo₀ {p′ = p′} {σ′ = σ′} o) = lim-r {h = λ m → ψ0 p′ σ′ (h m)} n (ψ0-cong p) o
lim-r {h = h} n p (ψo₁ {p′ = p′} {σ′ = σ′} {z′ = z′} o) = lim-r {h = λ m → ψ1 p′ σ′ z′ (h m)} n (ψ1-cong p) o
lim-r {h = h} n p (addo {a′ = a′} {σ′ = σ′} o k a) = lim-r {h = λ m → addˢ a′ σ′ (h m)} n (add-cong k a p) o
lim-r {h = h} n p (tro {e′ = e′} o)  = lim-r {h = λ m → trˢ e′ (h m)} n (tr-cong p) o
lim-r {h = h} n p (tr⁻o {e′ = e′} o) = lim-r {h = λ m → tr⁻ˢ e′ (h m)} n (tr⁻-cong p) o

lim-l : ∀ {k k′} {h : ℕ → Ordˢ k} {y : Ordˢ k′} → (∀ n → h n ⊑ᵒ y) → Ord₊ˢ.lim h ⊑ᵒ y
lim-l K idO (Goodᶻ.gl G st) G′ = lim-⊑ (λ n → K n idO (G n) G′)
lim-l {h = h} {y = y} K (ψo₀ {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} o) =
  lim-l {h = λ m → ψ0 p σ (h m)} {y = ψ0 p′ σ′ y} (λ n o′ → K n (ψo₀ o′)) o
lim-l {h = h} {y = y} K (ψo₁ {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} {z = z} {z′ = z′} o) =
  lim-l {h = λ m → ψ1 p σ z (h m)} {y = ψ1 p′ σ′ z′ y} (λ n o′ → K n (ψo₁ o′)) o
lim-l {h = h} {y = y} K (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) =
  lim-l {h = λ m → addˢ a σ (h m)} {y = addˢ a′ σ′ y} (λ n o′ → K n (addo o′ k ea)) o
lim-l {h = h} {y = y} K (tro {e = e} {e′ = e′} o)  =
  lim-l {h = λ m → trˢ e (h m)} {y = trˢ e′ y} (λ n o′ → K n (tro o′)) o
lim-l {h = h} {y = y} K (tr⁻o {e = e} {e′ = e′} o) =
  lim-l {h = λ m → tr⁻ˢ e (h m)} {y = tr⁻ˢ e′ y} (λ n o′ → K n (tr⁻o o′)) o

suc-r : ∀ {k k′} {x : Ordˢ k} {y : Ordˢ k′} → x ⊑ᵒ y → x ⊑ᵒ Ord₊ˢ.suc y
suc-r p idO G (Goodᶻ.gs G′) = λ h → ≺s (p idO G G′ h)
suc-r {y = y} p (ψo₀ {p′ = p′} {σ′ = σ′} o) =
  lim-r {h = iter (ψ0 p′ σ′ y +ˢ_) Ord₊ˢ.zero} 1 (ψ0-cong p) o
suc-r {y = y} p (ψo₁ {p′ = p′} {σ′ = σ′} {z′ = z′} o) =
  lim-r {h = iter (ψ1 p′ σ′ z′ y +ˢ_) Ord₊ˢ.zero} 1 (ψ1-cong p) o
suc-r {y = y} p (addo {a′ = a′} {σ′ = σ′} o k a) = suc-r {y = addˢ a′ σ′ y} (add-cong k a p) o
suc-r {y = y} p (tro {e′ = e′} o)  = suc-r {y = trˢ e′ y} (tr-cong p) o
suc-r {y = y} p (tr⁻o {e′ = e′} o) = suc-r {y = tr⁻ˢ e′ y} (tr⁻-cong p) o

ŝ-r : ∀ {k k′ c} {x : Ordˢ k} {t₀ : Ordˢ k′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} → x ⊑ᵒ t₀ → x ⊑ᵒ Ord₊ˢ.ŝ c t₀ g
ĉ-r : ∀ {k k′ c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {x : Ordˢ k} {o₀ : Ordˢ k′} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k′} →
      x ⊑ᵒ o₀ → x ⊑ᵒ Ord₊ˢ.ĉᴸ c t₀ g o₀ o
ŝ-r {k′ = zero} p idO G (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ⊑-lim 0 (p idO G Go₀)
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (ψo₀ {p′ = p′} {σ′ = σ′} o) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = ψ0 p′ σ′ t₀} {o = λ η e → ψ0 p′ σ′ (g η e)} (ψ0-cong p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (ψo₀ {p′ = p′} {σ′ = σ′} o) =
  ŝ-r {c = c} {t₀ = ψ0 p′ σ′ t₀} {g = λ η e → ψ0 p′ σ′ (g η e)} (ψ0-cong p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (ψo₀ {p′ = p′} {σ′ = σ′} o) =
  ŝ-r {c = c} {t₀ = ψ0 p′ σ′ t₀} {g = λ η e → ψ0 p′ σ′ (g η e)} (ψ0-cong p) o
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (ψo₁ {p′ = p′} {σ′ = σ′} {z′ = z′} o) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = ψ1 p′ σ′ z′ t₀} {o = λ η e → ψ1 p′ σ′ z′ (g η e)} (ψ1-cong p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (ψo₁ {p′ = p′} {σ′ = σ′} {z′ = z′} o) =
  ŝ-r {c = c} {t₀ = ψ1 p′ σ′ z′ t₀} {g = λ η e → ψ1 p′ σ′ z′ (g η e)} (ψ1-cong p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (ψo₁ {p′ = p′} {σ′ = σ′} {z′ = z′} o) =
  ŝ-r {c = c} {t₀ = ψ1 p′ σ′ z′ t₀} {g = λ η e → ψ1 p′ σ′ z′ (g η e)} (ψ1-cong p) o
ŝ-r {k′ = zero} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ĉ-r {c = c} {t₀ = toZ t₀} {g = λ η e → toZ (g η e)} {o₀ = addˢ a′ σ′ t₀} {o = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {k′ = suc _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-r {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {k′ = lim _ _} {c = c} {t₀ = t₀} {g = g} p (addo {a′ = a′} {σ′ = σ′} o k a) =
  ŝ-r {c = c} {t₀ = addˢ a′ σ′ t₀} {g = λ η e → addˢ a′ σ′ (g η e)} (add-cong k a p) o
ŝ-r {c = c} {t₀ = t₀} {g = g} p (tro {e′ = e′} o)  = ŝ-r {c = c} {t₀ = trˢ e′ t₀} {g = λ η d → trˢ e′ (g η d)} (tr-cong p) o
ŝ-r {c = c} {t₀ = t₀} {g = g} p (tr⁻o {e′ = e′} o) = ŝ-r {c = c} {t₀ = tr⁻ˢ e′ t₀} {g = λ η d → tr⁻ˢ e′ (g η d)} (tr⁻-cong p) o
ĉ-r p idO G (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ⊑-lim 0 (p idO G Go₀)
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (ψo₀ {p′ = p′} {σ′ = σ′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = ψ0 p′ σ′ o₀} {o = λ η e → ψ0 p′ σ′ (o η e)} (ψ0-cong p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (ψo₁ {p′ = p′} {σ′ = σ′} {z′ = z′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = ψ1 p′ σ′ z′ o₀} {o = λ η e → ψ1 p′ σ′ z′ (o η e)} (ψ1-cong p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (addo {a′ = a′} {σ′ = σ′} o′ k a) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = addˢ a′ σ′ o₀} {o = λ η e → addˢ a′ σ′ (o η e)} (add-cong k a p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tro {e′ = e′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = trˢ e′ o₀} {o = λ η d → trˢ e′ (o η d)} (tr-cong p) o′
ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = o₀} {o = o} p (tr⁻o {e′ = e′} o′) =
  ĉ-r {c = c} {t₀ = t₀} {g = g} {o₀ = tr⁻ˢ e′ o₀} {o = λ η d → tr⁻ˢ e′ (o η d)} (tr⁻-cong p) o′
```

**`limᵢ-r`** 与 Uniform 逐字, 只是 `ψo` 分成两种栈, 派发相同 (弹栈不出现在 `limᵢ` 尾巴上).

```agda
limᵢ-r : ∀ {k k′ j} {x : Ordˢ k} {q : j <ᴵ k′} {g : Uˢ j (<→◃ q) → Ordˢ k′} →
         (∀ z → z ≅ˢ Ωˢ j → x ⊑ᵒ g (intoˢ (<→◃ q) z)) → x ⊑ᵒ Ord₊ˢ.limᵢ q g
limᵢ-r {q = ()} H idO
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (ψo₀ {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} o) with <ᴵ-dec (σ′ q) p′
... | injᵃ (via e r) = limᵢ-r (λ z d →
        subst (λ u → ψ0 p σ x ⊑ᵒ ψ0 p′ σ′ (g (intoˢ (<→◃ q) (tr⁻ˢ e u)))) (sym (out-intoˢ (<→◃ r) z))
              (ψ0-cong (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (ψ0-cong (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-r 0 (ψ0-cong (H (Ωˢ j) (Ωˢ-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (ψo₁ {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} {z = z₁} {z′ = z₁′} o)
  with <ᴵ-dec (σ′ q) p′
... | injᵃ (via e r) = limᵢ-r (λ z d →
        subst (λ u → ψ1 p σ z₁ x ⊑ᵒ ψ1 p′ σ′ z₁′ (g (intoˢ (<→◃ q) (tr⁻ˢ e u)))) (sym (out-intoˢ (<→◃ r) z))
              (ψ1-cong (H (tr⁻ˢ e z) (tr⁻ˢ-≅ e (≅ˢ-trans d (Ωˢ-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (ψ1-cong (H (Ωˢ j) (Ωˢ-refl j))) o
... | injᶜ _ = lim-r 0 (ψ1-cong (H (Ωˢ j) (Ωˢ-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o k ea) = limᵢ-r (λ z d →
  subst (λ u → addˢ a σ x ⊑ᵒ addˢ a′ σ′ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ′ q)) z))
        (add-cong k ea (H z d))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → trˢ e x ⊑ᵒ trˢ e′ (g (intoˢ (<→◃ q) (backˢ (resˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e′))) z))
        (tr-cong (H (backˢ (resˢ q e′) z) (≅ˢ-trans (backˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (resˢ q e′)))))))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr⁻ˢ e x ⊑ᵒ tr⁻ˢ e′ (g (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e′) u)))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e′))) z))
        (tr⁻-cong (H (backˢ (res⁻ˢ q e′) z) (≅ˢ-trans (back⁻ˢ-≅ q e′ d) (Ωˢ-≅ (≅ᴵ-sym (eqˢ (res⁻ˢ q e′)))))))) o
```

## §7 链的起点、`zero-l` 与 $\Omega$ 的单调性

**`B1` 的假设形式.** Uniform 的 `B1 : Ω j ⊑ᵒ ψ q σ z` 依赖 $\psi_q(0)=\Omega_j$. 有 $\hat\Omega$ 帧时 $\psi^{[\hat\Omega]}_q(0)$ 是弹栈闭包, 所以陈述改成: 若 $x\sqsubseteq^\mathsf o\psi^P_q(0)$, 则对一切自反的 $z$ 有 $x\sqsubseteq^\mathsf o\psi^P_q(z)$. 对 $z$ 结构递归: 后继/极限取第 1/0 项, `limᵢ` 穿透用 `limᵢ-r`, 折叠取第 0 项, `up` 换 `Sim`, `ŝ`/`ĉᴸ` 取第 0 点/第 0 个输出 (`ŝ-r`/`ĉ-r`). `up` 情况要求 $x\sqsubseteq^\mathsf o\psi^P_q(0)$ 对换过的 `Sim` 仍成立: 弹栈子句不读 `Sim`, `ψ1 q σ z zero` 与 `ψ1 q σ′ z zero` 定义性相等, 所以同一个假设可用.

```agda
B1₀ : ∀ {i ℓ k k₀} {q : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k₀} → x ⊑ᵒ Ωˢ i → (z : Ordˢ k) → z ≅ˢ z → x ⊑ᵒ ψ0 q σ z
B1₀ h Ord₊ˢ.zero e = h
B1₀ {q = q} {σ = σ} h (Ord₊ˢ.suc a) e = lim-r 1 (B1₀ {q = q} {σ = σ} h a (s-invˢ e))
B1₀ {q = q} {σ = σ} h (Ord₊ˢ.lim f) e = lim-r 0 (B1₀ {q = q} {σ = σ} h (f 0) (l-invˢ e 0))
B1₀ {q = q} {σ = σ} {x = x} h (Ord₊ˢ.limᵢ {i = j′} q′ g) e with <ᴵ-dec (σ q′) q
... | injᵃ (via e₁ r) = limᵢ-r (λ z d →
        subst (λ u → x ⊑ᵒ ψ0 q σ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ u)))) (sym (out-intoˢ (<→◃ r) z))
              (B1₀ {q = q} {σ = σ} h (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ z))) (i-respˢ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1₀ {q = q} {σ = σ} h (g (intoˢ (<→◃ q′) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-r 0 (B1₀ {q = q} {σ = σ} h (g (intoˢ (<→◃ q′) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
B1₀ {q = q} {σ = σ} h (Ord₊ˢ.up zero x) e     = B1₀ {q = q} {σ = λ r → σ (suc r)} h x (u-reflˢ zero e)
B1₀ {q = q} {σ = σ} h (Ord₊ˢ.up (self n) x) e = B1₀ {q = q} {σ = λ r → σ (lim n r)} h x (u-reflˢ (self n) e)
B1₀ {k = zero}    {q = q} {σ = σ} h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-r (B1₀ {q = q} {σ = σ} h t₀ (ŝ-refl₀ e))
B1₀ {k = suc _}   {q = q} {σ = σ} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1₀ {q = q} {σ = σ} h t₀ (ŝ-refl₀ e))
B1₀ {k = lim _ _} {q = q} {σ = σ} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1₀ {q = q} {σ = σ} h t₀ (ŝ-refl₀ e))
B1₀ {q = q} {σ = σ} h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-r (B1₀ {q = q} {σ = σ} h o₀ (ĉ-refl₀ e))

B1₁ : ∀ {i ℓ k k₀} {q : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z₁ : zero <ᴵ ℓ} {x : Ordˢ k₀} →
      x ⊑ᵒ ψ1 q σ z₁ Ord₊ˢ.zero → (z : Ordˢ k) → z ≅ˢ z → x ⊑ᵒ ψ1 q σ z₁ z
B1₁ h Ord₊ˢ.zero e = h
B1₁ {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.suc a) e = lim-r 1 (B1₁ {q = q} {σ = σ} {z₁ = z₁} h a (s-invˢ e))
B1₁ {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.lim f) e = lim-r 0 (B1₁ {q = q} {σ = σ} {z₁ = z₁} h (f 0) (l-invˢ e 0))
B1₁ {q = q} {σ = σ} {z₁ = z₁} {x = x} h (Ord₊ˢ.limᵢ {i = j′} q′ g) e with <ᴵ-dec (σ q′) q
... | injᵃ (via e₁ r) = limᵢ-r (λ z d →
        subst (λ u → x ⊑ᵒ ψ1 q σ z₁ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ u)))) (sym (out-intoˢ (<→◃ r) z))
              (B1₁ {q = q} {σ = σ} {z₁ = z₁} h (g (intoˢ (<→◃ q′) (tr⁻ˢ e₁ z))) (i-respˢ e (self-tr⁻ˢ e₁ (≅ˢ-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1₁ {q = q} {σ = σ} {z₁ = z₁} h (g (intoˢ (<→◃ q′) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
... | injᶜ _ = lim-r 0 (B1₁ {q = q} {σ = σ} {z₁ = z₁} h (g (intoˢ (<→◃ q′) (Ωˢ j′))) (i-respˢ e (Ωˢ-refl j′)))
B1₁ {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.up zero x) e     = B1₁ {q = q} {σ = λ r → σ (suc r)} {z₁ = z₁} h x (u-reflˢ zero e)
B1₁ {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.up (self n) x) e = B1₁ {q = q} {σ = λ r → σ (lim n r)} {z₁ = z₁} h x (u-reflˢ (self n) e)
B1₁ {k = zero}    {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.ŝ c t₀ g) e = ĉ-r (B1₁ {q = q} {σ = σ} {z₁ = z₁} h t₀ (ŝ-refl₀ e))
B1₁ {k = suc _}   {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1₁ {q = q} {σ = σ} {z₁ = z₁} h t₀ (ŝ-refl₀ e))
B1₁ {k = lim _ _} {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.ŝ c t₀ g) e = ŝ-r (B1₁ {q = q} {σ = σ} {z₁ = z₁} h t₀ (ŝ-refl₀ e))
B1₁ {q = q} {σ = σ} {z₁ = z₁} h (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) e = ĉ-r (B1₁ {q = q} {σ = σ} {z₁ = z₁} h o₀ (ĉ-refl₀ e))
```

**`add-r`、`zero-l`.** `add-r` 加 `ŝ`/`ĉᴸ` 情况 (取第 0 点/输出). `zero-l` 的四种观测: `idO` 时计值是 `zero`, 没有前驱; `ψo₀` 用 `B1₀` (假设 $\Omega_i\sqsubseteq^\mathsf o\Omega_i$); `ψo₁` 用 `B1₁` (假设由 `ψ1-≅` 给出: 两侧的弹栈闭包互模拟); 搬运观测对搬运后的右端递归 (要写出左端的层号 `{k = b}`, 否则报 `b != k of type Ordᴵ`).

```agda
add-r : ∀ {k ℓ ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordˢ k) → a ≅ˢ a′ → b ≅ˢ b → a ⊑ᵒ addˢ a′ σ b
add-r Ord₊ˢ.zero ea eb = ≅→⊑ᵒ ea
add-r {σ = σ} (Ord₊ˢ.suc b) ea eb = suc-r (add-r {σ = σ} b ea (s-invˢ eb))
add-r {σ = σ} (Ord₊ˢ.lim h) ea eb = lim-r 0 (add-r {σ = σ} (h 0) ea (l-invˢ eb 0))
add-r {a = a} {a′ = a′} {σ = σ} (Ord₊ˢ.limᵢ q g) ea eb = limᵢ-r (λ z d →
  subst (λ u → a ⊑ᵒ addˢ a′ σ (g (intoˢ (<→◃ q) u))) (sym (out-intoˢ (<→◃ (σ q)) z))
        (add-r {σ = σ} (g (intoˢ (<→◃ q) z)) ea (i-respˢ eb (≅ˢ-reflˡ d))))
add-r {σ = σ} (Ord₊ˢ.up zero x)     ea eb = add-r {σ = λ q → σ (suc q)} x ea (u-reflˢ zero eb)
add-r {σ = σ} (Ord₊ˢ.up (self n) x) ea eb = add-r {σ = λ q → σ (lim n q)} x ea (u-reflˢ (self n) eb)
add-r {k = zero}    {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ĉ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {k = suc _}   {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {k = lim _ _} {σ = σ} (Ord₊ˢ.ŝ c t₀ g) ea eb = ŝ-r (add-r {σ = σ} t₀ ea (ŝ-refl₀ eb))
add-r {σ = σ} (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) ea eb = ĉ-r (add-r {σ = σ} o₀ ea (ĉ-refl₀ eb))

𝟎ˢ : ∀ {ℓ} → Ordˢ ℓ
𝟎ˢ = Ord₊ˢ.zero

zero-l : ∀ {k k′} {y : Ordˢ k′} → y ≅ˢ y → 𝟎ˢ {k} ⊑ᵒ y
zero-l ey idO Goodᶻ.gz G′ = λ ()
zero-l {y = y} ey (ψo₀ {i = i} {p′ = p′} {σ′ = σ′} o) = B1₀ {q = p′} {σ = σ′} (≅→⊑ᵒ (Ωˢ-refl i)) y ey o
zero-l {y = y} ey (ψo₁ {i = i} {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} {z = z} {z′ = z′} o) =
  B1₁ {q = p′} {σ = σ′} {z₁ = z′} {x = ψ1 p σ z 𝟎ˢ}
      (≅→⊑ᵒ (ψ1-≅ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} {z = z} {z′ = z′} (≅ᴵ-refl i) z≅)) y ey o
zero-l {y = y} ey (addo {σ′ = σ′} o k ea) = add-r {σ = σ′} y ea ey o
zero-l ey (tro {b = b} {e′ = e′} o)  = zero-l {k = b} (self-trˢ e′ ey) o
zero-l ey (tr⁻o {a = a} {e′ = e′} o) = zero-l {k = a} (self-tr⁻ˢ e′ ey) o
```

**$\Omega$ 的单调性** 与 Uniform §5 逐字 (`⊑ᵒ-≅ʳ` 现在经证书搬运).

```agda
Ω0 : ∀ b → Ωˢ zero ⊑ᵒ Ωˢ b
Ω0 zero      = ≅→⊑ᵒ (Ωˢ-refl zero)
Ω0 (suc b)   = limᵢ-r (λ z d → up-r {r = zero} {y = z} (⊑ᵒ-≅ʳ (Ω0 b) (≅ˢ-sym d)))
Ω0 (lim g s) = lim-r 0 (up-r {r = self 0} (Ω0 (g 0)))

Ω< : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ωˢ (suc a) ⊑ᵒ Ωˢ b
Ω< e zero      = ≅→⊑ᵒ (Ωˢ-≅ (s≅ e))
Ω< e (suc q)   = limᵢ-r (λ z d → up-r {r = zero} {y = z} (⊑ᵒ-≅ʳ (Ω< e q) (≅ˢ-sym d)))
Ω< e (lim n q) = lim-r n (up-r {r = self n} (Ω< e q))

Ω-monoᵒ : ∀ {a b} → a ⊑ᴵ b → Ωˢ a ⊑ᵒ Ωˢ b
Ω-monoᵒ {b = b} z⊑ = Ω0 b
Ω-monoᵒ (s⊑ e q)   = Ω< e q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l {r = self n} (Ω-monoᵒ (k n)))
```

## §8 遗传好树 `Good`

`Good₊` 照 Uniform §6, 加两个构造子.

- `bŝ`: $t_0$ 与各 $g\,\eta\,e$ 好; 自反 ($t_0\cong t_0$, $g$ 在相关的 $\eta$ 上相关; 用于 §9 的第 0 层搬运); $t_0\sqsubseteq^\mathsf o g\,\eta\,e$; $g$ 对 $\eta$ 单调; **支配** `Dom ℓ c t₀ g`.
- `bĉ`: 链的证书与 Prefix `gc` 的前六个字段 (链已在 `Z` 里, 证书现成), 输出好且单调 (观测意义).

**支配按层号分.** 第 0 层的 `ŝ` 将被 `toZ` 读成链, 需要的正是 `gc` 的 `d₀`/`dE`: 对**一切**证书, $c\sqsubseteq^\mathsf I$ 链点计值后的层号 (对一切证书量化, 因为证书由 `Good→Goodᶻ` 事后给出). 非零层的 `ŝ` 还不是链, 它的链点要等外层的 $\psi_0$ 把它映到第 0 层才确定, 此时只记 $c\sqsubseteq^\mathsf I2$; 到第 0 层时由严格性引理补出链点的支配 (Stage2Label §4). 界 $\le2$ 正是 Prefix §8 (b) 的 "$\delta\le1$".

```agda
two : Ordᴵ
two = suc (suc zero)

Dom : (ℓ c : Ordᴵ) → Ordˢ ℓ → ((η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ) → Set
Dom zero      c t₀ g = (∀ G → c ⊑ᴵ toLevel (force (toZ t₀) G) (force-HS _ G)) ×
                       (∀ η e G → c ⊑ᴵ toLevel (force (toZ (g η e)) G) (force-HS _ G))
Dom (suc _)   c t₀ g = c ⊑ᴵ two
Dom (lim _ _) c t₀ g = c ⊑ᴵ two

module _ (ℓ : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set) where
  data Good₊ : Ordˢ ℓ → Set where
    bz : Good₊ Ord₊ˢ.zero
    bs : ∀ {a} → Good₊ a → Good₊ (Ord₊ˢ.suc a)
    bl : ∀ {h : ℕ → Ordˢ ℓ} → (∀ n → Good₊ (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ (Ord₊ˢ.lim h)
    bi : ∀ {j} {p : j <ᴵ ℓ} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} →
         (∀ (z : Ordˢ j) → z ≅ˢ z → G< j (<→◃ p) (intoˢ (<→◃ p) z) → Good₊ (f (intoˢ (<→◃ p) z))) →
         (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ p) z) ⊑ᵒ f (intoˢ (<→◃ p) z′)) →
         Good₊ (Ord₊ˢ.limᵢ p f)
    bu : ∀ {k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Good₊ (Ord₊ˢ.up r x)
    bŝ : ∀ {c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
         Good₊ t₀ → (∀ η e → Good₊ (g η e)) →
         t₀ ≅ˢ t₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ˢ g η′ e′) →
         (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
         Dom ℓ c t₀ g → Good₊ (Ord₊ˢ.ŝ c t₀ g)
    bĉ : ∀ {c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ}
         (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
         c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
         (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
         (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
         (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
         Good₊ o₀ → (∀ η e → Good₊ (o η e)) →
         (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
         Good₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o)

Gd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → Set
Gd i zero         x = Good₊ i Gd x
Gd i (suc r)      x = Gd i r x
Gd _ (self {f} n) x = Good₊ (f n) Gd x
Gd i (lim n r)    x = Gd i r x

Good : ∀ {ℓ} → Ordˢ ℓ → Set
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Gd i r (intoˢ r x) → Good x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} → Good x → Gd i r (intoˢ r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g

Gd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordˢ i} → Gd i r (intoˢ r x) → Gd i r′ (intoˢ r′ x)
Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)
```

**第 0 层的好树有证书.** `Good→Goodᶻ` 对 `Good` 递归: `gl` 的步进取观测 `idO` 下的 $\sqsubseteq^\mathsf o$ (对任意证书, 实例化为递归给出的证书); `bŝ` 变成 `gc`, 链与输出相同, `d₀`/`dE` 由 `Dom zero` 在递归给出的证书处实例化; `bĉ` 直接搬链的证书. 这是 Uniform §8 的 `Good→HS` 的对应.

```agda
Good→Goodᶻ : ∀ {x : Ordˢ zero} → Good x → Goodᶻ (toZ x)
Good→Goodᶻ bz         = Goodᶻ.gz
Good→Goodᶻ (bs g)     = Goodᶻ.gs (Good→Goodᶻ g)
Good→Goodᶻ (bl hg st) = Goodᶻ.gl (λ n → Good→Goodᶻ (hg n)) (λ n → st n idO (Good→Goodᶻ (hg n)) (Good→Goodᶻ (hg (suc n))))
Good→Goodᶻ (bi {p = ()} hb hm)
Good→Goodᶻ (bu {r = ()} g)
Good→Goodᶻ (bŝ g₀ gg et eg m mm (d₀ , dE)) =
  Goodᶻ.gc G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
           (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
           G₀ Gg (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
  where
  G₀ = Good→Goodᶻ g₀
  Gg = λ η e → Good→Goodᶻ (gg η e)
Good→Goodᶻ (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  Goodᶻ.gc G₀ Gg d₀ dE m₀ mE (Good→Goodᶻ go) (λ η e → Good→Goodᶻ (gO η e))
           (λ η e → mo η e idO (Good→Goodᶻ go) (Good→Goodᶻ (gO η e)))
           (λ η e η′ e′ h → mO η e η′ e′ h idO (Good→Goodᶻ (gO η e)) (Good→Goodᶻ (gO η′ e′)))
```

## §9 `Good` 对搬运封闭

照 Uniform §6 的四重互递归. 新情况: `bŝ` 逐点, 支配经 `Dom-tr`/`Dom-tr⁻` 搬运. 非零层的支配是 $c\sqsubseteq^\mathsf I2$, 不动; 第 0 层 ($e$ 必为 `z≅`) 的支配谈的是 `trˢ z≅ t₀` 的计值, 它与 $t_0$ 的计值经 `trˢ-≅ z≅` (要 $t_0$ 自反, 即 `bŝ` 的自反字段) 与 `force-≅` 相关, 证书由 `Good→Goodᶻ` 给出 (`Dom0-≅`). `bĉ` 链不动, 输出逐点.

```agda
back-mono : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (resˢ q e))} → u ⊑ᵒ u′ → backˢ (resˢ q e) u ⊑ᵒ backˢ (resˢ q e) u′
back-mono zero      (s≅ e) h = tr⁻-cong h
back-mono (suc q)   (s≅ e) h = back-mono q e h
back-mono (lim n q) (l≅ f) h = back-mono q (f n) h

back⁻-mono : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordˢ (repˢ (res⁻ˢ q e))} → u ⊑ᵒ u′ → backˢ (res⁻ˢ q e) u ⊑ᵒ backˢ (res⁻ˢ q e) u′
back⁻-mono zero      (s≅ e) h = tr-cong h
back⁻-mono (suc q)   (s≅ e) h = back⁻-mono q e h
back⁻-mono (lim n q) (l≅ f) h = back⁻-mono q (f n) h

self-back : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → u ≅ˢ u → backˢ (resˢ q e) u ≅ˢ backˢ (resˢ q e) u
self-back q e d = ≅ˢ-reflˡ (backˢ-≅ q e d)

self-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → u ≅ˢ u → backˢ (res⁻ˢ q e) u ≅ˢ backˢ (res⁻ˢ q e) u
self-back⁻ q e d = ≅ˢ-reflˡ (back⁻ˢ-≅ q e d)

Dom0-≅ : ∀ {c} {t₀ t₀′ : Ordˢ zero} {g g′ : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} →
         Good t₀ → (∀ η d → Good (g η d)) → t₀′ ≅ˢ t₀ → (∀ η d → g′ η d ≅ˢ g η d) →
         Dom zero c t₀ g → Dom zero c t₀′ g′
Dom0-≅ g0 gg et eg (d₀ , dE) =
  (λ G → ⊑ᴵ-≅ʳ (d₀ (Good→Goodᶻ g0)) (toLevel-≅ (force-HS _ (Good→Goodᶻ g0)) (force-HS _ G)
            (force-≅ (toZ-≅ (≅ˢ-sym et)) (Good→Goodᶻ g0) G))) ,
  (λ η d G → ⊑ᴵ-≅ʳ (dE η d (Good→Goodᶻ (gg η d))) (toLevel-≅ (force-HS _ (Good→Goodᶻ (gg η d))) (force-HS _ G)
            (force-≅ (toZ-≅ (≅ˢ-sym (eg η d))) (Good→Goodᶻ (gg η d)) G)))

Dom-tr : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ a} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ a} →
         Good t₀ → (∀ η d → Good (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
         Dom a c t₀ g → Dom b c (trˢ e t₀) (λ η d → trˢ e (g η d))
Dom-tr z≅     g0 gg et eg h = Dom0-≅ g0 gg (trˢ-≅ z≅ et) (λ η d → trˢ-≅ z≅ (eg η d)) h
Dom-tr (s≅ _) g0 gg et eg h = h
Dom-tr (l≅ _) g0 gg et eg h = h

Dom-tr⁻ : ∀ {a b c} (e : a ≅ᴵ b) {t₀ : Ordˢ b} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ b} →
          Good t₀ → (∀ η d → Good (g η d)) → t₀ ≅ˢ t₀ → (∀ η d → g η d ≅ˢ g η d) →
          Dom b c t₀ g → Dom a c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
Dom-tr⁻ z≅     g0 gg et eg h = Dom0-≅ g0 gg (tr⁻ˢ-≅ z≅ et) (λ η d → tr⁻ˢ-≅ z≅ (eg η d)) h
Dom-tr⁻ (s≅ _) g0 gg et eg h = h
Dom-tr⁻ (l≅ _) g0 gg et eg h = h

Good-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} → Good x → Good (trˢ e x)
Good-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} → Good x → Good (tr⁻ˢ e x)
Good-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} → Good u → Good (backˢ (resˢ q e) u)
Good-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} → Good u → Good (backˢ (res⁻ˢ q e) u)

Good-tr e bz         = bz
Good-tr e (bs g)     = bs (Good-tr e g)
Good-tr e (bl hg st) = bl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
Good-tr e (bi {p = q} {f = f} hb hm) = bi
  (λ z ez g → subst (λ w → Good (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z))
                    (Good-tr e (hb (backˢ (resˢ q e) z) (self-back q e ez)
                                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (ltˢ (resˢ q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ⊑ᵒ trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w′))))
                         (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) z′))
                         (tr-cong (hm (back-mono q e h))))
Good-tr (s≅ e) (bu {r = zero} g)   = bu (Good-tr e g)
Good-tr (l≅ f) (bu {r = self n} g) = bu (Good-tr (f n) g)
Good-tr e (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-tr e g0) (λ η d → Good-tr e (gg η d)) (self-trˢ e et)
     (λ η d η′ d′ eη → trˢ-≅ e (≅-trˢ e (eg η d η′ d′ eη)))
     (λ η d → tr-cong (m η d)) (λ η d η′ d′ h → tr-cong (mm η d η′ d′ h))
     (Dom-tr e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
Good-tr e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-tr e go) (λ η d → Good-tr e (gO η d))
     (λ η d → tr-cong (mo η d)) (λ η d η′ d′ h → tr-cong (mO η d η′ d′ h))

Good-tr⁻ e bz         = bz
Good-tr⁻ e (bs g)     = bs (Good-tr⁻ e g)
Good-tr⁻ e (bl hg st) = bl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
Good-tr⁻ e (bi {p = q} {f = f} hb hm) = bi
  (λ z ez g → subst (λ w → Good (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))))) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z))
                    (Good-tr⁻ e (hb (backˢ (res⁻ˢ q e) z) (self-back⁻ q e ez)
                                    (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (ltˢ (res⁻ˢ q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ⊑ᵒ tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w′))))
                         (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z)) (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) z′))
                         (tr⁻-cong (hm (back⁻-mono q e h))))
Good-tr⁻ (s≅ e) (bu {r = zero} g)   = bu (Good-tr⁻ e g)
Good-tr⁻ (l≅ f) (bu {r = self n} g) = bu (Good-tr⁻ (f n) g)
Good-tr⁻ e (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-tr⁻ e g0) (λ η d → Good-tr⁻ e (gg η d)) (self-tr⁻ˢ e et)
     (λ η d η′ d′ eη → tr⁻ˢ-≅ e (≅-tr⁻ˢ e (eg η d η′ d′ eη)))
     (λ η d → tr⁻-cong (m η d)) (λ η d η′ d′ h → tr⁻-cong (mm η d η′ d′ h))
     (Dom-tr⁻ e g0 gg et (λ η d → eg η d η d (≅ᴵ-refl η)) dm)
Good-tr⁻ e (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-tr⁻ e go) (λ η d → Good-tr⁻ e (gO η d))
     (λ η d → tr⁻-cong (mo η d)) (λ η d η′ d′ h → tr⁻-cong (mO η d η′ d′ h))

Good-back zero      (s≅ e) g = Good-tr⁻ e g
Good-back (suc q)   (s≅ e) g = Good-back q e g
Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

Good-back⁻ zero      (s≅ e) g = Good-tr e g
Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g
```

## §10 $\Omega$ 与加法

`Good-Ω` 与 Uniform 逐字. **加法的层号条件 `Lv k ℓ`**: 被加数在第 0 层时, 尾巴也在第 0 层. 理由: 尾巴是非零层 (种类 `false`) 的 `ŝ` 时, `addˢ` 输出被加数层上的 `ŝ`; 被加数在第 0 层时, 输出要第 0 层的支配 (对一切证书), 而输入只有 $c\sqsubseteq^\mathsf I2$. 这种组合只在退化层号上出现 (§0 的 `vac`: `Simᴵ Z⁰ zero`), 由 `Lv` 排除. `Lv` 沿 `up` 下降 (`Lv-up`: 被加数在第 0 层时不会有 `up` 节点). 由同一层号的加法迭代 (`Good-iter`) 与规则 4 的步进 (`rule4ᵒ`) 都满足 `Lv-refl`.

```agda
Good-Ω : ∀ a → Good (Ωˢ a)
Good-Ω zero      = bs bz
Good-Ω (suc c)   = bi (λ z ez g → bu g) (λ {z} {z′} h → up-l {r = zero} {x = z} (up-r {r = zero} {y = z′} h))
Good-Ω (lim g s) = bl (λ n → bu (Good-Ω (g n))) (λ n → up-l {r = self n} (up-r {r = self (suc n)} (Ω-monoᵒ (s n))))

Lv : Ordᴵ → Ordᴵ → Set
Lv k zero      = kd k ≡ true
Lv k (suc _)   = ⊤
Lv k (lim _ _) = ⊤

Lv-refl : ∀ k → Lv k k
Lv-refl zero      = refl
Lv-refl (suc _)   = tt
Lv-refl (lim _ _) = tt

Lv-up : ∀ {k₀ k ℓ} → k₀ ◃₁ k → Lv k ℓ → Lv k₀ ℓ
Lv-up {ℓ = zero}    zero     ()
Lv-up {ℓ = zero}    (self n) ()
Lv-up {ℓ = suc _}   r        _ = tt
Lv-up {ℓ = lim _ _} r        _ = tt

Good-add : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} → Lv k ℓ → Good a → a ≅ˢ a → Good b → Good (addˢ a σ b)
Good-add lv ga ea bz          = ga
Good-add lv ga ea (bs g)      = bs (Good-add lv ga ea g)
Good-add lv ga ea (bl hg st)  = bl (λ n → Good-add lv ga ea (hg n)) (λ n → add-cong refl ea (st n))
Good-add {a = a} {σ = σ} lv ga ea (bi {p = q} {f = f} hb hm) = bi
  (λ z ez g → subst (λ u → Good (addˢ a σ (f (intoˢ (<→◃ q) u)))) (sym (out-intoˢ (<→◃ (σ q)) z))
                    (Good-add lv ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (λ {z} {z′} h → subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ⊑ᵒ addˢ a σ (f (intoˢ (<→◃ q) v)))
                         (sym (out-intoˢ (<→◃ (σ q)) z)) (sym (out-intoˢ (<→◃ (σ q)) z′)) (add-cong refl ea (hm h)))
Good-add lv ga ea (bu {r = zero} g)   = Good-add (Lv-up zero lv) ga ea g
Good-add lv ga ea (bu {r = self n} g) = Good-add (Lv-up (self n) lv) ga ea g
Good-add {k = zero} lv ga ea (bŝ g0 gg et eg m mm dm) =
  bĉ G₀ Gg (proj₁ dm G₀) (λ η e → proj₂ dm η e (Gg η e))
     (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
     (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h))
  where
  G₀ = Good→Goodᶻ g0
  Gg = λ η e → Good→Goodᶻ (gg η e)
Good-add {k = suc _} {ℓ = zero} lv ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
Good-add {k = lim _ _} {ℓ = zero} lv ga ea (bŝ g0 gg et eg m mm dm) = ⊥-elim (tf (sym lv))
Good-add {k = suc _} {ℓ = suc _} lv ga ea (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
Good-add {k = suc _} {ℓ = lim _ _} lv ga ea (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
Good-add {k = lim _ _} {ℓ = suc _} lv ga ea (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
Good-add {k = lim _ _} {ℓ = lim _ _} lv ga ea (bŝ g0 gg et eg m mm dm) =
  bŝ (Good-add lv ga ea g0) (λ η e → Good-add lv ga ea (gg η e)) (addˢ-≅ refl ea et)
     (λ η e η′ e′ eη → addˢ-≅ refl ea (eg η e η′ e′ eη))
     (λ η e → add-cong refl ea (m η e)) (λ η e η′ e′ h → add-cong refl ea (mm η e η′ e′ h)) dm
Good-add lv ga ea (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-add lv ga ea go) (λ η e → Good-add lv ga ea (gO η e))
     (λ η e → add-cong refl ea (mo η e)) (λ η e η′ e′ h → add-cong refl ea (mO η e η′ e′ h))

Good-iter : ∀ {ℓ} {c : Ordˢ ℓ} → Good c → c ≅ˢ c → ∀ n → Good (iter (c +ˢ_) Ord₊ˢ.zero n)
Good-iter {ℓ} gc ec zero    = bz
Good-iter {ℓ} gc ec (suc n) = Good-add (Lv-refl ℓ) gc ec (Good-iter gc ec n)

rule4ᵒ : ∀ {ℓ} {c : Ordˢ ℓ} → c ≅ˢ c → ∀ n → iter (c +ˢ_) Ord₊ˢ.zero n ⊑ᵒ iter (c +ˢ_) Ord₊ˢ.zero (suc n)
rule4ᵒ ec zero    = zero-l ec
rule4ᵒ ec (suc n) = add-cong refl ec (rule4ᵒ ec n)
```

**读法.** 第 0 层尾巴 `ŝ` 的和是 `ĉᴸ`: 链的证书由 `Good→Goodᶻ` 给出, 支配与单调在这些证书处实例化, 输出 $a+t_0$, $a+g\,\eta\,e$ 递归地好.

## §11 移植清单

相对 [Uniform](Uniform.lagda.md) (族 Level → Prefix 的 `Ordˢ`, 观测底部 $\sqsubseteq$ → 计值后的 $\sqsubseteq$):

| 名字 | 状态 | 说明 |
|---|---|---|
| `≅`/`R`/`≅-sym`/`tr-≅` 组/`≅-trans`/`Ω-≅`/`add-≅`/`ψ-≅` (Level §5–§7) | 移植 + 新子句 | `ŝ≅` 带 `kd` 与界的 $\cong^\mathsf I$; `ĉ≅` 带 `≅ᶻ`; `addˢ-≅` 多种类前提; `ψ-≅` 分 `ψ0-≅`/`ψ1-≅` |
| `≅ᶻ`, `chain≅`, `outs≅`, `force-≅`, `Goodᶻ-tr` | **新** | 计值与证书无关; 证书搬运 |
| `Obs`, `run`, `≈ᵒ`, `run-≅` | `ψ⁰o` 删去, `ψo` 分两种栈 | `addo` 相似多种类字段 |
| `_⊑ᵒ_`, `≅→⊑ᵒ` | 底部换成 `force`, 对一切证书 | |
| `⊑ᵒ-≅ʳ` | 中间项的证书由 `Goodᶻ-tr` 给 | Uniform 中一行 |
| `ψ-cong`, `add-cong`, `tr-cong`, `tr⁻-cong`, `up-l`, `up-r` | 逐字 (递归调用写出隐式树) | |
| `lim-r`, `lim-l`, `suc-r`, `limᵢ-r` | 逐字 (同上) | `idO` 先匹配证书 |
| `ŝ-r`, `ĉ-r` | **新** | 第 0 层时读作链, 第 0 项 |
| `B1`, `B1⁰` | 改为假设形式 `B1₀`/`B1₁` | $\psi^P(0)$ 不再是 $\Omega_j$ |
| `add-r`, `zero-l`, `Ω0`, `Ω<`, `Ω-monoᵒ` | 逐字 + `ŝ`/`ĉᴸ` 情况 | |
| `Good₊`/`Gd`/`Good` | 加 `bŝ` (含 `Dom`)、`bĉ` | |
| `Good→HS` | → `Good→Goodᶻ` | 落在 Prefix 的证书上 |
| `Good-tr` 四重 | + `Dom-tr`/`Dom-tr⁻`/`Dom0-≅` | 第 0 层支配经 `force-≅` 搬运 |
| `Good-Ω`, `Good-iter`, `rule4ᵒ` | 逐字 | |
| `Good-add` | 多前提 `Lv` | 排除退化层号 (`vac`) |
| `Good-ψ`, `Good-ψ⁰`, `chain-*`, `Uniform` | 见 Stage2Label | 闭包理论 (带栈、带支配) |

## §12 结论与边界

**已证** (`--safe --without-K`, 无公设、无洞、无编译指示): 新族的互模拟 `≅ˢ` 是 PER (对称、传递), 搬运不可见, 对 $\Omega$、加法 (同种类)、`toZ`、两种栈的 `ψᴾ` 是同余; `Z` 上的 `≅ᶻ` 与 `force-≅`/`Goodᶻ-tr`; 以计值为底的观测前序及其全部同余与上界引理 (含 `ŝ-r`/`ĉ-r`)、带栈的链起点 `B1₀`/`B1₁`、`zero-l`、`Ω-monoᵒ`; `Good` 及其对搬运、$\Omega$、加法的封闭, `Good→Goodᶻ`.

**移植需要的新东西** (相对机械的照抄): (i) `force-≅` 与 `Goodᶻ-tr` (观测前序对一切证书量化); (ii) 层号种类 `kd` (`ŝ` 的读法依赖层号是否为 0, 且不能由 `Sim` 推出, `vac`); (iii) `ŝ≅` 的传递性用 $c\cong^\mathsf Ic'$, 即紧的界; (iv) `B1` 的假设形式; (v) `Good` 的支配字段按层号分, 加法的 `Lv`; (vi) 递归调用写出隐式参数 (两条编译错误见 §5、§6).

**边界.**

- 栈只处理长度 $\le1$ (`ψ0`/`ψ1`, 以及对应的观测). 长度 2 的栈 ($\psi_0(\Omega_\Omega\cdot2)$) 要 `rebase` 在变量栈上计算 (`onlyΩ̂ P`), 本文没有写; 更根本的障碍是支配, 见 Stage2Label §11.
- 非零层的支配固定为 $c\sqsubseteq^\mathsf I2$. 这足够 $\psi_0(\Omega_\Omega+\Omega_2)$, 不足够更大的环境层号.
- 本文不改 `src/`、`archive/` 与已有的 Align 文件, README 未改.
